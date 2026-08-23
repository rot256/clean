import Clean.Caliper.MultiLimbSimExpr
import Clean.Caliper.WitgenSimIR
import Clean.Caliper.MultiLimbEntry

/-!
# The multi-limb lowering simulates the witness IR

The program level: `let`-steps, vector outputs, and the whole compiled program. The
shape follows the single-word `WitgenSimIR.lean`, with two differences that come from
the representation: a field value occupies `k` registers, so a step's copy is
`movLimbs` and an output element is `k` pushes, and the buffer contents are described
by `encFlat`, the concatenation of the elements' Montgomery limbs.
-/

namespace Caliper.MultiLimb

open Caliper Caliper.Limbs Caliper.WitgenCompile Witgen

/-! ## The buffer encoding of a vector -/

section Flat

variable {p : ℕ} [Fact p.Prime]

/-- The buffer words of a list of field elements: each element's `k` Montgomery limbs,
low limb first, concatenated. -/
def encFlat (k : ℕ) (l : List (F p)) : List (Word 64) :=
  l.flatMap fun x => encWords k (montVal k x)

omit [Fact p.Prime] in
@[simp] theorem encFlat_nil (k : ℕ) : encFlat k ([] : List (F p)) = [] := rfl

omit [Fact p.Prime] in
theorem encFlat_cons (k : ℕ) (x : F p) (l : List (F p)) :
    encFlat k (x :: l) = encWords k (montVal k x) ++ encFlat k l := by
  simp [encFlat]

omit [Fact p.Prime] in
theorem encFlat_append (k : ℕ) (l₁ l₂ : List (F p)) :
    encFlat k (l₁ ++ l₂) = encFlat k l₁ ++ encFlat k l₂ := by
  simp [encFlat]

omit [Fact p.Prime] in
theorem encFlat_length (k : ℕ) : ∀ l : List (F p), (encFlat k l).length = l.length * k
  | [] => by simp
  | x :: l => by
    rw [encFlat_cons, List.length_append, encWords_length, encFlat_length k l,
      List.length_cons]
    ring

/-- Appending one element's words, then the rest. -/
theorem append_toArray_assoc {α : Type} (arr : Array α) (l₁ l₂ : List α) :
    (arr ++ l₁.toArray) ++ l₂.toArray = arr ++ (l₁ ++ l₂).toArray := by simp

end Flat

/-! ## Extending the encoded context -/

section StateHelpers

variable {p : ℕ} [Fact p.Prime]

omit [Fact p.Prime] in
/-- `StateEncML` only constrains the registers below `next` and buffer `0`. -/
theorem StateEncML_frame {k pv L : ℕ} {envArr : Array (Word 64)}
    {locals : Array (F p ⊕ UInt64)} {idx next : ℕ} {s s' : State 64}
    (hs : StateEncML k pv L envArr locals idx next s)
    (hregs : ∀ q, q < next → s'.regs q = s.regs q) (hbuf0 : s'.bufs 0 = s.bufs 0) :
    StateEncML k pv L envArr locals idx next s' := by
  have h := StateEncML_mono hs (Nat.le_refl next) hregs hbuf0
  exact h

omit [Fact p.Prime] in
/-- Writing the index register re-points the encoding at the new index. -/
theorem StateEncML_setIdx {k pv L : ℕ} {envArr : Array (Word 64)}
    {locals : Array (F p ⊕ UInt64)} {idx next : ℕ} {s : State 64}
    (hk : 0 < k) (hs : StateEncML k pv L envArr locals idx next s) (i : ℕ) :
    StateEncML k pv L envArr locals i next
      (s.setReg (idxReg k L) (BitVec.ofNat 64 i)) := by
  obtain ⟨henv, hsz, hfr, hpre, hloc, -⟩ := hs
  have hidxlt : LT.lt (α := ℕ) (idxReg k L) next :=
    Nat.lt_of_lt_of_le (idxReg_lt k L) hfr
  have hidxk : k + 2 ≤ idxReg k L := by simp only [idxReg]; omega
  refine ⟨by rw [bufs_setReg]; exact henv, hsz, hfr,
    ⟨fun j hj => by
        rw [regs_setReg_ne _ _ (show 0 + j ≠ idxReg k L by omega)]
        exact hpre.modulus j hj,
      by
        rw [regs_setReg_ne _ _ (show k + 1 ≠ idxReg k L by omega)]
        exact hpre.const⟩, fun i' hi' => ?_, by rw [regs_setReg_self]⟩
  have hlt2 : localReg k i' + k ≤ idxReg k L :=
    localReg_le_localReg (Nat.lt_of_lt_of_le hi' hsz)
  have hloci := hloc i' hi'
  rcases hv : locals[i'] with x | u
  · rw [hv] at hloci
    intro j hj
    rw [regs_setReg_ne _ _ (show localReg k i' + j ≠ idxReg k L by omega)]
    exact hloci j hj
  · rw [hv] at hloci
    show (s.setReg (idxReg k L) (BitVec.ofNat 64 i)).regs (localReg k i') = encU u
    rw [regs_setReg_ne _ _ (show localReg k i' ≠ idxReg k L by omega)]
    exact hloci

end StateHelpers

/-! ## The program-level simulation -/

section Sim

variable {C : CostModel} {p : ℕ} [Fact p.Prime] {k pv : ℕ} (hf : FieldOkML p pv k)
variable (env : ProverEnvironment (F p)) (N : ℕ) (envArr : Array (Word 64))
variable (henv : EnvEncML k env N envArr) (hNk : N * k ≤ 2 ^ 64)

include hf henv hNk

/-- Simulation for one `let`-step: the code for step number `locals.size` runs from a
state encoding the context and lands in one encoding the context extended by the
step's reference value. -/
theorem compileStepML_sim (Γ : List VSort) (locals : Array (F p ⊕ UInt64)) (L : ℕ)
    (hL : LocalsMatch Γ locals) (hsz : locals.size < L) :
    ∀ (st : Step (F p)) (s : State 64),
      Step.compilable Γ st = true → Step.envBound N st = true →
      StateEncML k pv L envArr locals 0 (tmpBase k L) s →
      ∃ s' t d pp, Exec C (compileStepML k L locals.size st) s s' t d pp ∧
        StateEncML k pv L envArr (locals.push (stepValue env locals st)) 0
          (tmpBase k L) s' ∧
        LocalsMatch (Γ ++ [Step.sort st]) (locals.push (stepValue env locals st)) ∧
        s'.bufs = s.bufs ∧ s'.caps = s.caps
  | .letF e, s, hc, hb, hs => by
    simp only [Step.compilable] at hc
    simp only [Step.envBound] at hb
    have hΓ : Γ.length ≤ L := by rw [hL.1]; omega
    rcases hE : compileFML k L e (tmpBase k L) with ⟨ce, r, n'⟩
    have hbd := compileFML_bounds k L hf.limbs_pos hΓ e (tmpBase k L) hc
      (Nat.le_refl _)
    simp only [hE] at hbd
    obtain ⟨s₁, t₁, d₁, p₁, hex₁, hr₁, hp₁, hbf₁, hcp₁⟩ :=
      compileFML_sim hf env N envArr henv hNk Γ locals 0 L hL e (tmpBase k L) s
        hc hb hs
    simp only [hE] at hex₁ hr₁
    have hdis : localReg k locals.size + k ≤ r ∨ r + k ≤ localReg k locals.size := by
      rcases hbd.2.2 with h | h
      · exact Or.inl (Nat.le_trans (localReg_le hsz) h)
      · exact Or.inr (by rw [hL.1] at h; exact h)
    obtain ⟨s₂, t₂, d₂, p₂, hex₂, hd₂, hp₂, hbf₂, hcp₂⟩ :=
      movLimbs_exec (C := C) (k := k) (d := localReg k locals.size) (a := r) hdis hr₁
    obtain ⟨henv₀, hsz₀, hfr₀, hpre₀, hloc₀, hidx₀⟩ := hs
    have hjidx : localReg k locals.size + k ≤ idxReg k L :=
      localReg_le_localReg hsz
    have hk : 0 < k := hf.limbs_pos
    have hjk : k + 2 ≤ localReg k locals.size := by simp only [localReg]; omega
    have hjtmp : localReg k locals.size + k ≤ tmpBase k L := localReg_le hsz
    simp only [compileStepML, hE]
    refine ⟨s₂, _, _, _, .seq hex₁ hex₂, ⟨?_, ?_, hfr₀, ⟨?_, ?_⟩, ?_, ?_⟩, ?_, ?_, ?_⟩
    · rw [hbf₂, hbf₁]; exact henv₀
    · rw [Array.size_push]; omega
    · intro j hj
      rw [hp₂ _ (Or.inl (by omega)), hp₁ _ (by omega)]
      exact hpre₀.modulus j hj
    · rw [hp₂ _ (Or.inl (by omega)), hp₁ _ (by omega)]
      exact hpre₀.const
    · intro i hi
      rw [Array.size_push] at hi
      rcases Nat.lt_or_ge i locals.size with hlt | hge
      · have hli : localReg k i + k ≤ localReg k locals.size :=
          localReg_le_localReg hlt
        have hloci := hloc₀ i hlt
        rw [Array.getElem_push_lt hlt]
        rcases hv : locals[i] with x | u
        · rw [hv] at hloci
          intro j hj
          rw [hp₂ _ (Or.inl (by omega)), hp₁ _ (by omega)]
          exact hloci j hj
        · rw [hv] at hloci
          show s₂.regs (localReg k i) = encU u
          rw [hp₂ _ (Or.inl (by omega)), hp₁ _ (by omega)]
          exact hloci
      · have hib : i = locals.size := by omega
        subst hib
        rw [Array.getElem_push_eq]
        exact hd₂
    · rw [hp₂ _ (Or.inr (by omega)), hp₁ _ (Nat.lt_of_lt_of_le (idxReg_lt k L)
        (Nat.le_refl _))]
      exact hidx₀
    · exact LocalsMatch_push_inl hL _
    · rw [hbf₂, hbf₁]
    · rw [hcp₂, hcp₁]
  | .letU e, s, hc, hb, hs => by
    simp only [Step.compilable] at hc
    simp only [Step.envBound] at hb
    have hΓ : Γ.length ≤ L := by rw [hL.1]; omega
    rcases hE : compileUML k L e (tmpBase k L) with ⟨ce, r, n'⟩
    obtain ⟨s₁, t₁, d₁, p₁, hex₁, hr₁, hp₁, hbf₁, hcp₁⟩ :=
      compileUML_sim hf env N envArr henv hNk Γ locals 0 L hL e (tmpBase k L) s
        hc hb hs
    simp only [hE] at hex₁ hr₁
    obtain ⟨henv₀, hsz₀, hfr₀, hpre₀, hloc₀, hidx₀⟩ := hs
    have hjidx : localReg k locals.size + k ≤ idxReg k L :=
      localReg_le_localReg hsz
    have hk : 0 < k := hf.limbs_pos
    have hjk : k + 2 ≤ localReg k locals.size := by simp only [localReg]; omega
    have hjtmp : localReg k locals.size + k ≤ tmpBase k L := localReg_le hsz
    simp only [compileStepML, hE]
    refine ⟨_, _, _, _, .seq hex₁ .mov, ⟨?_, ?_, hfr₀, ⟨?_, ?_⟩, ?_, ?_⟩, ?_, ?_, ?_⟩
    · rw [bufs_setReg, hbf₁]; exact henv₀
    · rw [Array.size_push]; omega
    · intro j hj
      rw [regs_setReg_ne _ _ (show 0 + j ≠ localReg k locals.size by omega),
        hp₁ _ (by omega)]
      exact hpre₀.modulus j hj
    · rw [regs_setReg_ne _ _ (show k + 1 ≠ localReg k locals.size by omega),
        hp₁ _ (by omega)]
      exact hpre₀.const
    · intro i hi
      rw [Array.size_push] at hi
      rcases Nat.lt_or_ge i locals.size with hlt | hge
      · have hli : localReg k i + k ≤ localReg k locals.size :=
          localReg_le_localReg hlt
        have hloci := hloc₀ i hlt
        rw [Array.getElem_push_lt hlt]
        rcases hv : locals[i] with x | u
        · rw [hv] at hloci
          intro j hj
          rw [regs_setReg_ne _ _ (show localReg k i + j ≠ localReg k locals.size by
              omega), hp₁ _ (by omega)]
          exact hloci j hj
        · rw [hv] at hloci
          show _ = encU u
          rw [regs_setReg_ne _ _ (show localReg k i ≠ localReg k locals.size by omega),
            hp₁ _ (by omega)]
          exact hloci
      · have hib : i = locals.size := by omega
        subst hib
        rw [Array.getElem_push_eq]
        show (s₁.setReg (localReg k locals.size) (s₁.regs r)).regs
          (localReg k locals.size) = encU (U64Expr.eval { env, locals, idx := 0 } e)
        rw [regs_setReg_self]
        exact hr₁
    · rw [regs_setReg_ne _ _ (show idxReg k L ≠ localReg k locals.size by omega),
        hp₁ _ (Nat.lt_of_lt_of_le (idxReg_lt k L) (Nat.le_refl _))]
      exact hidx₀
    · exact LocalsMatch_push_inr hL _
    · rw [bufs_setReg, hbf₁]
    · rw [caps_setReg, hcp₁]

/-- Simulation for the `let`-step list: the compiled steps run left to right,
extending the encoded context step by step. -/
theorem compileStepsML_sim :
    ∀ (steps : List (Step (F p))) (Γ : List VSort) (locals : Array (F p ⊕ UInt64))
      (L : ℕ) (s : State 64),
      LocalsMatch Γ locals →
      stepsCompilable Γ steps = true → steps.all (Step.envBound N) = true →
      locals.size + steps.length ≤ L →
      StateEncML k pv L envArr locals 0 (tmpBase k L) s →
      ∃ s' t d pp, Exec C (compileStepsML k L steps locals.size) s s' t d pp ∧
        StateEncML k pv L envArr (evalSteps env steps locals) 0 (tmpBase k L) s' ∧
        LocalsMatch (Γ ++ steps.map Step.sort) (evalSteps env steps locals) ∧
        s'.bufs = s.bufs ∧ s'.caps = s.caps
  | [], Γ, locals, L, s, hL, _, _, _, hs => by
    simp only [compileStepsML, List.map_nil, List.append_nil, evalSteps]
    exact ⟨s, 0, 0, 0, .skip, hs, hL, rfl, rfl⟩
  | st :: rest, Γ, locals, L, s, hL, hc, hb, hlen, hs => by
    simp only [stepsCompilable, Bool.and_eq_true] at hc
    simp only [List.all_cons, Bool.and_eq_true] at hb
    simp only [List.length_cons] at hlen
    obtain ⟨s₁, t₁, d₁, p₁, hex₁, hs₁, hL₁, hbf₁, hcp₁⟩ :=
      compileStepML_sim (C := C) hf env N envArr henv hNk Γ locals L hL (by omega)
        st s hc.1 hb.1 hs
    obtain ⟨s₂, t₂, d₂, p₂, hex₂, hs₂, hL₂, hbf₂, hcp₂⟩ :=
      compileStepsML_sim rest (Γ ++ [Step.sort st])
        (locals.push (stepValue env locals st)) L s₁ hL₁ hc.2 hb.2
        (by rw [Array.size_push]; omega) hs₁
    have hsz : (locals.push (stepValue env locals st)).size = locals.size + 1 :=
      Array.size_push ..
    rw [hsz] at hex₂
    have hΓ : (Γ ++ [Step.sort st]) ++ rest.map Step.sort
        = Γ ++ (st :: rest).map Step.sort := by simp
    rw [hΓ] at hL₂
    rw [← evalSteps_cons] at hs₂ hL₂
    exact ⟨s₂, _, _, _, .seq hex₁ hex₂, hs₂, hL₂,
      hbf₂.trans hbf₁, hcp₂.trans hcp₁⟩

/-! ### Output-code fold lemmas

`compileVML` emits one unrolled block per output element; these lemmas run the fold
over the generation-time element list, tracking the output buffer. All are stated with
an already-executed prefix `c₀` (instantiated with `.skip` at the top level) because
`List.foldl` accumulates code on the left. -/

/-- Fold lemma for `.lit` outputs. -/
theorem compileVML_lit_fold (Γ : List VSort) (locals : Array (F p ⊕ UInt64)) (L : ℕ)
    (hL : LocalsMatch Γ locals) :
    ∀ (l : List (FExpr (F p))) {c₀ : Stmt 64} {s s₀ : State 64} {t₀ : ℕ} {d₀ p₀ : ℤ},
      Exec C c₀ s s₀ t₀ d₀ p₀ →
      l.all (FExpr.compilable Γ) = true → l.all (FExpr.envBound N) = true →
      StateEncML k pv L envArr locals 0 (tmpBase k L) s₀ →
      (s₀.bufs 1).size + l.length * k ≤ s₀.caps 1 →
      ∃ s' t d pp,
        Exec C (l.foldl (fun c e =>
            c ;; (compileFML k L e (tmpBase k L)).1 ;;
              pushLimbs k (compileFML k L e (tmpBase k L)).2.1) c₀) s s' t d pp ∧
        s'.bufs 1 = s₀.bufs 1 ++
          (encFlat k (l.map fun e => FExpr.eval { env, locals } e)).toArray ∧
        StateEncML k pv L envArr locals 0 (tmpBase k L) s' ∧
        (∀ b, b ≠ 1 → s'.bufs b = s₀.bufs b) ∧ s'.caps = s₀.caps := by
  intro l
  induction l with
  | nil =>
    intro c₀ s s₀ t₀ d₀ p₀ hex₀ _ _ hs _
    exact ⟨s₀, t₀, d₀, p₀, hex₀, by simp, hs, fun _ _ => rfl, rfl⟩
  | cons e l ih =>
    intro c₀ s s₀ t₀ d₀ p₀ hex₀ hc hb hs hcap
    simp only [List.all_cons, Bool.and_eq_true] at hc hb
    simp only [List.length_cons] at hcap
    rw [show (l.length + 1) * k = l.length * k + k by ring] at hcap
    obtain ⟨s₁, t₁, d₁, p₁, hex₁, hr₁, hp₁, hbf₁, hcp₁⟩ :=
      compileFML_sim hf env N envArr henv hNk Γ locals 0 L hL e (tmpBase k L) s₀
        hc.1 hb.1 hs
    obtain ⟨s₂, t₂, d₂, p₂, hex₂, hout₂, hbo₂, hrg₂, hcp₂⟩ :=
      pushLimbs_exec (C := C) hr₁ (by rw [hbf₁, hcp₁]; omega)
    have hs₂ : StateEncML k pv L envArr locals 0 (tmpBase k L) s₂ :=
      StateEncML_frame hs (fun q hq => by rw [hrg₂]; exact hp₁ q hq)
        (by rw [hbo₂ 0 (by decide), hbf₁])
    obtain ⟨s', t', d', pp', hex', hout', hs', hbo', hcp'⟩ :=
      ih (.seq hex₀ (.seq hex₁ hex₂)) hc.2 hb.2 hs₂
        (by rw [hout₂, hcp₂, hcp₁, hbf₁]
            have hl : (s₀.bufs 1 ++ (encWords k
                (montVal k (FExpr.eval { env, locals } e))).toArray).size
                = (s₀.bufs 1).size + k := by simp [encWords_length]
            omega)
    refine ⟨s', t', d', pp', hex', ?_, hs', ?_, ?_⟩
    · rw [hout', hout₂, hbf₁, List.map_cons, encFlat_cons]
      exact append_toArray_assoc _ _ _
    · intro b hb1
      rw [hbo' b hb1, hbo₂ b hb1, hbf₁]
    · rw [hcp', hcp₂, hcp₁]

/-- Fold lemma for `.mapRange` outputs: each block points the index register at the
element index, evaluates the body there and pushes the result. -/
theorem compileVML_mapRange_fold (Γ : List VSort) (locals : Array (F p ⊕ UInt64))
    (L : ℕ) (hL : LocalsMatch Γ locals) (body : FExpr (F p))
    (hcb : FExpr.compilable Γ body = true) (hbb : FExpr.envBound N body = true) :
    ∀ (is : List ℕ) {c₀ : Stmt 64} {s s₀ : State 64} {t₀ : ℕ} {d₀ p₀ : ℤ} {j₀ : ℕ},
      Exec C c₀ s s₀ t₀ d₀ p₀ →
      StateEncML k pv L envArr locals j₀ (tmpBase k L) s₀ →
      (s₀.bufs 1).size + is.length * k ≤ s₀.caps 1 →
      ∃ s' t d pp j',
        Exec C (is.foldl (fun c i =>
            c ;; .imm (idxReg k L) (BitVec.ofNat 64 i) ;;
              (compileFML k L body (tmpBase k L)).1 ;;
              pushLimbs k (compileFML k L body (tmpBase k L)).2.1) c₀) s s' t d pp ∧
        s'.bufs 1 = s₀.bufs 1 ++
          (encFlat k (is.map fun i =>
            FExpr.eval { env, locals, idx := i } body)).toArray ∧
        StateEncML k pv L envArr locals j' (tmpBase k L) s' ∧
        (∀ b, b ≠ 1 → s'.bufs b = s₀.bufs b) ∧ s'.caps = s₀.caps := by
  intro is
  induction is with
  | nil =>
    intro c₀ s s₀ t₀ d₀ p₀ j₀ hex₀ hs _
    exact ⟨s₀, t₀, d₀, p₀, j₀, hex₀, by simp, hs, fun _ _ => rfl, rfl⟩
  | cons i is ih =>
    intro c₀ s s₀ t₀ d₀ p₀ j₀ hex₀ hs hcap
    simp only [List.length_cons] at hcap
    rw [show (is.length + 1) * k = is.length * k + k by ring] at hcap
    have hs₁ : StateEncML k pv L envArr locals i (tmpBase k L)
        (s₀.setReg (idxReg k L) (BitVec.ofNat 64 i)) :=
      StateEncML_setIdx hf.limbs_pos hs i
    obtain ⟨s₂, t₂, d₂, p₂, hex₂, hr₂, hp₂, hbf₂, hcp₂⟩ :=
      compileFML_sim hf env N envArr henv hNk Γ locals i L hL body (tmpBase k L) _
        hcb hbb hs₁
    obtain ⟨s₃, t₃, d₃, p₃, hex₃, hout₃, hbo₃, hrg₃, hcp₃⟩ :=
      pushLimbs_exec (C := C) hr₂ (by
        rw [hbf₂, hcp₂]; simp only [bufs_setReg, caps_setReg]; omega)
    have hs₃ : StateEncML k pv L envArr locals i (tmpBase k L) s₃ :=
      StateEncML_frame hs₁ (fun q hq => by rw [hrg₃]; exact hp₂ q hq)
        (by rw [hbo₃ 0 (by decide), hbf₂])
    obtain ⟨s', t', d', pp', j', hex', hout', hs', hbo', hcp'⟩ :=
      ih (.seq hex₀ (.seq .imm (.seq hex₂ hex₃))) hs₃
        (by rw [hout₃, hcp₃, hcp₂, hbf₂]
            simp only [bufs_setReg, caps_setReg]
            have hl : (s₀.bufs 1 ++ (encWords k
                (montVal k (FExpr.eval { env, locals, idx := i } body))).toArray).size
                = (s₀.bufs 1).size + k := by simp [encWords_length]
            omega)
    refine ⟨s', t', d', pp', j', hex', ?_, hs', ?_, ?_⟩
    · rw [hout', hout₃, hbf₂, bufs_setReg, List.map_cons, encFlat_cons]
      exact append_toArray_assoc _ _ _
    · intro b hb1
      rw [hbo' b hb1, hbo₃ b hb1, hbf₂, bufs_setReg]
    · rw [hcp', hcp₃, hcp₂, caps_setReg]

set_option linter.unusedSectionVars false in
/-- Fold lemma for `.envRange` outputs: each block loads one element's limbs from the
environment buffer and pushes them. -/
theorem compileVML_envRange_fold (locals : Array (F p ⊕ UInt64))
    (L : ℕ) (offset : ℕ) :
    ∀ (is : List ℕ), (∀ i ∈ is, offset + i < N) →
      ∀ {c₀ : Stmt 64} {s s₀ : State 64} {t₀ : ℕ} {d₀ p₀ : ℤ},
      Exec C c₀ s s₀ t₀ d₀ p₀ →
      StateEncML k pv L envArr locals 0 (tmpBase k L) s₀ →
      (s₀.bufs 1).size + is.length * k ≤ s₀.caps 1 →
      ∃ s' t d pp,
        Exec C (is.foldl (fun c i =>
            c ;; envLimbs k (tmpBase k L + 1) ((offset + i) * k) (tmpBase k L) ;;
              pushLimbs k (tmpBase k L + 1)) c₀) s s' t d pp ∧
        s'.bufs 1 = s₀.bufs 1 ++
          (encFlat k (is.map fun i => env.get (offset + i))).toArray ∧
        StateEncML k pv L envArr locals 0 (tmpBase k L) s' ∧
        (∀ b, b ≠ 1 → s'.bufs b = s₀.bufs b) ∧ s'.caps = s₀.caps := by
  intro is
  induction is with
  | nil =>
    intro _ c₀ s s₀ t₀ d₀ p₀ hex₀ hs _
    exact ⟨s₀, t₀, d₀, p₀, hex₀, by simp, hs, fun _ _ => rfl, rfl⟩
  | cons i is ih =>
    intro his c₀ s s₀ t₀ d₀ p₀ hex₀ hs hcap
    simp only [List.length_cons] at hcap
    rw [show (is.length + 1) * k = is.length * k + k by ring] at hcap
    have hoi : offset + i < N := his i (List.mem_cons_self ..)
    have hmul : (offset + i + 1) * k ≤ N * k := Nat.mul_le_mul_right k (by omega)
    have hexp : (offset + i + 1) * k = (offset + i) * k + k := by ring
    obtain ⟨s₁, t₁, d₁, p₁, hex₁, hval₁, hlow₁, hhigh₁, hbf₁, hcp₁⟩ :=
      loadLimbs_exec (C := C) (base := tmpBase k L + 1) (idx := (offset + i) * k)
        (sc := tmpBase k L) (by omega) k
        (show (offset + i) * k + k ≤ 2 ^ 64 by omega)
        (show (offset + i) * k + k ≤ (s₀.bufs 0).size by rw [hs.env, henv.1]; omega)
    have hr₁ : RegsEnc s₁ (tmpBase k L + 1) k (montVal k (env.get (offset + i))) := by
      intro j hj
      rw [hval₁ j hj, hs.env]
      exact henv.2 (offset + i) hoi j hj
    obtain ⟨s₂, t₂, d₂, p₂, hex₂, hout₂, hbo₂, hrg₂, hcp₂⟩ :=
      pushLimbs_exec (C := C) hr₁ (by rw [hbf₁, hcp₁]; omega)
    have hs₂ : StateEncML k pv L envArr locals 0 (tmpBase k L) s₂ :=
      StateEncML_frame hs
        (fun q hq => by rw [hrg₂, hlow₁ q (by omega) (by omega)])
        (by rw [hbo₂ 0 (by decide), hbf₁])
    obtain ⟨s', t', d', pp', hex', hout', hs', hbo', hcp'⟩ :=
      ih (fun j hj => his j (List.mem_cons_of_mem _ hj))
        (.seq hex₀ (.seq hex₁ hex₂)) hs₂
        (by rw [hout₂, hcp₂, hcp₁, hbf₁]
            have hl : (s₀.bufs 1 ++ (encWords k
                (montVal k (env.get (offset + i)))).toArray).size
                = (s₀.bufs 1).size + k := by simp [encWords_length]
            omega)
    refine ⟨s', t', d', pp', hex', ?_, hs', ?_, ?_⟩
    · rw [hout', hout₂, hbf₁, List.map_cons, encFlat_cons]
      exact append_toArray_assoc _ _ _
    · intro b hb1
      rw [hbo' b hb1, hbo₂ b hb1, hbf₁]
    · rw [hcp', hcp₂, hcp₁]

set_option linter.unusedSectionVars false in
/-- Fold lemma for `.bitsOf` outputs: with the canonical value at `a` and the
Montgomery forms of `0` and `1` at `W` and `W + k`, each block extracts one bit,
selects between the two constants and pushes the result. -/
theorem compileVML_bitsOf_fold (locals : Array (F p ⊕ UInt64))
    (L : ℕ) {a W : ℕ} (haW : a + k ≤ W) (hwL : tmpBase k L ≤ W) (x : F p) :
    ∀ (is : List ℕ) {c₀ : Stmt 64} {s s₀ : State 64} {t₀ : ℕ} {d₀ p₀ : ℤ},
      Exec C c₀ s s₀ t₀ d₀ p₀ →
      RegsEnc s₀ a k (ZMod.val x) → RegsEnc s₀ W k 0 →
      RegsEnc s₀ (W + k) k (2 ^ (64 * k) % p) →
      StateEncML k pv L envArr locals 0 (tmpBase k L) s₀ →
      (s₀.bufs 1).size + is.length * k ≤ s₀.caps 1 →
      ∃ s' t d pp,
        Exec C (is.foldl (fun c i =>
            c ;; bitLimb k a i (W + 2 * k) ;;
              selectLimbs k (W + 2 * k + 3) (W + k) W (bitOut (W + 2 * k))
                (W + 2 * k + 2) ;;
              pushLimbs k (W + 2 * k + 3)) c₀) s s' t d pp ∧
        s'.bufs 1 = s₀.bufs 1 ++
          (encFlat k (is.map fun i =>
            (FiniteField.fromNat (ZMod.val x >>> i % 2) : F p))).toArray ∧
        StateEncML k pv L envArr locals 0 (tmpBase k L) s' ∧
        (∀ b, b ≠ 1 → s'.bufs b = s₀.bufs b) ∧ s'.caps = s₀.caps := by
  intro is
  induction is with
  | nil =>
    intro c₀ s s₀ t₀ d₀ p₀ hex₀ _ _ _ hs _
    exact ⟨s₀, t₀, d₀, p₀, hex₀, by simp, hs, fun _ _ => rfl, rfl⟩
  | cons i is ih =>
    intro c₀ s s₀ t₀ d₀ p₀ hex₀ hxa hz ho hs hcap
    simp only [List.length_cons] at hcap
    rw [show (is.length + 1) * k = is.length * k + k by ring] at hcap
    obtain ⟨s₁, t₁, d₁, p₁, hex₁, hflag₁, hp₁, hbf₁, hcp₁⟩ :=
      bitLimb_exec (C := C) (k := k) (a := a) (i := i) (w := W + 2 * k)
        (by omega) (lt_trans (ZMod.val_lt x) hf.bound) hxa
    obtain ⟨s₂, t₂, d₂, p₂, hex₂, hsel₂, hp₂, hbf₂, hcp₂⟩ :=
      selectLimbs_exec (C := C) (k := k) (d := W + 2 * k + 3) (a := W + k) (b := W)
        (f := bitOut (W + 2 * k)) (sc := W + 2 * k + 2)
        ⟨by omega, by omega, by simp only [bitOut]; omega, by omega⟩
        (show (if (ZMod.val x).testBit i then 1 else 0) ≤ 1 by split <;> omega)
        (fun j hj => by rw [hp₁ _ (by omega)]; exact ho j hj)
        (fun j hj => by rw [hp₁ _ (by omega)]; exact hz j hj)
        hflag₁
    have hsel : RegsEnc s₂ (W + 2 * k + 3) k
        (montVal k (FiniteField.fromNat (ZMod.val x >>> i % 2) : F p)) := by
      rw [← montVal_bit k (ZMod.val x) i]
      exact hsel₂
    obtain ⟨s₃, t₃, d₃, p₃, hex₃, hout₃, hbo₃, hrg₃, hcp₃⟩ :=
      pushLimbs_exec (C := C) hsel (by rw [hbf₂, hbf₁, hcp₂, hcp₁]; omega)
    have hpres : ∀ q, q < W + 2 * k → s₃.regs q = s₀.regs q := fun q hq => by
      rw [hrg₃, hp₂ q (by omega), hp₁ q hq]
    have hs₃ : StateEncML k pv L envArr locals 0 (tmpBase k L) s₃ :=
      StateEncML_frame hs (fun q hq => hpres q (by omega))
        (by rw [hbo₃ 0 (by decide), hbf₂, hbf₁])
    obtain ⟨s', t', d', pp', hex', hout', hs', hbo', hcp'⟩ :=
      ih (.seq hex₀ (.seq hex₁ (.seq hex₂ hex₃)))
        (fun j hj => by rw [hpres _ (by omega)]; exact hxa j hj)
        (fun j hj => by rw [hpres _ (by omega)]; exact hz j hj)
        (fun j hj => by rw [hpres _ (by omega)]; exact ho j hj) hs₃
        (by rw [hout₃, hcp₃, hcp₂, hcp₁, hbf₂, hbf₁]
            have hl : (s₀.bufs 1 ++ (encWords k (montVal k
                (FiniteField.fromNat (ZMod.val x >>> i % 2) : F p))).toArray).size
                = (s₀.bufs 1).size + k := by simp [encWords_length]
            omega)
    refine ⟨s', t', d', pp', hex', ?_, hs', ?_, ?_⟩
    · rw [hout', hout₃, hbf₂, hbf₁, List.map_cons, encFlat_cons]
      exact append_toArray_assoc _ _ _
    · intro b hb1
      rw [hbo' b hb1, hbo₃ b hb1, hbf₂, hbf₁]
    · rw [hcp', hcp₃, hcp₂, hcp₁]

set_option linter.unusedSectionVars false in
/-- The list a `Vector.mapRange` flattens to. -/
theorem toList_mapRange {α : Type} (n : ℕ) (g : ℕ → α) :
    (Vector.mapRange n g).toList = (List.range n).map g := by
  refine List.ext_getElem (by simp) fun i h₁ h₂ => ?_
  simp [Vector.getElem_mapRange]

/-- Simulation for vector outputs: the compiled block appends exactly the reference
output's Montgomery limbs to the output buffer. -/
theorem compileVML_sim (Γ : List VSort) (locals : Array (F p ⊕ UInt64)) (L : ℕ)
    (hL : LocalsMatch Γ locals) :
    ∀ {n : ℕ} (v : VExpr (F p) n) (s : State 64),
      VExpr.compilable Γ v = true → VExpr.envBound N v = true →
      StateEncML k pv L envArr locals 0 (tmpBase k L) s →
      (s.bufs 1).size + n * k ≤ s.caps 1 →
      ∃ s' t d pp, Exec C (compileVML k L v) s s' t d pp ∧
        s'.bufs 1 = s.bufs 1 ++
          (encFlat k (VExpr.eval { env, locals } v).toList).toArray ∧
        StateEncML k pv L envArr locals 0 (tmpBase k L) s' ∧
        (∀ b, b ≠ 1 → s'.bufs b = s.bufs b) ∧ s'.caps = s.caps
  | _, .lit es, s, hc, hb, hs, hcap => by
    simp only [VExpr.compilable] at hc
    simp only [VExpr.envBound] at hb
    obtain ⟨s', t, d, pp, hex, hout, hs', hbo, hcp⟩ :=
      compileVML_lit_fold hf env N envArr henv hNk Γ locals L hL es.toList
        (.skip (s := s)) hc hb hs (by rw [Vector.length_toList]; exact hcap)
    refine ⟨s', t, d, pp, hex, ?_, hs', hbo, hcp⟩
    rw [hout]
    congr 2
    simp [VExpr.eval, Vector.toList_map]
  | _, .mapRange n body, s, hc, hb, hs, hcap => by
    simp only [VExpr.compilable] at hc
    simp only [VExpr.envBound] at hb
    obtain ⟨s₁, t, d, pp, j', hex, hout, hs₁, hbo, hcp⟩ :=
      compileVML_mapRange_fold hf env N envArr henv hNk Γ locals L hL body hc hb
        (List.range n) (.skip (s := s)) hs (by rw [List.length_range]; exact hcap)
    refine ⟨s₁.setReg (idxReg k L) 0, _, _, _, .seq hex .imm, ?_, ?_, ?_, ?_⟩
    · rw [bufs_setReg, hout]
      congr 2
      rw [show (VExpr.eval { env, locals } (VExpr.mapRange n body)).toList
          = (List.range n).map fun i =>
            FExpr.eval { env, locals, idx := i } body from by
        simp only [VExpr.eval]; exact toList_mapRange hf env N envArr henv hNk n _]
    · have := StateEncML_setIdx (pv := pv) hf.limbs_pos hs₁ 0
      simpa using this
    · intro b hb1
      rw [bufs_setReg]; exact hbo b hb1
    · rw [caps_setReg]; exact hcp
  | n, .envRange offset, s, hc, hb, hs, hcap => by
    simp only [VExpr.envBound, decide_eq_true_eq] at hb
    obtain ⟨s', t, d, pp, hex, hout, hs', hbo, hcp⟩ :=
      compileVML_envRange_fold hf env N envArr henv hNk locals L offset
        (List.range n) (fun i hi => by have := List.mem_range.mp hi; omega)
        (.skip (s := s)) hs (by rw [List.length_range]; exact hcap)
    refine ⟨s', t, d, pp, hex, ?_, hs', hbo, hcp⟩
    rw [hout]
    congr 2
    rw [show (VExpr.eval { env, locals } (VExpr.envRange (n := n) offset)).toList
        = (List.range n).map fun i => env.get (offset + i) from by
      simp only [VExpr.eval]; exact toList_mapRange hf env N envArr henv hNk n _]
  | n, .bitsOf x, s, hc, hb, hs, hcap => by
    simp only [VExpr.compilable] at hc
    simp only [VExpr.envBound] at hb
    have hΓ : Γ.length ≤ L := by rw [hL.1]; exact hs.size
    have hk : 0 < k := hf.limbs_pos
    rcases hE : compileFML k L x (tmpBase k L) with ⟨cx, rx, n₁⟩
    have hbd := compileFML_bounds k L hk hΓ x (tmpBase k L) hc (Nat.le_refl _)
    simp only [hE] at hbd
    obtain ⟨s₁, t₁, d₁, p₁, hex₁, hr₁, hp₁, hbf₁, hcp₁⟩ :=
      compileFML_sim hf env N envArr henv hNk Γ locals 0 L hL x (tmpBase k L) s
        hc hb hs
    simp only [hE] at hex₁ hr₁
    have hs₁ := StateEncML_mono hs hbd.1 hp₁ (by rw [hbf₁])
    have hfr₁ : k + 3 + L * k ≤ n₁ := by
      have := hs₁.frame; simp only [tmpBase] at this; exact this
    obtain ⟨s₂, t₂, d₂, p₂, hex₂, hr₂, hp₂, hbf₂, hcp₂⟩ :=
      leaveMont_field (C := C) (w := n₁) (a := rx) hk hf.two_lt hf.bound hf.const
        hs₁.pre (by omega) (by omega) hr₁
    have hmc : montMulConstOut k n₁ + k ≤ n₁ + montMulConstFrame k :=
      montMulConstOut_le k n₁
    obtain ⟨s₃, t₃, d₃, p₃, hex₃, hz₃, hlow₃, hhigh₃, hbf₃, hcp₃⟩ :=
      immLimbs_exec (C := C) (n₁ + montMulConstFrame k) 0 (s := s₂) k
    obtain ⟨s₄, t₄, d₄, p₄, hex₄, ho₄, hlow₄, hhigh₄, hbf₄, hcp₄⟩ :=
      immLimbs_exec (C := C) (n₁ + montMulConstFrame k + k)
        (2 ^ (64 * k) % FiniteField.size (F p)) (s := s₃) k
    have hpres₄ : ∀ q, q < n₁ + montMulConstFrame k → s₄.regs q = s₂.regs q :=
      fun q hq => by
        rw [hlow₄ q (Nat.lt_of_lt_of_le hq (Nat.le_add_right _ _)), hlow₃ q hq]
    have hxa : RegsEnc s₄ (montMulConstOut k n₁) k (ZMod.val
        (FExpr.eval { env, locals } x)) := fun j hj => by
      have hlt : montMulConstOut k n₁ + j < n₁ + montMulConstFrame k :=
        Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj _) hmc
      rw [hpres₄ (montMulConstOut k n₁ + j) hlt]; exact hr₂ j hj
    have hz : RegsEnc s₄ (n₁ + montMulConstFrame k) k 0 := fun j hj => by
      have hlt : n₁ + montMulConstFrame k + j < n₁ + montMulConstFrame k + k :=
        Nat.add_lt_add_left hj _
      rw [hlow₄ (n₁ + montMulConstFrame k + j) hlt]; exact hz₃ j hj
    have hs₄ : StateEncML k pv L envArr locals 0 (tmpBase k L) s₄ :=
      StateEncML_frame hs (fun q hq => by
        rw [hpres₄ q (show q < n₁ + montMulConstFrame k by omega),
          hp₂ q (show q < n₁ by omega), hp₁ q hq])
        (by rw [hbf₄, hbf₃, hbf₂, hbf₁])
    obtain ⟨s', t', d', pp', hex', hout', hs', hbo', hcp'⟩ :=
      compileVML_bitsOf_fold hf env N envArr henv hNk locals L hmc
        (show tmpBase k L ≤ n₁ + montMulConstFrame k by omega)
        (FExpr.eval { env, locals } x) (List.range n) (.skip (s := s₄)) hxa hz ho₄ hs₄
        (by rw [hbf₄, hbf₃, hbf₂, hbf₁, hcp₄, hcp₃, hcp₂, hcp₁, List.length_range]
            exact hcap)
    simp only [compileVML, hE]
    refine ⟨s', _, _, _,
      .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex'))), ?_, hs', ?_, ?_⟩
    · rw [hout', hbf₄, hbf₃, hbf₂, hbf₁]
      congr 2
      rw [show (VExpr.eval { env, locals } (VExpr.bitsOf (n := n) x)).toList
          = (List.range n).map fun i =>
            (FiniteField.fromNat (ZMod.val (FExpr.eval { env, locals } x) >>> i % 2)
              : F p) from by
        simp only [VExpr.eval]; exact toList_mapRange hf env N envArr henv hNk n _]
    · intro b hb1
      rw [hbo' b hb1, hbf₄, hbf₃, hbf₂, hbf₁]
    · rw [hcp', hcp₄, hcp₃, hcp₂, hcp₁]
  | _, .append a b, s, hc, hb, hs, hcap => by
    simp only [VExpr.compilable, Bool.and_eq_true] at hc
    simp only [VExpr.envBound, Bool.and_eq_true] at hb
    rw [show ∀ m n : ℕ, (m + n) * k = m * k + n * k from fun m n => by ring] at hcap
    obtain ⟨s₁, t₁, d₁, p₁, hex₁, hout₁, hs₁, hbo₁, hcp₁⟩ :=
      compileVML_sim Γ locals L hL a s hc.1 hb.1 hs (by omega)
    obtain ⟨s₂, t₂, d₂, p₂, hex₂, hout₂, hs₂, hbo₂, hcp₂⟩ :=
      compileVML_sim Γ locals L hL b s₁ hc.2 hb.2 hs₁
        (by rw [hout₁, hcp₁]
            simp only [Array.size_append, List.size_toArray, encFlat_length,
              Vector.length_toList]
            omega)
    refine ⟨s₂, _, _, _, .seq hex₁ hex₂, ?_, hs₂, ?_, ?_⟩
    · rw [hout₂, hout₁]
      rw [show (VExpr.eval { env, locals } (VExpr.append a b)).toList
          = (VExpr.eval { env, locals } a).toList
            ++ (VExpr.eval { env, locals } b).toList from by
        simp [VExpr.eval]]
      rw [encFlat_append]
      exact append_toArray_assoc _ _ _
    · intro bb hb1
      rw [hbo₂ bb hb1, hbo₁ bb hb1]
    · rw [hcp₂, hcp₁]

/-! ## The whole program -/

/-- **The multi-limb lowering simulates the witness IR.** For every compilable,
environment-bounded witness program, from any start state whose buffer `0` holds the
reference environment in Montgomery form, the emitted code has an execution ending
with buffer `1` holding the Montgomery limbs of `WitgenIR.eval`'s output.

Out-of-range buffer accesses have no `Exec` derivation, so exhibiting the execution
also proves memory safety. -/
theorem compileIRCodeML_sim {steps : List (Step (F p))} {m : ℕ} {out : VExpr (F p) m}
    (hcomp : WitgenIR.compilable (WitgenIR.ir steps out) = true)
    (hbound : WitgenIR.envBound N (WitgenIR.ir steps out) = true)
    {s : State 64} (hbuf : s.bufs 0 = envArr) :
    ∃ s' t d pp,
      Exec C (compileIRCodeML k p pv steps.length steps out) s s' t d pp ∧
      s'.bufs 1 = (encFlat k ((WitgenIR.ir steps out).eval env).toList).toArray := by
  simp only [WitgenIR.compilable, Bool.and_eq_true] at hcomp
  simp only [WitgenIR.envBound, Bool.and_eq_true] at hbound
  have hk : 0 < k := hf.limbs_pos
  set L := steps.length with hLdef
  -- the prelude
  obtain ⟨s₁, t₁, d₁, p₁, hex₁, hmod₁, hlow₁, hhigh₁, hbf₁, hcp₁⟩ :=
    immLimbs_exec (C := C) 0 p (s := s.allocBuf 1 (m * k)) (k + 1)
  have hpre : PreludeEnc p pv k
      ((s₁.setReg (k + 1) (BitVec.ofNat 64 pv)).setReg (idxReg k L) 0) :=
    ⟨fun j hj => by
        rw [regs_setReg_ne _ _ (show 0 + j ≠ idxReg k L by
            simp only [idxReg]; omega),
          regs_setReg_ne _ _ (show 0 + j ≠ k + 1 by omega)]
        exact hmod₁ j hj,
      by
        rw [regs_setReg_ne _ _ (show k + 1 ≠ idxReg k L by
            simp only [idxReg]; omega), regs_setReg_self]⟩
  have hLM : LocalsMatch ([] : List VSort) (#[] : Array (F p ⊕ UInt64)) :=
    ⟨rfl, fun i hi => absurd hi (by simp)⟩
  have hs₃ : StateEncML k pv L envArr (#[] : Array (F p ⊕ UInt64)) 0 (tmpBase k L)
      ((s₁.setReg (k + 1) (BitVec.ofNat 64 pv)).setReg (idxReg k L) 0) := by
    refine ⟨?_, by simp, Nat.le_refl _, hpre, fun i hi => absurd hi (by simp), ?_⟩
    · rw [bufs_setReg, bufs_setReg, hbf₁, bufs_allocBuf_ne _ _ (by decide)]
      exact hbuf
    · rw [regs_setReg_self]; rfl
  obtain ⟨s₄, t₄, d₄, p₄, hex₄, hs₄, hL₄, hbf₄, hcp₄⟩ :=
    compileStepsML_sim (C := C) hf env N envArr henv hNk steps [] #[] L _
      hLM hcomp.1 hbound.1 (by simp [hLdef]) hs₃
  have hcap₄ : (s₄.bufs 1).size + m * k ≤ s₄.caps 1 := by
    rw [hbf₄, hcp₄]
    simp only [caps_setReg, bufs_setReg, hbf₁, hcp₁, bufs_allocBuf_self,
      caps_allocBuf_self]
    simp
  obtain ⟨s₅, t₅, d₅, p₅, hex₅, hout₅, -, -, -⟩ :=
    compileVML_sim (C := C) hf env N envArr henv hNk (steps.map Step.sort)
      (evalSteps env steps #[]) L (by rw [List.nil_append] at hL₄; exact hL₄) out s₄
      hcomp.2 hbound.2 hs₄ hcap₄
  refine ⟨s₅, _, _, _,
    .seq .memAllocI (.seq (.seq hex₁ .imm) (.seq .imm (.seq hex₄ hex₅))), ?_⟩
  rw [hout₅, hbf₄]
  simp only [bufs_setReg, hbf₁, bufs_allocBuf_self, WitgenIR.eval]
  rw [Array.empty_append]

end Sim

/-! ## The checked entry point -/

section Entry

variable {C : CostModel} {p : ℕ} [Fact p.Prime]

/-- **The checked multi-limb entry point is correct.** For every witness program
`compileML` accepts, from any start state whose buffer `0` holds the reference
environment in Montgomery form, the emitted code has an execution ending with buffer
`1` holding the Montgomery limbs of the program's reference output. Together with
`compileML_timeLe` this is the pair a compiled witness program certifies: it computes
the right thing, in a number of steps the compiler names in advance. -/
theorem compileML_sim {N m : ℕ} {steps : List (Step (F p))} {out : VExpr (F p) m}
    {code : Stmt 64} (h : compileML N steps out = some code)
    (env : ProverEnvironment (F p)) (envArr : Array (Word 64))
    (henv : EnvEncML (limbCount p) env N envArr)
    {s : State 64} (hbuf : s.bufs 0 = envArr) :
    ∃ s' t d pp, Exec C code s s' t d pp ∧
      s'.bufs 1 = (encFlat (limbCount p)
        ((WitgenIR.ir steps out).eval env).toList).toArray := by
  obtain ⟨hcomp, hbound, hNk, -, hp2, hk0, hkb, hpinv, rfl⟩ := compileML_checks h
  rw [size_F] at hNk hp2 hk0 hkb hpinv ⊢
  have hf : FieldOkML p (montConstWord p) (limbCount p) :=
    ⟨hp2, hk0, lt_two_pow_limbCount p, hpinv, hkb⟩
  exact compileIRCodeML_sim hf env N envArr henv hNk hcomp hbound hbuf

end Entry

end Caliper.MultiLimb
