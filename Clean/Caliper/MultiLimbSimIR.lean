import Clean.Caliper.MultiLimbSimExpr
import Clean.Caliper.WitgenSimIR

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

end Sim

end Caliper.MultiLimb
