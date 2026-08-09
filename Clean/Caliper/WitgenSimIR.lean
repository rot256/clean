import Clean.Caliper.WitgenSimExpr
import Clean.Caliper.WitgenCost

/-!
# End-to-end simulation for the witgen compiler

Phase 3c of the witgen compiler correctness proof: the **program-level simulation**,
built on the scalar-expression simulation of `Clean/Caliper/WitgenSimExpr.lean`.

* `compileStep_sim` — executing one compiled `let`-step extends the state encoding:
  the step's value lands in its local register, and `LocalsMatch`/`StateEnc` extend
  by the reference-evaluated local.
* `compileSteps_sim` — the step list, by induction, threading `StateEnc`.
* `compileV_sim` — the compiled output code appends the *encoded reference output*
  (`VExpr.eval`, elementwise `encF`) to the output buffer `1`. The unrolled
  `mapRange` / `envRange` / `bitsOf` loops are handled by fold lemmas over the
  generation-time index list.
* `compileIR_sim` — the raw-compiler form: for every compilable, environment-bounded
  witness program, from any start state whose buffer `0` encodes the environment,
  the compiled code *has an execution* that ends with buffer `1` holding exactly the
  encoded `WitgenIR.eval` output. Since out-of-range buffer accesses have no `Exec`
  derivation, this existence theorem doubles as a memory-safety proof.
* `compile_sim` — **the headline**: the same statement about the checked entry point
  `compile`, with fewer hypotheses — `compile N ir = some code` already carries
  compilability, the environment bound, `N ≤ 2 ^ 64`, `m < 2 ^ 64`, *and* the
  field-size side conditions `2 < p` / `p * p ≤ 2 ^ 64` (via
  `compile_size_checks`), so only primality (`[Fact p.Prime]`) and the
  environment encoding remain.

Combined with phase 2 (`WitgenCost.lean`: exact static running time, space ≤ output
length + the certified register live set), this yields end-to-end corollaries like
`isZero_witgen_correct_155` and its circuit-anchored form
`isZero_witgen_correct_155_circuit`: the compiled witness program of the BabyBear
`Gadgets.IsZeroField.circuit` — extracted from the circuit itself, see
`isZeroCircuitIR_eq_testIsZero` in `WitgenCompile.lean` — computes the correct
encoded witness output in exactly 155 unit steps with peak live memory 16 words
(the output word plus the 15-register live set `isZero_regPeak`).

Everything is at the compiler's design point: word size `w = 64`, `F = F p` for a
prime `p` with `2 < p` and `p * p ≤ 2 ^ 64` (facts the internal lemmas take as
hypotheses and the checked-entry theorems derive from `compile … = some code`),
environment length `N ≤ 2 ^ 64`, and output length `m < 2 ^ 64`.
-/

namespace Caliper.WitgenCompile

open Witgen

/-! ## Step values and extension of the encoding relations -/

/-- The scalar value one `let`-step contributes to the locals array — exactly what
`evalSteps` pushes. -/
def stepValue {F : Type} [FiniteField F] (env : ProverEnvironment F)
    (locals : Array (F ⊕ UInt64)) : Step F → F ⊕ UInt64
  | .letF e => .inl (e.eval { env, locals })
  | .letU e => .inr (e.eval { env, locals })

/-- `evalSteps` peels off the head step as a `stepValue` push. -/
theorem evalSteps_cons {F : Type} [FiniteField F] (env : ProverEnvironment F)
    (st : Step F) (rest : List (Step F)) (locals : Array (F ⊕ UInt64)) :
    evalSteps env (st :: rest) locals
      = evalSteps env rest (locals.push (stepValue env locals st)) := by
  cases st <;> rfl

section StateHelpers

variable {p : ℕ}

/-- Pushing a field-sorted local extends `LocalsMatch` by a `.fld` sort. -/
theorem LocalsMatch_push_inl {Γ : List VSort} {locals : Array (F p ⊕ UInt64)}
    (hL : LocalsMatch Γ locals) (x : F p) :
    LocalsMatch (Γ ++ [VSort.fld]) (locals.push (.inl x)) := by
  obtain ⟨hlen, hget⟩ := hL
  refine ⟨by simp [hlen], fun i hi => ?_⟩
  rw [Array.size_push] at hi
  rcases Nat.lt_or_ge i locals.size with h | h
  · rw [List.getElem?_append_left (by omega), Array.getElem_push_lt h]
    exact hget i h
  · have his : i = locals.size := by omega
    subst his
    simp only [Array.getElem_push_eq]
    rw [← hlen, List.getElem?_concat_length]

/-- Pushing a u64-sorted local extends `LocalsMatch` by a `.u64` sort. -/
theorem LocalsMatch_push_inr {Γ : List VSort} {locals : Array (F p ⊕ UInt64)}
    (hL : LocalsMatch Γ locals) (u : UInt64) :
    LocalsMatch (Γ ++ [VSort.u64]) (locals.push (.inr u)) := by
  obtain ⟨hlen, hget⟩ := hL
  refine ⟨by simp [hlen], fun i hi => ?_⟩
  rw [Array.size_push] at hi
  rcases Nat.lt_or_ge i locals.size with h | h
  · rw [List.getElem?_append_left (by omega), Array.getElem_push_lt h]
    exact hget i h
  · have his : i = locals.size := by omega
    subst his
    simp only [Array.getElem_push_eq]
    rw [← hlen, List.getElem?_concat_length]

/-- `StateEnc` only constrains registers below `next` and buffer `0`: any state
agreeing there satisfies it too. (Generalizes `StateEnc_mono`, which requires all
buffers equal.) -/
theorem StateEnc_frame {envArr : Array (Word 64)} {Γ : List VSort}
    {locals : Array (F p ⊕ UInt64)} {idx L next : ℕ} {s s' : State 64}
    (hs : StateEnc envArr Γ locals idx L next s)
    (hregs : ∀ q, q < next → s'.regs q = s.regs q)
    (hbuf0 : s'.bufs 0 = s.bufs 0) :
    StateEnc envArr Γ locals idx L next s' := by
  obtain ⟨hbuf, h1, h2, h3, h4⟩ := hs
  refine ⟨hbuf0.trans hbuf, h1, h2, fun i hi => ?_, ?_⟩
  · rw [hregs i (by omega)]; exact h3 i hi
  · rw [hregs L (by omega)]; exact h4

/-- Writing the idx register re-points `StateEnc` at the new index. -/
theorem StateEnc_setIdx {envArr : Array (Word 64)} {Γ : List VSort}
    {locals : Array (F p ⊕ UInt64)} {idx L next : ℕ} {s : State 64}
    (hs : StateEnc envArr Γ locals idx L next s) (i : ℕ) :
    StateEnc envArr Γ locals i L next (s.setReg L (BitVec.ofNat 64 i)) := by
  obtain ⟨hbuf, h1, h2, h3, h4⟩ := hs
  refine ⟨hbuf, h1, h2, fun j hj => ?_, by rw [regs_setReg_self]⟩
  rw [regs_setReg_ne _ _ (show j ≠ L by omega)]
  exact h3 j hj

end StateHelpers

/-- The shift-and-mask block of the unrolled `bitsOf` computes the canonical word of
the field-valued bit. -/
private theorem encF_bitWord {p : ℕ} [Fact p.Prime] (hp2 : 2 < p)
    (hpw : p * p ≤ 2 ^ 64) (x : F p) {i : ℕ} (hi : i < 2 ^ 64) :
    encF x >>> (BitVec.ofNat 64 i).toNat &&& 1
      = encF ((ZMod.val x >>> i % 2 : ℕ) : F p) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hi, encF_toNat hpw, encF_toNat hpw, ZMod.val_natCast,
    Nat.mod_eq_of_lt (show ZMod.val x >>> i % 2 < p by omega),
    show (1 : Word 64).toNat = 1 from rfl, Nat.and_one_is_mod]

/-- Pushing onto an array prepends to the list still to be appended. -/
private theorem push_append_toArray {α : Type} (arr : Array α) (v : α) (l : List α) :
    (arr.push v) ++ l.toArray = arr ++ (v :: l).toArray := by
  simp

/-! ## The program-level simulation -/

section Sim

variable {C : CostModel} (p : ℕ) [Fact p.Prime] (hp2 : 2 < p) (hpw : p * p ≤ 2 ^ 64)
variable (env : ProverEnvironment (F p)) (N : ℕ) (envArr : Array (Word 64))
variable (henv : EnvEnc env N envArr) (hN : N ≤ 2 ^ 64)

include hp2 hpw henv hN

/-- **Simulation for one `let`-step**: the code `compileStep` emits for step number
`locals.size` runs from any state encoding the context (with temporaries free from
`L + 1`), and the resulting state encodes the context extended by the step's
reference value — the new local in its register, `LocalsMatch` and `StateEnc`
extended accordingly. Buffers and capacities are untouched. -/
theorem compileStep_sim (Γ : List VSort) (locals : Array (F p ⊕ UInt64)) (L : ℕ)
    (hL : LocalsMatch Γ locals) (hsz : locals.size < L) :
    ∀ (st : Step (F p)) (s : State 64),
      Step.compilable Γ st = true → Step.envBound N st = true →
      StateEnc envArr Γ locals 0 L (L + 1) s →
      ∃ s' t d pp, Exec C (compileStep (w := 64) L locals.size st) s s' t d pp ∧
        StateEnc envArr (Γ ++ [Step.sort st]) (locals.push (stepValue env locals st))
          0 L (L + 1) s' ∧
        LocalsMatch (Γ ++ [Step.sort st]) (locals.push (stepValue env locals st)) ∧
        s'.bufs = s.bufs ∧ s'.caps = s.caps
  | .letF e, s, hc, hb, hs => by
    simp only [Step.compilable] at hc
    simp only [Step.envBound] at hb
    rcases hE : compileF (w := 64) L e (L + 1) with ⟨ce, r, n'⟩
    obtain ⟨s₁, t₁, d₁, p₁, hex₁, hr₁, hp₁, hbf₁, hcp₁⟩ :=
      compileF_sim p hp2 hpw env N envArr henv hN Γ locals 0 L hL e (L + 1) s hc hb hs
    simp only [hE] at hex₁ hr₁
    obtain ⟨s₂, t₂, d₂, p₂, hex₂, hr₂, hb₂, hc₂⟩ :=
      freeTemps_exec (C := C) (L + 1) ((n' : ℕ) - (L + 1))
        (s₁.setReg locals.size (s₁.regs r))
    obtain ⟨hbuf, h1, h2, h3, h4⟩ := hs
    simp only [compileStep, hE]
    refine ⟨_, _, _, _, .seq hex₁ (.seq .mov hex₂), ⟨?_, ?_, h2, fun i hi => ?_, ?_⟩,
      ?_, ?_, ?_⟩
    · rw [hb₂, bufs_setReg, hbf₁]; exact hbuf
    · rw [Array.size_push]; omega
    · rw [Array.size_push] at hi
      rcases Nat.lt_or_ge i locals.size with hlt | hge
      · rw [hr₂, regs_setReg_ne _ _ (show i ≠ locals.size by omega),
          hp₁ i (by omega), Array.getElem_push_lt hlt]
        exact h3 i hlt
      · have : i = locals.size := by omega
        subst this
        rw [hr₂, regs_setReg_self]
        simp only [stepValue, Array.getElem_push_eq, encLocal]
        exact hr₁
    · rw [hr₂, regs_setReg_ne _ _ (show L ≠ locals.size by omega), hp₁ L (by omega)]
      exact h4
    · exact LocalsMatch_push_inl hL _
    · rw [hb₂, bufs_setReg, hbf₁]
    · rw [hc₂, caps_setReg, hcp₁]
  | .letU e, s, hc, hb, hs => by
    simp only [Step.compilable] at hc
    simp only [Step.envBound] at hb
    rcases hE : compileU (w := 64) L e (L + 1) with ⟨ce, r, n'⟩
    obtain ⟨s₁, t₁, d₁, p₁, hex₁, hr₁, hp₁, hbf₁, hcp₁⟩ :=
      compileU_sim p hp2 hpw env N envArr henv hN Γ locals 0 L hL e (L + 1) s hc hb hs
    simp only [hE] at hex₁ hr₁
    obtain ⟨s₂, t₂, d₂, p₂, hex₂, hr₂, hb₂, hc₂⟩ :=
      freeTemps_exec (C := C) (L + 1) ((n' : ℕ) - (L + 1))
        (s₁.setReg locals.size (s₁.regs r))
    obtain ⟨hbuf, h1, h2, h3, h4⟩ := hs
    simp only [compileStep, hE]
    refine ⟨_, _, _, _, .seq hex₁ (.seq .mov hex₂), ⟨?_, ?_, h2, fun i hi => ?_, ?_⟩,
      ?_, ?_, ?_⟩
    · rw [hb₂, bufs_setReg, hbf₁]; exact hbuf
    · rw [Array.size_push]; omega
    · rw [Array.size_push] at hi
      rcases Nat.lt_or_ge i locals.size with hlt | hge
      · rw [hr₂, regs_setReg_ne _ _ (show i ≠ locals.size by omega),
          hp₁ i (by omega), Array.getElem_push_lt hlt]
        exact h3 i hlt
      · have : i = locals.size := by omega
        subst this
        rw [hr₂, regs_setReg_self]
        simp only [stepValue, Array.getElem_push_eq, encLocal]
        exact hr₁
    · rw [hr₂, regs_setReg_ne _ _ (show L ≠ locals.size by omega), hp₁ L (by omega)]
      exact h4
    · exact LocalsMatch_push_inr hL _
    · rw [hb₂, bufs_setReg, hbf₁]
    · rw [hc₂, caps_setReg, hcp₁]

/-- **Simulation for the `let`-step list**: the compiled steps run left to right,
extending the encoded context step by step, and the final state encodes the fully
evaluated locals (`evalSteps`). Buffers and capacities are untouched. -/
theorem compileSteps_sim :
    ∀ (steps : List (Step (F p))) (Γ : List VSort) (locals : Array (F p ⊕ UInt64))
      (L : ℕ) (s : State 64),
      LocalsMatch Γ locals →
      stepsCompilable Γ steps = true → steps.all (Step.envBound N) = true →
      locals.size + steps.length ≤ L →
      StateEnc envArr Γ locals 0 L (L + 1) s →
      ∃ s' t d pp, Exec C (compileSteps (w := 64) L steps locals.size) s s' t d pp ∧
        StateEnc envArr (Γ ++ steps.map Step.sort) (evalSteps env steps locals)
          0 L (L + 1) s' ∧
        LocalsMatch (Γ ++ steps.map Step.sort) (evalSteps env steps locals) ∧
        s'.bufs = s.bufs ∧ s'.caps = s.caps
  | [], Γ, locals, L, s, hL, _, _, _, hs => by
    simp only [compileSteps, List.map_nil, List.append_nil, evalSteps]
    exact ⟨s, 0, 0, 0, .skip, hs, hL, rfl, rfl⟩
  | st :: rest, Γ, locals, L, s, hL, hc, hb, hlen, hs => by
    simp only [stepsCompilable, Bool.and_eq_true] at hc
    simp only [List.all_cons, Bool.and_eq_true] at hb
    simp only [List.length_cons] at hlen
    obtain ⟨s₁, t₁, d₁, p₁, hex₁, hs₁, hL₁, hbf₁, hcp₁⟩ :=
      compileStep_sim p hp2 hpw env N envArr henv hN Γ locals L hL (by omega)
        st s hc.1 hb.1 hs
    obtain ⟨s₂, t₂, d₂, p₂, hex₂, hs₂, hL₂, hbf₂, hcp₂⟩ :=
      compileSteps_sim rest (Γ ++ [Step.sort st])
        (locals.push (stepValue env locals st)) L s₁ hL₁ hc.2 hb.2
        (by rw [Array.size_push]; omega) hs₁
    have hsz : (locals.push (stepValue env locals st)).size = locals.size + 1 :=
      Array.size_push ..
    rw [hsz] at hex₂
    have hΓ : (Γ ++ [Step.sort st]) ++ rest.map Step.sort
        = Γ ++ (st :: rest).map Step.sort := by
      simp
    rw [hΓ, ← evalSteps_cons] at hs₂ hL₂
    exact ⟨s₂, _, _, _, .seq hex₁ hex₂, hs₂, hL₂,
      hbf₂.trans hbf₁, hcp₂.trans hcp₁⟩

/-! ### Output-code fold lemmas

`compileV` emits one unrolled block per output element; these lemmas run the fold
over the generation-time element list, tracking the output buffer's contents. All are
stated with an already-executed prefix `c₀` (instantiated with `.skip` at the top
level) because `List.foldl` accumulates code on the left. -/

/-- Fold lemma for `.lit` outputs: each block computes one element (temporaries from
`L + 1`) and pushes its canonical word. -/
private theorem compileV_lit_fold (Γ : List VSort) (locals : Array (F p ⊕ UInt64))
    (L : ℕ) (hL : LocalsMatch Γ locals) :
    ∀ (l : List (FExpr (F p))) {c₀ : Stmt 64} {s s₀ : State 64} {t₀ : ℕ} {d₀ p₀ : ℤ},
      Exec C c₀ s s₀ t₀ d₀ p₀ →
      l.all (FExpr.compilable Γ) = true → l.all (FExpr.envBound N) = true →
      StateEnc envArr Γ locals 0 L (L + 1) s₀ →
      (s₀.bufs 1).size + l.length ≤ s₀.caps 1 →
      ∃ s' t d pp,
        Exec C (l.foldl (fun c e =>
            c ;; (compileF (w := 64) L e (L + 1)).1 ;;
              .memPush 1 (compileF (w := 64) L e (L + 1)).2.1 ;;
              freeTemps (L + 1)
                (((compileF (w := 64) L e (L + 1)).2.2 : ℕ) - (L + 1))) c₀) s s' t d pp ∧
        s'.bufs 1 = s₀.bufs 1 ++
          (l.map fun e => encF (FExpr.eval { env, locals } e)).toArray ∧
        StateEnc envArr Γ locals 0 L (L + 1) s' ∧
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
    obtain ⟨s₁, t₁, d₁, p₁, hex₁, hr₁, hp₁, hbf₁, hcp₁⟩ :=
      compileF_sim p hp2 hpw env N envArr henv hN Γ locals 0 L hL e (L + 1) s₀
        hc.1 hb.1 hs
    have hpush : (s₁.bufs 1).size < s₁.caps 1 := by
      rw [hbf₁, hcp₁]; omega
    have hs₂ : StateEnc envArr Γ locals 0 L (L + 1)
        (s₁.setBuf 1 ((s₁.bufs 1).push (s₁.regs (compileF (w := 64) L e (L + 1)).2.1))) :=
      StateEnc_frame (StateEnc_frame hs hp₁ (by rw [hbf₁])) (fun _ _ => rfl)
        (bufs_setBuf_ne _ _ (by decide))
    obtain ⟨s₃, t₃, d₃, p₃, hexF, hrF, hbF, hcF⟩ :=
      freeTemps_exec (C := C) (L + 1)
        (((compileF (w := 64) L e (L + 1)).2.2 : ℕ) - (L + 1))
        (s₁.setBuf 1 ((s₁.bufs 1).push (s₁.regs (compileF (w := 64) L e (L + 1)).2.1)))
    obtain ⟨s', t', d', pp', hex', hout', hs', hbo', hcp'⟩ :=
      ih (.seq hex₀ (.seq hex₁ (.seq (.memPush hpush) hexF))) hc.2 hb.2
        (StateEnc_frame hs₂ (fun q _ => by rw [hrF]) (by rw [hbF]))
        (by rw [hbF, hcF, bufs_setBuf_self, Array.size_push, caps_setBuf, hbf₁, hcp₁]
            omega)
    refine ⟨s', t', d', pp', hex', ?_, hs', ?_, ?_⟩
    · rw [hout', hbF, bufs_setBuf_self, hbf₁, hr₁, List.map_cons]
      exact push_append_toArray _ _ _
    · intro b hb1
      rw [hbo' b hb1, hbF, bufs_setBuf_ne _ _ hb1, hbf₁]
    · rw [hcp', hcF, caps_setBuf, hcp₁]

/-- Fold lemma for `.mapRange` outputs: each block sets the idx register `L` to the
element index, computes the body at that index, and pushes the result. The final idx
value is existential (the trailing `.imm L 0` of `compileV` resets it). -/
private theorem compileV_mapRange_fold (Γ : List VSort) (locals : Array (F p ⊕ UInt64))
    (L : ℕ) (hL : LocalsMatch Γ locals) (body : FExpr (F p))
    (hcb : FExpr.compilable Γ body = true) (hbb : FExpr.envBound N body = true) :
    ∀ (is : List ℕ) {c₀ : Stmt 64} {s s₀ : State 64} {t₀ : ℕ} {d₀ p₀ : ℤ} {j₀ : ℕ},
      Exec C c₀ s s₀ t₀ d₀ p₀ →
      StateEnc envArr Γ locals j₀ L (L + 1) s₀ →
      (s₀.bufs 1).size + is.length ≤ s₀.caps 1 →
      ∃ s' t d pp j',
        Exec C (is.foldl (fun c i =>
            c ;; (.imm L (BitVec.ofNat 64 i) ;; (compileF (w := 64) L body (L + 1)).1) ;;
              .memPush 1 (compileF (w := 64) L body (L + 1)).2.1 ;;
              freeTemps (L + 1)
                (((compileF (w := 64) L body (L + 1)).2.2 : ℕ) - (L + 1))) c₀)
          s s' t d pp ∧
        s'.bufs 1 = s₀.bufs 1 ++
          (is.map fun i => encF (FExpr.eval { env, locals, idx := i } body)).toArray ∧
        StateEnc envArr Γ locals j' L (L + 1) s' ∧
        (∀ b, b ≠ 1 → s'.bufs b = s₀.bufs b) ∧ s'.caps = s₀.caps := by
  intro is
  induction is with
  | nil =>
    intro c₀ s s₀ t₀ d₀ p₀ j₀ hex₀ hs _
    exact ⟨s₀, t₀, d₀, p₀, j₀, hex₀, by simp, hs, fun _ _ => rfl, rfl⟩
  | cons i is ih =>
    intro c₀ s s₀ t₀ d₀ p₀ j₀ hex₀ hs hcap
    simp only [List.length_cons] at hcap
    have hs₁ : StateEnc envArr Γ locals i L (L + 1)
        (s₀.setReg L (BitVec.ofNat 64 i)) := StateEnc_setIdx hs i
    obtain ⟨s₂, t₂, d₂, p₂, hex₂, hr₂, hp₂, hbf₂, hcp₂⟩ :=
      compileF_sim p hp2 hpw env N envArr henv hN Γ locals i L hL body (L + 1) _
        hcb hbb hs₁
    have hpush : (s₂.bufs 1).size < s₂.caps 1 := by
      rw [hbf₂, hcp₂]; simp only [bufs_setReg, caps_setReg]; omega
    have hs₃ : StateEnc envArr Γ locals i L (L + 1)
        (s₂.setBuf 1 ((s₂.bufs 1).push
          (s₂.regs (compileF (w := 64) L body (L + 1)).2.1))) :=
      StateEnc_frame (StateEnc_frame hs₁ hp₂ (by rw [hbf₂])) (fun _ _ => rfl)
        (bufs_setBuf_ne _ _ (by decide))
    obtain ⟨s₃, t₃, d₃, p₃, hexF, hrF, hbF, hcF⟩ :=
      freeTemps_exec (C := C) (L + 1)
        (((compileF (w := 64) L body (L + 1)).2.2 : ℕ) - (L + 1))
        (s₂.setBuf 1 ((s₂.bufs 1).push
          (s₂.regs (compileF (w := 64) L body (L + 1)).2.1)))
    obtain ⟨s', t', d', pp', j', hex', hout', hs', hbo', hcp'⟩ :=
      ih (.seq hex₀ (.seq (.seq .imm hex₂) (.seq (.memPush hpush) hexF)))
        (StateEnc_frame hs₃ (fun q _ => by rw [hrF]) (by rw [hbF]))
        (by rw [hbF, hcF, bufs_setBuf_self, Array.size_push, caps_setBuf, hbf₂, hcp₂]
            simp only [bufs_setReg, caps_setReg]; omega)
    refine ⟨s', t', d', pp', j', hex', ?_, hs', ?_, ?_⟩
    · rw [hout', hbF, bufs_setBuf_self, hbf₂, bufs_setReg, hr₂, List.map_cons]
      exact push_append_toArray _ _ _
    · intro b hb1
      rw [hbo' b hb1, hbF, bufs_setBuf_ne _ _ hb1, hbf₂, bufs_setReg]
    · rw [hcp', hcF, caps_setBuf, hcp₂, caps_setReg]

omit [Fact (Nat.Prime p)] hp2 hpw in
/-- Fold lemma for `.envRange` outputs: each block acquires its two temporaries,
loads the static environment index (temporary `L + 1`), reads the environment
buffer `0` (temporary `L + 2`), pushes the cell — which by `EnvEnc` is the
canonical word of the reference environment value — and releases the two
temporaries again (`freeTemps (L + 1) 2`). -/
private theorem compileV_envRange_fold (Γ : List VSort) (locals : Array (F p ⊕ UInt64))
    (L : ℕ) (offset : ℕ) :
    ∀ (is : List ℕ), (∀ i ∈ is, offset + i < N) →
      ∀ {c₀ : Stmt 64} {s s₀ : State 64} {t₀ : ℕ} {d₀ p₀ : ℤ},
      Exec C c₀ s s₀ t₀ d₀ p₀ →
      StateEnc envArr Γ locals 0 L (L + 1) s₀ →
      (s₀.bufs 1).size + is.length ≤ s₀.caps 1 →
      ∃ s' t d pp,
        Exec C (is.foldl (fun c i =>
            c ;; (.regAlloc (L + 1) ;; .imm (L + 1) (BitVec.ofNat 64 (offset + i)) ;;
                .regAlloc (L + 2) ;; .memLoad (L + 2) 0 (L + 1)) ;;
              .memPush 1 (L + 2) ;; freeTemps (L + 1) 2) c₀) s s' t d pp ∧
        s'.bufs 1 = s₀.bufs 1 ++
          (is.map fun i => encF (env.get (offset + i))).toArray ∧
        StateEnc envArr Γ locals 0 L (L + 1) s' ∧
        (∀ b, b ≠ 1 → s'.bufs b = s₀.bufs b) ∧ s'.caps = s₀.caps := by
  intro is
  induction is with
  | nil =>
    intro _ c₀ s s₀ t₀ d₀ p₀ hex₀ hs _
    exact ⟨s₀, t₀, d₀, p₀, hex₀, by simp, hs, fun _ _ => rfl, rfl⟩
  | cons i is ih =>
    intro his c₀ s s₀ t₀ d₀ p₀ hex₀ hs hcap
    simp only [List.length_cons] at hcap
    have hoi : offset + i < N := his i (List.mem_cons_self ..)
    -- the read block's states
    set sI := ((s₀.setRegAlloc (L + 1) true).setReg (L + 1)
      (BitVec.ofNat 64 (offset + i))).setRegAlloc (L + 2) true with hsIdef
    have hidx : (sI.regs (L + 1)).toNat = offset + i := by
      rw [hsIdef, regs_setRegAlloc, regs_setReg_self, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega)]
    have hget : (sI.regs (L + 1)).toNat < (sI.bufs 0).size := by
      rw [hidx, hsIdef, bufs_setRegAlloc, bufs_setReg, bufs_setRegAlloc, hs.1, henv.1]
      exact hoi
    set sL := sI.setReg (L + 2) ((sI.bufs 0)[(sI.regs (L + 1)).toNat]'hget) with hsLdef
    have hval : sL.regs (L + 2) = encF (env.get (offset + i)) := by
      rw [hsLdef, regs_setReg_self, ← getElem!_pos]
      rw [hidx, hsIdef, bufs_setRegAlloc, bufs_setReg, bufs_setRegAlloc, hs.1]
      exact henv.2 _ hoi
    have hpushOk : (sL.bufs 1).size < sL.caps 1 := by
      rw [hsLdef, bufs_setReg, caps_setReg, hsIdef, bufs_setRegAlloc, bufs_setReg,
        bufs_setRegAlloc, caps_setRegAlloc, caps_setReg, caps_setRegAlloc]
      omega
    set sP := sL.setBuf 1 ((sL.bufs 1).push (sL.regs (L + 2))) with hsPdef
    obtain ⟨s₃, t₃, d₃, p₃, hexF, hrF, hbF, hcF⟩ :=
      freeTemps_exec (C := C) (L + 1) 2 sP
    have hpres : ∀ q, q < L + 1 → sP.regs q = s₀.regs q := by
      intro q hq
      rw [hsPdef, regs_setBuf, hsLdef, regs_setReg_ne _ _ (show q ≠ L + 2 by omega),
        hsIdef, regs_setRegAlloc, regs_setReg_ne _ _ (show q ≠ L + 1 by omega),
        regs_setRegAlloc]
    have hbP : ∀ b, b ≠ 1 → sP.bufs b = s₀.bufs b := by
      intro b hb1
      rw [hsPdef, bufs_setBuf_ne _ _ hb1, hsLdef, bufs_setReg, hsIdef,
        bufs_setRegAlloc, bufs_setReg, bufs_setRegAlloc]
    have hcP : sP.caps = s₀.caps := by
      rw [hsPdef, caps_setBuf, hsLdef, caps_setReg, hsIdef, caps_setRegAlloc,
        caps_setReg, caps_setRegAlloc]
    have hbP1 : sP.bufs 1 = (s₀.bufs 1).push (encF (env.get (offset + i))) := by
      rw [hsPdef, bufs_setBuf_self, hval, hsLdef, bufs_setReg, hsIdef,
        bufs_setRegAlloc, bufs_setReg, bufs_setRegAlloc]
    obtain ⟨s', t', d', pp', hex', hout', hs', hbo', hcp'⟩ :=
      ih (fun j hj => his j (List.mem_cons_of_mem _ hj))
        (.seq hex₀ (.seq (.seq .regAlloc (.seq .imm (.seq .regAlloc (.memLoad hget))))
          (.seq (.memPush hpushOk) hexF)))
        (StateEnc_frame hs (fun q hq => by rw [hrF]; exact hpres q hq)
          (by rw [hbF]; exact hbP 0 (by decide)))
        (by rw [hbF, hcF, hbP1, hcP, Array.size_push]; omega)
    refine ⟨s', t', d', pp', hex', ?_, hs', ?_, ?_⟩
    · rw [hout', hbF, hbP1, List.map_cons]
      exact push_append_toArray _ _ _
    · intro b hb1
      rw [hbo' b hb1, hbF, hbP b hb1]
    · rw [hcp', hcF, hcP]

omit henv hN in
/-- Fold lemma for `.bitsOf` outputs: with the decomposed value's canonical word held
in register `rx`, each block acquires its four temporaries, shifts, masks and pushes
one bit as a field element, and releases the four again (`freeTemps n₁ 4`).
Registers `rx` and everything below `L + 1` survive. -/
private theorem compileV_bitsOf_fold (Γ : List VSort) (locals : Array (F p ⊕ UInt64))
    (L : ℕ) {rx n₁ : ℕ} (hrx : LT.lt (α := ℕ) rx n₁) (hLn : L + 1 ≤ n₁) (v : F p) :
    ∀ (is : List ℕ), (∀ i ∈ is, i < 2 ^ 64) →
      ∀ {c₀ : Stmt 64} {s s₀ : State 64} {t₀ : ℕ} {d₀ p₀ : ℤ},
      Exec C c₀ s s₀ t₀ d₀ p₀ →
      s₀.regs rx = encF v →
      StateEnc envArr Γ locals 0 L (L + 1) s₀ →
      (s₀.bufs 1).size + is.length ≤ s₀.caps 1 →
      ∃ s' t d pp,
        Exec C (is.foldl (fun c i =>
            c ;; (.regAlloc n₁ ;; .imm n₁ (BitVec.ofNat 64 i) ;;
                .regAlloc (n₁ + 1) ;; .bin .shr (n₁ + 1) rx n₁ ;;
                .regAlloc (n₁ + 2) ;; .imm (n₁ + 2) 1 ;;
                .regAlloc (n₁ + 3) ;; .bin .and (n₁ + 3) (n₁ + 1) (n₁ + 2)) ;;
              .memPush 1 (n₁ + 3) ;; freeTemps n₁ 4) c₀) s s' t d pp ∧
        s'.bufs 1 = s₀.bufs 1 ++
          (is.map fun i => encF ((ZMod.val v >>> i % 2 : ℕ) : F p)).toArray ∧
        StateEnc envArr Γ locals 0 L (L + 1) s' ∧
        (∀ b, b ≠ 1 → s'.bufs b = s₀.bufs b) ∧ s'.caps = s₀.caps := by
  intro is
  induction is with
  | nil =>
    intro _ c₀ s s₀ t₀ d₀ p₀ hex₀ _ hs _
    exact ⟨s₀, t₀, d₀, p₀, hex₀, by simp, hs, fun _ _ => rfl, rfl⟩
  | cons i is ih =>
    intro his c₀ s s₀ t₀ d₀ p₀ hex₀ hrv hs hcap
    simp only [List.length_cons] at hcap
    have hi : i < 2 ^ 64 := his i (List.mem_cons_self ..)
    -- name the eight register-touching steps
    set s₁ := (s₀.setRegAlloc n₁ true).setReg n₁ (BitVec.ofNat 64 i) with hs₁def
    set s₂ := (s₁.setRegAlloc (n₁ + 1) true).setReg (n₁ + 1)
      (BinOp.eval .shr ((s₁.setRegAlloc (n₁ + 1) true).regs rx)
        ((s₁.setRegAlloc (n₁ + 1) true).regs n₁)) with hs₂def
    set s₃ := (s₂.setRegAlloc (n₁ + 2) true).setReg (n₁ + 2) 1 with hs₃def
    set s₄ := (s₃.setRegAlloc (n₁ + 3) true).setReg (n₁ + 3)
      (BinOp.eval .and ((s₃.setRegAlloc (n₁ + 3) true).regs (n₁ + 1))
        ((s₃.setRegAlloc (n₁ + 3) true).regs (n₁ + 2))) with hs₄def
    have hval : s₄.regs (n₁ + 3) = encF ((ZMod.val v >>> i % 2 : ℕ) : F p) := by
      rw [hs₄def, regs_setReg_self, regs_setRegAlloc, hs₃def,
        regs_setReg_ne _ _ (show n₁ + 1 ≠ n₁ + 2 by omega), regs_setRegAlloc,
        regs_setReg_self, hs₂def, regs_setReg_self, regs_setRegAlloc, hs₁def,
        regs_setReg_ne _ _ (show rx ≠ n₁ by omega), regs_setRegAlloc,
        regs_setReg_self, hrv]
      simp only [BinOp.eval]
      exact encF_bitWord hp2 hpw v hi
    have hp4 : ∀ q, q < L + 1 → s₄.regs q = s₀.regs q := by
      intro q hq
      rw [hs₄def, regs_setReg_ne _ _ (show q ≠ n₁ + 3 by omega), regs_setRegAlloc,
        hs₃def, regs_setReg_ne _ _ (show q ≠ n₁ + 2 by omega), regs_setRegAlloc,
        hs₂def, regs_setReg_ne _ _ (show q ≠ n₁ + 1 by omega), regs_setRegAlloc,
        hs₁def, regs_setReg_ne _ _ (show q ≠ n₁ by omega), regs_setRegAlloc]
    have hb4 : s₄.bufs = s₀.bufs := by
      rw [hs₄def, bufs_setReg, bufs_setRegAlloc, hs₃def, bufs_setReg,
        bufs_setRegAlloc, hs₂def, bufs_setReg, bufs_setRegAlloc, hs₁def,
        bufs_setReg, bufs_setRegAlloc]
    have hc4 : s₄.caps = s₀.caps := by
      rw [hs₄def, caps_setReg, caps_setRegAlloc, hs₃def, caps_setReg,
        caps_setRegAlloc, hs₂def, caps_setReg, caps_setRegAlloc, hs₁def,
        caps_setReg, caps_setRegAlloc]
    have hpush : (s₄.bufs 1).size < s₄.caps 1 := by
      rw [hb4, hc4]; omega
    set sP := s₄.setBuf 1 ((s₄.bufs 1).push (s₄.regs (n₁ + 3))) with hsPdef
    obtain ⟨s₅, t₅, d₅, p₅, hexF, hrF, hbF, hcF⟩ := freeTemps_exec (C := C) n₁ 4 sP
    have hrx5 : s₅.regs rx = encF v := by
      rw [hrF, hsPdef, regs_setBuf, hs₄def,
        regs_setReg_ne _ _ (show rx ≠ n₁ + 3 by omega), regs_setRegAlloc, hs₃def,
        regs_setReg_ne _ _ (show rx ≠ n₁ + 2 by omega), regs_setRegAlloc, hs₂def,
        regs_setReg_ne _ _ (show rx ≠ n₁ + 1 by omega), regs_setRegAlloc, hs₁def,
        regs_setReg_ne _ _ (show rx ≠ n₁ by omega), regs_setRegAlloc]
      exact hrv
    obtain ⟨s', t', d', pp', hex', hout', hs', hbo', hcp'⟩ :=
      ih (fun j hj => his j (List.mem_cons_of_mem _ hj))
        (.seq hex₀ (.seq (.seq .regAlloc (.seq .imm (.seq .regAlloc (.seq .bin
            (.seq .regAlloc (.seq .imm (.seq .regAlloc .bin)))))))
          (.seq (.memPush hpush) hexF)))
        hrx5
        (StateEnc_frame hs
          (fun q hq => by rw [hrF, hsPdef, regs_setBuf]; exact hp4 q hq)
          (by rw [hbF, hsPdef, bufs_setBuf_ne _ _ (show (0:ℕ) ≠ 1 by omega), hb4]))
        (by rw [hbF, hcF, hsPdef, bufs_setBuf_self, Array.size_push, caps_setBuf,
              hb4, hc4]
            omega)
    refine ⟨s', t', d', pp', hex', ?_, hs', ?_, ?_⟩
    · rw [hout', hbF, hsPdef, bufs_setBuf_self, hb4, hval, List.map_cons]
      exact push_append_toArray _ _ _
    · intro b hb1
      rw [hbo' b hb1, hbF, hsPdef, bufs_setBuf_ne _ _ hb1, hb4]
    · rw [hcp', hcF, hsPdef, caps_setBuf, hc4]

/-- **Simulation for vector outputs**: the code `compileV` emits for a compilable,
environment-bounded `VExpr` runs from any state encoding the context (idx `0`,
temporaries from `L + 1`) with enough reserved output capacity, and appends exactly
the encoded reference output (`VExpr.eval`, elementwise `encF`) to buffer `1`. The
state encoding survives, no other buffer changes, and capacities are untouched. -/
theorem compileV_sim (Γ : List VSort) (locals : Array (F p ⊕ UInt64)) (L : ℕ)
    (hL : LocalsMatch Γ locals) :
    ∀ {n : ℕ} (v : VExpr (F p) n) (s : State 64),
      VExpr.compilable Γ v = true → VExpr.envBound N v = true → n ≤ 2 ^ 64 →
      StateEnc envArr Γ locals 0 L (L + 1) s →
      (s.bufs 1).size + n ≤ s.caps 1 →
      ∃ s' t d pp, Exec C (compileV (w := 64) L v) s s' t d pp ∧
        s'.bufs 1 = s.bufs 1 ++
          (Vector.map encF (VExpr.eval { env, locals } v)).toArray ∧
        StateEnc envArr Γ locals 0 L (L + 1) s' ∧
        (∀ b, b ≠ 1 → s'.bufs b = s.bufs b) ∧ s'.caps = s.caps
  | _, .lit es, s, hc, hb, _hn, hs, hcap => by
    simp only [VExpr.compilable] at hc
    simp only [VExpr.envBound] at hb
    obtain ⟨s', t, d, pp, hex, hout, hs', hbo, hcp⟩ :=
      compileV_lit_fold p hp2 hpw env N envArr henv hN Γ locals L hL es.toList
        (.skip (s := s)) hc hb hs (by rw [Vector.length_toList]; exact hcap)
    refine ⟨s', t, d, pp, hex, ?_, hs', hbo, hcp⟩
    rw [hout]
    congr 1
    apply Array.ext
    · simp
    · intro i h₁ h₂
      simp [VExpr.eval]
  | _, .mapRange n body, s, hc, hb, _hn, hs, hcap => by
    simp only [VExpr.compilable] at hc
    simp only [VExpr.envBound] at hb
    obtain ⟨s₁, t, d, pp, j', hex, hout, hs₁, hbo, hcp⟩ :=
      compileV_mapRange_fold p hp2 hpw env N envArr henv hN Γ locals L hL body hc hb
        (List.range n) (.skip (s := s)) hs (by rw [List.length_range]; exact hcap)
    refine ⟨s₁.setReg L 0, _, _, _, .seq hex .imm, ?_, ?_, ?_, ?_⟩
    · rw [bufs_setReg, hout]
      congr 1
      apply Array.ext
      · simp
      · intro i h₁ h₂
        simp [VExpr.eval, Vector.getElem_mapRange]
    · have := StateEnc_setIdx hs₁ 0
      simpa using this
    · intro b hb1
      rw [bufs_setReg]; exact hbo b hb1
    · rw [caps_setReg]; exact hcp
  | n, .envRange offset, s, hc, hb, _hn, hs, hcap => by
    simp only [VExpr.envBound, decide_eq_true_eq] at hb
    obtain ⟨s', t, d, pp, hex, hout, hs', hbo, hcp⟩ :=
      compileV_envRange_fold p env N envArr henv hN Γ locals L offset
        (List.range n) (fun i hi => by have := List.mem_range.mp hi; omega)
        (.skip (s := s)) hs (by rw [List.length_range]; exact hcap)
    refine ⟨s', t, d, pp, hex, ?_, hs', hbo, hcp⟩
    rw [hout]
    congr 1
    apply Array.ext
    · simp
    · intro i h₁ h₂
      simp [VExpr.eval, Vector.getElem_mapRange]
  | n, .bitsOf x, s, hc, hb, hn, hs, hcap => by
    simp only [VExpr.compilable] at hc
    simp only [VExpr.envBound] at hb
    rcases hE : compileF (w := 64) L x (L + 1) with ⟨cx, rx, n₁⟩
    have hbd := compileF_bounds L (Nat.le_trans (Nat.le_of_eq hL.1) hs.2.1) x (L + 1)
      hc (Nat.lt_succ_self L)
    simp only [hE] at hbd
    obtain ⟨s₁, t₁, d₁, p₁, hex₁, hr₁, hp₁, hbf₁, hcp₁⟩ :=
      compileF_sim p hp2 hpw env N envArr henv hN Γ locals 0 L hL x (L + 1) s hc hb hs
    simp only [hE] at hex₁ hr₁
    obtain ⟨s', t, d, pp, hex₂, hout, hs', hbo, hcp⟩ :=
      compileV_bitsOf_fold p hp2 hpw envArr (Γ := Γ) (locals := locals) L
        (rx := rx) (n₁ := n₁) hbd.2 hbd.1 (FExpr.eval { env, locals } x)
        (List.range n) (fun i hi => by have := List.mem_range.mp hi; omega)
        (.skip (s := s₁)) hr₁ (StateEnc_frame hs hp₁ (by rw [hbf₁]))
        (by rw [hbf₁, hcp₁, List.length_range]; exact hcap)
    obtain ⟨s₆, t₆, d₆, p₆, hexF, hrF, hbF, hcF⟩ :=
      freeTemps_exec (C := C) (L + 1) ((n₁ : ℕ) - (L + 1)) s'
    simp only [compileV, hE]
    refine ⟨s₆, _, _, _, .seq hex₁ (.seq hex₂ hexF), ?_, ?_, ?_, ?_⟩
    · rw [hbF, hout, hbf₁]
      congr 1
      apply Array.ext
      · simp
      · intro i h₁ h₂
        simp [VExpr.eval, Vector.getElem_mapRange]
    · exact StateEnc_frame hs' (fun q _ => by rw [hrF]) (by rw [hbF])
    · intro b hb1
      rw [hbF, hbo b hb1, hbf₁]
    · rw [hcF, hcp, hcp₁]
  | _, .append a b, s, hc, hb, hn, hs, hcap => by
    simp only [VExpr.compilable, Bool.and_eq_true] at hc
    simp only [VExpr.envBound, Bool.and_eq_true] at hb
    obtain ⟨s₁, t₁, d₁, p₁, hex₁, hout₁, hs₁, hbo₁, hcp₁⟩ :=
      compileV_sim Γ locals L hL a s hc.1 hb.1 (by omega) hs (by omega)
    obtain ⟨s₂, t₂, d₂, p₂, hex₂, hout₂, hs₂, hbo₂, hcp₂⟩ :=
      compileV_sim Γ locals L hL b s₁ hc.2 hb.2 (by omega) hs₁
        (by rw [hout₁, hcp₁, Array.size_append, Vector.size_toArray]; omega)
    refine ⟨s₂, _, _, _, .seq hex₁ hex₂, ?_, hs₂, ?_, ?_⟩
    · rw [hout₂, hout₁]
      simp [VExpr.eval, Array.append_assoc]
    · intro bb hb1
      rw [hbo₂ bb hb1, hbo₁ bb hb1]
    · rw [hcp₂, hcp₁]

/-- **End-to-end simulation and memory safety for compiled witness programs.**

For every compilable, environment-bounded witness program, from *any* start state
whose buffer `0` encodes the reference environment, the compiled code has an
execution that terminates with the output buffer `1` holding exactly the encoded
reference output `WitgenIR.eval` (elementwise canonical words `encF`).

Since out-of-range buffer accesses have no `Exec` derivation, exhibiting this
execution also proves the compiled code memory-safe. Together with phase 2, the
execution's time is exactly the syntactic constant `code.staticTime C`
(`compileIR_time_eq`) and its memory peak is at most `m` (`compileIR_space_le`). -/
theorem compileIR_sim {steps : List (Step (F p))} {m : ℕ} {out : VExpr (F p) m}
    {code : Stmt 64}
    (hcode : compileIR (w := 64) steps.length (WitgenIR.ir steps out) = some code)
    (hcomp : WitgenIR.compilable (WitgenIR.ir steps out) = true)
    (hbound : WitgenIR.envBound N (WitgenIR.ir steps out) = true)
    (hm : m < 2 ^ 64) {s : State 64} (hbuf : s.bufs 0 = envArr) :
    ∃ s' t d pp, Exec C code s s' t d pp ∧
      s'.bufs 1 = (Vector.map encF ((WitgenIR.ir steps out).eval env)).toArray := by
  simp only [compileIR, compileIRCode, Option.some.injEq] at hcode
  subst hcode
  simp only [WitgenIR.compilable, Bool.and_eq_true] at hcomp
  simp only [WitgenIR.envBound, Bool.and_eq_true] at hbound
  -- the state after the preamble (`memAllocI 1 m`, `imm L 0`)
  have hLM : LocalsMatch ([] : List VSort) (#[] : Array (F p ⊕ UInt64)) :=
    ⟨rfl, fun i hi => absurd hi (by simp)⟩
  obtain ⟨sA, tA, dA, pA, hexA, hrA, hbA, hcA⟩ :=
    allocRegs_exec (C := C) (steps.length + 1) (s.allocBuf 1 m)
  have hs₃ : StateEnc envArr ([] : List VSort) (#[] : Array (F p ⊕ UInt64)) 0
      steps.length (steps.length + 1) (sA.setReg steps.length 0) := by
    refine ⟨?_, by simp, by omega, fun i hi => absurd hi (by simp), ?_⟩
    · rw [bufs_setReg, hbA, bufs_allocBuf_ne _ _ (show (0:ℕ) ≠ 1 by omega)]
      exact hbuf
    · rw [regs_setReg_self]; rfl
  obtain ⟨s₄, t₄, d₄, p₄, hex₄, hs₄, hL₄, hbf₄, hcp₄⟩ :=
    compileSteps_sim p hp2 hpw env N envArr henv hN steps [] #[] steps.length _
      hLM hcomp.1 hbound.1 (by simp) hs₃
  rw [List.nil_append] at hs₄ hL₄
  have hcap₄ : (s₄.bufs 1).size + m ≤ s₄.caps 1 := by
    rw [hbf₄, hcp₄]
    simp only [bufs_setReg, caps_setReg]
    rw [hbA, hcA]
    simp only [bufs_allocBuf_self, caps_allocBuf_self]
    simp
  obtain ⟨s₅, t₅, d₅, p₅, hex₅, hout₅, _, _, _⟩ :=
    compileV_sim p hp2 hpw env N envArr henv hN (steps.map Step.sort)
      (evalSteps env steps #[]) steps.length hL₄ out s₄ hcomp.2 hbound.2
      (le_of_lt hm) hs₄ hcap₄
  obtain ⟨s₆, t₆, d₆, p₆, hexF, hrF, hbF, hcF⟩ :=
    freeTemps_exec (C := C) 0 (steps.length + 1) s₅
  refine ⟨s₆, _, _, _,
    .seq .memAllocI (.seq hexA (.seq .imm (.seq hex₄ (.seq hex₅ hexF)))), ?_⟩
  rw [hbF, hout₅, hbf₄]
  simp only [bufs_setReg]
  rw [hbA]
  simp only [bufs_allocBuf_self, WitgenIR.eval]
  rw [Array.empty_append]

omit hp2 hpw hN in
/-- **The checked-entry end-to-end theorem.** For every witness program the checked
entry point accepts — `compile N ir = some code`, which already carries
compilability, the environment bound, `N ≤ 2 ^ 64`, `m < 2 ^ 64` *and* the
field-size side conditions `2 < p`, `p * p ≤ 2 ^ 64` (`compile_size_checks`) —
from *any* start state whose buffer `0` encodes the reference environment, the
compiled code has an execution that terminates with the output buffer `1` holding
exactly the encoded IR reference output `WitgenIR.irEval` (elementwise canonical
words `encF`). On `.ir` programs `irEval` is `eval` definitionally, so this is the
familiar statement; on `.certified` programs the packed equivalence proof
transports it to the native closure itself — stated explicitly as
`compile_sim_certified` below.

Exhibiting the execution also proves memory safety; by phase 2 its time is exactly
`code.staticTime C` (`compile_time_eq`) and its memory peak at most `m`
(`compile_space_le`). The only remaining field hypothesis is primality
(`[Fact p.Prime]`) — the one side condition that cannot be checked at generation
time; callers no longer supply `2 < p` or `p * p ≤ 2 ^ 64`. -/
theorem compile_sim {m : ℕ} {ir : WitgenIR (F p) m} {code : Stmt 64}
    (hcode : compile N ir = some code) {s : State 64} (hbuf : s.bufs 0 = envArr) :
    ∃ s' t d pp, Exec C code s s' t d pp ∧
      s'.bufs 1 = (Vector.map encF (ir.irEval env)).toArray := by
  obtain ⟨-, -, hN', hm, hp2, hpw⟩ := compile_checks hcode
  rw [size_F] at hp2 hpw
  obtain ⟨steps, out, heval, hcomp, hbound, hIR⟩ := compile_toCompileIR hcode
  rw [heval]
  exact compileIR_sim p hp2 hpw env N envArr henv hN' hIR hcomp hbound hm hbuf

omit hp2 hpw hN in
/-- **The certified-native corollary: the machine provably computes the native
closure's output.** For a certified witness program — a native closure `f` bundled
with an IR reimplementation and an equivalence proof — every `compile`-accepted code
has an execution ending with the output buffer holding exactly the encoded output
**of `f` itself**: `compile_sim` gives the IR reference output, and the packed
equivalence rewrites it to `f env`. This is the guarantee a bare `.native f` can
never have; the certified form buys it at the price of one equivalence proof. -/
theorem compile_sim_certified {m : ℕ} {f : ProverEnvironment (F p) → Vector (F p) m}
    {steps : List (Step (F p))} {out : VExpr (F p) m}
    {h : ∀ e, f e = (WitgenIR.ir steps out).eval e} {code : Stmt 64}
    (hcode : compile N (WitgenIR.certified f steps out h) = some code)
    {s : State 64} (hbuf : s.bufs 0 = envArr) :
    ∃ s' t d pp, Exec C code s s' t d pp ∧
      s'.bufs 1 = (Vector.map encF (f env)).toArray := by
  obtain ⟨s', t, d, pp, hex, hout⟩ := compile_sim p env N envArr henv hcode hbuf
  refine ⟨s', t, d, pp, hex, ?_⟩
  rw [hout, show (WitgenIR.certified f steps out h).irEval env = f env from (h env).symm]

end Sim

/-! ## The headline corollary: BabyBear `IsZeroField`, end to end -/

/-- **The end-to-end headline for the BabyBear `IsZeroField` witness program**:
from every start state whose buffer `0` encodes the environment, the compiled
program `isZeroCompiled` has an execution that

* terminates with buffer `1` holding the **correct encoded witness output**
  (`testIsZero.eval env`, elementwise canonical words),
* in **exactly 155 unit-cost steps** (in particular far below `2 ^ 40`), and
* with **peak live memory at most 16 words** — the one output word plus the
  certified 15-register live set (`isZero_regPeak`).

Exhibiting the execution also proves memory safety (out-of-range accesses have no
`Exec` derivation). Determinism (`Exec.deterministic`) makes these the costs and the
output of *every* execution of `isZeroCompiled` from such a state.

Everything goes through the checked entry point: `isZeroCompiled` is defined via
`compile`, whose checks (`compile_testIsZero` at `N = 1`, generalized to any
`0 < N ≤ 2 ^ 64` here) feed `compile_sim`, `compile_time_eq` and
`compile_space_le`. -/
theorem isZero_witgen_correct_155 {env : ProverEnvironment (F pBabybear)}
    {N : ℕ} {envArr : Array (Word 64)} {s : State 64}
    (henv : EnvEnc env N envArr) (hN0 : 0 < N) (hN : N ≤ 2 ^ 64)
    (hbuf : s.bufs 0 = envArr) :
    ∃ s' d pp, Exec .unit isZeroCompiled s s' 155 d pp ∧
      s'.bufs 1 = (Vector.map encF (testIsZero.eval env)).toArray ∧
      pp ≤ 16 := by
  have hbound : WitgenIR.envBound N testIsZero = true := by
    simp [testIsZero, WitgenIR.envBound, VExpr.envBound, FExpr.envBound,
      BExpr.envBound, Expression.envBound, hN0]
  have hcode : compile N testIsZero = some isZeroCompiled :=
    (compile_eq_compileIR_of_checks (by native_decide) hbound hN
      (by norm_num) (by native_decide) (by native_decide)).trans compileIR_testIsZero
  obtain ⟨s', t, d, pp, hex, hout⟩ :=
    compile_sim (C := .unit) pBabybear env N envArr henv hcode hbuf
  have ht : t = 155 := by
    rw [compile_time_eq hcode hex, isZeroCompiled_staticTime_unit]
  have hpp : pp ≤ 16 := by
    have := (compile_space_le hcode hex).2
    rw [isZero_regPeak] at this
    omega
  exact ⟨s', d, pp, ht ▸ hex, hout, hpp⟩

/-- The `< 2 ^ 40` phrasing of the headline: an execution computing the correct
encoded witness output exists, and its time is below `2 ^ 40` (it is exactly 155). -/
theorem isZero_witgen_correct_lt_2_40 {env : ProverEnvironment (F pBabybear)}
    {N : ℕ} {envArr : Array (Word 64)} {s : State 64}
    (henv : EnvEnc env N envArr) (hN0 : 0 < N) (hN : N ≤ 2 ^ 64)
    (hbuf : s.bufs 0 = envArr) :
    ∃ s' t d pp, Exec .unit isZeroCompiled s s' t d pp ∧
      s'.bufs 1 = (Vector.map encF (testIsZero.eval env)).toArray ∧
      t < 2 ^ 40 ∧ pp < 2 ^ 40 := by
  obtain ⟨s', d, pp, hex, hout, hpp⟩ :=
    isZero_witgen_correct_155 henv hN0 hN hbuf
  exact ⟨s', 155, d, pp, hex, hout, by omega, by omega⟩

/-- **The circuit-anchored headline**: the same statement with the witness program
*derived from the Clean circuit* rather than named as a test fixture. The full
derivation chain, every link machine-checked:

1. **circuit → IR**: Clean circuits embed their witness generators structurally;
   `isZeroCircuitIR` (`WitgenCompile.lean`) is the payload of the first witness
   operation of `Gadgets.IsZeroField.circuit` at input `var ⟨0⟩`, extracted by
   `FlatOperation.witnessOperations`, and `isZeroCircuitIR = testIsZero` holds
   definitionally (`isZeroCircuitIR_eq_testIsZero`);
2. **IR → code**: the checked entry point accepts it and emits `isZeroCompiled`
   (`compile_testIsZero`, generalized over `N` inside `isZero_witgen_correct_155`);
3. **code → 155 steps, correct output**: every execution takes exactly 155 unit
   steps and ends with buffer `1` holding the encoded `WitgenIR.eval` output, with
   peak memory ≤ 16 words — output word + certified register live set
   (`compile_sim` + `compile_time_eq` + `compile_space_le`).

The circuit's only other witness generator is the trivial `<==` copy for its output
`b` (`isZeroCircuit_witnessIRs` lists both, and that they are all of them). -/
theorem isZero_witgen_correct_155_circuit {env : ProverEnvironment (F pBabybear)}
    {N : ℕ} {envArr : Array (Word 64)} {s : State 64}
    (henv : EnvEnc env N envArr) (hN0 : 0 < N) (hN : N ≤ 2 ^ 64)
    (hbuf : s.bufs 0 = envArr) :
    ∃ s' d pp, Exec .unit isZeroCompiled s s' 155 d pp ∧
      s'.bufs 1 = (Vector.map encF (isZeroCircuitIR.eval env)).toArray ∧
      pp ≤ 16 := by
  rw [isZeroCircuitIR_eq_testIsZero]
  exact isZero_witgen_correct_155 henv hN0 hN hbuf

/-! ## The certified-native headline, instantiated

`isZeroCertified` (`WitgenCompile.lean`) is the `IsZeroField` witness written as an
ordinary Lean closure (`isZeroNative`), certified against the `testIsZero` IR
program. The corollary below is `compile_sim_certified` + phase 2 at that instance:
the machine provably computes **the native closure's own output** — in exactly 155
unit steps, with peak memory ≤ 16 words. -/

/-- **The certified-native headline**: from every start state whose buffer `0`
encodes the environment, the code compiled from `isZeroCertified` (which is
`isZeroCompiled`, `compile_isZeroCertified`) has an execution that terminates with
buffer `1` holding the encoded output of the **native closure** `isZeroNative`, in
**exactly 155 unit steps**, with **peak live memory at most 16 words**. -/
theorem isZeroCertified_witgen_correct_155 {env : ProverEnvironment (F pBabybear)}
    {N : ℕ} {envArr : Array (Word 64)} {s : State 64}
    (henv : EnvEnc env N envArr) (hN0 : 0 < N) (hN : N ≤ 2 ^ 64)
    (hbuf : s.bufs 0 = envArr) :
    ∃ s' d pp, Exec .unit isZeroCompiled s s' 155 d pp ∧
      s'.bufs 1 = (Vector.map encF (isZeroNative env)).toArray ∧
      pp ≤ 16 := by
  obtain ⟨s', d, pp, hex, hout, hpp⟩ := isZero_witgen_correct_155 henv hN0 hN hbuf
  refine ⟨s', d, pp, hex, ?_, hpp⟩
  rw [hout, ← isZeroNative_eq_testIsZero]

end Caliper.WitgenCompile
