import Clean.Caliper.MultiLimbIR
import Clean.Caliper.WitgenCompile

/-!
# The multi-limb entry point

`compileML` is to the multi-limb lowering what `compile` is to the single-word one: it
runs every generation-time check and returns `none` if any fails, so the emitted code
is only ever produced under conditions the proofs assume.

The checks split in two. The program-side ones are the same as `compile`'s —
compilability, the environment bound, and the two size bounds that keep indices inside
their 64-bit immediates. The environment bound is `N * k ≤ 2 ^ 64` rather than
`N ≤ 2 ^ 64`: an element takes `k` words, so it is the *word* index that has to fit.
The field-side ones are `fieldOkML`: the modulus is odd and above two, it needs at
least one limb, its limb count leaves the inversion's iteration budget inside a word,
and the computed Montgomery constant passes its own congruence.

Nothing here bounds the field from above. `compile` needs `p² ≤ 2 ^ 64` and so refuses
BN254; `fieldOkML pBN254` is `true`.

## What a successful compile certifies

`compileML_timeLe`: every execution of the emitted code takes at most
`irCostML k m steps out` unit steps, a number the compiler computes from the program
and the modulus without running anything. `compileML_underBudget` is the form a budget
claim takes — `witgen < 2 ^ 40` and the like — with the comparison decided at
generation time.

`compileML_sim` (in `MultiLimbSimIR.lean`) is the correctness half: the emitted code
has an execution ending with the output buffer holding the Montgomery limbs of
`WitgenIR.eval`'s output.
-/

namespace Caliper.MultiLimb

open Caliper Witgen Caliper.WitgenCompile

variable {F : Type} [instF : FiniteField F]

/-- The field-side checks, all decided at generation time. `montConstOk` is what keeps
the untrusted Hensel lifting out of the trusted path. -/
def fieldOkML (p : ℕ) : Bool :=
  decide (2 < p) && decide (0 < limbCount p) &&
    decide (128 * limbCount p < 2 ^ 64) && montConstOk p (montConstWord p)

/-- The checked multi-limb entry point. Returns `some code` exactly when every
generation-time check passes. -/
def compileML (N : ℕ) {m : ℕ} (steps : List (Step F)) (out : VExpr F m) :
    Option (Stmt 64) :=
  if WitgenIR.compilable (WitgenIR.ir steps out)
      && WitgenIR.envBound N (WitgenIR.ir steps out)
      && decide (N * limbCount (FiniteField.size F) ≤ 2 ^ 64) && decide (m < 2 ^ 64)
      && fieldOkML (FiniteField.size F) then
    some (compileIRCodeML (limbCount (FiniteField.size F)) (FiniteField.size F)
      (montConstWord (FiniteField.size F)) steps.length steps out)
  else none

/-- Destructuring a successful compile: the checks held, and the code is the one
`irCostML` prices. -/
theorem compileML_checks {N m : ℕ} {steps : List (Step F)} {out : VExpr F m}
    {code : Stmt 64} (h : compileML N steps out = some code) :
    WitgenIR.compilable (WitgenIR.ir steps out) = true ∧
      WitgenIR.envBound N (WitgenIR.ir steps out) = true ∧
      N * limbCount (FiniteField.size F) ≤ 2 ^ 64 ∧ m < 2 ^ 64 ∧
      2 < FiniteField.size F ∧
      0 < limbCount (FiniteField.size F) ∧
      128 * limbCount (FiniteField.size F) < 2 ^ 64 ∧
      (FiniteField.size F * montConstWord (FiniteField.size F) + 1) % 2 ^ 64 = 0 ∧
      code = compileIRCodeML (limbCount (FiniteField.size F)) (FiniteField.size F)
        (montConstWord (FiniteField.size F)) steps.length steps out := by
  simp only [compileML] at h
  split at h
  · rename_i hcond
    simp only [fieldOkML, Bool.and_eq_true, decide_eq_true_eq] at hcond
    exact ⟨hcond.1.1.1.1, hcond.1.1.1.2, hcond.1.1.2, hcond.1.2,
      hcond.2.1.1.1, hcond.2.1.1.2, hcond.2.1.2, montConstOk_spec hcond.2.2,
      (Option.some_inj.mp h).symm⟩
  · exact absurd h (by simp)

/-- **The running time of compiled witgen is bounded, at every field the checks
accept.** Every execution of the emitted code takes at most `irCostML` unit steps — a
number computed from the program and the modulus, without running anything. -/
theorem compileML_timeLe {N m : ℕ} {steps : List (Step F)} {out : VExpr F m}
    {code : Stmt 64} (h : compileML N steps out = some code) :
    TimeLe CostModel.unit code
      (irCostML (limbCount (FiniteField.size F)) m steps out) := by
  obtain ⟨-, -, -, -, -, hk0, hk, -, rfl⟩ := compileML_checks h
  obtain ⟨k', hk'⟩ : ∃ k', limbCount (FiniteField.size F) = k' + 1 :=
    ⟨limbCount (FiniteField.size F) - 1, by omega⟩
  rw [hk'] at hk ⊢
  exact compileIRCodeML_timeLe hk steps out

/-- The shape a budget claim takes: the compiler's own cost function is compared to
the budget at generation time, and the comparison transfers to every execution. -/
theorem compileML_underBudget {N m B : ℕ} {steps : List (Step F)} {out : VExpr F m}
    {code : Stmt 64} (h : compileML N steps out = some code)
    (hB : irCostML (limbCount (FiniteField.size F)) m steps out ≤ B) :
    TimeLe CostModel.unit code B := (compileML_timeLe h).mono hB

/-! ## The fields, checked

`compile` refuses every modulus above `2 ^ 32`; these pass. The per-operation costs
are the closed forms proved in `MultiLimb.lean` and `MultiLimbInv.lean`, evaluated at
BN254's four limbs. -/

/-- info: [true, true, true, true] -/
#guard_msgs in
#eval [2 ^ 31 - 2 ^ 27 + 1, pGoldilocks, pBN254, pBLS12381Scalar].map fieldOkML

/- Add, multiply, convert, invert — unit steps at BN254. -/
/-- info: [59, 325, 329, 107026] -/
#guard_msgs in
#eval [addCostML 4, mulCostML 4, constCostML 4, invCostML 4]

end Caliper.MultiLimb
