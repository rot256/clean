import Clean.Caliper.MultiLimb
import Clean.Circuit.WitnessIR

/-!
# Multi-limb lowering of circuit expressions, and its worst-case cost

The bridge from the witgen IR to the multi-limb gadgets: a circuit `Expression`
compiles to code over `k`-limb field values, where `k = limbCount p` is fixed by the
modulus. Nothing here restricts `p`, so this is the lowering the compiler needs to
stop rejecting BN254 and every other field above `2 ^ 32`.

Registers are allocated in one direction. A node is given a base `next` and takes the
block `[next, next')`; its result is the *top* `k` registers of that block. That is
what the gadget layouts want — every one of them puts its scratch above the values it
reads and its destination above that — so a parent's operands, which are its
children's results, sit below the parent's own frame by construction.

`exprCostML` is the worst-case running time as a function of the *expression* and the
limb count, and `compileExprML_time` proves the emitted code takes exactly that many
steps — exactly, not merely at most, because the code is straight-line. Together with
`limbCount` that is a runtime bound for every expression at every field.
-/

namespace Caliper.MultiLimb

open Caliper Witgen

variable {F : Type} [FiniteField F]

/-- Multi-limb lowering of a circuit expression. A value occupies `k` consecutive
registers. `pReg` holds the modulus's limbs (`k + 1` of them, the top one zero) and
`pinv` the Montgomery constant's low word, both below `next`. Returns the code, the
result's base register, and the next free register. -/
def compileExprML (k pReg pinv : ℕ) : Expression F → Reg → Stmt 64 × Reg × Reg
  | .var v, next => (loadLimbs (next + 1) (v.index * k) next k, next + 1, next + 1 + k)
  | .const c, next =>
    -- constants are converted to Montgomery form at generation time, matching the
    -- form `montAdd` and `montMulSOS` read their operands in
    (immLimbs next (FiniteField.val c * 2 ^ (64 * k) % FiniteField.size F) k,
     next, next + k)
  | .add x y, next =>
    let (cx, rx, n₁) := compileExprML k pReg pinv x next
    let (cy, ry, n₂) := compileExprML k pReg pinv y n₁
    (cx ;; cy ;; montAdd k rx ry pReg n₂, montAddOut k n₂, n₂ + montAddFrame k)
  | .mul x y, next =>
    let (cx, rx, n₁) := compileExprML k pReg pinv x next
    let (cy, ry, n₂) := compileExprML k pReg pinv y n₁
    (cx ;; cy ;; montMulSOS k rx ry pReg pinv n₂, montOut k n₂, n₂ + montFrame k)

/-- Worst-case running time of the multi-limb lowering, as a function of the
expression and the limb count. A variable read is two instructions a limb, a constant
one; an addition adds `14k + 3` and a multiplication `16k² + 15k + 9`. -/
def exprCostML (k : ℕ) : Expression F → ℕ
  | .var _ => 2 * k
  | .const _ => k
  | .add x y => exprCostML k x + exprCostML k y + (14 * k + 3)
  | .mul x y => exprCostML k x + exprCostML k y + (16 * k ^ 2 + 15 * k + 9)

/-- Everything the multi-limb lowering emits is straight-line and allocation-free. -/
theorem compileExprML_saf (k pReg pinv : ℕ) :
    ∀ (e : Expression F) (next : Reg), SAF (compileExprML k pReg pinv e next).1
  | .var _, _ => loadLimbs_saf _ _ _ _
  | .const _, _ => immLimbs_saf _ _ _
  | .add x y, next =>
    (compileExprML_saf k pReg pinv x next).seq
      ((compileExprML_saf k pReg pinv y _).seq (montAdd_saf _ _ _ _ _))
  | .mul x y, next =>
    (compileExprML_saf k pReg pinv x next).seq
      ((compileExprML_saf k pReg pinv y _).seq (montMulSOS_saf _ _ _ _ _ _))

/-- The emitted code's static time is exactly `exprCostML`. -/
theorem compileExprML_staticTime (k' pReg pinv : ℕ) :
    ∀ (e : Expression F) (next : Reg),
      (compileExprML (k' + 1) pReg pinv e next).1.staticTime CostModel.unit
        = exprCostML (k' + 1) e
  | .var v, next => by
    show (loadLimbs (next + 1) (v.index * (k' + 1)) next (k' + 1)).staticTime
      CostModel.unit = _
    rw [loadLimbs_staticTime]
    simp [exprCostML, CostModel.unit]
    ring
  | .const c, next => by
    show (immLimbs next (FiniteField.val c * 2 ^ (64 * (k' + 1)) % FiniteField.size F)
      (k' + 1)).staticTime CostModel.unit = _
    rw [immLimbs_staticTime]
    simp [exprCostML, CostModel.unit]
  | .add x y, next => by
    show (compileExprML (k' + 1) pReg pinv x next).1.staticTime CostModel.unit
      + ((compileExprML (k' + 1) pReg pinv y _).1.staticTime CostModel.unit
        + (montAdd ..).staticTime CostModel.unit) = _
    rw [compileExprML_staticTime k' pReg pinv x next,
      compileExprML_staticTime k' pReg pinv y _, montAdd_staticTime_unit]
    simp [exprCostML]
    ring
  | .mul x y, next => by
    show (compileExprML (k' + 1) pReg pinv x next).1.staticTime CostModel.unit
      + ((compileExprML (k' + 1) pReg pinv y _).1.staticTime CostModel.unit
        + (montMulSOS ..).staticTime CostModel.unit) = _
    rw [compileExprML_staticTime k' pReg pinv x next,
      compileExprML_staticTime k' pReg pinv y _, montMulSOS_staticTime_unit]
    simp [exprCostML]
    ring

/-- **Worst-case runtime of a compiled circuit expression, at every field.** Every
execution of the multi-limb lowering of `e` over a `k`-limb modulus takes exactly
`exprCostML k e` unit steps. `k` and `e` are both parameters, so this prices every
expression at every prime. -/
theorem compileExprML_time {k' pReg pinv : ℕ} {e : Expression F} {next : Reg}
    {s s' : State 64} {t : ℕ} {d pp : ℤ}
    (h : Exec CostModel.unit (compileExprML (k' + 1) pReg pinv e next).1 s s' t d pp) :
    t = exprCostML (k' + 1) e :=
  (h.straight_time_eq (compileExprML_saf _ _ _ _ _).1).trans
    (compileExprML_staticTime _ _ _ _ _)

end Caliper.MultiLimb
