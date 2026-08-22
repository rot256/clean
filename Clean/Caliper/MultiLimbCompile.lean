import Clean.Caliper.MultiLimb
import Clean.Circuit.WitnessIR

/-!
# Multi-limb lowering of circuit expressions, and its worst-case cost

The bridge from the witgen IR to the multi-limb gadgets: a circuit `Expression`
compiles to code over `k`-limb field values, where `k = limbCount p` is fixed by the
modulus. Nothing here restricts `p`, so this is the lowering the compiler needs to
stop rejecting BN254 and every other field above `2 ^ 32`.

`exprCostML` is the worst-case running time as a function of the *expression* and the
limb count, and `compileExprML_time` proves the emitted code takes exactly that many
steps — exactly, not merely at most, because the code is straight-line. Together with
`limbCount` that is a runtime bound for every expression at every field.

Only the cost is proved here. That the emitted code computes the right field element
rests on the correctness of `montMulOpt`, which is not yet proved; until it is, this
lowering must not be wired into the verified `compile` entry point.
-/

namespace Caliper.MultiLimb

open Caliper Witgen

variable {F : Type} [FiniteField F]

/-- Registers a multi-limb operation node uses for its destination and scratch.
Generous by a few words; the liveness analysis reclaims what dies. -/
def nodeScratch (k : ℕ) : ℕ := 5 * k + 8

/-- Multi-limb lowering of a circuit expression. A value occupies `k` consecutive
registers. `pReg` holds the modulus's limbs and `pinv` the Montgomery constant, both
below `next`. Returns the code, the result's base register, and the next free
register. -/
def compileExprML (k pReg pinv : ℕ) : Expression F → Reg → Stmt 64 × Reg × Reg
  | .var v, next => (loadLimbs next (v.index * k) (next + k) k, next, next + k + 1)
  | .const c, next => (immLimbs next (FiniteField.val c) k, next, next + k)
  | .add x y, next =>
    let (cx, rx, n₁) := compileExprML k pReg pinv x next
    let (cy, ry, n₂) := compileExprML k pReg pinv y n₁
    (cx ;; cy ;; montAdd k n₂ rx ry pReg (n₂ + k) (n₂ + 2 * k) (n₂ + 3 * k)
      (n₂ + 4 * k) (n₂ + 4 * k + 1),
     n₂, n₂ + nodeScratch k)
  | .mul x y, next =>
    let (cx, rx, n₁) := compileExprML k pReg pinv x next
    let (cy, ry, n₂) := compileExprML k pReg pinv y n₁
    (cx ;; cy ;; montMulRed k n₂ (n₂ + k) rx ry pReg pinv (n₂ + 3 * k + 2)
      (n₂ + 3 * k + 3) (n₂ + 4 * k + 3) (n₂ + 5 * k + 3),
     n₂, n₂ + nodeScratch k)

/-- Worst-case running time of the multi-limb lowering, as a function of the
expression and the limb count. A variable read is two instructions a limb, a constant
one; an addition adds `14k + 3` and a multiplication `16k² + 15k`. -/
def exprCostML (k : ℕ) : Expression F → ℕ
  | .var _ => 2 * k
  | .const _ => k
  | .add x y => exprCostML k x + exprCostML k y + (14 * k + 3)
  | .mul x y => exprCostML k x + exprCostML k y + (16 * k ^ 2 + 15 * k)

/-- Everything the multi-limb lowering emits is straight-line and allocation-free. -/
theorem compileExprML_saf (k pReg pinv : ℕ) :
    ∀ (e : Expression F) (next : Reg), SAF (compileExprML k pReg pinv e next).1
  | .var _, _ => loadLimbs_saf _ _ _ _
  | .const _, _ => immLimbs_saf _ _ _
  | .add x y, next =>
    (compileExprML_saf k pReg pinv x next).seq
      ((compileExprML_saf k pReg pinv y _).seq (montAdd_saf _ _ _ _ _ _ _ _ _ _))
  | .mul x y, next =>
    (compileExprML_saf k pReg pinv x next).seq
      ((compileExprML_saf k pReg pinv y _).seq (montMulRed_saf _ _ _ _ _ _ _ _ _ _ _))

/-- The emitted code's static time is exactly `exprCostML`. -/
theorem compileExprML_staticTime (k' pReg pinv : ℕ) :
    ∀ (e : Expression F) (next : Reg),
      (compileExprML (k' + 1) pReg pinv e next).1.staticTime CostModel.unit
        = exprCostML (k' + 1) e
  | .var v, next => by
    show (loadLimbs next (v.index * (k' + 1)) (next + (k' + 1)) (k' + 1)).staticTime
      CostModel.unit = _
    rw [loadLimbs_staticTime]
    simp [exprCostML, CostModel.unit]
    ring
  | .const c, next => by
    show (immLimbs next (FiniteField.val c) (k' + 1)).staticTime CostModel.unit = _
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
        + (montMulRed ..).staticTime CostModel.unit) = _
    rw [compileExprML_staticTime k' pReg pinv x next,
      compileExprML_staticTime k' pReg pinv y _, montMulRed_staticTime_unit]
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
