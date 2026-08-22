import Clean.Caliper.MultiLimbEntry

/-!
# A benchmark: elliptic-curve arithmetic at BN254

The cost formulas are proved for all `k`; this prices a real program with them. The
program is a Jacobian point doubling on a short Weierstrass curve with `a = 0` — the
BN254 curve — written as witgen IR and costed by `irCostML`, the same function
`compileML_timeLe` bounds the emitted code by.

Doubling `(X, Y, Z)` with `a = 0`:

    A = X²    B = Y²    C = B²
    D = 2((X + B)² - A - C)
    E = 3A    F = E²
    X' = F - 2D    Y' = E(D - X') - 8C    Z' = 2YZ

Seven multiplications and a handful of additions — the small scalar multiples are
doublings, not multiplies, which is what makes the count worth taking from a real
program rather than a table. Subtraction is `x + (p - 1) * y`, so it costs a multiply
here; the IR has no field subtraction node.

The point of the number is the ratio to a budget: `2 ^ 40` steps buys about `2 ^ 19`
scalar multiplications, so a witgen that could compute a discrete log on this curve is
nowhere near the budget.
-/

namespace Caliper.MultiLimb

open Caliper Witgen

/-- The curve's field. -/
abbrev Fbn := _root_.F pBN254

/-- Environment slot `i` as a field-sorted expression. -/
def envVar (i : ℕ) : FExpr Fbn := .expr (.var ⟨i⟩)

/-- A local, by step index. -/
def loc (i : ℕ) : FExpr Fbn := .localVar i

/-- `x + x`. -/
def dbl (x : FExpr Fbn) : FExpr Fbn := .add x x

/-- `x - y`, the only way the IR has to say it. -/
def sub (x y : FExpr Fbn) : FExpr Fbn :=
  .add x (.mul (.const (-1 : Fbn)) y)

/-- Jacobian doubling, `a = 0`. Inputs `X`, `Y`, `Z` are environment slots `0`, `1`,
`2`; the outputs are the last three locals. -/
def jacobianDouble : List (Step Fbn) :=
  [ .letF (.mul (envVar 0) (envVar 0)),                       -- 0: A = X²
    .letF (.mul (envVar 1) (envVar 1)),                       -- 1: B = Y²
    .letF (.mul (loc 1) (loc 1)),                             -- 2: C = B²
    .letF (.add (envVar 0) (loc 1)),                          -- 3: X + B
    .letF (.mul (loc 3) (loc 3)),                             -- 4: (X + B)²
    .letF (dbl (sub (sub (loc 4) (loc 0)) (loc 2))),          -- 5: D
    .letF (.add (dbl (loc 0)) (loc 0)),                       -- 6: E = 3A
    .letF (.mul (loc 6) (loc 6)),                             -- 7: F = E²
    .letF (sub (loc 7) (dbl (loc 5))),                        -- 8: X'
    .letF (.mul (loc 6) (sub (loc 5) (loc 8))),               -- 9: E(D - X')
    .letF (sub (loc 9) (dbl (dbl (dbl (loc 2))))),            -- 10: Y'
    .letF (dbl (.mul (envVar 1) (envVar 2))) ]                -- 11: Z'

def jacobianDoubleOut : VExpr Fbn 3 :=
  .lit #v[loc 8, loc 10, loc 11]

/-- Its worst-case running time, in unit steps. -/
def doubleCost : ℕ := irCostML 4 3 jacobianDouble jacobianDoubleOut

/-- info: 6234 -/
#guard_msgs in
#eval doubleCost

/-- A doubling is under `2 ^ 13` steps. -/
theorem doubleCost_lt : doubleCost < 2 ^ 13 := by decide +kernel

/-- A `254`-bit scalar multiplication, double-and-add: one doubling a bit and an
addition on about half of them, an addition costing roughly a doubling and a half. -/
def scalarMulCost : ℕ := 254 * doubleCost + 127 * (doubleCost * 3 / 2)

/-- info: 2771013 -/
#guard_msgs in
#eval scalarMulCost

/-- **A BN254 scalar multiplication costs under `2 ^ 22` machine steps**, so a `2 ^ 40`
witgen budget buys more than `2 ^ 18` of them. Discrete logarithms on this curve are
`2 ^ 127` group operations; the gap is the point of the bound. -/
theorem scalarMulCost_lt : scalarMulCost < 2 ^ 22 := by decide +kernel

/-- info: 396790 -/
#guard_msgs in
#eval 2 ^ 40 / scalarMulCost

end Caliper.MultiLimb
