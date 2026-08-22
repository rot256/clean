import Clean.Caliper.MultiLimbCompile
import Clean.Caliper.MultiLimbInv

/-!
# Multi-limb lowering of the witgen IR

The single-word compiler in `WitgenCompile.lean` reduces with one `umod`, which is
sound only when `p² ≤ 2 ^ 64`. This is the same compiler over `k`-limb field values,
with `k = limbCount p`, so it works at BN254, BLS12-381 and every other field.

## Representation

Field values are `k` consecutive registers holding base-`2 ^ 64` limbs, **in
Montgomery form**: the register block for `x` holds `x * R mod p` with
`R = 2 ^ (64k)`. Both buffers use the same encoding — the environment (buffer `0`)
holds `k` words per element, and the output (buffer `1`) is pushed `k` words per
element — so a variable read and an output push are pure moves, and no conversion
appears anywhere except where the IR's own semantics asks for the canonical value:
`U64Expr.val`, `BExpr.flt`, `BExpr.bit` and `VExpr.bitsOf`. Field constants are
converted at *generation* time, their Montgomery limbs emitted as immediates.

## Register layout

    0 .. k        the modulus, `k + 1` limbs with a zero on top
    k + 1         the Montgomery constant's low word
    k + 2 + i*k   local `i` (a u64 local uses the first register of its block)
    k + 2 + L*k   the `mapRange` index register
    k + 3 + L*k   temporaries

Every gadget wants its frame above the values it reads, so temporaries are handed out
upwards and each node's result is the top of its own block. Locals and the modulus sit
below every frame by construction.

## Cost

`fCostML`, `uCostML` and `bCostML` are the worst-case running times, as functions of
the expression and the limb count. They are *upper* bounds, not equalities: inversion
is a loop. `TimeLe` is what carries a loop's bound through the surrounding
straight-line code — see `RegOnly.lean`.
-/

namespace Caliper.MultiLimb

open Caliper Witgen

variable {F : Type} [FiniteField F] {C : CostModel}

/-! ## Layout -/

/-- Register block of local `i`. -/
def localReg (k i : ℕ) : ℕ := k + 2 + i * k

/-- The `mapRange` index register. -/
def idxReg (k L : ℕ) : ℕ := k + 2 + L * k

/-- First temporary. -/
def tmpBase (k L : ℕ) : ℕ := k + 3 + L * k

/-- The modulus and the Montgomery constant, emitted once at the head of a program.
`p` is written over `k + 1` limbs, so its top limb is zero and the final conditional
subtraction of a Montgomery multiply can read it. -/
def preludeML (k p pinv : ℕ) : Stmt 64 :=
  immLimbs 0 p (k + 1) ;; .imm (k + 1) (BitVec.ofNat 64 pinv)

/-- `k` pushes of a field value onto the output buffer. -/
def pushLoop (src : ℕ) : ℕ → Stmt 64
  | 0 => .skip
  | n + 1 => pushLoop src n ;; .memPush 1 (src + n)

def pushLimbs (k src : ℕ) : Stmt 64 := pushLoop src k

/-- `k` loads of a field value from the environment buffer at word `idx`. -/
def envLimbs (k dst idx sc : ℕ) : Stmt 64 := loadLimbs dst idx sc k

/-! ## Conversions used by the IR's canonical-value constructors -/

/-- Montgomery → canonical, at the program's fixed modulus registers. -/
def leaveMont (k a w : ℕ) : Stmt 64 := montMulConst k 1 a 0 (k + 1) w

/-- Canonical → Montgomery, by the generation-time constant `R² mod p`. -/
def enterMont (k rsq a w : ℕ) : Stmt 64 := montMulConst k rsq a 0 (k + 1) w

/-! ## Expressions -/

mutual

/-- Compile a field-sorted expression. `L` is the number of `let`-steps. The excluded
constructors (`listGet`, `dataGet`, `hintGet`) lower to a dead zero, exactly as in the
single-word compiler; `compilable` rules them out. -/
def compileFML (k L : ℕ) : FExpr F → Reg → Stmt 64 × Reg × Reg
  | .expr e, next => compileExprML k 0 (k + 1) e next
  | .const c, next =>
    (immLimbs next
      (FiniteField.val c * 2 ^ (64 * k) % FiniteField.size F) k, next, next + k)
  | .localVar i, next => (.skip, localReg k i, next)
  | .add x y, next =>
    let (cx, rx, n₁) := compileFML k L x next
    let (cy, ry, n₂) := compileFML k L y n₁
    (cx ;; cy ;; montAdd k rx ry 0 n₂, montAddOut k n₂, n₂ + montAddFrame k)
  | .mul x y, next =>
    let (cx, rx, n₁) := compileFML k L x next
    let (cy, ry, n₂) := compileFML k L y n₁
    (cx ;; cy ;; montMulSOS k rx ry 0 (k + 1) n₂, montOut k n₂, n₂ + montFrame k)
  | .inv x, next =>
    let (cx, rx, n₁) := compileFML k L x next
    -- `x` is `x·R`; the gcd gives `(x·R)⁻¹ = x⁻¹R⁻¹`, and one multiply by `R³ mod p`
    -- brings that back to `x⁻¹R`
    (cx ;; invLimbs k rx 0 n₁ ;;
      montMulConst k (2 ^ (3 * (64 * k)) % FiniteField.size F) (invOut k n₁) 0 (k + 1)
        (n₁ + 5 * k + 16),
     montMulConstOut k (n₁ + 5 * k + 16),
     n₁ + 5 * k + 16 + montMulConstFrame k)
  | .ofU64 n, next =>
    let (cn, rn, n₁) := compileUML k L n next
    -- a word is below `p` at every multi-limb field, so zero-extending and entering
    -- Montgomery form is the whole conversion
    (cn ;; immLimbs n₁ 0 k ;; .mov n₁ rn ;;
      enterMont k (2 ^ (2 * (64 * k)) % FiniteField.size F) n₁ (n₁ + k),
     montMulConstOut k (n₁ + k), n₁ + k + montMulConstFrame k)
  | .ite c t e, next =>
    let (cc, rc, n₁) := compileBML k L c next
    let (ct, rt, n₂) := compileFML k L t n₁
    let (ce, re, n₃) := compileFML k L e n₂
    (cc ;; ct ;; ce ;; selectLimbs k (n₃ + 1) rt re rc n₃, n₃ + 1, n₃ + 1 + k)
  | .listGet .., next => (immLimbs next 0 k, next, next + k)
  | .dataGet .., next => (immLimbs next 0 k, next, next + k)
  | .hintGet .., next => (immLimbs next 0 k, next, next + k)

/-- Compile a u64-sorted expression. Results are a single register. -/
def compileUML (k L : ℕ) : U64Expr F → Reg → Stmt 64 × Reg × Reg
  | .const n, next => (.imm next (BitVec.ofNat 64 n.toNat), next, next + 1)
  | .val x, next =>
    let (cx, rx, n₁) := compileFML k L x next
    -- the low limb of the canonical value is the `UInt64` the IR asks for
    (cx ;; leaveMont k rx n₁, montMulConstOut k n₁, n₁ + montMulConstFrame k)
  | .idx, next => (.skip, idxReg k L, next)
  | .localVar i, next => (.skip, localReg k i, next)
  | .add x y, next =>
    let (cx, rx, n₁) := compileUML k L x next
    let (cy, ry, n₂) := compileUML k L y n₁
    (cx ;; cy ;; .bin .add n₂ rx ry, n₂, n₂ + 1)
  | .mul x y, next =>
    let (cx, rx, n₁) := compileUML k L x next
    let (cy, ry, n₂) := compileUML k L y n₁
    (cx ;; cy ;; .bin .mul n₂ rx ry, n₂, n₂ + 1)
  | .div x y, next =>
    let (cx, rx, n₁) := compileUML k L x next
    let (cy, ry, n₂) := compileUML k L y n₁
    (cx ;; cy ;; .bin .udiv n₂ rx ry, n₂, n₂ + 1)
  | .mod x y, next =>
    let (cx, rx, n₁) := compileUML k L x next
    let (cy, ry, n₂) := compileUML k L y n₁
    (cx ;; cy ;; .bin .umod n₂ rx ry, n₂, n₂ + 1)
  | .land x y, next =>
    let (cx, rx, n₁) := compileUML k L x next
    let (cy, ry, n₂) := compileUML k L y n₁
    (cx ;; cy ;; .bin .and n₂ rx ry, n₂, n₂ + 1)
  | .lor x y, next =>
    let (cx, rx, n₁) := compileUML k L x next
    let (cy, ry, n₂) := compileUML k L y n₁
    (cx ;; cy ;; .bin .or n₂ rx ry, n₂, n₂ + 1)
  | .lxor x y, next =>
    let (cx, rx, n₁) := compileUML k L x next
    let (cy, ry, n₂) := compileUML k L y n₁
    (cx ;; cy ;; .bin .xor n₂ rx ry, n₂, n₂ + 1)
  | .shiftL x y, next =>
    let (cx, rx, n₁) := compileUML k L x next
    let (cy, ry, n₂) := compileUML k L y n₁
    (cx ;; cy ;; .imm n₂ (BitVec.ofNat 64 63) ;;
      .bin .and (n₂ + 1) ry n₂ ;; .bin .shl (n₂ + 2) rx (n₂ + 1),
     n₂ + 2, n₂ + 3)
  | .shiftR x y, next =>
    let (cx, rx, n₁) := compileUML k L x next
    let (cy, ry, n₂) := compileUML k L y n₁
    (cx ;; cy ;; .imm n₂ (BitVec.ofNat 64 63) ;;
      .bin .and (n₂ + 1) ry n₂ ;; .bin .shr (n₂ + 2) rx (n₂ + 1),
     n₂ + 2, n₂ + 3)
  | .ite c t e, next =>
    let (cc, rc, n₁) := compileBML k L c next
    let (ct, rt, n₂) := compileUML k L t n₁
    let (ce, re, n₃) := compileUML k L e n₂
    (cc ;; ct ;; ce ;; selectLimbs 1 (n₃ + 1) rt re rc n₃, n₃ + 1, n₃ + 2)

/-- Compile a condition. Results are a single `{0, 1}` register. Note `BExpr.neq` is
u64 *equality* despite the name, as in the single-word compiler. -/
def compileBML (k L : ℕ) : BExpr F → Reg → Stmt 64 × Reg × Reg
  | .true, next => (.imm next 1, next, next + 1)
  | .false, next => (.imm next 0, next, next + 1)
  | .feq x y, next =>
    -- Montgomery form is a bijection, so equality needs no conversion
    let (cx, rx, n₁) := compileFML k L x next
    let (cy, ry, n₂) := compileFML k L y n₁
    (cx ;; cy ;; eqLimbs k rx ry n₂, eqOut n₂, n₂ + eqFrame)
  | .neq x y, next =>
    let (cx, rx, n₁) := compileUML k L x next
    let (cy, ry, n₂) := compileUML k L y n₁
    (cx ;; cy ;; .bin .eq n₂ rx ry, n₂, n₂ + 1)
  | .lt x y, next =>
    let (cx, rx, n₁) := compileUML k L x next
    let (cy, ry, n₂) := compileUML k L y n₁
    (cx ;; cy ;; .bin .ult n₂ rx ry, n₂, n₂ + 1)
  | .flt x y, next =>
    -- an order comparison is on canonical values, so both sides leave Montgomery form
    let (cx, rx, n₁) := compileFML k L x next
    let (cy, ry, n₂) := compileFML k L y n₁
    let m₁ := n₂ + montMulConstFrame k
    (cx ;; cy ;; leaveMont k rx n₂ ;; leaveMont k ry m₁ ;;
      ltLimbs k (montMulConstOut k n₂) (montMulConstOut k m₁)
        (m₁ + montMulConstFrame k),
     ltOut k (m₁ + montMulConstFrame k),
     m₁ + montMulConstFrame k + ltFrame k)
  | .bit x i, next =>
    let (cx, rx, n₁) := compileFML k L x next
    (cx ;; leaveMont k rx n₁ ;;
      bitLimb k (montMulConstOut k n₁) i (n₁ + montMulConstFrame k),
     bitOut (n₁ + montMulConstFrame k), n₁ + montMulConstFrame k + bitFrame)
  | .not b, next =>
    let (cb, rb, n₁) := compileBML k L b next
    (cb ;; .un .isZero n₁ rb, n₁, n₁ + 1)
  | .and x y, next =>
    let (cx, rx, n₁) := compileBML k L x next
    let (cy, ry, n₂) := compileBML k L y n₁
    (cx ;; cy ;; .bin .and n₂ rx ry, n₂, n₂ + 1)

end

/-! ## Programs -/

/-- Compile one `let`-step into local `j`. -/
def compileStepML (k L : ℕ) (j : ℕ) : Step F → Stmt 64
  | .letF e =>
    let (c, r, _) := compileFML k L e (tmpBase k L)
    c ;; movLimbs k (localReg k j) r
  | .letU e =>
    let (c, r, _) := compileUML k L e (tmpBase k L)
    c ;; .mov (localReg k j) r

def compileStepsML (k L : ℕ) (steps : List (Step F)) (j : ℕ) : Stmt 64 :=
  match steps with
  | [] => .skip
  | s :: rest => compileStepML k L j s ;; compileStepsML k L rest (j + 1)

/-- Compile a vector output. Elements are pushed `k` words apiece, in Montgomery form
— the same encoding the environment uses — except `bitsOf`, whose bits are converted
by selecting between the emitted Montgomery forms of `0` and `1`. -/
def compileVML (k L : ℕ) : {n : ℕ} → VExpr F n → Stmt 64
  | _, .lit es =>
    es.toList.foldl (init := .skip) fun c e =>
      let (ce, r, _) := compileFML k L e (tmpBase k L)
      c ;; ce ;; pushLimbs k r
  | _, .mapRange n body =>
    ((List.range n).foldl (init := .skip) fun c i =>
      let (cb, r, _) := compileFML k L body (tmpBase k L)
      c ;; .imm (idxReg k L) (BitVec.ofNat 64 i) ;; cb ;; pushLimbs k r) ;;
    .imm (idxReg k L) 0
  | n, .envRange offset =>
    (List.range n).foldl (init := .skip) fun c i =>
      c ;; envLimbs k (tmpBase k L + 1) ((offset + i) * k) (tmpBase k L) ;;
        pushLimbs k (tmpBase k L + 1)
  | n, .bitsOf x =>
    let (cx, rx, n₁) := compileFML k L x (tmpBase k L)
    cx ;; leaveMont k rx n₁ ;;
    immLimbs (n₁ + montMulConstFrame k) 0 k ;;
    immLimbs (n₁ + montMulConstFrame k + k)
      (2 ^ (64 * k) % FiniteField.size F) k ;;
    (List.range n).foldl (init := .skip) fun c i =>
      c ;; bitLimb k (montMulConstOut k n₁) i (n₁ + montMulConstFrame k + 2 * k) ;;
        selectLimbs k (n₁ + montMulConstFrame k + 2 * k + 3)
          (n₁ + montMulConstFrame k + k) (n₁ + montMulConstFrame k)
          (bitOut (n₁ + montMulConstFrame k + 2 * k))
          (n₁ + montMulConstFrame k + 2 * k + 2) ;;
        pushLimbs k (n₁ + montMulConstFrame k + 2 * k + 3)
  | _, .append a b => compileVML k L a ;; compileVML k L b

/-- The code for a structured program: allocate `m * k` output words, lay down the
modulus and the Montgomery constant, zero the index register, run the `let`-steps into
the local blocks, push the outputs. -/
def compileIRCodeML (k p pinv L : ℕ) {m : ℕ} (steps : List (Step F))
    (out : VExpr F m) : Stmt 64 :=
  .memAllocI 1 (m * k) ;;
  preludeML k p pinv ;;
  .imm (idxReg k L) 0 ;;
  compileStepsML k L steps 0 ;;
  compileVML k L out

/-! ## Cost

Worst-case running time as a function of the expression and the limb count. These are
upper bounds: inversion is a loop, so no equality is available for an expression that
contains one. Everything else is straight-line and its contribution is exact. -/

/-- A modular addition. -/
def addCostML (k : ℕ) : ℕ := 14 * k + 3

/-- A Montgomery multiply, with its conditional subtraction. -/
def mulCostML (k : ℕ) : ℕ := 16 * k ^ 2 + 15 * k + 9

/-- A multiply by a generation-time constant — either direction of the Montgomery
conversion. -/
def constCostML (k : ℕ) : ℕ := 16 * k ^ 2 + 16 * k + 9

/-- An inversion: the only bound here that is not exact. -/
def invCostML (k : ℕ) : ℕ := 5888 * k ^ 2 + 3204 * k + 2

mutual

def fCostML (k : ℕ) : FExpr F → ℕ
  | .expr e => exprCostML k e
  | .const _ => k
  | .localVar _ => 0
  | .add x y => fCostML k x + fCostML k y + addCostML k
  | .mul x y => fCostML k x + fCostML k y + mulCostML k
  | .inv x => fCostML k x + invCostML k + constCostML k
  | .ofU64 n => uCostML k n + (k + 1) + constCostML k
  | .ite c t e => bCostML k c + fCostML k t + fCostML k e + 3 * k
  | .listGet .. => k
  | .dataGet .. => k
  | .hintGet .. => k

def uCostML (k : ℕ) : U64Expr F → ℕ
  | .const _ => 1
  | .val x => fCostML k x + constCostML k
  | .idx => 0
  | .localVar _ => 0
  | .add x y | .mul x y | .div x y | .mod x y
  | .land x y | .lor x y | .lxor x y => uCostML k x + uCostML k y + 1
  | .shiftL x y | .shiftR x y => uCostML k x + uCostML k y + 3
  | .ite c t e => bCostML k c + uCostML k t + uCostML k e + 3

def bCostML (k : ℕ) : BExpr F → ℕ
  | .true | .false => 1
  | .feq x y => fCostML k x + fCostML k y + (2 * k + 2)
  | .neq x y | .lt x y => uCostML k x + uCostML k y + 1
  | .flt x y => fCostML k x + fCostML k y + 2 * constCostML k + (6 * k + 2)
  | .bit x _ => fCostML k x + constCostML k + 4
  | .not b => bCostML k b + 1
  | .and x y => bCostML k x + bCostML k y + 1

end

/-! ### Leaf bounds -/

theorem timeLe_of_saf {c : Stmt 64} (h : SAF c) : TimeLe C c (c.staticTime C) :=
  TimeLe.of_loopFree h.1.loopFree

theorem timeLe_of_regOnly {c : Stmt 64} (h : c.RegOnly) : TimeLe C c (c.staticTime C) :=
  TimeLe.of_loopFree h.loopFree

theorem pushLoop_loopFree (src : ℕ) : ∀ n, (pushLoop src n).LoopFree
  | 0 => trivial
  | n + 1 => ⟨pushLoop_loopFree src n, trivial⟩

theorem pushLoop_staticTime_unit (src : ℕ) :
    ∀ n, (pushLoop src n).staticTime CostModel.unit = n
  | 0 => by simp [pushLoop, Stmt.staticTime]
  | n + 1 => by
    show (pushLoop src n).staticTime CostModel.unit + _ = _
    rw [pushLoop_staticTime_unit src n]; simp [Stmt.staticTime, CostModel.unit]

theorem pushLimbs_timeLe (k src : ℕ) : TimeLe CostModel.unit (pushLimbs k src) k := by
  have h := TimeLe.of_loopFree (C := CostModel.unit) (pushLoop_loopFree src k)
  rw [pushLoop_staticTime_unit] at h
  exact h

theorem envLimbs_timeLe (k dst idx sc : ℕ) :
    TimeLe CostModel.unit (envLimbs k dst idx sc) (2 * k) := by
  have h := timeLe_of_saf (C := CostModel.unit) (loadLimbs_saf dst idx sc k)
  rw [loadLimbs_staticTime] at h
  exact h.mono (by simp [CostModel.unit]; omega)

theorem immLimbs_timeLe (base v n : ℕ) :
    TimeLe CostModel.unit (immLimbs base v n) n := by
  have h := timeLe_of_saf (C := CostModel.unit) (immLimbs_saf base v n)
  rw [immLimbs_staticTime] at h
  exact h.mono (by simp [CostModel.unit])

theorem movLimbs_timeLe (k d a : ℕ) : TimeLe CostModel.unit (movLimbs k d a) k := by
  have h := timeLe_of_regOnly (C := CostModel.unit) (movLimbs_regOnly k d a)
  rw [movLimbs_staticTime_unit] at h
  exact h

theorem montAdd_timeLe (k a b pReg w : ℕ) :
    TimeLe CostModel.unit (montAdd k a b pReg w) (addCostML k) := by
  have h := timeLe_of_saf (C := CostModel.unit) (montAdd_saf k a b pReg w)
  rw [montAdd_staticTime_unit] at h
  exact h

theorem montMulSOS_timeLe (k' a b pReg pinv w : ℕ) :
    TimeLe CostModel.unit (montMulSOS (k' + 1) a b pReg pinv w) (mulCostML (k' + 1)) := by
  have h := timeLe_of_saf (C := CostModel.unit) (montMulSOS_saf (k' + 1) a b pReg pinv w)
  rw [montMulSOS_staticTime_unit] at h
  exact h.mono (by simp [mulCostML]; ring_nf; omega)

theorem montMulConst_timeLe (k' c a pReg pinv w : ℕ) :
    TimeLe CostModel.unit (montMulConst (k' + 1) c a pReg pinv w)
      (constCostML (k' + 1)) := by
  have h := timeLe_of_saf (C := CostModel.unit) (montMulConst_saf (k' + 1) c a pReg pinv w)
  rw [montMulConst_staticTime_unit] at h
  exact h.mono (by simp [constCostML]; ring_nf; omega)

theorem selectLimbs_timeLe (k d a b f sc : ℕ) :
    TimeLe CostModel.unit (selectLimbs k d a b f sc) (3 * k) := by
  have h := timeLe_of_regOnly (C := CostModel.unit) (selectLimbs_regOnly k d a b f sc)
  rw [selectLimbs_staticTime] at h
  exact h.mono (by simp [selStepCost, CostModel.unit]; omega)

theorem eqLimbs_timeLe (k a b w : ℕ) :
    TimeLe CostModel.unit (eqLimbs k a b w) (2 * k + 2) := by
  have h := timeLe_of_saf (C := CostModel.unit) (eqLimbs_saf k a b w)
  rw [eqLimbs_staticTime_unit] at h
  exact h

theorem ltLimbs_timeLe (k a b w : ℕ) :
    TimeLe CostModel.unit (ltLimbs k a b w) (6 * k + 2) := by
  have h := timeLe_of_saf (C := CostModel.unit) (ltLimbs_saf k a b w)
  rw [ltLimbs_staticTime_unit] at h
  exact h

theorem bitLimb_timeLe (k a i w : ℕ) : TimeLe CostModel.unit (bitLimb k a i w) 4 :=
  (timeLe_of_saf (C := CostModel.unit) (bitLimb_saf k a i w)).mono
    (bitLimb_staticTime_unit_le k a i w)

theorem invLimbs_timeLe {k a pReg w : ℕ} (hk : 128 * k < 2 ^ 64) :
    TimeLe CostModel.unit (invLimbs k a pReg w) (invCostML k) :=
  Triple.timeLe (invLimbs_triple hk)

theorem compileExprML_timeLe (k' pReg pinv : ℕ) (e : Expression F) (next : Reg) :
    TimeLe CostModel.unit (compileExprML (k' + 1) pReg pinv e next).1
      (exprCostML (k' + 1) e) := by
  have h := timeLe_of_saf (C := CostModel.unit) (compileExprML_saf (k' + 1) pReg pinv e next)
  rw [compileExprML_staticTime] at h
  exact h

theorem timeLe_skip : TimeLe CostModel.unit (.skip : Stmt 64) 0 :=
  (TimeLe.of_loopFree (c := (Stmt.skip : Stmt 64)) trivial).mono
    (by simp [Stmt.staticTime])

theorem timeLe_imm (d : Reg) (v : Word 64) : TimeLe CostModel.unit (.imm d v) 1 :=
  (TimeLe.of_loopFree (c := Stmt.imm d v) trivial).mono
    (by simp [Stmt.staticTime, CostModel.unit])

theorem timeLe_mov (d a : Reg) : TimeLe CostModel.unit (.mov (w := 64) d a) 1 :=
  (TimeLe.of_loopFree (c := Stmt.mov (w := 64) d a) trivial).mono
    (by simp [Stmt.staticTime, CostModel.unit])

theorem timeLe_un (op : UnOp) (d a : Reg) :
    TimeLe CostModel.unit (.un (w := 64) op d a) 1 :=
  (TimeLe.of_loopFree (c := Stmt.un (w := 64) op d a) trivial).mono
    (by simp [Stmt.staticTime, CostModel.unit])

theorem timeLe_bin (op : BinOp) (d a b : Reg) :
    TimeLe CostModel.unit (.bin (w := 64) op d a b) 1 :=
  (TimeLe.of_loopFree (c := Stmt.bin (w := 64) op d a b) trivial).mono
    (by simp [Stmt.staticTime, CostModel.unit])

/-! ### The bound, by structural induction -/

mutual

/-- **Worst-case runtime of a lowered field expression, at every field.** -/
theorem compileFML_timeLe {k' L : ℕ} (hk : 128 * (k' + 1) < 2 ^ 64) :
    ∀ (e : FExpr F) (next : Reg),
      TimeLe CostModel.unit (compileFML (k' + 1) L e next).1 (fCostML (k' + 1) e)
  | .expr e, next => compileExprML_timeLe k' 0 (k' + 2) e next
  | .const _, next => immLimbs_timeLe _ _ _
  | .localVar _, _ => timeLe_skip
  | .add x y, next => by
    refine ((compileFML_timeLe hk x next).seq
      ((compileFML_timeLe hk y _).seq (montAdd_timeLe _ _ _ _ _))).mono ?_
    simp [fCostML]; omega
  | .mul x y, next => by
    refine ((compileFML_timeLe hk x next).seq
      ((compileFML_timeLe hk y _).seq (montMulSOS_timeLe _ _ _ _ _ _))).mono ?_
    simp [fCostML]; omega
  | .inv x, next => by
    refine ((compileFML_timeLe hk x next).seq
      ((invLimbs_timeLe hk).seq (montMulConst_timeLe _ _ _ _ _ _))).mono ?_
    simp [fCostML]; omega
  | .ofU64 n, next => by
    refine ((compileUML_timeLe hk n next).seq ((immLimbs_timeLe _ _ _).seq
      ((timeLe_mov _ _).seq (montMulConst_timeLe _ _ _ _ _ _)))).mono ?_
    simp [fCostML]; omega
  | .ite c t e, next => by
    refine ((compileBML_timeLe hk c next).seq ((compileFML_timeLe hk t _).seq
      ((compileFML_timeLe hk e _).seq (selectLimbs_timeLe _ _ _ _ _ _)))).mono ?_
    simp [fCostML]; omega
  | .listGet .., _ => immLimbs_timeLe _ _ _
  | .dataGet .., _ => immLimbs_timeLe _ _ _
  | .hintGet .., _ => immLimbs_timeLe _ _ _

/-- Worst-case runtime of a lowered u64 expression. -/
theorem compileUML_timeLe {k' L : ℕ} (hk : 128 * (k' + 1) < 2 ^ 64) :
    ∀ (e : U64Expr F) (next : Reg),
      TimeLe CostModel.unit (compileUML (k' + 1) L e next).1 (uCostML (k' + 1) e)
  | .const _, _ => timeLe_imm _ _
  | .val x, next => by
    refine ((compileFML_timeLe hk x next).seq (montMulConst_timeLe _ _ _ _ _ _)).mono ?_
    simp [uCostML]
  | .idx, _ => timeLe_skip
  | .localVar _, _ => timeLe_skip
  | .add x y, next => by
    refine ((compileUML_timeLe hk x next).seq
      ((compileUML_timeLe hk y _).seq (timeLe_bin _ _ _ _))).mono ?_
    simp [uCostML]; omega
  | .mul x y, next => by
    refine ((compileUML_timeLe hk x next).seq
      ((compileUML_timeLe hk y _).seq (timeLe_bin _ _ _ _))).mono ?_
    simp [uCostML]; omega
  | .div x y, next => by
    refine ((compileUML_timeLe hk x next).seq
      ((compileUML_timeLe hk y _).seq (timeLe_bin _ _ _ _))).mono ?_
    simp [uCostML]; omega
  | .mod x y, next => by
    refine ((compileUML_timeLe hk x next).seq
      ((compileUML_timeLe hk y _).seq (timeLe_bin _ _ _ _))).mono ?_
    simp [uCostML]; omega
  | .land x y, next => by
    refine ((compileUML_timeLe hk x next).seq
      ((compileUML_timeLe hk y _).seq (timeLe_bin _ _ _ _))).mono ?_
    simp [uCostML]; omega
  | .lor x y, next => by
    refine ((compileUML_timeLe hk x next).seq
      ((compileUML_timeLe hk y _).seq (timeLe_bin _ _ _ _))).mono ?_
    simp [uCostML]; omega
  | .lxor x y, next => by
    refine ((compileUML_timeLe hk x next).seq
      ((compileUML_timeLe hk y _).seq (timeLe_bin _ _ _ _))).mono ?_
    simp [uCostML]; omega
  | .shiftL x y, next => by
    refine ((compileUML_timeLe hk x next).seq ((compileUML_timeLe hk y _).seq
      ((timeLe_imm _ _).seq ((timeLe_bin _ _ _ _).seq (timeLe_bin _ _ _ _))))).mono ?_
    simp [uCostML]; omega
  | .shiftR x y, next => by
    refine ((compileUML_timeLe hk x next).seq ((compileUML_timeLe hk y _).seq
      ((timeLe_imm _ _).seq ((timeLe_bin _ _ _ _).seq (timeLe_bin _ _ _ _))))).mono ?_
    simp [uCostML]; omega
  | .ite c t e, next => by
    refine ((compileBML_timeLe hk c next).seq ((compileUML_timeLe hk t _).seq
      ((compileUML_timeLe hk e _).seq (selectLimbs_timeLe _ _ _ _ _ _)))).mono ?_
    simp [uCostML]; omega

/-- Worst-case runtime of a lowered condition. -/
theorem compileBML_timeLe {k' L : ℕ} (hk : 128 * (k' + 1) < 2 ^ 64) :
    ∀ (e : BExpr F) (next : Reg),
      TimeLe CostModel.unit (compileBML (k' + 1) L e next).1 (bCostML (k' + 1) e)
  | .true, _ => timeLe_imm _ _
  | .false, _ => timeLe_imm _ _
  | .feq x y, next => by
    refine ((compileFML_timeLe hk x next).seq
      ((compileFML_timeLe hk y _).seq (eqLimbs_timeLe _ _ _ _))).mono ?_
    simp [bCostML]; omega
  | .neq x y, next => by
    refine ((compileUML_timeLe hk x next).seq
      ((compileUML_timeLe hk y _).seq (timeLe_bin _ _ _ _))).mono ?_
    simp [bCostML]; omega
  | .lt x y, next => by
    refine ((compileUML_timeLe hk x next).seq
      ((compileUML_timeLe hk y _).seq (timeLe_bin _ _ _ _))).mono ?_
    simp [bCostML]; omega
  | .flt x y, next => by
    refine ((compileFML_timeLe hk x next).seq ((compileFML_timeLe hk y _).seq
      ((montMulConst_timeLe _ _ _ _ _ _).seq
        ((montMulConst_timeLe _ _ _ _ _ _).seq (ltLimbs_timeLe _ _ _ _))))).mono ?_
    simp [bCostML]; omega
  | .bit x i, next => by
    refine ((compileFML_timeLe hk x next).seq
      ((montMulConst_timeLe _ _ _ _ _ _).seq (bitLimb_timeLe _ _ _ _))).mono ?_
    simp [bCostML]; omega
  | .not b, next => by
    refine ((compileBML_timeLe hk b next).seq (timeLe_un _ _ _)).mono ?_
    simp [bCostML]
  | .and x y, next => by
    refine ((compileBML_timeLe hk x next).seq
      ((compileBML_timeLe hk y _).seq (timeLe_bin _ _ _ _))).mono ?_
    simp [bCostML]; omega

end

/-! ## Programs, and their cost

The remaining shapes are folds over a list, so one lemma about folds covers the
output vector's four cases. -/

/-- A fold accumulates its bound. -/
theorem timeLe_foldl {α : Type} (f : Stmt 64 → α → Stmt 64) (g : α → ℕ)
    (hf : ∀ c a t, TimeLe C c t → TimeLe C (f c a) (t + g a)) :
    ∀ (l : List α) (init : Stmt 64) (T : ℕ), TimeLe C init T →
      TimeLe C (l.foldl f init) (T + (l.map g).sum)
  | [], init, T, h => h.mono (by simp)
  | a :: l, init, T, h => by
    have := timeLe_foldl f g hf l (f init a) (T + g a) (hf init a T h)
    exact this.mono (by simp [List.sum_cons]; omega)

def stepCostML (k : ℕ) : Step F → ℕ
  | .letF e => fCostML k e + k
  | .letU e => uCostML k e + 1

def stepsCostML (k : ℕ) (steps : List (Step F)) : ℕ := (steps.map (stepCostML k)).sum

def vCostML (k : ℕ) : {n : ℕ} → VExpr F n → ℕ
  | _, .lit es => (es.toList.map (fun e => fCostML k e + k)).sum
  | _, .mapRange n body => n * (1 + fCostML k body + k) + 1
  | n, .envRange _ => n * (3 * k)
  | n, .bitsOf x => fCostML k x + constCostML k + 2 * k + n * (4 + 4 * k)
  | _, .append a b => vCostML k a + vCostML k b

/-- **Worst-case runtime of a compiled program's outputs, at every field.** -/
def irCostML (k m : ℕ) (steps : List (Step F)) (out : VExpr F m) : ℕ :=
  m * k + (k + 2) + 1 + stepsCostML k steps + vCostML k out

theorem compileStepML_timeLe {k' L : ℕ} (hk : 128 * (k' + 1) < 2 ^ 64) (j : ℕ) :
    ∀ st : Step F,
      TimeLe CostModel.unit (compileStepML (k' + 1) L j st) (stepCostML (k' + 1) st)
  | .letF e => (compileFML_timeLe hk e _).seq (movLimbs_timeLe _ _ _)
  | .letU e => (compileUML_timeLe hk e _).seq (timeLe_mov _ _)

theorem compileStepsML_timeLe {k' L : ℕ} (hk : 128 * (k' + 1) < 2 ^ 64) :
    ∀ (steps : List (Step F)) (j : ℕ),
      TimeLe CostModel.unit (compileStepsML (k' + 1) L steps j)
        (stepsCostML (k' + 1) steps)
  | [], _ => timeLe_skip.mono (by simp [stepsCostML])
  | st :: rest, j =>
    ((compileStepML_timeLe hk j st).seq (compileStepsML_timeLe hk rest (j + 1))).mono
      (by simp [stepsCostML, List.sum_cons])

theorem compileVML_timeLe {k' L : ℕ} (hk : 128 * (k' + 1) < 2 ^ 64) :
    ∀ {n : ℕ} (out : VExpr F n),
      TimeLe CostModel.unit (compileVML (k' + 1) L out) (vCostML (k' + 1) out)
  | _, .lit es => by
    refine (timeLe_foldl _ (fun e => fCostML (k' + 1) e + (k' + 1))
      (fun c e t h => (h.seq ((compileFML_timeLe hk e _).seq
        (pushLimbs_timeLe _ _))).mono (by omega))
      es.toList .skip 0 timeLe_skip).mono ?_
    simp [vCostML]
  | _, .mapRange n body => by
    refine ((timeLe_foldl _ (fun _ : ℕ => 1 + fCostML (k' + 1) body + (k' + 1))
      (fun c _ t h => (h.seq ((timeLe_imm _ _).seq
        ((compileFML_timeLe hk body _).seq (pushLimbs_timeLe _ _)))).mono (by omega))
      (List.range n) .skip 0 timeLe_skip).seq (timeLe_imm _ _)).mono ?_
    simp [vCostML, List.map_const', List.sum_replicate]
  | n, .envRange offset => by
    refine (timeLe_foldl _ (fun _ : ℕ => 3 * (k' + 1))
      (fun c _ t h => (h.seq ((envLimbs_timeLe _ _ _ _).seq
        (pushLimbs_timeLe _ _))).mono (by omega))
      (List.range n) .skip 0 timeLe_skip).mono ?_
    simp [vCostML, List.map_const', List.sum_replicate]
  | n, .bitsOf x => by
    refine ((compileFML_timeLe hk x _).seq ((montMulConst_timeLe _ _ _ _ _ _).seq
      ((immLimbs_timeLe _ _ _).seq ((immLimbs_timeLe _ _ _).seq
        (timeLe_foldl _ (fun _ : ℕ => 4 + 4 * (k' + 1))
          (fun c _ t h => (h.seq ((bitLimb_timeLe _ _ _ _).seq
            ((selectLimbs_timeLe _ _ _ _ _ _).seq (pushLimbs_timeLe _ _)))).mono
            (by omega))
          (List.range n) .skip 0 timeLe_skip))))).mono ?_
    simp [vCostML, List.map_const', List.sum_replicate]
    omega
  | _, .append a b =>
    ((compileVML_timeLe hk a).seq (compileVML_timeLe hk b)).mono (by simp [vCostML])

/-- **The running time of a compiled witgen program is bounded, at every field.**
Every execution of `compileIRCodeML` takes at most `irCostML` unit steps: a number the
compiler computes from the program and the modulus, without running anything. -/
theorem compileIRCodeML_timeLe {k' p pinv L m : ℕ} (hk : 128 * (k' + 1) < 2 ^ 64)
    (steps : List (Step F)) (out : VExpr F m) :
    TimeLe CostModel.unit (compileIRCodeML (k' + 1) p pinv L steps out)
      (irCostML (k' + 1) m steps out) := by
  have halloc : TimeLe CostModel.unit
      (Stmt.memAllocI (w := 64) 1 (m * (k' + 1))) (m * (k' + 1)) :=
    (TimeLe.of_loopFree (c := Stmt.memAllocI (w := 64) 1 (m * (k' + 1))) trivial).mono
      (by simp [Stmt.staticTime, CostModel.unit])
  have hpre : TimeLe CostModel.unit (preludeML (k' + 1) p pinv) (k' + 1 + 2) :=
    ((immLimbs_timeLe _ _ _).seq (timeLe_imm _ _)).mono (by omega)
  refine (halloc.seq (hpre.seq ((timeLe_imm _ _).seq
    ((compileStepsML_timeLe hk steps 0).seq (compileVML_timeLe hk out))))).mono ?_
  simp [irCostML]
  omega

end Caliper.MultiLimb
