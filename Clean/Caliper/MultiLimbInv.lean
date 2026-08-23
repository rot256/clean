import Clean.Caliper.RegOnly
import Clean.Caliper.MultiLimbOps
import Clean.Caliper.GcdArith

/-!
# Multi-limb inversion by binary extended GCD

The last field operation. Given a canonical `a < p`, `invLimbs` computes `a⁻¹ mod p`
(and `0` at `a = 0`, matching the field's convention) by the binary extended
Euclidean algorithm with modular halving:

```
u = a; v = p; r = 1; s = 0          -- u ≡ r·a, v ≡ s·a  (mod p)
repeat:
  if u = 0: stop                     -- then v = gcd = 1, so s = a⁻¹
  if u even:      u /= 2;  r = r/2 mod p
  elif v even:    v /= 2;  s = s/2 mod p
  elif u ≥ v:     u = (u-v)/2;  r = (r-s)/2 mod p
  else:           v = (v-u)/2;  s = (s-r)/2 mod p
```

Every iteration halves one of `u`, `v` or a difference, so `bitlen u + bitlen v` falls
by at least one and `2 * 64k` iterations always suffice.

## Why the loop is counted

The alternative to a loop is a straight-line Fermat ladder, whose time is an equality
rather than a bound — but at BN254 it unrolls to about 166 000 *instructions*, which
is not a program anyone can ship. So this is a `whileNZ`, and the bound is a `≤`.

The measure is an explicit iteration counter rather than the data. A data measure
would need the bit-length argument above at the machine level; a counter needs only
that the body decrements it, which is one instruction to check. The loop stops when
the counter runs out *or* when `u` reaches zero — the body zeroes the counter in that
case — so the early exit survives and the bound holds unconditionally, without any
reasoning about what the arithmetic does.

That is the whole point of `Stmt.RegOnly`: the body is register-only, so it always
executes and costs at most its `staticTime` whatever the data, and the loop's time
follows from the counter alone.

## What is proved here

The running time, and nothing else. `invLimbs_time` bounds every execution by
`5888k² + 3204k + 2` unit steps — 107 026 at BN254's `k = 4`, against about 179 000
for a Fermat ladder run as a loop. That the value computed is the inverse is *not* proved
yet; it is the one gap left in the multi-limb field layer.
-/

namespace Caliper.MultiLimb

open Caliper Caliper.Limbs

variable {C : CostModel}

/-! ## Moving and shifting limbs -/

def movLoop (d a : ℕ) : ℕ → Stmt 64
  | 0 => .skip
  | n + 1 => movLoop d a n ;; .mov (d + n) (a + n)

/-- `d ← a` over `k` limbs. -/
def movLimbs (k d a : ℕ) : Stmt 64 := movLoop d a k

/-- One limb of a right shift by one: the limb's own top bits, plus the low bit of the
limb above. The two halves occupy disjoint bits, so they are combined with `add` rather
than `or` — same instruction count, and an addition is what the limb arithmetic
already knows how to reason about. -/
def shr1Step (d a sc j : ℕ) : Stmt 64 :=
  .bin .shr (sc + 2) (a + j) sc ;;
  .bin .shl (sc + 3) (a + j + 1) (sc + 1) ;;
  .bin .add (d + j) (sc + 2) (sc + 3)

def shr1Loop (d a sc : ℕ) : ℕ → Stmt 64
  | 0 => .skip
  | n + 1 => shr1Loop d a sc n ;; shr1Step d a sc n

/-- `d ← a >>> 1` over `k` limbs. `a`'s limb `k` is read as the word shifted in from
above, so the caller passes `k + 1` words. `sc .. sc + 3` are scratch. -/
def shr1Limbs (k d a sc : ℕ) : Stmt 64 :=
  .imm sc 1 ;; .imm (sc + 1) 63 ;; shr1Loop d a sc k

def orLoop (acc a : ℕ) : ℕ → Stmt 64
  | 0 => .skip
  | n + 1 => orLoop acc a n ;; .bin .or acc acc (a + n)

/-- `w + 1 ← 1` if any of the `k` limbs at `a` is nonzero. -/
def nzLimbs (k a w : ℕ) : Stmt 64 :=
  .imm (w + 1) 0 ;; orLoop (w + 1) a k ;; .un .isNonZero (w + 1) (w + 1)

def nzOut (w : ℕ) : ℕ := w + 1

/-! ## Halving modulo the modulus

`a / 2 mod p` for `a < p` and `p` odd: add `p` when `a` is odd — which makes the total
even without leaving the residue class — then shift the `k + 1`-word sum down one
place. Branch-free, because the conditional add is a select. -/

/-- Frame, relative to `w`: a zero block at `0`, the odd bit at `k`, the mask
immediate at `k + 1`, the select's scratch at `k + 2`, `p`-or-zero at `k + 3`, the
addition's scratch at `2k + 3`, the `k + 1`-word sum at `2k + 7`, the shift's scratch
at `3k + 8`, and the result at `3k + 12`. -/
def halfModP (k a pReg w : ℕ) : Stmt 64 :=
  immLimbs w 0 k ;;
  .imm (w + k + 1) 2 ;;
  .bin .umod (w + k) a (w + k + 1) ;;
  selectLimbs k (w + k + 3) pReg w (w + k) (w + k + 2) ;;
  addLimbs k (w + 2 * k + 7) a (w + k + 3) (w + 2 * k + 3) ;;
  .mov (w + 3 * k + 7) (w + 2 * k + 3) ;;
  shr1Limbs k (w + 3 * k + 12) (w + 2 * k + 7) (w + 3 * k + 8)

def halfModPOut (k w : ℕ) : ℕ := w + 3 * k + 12

def halfModPFrame (k : ℕ) : ℕ := 4 * k + 12

/-! ## The three updates a row performs

Each writes a `k`-word block that lives below the frame, so each ends in a copy back
out of the frame. -/

/-- `dst ← src >>> 1`, both `k`-word blocks below the frame. -/
def shrCopy (k dst src w : ℕ) : Stmt 64 :=
  movLimbs k w src ;;
  .imm (w + k) 0 ;;
  shr1Limbs k (w + k + 5) w (w + k + 1) ;;
  movLimbs k dst (w + k + 5)

def shrCopyFrame (k : ℕ) : ℕ := 2 * k + 5

/-- `dst ← src / 2 mod p`. -/
def halfCopy (k dst src pReg w : ℕ) : Stmt 64 :=
  halfModP k src pReg w ;; movLimbs k dst (halfModPOut k w)

def halfCopyFrame (k : ℕ) : ℕ := halfModPFrame k

/-- `dst ← (x - y) mod p`. -/
def subModCopy (k dst x y pReg w : ℕ) : Stmt 64 :=
  montSub k x y pReg w ;; movLimbs k dst (montSubOut k w)

def subModCopyFrame (k : ℕ) : ℕ := montSubFrame k

/-! ## One row -/

/-- The four cases, with the two odd bits and the comparison as the branch flags.
Frame, relative to `W`: the mask immediate at `0`, `u`'s odd bit at `1`, `v`'s at `2`,
and the branch bodies from `3`. -/
def invStep (k u v r s pReg W : ℕ) : Stmt 64 :=
  .imm W 2 ;;
  .bin .umod (W + 1) u W ;;
  .bin .umod (W + 2) v W ;;
  .ifNZ (W + 1)
    (.ifNZ (W + 2)
      (-- both odd: subtract both ways, then halve the smaller difference
        subLimbs k (W + 3 + k + 4) u v (W + 3) (W + 3 + k) ;;
        subLimbs k (W + 3 + 3 * k + 8) v u (W + 3 + 2 * k + 4) (W + 3 + 3 * k + 4) ;;
        .ifNZ (W + 3 + k)
          (shrCopy k u (W + 3 + k + 4) (W + 3 + 4 * k + 8) ;;
            subModCopy k r r s pReg (W + 3 + 4 * k + 8 + shrCopyFrame k) ;;
            halfCopy k r r pReg
              (W + 3 + 4 * k + 8 + shrCopyFrame k + subModCopyFrame k))
          (shrCopy k v (W + 3 + 3 * k + 8) (W + 3 + 4 * k + 8) ;;
            subModCopy k s s r pReg (W + 3 + 4 * k + 8 + shrCopyFrame k) ;;
            halfCopy k s s pReg
              (W + 3 + 4 * k + 8 + shrCopyFrame k + subModCopyFrame k)))
      (-- v even
        shrCopy k v v (W + 3) ;;
        halfCopy k s s pReg (W + 3 + shrCopyFrame k)))
    (-- u even
      shrCopy k u u (W + 3) ;;
      halfCopy k r r pReg (W + 3 + shrCopyFrame k))

/-! ## The counted loop -/

/-- One pass: stop when `u` is zero by zeroing the counter, otherwise spend one
iteration on a row. -/
def invBody (k u v r s pReg cnt W : ℕ) : Stmt 64 :=
  nzLimbs k u W ;;
  .ifNZ (W + 1)
    (.imm (W + 2) 1 ;;
      .bin .sub cnt cnt (W + 2) ;;
      invStep k u v r s pReg (W + 3))
    (.imm cnt 0)

def invLoop (k u v r s pReg cnt W : ℕ) : Stmt 64 :=
  .whileNZ .skip cnt (invBody k u v r s pReg cnt W)

/-- The iteration budget: `bitlen u + bitlen v` starts below `2 * 64k` and falls by at
least one each row. -/
def invBudget (k : ℕ) : ℕ := 128 * k

/-- `a⁻¹ mod p` for a canonical `a < p`, in `invOut k w`. Frame, relative to `w`: the
counter at `0`, then `u`, `v`, `r`, `s` at `1`, `k + 1`, `2k + 1`, `3k + 1`, and the
loop's own frame from `4k + 1`. Everything the loop writes is above the counter, which
is what makes the counter's decrement the only fact its time bound needs. -/
def invLimbs (k a pReg w : ℕ) : Stmt 64 :=
  movLimbs k (w + 1) a ;;
  movLimbs k (w + 1 + k) pReg ;;
  immLimbs (w + 1 + 2 * k) 1 k ;;
  immLimbs (w + 1 + 3 * k) 0 k ;;
  .imm w (BitVec.ofNat 64 (invBudget k)) ;;
  invLoop k (w + 1) (w + 1 + k) (w + 1 + 2 * k) (w + 1 + 3 * k) pReg w (w + 1 + 4 * k)

/-- Where an inversion based at `w` leaves its `k`-limb result: the `s` block. -/
def invOut (k w : ℕ) : ℕ := w + 1 + 3 * k

/-! ## Cost

Closed forms in `k` for every block, in the unit model. The `max` in an `ifNZ`'s
static time is between two polynomials in `k`, so `omega` resolves it. -/

theorem movLoop_staticTime (C : CostModel) (d a : ℕ) :
    ∀ n, (movLoop d a n).staticTime C = n * C.mov
  | 0 => by simp [movLoop, Stmt.staticTime]
  | n + 1 => by
    show (movLoop d a n).staticTime C + _ = _
    rw [movLoop_staticTime C d a n]; simp [Stmt.staticTime]; ring

theorem movLimbs_staticTime_unit (k d a : ℕ) :
    (movLimbs k d a).staticTime CostModel.unit = k := by
  rw [show movLimbs k d a = movLoop d a k from rfl, movLoop_staticTime]
  simp [CostModel.unit]

theorem shr1Loop_staticTime_unit (d a sc : ℕ) :
    ∀ n, (shr1Loop d a sc n).staticTime CostModel.unit = 3 * n
  | 0 => by simp [shr1Loop, Stmt.staticTime]
  | n + 1 => by
    show (shr1Loop d a sc n).staticTime CostModel.unit + _ = _
    rw [shr1Loop_staticTime_unit d a sc n]
    simp [shr1Step, Stmt.staticTime, CostModel.unit]
    ring

theorem shr1Limbs_staticTime_unit (k d a sc : ℕ) :
    (shr1Limbs k d a sc).staticTime CostModel.unit = 3 * k + 2 := by
  show (Stmt.imm sc 1).staticTime CostModel.unit
    + ((Stmt.imm (sc + 1) 63).staticTime CostModel.unit
      + (shr1Loop d a sc k).staticTime CostModel.unit) = _
  rw [shr1Loop_staticTime_unit]
  simp [Stmt.staticTime, CostModel.unit]
  omega

theorem orLoop_staticTime_unit (acc a : ℕ) :
    ∀ n, (orLoop acc a n).staticTime CostModel.unit = n
  | 0 => by simp [orLoop, Stmt.staticTime]
  | n + 1 => by
    show (orLoop acc a n).staticTime CostModel.unit + _ = _
    rw [orLoop_staticTime_unit acc a n]; simp [Stmt.staticTime, CostModel.unit]

theorem nzLimbs_staticTime_unit (k a w : ℕ) :
    (nzLimbs k a w).staticTime CostModel.unit = k + 2 := by
  show (Stmt.imm (w + 1) 0).staticTime CostModel.unit
    + ((orLoop (w + 1) a k).staticTime CostModel.unit
      + (Stmt.un .isNonZero (w + 1) (w + 1)).staticTime CostModel.unit) = _
  rw [orLoop_staticTime_unit]
  simp [Stmt.staticTime, CostModel.unit]
  omega

theorem halfModP_staticTime_unit (k a pReg w : ℕ) :
    (halfModP k a pReg w).staticTime CostModel.unit = 12 * k + 6 := by
  show (immLimbs w 0 k).staticTime CostModel.unit
    + ((Stmt.imm (w + k + 1) (2 : Word 64)).staticTime CostModel.unit
      + ((Stmt.bin (w := 64) .umod (w + k) a (w + k + 1)).staticTime CostModel.unit
        + ((selectLimbs k (w + k + 3) pReg w (w + k) (w + k + 2)).staticTime
              CostModel.unit
          + ((addLimbs k (w + 2 * k + 7) a (w + k + 3) (w + 2 * k + 3)).staticTime
                CostModel.unit
            + ((Stmt.mov (w + 3 * k + 7) (w + 2 * k + 3)).staticTime CostModel.unit
              + (shr1Limbs k (w + 3 * k + 12) (w + 2 * k + 7)
                  (w + 3 * k + 8)).staticTime CostModel.unit))))) = _
  rw [immLimbs_staticTime, selectLimbs_staticTime,
    show addLimbs k (w + 2 * k + 7) a (w + k + 3) (w + 2 * k + 3)
      = addLimbsC k (w + 2 * k + 7) a (w + k + 3) (w + 2 * k + 3) 0 from rfl,
    addLimbsC_staticTime, shr1Limbs_staticTime_unit]
  simp [Stmt.staticTime, addStepCost, selStepCost, CostModel.unit]
  omega

theorem shrCopy_staticTime_unit (k dst src w : ℕ) :
    (shrCopy k dst src w).staticTime CostModel.unit = 5 * k + 3 := by
  show (movLimbs k w src).staticTime CostModel.unit
    + ((Stmt.imm (w + k) 0).staticTime CostModel.unit
      + ((shr1Limbs k (w + k + 5) w (w + k + 1)).staticTime CostModel.unit
        + (movLimbs k dst (w + k + 5)).staticTime CostModel.unit)) = _
  rw [movLimbs_staticTime_unit, movLimbs_staticTime_unit, shr1Limbs_staticTime_unit]
  simp [Stmt.staticTime, CostModel.unit]
  omega

theorem halfCopy_staticTime_unit (k dst src pReg w : ℕ) :
    (halfCopy k dst src pReg w).staticTime CostModel.unit = 13 * k + 6 := by
  show (halfModP k src pReg w).staticTime CostModel.unit
    + (movLimbs k dst (halfModPOut k w)).staticTime CostModel.unit = _
  rw [halfModP_staticTime_unit, movLimbs_staticTime_unit]
  omega

theorem subModCopy_staticTime_unit (k dst x y pReg w : ℕ) :
    (subModCopy k dst x y pReg w).staticTime CostModel.unit = 15 * k + 2 := by
  show (montSub k x y pReg w).staticTime CostModel.unit
    + (movLimbs k dst (montSubOut k w)).staticTime CostModel.unit = _
  rw [montSub_staticTime_unit, movLimbs_staticTime_unit]
  omega

/-- A row costs `45k + 19` unit steps in the worst case. -/
theorem invStep_staticTime_unit (k u v r s pReg W : ℕ) :
    (invStep k u v r s pReg W).staticTime CostModel.unit = 45 * k + 19 := by
  simp only [invStep, Stmt.staticTime, shrCopy_staticTime_unit,
    halfCopy_staticTime_unit, subModCopy_staticTime_unit, subLimbs_staticTime]
  simp only [addStepCost, CostModel.unit, Nat.max_def]
  split_ifs <;> omega

/-- One pass of the loop costs `46k + 24` unit steps in the worst case. -/
theorem invBody_staticTime_unit (k u v r s pReg cnt W : ℕ) :
    (invBody k u v r s pReg cnt W).staticTime CostModel.unit = 46 * k + 24 := by
  simp only [invBody, Stmt.staticTime, nzLimbs_staticTime_unit,
    invStep_staticTime_unit]
  simp only [CostModel.unit, Nat.max_def]
  split_ifs <;> omega

/-! ## Register-only, and the frame

Two facts per block. `RegOnly` says it always executes and never touches memory, so a
`Triple` for it needs no precondition; `WritesAbove` says which registers it can
disturb, which is how the counter survives a row. -/

theorem immLimbs_regOnly (base v : ℕ) : ∀ n, (immLimbs base v n).RegOnly
  | 0 => trivial
  | n + 1 => ⟨immLimbs_regOnly base v n, trivial⟩

theorem immLimbs_writesAbove {base v lo : ℕ} (h : lo ≤ base) :
    ∀ n, (immLimbs base v n).WritesAbove lo
  | 0 => writesAbove_skip lo
  | n + 1 => (immLimbs_writesAbove h n).seq
      (writesAbove_imm (show lo ≤ base + n by omega))

theorem addLoop_regOnly (d a b sc : ℕ) : ∀ n, (addLoop d a b sc n).RegOnly
  | 0 => trivial
  | n + 1 => ⟨addLoop_regOnly d a b sc n, by simp [addStep]⟩

theorem addLoop_writesAbove {d a b sc lo : ℕ} (hd : lo ≤ d) (hs : lo ≤ sc) :
    ∀ n, (addLoop d a b sc n).WritesAbove lo
  | 0 => writesAbove_skip lo
  | n + 1 => (addLoop_writesAbove hd hs n).seq
      ((writesAbove_bin (show lo ≤ sc + 1 by omega)).seq
        ((writesAbove_bin (show lo ≤ sc + 2 by omega)).seq
          ((writesAbove_bin (show lo ≤ d + n by omega)).seq
            ((writesAbove_bin (show lo ≤ sc + 3 by omega)).seq
              (writesAbove_bin (show lo ≤ sc from hs))))))

theorem addLimbsC_regOnly (k d a b sc c0 : ℕ) : (addLimbsC k d a b sc c0).RegOnly :=
  ⟨trivial, addLoop_regOnly d a b sc k⟩

theorem addLimbsC_writesAbove {k d a b sc c0 lo : ℕ} (hd : lo ≤ d) (hs : lo ≤ sc) :
    (addLimbsC k d a b sc c0).WritesAbove lo :=
  (writesAbove_imm (show lo ≤ sc from hs)).seq (addLoop_writesAbove hd hs k)

theorem notLoop_regOnly (nb b : ℕ) : ∀ n, (notLoop nb b n).RegOnly
  | 0 => trivial
  | n + 1 => ⟨notLoop_regOnly nb b n, trivial⟩

theorem notLoop_writesAbove {nb b lo : ℕ} (h : lo ≤ nb) :
    ∀ n, (notLoop nb b n).WritesAbove lo
  | 0 => writesAbove_skip lo
  | n + 1 => (notLoop_writesAbove h n).seq
      (writesAbove_un (show lo ≤ nb + n by omega))

theorem subLimbs_regOnly (k d a b nb sc : ℕ) : (subLimbs k d a b nb sc).RegOnly :=
  ⟨notLoop_regOnly nb b k, addLimbsC_regOnly k d a nb sc 1⟩

theorem subLimbs_writesAbove {k d a b nb sc lo : ℕ} (hd : lo ≤ d) (hn : lo ≤ nb)
    (hs : lo ≤ sc) : (subLimbs k d a b nb sc).WritesAbove lo :=
  (notLoop_writesAbove hn k).seq (addLimbsC_writesAbove hd hs)

theorem selectLoop_regOnly (d a b f sc : ℕ) : ∀ n, (selectLoop d a b f sc n).RegOnly
  | 0 => trivial
  | n + 1 => ⟨selectLoop_regOnly d a b f sc n, by simp [selectStep]⟩

theorem selectLoop_writesAbove {d a b f sc lo : ℕ} (hd : lo ≤ d) (hs : lo ≤ sc) :
    ∀ n, (selectLoop d a b f sc n).WritesAbove lo
  | 0 => writesAbove_skip lo
  | n + 1 => (selectLoop_writesAbove hd hs n).seq
      ((writesAbove_bin (show lo ≤ sc from hs)).seq
        ((writesAbove_bin (show lo ≤ sc from hs)).seq
          (writesAbove_bin (show lo ≤ d + n by omega))))

theorem selectLimbs_regOnly (k d a b f sc : ℕ) : (selectLimbs k d a b f sc).RegOnly :=
  selectLoop_regOnly d a b f sc k

theorem selectLimbs_writesAbove {k d a b f sc lo : ℕ} (hd : lo ≤ d) (hs : lo ≤ sc) :
    (selectLimbs k d a b f sc).WritesAbove lo :=
  selectLoop_writesAbove hd hs k

theorem montSub_regOnly (k a b pReg w : ℕ) : (montSub k a b pReg w).RegOnly :=
  ⟨subLimbs_regOnly .., addLimbsC_regOnly .., selectLimbs_regOnly ..⟩

theorem montSub_writesAbove {k a b pReg w lo : ℕ} (h : lo ≤ w) :
    (montSub k a b pReg w).WritesAbove lo :=
  (subLimbs_writesAbove (show lo ≤ w + k + 4 by omega) (show lo ≤ w from h)
      (show lo ≤ w + k by omega)).seq
    ((addLimbsC_writesAbove (show lo ≤ w + 2 * k + 8 by omega)
        (show lo ≤ w + 2 * k + 4 by omega)).seq
      (selectLimbs_writesAbove
        (show lo ≤ montSubOut k w by simp only [montSubOut]; omega)
        (show lo ≤ w + 3 * k + 8 by omega)))

theorem movLoop_regOnly (d a : ℕ) : ∀ n, (movLoop d a n).RegOnly
  | 0 => trivial
  | n + 1 => ⟨movLoop_regOnly d a n, trivial⟩

theorem movLoop_writesAbove {d a lo : ℕ} (h : lo ≤ d) :
    ∀ n, (movLoop d a n).WritesAbove lo
  | 0 => writesAbove_skip lo
  | n + 1 => (movLoop_writesAbove h n).seq
      (writesAbove_mov (show lo ≤ d + n by omega))

theorem movLimbs_regOnly (k d a : ℕ) : (movLimbs k d a).RegOnly := movLoop_regOnly d a k

theorem movLimbs_writesAbove {k d a lo : ℕ} (h : lo ≤ d) :
    (movLimbs k d a).WritesAbove lo := movLoop_writesAbove h k

theorem shr1Loop_regOnly (d a sc : ℕ) : ∀ n, (shr1Loop d a sc n).RegOnly
  | 0 => trivial
  | n + 1 => ⟨shr1Loop_regOnly d a sc n, by simp [shr1Step]⟩

theorem shr1Loop_writesAbove {d a sc lo : ℕ} (hd : lo ≤ d) (hs : lo ≤ sc) :
    ∀ n, (shr1Loop d a sc n).WritesAbove lo
  | 0 => writesAbove_skip lo
  | n + 1 => (shr1Loop_writesAbove hd hs n).seq
      ((writesAbove_bin (show lo ≤ sc + 2 by omega)).seq
        ((writesAbove_bin (show lo ≤ sc + 3 by omega)).seq
          (writesAbove_bin (show lo ≤ d + n by omega))))

theorem shr1Limbs_regOnly (k d a sc : ℕ) : (shr1Limbs k d a sc).RegOnly :=
  ⟨trivial, trivial, shr1Loop_regOnly d a sc k⟩

theorem shr1Limbs_writesAbove {k d a sc lo : ℕ} (hd : lo ≤ d) (hs : lo ≤ sc) :
    (shr1Limbs k d a sc).WritesAbove lo :=
  (writesAbove_imm (show lo ≤ sc from hs)).seq
    ((writesAbove_imm (show lo ≤ sc + 1 by omega)).seq
      (shr1Loop_writesAbove hd hs k))

theorem orLoop_regOnly (acc a : ℕ) : ∀ n, (orLoop acc a n).RegOnly
  | 0 => trivial
  | n + 1 => ⟨orLoop_regOnly acc a n, trivial⟩

theorem orLoop_writesAbove {acc a lo : ℕ} (h : lo ≤ acc) :
    ∀ n, (orLoop acc a n).WritesAbove lo
  | 0 => writesAbove_skip lo
  | n + 1 => (orLoop_writesAbove h n).seq (writesAbove_bin (show lo ≤ acc from h))

theorem nzLimbs_regOnly (k a w : ℕ) : (nzLimbs k a w).RegOnly :=
  ⟨trivial, orLoop_regOnly (w + 1) a k, trivial⟩

theorem nzLimbs_writesAbove {k a w lo : ℕ} (h : lo ≤ w) :
    (nzLimbs k a w).WritesAbove lo :=
  (writesAbove_imm (show lo ≤ w + 1 by omega)).seq
    ((orLoop_writesAbove (show lo ≤ w + 1 by omega) k).seq
      (writesAbove_un (show lo ≤ w + 1 by omega)))

theorem halfModP_regOnly (k a pReg w : ℕ) : (halfModP k a pReg w).RegOnly :=
  ⟨immLimbs_regOnly .., trivial, trivial, selectLimbs_regOnly .., addLimbsC_regOnly ..,
    trivial, shr1Limbs_regOnly ..⟩

theorem halfModP_writesAbove {k a pReg w lo : ℕ} (h : lo ≤ w) :
    (halfModP k a pReg w).WritesAbove lo :=
  (immLimbs_writesAbove h k).seq
    ((writesAbove_imm (show lo ≤ w + k + 1 by omega)).seq
      ((writesAbove_bin (show lo ≤ w + k by omega)).seq
        ((selectLimbs_writesAbove (show lo ≤ w + k + 3 by omega)
            (show lo ≤ w + k + 2 by omega)).seq
          ((addLimbsC_writesAbove (show lo ≤ w + 2 * k + 7 by omega)
              (show lo ≤ w + 2 * k + 3 by omega)).seq
            ((writesAbove_mov (show lo ≤ w + 3 * k + 7 by omega)).seq
              (shr1Limbs_writesAbove (show lo ≤ w + 3 * k + 12 by omega)
                (show lo ≤ w + 3 * k + 8 by omega)))))))

theorem shrCopy_regOnly (k dst src w : ℕ) : (shrCopy k dst src w).RegOnly :=
  ⟨movLimbs_regOnly .., trivial, shr1Limbs_regOnly .., movLimbs_regOnly ..⟩

theorem shrCopy_writesAbove {k dst src w lo : ℕ} (hw : lo ≤ w) (hd : lo ≤ dst) :
    (shrCopy k dst src w).WritesAbove lo :=
  (movLimbs_writesAbove (show lo ≤ w from hw)).seq
    ((writesAbove_imm (show lo ≤ w + k by omega)).seq
      ((shr1Limbs_writesAbove (show lo ≤ w + k + 5 by omega)
          (show lo ≤ w + k + 1 by omega)).seq
        (movLimbs_writesAbove (show lo ≤ dst from hd))))

theorem halfCopy_regOnly (k dst src pReg w : ℕ) : (halfCopy k dst src pReg w).RegOnly :=
  ⟨halfModP_regOnly .., movLimbs_regOnly ..⟩

theorem halfCopy_writesAbove {k dst src pReg w lo : ℕ} (hw : lo ≤ w) (hd : lo ≤ dst) :
    (halfCopy k dst src pReg w).WritesAbove lo :=
  (halfModP_writesAbove hw).seq (movLimbs_writesAbove (show lo ≤ dst from hd))

theorem subModCopy_regOnly (k dst x y pReg w : ℕ) :
    (subModCopy k dst x y pReg w).RegOnly := ⟨montSub_regOnly .., movLimbs_regOnly ..⟩

theorem subModCopy_writesAbove {k dst x y pReg w lo : ℕ} (hw : lo ≤ w) (hd : lo ≤ dst) :
    (subModCopy k dst x y pReg w).WritesAbove lo :=
  (montSub_writesAbove hw).seq (movLimbs_writesAbove (show lo ≤ dst from hd))

theorem invStep_regOnly (k u v r s pReg W : ℕ) : (invStep k u v r s pReg W).RegOnly :=
  ⟨trivial, trivial, trivial,
    ⟨⟨subLimbs_regOnly .., subLimbs_regOnly ..,
        ⟨⟨shrCopy_regOnly .., subModCopy_regOnly .., halfCopy_regOnly ..⟩,
          ⟨shrCopy_regOnly .., subModCopy_regOnly .., halfCopy_regOnly ..⟩⟩⟩,
      ⟨shrCopy_regOnly .., halfCopy_regOnly ..⟩⟩,
    ⟨shrCopy_regOnly .., halfCopy_regOnly ..⟩⟩

theorem invStep_writesAbove {k u v r s pReg W lo : ℕ} (hW : lo ≤ W) (hu : lo ≤ u)
    (hv : lo ≤ v) (hr : lo ≤ r) (hs : lo ≤ s) :
    (invStep k u v r s pReg W).WritesAbove lo :=
  (writesAbove_imm (show lo ≤ W from hW)).seq
    ((writesAbove_bin (show lo ≤ W + 1 by omega)).seq
      ((writesAbove_bin (show lo ≤ W + 2 by omega)).seq
        (Stmt.WritesAbove.ifNZ
          (Stmt.WritesAbove.ifNZ
            ((subLimbs_writesAbove (show lo ≤ W + 3 + k + 4 by omega)
                (show lo ≤ W + 3 by omega) (show lo ≤ W + 3 + k by omega)).seq
              ((subLimbs_writesAbove (show lo ≤ W + 3 + 3 * k + 8 by omega)
                  (show lo ≤ W + 3 + 2 * k + 4 by omega)
                  (show lo ≤ W + 3 + 3 * k + 4 by omega)).seq
                (Stmt.WritesAbove.ifNZ
                  ((shrCopy_writesAbove (show lo ≤ W + 3 + 4 * k + 8 by omega) hu).seq
                    ((subModCopy_writesAbove
                        (show lo ≤ W + 3 + 4 * k + 8 + shrCopyFrame k by
                          simp only [shrCopyFrame]; omega) hr).seq
                      (halfCopy_writesAbove
                        (show lo ≤ W + 3 + 4 * k + 8 + shrCopyFrame k
                            + subModCopyFrame k by
                          simp only [shrCopyFrame, subModCopyFrame, montSubFrame]
                          omega) hr)))
                  ((shrCopy_writesAbove (show lo ≤ W + 3 + 4 * k + 8 by omega) hv).seq
                    ((subModCopy_writesAbove
                        (show lo ≤ W + 3 + 4 * k + 8 + shrCopyFrame k by
                          simp only [shrCopyFrame]; omega) hs).seq
                      (halfCopy_writesAbove
                        (show lo ≤ W + 3 + 4 * k + 8 + shrCopyFrame k
                            + subModCopyFrame k by
                          simp only [shrCopyFrame, subModCopyFrame, montSubFrame]
                          omega) hs))))))
            ((shrCopy_writesAbove (show lo ≤ W + 3 by omega) hv).seq
              (halfCopy_writesAbove
                (show lo ≤ W + 3 + shrCopyFrame k by
                  simp only [shrCopyFrame]; omega) hs)))
          ((shrCopy_writesAbove (show lo ≤ W + 3 by omega) hu).seq
            (halfCopy_writesAbove
              (show lo ≤ W + 3 + shrCopyFrame k by
                simp only [shrCopyFrame]; omega) hr)))))

theorem invBody_regOnly (k u v r s pReg cnt W : ℕ) :
    (invBody k u v r s pReg cnt W).RegOnly :=
  ⟨nzLimbs_regOnly .., ⟨trivial, trivial, invStep_regOnly ..⟩, trivial⟩

/-! ## What the gadgets compute

The time bound above needs none of this. What follows is the value side: each gadget's
`Exec` spec, built up to `invLimbs_exec`. -/

theorem movLoop_exec {k d a : ℕ} (hdis : d + k ≤ a ∨ a + k ≤ d)
    {s : State 64} {A : ℕ} (har : RegsEnc s a k A) :
    ∀ n ≤ k, ∃ s' t dd pp, Exec C (movLoop d a n) s s' t dd pp ∧
      (∀ j < n, s'.regs (d + j) = BitVec.ofNat 64 (limb 64 A j)) ∧
      (∀ q, q < d ∨ d + n ≤ q → s'.regs q = s.regs q) ∧
      s'.bufs = s.bufs ∧ s'.caps = s.caps := by
  intro n
  induction n with
  | zero =>
    intro _
    exact ⟨s, 0, 0, 0, .skip, fun _ hj => absurd hj (by omega), fun _ _ => rfl, rfl, rfl⟩
  | succ n ih =>
    intro hn
    obtain ⟨s₁, t₁, d₁, p₁, hex₁, hd₁, hpres₁, hbuf₁, hcap₁⟩ := ih (by omega)
    have hsrc : s₁.regs (a + n) = BitVec.ofNat 64 (limb 64 A n) := by
      rw [hpres₁ (a + n) (by omega)]; exact har n (by omega)
    refine ⟨_, _, _, _, .seq hex₁ .mov, ?_, ?_, ?_, ?_⟩
    · intro j hj
      rcases Nat.lt_or_ge j n with hlt | hge
      · rw [regs_setReg_ne _ _ (show d + j ≠ d + n by omega)]; exact hd₁ j hlt
      · have : j = n := by omega
        subst this
        rw [regs_setReg_self]; exact hsrc
    · intro q hq
      rw [regs_setReg_ne _ _ (show q ≠ d + n by omega), hpres₁ q (by omega)]
    · simpa using hbuf₁
    · simpa using hcap₁

/-- A copy moves the value, and touches nothing outside its destination. -/
theorem movLimbs_exec {k d a : ℕ} (hdis : d + k ≤ a ∨ a + k ≤ d)
    {s : State 64} {A : ℕ} (har : RegsEnc s a k A) :
    ∃ s' t dd pp, Exec C (movLimbs k d a) s s' t dd pp ∧
      RegsEnc s' d k A ∧
      (∀ q, q < d ∨ d + k ≤ q → s'.regs q = s.regs q) ∧
      s'.bufs = s.bufs ∧ s'.caps = s.caps :=
  movLoop_exec hdis har k le_rfl

/-! ### The zero test -/

theorem orLoop_exec {k a w : ℕ} (hopA : a + k ≤ w) {s : State 64}
    (hacc : s.regs (w + 1) = 0) :
    ∀ n ≤ k, ∃ s' t dd pp, Exec C (orLoop (w + 1) a n) s s' t dd pp ∧
      (s'.regs (w + 1) = 0 ↔ ∀ j < n, s.regs (a + j) = 0) ∧
      (∀ q, q ≠ w + 1 → s'.regs q = s.regs q) ∧
      s'.bufs = s.bufs ∧ s'.caps = s.caps := by
  intro n
  induction n with
  | zero =>
    intro _
    exact ⟨s, 0, 0, 0, .skip, ⟨fun _ j hj => absurd hj (by omega), fun _ => hacc⟩,
      fun _ _ => rfl, rfl, rfl⟩
  | succ n ih =>
    intro hn
    obtain ⟨s₁, t₁, d₁, p₁, hex₁, hiff, hpres₁, hbuf₁, hcap₁⟩ := ih (by omega)
    refine ⟨_, _, _, _, .seq hex₁ .bin, ?_, ?_, ?_, ?_⟩
    · rw [regs_setReg_self, hpres₁ (a + n) (by omega)]
      show ((s₁.regs (w + 1) ||| s.regs (a + n) : Word 64) = 0) ↔ _
      rw [word_or_eq_zero, hiff]
      constructor
      · rintro ⟨h1, h2⟩ j hj
        rcases Nat.lt_or_ge j n with hlt | hge
        · exact h1 j hlt
        · have : j = n := by omega
          subst this; exact h2
      · intro h; exact ⟨fun j hj => h j (by omega), h n (by omega)⟩
    · intro q hq
      rw [regs_setReg_ne _ _ hq, hpres₁ q hq]
    · simpa using hbuf₁
    · simpa using hcap₁

/-- **The zero test is correct.** -/
theorem nzLimbs_exec {k a w : ℕ} (hopA : a + k ≤ w)
    {s : State 64} {A : ℕ} (hA : A < 2 ^ (64 * k)) (har : RegsEnc s a k A) :
    ∃ s' t dd pp, Exec C (nzLimbs k a w) s s' t dd pp ∧
      s'.regs (nzOut w) = BitVec.ofNat 64 (if A = 0 then 0 else 1) ∧
      (∀ q, q ≠ w + 1 → s'.regs q = s.regs q) ∧
      s'.bufs = s.bufs ∧ s'.caps = s.caps := by
  have hacc : (s.setReg (w + 1) (0 : Word 64)).regs (w + 1) = 0 := by simp
  obtain ⟨s₁, t₁, d₁, p₁, hex₁, hiff, hpres₁, hbuf₁, hcap₁⟩ :=
    orLoop_exec (C := C) hopA hacc k le_rfl
  have hzero : (∀ j < k, (s.setReg (w + 1) (0 : Word 64)).regs (a + j) = 0) ↔ A = 0 := by
    constructor
    · intro h
      refine eq_of_limbs hA (Nat.two_pow_pos _) fun j hj => ?_
      have := h j hj
      rw [regs_setReg_ne _ _ (show a + j ≠ w + 1 by omega), har j hj] at this
      have hnat := congrArg BitVec.toNat this
      have hlt := limb_lt 64 A j
      have hz : (0 : Word 64).toNat = 0 := rfl
      have hz2 : limb 64 0 j = 0 := by simp [limb]
      simp only [BitVec.toNat_ofNat] at hnat
      omega
    · rintro rfl j hj
      rw [regs_setReg_ne _ _ (show a + j ≠ w + 1 by omega), har j hj]
      simp [limb]
  refine ⟨_, _, _, _, .seq .imm (.seq hex₁ .un), ?_, ?_, ?_, ?_⟩
  · rw [show nzOut w = w + 1 from rfl, regs_setReg_self]
    show (if s₁.regs (w + 1) = 0 then 0 else 1 : Word 64) = _
    by_cases hA0 : A = 0
    · rw [if_pos (hiff.mpr (hzero.mpr hA0)), if_pos hA0]; simp
    · rw [if_neg (fun h => hA0 (hzero.mp (hiff.mp h))), if_neg hA0]; simp
  · intro q hq
    rw [regs_setReg_ne _ _ hq, hpres₁ q hq, regs_setReg_ne _ _ hq]
  · simpa using hbuf₁
  · simpa using hcap₁

/-! ### The limb arithmetic of a shift

Shifting a value down one place moves each limb's top bits down and pulls in the low
bit of the limb above — which is exactly the two halves the step computes, and they
occupy disjoint bits, so adding them is combining them. -/

theorem limb_div_two (A j : ℕ) :
    limb 64 (A / 2) j = limb 64 A j / 2 + limb 64 A (j + 1) % 2 * 2 ^ 63 := by
  have hpow : (2:ℕ) ^ (64 * (j + 1)) = 2 ^ (64 * j) * 2 ^ 64 := by
    rw [← pow_add]; ring_nf
  have hd : A / 2 / 2 ^ (64 * j) = A / 2 ^ (64 * j) / 2 := by
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm]
  have hd2 : A / 2 ^ (64 * (j + 1)) = A / 2 ^ (64 * j) / 2 ^ 64 := by
    rw [hpow, ← Nat.div_div_eq_div_mul]
  simp only [limb, hd, hd2]
  omega

/-! ### The shift itself -/

theorem word_shr_one {x : ℕ} (hx : x < 2 ^ 64) :
    (BitVec.ofNat 64 x) >>> ((BitVec.ofNat 64 1).toNat)
      = BitVec.ofNat 64 (x / 2) := by
  rw [show (BitVec.ofNat 64 1).toNat = 1 from rfl]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega

theorem word_shl_63 (y : ℕ) :
    (BitVec.ofNat 64 y) <<< ((BitVec.ofNat 64 63).toNat)
      = BitVec.ofNat 64 (y % 2 * 2 ^ 63) := by
  rw [show (BitVec.ofNat 64 63).toNat = 63 from rfl]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq_mul_pow]
  omega

theorem shr1Loop_exec {k d a sc : ℕ} (hasc : a + k + 1 ≤ sc) (hscd : sc + 4 ≤ d)
    {s : State 64} {A : ℕ}
    (har : ∀ j < k + 1, s.regs (a + j) = BitVec.ofNat 64 (limb 64 A j))
    (h1 : s.regs sc = BitVec.ofNat 64 1)
    (h63 : s.regs (sc + 1) = BitVec.ofNat 64 63) :
    ∀ n ≤ k, ∃ s' t dd pp, Exec C (shr1Loop d a sc n) s s' t dd pp ∧
      (∀ j < n, s'.regs (d + j) = BitVec.ofNat 64 (limb 64 (A / 2) j)) ∧
      (∀ q, q ≠ sc + 2 → q ≠ sc + 3 → (q < d ∨ d + n ≤ q) →
        s'.regs q = s.regs q) ∧
      s'.bufs = s.bufs ∧ s'.caps = s.caps := by
  intro n
  induction n with
  | zero =>
    intro _
    exact ⟨s, 0, 0, 0, .skip, fun _ hj => absurd hj (by omega),
      fun _ _ _ _ => rfl, rfl, rfl⟩
  | succ n ih =>
    intro hn
    obtain ⟨s₁, t₁, d₁, p₁, hex₁, hd₁, hpres₁, hbuf₁, hcap₁⟩ := ih (by omega)
    have hxj : s₁.regs (a + n) = BitVec.ofNat 64 (limb 64 A n) := by
      rw [hpres₁ _ (by omega) (by omega) (by omega)]; exact har n (by omega)
    have hxj1 : s₁.regs (a + n + 1) = BitVec.ofNat 64 (limb 64 A (n + 1)) := by
      rw [hpres₁ _ (by omega) (by omega) (by omega),
        show a + n + 1 = a + (n + 1) by ring]
      exact har (n + 1) (by omega)
    have hsc : s₁.regs sc = BitVec.ofNat 64 1 := by
      rw [hpres₁ _ (by omega) (by omega) (by omega)]; exact h1
    have hsc1 : s₁.regs (sc + 1) = BitVec.ofNat 64 63 := by
      rw [hpres₁ _ (by omega) (by omega) (by omega)]; exact h63
    have hbound : limb 64 A n / 2 + limb 64 A (n + 1) % 2 * 2 ^ 63 < 2 ^ 64 := by
      have := limb_lt 64 A n
      omega
    refine ⟨_, _, _, _, .seq hex₁ (.seq .bin (.seq .bin .bin)), ?_, ?_, ?_, ?_⟩
    · intro j hj
      rcases Nat.lt_or_ge j n with hlt | hge
      · rw [regs_setReg_ne _ _ (show d + j ≠ d + n by omega),
          regs_setReg_ne _ _ (show d + j ≠ sc + 3 by omega),
          regs_setReg_ne _ _ (show d + j ≠ sc + 2 by omega)]
        exact hd₁ j hlt
      · have hjn : j = n := by omega
        rw [hjn, regs_setReg_self]
        show (BinOp.eval .add
          (((s₁.setReg (sc + 2) _).setReg (sc + 3) _).regs (sc + 2))
          (((s₁.setReg (sc + 2) _).setReg (sc + 3) _).regs (sc + 3)) : Word 64) = _
        rw [regs_setReg_ne _ _ (show sc + 2 ≠ sc + 3 by omega), regs_setReg_self,
          regs_setReg_self, regs_setReg_ne _ _ (show a + n + 1 ≠ sc + 2 by omega),
          regs_setReg_ne _ _ (show sc + 1 ≠ sc + 2 by omega), hxj, hxj1, hsc, hsc1]
        show ((BitVec.ofNat 64 (limb 64 A n) >>> (BitVec.ofNat 64 1).toNat
          + (BitVec.ofNat 64 (limb 64 A (n + 1))) <<< (BitVec.ofNat 64 63).toNat
          : Word 64)) = _
        rw [word_shr_one (limb_lt 64 A n), word_shl_63 (limb 64 A (n + 1)),
          word_add, Nat.mod_eq_of_lt hbound, limb_div_two]
    · intro q hq2 hq3 hq
      rw [regs_setReg_ne _ _ (show q ≠ d + n by omega),
        regs_setReg_ne _ _ hq3, regs_setReg_ne _ _ hq2,
        hpres₁ q hq2 hq3 (by omega)]
    · simpa using hbuf₁
    · simpa using hcap₁

/-- **The shift is correct.** From `k + 1` limbs of `A`, the destination's `k` limbs
hold `A / 2`. -/
theorem shr1Limbs_exec {k d a sc : ℕ} (hasc : a + k + 1 ≤ sc) (hscd : sc + 4 ≤ d)
    {s : State 64} {A : ℕ}
    (har : ∀ j < k + 1, s.regs (a + j) = BitVec.ofNat 64 (limb 64 A j)) :
    ∃ s' t dd pp, Exec C (shr1Limbs k d a sc) s s' t dd pp ∧
      RegsEnc s' d k (A / 2) ∧
      (∀ q, q < sc → s'.regs q = s.regs q) ∧
      (∀ q, d + k ≤ q → s'.regs q = s.regs q) ∧
      s'.bufs = s.bufs ∧ s'.caps = s.caps := by
  set s₀ := (s.setReg sc (BitVec.ofNat 64 1)).setReg (sc + 1) (BitVec.ofNat 64 63)
    with hs₀
  have har₀ : ∀ j < k + 1, s₀.regs (a + j) = BitVec.ofNat 64 (limb 64 A j) := by
    intro j hj
    rw [hs₀, regs_setReg_ne _ _ (show a + j ≠ sc + 1 by omega),
      regs_setReg_ne _ _ (show a + j ≠ sc by omega)]
    exact har j hj
  have h1₀ : s₀.regs sc = BitVec.ofNat 64 1 := by
    rw [hs₀, regs_setReg_ne _ _ (show sc ≠ sc + 1 by omega), regs_setReg_self]
  have h63₀ : s₀.regs (sc + 1) = BitVec.ofNat 64 63 := by
    rw [hs₀, regs_setReg_self]
  obtain ⟨s₁, t₁, d₁, p₁, hex₁, hd₁, hpres₁, hbuf₁, hcap₁⟩ :=
    shr1Loop_exec (C := C) hasc hscd har₀ h1₀ h63₀ k le_rfl
  refine ⟨s₁, _, _, _, .seq .imm (.seq .imm hex₁), hd₁, ?_, ?_, ?_, ?_⟩
  · intro q hq
    rw [hpres₁ q (by omega) (by omega) (by omega), hs₀,
      regs_setReg_ne _ _ (show q ≠ sc + 1 by omega),
      regs_setReg_ne _ _ (show q ≠ sc by omega)]
  · intro q hq
    rw [hpres₁ q (by omega) (by omega) (by omega), hs₀,
      regs_setReg_ne _ _ (show q ≠ sc + 1 by omega),
      regs_setReg_ne _ _ (show q ≠ sc by omega)]
  · rw [hbuf₁, hs₀]; simp
  · rw [hcap₁, hs₀]; simp

/-! ### Halving modulo the modulus -/

theorem word_umod_two (x : ℕ) :
    (BitVec.ofNat 64 x % BitVec.ofNat 64 2 : Word 64) = BitVec.ofNat 64 (x % 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_umod, show (BitVec.ofNat 64 2).toNat = 2 from rfl]
  simp only [BitVec.toNat_ofNat]
  omega

/-- **Halving modulo the modulus is correct.** -/
theorem halfModP_exec {k a pReg w : ℕ} (hopA : a + k ≤ w) (hmod : pReg + k ≤ w)
    {s : State 64} {p A : ℕ} (hp : p % 2 = 1) (hpR : p < 2 ^ (64 * k)) (hA : A < p)
    (har : RegsEnc s a k A) (hpr : RegsEnc s pReg k p) :
    ∃ s' t dd pp, Exec C (halfModP k a pReg w) s s' t dd pp ∧
      RegsEnc s' (halfModPOut k w) k (halfMod p A) ∧
      (∀ q, q < w → s'.regs q = s.regs q) ∧
      s'.bufs = s.bufs ∧ s'.caps = s.caps := by
  have hRpos : (0:ℕ) < 2 ^ (64 * k) := Nat.two_pow_pos _
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; simp at hpR; omega
    · exact h
  -- the zero block
  obtain ⟨s₁, t₁, d₁, p₁, hex₁, hz₁, hlow₁, hhigh₁, hbuf₁, hcap₁⟩ :=
    immLimbs_exec (C := C) w 0 (s := s) k
  -- the parity bit
  set s₂ := s₁.setReg (w + k + 1) (BitVec.ofNat 64 2) with hs₂
  have hpar : (BinOp.eval .umod (s₂.regs a) (s₂.regs (w + k + 1)) : Word 64)
      = BitVec.ofNat 64 (A % 2) := by
    have ha0 : s₂.regs a = BitVec.ofNat 64 (limb 64 A 0) := by
      rw [hs₂, regs_setReg_ne _ _ (show a ≠ w + k + 1 by omega),
        hlow₁ a (by omega)]
      have := har 0 hk; simpa using this
    have h2 : s₂.regs (w + k + 1) = BitVec.ofNat 64 2 := by rw [hs₂]; simp
    rw [ha0, h2]
    show (BitVec.ofNat 64 (limb 64 A 0) % BitVec.ofNat 64 2 : Word 64) = _
    rw [word_umod_two (limb 64 A 0)]
    congr 1
    simp only [limb, Nat.mul_zero, pow_zero, Nat.div_one]
    omega
  set s₃ := s₂.setReg (w + k) (BitVec.ofNat 64 (A % 2)) with hs₃
  have hex₃ : Exec C (.bin .umod (w + k) a (w + k + 1)) s₂ s₃ (C.bin .umod) 0 0 := by
    rw [hs₃, ← hpar]; exact .bin
  -- the conditional modulus
  have hsel : SelLayout k (w + k + 3) pReg w (w + k) (w + k + 2) :=
    ⟨by omega, by omega, by omega, by omega⟩
  have hpr₃ : RegsEnc s₃ pReg k p := by
    intro j hj
    rw [hs₃, regs_setReg_ne _ _ (show pReg + j ≠ w + k by omega), hs₂,
      regs_setReg_ne _ _ (show pReg + j ≠ w + k + 1 by omega), hlow₁ _ (by omega)]
    exact hpr j hj
  have hz₃ : RegsEnc s₃ w k 0 := by
    intro j hj
    rw [hs₃, regs_setReg_ne _ _ (show w + j ≠ w + k by omega), hs₂,
      regs_setReg_ne _ _ (show w + j ≠ w + k + 1 by omega)]
    exact hz₁ j hj
  have hflag₃ : s₃.regs (w + k) = BitVec.ofNat 64 (A % 2) := by rw [hs₃]; simp
  obtain ⟨s₄, t₄, d₄, p₄, hex₄, hsel₄, hpres₄, hbuf₄, hcap₄⟩ :=
    selectLimbs_exec (C := C) hsel (show A % 2 ≤ 1 by omega) hpr₃ hz₃ hflag₃
  -- the sum
  set pz := if A % 2 = 1 then p else 0 with hpz
  have hpzlt : pz < 2 ^ (64 * k) := by rw [hpz]; split_ifs <;> omega
  have hsel₄' : RegsEnc s₄ (w + k + 3) k pz := hsel₄
  have har₄ : RegsEnc s₄ a k A := by
    intro j hj
    rw [hpres₄ _ (by omega), hs₃, regs_setReg_ne _ _ (show a + j ≠ w + k by omega),
      hs₂, regs_setReg_ne _ _ (show a + j ≠ w + k + 1 by omega), hlow₁ _ (by omega)]
    exact har j hj
  have hadd : AddLayout k (w + 2 * k + 7) a (w + k + 3) (w + 2 * k + 3) :=
    ⟨by omega, by omega, by omega⟩
  obtain ⟨s₅, t₅, d₅, p₅, hex₅, hsum₅, hcar₅, hpres₅, hbuf₅, hcap₅⟩ :=
    addLimbs_exec (C := C) hadd (by omega) hpzlt har₄ hsel₄'
  -- the carry becomes the top limb
  have hAplt : A + pz < 2 ^ (64 * (k + 1)) := by
    have hpow : (2:ℕ) ^ (64 * (k + 1)) = 2 ^ (64 * k) * 2 ^ 64 := by
      rw [← pow_add]; ring_nf
    have h2 : (2:ℕ) ≤ 2 ^ 64 := by norm_num
    have : (2:ℕ) * 2 ^ (64 * k) ≤ 2 ^ (64 * k) * 2 ^ 64 := by
      rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ h2
    rw [hpow]; rw [hpz]; split_ifs <;> omega
  have hlimbs₆ : ∀ j < k + 1,
      (s₅.setReg (w + 3 * k + 7) (s₅.regs (w + 2 * k + 3))).regs (w + 2 * k + 7 + j)
        = BitVec.ofNat 64 (limb 64 (A + pz) j) := by
    intro j hj
    rcases Nat.lt_or_ge j k with hlt | hge
    · rw [regs_setReg_ne _ _ (show w + 2 * k + 7 + j ≠ w + 3 * k + 7 by omega)]
      exact hsum₅ j hlt
    · have hjk : j = k := by omega
      rw [hjk, show w + 2 * k + 7 + k = w + 3 * k + 7 by ring, regs_setReg_self,
        hcar₅, limb_top hAplt]
  -- the shift
  obtain ⟨s₇, t₇, d₇, p₇, hex₇, hd₇, hpres₇, hhigh₇, hbuf₇, hcap₇⟩ :=
    shr1Limbs_exec (C := C) (k := k) (d := w + 3 * k + 12) (a := w + 2 * k + 7)
      (sc := w + 3 * k + 8) (by omega) (by omega) hlimbs₆
  have hhalf : (A + pz) / 2 = halfMod p A := by
    rw [hpz]; unfold halfMod; split_ifs <;> omega
  refine ⟨s₇, _, _, _,
    .seq hex₁ (.seq .imm (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq .mov hex₇))))),
    ?_, ?_, ?_, ?_⟩
  · rw [show halfModPOut k w = w + 3 * k + 12 from rfl, ← hhalf]; exact hd₇
  · intro q hq
    rw [hpres₇ q (by omega), regs_setReg_ne _ _ (show q ≠ w + 3 * k + 7 by omega),
      hpres₅ q (by omega), hpres₄ q (by omega), hs₃,
      regs_setReg_ne _ _ (show q ≠ w + k by omega), hs₂,
      regs_setReg_ne _ _ (show q ≠ w + k + 1 by omega), hlow₁ q hq]
  · rw [hbuf₇]; simp only [bufs_setReg]; rw [hbuf₅, hbuf₄, hs₃, hs₂]; simpa using hbuf₁
  · rw [hcap₇]; simp only [caps_setReg]; rw [hcap₅, hcap₄, hs₃, hs₂]; simpa using hcap₁

/-! ### The three updates a row performs -/

theorem shrCopy_exec {k dst src w : ℕ} (hsrc : src + k ≤ w) (hdst : dst + k ≤ w)
    {st : State 64} {A : ℕ} (hA : A < 2 ^ (64 * k)) (har : RegsEnc st src k A) :
    ∃ st' t dd pp, Exec C (shrCopy k dst src w) st st' t dd pp ∧
      RegsEnc st' dst k (A / 2) ∧
      (∀ q, q < w → (q < dst ∨ dst + k ≤ q) → st'.regs q = st.regs q) ∧
      st'.bufs = st.bufs ∧ st'.caps = st.caps := by
  obtain ⟨s₁, t₁, d₁, p₁, hex₁, hd₁, hpres₁, hbuf₁, hcap₁⟩ :=
    movLimbs_exec (C := C) (d := w) (a := src) (Or.inr hsrc) har
  set s₂ := s₁.setReg (w + k) (0 : Word 64) with hs₂
  have hlimbs : ∀ j < k + 1, s₂.regs (w + j) = BitVec.ofNat 64 (limb 64 A j) := by
    intro j hj
    rcases Nat.lt_or_ge j k with hlt | hge
    · rw [hs₂, regs_setReg_ne _ _ (show w + j ≠ w + k by omega)]; exact hd₁ j hlt
    · have hjk : j = k := by omega
      rw [hjk, hs₂, regs_setReg_self, show limb 64 A k = 0 by
        simp only [limb]; rw [Nat.div_eq_of_lt hA]; simp]
      rfl
  obtain ⟨s₃, t₃, d₃, p₃, hex₃, hd₃, hpres₃, hhigh₃, hbuf₃, hcap₃⟩ :=
    shr1Limbs_exec (C := C) (k := k) (d := w + k + 5) (a := w) (sc := w + k + 1)
      (by omega) (by omega) hlimbs
  obtain ⟨s₄, t₄, d₄, p₄, hex₄, hd₄, hpres₄, hbuf₄, hcap₄⟩ :=
    movLimbs_exec (C := C) (d := dst) (a := w + k + 5) (Or.inl (by omega)) hd₃
  refine ⟨s₄, _, _, _, .seq hex₁ (.seq .imm (.seq hex₃ hex₄)), hd₄, ?_, ?_, ?_⟩
  · intro q hqw hqd
    rw [hpres₄ q hqd, hpres₃ q (by omega), hs₂,
      regs_setReg_ne _ _ (show q ≠ w + k by omega), hpres₁ q (Or.inl hqw)]
  · rw [hbuf₄, hbuf₃, hs₂]; simpa using hbuf₁
  · rw [hcap₄, hcap₃, hs₂]; simpa using hcap₁

theorem halfCopy_exec {k dst src pReg w : ℕ} (hsrc : src + k ≤ w)
    (hmod : pReg + k ≤ w) (hdst : dst + k ≤ w)
    {st : State 64} {p A : ℕ} (hp : p % 2 = 1) (hpR : p < 2 ^ (64 * k)) (hA : A < p)
    (har : RegsEnc st src k A) (hpr : RegsEnc st pReg k p) :
    ∃ st' t dd pp, Exec C (halfCopy k dst src pReg w) st st' t dd pp ∧
      RegsEnc st' dst k (halfMod p A) ∧
      (∀ q, q < w → (q < dst ∨ dst + k ≤ q) → st'.regs q = st.regs q) ∧
      st'.bufs = st.bufs ∧ st'.caps = st.caps := by
  obtain ⟨s₁, t₁, d₁, p₁, hex₁, hd₁, hpres₁, hbuf₁, hcap₁⟩ :=
    halfModP_exec (C := C) hsrc hmod hp hpR hA har hpr
  obtain ⟨s₂, t₂, d₂, p₂, hex₂, hd₂, hpres₂, hbuf₂, hcap₂⟩ :=
    movLimbs_exec (C := C) (d := dst) (a := halfModPOut k w)
      (Or.inl (by simp only [halfModPOut]; omega)) hd₁
  refine ⟨s₂, _, _, _, .seq hex₁ hex₂, hd₂, ?_, hbuf₂.trans hbuf₁, hcap₂.trans hcap₁⟩
  intro q hqw hqd
  rw [hpres₂ q hqd, hpres₁ q hqw]

theorem subModCopy_exec {k dst x y pReg w : ℕ} (hx : x + k ≤ w) (hy : y + k ≤ w)
    (hmod : pReg + k ≤ w) (hdst : dst + k ≤ w)
    {st : State 64} {p X Y : ℕ} (hp : 0 < p) (hpR : p < 2 ^ (64 * k))
    (hX : X < p) (hY : Y < p)
    (hxr : RegsEnc st x k X) (hyr : RegsEnc st y k Y) (hpr : RegsEnc st pReg k p) :
    ∃ st' t dd pp, Exec C (subModCopy k dst x y pReg w) st st' t dd pp ∧
      RegsEnc st' dst k (subMod p X Y) ∧
      (∀ q, q < w → (q < dst ∨ dst + k ≤ q) → st'.regs q = st.regs q) ∧
      st'.bufs = st.bufs ∧ st'.caps = st.caps := by
  obtain ⟨s₁, t₁, d₁, p₁, hex₁, hd₁, hpres₁, hbuf₁, hcap₁⟩ :=
    montSub_exec (C := C) ⟨hx, hy, hmod⟩ hp hpR hX hY hpr hxr hyr
  obtain ⟨s₂, t₂, d₂, p₂, hex₂, hd₂, hpres₂, hbuf₂, hcap₂⟩ :=
    movLimbs_exec (C := C) (d := dst) (a := montSubOut k w)
      (Or.inl (by simp only [montSubOut]; omega)) hd₁
  refine ⟨s₂, _, _, _, .seq hex₁ hex₂, ?_, ?_, hbuf₂.trans hbuf₁, hcap₂.trans hcap₁⟩
  · exact hd₂.congr (by simp [subMod])
  · intro q hqw hqd
    rw [hpres₂ q hqd, hpres₁ q hqw]

/-! ### The shape the branches share

All four branches shift one value down a place and rework one coefficient. Stating
the two shapes once, with the untouched blocks left anonymous — preservation is
"everything below the frame that is outside the two destinations" — is what keeps the
row's case analysis to its four cases rather than sixteen. -/

theorem word_ofNat_eq_zero {x : ℕ} (hx : x < 2 ^ 64) :
    (BitVec.ofNat 64 x = 0) ↔ x = 0 := by
  constructor
  · intro h
    have hn := congrArg BitVec.toNat h
    have hz : (0 : Word 64).toNat = 0 := rfl
    simp only [BitVec.toNat_ofNat] at hn
    omega
  · rintro rfl; rfl

/-- Shift one value, halve one coefficient. -/
theorem shrHalf_exec {k X Xsrc Y pReg W : ℕ}
    (hmod : pReg + k ≤ X) (hmodW : pReg + k ≤ W) (hsrc : Xsrc + k ≤ W)
    (hXW : X + k ≤ W) (hYW : Y + k ≤ W) (hXY : X + k ≤ Y ∨ Y + k ≤ X)
    {st : State 64} {p A B : ℕ}
    (hp : p % 2 = 1) (hpR : p < 2 ^ (64 * k)) (hA : A < 2 ^ (64 * k)) (hB : B < p)
    (hXr : RegsEnc st Xsrc k A) (hYr : RegsEnc st Y k B) (hpr : RegsEnc st pReg k p) :
    ∃ st' t dd pp,
      Exec C (shrCopy k X Xsrc W ;; halfCopy k Y Y pReg (W + shrCopyFrame k))
        st st' t dd pp ∧
      RegsEnc st' X k (A / 2) ∧ RegsEnc st' Y k (halfMod p B) ∧
      (∀ q, q < W → (q < X ∨ X + k ≤ q) → (q < Y ∨ Y + k ≤ q) →
        st'.regs q = st.regs q) ∧
      st'.bufs = st.bufs ∧ st'.caps = st.caps := by
  obtain ⟨s₁, t₁, d₁, p₁, hex₁, hX₁, hpres₁, hbuf₁, hcap₁⟩ :=
    shrCopy_exec (C := C) hsrc hXW hA hXr
  have hY₁ : RegsEnc s₁ Y k B := by
    intro j hj; rw [hpres₁ _ (by omega) (by omega)]; exact hYr j hj
  have hp₁ : RegsEnc s₁ pReg k p := by
    intro j hj; rw [hpres₁ _ (by omega) (by omega)]; exact hpr j hj
  obtain ⟨s₂, t₂, d₂, p₂, hex₂, hY₂, hpres₂, hbuf₂, hcap₂⟩ :=
    halfCopy_exec (C := C) (w := W + shrCopyFrame k)
      (show Y + k ≤ W + shrCopyFrame k by omega)
      (show pReg + k ≤ W + shrCopyFrame k by omega)
      (show Y + k ≤ W + shrCopyFrame k by omega) hp hpR hB hY₁ hp₁
  refine ⟨s₂, _, _, _, .seq hex₁ hex₂, ?_, hY₂, ?_,
    hbuf₂.trans hbuf₁, hcap₂.trans hcap₁⟩
  · intro j hj; rw [hpres₂ _ (by omega) (by omega)]; exact hX₁ j hj
  · intro q hqW hqX hqY
    rw [hpres₂ q (by omega) hqY, hpres₁ q hqW hqX]

/-- Shift one value, and rework one coefficient against another. -/
theorem shrSubHalf_exec {k X Xsrc Y Z pReg W : ℕ}
    (hmod : pReg + k ≤ X) (hmodY : pReg + k ≤ Y) (hmodW : pReg + k ≤ W)
    (hsrc : Xsrc + k ≤ W)
    (hXW : X + k ≤ W) (hYW : Y + k ≤ W) (hZW : Z + k ≤ W)
    (hXY : X + k ≤ Y ∨ Y + k ≤ X) (hXZ : X + k ≤ Z ∨ Z + k ≤ X)
    (hYZ : Y + k ≤ Z ∨ Z + k ≤ Y)
    {st : State 64} {p A B D : ℕ}
    (hp : p % 2 = 1) (hpR : p < 2 ^ (64 * k)) (hA : A < 2 ^ (64 * k))
    (hB : B < p) (hD : D < p)
    (hXr : RegsEnc st Xsrc k A) (hYr : RegsEnc st Y k B) (hZr : RegsEnc st Z k D)
    (hpr : RegsEnc st pReg k p) :
    ∃ st' t dd pp,
      Exec C (shrCopy k X Xsrc W ;;
        subModCopy k Y Y Z pReg (W + shrCopyFrame k) ;;
        halfCopy k Y Y pReg (W + shrCopyFrame k + subModCopyFrame k)) st st' t dd pp ∧
      RegsEnc st' X k (A / 2) ∧ RegsEnc st' Y k (halfMod p (subMod p B D)) ∧
      (∀ q, q < W → (q < X ∨ X + k ≤ q) → (q < Y ∨ Y + k ≤ q) →
        st'.regs q = st.regs q) ∧
      st'.bufs = st.bufs ∧ st'.caps = st.caps := by
  obtain ⟨s₁, t₁, d₁, p₁, hex₁, hX₁, hpres₁, hbuf₁, hcap₁⟩ :=
    shrCopy_exec (C := C) hsrc hXW hA hXr
  have hY₁ : RegsEnc s₁ Y k B := by
    intro j hj; rw [hpres₁ _ (by omega) (by omega)]; exact hYr j hj
  have hZ₁ : RegsEnc s₁ Z k D := by
    intro j hj; rw [hpres₁ _ (by omega) (by omega)]; exact hZr j hj
  have hp₁ : RegsEnc s₁ pReg k p := by
    intro j hj; rw [hpres₁ _ (by omega) (by omega)]; exact hpr j hj
  obtain ⟨s₂, t₂, d₂, p₂, hex₂, hY₂, hpres₂, hbuf₂, hcap₂⟩ :=
    subModCopy_exec (C := C) (w := W + shrCopyFrame k)
      (show Y + k ≤ W + shrCopyFrame k by omega)
      (show Z + k ≤ W + shrCopyFrame k by omega)
      (show pReg + k ≤ W + shrCopyFrame k by omega)
      (show Y + k ≤ W + shrCopyFrame k by omega)
      (show 0 < p by omega) hpR hB hD hY₁ hZ₁ hp₁
  have hp₂ : RegsEnc s₂ pReg k p := by
    intro j hj; rw [hpres₂ _ (by omega) (by omega)]; exact hp₁ j hj
  obtain ⟨s₃, t₃, d₃, p₃, hex₃, hY₃, hpres₃, hbuf₃, hcap₃⟩ :=
    halfCopy_exec (C := C) (w := W + shrCopyFrame k + subModCopyFrame k)
      (show Y + k ≤ W + shrCopyFrame k + subModCopyFrame k by omega)
      (show pReg + k ≤ W + shrCopyFrame k + subModCopyFrame k by omega)
      (show Y + k ≤ W + shrCopyFrame k + subModCopyFrame k by omega)
      hp hpR (subMod_lt (show 0 < p by omega)) hY₂ hp₂
  refine ⟨s₃, _, _, _, .seq hex₁ (.seq hex₂ hex₃), ?_, hY₃, ?_,
    hbuf₃.trans (hbuf₂.trans hbuf₁), hcap₃.trans (hcap₂.trans hcap₁)⟩
  · intro j hj
    rw [hpres₃ _ (by omega) (by omega), hpres₂ _ (by omega) (by omega)]
    exact hX₁ j hj
  · intro q hqW hqX hqY
    rw [hpres₃ q (by omega) hqY, hpres₂ q (by omega) hqY, hpres₁ q hqW hqX]

/-! ### One row

The four cases of `gcdRow`, each carried by one of the two shapes above. The parity
bits are `umod 2` rather than a mask, and the comparison is the subtraction's own
no-borrow bit, so nothing here needs bit-level reasoning. -/

theorem sub_flag {k A B : ℕ} (hA : A < 2 ^ (64 * k)) (hB : B < 2 ^ (64 * k)) :
    (A + 2 ^ (64 * k) - B) / 2 ^ (64 * k) = if B ≤ A then 1 else 0 := by
  split_ifs with hle
  · exact Nat.div_eq_of_lt_le (by omega) (by omega)
  · exact Nat.div_eq_of_lt (by omega)

/-- **One row is correct.** -/
theorem invStep_exec {k u v r s pReg W : ℕ}
    (hpu : pReg + k ≤ u) (huv : u + k ≤ v) (hvr : v + k ≤ r) (hrs : r + k ≤ s)
    (hsW : s + k ≤ W)
    {st : State 64} {p a U V R S : ℕ}
    (hp : p % 2 = 1) (hpR : p < 2 ^ (64 * k)) (h1 : 1 < p)
    (hinv : GcdInv p a U V R S)
    (hur : RegsEnc st u k U) (hvv : RegsEnc st v k V)
    (hrr : RegsEnc st r k R) (hss : RegsEnc st s k S)
    (hpr : RegsEnc st pReg k p) :
    ∃ st' t dd pp, Exec C (invStep k u v r s pReg W) st st' t dd pp ∧
      RegsEnc st' u k (gcdRow p U V R S).1 ∧
      RegsEnc st' v k (gcdRow p U V R S).2.1 ∧
      RegsEnc st' r k (gcdRow p U V R S).2.2.1 ∧
      RegsEnc st' s k (gcdRow p U V R S).2.2.2 ∧
      RegsEnc st' pReg k p ∧
      (∀ q, q < u → st'.regs q = st.regs q) ∧
      st'.bufs = st.bufs ∧ st'.caps = st.caps := by
  obtain ⟨hV0, hUlt, hVle, hRlt, hSlt, hpar, hg, hru, hsv⟩ := hinv
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; simp at hpR; omega
    · exact h
  have hUb : U < 2 ^ (64 * k) := by omega
  have hVb : V < 2 ^ (64 * k) := by omega
  -- the parity bits
  set st₁ := st.setReg W (BitVec.ofNat 64 2) with h₁
  have hu0 : st₁.regs u = BitVec.ofNat 64 (limb 64 U 0) := by
    rw [h₁, regs_setReg_ne _ _ (show u ≠ W by omega)]
    have := hur 0 hk; simpa using this
  have hW1 : st₁.regs W = BitVec.ofNat 64 2 := by rw [h₁]; simp
  have hval1 : (BinOp.eval .umod (st₁.regs u) (st₁.regs W) : Word 64)
      = BitVec.ofNat 64 (U % 2) := by
    rw [hu0, hW1]
    show (BitVec.ofNat 64 (limb 64 U 0) % BitVec.ofNat 64 2 : Word 64) = _
    rw [word_umod_two]
    congr 1
    simp only [limb, Nat.mul_zero, pow_zero, Nat.div_one]
    omega
  set st₂ := st₁.setReg (W + 1) (BitVec.ofNat 64 (U % 2)) with h₂
  have hex₂ : Exec C (.bin .umod (W + 1) u W) st₁ st₂ (C.bin .umod) 0 0 := by
    rw [h₂, ← hval1]; exact .bin
  have hv0 : st₂.regs v = BitVec.ofNat 64 (limb 64 V 0) := by
    rw [h₂, regs_setReg_ne _ _ (show v ≠ W + 1 by omega), h₁,
      regs_setReg_ne _ _ (show v ≠ W by omega)]
    have := hvv 0 hk; simpa using this
  have hW2 : st₂.regs W = BitVec.ofNat 64 2 := by
    rw [h₂, regs_setReg_ne _ _ (show W ≠ W + 1 by omega)]; exact hW1
  have hval2 : (BinOp.eval .umod (st₂.regs v) (st₂.regs W) : Word 64)
      = BitVec.ofNat 64 (V % 2) := by
    rw [hv0, hW2]
    show (BitVec.ofNat 64 (limb 64 V 0) % BitVec.ofNat 64 2 : Word 64) = _
    rw [word_umod_two]
    congr 1
    simp only [limb, Nat.mul_zero, pow_zero, Nat.div_one]
    omega
  set st₃ := st₂.setReg (W + 2) (BitVec.ofNat 64 (V % 2)) with h₃
  have hex₃ : Exec C (.bin .umod (W + 2) v W) st₂ st₃ (C.bin .umod) 0 0 := by
    rw [h₃, ← hval2]; exact .bin
  -- everything below `W` survives the prologue
  have hpres₃ : ∀ q, q < W → st₃.regs q = st.regs q := by
    intro q hq
    rw [h₃, regs_setReg_ne _ _ (show q ≠ W + 2 by omega), h₂,
      regs_setReg_ne _ _ (show q ≠ W + 1 by omega), h₁,
      regs_setReg_ne _ _ (show q ≠ W by omega)]
  have hu₃ : RegsEnc st₃ u k U := fun j hj => by
    rw [hpres₃ _ (by omega)]; exact hur j hj
  have hv₃ : RegsEnc st₃ v k V := fun j hj => by
    rw [hpres₃ _ (by omega)]; exact hvv j hj
  have hr₃ : RegsEnc st₃ r k R := fun j hj => by
    rw [hpres₃ _ (by omega)]; exact hrr j hj
  have hs₃ : RegsEnc st₃ s k S := fun j hj => by
    rw [hpres₃ _ (by omega)]; exact hss j hj
  have hp₃ : RegsEnc st₃ pReg k p := fun j hj => by
    rw [hpres₃ _ (by omega)]; exact hpr j hj
  have hf1 : st₃.regs (W + 1) = BitVec.ofNat 64 (U % 2) := by
    rw [h₃, regs_setReg_ne _ _ (show W + 1 ≠ W + 2 by omega), h₂]; simp
  have hf2 : st₃.regs (W + 2) = BitVec.ofNat 64 (V % 2) := by rw [h₃]; simp
  by_cases hue : U % 2 = 0
  · -- `u` is even
    have hrow : gcdRow p U V R S = (U / 2, V, halfMod p R, S) := by
      unfold gcdRow; rw [if_pos hue]
    obtain ⟨st', t', d', p', hex', hX, hY, hpres', hbuf', hcap'⟩ :=
      shrHalf_exec (C := C) (X := u) (Xsrc := u) (Y := r) (W := W + 3)
        (by omega) (by omega) (by omega) (by omega) (by omega) (Or.inl (by omega))
        hp hpR hUb (by omega) hu₃ hr₃ hp₃
    refine ⟨st', _, _, _,
      .seq .imm (.seq hex₂ (.seq hex₃
        (.ifNZ_false (by rw [hf1, hue]; rfl) hex'))), ?_, ?_, ?_, ?_, ?_, ?_,
      hbuf'.trans (by rw [h₃, h₂, h₁]; simp),
      hcap'.trans (by rw [h₃, h₂, h₁]; simp)⟩
    · rw [hrow]; exact hX
    · rw [hrow]; exact fun j hj => by
        rw [hpres' _ (by omega) (by omega) (by omega)]; exact hv₃ j hj
    · rw [hrow]; exact hY
    · rw [hrow]; exact fun j hj => by
        rw [hpres' _ (by omega) (by omega) (by omega)]; exact hs₃ j hj
    · exact fun j hj => by
        rw [hpres' _ (by omega) (by omega) (by omega)]; exact hp₃ j hj
    · intro q hq
      rw [hpres' q (by omega) (by omega) (by omega), hpres₃ q (by omega)]
  · by_cases hve : V % 2 = 0
    · -- `u` odd, `v` even
      have hrow : gcdRow p U V R S = (U, V / 2, R, halfMod p S) := by
        unfold gcdRow; rw [if_neg hue, if_pos hve]
      obtain ⟨st', t', d', p', hex', hX, hY, hpres', hbuf', hcap'⟩ :=
        shrHalf_exec (C := C) (X := v) (Xsrc := v) (Y := s) (W := W + 3)
          (by omega) (by omega) (by omega) (by omega) (by omega) (Or.inl (by omega))
          hp hpR hVb (by omega) hv₃ hs₃ hp₃
      refine ⟨st', _, _, _,
        .seq .imm (.seq hex₂ (.seq hex₃
          (.ifNZ_true (by rw [hf1]; simpa using (word_ofNat_eq_zero
            (show U % 2 < 2 ^ 64 by omega)).not.mpr hue)
            (.ifNZ_false (by rw [hf2, hve]; rfl) hex')))), ?_, ?_, ?_, ?_, ?_, ?_,
        hbuf'.trans (by rw [h₃, h₂, h₁]; simp),
        hcap'.trans (by rw [h₃, h₂, h₁]; simp)⟩
      · rw [hrow]; exact fun j hj => by
          rw [hpres' _ (by omega) (by omega) (by omega)]; exact hu₃ j hj
      · rw [hrow]; exact hX
      · rw [hrow]; exact fun j hj => by
          rw [hpres' _ (by omega) (by omega) (by omega)]; exact hr₃ j hj
      · rw [hrow]; exact hY
      · exact fun j hj => by
          rw [hpres' _ (by omega) (by omega) (by omega)]; exact hp₃ j hj
      · intro q hq
        rw [hpres' q (by omega) (by omega) (by omega), hpres₃ q (by omega)]
    · -- both odd: subtract both ways, then take the smaller difference
      have hsubl₁ : SubLayout k (W + 3 + k + 4) u v (W + 3) (W + 3 + k) :=
        ⟨by omega, by omega, by omega, by omega⟩
      obtain ⟨sa, ta, da, pa, hexa, hda, hfa, hpresa, hbufa, hcapa⟩ :=
        subLimbs_exec (C := C) hsubl₁ hUb hVb hu₃ hv₃
      have hsubl₂ : SubLayout k (W + 3 + 3 * k + 8) v u (W + 3 + 2 * k + 4)
          (W + 3 + 3 * k + 4) := ⟨by omega, by omega, by omega, by omega⟩
      obtain ⟨sb, tb, db, pb, hexb, hdb, hfb, hpresb, hbufb, hcapb⟩ :=
        subLimbs_exec (C := C) hsubl₂ hVb hUb
          (fun j hj => by rw [hpresa _ (by omega)]; exact hv₃ j hj)
          (fun j hj => by rw [hpresa _ (by omega)]; exact hu₃ j hj)
      have hpresab : ∀ q, q < W + 3 → sb.regs q = st₃.regs q := by
        intro q hq; rw [hpresb q (by omega), hpresa q (by omega)]
      have hu_b : RegsEnc sb u k U := fun j hj => by
        rw [hpresab _ (by omega)]; exact hu₃ j hj
      have hv_b : RegsEnc sb v k V := fun j hj => by
        rw [hpresab _ (by omega)]; exact hv₃ j hj
      have hr_b : RegsEnc sb r k R := fun j hj => by
        rw [hpresab _ (by omega)]; exact hr₃ j hj
      have hs_b : RegsEnc sb s k S := fun j hj => by
        rw [hpresab _ (by omega)]; exact hs₃ j hj
      have hp_b : RegsEnc sb pReg k p := fun j hj => by
        rw [hpresab _ (by omega)]; exact hp₃ j hj
      have hflag : sb.regs (W + 3 + k) = BitVec.ofNat 64 (if V ≤ U then 1 else 0) := by
        rw [hpresb _ (by omega), hfa, sub_flag hUb hVb]
      by_cases hvu : V ≤ U
      · have hrow : gcdRow p U V R S
            = ((U - V) / 2, V, halfMod p (subMod p R S), S) := by
          unfold gcdRow; rw [if_neg hue, if_neg hve, if_pos hvu]
        have hD0 : RegsEnc sb (W + 3 + k + 4) k (U + 2 ^ (64 * k) - V) := fun j hj => by
          rw [hpresb _ (by omega)]; exact hda j hj
        have hD : RegsEnc sb (W + 3 + k + 4) k (U - V) :=
          hD0.congr (by rw [show U + 2 ^ (64 * k) - V = (U - V) + 2 ^ (64 * k) by omega,
            Nat.add_mod_right])
        obtain ⟨st', t', d', p', hex', hX, hY, hpres', hbuf', hcap'⟩ :=
          shrSubHalf_exec (C := C) (X := u) (Xsrc := W + 3 + k + 4) (Y := r) (Z := s)
            (W := W + 3 + 4 * k + 8) (by omega) (by omega) (by omega) (by omega)
            (by omega) (by omega) (by omega) (Or.inl (by omega)) (Or.inl (by omega))
            (Or.inl (by omega)) hp hpR (by omega) (by omega) (by omega)
            hD hr_b hs_b hp_b
        refine ⟨st', _, _, _,
          .seq .imm (.seq hex₂ (.seq hex₃
            (.ifNZ_true (by rw [hf1]; simpa using (word_ofNat_eq_zero
              (show U % 2 < 2 ^ 64 by omega)).not.mpr hue)
              (.ifNZ_true (by rw [hf2]; simpa using (word_ofNat_eq_zero
                (show V % 2 < 2 ^ 64 by omega)).not.mpr hve)
                (.seq hexa (.seq hexb (.ifNZ_true (by
                  rw [hflag, if_pos hvu]; simp) hex'))))))), ?_, ?_, ?_, ?_, ?_, ?_,
          hbuf'.trans (hbufb.trans (hbufa.trans (by rw [h₃, h₂, h₁]; simp))),
          hcap'.trans (hcapb.trans (hcapa.trans (by rw [h₃, h₂, h₁]; simp)))⟩
        · rw [hrow]; exact hX
        · rw [hrow]; exact fun j hj => by
            rw [hpres' _ (by omega) (by omega) (by omega)]; exact hv_b j hj
        · rw [hrow]; exact hY
        · rw [hrow]; exact fun j hj => by
            rw [hpres' _ (by omega) (by omega) (by omega)]; exact hs_b j hj
        · exact fun j hj => by
            rw [hpres' _ (by omega) (by omega) (by omega)]; exact hp_b j hj
        · intro q hq
          rw [hpres' q (by omega) (by omega) (by omega), hpresab q (by omega),
            hpres₃ q (by omega)]
      · have hrow : gcdRow p U V R S
            = (U, (V - U) / 2, R, halfMod p (subMod p S R)) := by
          unfold gcdRow; rw [if_neg hue, if_neg hve, if_neg hvu]
        have hD : RegsEnc sb (W + 3 + 3 * k + 8) k (V - U) :=
          hdb.congr (by rw [show V + 2 ^ (64 * k) - U = (V - U) + 2 ^ (64 * k) by omega,
            Nat.add_mod_right])
        obtain ⟨st', t', d', p', hex', hX, hY, hpres', hbuf', hcap'⟩ :=
          shrSubHalf_exec (C := C) (X := v) (Xsrc := W + 3 + 3 * k + 8) (Y := s)
            (Z := r) (W := W + 3 + 4 * k + 8) (by omega) (by omega) (by omega)
            (by omega) (by omega) (by omega) (by omega) (Or.inl (by omega))
            (Or.inl (by omega)) (Or.inr (by omega)) hp hpR (by omega) (by omega)
            (by omega) hD hs_b hr_b hp_b
        refine ⟨st', _, _, _,
          .seq .imm (.seq hex₂ (.seq hex₃
            (.ifNZ_true (by rw [hf1]; simpa using (word_ofNat_eq_zero
              (show U % 2 < 2 ^ 64 by omega)).not.mpr hue)
              (.ifNZ_true (by rw [hf2]; simpa using (word_ofNat_eq_zero
                (show V % 2 < 2 ^ 64 by omega)).not.mpr hve)
                (.seq hexa (.seq hexb (.ifNZ_false (by
                  rw [hflag, if_neg hvu]; rfl) hex'))))))), ?_, ?_, ?_, ?_, ?_, ?_,
          hbuf'.trans (hbufb.trans (hbufa.trans (by rw [h₃, h₂, h₁]; simp))),
          hcap'.trans (hcapb.trans (hcapa.trans (by rw [h₃, h₂, h₁]; simp)))⟩
        · rw [hrow]; exact fun j hj => by
            rw [hpres' _ (by omega) (by omega) (by omega)]; exact hu_b j hj
        · rw [hrow]; exact hX
        · rw [hrow]; exact fun j hj => by
            rw [hpres' _ (by omega) (by omega) (by omega)]; exact hr_b j hj
        · rw [hrow]; exact hY
        · exact fun j hj => by
            rw [hpres' _ (by omega) (by omega) (by omega)]; exact hp_b j hj
        · intro q hq
          rw [hpres' q (by omega) (by omega) (by omega), hpresab q (by omega),
            hpres₃ q (by omega)]

/-! ## The time bound

The measure is the counter, so `whileNZ_measure` needs three facts and no arithmetic:
the guard is `skip`, a nonzero counter means an iteration remains, and the body leaves
the counter strictly smaller — by one when it does a row, and to zero when `u` has
reached zero and the loop is done. -/

/-- Sequencing at zero memory, the shape every block here has. -/
theorem seq0 {P R Q : State 64 → Prop} {c₁ c₂ : Stmt 64} {T₁ T₂ : ℕ}
    (h₁ : Triple C P c₁ R T₁ 0 0) (h₂ : Triple C R c₂ Q T₂ 0 0) :
    Triple C P (c₁ ;; c₂) Q (T₁ + T₂) 0 0 :=
  (h₁.seq h₂).weaken (le_refl _) (by simp) (by simp)

/-- Subtracting one from a nonzero word takes one off its value. -/
theorem toNat_sub_one {x : Word 64} (h : x ≠ 0) :
    (x - (1 : Word 64)).toNat = x.toNat - 1 := by
  have h1 : x.toNat ≠ 0 := fun hh => h (BitVec.eq_of_toNat_eq (by simp [hh]))
  have h2 : x.toNat < 2 ^ 64 := x.isLt
  have h3 : (1 : Word 64).toNat = 1 := rfl
  simp only [BitVec.toNat_sub, h3]
  omega

/-- One pass either spends an iteration on a row or, `u` having reached zero, empties
the counter. Either way the counter ends strictly smaller, and no data hypothesis
appears: the body is register-only, so it always runs. -/
theorem invBody_triple {k u v r s pReg cnt W : ℕ} (hW : cnt < W)
    (hu : cnt < u) (hv : cnt < v) (hr : cnt < r) (hs : cnt < s) (n : ℕ) :
    Triple CostModel.unit
      (fun st => (st.regs cnt).toNat ≤ n + 1 ∧ st.regs cnt ≠ 0)
      (invBody k u v r s pReg cnt W)
      (fun st => (st.regs cnt).toNat ≤ n)
      (46 * k + 24) 0 0 := by
  have hnz : Triple CostModel.unit
      (fun st => (st.regs cnt).toNat ≤ n + 1 ∧ st.regs cnt ≠ 0)
      (nzLimbs k u W)
      (fun st => (st.regs cnt).toNat ≤ n + 1 ∧ st.regs cnt ≠ 0)
      (k + 2) 0 0 := by
    have h := (nzLimbs_regOnly k u W).triple_frame (C := CostModel.unit)
      (P := fun st => (st.regs cnt).toNat ≤ n + 1 ∧ st.regs cnt ≠ 0)
      (R := fun q => q = cnt)
      (fun q hq => hq ▸ nzLimbs_writesAbove (lo := cnt + 1) hW cnt
        (Nat.lt_succ_self cnt))
      (fun st st' hpres hst => by rw [hpres cnt rfl]; exact hst)
    rw [nzLimbs_staticTime_unit] at h
    exact h
  have hstep : Triple CostModel.unit
      (fun st => (st.regs cnt).toNat ≤ n) (invStep k u v r s pReg (W + 3))
      (fun st => (st.regs cnt).toNat ≤ n) (45 * k + 19) 0 0 := by
    have h := (invStep_regOnly k u v r s pReg (W + 3)).triple_frame
      (C := CostModel.unit) (P := fun st => (st.regs cnt).toNat ≤ n)
      (R := fun q => q = cnt)
      (fun q hq => hq ▸ invStep_writesAbove (lo := cnt + 1)
        (show cnt + 1 ≤ W + 3 by omega) hu hv hr hs cnt (Nat.lt_succ_self cnt))
      (fun st st' hpres hst => by rw [hpres cnt rfl]; exact hst)
    rw [invStep_staticTime_unit] at h
    exact h
  have hthen : Triple CostModel.unit
      (fun st => ((st.regs cnt).toNat ≤ n + 1 ∧ st.regs cnt ≠ 0) ∧
        st.regs (W + 1) ≠ 0)
      (.imm (W + 2) 1 ;; .bin .sub cnt cnt (W + 2) ;;
        invStep k u v r s pReg (W + 3))
      (fun st => (st.regs cnt).toNat ≤ n) (45 * k + 21) 0 0 := by
    have himm : Triple CostModel.unit
        (fun st => ((st.regs cnt).toNat ≤ n + 1 ∧ st.regs cnt ≠ 0) ∧
          st.regs (W + 1) ≠ 0)
        (Stmt.imm (W + 2) (1 : Word 64))
        (fun st => (st.regs cnt).toNat ≤ n + 1 ∧ st.regs cnt ≠ 0 ∧
          st.regs (W + 2) = (1 : Word 64)) 1 0 0 := by
      refine (Triple.imm ?_).weaken ?_ (le_refl _) (le_refl _)
      · rintro st ⟨⟨h1, h2⟩, -⟩
        refine ⟨?_, ?_, by simp⟩
        · rw [regs_setReg_ne _ _ (show cnt ≠ W + 2 by omega)]; exact h1
        · rw [regs_setReg_ne _ _ (show cnt ≠ W + 2 by omega)]; exact h2
      · simp [CostModel.unit]
    have hsub : Triple CostModel.unit
        (fun st => (st.regs cnt).toNat ≤ n + 1 ∧ st.regs cnt ≠ 0 ∧
          st.regs (W + 2) = (1 : Word 64))
        (Stmt.bin (w := 64) .sub cnt cnt (W + 2))
        (fun st => (st.regs cnt).toNat ≤ n) 1 0 0 := by
      refine (Triple.bin ?_).weaken ?_ (le_refl _) (le_refl _)
      · rintro st ⟨h1, h2, h3⟩
        rw [regs_setReg_self]
        show ((st.regs cnt - st.regs (W + 2) : Word 64)).toNat ≤ n
        rw [h3, toNat_sub_one h2]
        omega
      · simp [CostModel.unit]
    refine (seq0 himm (seq0 hsub hstep)).weaken ?_ (le_refl _) (le_refl _)
    omega
  have helse : Triple CostModel.unit
      (fun st => ((st.regs cnt).toNat ≤ n + 1 ∧ st.regs cnt ≠ 0) ∧
        st.regs (W + 1) = 0)
      (Stmt.imm cnt (0 : Word 64)) (fun st => (st.regs cnt).toNat ≤ n)
      (45 * k + 21) 0 0 := by
    refine (Triple.imm (fun st _ => ?_)).weaken ?_ (le_refl _) (le_refl _)
    · rw [regs_setReg_self]; simp
    · simp [CostModel.unit]
  have hif := Triple.ifNZ hthen helse
  refine (seq0 hnz hif).weaken ?_ (le_refl _) (le_refl _)
  simp [CostModel.unit]
  omega

/-- **The inversion's running time is bounded**, at every field: `5888k² + O(k)` unit
steps, 107 026 at BN254's `k = 4`. -/
theorem invLimbs_triple {k a pReg w : ℕ} (hk : 128 * k < 2 ^ 64) :
    Triple CostModel.unit (fun _ => True) (invLimbs k a pReg w) (fun _ => True)
      (5888 * k ^ 2 + 3204 * k + 2) 0 0 := by
  have hloop := Triple.whileNZ_measure (C := CostModel.unit)
    (I := fun n st => (st.regs w).toNat ≤ n) (J := fun n st => (st.regs w).toNat ≤ n)
    (g := .skip) (r := w)
    (body := invBody k (w + 1) (w + 1 + k) (w + 1 + 2 * k) (w + 1 + 3 * k) pReg w
      (w + 1 + 4 * k))
    (Tg := 0) (Dg := 0) (Mg := 0) (Tb := 46 * k + 24) (Db := 0) (Mb := 0)
    (fun _ => Triple.skip fun _ h => h)
    (fun n st hst hne => by
      rcases n with _ | n'
      · refine absurd (BitVec.eq_of_toNat_eq ?_) hne
        have hz : (0 : Word 64).toNat = 0 := rfl
        omega
      · exact ⟨n', rfl⟩)
    (fun n => invBody_triple (by omega) (by omega) (by omega) (by omega) (by omega) n)
    (128 * k)
  have hloop' : Triple CostModel.unit (fun st => (st.regs w).toNat ≤ 128 * k)
      (invLoop k (w + 1) (w + 1 + k) (w + 1 + 2 * k) (w + 1 + 3 * k) pReg w
        (w + 1 + 4 * k))
      (fun _ => True)
      ((128 * k + 1) * (0 + CostModel.unit.branch) + 128 * k * (46 * k + 24)) 0 0 :=
    hloop.conseq (fun _ h => h) (fun _ _ => trivial) (le_refl _) (by simp) (by simp)
  have t₁ := (movLimbs_regOnly k (w + 1) a).triple (C := CostModel.unit)
    (P := fun _ => True) (Q := fun _ => True) (fun _ _ _ _ _ => trivial)
  have t₂ := (movLimbs_regOnly k (w + 1 + k) pReg).triple (C := CostModel.unit)
    (P := fun _ => True) (Q := fun _ => True) (fun _ _ _ _ _ => trivial)
  have t₃ := (immLimbs_regOnly (w + 1 + 2 * k) 1 k).triple (C := CostModel.unit)
    (P := fun _ => True) (Q := fun _ => True) (fun _ _ _ _ _ => trivial)
  have t₄ := (immLimbs_regOnly (w + 1 + 3 * k) 0 k).triple (C := CostModel.unit)
    (P := fun _ => True) (Q := fun _ => True) (fun _ _ _ _ _ => trivial)
  rw [movLimbs_staticTime_unit] at t₁ t₂
  rw [immLimbs_staticTime] at t₃ t₄
  have t₅ : Triple CostModel.unit (fun _ => True)
      (Stmt.imm w (BitVec.ofNat 64 (invBudget k)))
      (fun st => (st.regs w).toNat ≤ 128 * k) 1 0 0 := by
    refine (Triple.imm (fun st _ => ?_)).weaken ?_ (le_refl _) (le_refl _)
    · rw [regs_setReg_self]
      show (BitVec.ofNat 64 (invBudget k)).toNat ≤ 128 * k
      simp only [BitVec.toNat_ofNat, invBudget]
      omega
    · simp [CostModel.unit]
  refine (seq0 t₁ (seq0 t₂ (seq0 t₃ (seq0 t₄ (seq0 t₅ hloop'))))).weaken ?_
    (le_refl _) (le_refl _)
  simp only [CostModel.unit]
  ring_nf
  omega

/-- Every execution of an inversion is within the bound. -/
theorem invLimbs_time {k a pReg w : ℕ} (hk : 128 * k < 2 ^ 64) (s : State 64) :
    ∃ s' t dd pp, Exec CostModel.unit (invLimbs k a pReg w) s s' t dd pp ∧
      t ≤ 5888 * k ^ 2 + 3204 * k + 2 := by
  obtain ⟨s', t, dd, pp, hex, -, ht, -, -⟩ := invLimbs_triple (a := a) (pReg := pReg) hk s trivial
  exact ⟨s', t, dd, pp, hex, ht⟩

end Caliper.MultiLimb
