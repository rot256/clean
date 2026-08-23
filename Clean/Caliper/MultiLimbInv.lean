import Clean.Caliper.RegOnly
import Clean.Caliper.MultiLimbOps

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

open Caliper

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
    + ((Stmt.imm (w + k + 1) 1).staticTime CostModel.unit
      + ((Stmt.bin .and (w + k) a (w + k + 1)).staticTime CostModel.unit
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
