import Caliper.Core
import Mathlib.Tactic

/-!
# Base-`2 ^ w` limb representation

The arithmetic layer under multi-limb field elements: a natural number is carried in
`k` machine words, little-endian, and this file relates the two.

`limb w v i` is the `i`-th limb of `v` and `ofLimbs w f k` reads `k` limbs back into
a number. The pair round-trips modulo `2 ^ (w * k)` (`ofLimbs_limb`), which is the
only fact the machine-level gadgets need: a value known to be `< 2 ^ (w * k)` is
determined by its limbs, so limb-wise operations that agree with the arithmetic one
compute it.

Everything here is pure `ℕ` arithmetic. The `Stmt`-level gadgets and their `Exec`
specs are in `MultiLimb.lean`.
-/

namespace Caliper.Limbs

/-- The `i`-th base-`2 ^ w` limb of `v`. -/
def limb (w v i : ℕ) : ℕ := v / 2 ^ (w * i) % 2 ^ w

/-- Little-endian value of the first `k` limbs supplied by `f`. -/
def ofLimbs (w : ℕ) (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => ofLimbs w f k + f k * 2 ^ (w * k)

@[simp] theorem ofLimbs_zero (w : ℕ) (f : ℕ → ℕ) : ofLimbs w f 0 = 0 := rfl

theorem ofLimbs_succ (w : ℕ) (f : ℕ → ℕ) (k : ℕ) :
    ofLimbs w f (k + 1) = ofLimbs w f k + f k * 2 ^ (w * k) := rfl

/-- `ofLimbs` depends only on the limbs it reads. -/
theorem ofLimbs_congr {w : ℕ} {f g : ℕ → ℕ} {k : ℕ} (h : ∀ i < k, f i = g i) :
    ofLimbs w f k = ofLimbs w g k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [ofLimbs_succ, ofLimbs_succ, ih fun i hi => h i (by omega), h k (by omega)]

theorem limb_lt (w v i : ℕ) : limb w v i < 2 ^ w := Nat.mod_lt _ (Nat.two_pow_pos w)

/-- Splitting a modulus into a low part and a digit: `v % (A * B) = v % A + A * (v / A % B)`.
The recursion step of `ofLimbs_limb`. -/
theorem mod_mul_split (v A B : ℕ) : v % (A * B) = v % A + A * (v / A % B) := by
  simp [Nat.mod_mul]

/-- Reading `k` limbs back gives the value modulo `2 ^ (w * k)`. -/
theorem ofLimbs_limb (w v : ℕ) : ∀ k, ofLimbs w (limb w v) k = v % 2 ^ (w * k)
  | 0 => by simp [ofLimbs, Nat.mod_one]
  | k + 1 => by
    have hpow : (2:ℕ) ^ (w * (k + 1)) = 2 ^ (w * k) * 2 ^ w := by
      rw [← pow_add]; ring_nf
    rw [ofLimbs_succ, ofLimbs_limb w v k, limb, hpow,
      mod_mul_split v (2 ^ (w * k)) (2 ^ w)]
    ring

/-- A value below `2 ^ (w * k)` is exactly its `k` limbs. -/
theorem ofLimbs_limb_of_lt {w v k : ℕ} (h : v < 2 ^ (w * k)) :
    ofLimbs w (limb w v) k = v := by
  rw [ofLimbs_limb, Nat.mod_eq_of_lt h]

/-- `ofLimbs` of limbs each `< 2 ^ w` stays below `2 ^ (w * k)`. -/
theorem ofLimbs_lt {w : ℕ} {f : ℕ → ℕ} (hf : ∀ i, f i < 2 ^ w) :
    ∀ k, ofLimbs w f k < 2 ^ (w * k)
  | 0 => by simp
  | k + 1 => by
    have ih := ofLimbs_lt hf k
    have hk := hf k
    have : (2:ℕ) ^ (w * (k + 1)) = 2 ^ (w * k) * 2 ^ w := by
      rw [← pow_add]; ring_nf
    rw [ofLimbs_succ, this]
    calc ofLimbs w f k + f k * 2 ^ (w * k)
        < 2 ^ (w * k) + f k * 2 ^ (w * k) := by omega
      _ = (f k + 1) * 2 ^ (w * k) := by ring
      _ ≤ 2 ^ w * 2 ^ (w * k) := Nat.mul_le_mul_right _ (by omega)
      _ = 2 ^ (w * k) * 2 ^ w := by ring

/-- Limbs determine a value below `2 ^ (w * k)`. -/
theorem eq_of_limbs {w k a b : ℕ} (ha : a < 2 ^ (w * k)) (hb : b < 2 ^ (w * k))
    (h : ∀ i < k, limb w a i = limb w b i) : a = b := by
  rw [← ofLimbs_limb_of_lt ha, ← ofLimbs_limb_of_lt hb, ofLimbs_congr h]

end Caliper.Limbs
