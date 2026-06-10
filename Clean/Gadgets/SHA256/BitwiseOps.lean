import Clean.Circuit
import Clean.Gadgets.Boolean
import Clean.Utils.Primes
import Clean.Utils.Bits

section
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2)]

namespace Gadgets.SHA256

/-!
# 32-bit Bitwise Operations for SHA-256

All operations work on `fields 32`, where each field element represents one bit (boolean).
Bit 0 is the least-significant bit (LSB-first convention).

No lookup tables are used; all operations are expressed as R1CS constraints.
-/

/-- State: 8 boolean 32-bit words. -/
abbrev SHA256State := ProvableVector (fields 32) 8

/-- Block: 16 boolean 32-bit words. -/
abbrev SHA256Block := ProvableVector (fields 32) 16

/-- Message schedule: 64 boolean 32-bit words. -/
abbrev SHA256Schedule := ProvableVector (fields 32) 64

/-- Interpret a bit vector as a natural number (LSB at index 0). -/
def valueBits (bits : Vector (F p) 32) : ℕ :=
  Finset.univ.sum fun (i : Fin 32) => bits[i].val * 2^i.val

/-- All bits are boolean (0 or 1). -/
def Normalized (w : Vector (F p) 32) : Prop :=
  ∀ i : Fin 32, w[i] = 0 ∨ w[i] = 1

/-- The linear combination of bits as an expression: Σ bits[i] · 2^i (LSB first) -/
abbrev fromBitsExpr (bits : Var (fields 32) (F p)) : Expression (F p) :=
  Utils.Bits.fieldFromBitsExpr bits

/-- A constant 32-bit word from a natural number (LSB-first bit decomposition). -/
def constWord32 (n : ℕ) : Var (fields 32) (F p) :=
  Vector.ofFn fun (i : Fin 32) => ((n / 2^i.val % 2 : ℕ) : F p)

/-!
## Pure combinators (no witnesses, no constraints)
-/

/-- Bitwise NOT: maps each bit a[i] ↦ 1 − a[i]. -/
def not32 (a : Var (fields 32) (F p)) : Var (fields 32) (F p) :=
  a.map fun ai => (1 : Expression (F p)) - ai

/-!
## Value lemmas for normalized words
-/

/-- Geometric sum of bit weights: `Σ_{i < m} 2^i = 2^m − 1`. -/
lemma sum_two_pow (m : ℕ) : ∑ i : Fin m, 2^(i : ℕ) = 2^m - 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    have h2 : (2:ℕ)^(m+1) = 2 * 2^m := by rw [pow_succ]; ring
    have h3 : (0:ℕ) < 2^m := Nat.two_pow_pos m
    omega

omit [Fact (p > 2)] in
/-- Each bit of a normalized word has value at most 1. -/
lemma val_le_one_of_normalized {w : Vector (F p) 32} (h : Normalized w) (i : Fin 32) :
    w[i].val ≤ 1 := by
  rcases h i with h0 | h1
  · rw [h0]; simp
  · rw [h1, ZMod.val_one]

omit [Fact (p > 2)] in
/-- The value of a normalized 32-bit word is below `2^32`. -/
lemma valueBits_lt_of_normalized {w : Vector (F p) 32} (h : Normalized w) :
    valueBits w < 2^32 := by
  have hle : valueBits w ≤ ∑ i : Fin 32, 2^(i : ℕ) := by
    unfold valueBits
    apply Finset.sum_le_sum
    intro i _
    calc w[i].val * 2^(i : ℕ) ≤ 1 * 2^(i : ℕ) :=
          Nat.mul_le_mul_right _ (val_le_one_of_normalized h i)
      _ = 2^(i : ℕ) := one_mul _
  have hsum := sum_two_pow 32
  omega

omit [Fact (p > 2)] in
/-- The bitwise complement of a normalized word is normalized. -/
lemma normalized_not {w : Vector (F p) 32} (h : Normalized w) :
    Normalized (w.map fun x => 1 - x) := by
  intro i
  have hi : (w.map fun x => 1 - x)[i] = 1 - w[i] := by
    simp [Vector.getElem_map]
  rcases h i with h0 | h1
  · right; rw [hi, h0, sub_zero]
  · left; rw [hi, h1, sub_self]

omit [Fact (p > 2)] in
/-- The value of the bitwise complement of a normalized word: `¬w = 2^32 − 1 − w`. -/
lemma valueBits_not {w : Vector (F p) 32} (h : Normalized w) :
    valueBits (w.map fun x => 1 - x) = 2^32 - 1 - valueBits w := by
  have hsum : valueBits (w.map fun x => 1 - x) + valueBits w = ∑ i : Fin 32, 2^(i : ℕ) := by
    unfold valueBits
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have hi : (w.map fun x => 1 - x)[i] = 1 - w[i] := by
      simp [Vector.getElem_map]
    rw [hi]
    rcases h i with h0 | h1
    · rw [h0, sub_zero, ZMod.val_one, ZMod.val_zero]
      ring
    · rw [h1, sub_self, ZMod.val_zero, ZMod.val_one]
      ring
  have h32 := sum_two_pow 32
  have hlt := valueBits_lt_of_normalized h
  omega

/-- Rotate right by `k` bits (mod 32): z[i] = a[(i + k) mod 32]. -/
def rotr32 (k : Fin 32) (a : Var (fields 32) (F p)) : Var (fields 32) (F p) :=
  a.rotate k

/-- Shift right by `k` bits: z[i] = a[i + k] if i + k < 32, else 0. -/
def shr32 (k : Fin 32) (a : Var (fields 32) (F p)) : Var (fields 32) (F p) :=
  Vector.ofFn fun (i : Fin 32) =>
    if h : i.val + k.val < 32
    then a[i.val + k.val]'h
    else (0 : Expression (F p))

end Gadgets.SHA256
end
