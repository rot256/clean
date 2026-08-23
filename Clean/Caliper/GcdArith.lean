import Mathlib.Tactic
import Mathlib.Data.Nat.Size

/-!
# The binary extended gcd, arithmetically

The pure function the inversion gadget computes, and why it computes the inverse. No
machine state appears here: `gcdRow` is one row of the loop as a map on four naturals,
`GcdInv` is what every row preserves, and `gcdRow_size` is why the loop finishes.

The row is the standard binary extended Euclid with modular halving:

    u = a; v = p; r = 1; s = 0            -- u ≡ r·a, v ≡ s·a  (mod p)
    if u even:      u /= 2;  r = r/2 mod p
    elif v even:    v /= 2;  s = s/2 mod p
    elif v ≤ u:     u = (u-v)/2;  r = (r-s)/2 mod p
    else:           v = (v-u)/2;  s = (s-r)/2 mod p

Halving `r` modulo `p` is exact when `r` is even and `(r + p) / 2` otherwise — the
same residue, since `p` is odd. Everything below is stated with additions rather than
`ℕ` subtractions wherever a residue is involved, which is what keeps `omega` and
`Nat.ModEq` usable.

On exit `u = 0`, so `v = gcd(u, v) = gcd(a, p)`, and `v ≡ s·a` gives `s·a ≡ gcd(a,p)`.
At a prime `p` with `a < p` that gcd is `1` unless `a = 0`, and `a = 0` exits before
the first row with `s = 0` — which is the field's own convention for `0⁻¹`.
-/

namespace Caliper.MultiLimb

/-! ## Halving and subtracting, modulo `p` -/

/-- `x / 2 mod p` for odd `p`: exact when `x` is even, `(x + p) / 2` otherwise. -/
def halfMod (p x : ℕ) : ℕ := if x % 2 = 0 then x / 2 else (x + p) / 2

/-- `(x - y) mod p`, written without a truncating subtraction. -/
def subMod (p x y : ℕ) : ℕ := (x + p - y) % p

theorem halfMod_lt {p x : ℕ} (hx : x < p) : halfMod p x < p := by
  unfold halfMod; split <;> omega

/-- Halving is the inverse of doubling, modulo an odd `p`. -/
theorem halfMod_two_mul {p x : ℕ} (hp : p % 2 = 1) :
    2 * halfMod p x ≡ x [MOD p] := by
  unfold halfMod
  split
  · rename_i h; rw [show 2 * (x / 2) = x by omega]
  · rename_i h
    rw [show 2 * ((x + p) / 2) = x + p by omega]
    exact (Nat.add_modEq_right).trans (Nat.ModEq.refl x)

theorem subMod_lt {p x y : ℕ} (hp : 0 < p) : subMod p x y < p := Nat.mod_lt _ hp

/-- What `subMod` is for: adding `y` back recovers `x`, modulo `p`. -/
theorem subMod_add {p x y : ℕ} (hy : y ≤ p) : subMod p x y + y ≡ x [MOD p] := by
  have h : (x + p - y) % p + y ≡ (x + p - y) + y [MOD p] :=
    Nat.ModEq.add_right _ (Nat.mod_modEq _ _)
  refine h.trans ?_
  rw [show x + p - y + y = x + p by omega]
  exact Nat.add_modEq_right

/-- Two is invertible modulo an odd `p`, so it cancels. -/
theorem two_cancel {p x y : ℕ} (hp : p % 2 = 1) (h : 2 * x ≡ 2 * y [MOD p]) :
    x ≡ y [MOD p] := by
  refine Nat.ModEq.cancel_left_of_coprime ?_ h
  rw [Nat.gcd_comm, Nat.gcd_rec, hp]
  simp

/-! ## One row -/

/-- One row of the loop, as a map on `(u, v, r, s)`. -/
def gcdRow (p u v r s : ℕ) : ℕ × ℕ × ℕ × ℕ :=
  if u % 2 = 0 then (u / 2, v, halfMod p r, s)
  else if v % 2 = 0 then (u, v / 2, r, halfMod p s)
  else if v ≤ u then ((u - v) / 2, v, halfMod p (subMod p r s), s)
  else (u, (v - u) / 2, r, halfMod p (subMod p s r))

/-- What a row preserves. `u ≡ r·a` and `v ≡ s·a` are the extended part; the gcd and
the parity clause are what make the halvings sound; `0 < v` is what makes the measure
argument work. -/
structure GcdInv (p a u v r s : ℕ) : Prop where
  vpos : 0 < v
  ult : u < p
  vle : v ≤ p
  rlt : r < p
  slt : s < p
  parity : u % 2 = 1 ∨ v % 2 = 1
  gcd : Nat.gcd u v = Nat.gcd a p
  ru : u ≡ r * a [MOD p]
  sv : v ≡ s * a [MOD p]

/-! ## The congruences a row preserves -/

/-- Halving a value and its coefficient together. -/
theorem half_congr {p a u r : ℕ} (hp : p % 2 = 1) (hu : u % 2 = 0)
    (h : u ≡ r * a [MOD p]) : u / 2 ≡ halfMod p r * a [MOD p] := by
  refine two_cancel hp ?_
  calc 2 * (u / 2) = u := by omega
    _ ≡ r * a [MOD p] := h
    _ ≡ 2 * halfMod p r * a [MOD p] :=
        (Nat.ModEq.mul_right a (halfMod_two_mul hp)).symm
    _ = 2 * (halfMod p r * a) := by ring

/-- Subtracting one pair from another and halving. Stated with `+ v` on the left
rather than a truncating subtraction on the right, which is what makes it a chain of
`Nat.ModEq` steps. -/
theorem subHalf_congr {p a u v r s : ℕ} (hp : p % 2 = 1) (hs : s ≤ p)
    (hvu : v ≤ u) (heven : (u - v) % 2 = 0)
    (hru : u ≡ r * a [MOD p]) (hsv : v ≡ s * a [MOD p]) :
    (u - v) / 2 ≡ halfMod p (subMod p r s) * a [MOD p] := by
  refine two_cancel hp ?_
  have key : 2 * (halfMod p (subMod p r s) * a) + v ≡ u [MOD p] := by
    calc 2 * (halfMod p (subMod p r s) * a) + v
        = 2 * halfMod p (subMod p r s) * a + v := by ring
      _ ≡ subMod p r s * a + v [MOD p] :=
          Nat.ModEq.add_right v (Nat.ModEq.mul_right a (halfMod_two_mul hp))
      _ ≡ subMod p r s * a + s * a [MOD p] := Nat.ModEq.add_left _ hsv
      _ = (subMod p r s + s) * a := by ring
      _ ≡ r * a [MOD p] := Nat.ModEq.mul_right a (subMod_add hs)
      _ ≡ u [MOD p] := hru.symm
  have hexact : 2 * ((u - v) / 2) + v = u := by omega
  refine Nat.ModEq.add_right_cancel' v ?_
  rw [hexact]
  exact key.symm

/-! ## The gcd a row preserves

Every halving is by a factor coprime to the other operand, which is what the parity
clause of the invariant is for. -/

theorem coprime_two {v : ℕ} (hv : v % 2 = 1) : Nat.Coprime 2 v := by
  have h : Nat.gcd 2 v = 1 := by rw [Nat.gcd_rec, hv]; simp
  exact h

theorem gcd_half_left {u v : ℕ} (hu : u % 2 = 0) (hv : v % 2 = 1) :
    Nat.gcd (u / 2) v = Nat.gcd u v := by
  conv_rhs => rw [show u = 2 * (u / 2) by omega]
  exact (Nat.Coprime.gcd_mul_left_cancel _ (coprime_two hv)).symm

theorem gcd_half_right {u v : ℕ} (hu : u % 2 = 1) (hv : v % 2 = 0) :
    Nat.gcd u (v / 2) = Nat.gcd u v := by
  conv_rhs => rw [show v = 2 * (v / 2) by omega]
  exact (Nat.Coprime.gcd_mul_left_cancel_right _ (coprime_two hu)).symm

theorem gcd_subHalf_left {u v : ℕ} (hv : v % 2 = 1) (hvu : v ≤ u)
    (he : (u - v) % 2 = 0) : Nat.gcd ((u - v) / 2) v = Nat.gcd u v := by
  rw [gcd_half_left he hv]
  exact Nat.gcd_sub_self_left hvu

theorem gcd_subHalf_right {u v : ℕ} (hu : u % 2 = 1) (huv : u ≤ v)
    (he : (v - u) % 2 = 0) : Nat.gcd u ((v - u) / 2) = Nat.gcd u v := by
  rw [gcd_half_right hu he]
  exact Nat.gcd_sub_self_right huv

/-! ## A row preserves the invariant -/

theorem gcdRow_inv {p a u v r s : ℕ} (hp : p % 2 = 1) (h1 : 1 < p)
    (hinv : GcdInv p a u v r s) :
    GcdInv p a (gcdRow p u v r s).1 (gcdRow p u v r s).2.1
      (gcdRow p u v r s).2.2.1 (gcdRow p u v r s).2.2.2 := by
  obtain ⟨hv0, hul, hvl, hrl, hsl, hpar, hg, hru, hsv⟩ := hinv
  unfold gcdRow
  split_ifs with hue hve hvu <;> dsimp only
  · -- `u` even, so `v` is odd
    have hvo : v % 2 = 1 := hpar.resolve_left (by omega)
    exact ⟨hv0, by omega, hvl, halfMod_lt hrl, hsl, Or.inr hvo,
      by rw [gcd_half_left hue hvo]; exact hg, half_congr hp hue hru, hsv⟩
  · -- `u` odd, `v` even
    have huo : u % 2 = 1 := by omega
    exact ⟨by omega, hul, by omega, hrl, halfMod_lt hsl, Or.inl huo,
      by rw [gcd_half_right huo hve]; exact hg, hru, half_congr hp hve hsv⟩
  · -- both odd, `v ≤ u`
    have huo : u % 2 = 1 := by omega
    have hvo : v % 2 = 1 := by omega
    have hev : (u - v) % 2 = 0 := by omega
    exact ⟨hv0, by omega, hvl, halfMod_lt (subMod_lt (by omega)), hsl, Or.inr hvo,
      by rw [gcd_subHalf_left hvo hvu hev]; exact hg,
      subHalf_congr hp hsl.le hvu hev hru hsv, hsv⟩
  · -- both odd, `u < v`
    have huo : u % 2 = 1 := by omega
    have hvo : v % 2 = 1 := by omega
    have hev : (v - u) % 2 = 0 := by omega
    exact ⟨by omega, hul, by omega, hrl, halfMod_lt (subMod_lt (by omega)),
      Or.inl huo, by rw [gcd_subHalf_right huo (by omega) hev]; exact hg, hru,
      subHalf_congr hp hrl.le (by omega) hev hsv hru⟩

/-! ## A row makes progress

`Nat.size u + Nat.size v` falls by at least one, so `2 * 64k` rows always reach
`u = 0`. -/

theorem size_div_two_lt {n : ℕ} (h : n ≠ 0) : Nat.size (n / 2) < Nat.size n := by
  have hpos : 0 < Nat.size n := Nat.size_pos.mpr (by omega)
  have hlt : n < 2 ^ Nat.size n := Nat.lt_size_self n
  have hsplit : (2:ℕ) ^ Nat.size n = 2 * 2 ^ (Nat.size n - 1) := by
    rw [← pow_succ']; congr 1; omega
  have : Nat.size (n / 2) ≤ Nat.size n - 1 := Nat.size_le.mpr (by omega)
  omega

theorem gcdRow_size {p a u v r s : ℕ} (hinv : GcdInv p a u v r s) (hu : u ≠ 0) :
    Nat.size (gcdRow p u v r s).1 + Nat.size (gcdRow p u v r s).2.1
      < Nat.size u + Nat.size v := by
  obtain ⟨hv0, -, -, -, -, -, -, -, -⟩ := hinv
  unfold gcdRow
  split_ifs with hue hve hvu <;> dsimp only
  · exact Nat.add_lt_add_right (size_div_two_lt hu) _
  · exact Nat.add_lt_add_left (size_div_two_lt (by omega)) _
  · exact Nat.add_lt_add_right
      (Nat.lt_of_le_of_lt (Nat.size_le_size (by omega)) (size_div_two_lt hu)) _
  · exact Nat.add_lt_add_left
      (Nat.lt_of_le_of_lt (Nat.size_le_size (by omega)) (size_div_two_lt (by omega))) _

/-! ## Entry and exit -/

theorem gcdInv_init {p a : ℕ} (hp : p % 2 = 1) (h1 : 1 < p) (ha : a < p) :
    GcdInv p a a p 1 0 :=
  ⟨by omega, ha, le_refl _, h1, by omega, Or.inr hp, rfl, by rw [one_mul],
    by simp [Nat.ModEq]⟩

/-- **On exit the coefficient is the inverse.** `u = 0` makes the running gcd equal to
`v`, and the invariant says `v ≡ s·a`; at a `p` coprime to `a` that gcd is `1`. -/
theorem gcdInv_result {p a v r s : ℕ} (hinv : GcdInv p a 0 v r s)
    (hcop : Nat.gcd a p = 1) : s * a ≡ 1 [MOD p] := by
  obtain ⟨-, -, -, -, -, -, hg, -, hsv⟩ := hinv
  rw [Nat.gcd_zero_left, hcop] at hg
  rw [hg] at hsv
  exact hsv.symm

end Caliper.MultiLimb
