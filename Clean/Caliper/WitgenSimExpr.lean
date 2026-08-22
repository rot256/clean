import Clean.Caliper.WitgenSim

/-!
# Scalar-expression simulation for the witgen compiler

Phase 3b: the scalar compiler induction. For every compilable, environment-bounded
scalar expression of the witness IR (`Expression`, `FExpr`, `U64Expr`, `BExpr`), the
emitted code executes from any state satisfying the state-encoding invariant
`StateEnc`, terminates, leaves the encoded value of the reference evaluation in the
result register, and preserves all registers below the free-register counter `next`
along with all buffers and capacities.

The theorems are `compileExpr_sim` (standalone, circuit expressions being a separate
AST) and the mutual `compileF_sim` / `compileU_sim` / `compileB_sim`, mirroring the
mutual compilers. The field leaf gadgets are handled by `WitgenSim.lean`; this file
is the induction glue and the word-level facts for the remaining instructions.

At the compiler's design point: `w = 64`, `F = F p` for a prime `p` with `2 < p` and
`p * p ≤ 2 ^ 64`. The environment is encoded in buffer `0` (`EnvEnc`) and its length
`N` must satisfy `N ≤ 2 ^ 64`, so that static `memLoad` indices baked as 64-bit
immediates read back exactly.
-/

namespace Caliper.WitgenCompile

open Witgen

/-! ## Word-level helper lemmas -/

/-- Distinct u64 values have distinct bit-pattern words. -/
private theorem encU_injective : Function.Injective encU := by
  intro a b h
  have h' := congrArg BitVec.toNat h
  rw [encU_toNat, encU_toNat] at h'
  exact UInt64.toNat_inj.mp h'

/-- The shift-amount mask `&&& (w - 1)` of the compiled u64 shifts is `% 64` on
values, matching `UInt64`'s mod-64 shift semantics. -/
private theorem toNat_and_63 (y : Word 64) :
    (y &&& BitVec.ofNat 64 (64 - 1)).toNat = y.toNat % 64 := by
  have h63 : (64 - 1) % 2 ^ 64 = 2 ^ 6 - 1 := by norm_num
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, h63, Nat.and_two_pow_sub_one_eq_mod]

private theorem encU_add (a b : UInt64) : encU a + encU b = encU (a + b) := by
  apply BitVec.eq_of_toNat_eq; simp [encU_toNat]

private theorem encU_mul (a b : UInt64) : encU a * encU b = encU (a * b) := by
  apply BitVec.eq_of_toNat_eq; simp [encU_toNat]

private theorem encU_div (a b : UInt64) : encU a / encU b = encU (a / b) := by
  apply BitVec.eq_of_toNat_eq; simp [encU_toNat]

private theorem encU_mod (a b : UInt64) : encU a % encU b = encU (a % b) := by
  apply BitVec.eq_of_toNat_eq; simp [encU_toNat]

private theorem encU_and (a b : UInt64) : encU a &&& encU b = encU (a &&& b) := by
  apply BitVec.eq_of_toNat_eq; simp [encU_toNat]

private theorem encU_or (a b : UInt64) : encU a ||| encU b = encU (a ||| b) := by
  apply BitVec.eq_of_toNat_eq; simp [encU_toNat]

private theorem encU_xor (a b : UInt64) : encU a ^^^ encU b = encU (a ^^^ b) := by
  apply BitVec.eq_of_toNat_eq; simp [encU_toNat]

/-- The compiled left shift (mask, then machine `shl`) agrees with `UInt64.shiftLeft`. -/
private theorem encU_shiftL (a b : UInt64) :
    encU a <<< (encU b &&& BitVec.ofNat 64 (64 - 1)).toNat = encU (a <<< b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, toNat_and_63, encU_toNat, encU_toNat, encU_toNat,
    UInt64.toNat_shiftLeft]

/-- The compiled right shift (mask, then machine `shr`) agrees with `UInt64.shiftRight`. -/
private theorem encU_shiftR (a b : UInt64) :
    encU a >>> (encU b &&& BitVec.ofNat 64 (64 - 1)).toNat = encU (a >>> b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, toNat_and_63, encU_toNat, encU_toNat, encU_toNat,
    UInt64.toNat_shiftRight]

/-- The condition-word `&&&` is boolean conjunction. -/
private theorem encB_and (a b : Bool) : encB a &&& encB b = encB (a && b) := by
  cases a <;> cases b <;> decide

/-- The `isZero` of a condition word is the negated condition's word. -/
private theorem encB_not (b : Bool) :
    (if encB b = 0 then 1 else 0 : Word 64) = encB (!b) := by
  cases b <;> decide

/-- The `eq`-comparison of bit-pattern words decides u64 equality (generic in the
`Decidable` instance, to match whatever instance the reference `eval` elaborated). -/
private theorem encB_ueq (x y : UInt64) [Decidable (x = y)] :
    (if encU x = encU y then 1 else 0 : Word 64) = encB (decide (x = y)) := by
  by_cases h : x = y
  · rw [decide_eq_true h, if_pos (congrArg encU h)]
    rfl
  · rw [decide_eq_false h, if_neg fun he => h (encU_injective he)]
    rfl

/-- The `ult`-comparison of bit-pattern words decides u64 `<`. -/
private theorem encB_ult (x y : UInt64) [Decidable (x < y)] :
    (if (encU x).toNat < (encU y).toNat then 1 else 0 : Word 64) =
      encB (decide (x < y)) := by
  rw [encU_toNat, encU_toNat]
  by_cases h : x < y
  · rw [decide_eq_true h, if_pos (UInt64.lt_iff_toNat_lt.mp h)]
    rfl
  · rw [decide_eq_false h, if_neg fun hlt => h (UInt64.lt_iff_toNat_lt.mpr hlt)]
    rfl

/-- The word of a u64 constant, baked as a `toNat` immediate, is its bit pattern. -/
private theorem encU_ofNat_toNat (n : UInt64) : BitVec.ofNat 64 n.toNat = encU n := by
  apply BitVec.eq_of_toNat_eq
  rw [encU_toNat, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt n.toBitVec.isLt

/-- The `idx` register's word reads back as the u64 of the index. -/
private theorem encU_ofNat (n : ℕ) : BitVec.ofNat 64 n = encU (UInt64.ofNat n) := rfl

section FieldWord

variable {p : ℕ} [Fact p.Prime]

/-- The canonical word of `1`. -/
private theorem encF_one : encF (1 : F p) = 1 := by
  have h2 := (Fact.out : p.Prime).two_le
  apply BitVec.eq_of_toNat_eq
  rw [encF, BitVec.toNat_ofNat, ZMod.val_one_eq_one_mod,
    Nat.mod_eq_of_lt (show 1 < p by omega)]
  rfl

omit [Fact p.Prime] in
/-- The `val` bridge: the bit pattern of `UInt64.ofNat x.val` is the canonical word
(both sides truncate `val x` mod `2 ^ 64`). -/
private theorem encU_ofNat_val (x : F p) :
    encU (UInt64.ofNat (ZMod.val x)) = encF x := rfl

/-- The `ofU64` bridge: reducing a bit-pattern word by the modulus immediate gives
the canonical word of the `ℕ`-cast. -/
private theorem encU_umod_p (hpw : p * p ≤ 2 ^ 64) (u : UInt64) :
    encU u % BitVec.ofNat 64 p = encF ((u.toNat : F p)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_umod, encU_toNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (p_lt_two_pow_64 hpw), encF_toNat hpw, ZMod.val_natCast]

/-- The `eq`-comparison of canonical words decides field equality. The `Decidable`
instance is a strict-implicit binder used via `@decide`, so that it is solved by
unification against the instance the reference `eval` elaborated (not re-synthesized,
which would pick a different-but-propositionally-equal instance). -/
private theorem encB_feq (hpw : p * p ≤ 2 ^ 64) (x y : F p) {inst : Decidable (x = y)} :
    (if encF x = encF y then 1 else 0 : Word 64) = encB (@decide (x = y) inst) := by
  cases hd : @decide (x = y) inst with
  | false =>
    rw [if_neg fun he => of_decide_eq_false hd (encF_injective hpw he)]
    rfl
  | true =>
    rw [if_pos (congrArg encF (of_decide_eq_true hd))]
    rfl

/-- The `ult`-comparison of canonical words decides the field-value `<`. -/
private theorem encB_flt (hpw : p * p ≤ 2 ^ 64) (x y : F p)
    [Decidable (ZMod.val x < ZMod.val y)] :
    (if (encF x).toNat < (encF y).toNat then 1 else 0 : Word 64) =
      encB (decide (ZMod.val x < ZMod.val y)) := by
  rw [encF_toNat hpw, encF_toNat hpw]
  by_cases h : ZMod.val x < ZMod.val y
  · rw [decide_eq_true h, if_pos h]
    rfl
  · rw [decide_eq_false h, if_neg h]
    rfl

/-- Shift-and-mask extraction of bit `i` of a canonical word. -/
private theorem encF_testBit (hpw : p * p ≤ 2 ^ 64) (x : F p) {i : ℕ}
    (hi : i < 2 ^ 64) :
    encF x >>> (BitVec.ofNat 64 i).toNat &&& 1 = encB ((ZMod.val x).testBit i) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, encF_toNat hpw, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hi, Nat.shiftRight_eq_div_pow, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (ZMod.val x / 2 ^ i) with h | h <;>
    simp [Nat.and_one_is_mod, h, encB]

end FieldWord

/-! ## Register bounds of the scalar compilers

The scalar compilers thread `next` monotonically and return `next ≤ next'` with
`resultReg < next'`. Because the copy-eliding arms return a local register or the idx
register directly rather than a fresh temporary, the result bound is not purely
syntactic: it needs the expression compilable against `Γ`, `Γ.length ≤ L`, and
`L < next` — the facts `LocalsMatch` and `StateEnc` provide. These bounds justify the
operand-survival steps of the simulation proofs.

Register inequalities here and below are stated over bare `ℕ`, not the `Reg` abbrev:
`omega` does not unfold `Reg`, so a hypothesis at type `Reg` is invisible to it. -/

/-- `compileExpr` register bounds: `next ≤ next'` and `resultReg < next'`. -/
theorem compileExpr_bounds {F : Type} [FiniteField F] :
    ∀ (e : Expression F) (next : ℕ),
    next ≤ (compileExpr (w := 64) e next).2.2 ∧
      LT.lt (α := ℕ) (compileExpr (w := 64) e next).2.1 (compileExpr (w := 64) e next).2.2
  | .var _, next => ⟨Nat.le_add_right next 2, Nat.lt_succ_self (next + 1)⟩
  | .const _, next => ⟨Nat.le_succ next, Nat.lt_succ_self next⟩
  | .add x y, next =>
    have h₁ := compileExpr_bounds x next
    have h₂ := compileExpr_bounds y (compileExpr (w := 64) x next).2.2
    ⟨Nat.le_trans h₁.1 (Nat.le_trans h₂.1 (Nat.le_add_right _ 2)), Nat.lt_succ_self _⟩
  | .mul x y, next =>
    have h₁ := compileExpr_bounds x next
    have h₂ := compileExpr_bounds y (compileExpr (w := 64) x next).2.2
    ⟨Nat.le_trans h₁.1 (Nat.le_trans h₂.1 (Nat.le_add_right _ 2)), Nat.lt_succ_self _⟩

mutual

/-- `compileF` register bounds: for compilable expressions (with `Γ.length ≤ L`
and `L < next`), `next ≤ next'` and `resultReg < next'`. -/
theorem compileF_bounds {F : Type} [FiniteField F] {Γ : List VSort} (L : ℕ)
    (hΓ : Γ.length ≤ L) :
    ∀ (e : FExpr F) (next : ℕ), FExpr.compilable Γ e = true →
      LT.lt (α := ℕ) L next →
    next ≤ (compileF (w := 64) L e next).2.2 ∧
      LT.lt (α := ℕ) (compileF (w := 64) L e next).2.1 (compileF (w := 64) L e next).2.2
  | .expr e, next, _, _ => compileExpr_bounds e next
  | .const _, next, _, _ => ⟨Nat.le_succ next, Nat.lt_succ_self next⟩
  | .localVar i, next, hc, hLn => by
    simp only [FExpr.compilable, beq_iff_eq] at hc
    have hi : i < Γ.length := by
      by_contra hge
      rw [List.getElem?_eq_none (by omega)] at hc
      exact absurd hc (by simp)
    exact ⟨Nat.le_refl next, show LT.lt (α := ℕ) i next by omega⟩
  | .add x y, next, hc, hLn => by
    simp only [FExpr.compilable, Bool.and_eq_true] at hc
    have h₁ := compileF_bounds L hΓ x next hc.1 hLn
    have h₂ := compileF_bounds L hΓ y (compileF (w := 64) L x next).2.2 hc.2
      (Nat.lt_of_lt_of_le hLn h₁.1)
    exact ⟨Nat.le_trans h₁.1 (Nat.le_trans h₂.1 (Nat.le_add_right _ 2)),
      Nat.lt_succ_self _⟩
  | .mul x y, next, hc, hLn => by
    simp only [FExpr.compilable, Bool.and_eq_true] at hc
    have h₁ := compileF_bounds L hΓ x next hc.1 hLn
    have h₂ := compileF_bounds L hΓ y (compileF (w := 64) L x next).2.2 hc.2
      (Nat.lt_of_lt_of_le hLn h₁.1)
    exact ⟨Nat.le_trans h₁.1 (Nat.le_trans h₂.1 (Nat.le_add_right _ 2)),
      Nat.lt_succ_self _⟩
  | .inv x, next, hc, hLn =>
    have h₁ := compileF_bounds L hΓ x next hc hLn
    ⟨Nat.le_trans h₁.1 (Nat.le_add_right _ 2), Nat.lt_succ_self _⟩
  | .ofU64 n, next, hc, hLn =>
    have h₁ := compileU_bounds L hΓ n next hc hLn
    ⟨Nat.le_trans h₁.1 (Nat.le_add_right _ 2), Nat.lt_succ_self _⟩
  | .ite c t e, next, hc, hLn => by
    simp only [FExpr.compilable, Bool.and_eq_true] at hc
    have h₁ := compileB_bounds L hΓ c next hc.1.1 hLn
    have h₂ := compileF_bounds L hΓ t (compileB (w := 64) L c next).2.2 hc.1.2
      (Nat.lt_of_lt_of_le hLn h₁.1)
    have h₃ := compileF_bounds L hΓ e
      (compileF (w := 64) L t (compileB (w := 64) L c next).2.2).2.2 hc.2
      (Nat.lt_of_lt_of_le hLn (Nat.le_trans h₁.1 h₂.1))
    exact ⟨Nat.le_trans h₁.1 (Nat.le_trans h₂.1 (Nat.le_trans h₃.1
      (Nat.le_add_right _ 5))), Nat.lt_succ_self _⟩
  | .listGet .., next, _, _ => ⟨Nat.le_succ next, Nat.lt_succ_self next⟩
  | .dataGet .., next, _, _ => ⟨Nat.le_succ next, Nat.lt_succ_self next⟩
  | .hintGet .., next, _, _ => ⟨Nat.le_succ next, Nat.lt_succ_self next⟩

/-- `compileU` register bounds: for compilable expressions (with `Γ.length ≤ L`
and `L < next`), `next ≤ next'` and `resultReg < next'`. -/
theorem compileU_bounds {F : Type} [FiniteField F] {Γ : List VSort} (L : ℕ)
    (hΓ : Γ.length ≤ L) :
    ∀ (e : U64Expr F) (next : ℕ), U64Expr.compilable Γ e = true →
      LT.lt (α := ℕ) L next →
    next ≤ (compileU (w := 64) L e next).2.2 ∧
      LT.lt (α := ℕ) (compileU (w := 64) L e next).2.1 (compileU (w := 64) L e next).2.2
  | .const _, next, _, _ => ⟨Nat.le_succ next, Nat.lt_succ_self next⟩
  | .val x, next, hc, hLn => compileF_bounds L hΓ x next hc hLn
  | .idx, next, _, hLn => ⟨Nat.le_refl next, hLn⟩
  | .localVar i, next, hc, hLn => by
    simp only [U64Expr.compilable, beq_iff_eq] at hc
    have hi : i < Γ.length := by
      by_contra hge
      rw [List.getElem?_eq_none (by omega)] at hc
      exact absurd hc (by simp)
    exact ⟨Nat.le_refl next, show LT.lt (α := ℕ) i next by omega⟩
  | .add x y, next, hc, hLn => by
    simp only [U64Expr.compilable, Bool.and_eq_true] at hc
    have h₁ := compileU_bounds L hΓ x next hc.1 hLn
    have h₂ := compileU_bounds L hΓ y (compileU (w := 64) L x next).2.2 hc.2
      (Nat.lt_of_lt_of_le hLn h₁.1)
    exact ⟨Nat.le_trans h₁.1 (Nat.le_trans h₂.1 (Nat.le_succ _)), Nat.lt_succ_self _⟩
  | .mul x y, next, hc, hLn => by
    simp only [U64Expr.compilable, Bool.and_eq_true] at hc
    have h₁ := compileU_bounds L hΓ x next hc.1 hLn
    have h₂ := compileU_bounds L hΓ y (compileU (w := 64) L x next).2.2 hc.2
      (Nat.lt_of_lt_of_le hLn h₁.1)
    exact ⟨Nat.le_trans h₁.1 (Nat.le_trans h₂.1 (Nat.le_succ _)), Nat.lt_succ_self _⟩
  | .div x y, next, hc, hLn => by
    simp only [U64Expr.compilable, Bool.and_eq_true] at hc
    have h₁ := compileU_bounds L hΓ x next hc.1 hLn
    have h₂ := compileU_bounds L hΓ y (compileU (w := 64) L x next).2.2 hc.2
      (Nat.lt_of_lt_of_le hLn h₁.1)
    exact ⟨Nat.le_trans h₁.1 (Nat.le_trans h₂.1 (Nat.le_succ _)), Nat.lt_succ_self _⟩
  | .mod x y, next, hc, hLn => by
    simp only [U64Expr.compilable, Bool.and_eq_true] at hc
    have h₁ := compileU_bounds L hΓ x next hc.1 hLn
    have h₂ := compileU_bounds L hΓ y (compileU (w := 64) L x next).2.2 hc.2
      (Nat.lt_of_lt_of_le hLn h₁.1)
    exact ⟨Nat.le_trans h₁.1 (Nat.le_trans h₂.1 (Nat.le_succ _)), Nat.lt_succ_self _⟩
  | .land x y, next, hc, hLn => by
    simp only [U64Expr.compilable, Bool.and_eq_true] at hc
    have h₁ := compileU_bounds L hΓ x next hc.1 hLn
    have h₂ := compileU_bounds L hΓ y (compileU (w := 64) L x next).2.2 hc.2
      (Nat.lt_of_lt_of_le hLn h₁.1)
    exact ⟨Nat.le_trans h₁.1 (Nat.le_trans h₂.1 (Nat.le_succ _)), Nat.lt_succ_self _⟩
  | .lor x y, next, hc, hLn => by
    simp only [U64Expr.compilable, Bool.and_eq_true] at hc
    have h₁ := compileU_bounds L hΓ x next hc.1 hLn
    have h₂ := compileU_bounds L hΓ y (compileU (w := 64) L x next).2.2 hc.2
      (Nat.lt_of_lt_of_le hLn h₁.1)
    exact ⟨Nat.le_trans h₁.1 (Nat.le_trans h₂.1 (Nat.le_succ _)), Nat.lt_succ_self _⟩
  | .lxor x y, next, hc, hLn => by
    simp only [U64Expr.compilable, Bool.and_eq_true] at hc
    have h₁ := compileU_bounds L hΓ x next hc.1 hLn
    have h₂ := compileU_bounds L hΓ y (compileU (w := 64) L x next).2.2 hc.2
      (Nat.lt_of_lt_of_le hLn h₁.1)
    exact ⟨Nat.le_trans h₁.1 (Nat.le_trans h₂.1 (Nat.le_succ _)), Nat.lt_succ_self _⟩
  | .shiftL x y, next, hc, hLn => by
    simp only [U64Expr.compilable, Bool.and_eq_true] at hc
    have h₁ := compileU_bounds L hΓ x next hc.1 hLn
    have h₂ := compileU_bounds L hΓ y (compileU (w := 64) L x next).2.2 hc.2
      (Nat.lt_of_lt_of_le hLn h₁.1)
    exact ⟨Nat.le_trans h₁.1 (Nat.le_trans h₂.1 (Nat.le_add_right _ 3)),
      Nat.lt_succ_self _⟩
  | .shiftR x y, next, hc, hLn => by
    simp only [U64Expr.compilable, Bool.and_eq_true] at hc
    have h₁ := compileU_bounds L hΓ x next hc.1 hLn
    have h₂ := compileU_bounds L hΓ y (compileU (w := 64) L x next).2.2 hc.2
      (Nat.lt_of_lt_of_le hLn h₁.1)
    exact ⟨Nat.le_trans h₁.1 (Nat.le_trans h₂.1 (Nat.le_add_right _ 3)),
      Nat.lt_succ_self _⟩
  | .ite c t e, next, hc, hLn => by
    simp only [U64Expr.compilable, Bool.and_eq_true] at hc
    have h₁ := compileB_bounds L hΓ c next hc.1.1 hLn
    have h₂ := compileU_bounds L hΓ t (compileB (w := 64) L c next).2.2 hc.1.2
      (Nat.lt_of_lt_of_le hLn h₁.1)
    have h₃ := compileU_bounds L hΓ e
      (compileU (w := 64) L t (compileB (w := 64) L c next).2.2).2.2 hc.2
      (Nat.lt_of_lt_of_le hLn (Nat.le_trans h₁.1 h₂.1))
    exact ⟨Nat.le_trans h₁.1 (Nat.le_trans h₂.1 (Nat.le_trans h₃.1
      (Nat.le_add_right _ 5))), Nat.lt_succ_self _⟩

/-- `compileB` register bounds: for compilable expressions (with `Γ.length ≤ L`
and `L < next`), `next ≤ next'` and `resultReg < next'`. -/
theorem compileB_bounds {F : Type} [FiniteField F] {Γ : List VSort} (L : ℕ)
    (hΓ : Γ.length ≤ L) :
    ∀ (e : BExpr F) (next : ℕ), BExpr.compilable Γ e = true →
      LT.lt (α := ℕ) L next →
    next ≤ (compileB (w := 64) L e next).2.2 ∧
      LT.lt (α := ℕ) (compileB (w := 64) L e next).2.1 (compileB (w := 64) L e next).2.2
  | .true, next, _, _ => ⟨Nat.le_succ next, Nat.lt_succ_self next⟩
  | .false, next, _, _ => ⟨Nat.le_succ next, Nat.lt_succ_self next⟩
  | .feq x y, next, hc, hLn => by
    simp only [BExpr.compilable, Bool.and_eq_true] at hc
    have h₁ := compileF_bounds L hΓ x next hc.1 hLn
    have h₂ := compileF_bounds L hΓ y (compileF (w := 64) L x next).2.2 hc.2
      (Nat.lt_of_lt_of_le hLn h₁.1)
    exact ⟨Nat.le_trans h₁.1 (Nat.le_trans h₂.1 (Nat.le_succ _)), Nat.lt_succ_self _⟩
  | .neq x y, next, hc, hLn => by
    simp only [BExpr.compilable, Bool.and_eq_true] at hc
    have h₁ := compileU_bounds L hΓ x next hc.1 hLn
    have h₂ := compileU_bounds L hΓ y (compileU (w := 64) L x next).2.2 hc.2
      (Nat.lt_of_lt_of_le hLn h₁.1)
    exact ⟨Nat.le_trans h₁.1 (Nat.le_trans h₂.1 (Nat.le_succ _)), Nat.lt_succ_self _⟩
  | .lt x y, next, hc, hLn => by
    simp only [BExpr.compilable, Bool.and_eq_true] at hc
    have h₁ := compileU_bounds L hΓ x next hc.1 hLn
    have h₂ := compileU_bounds L hΓ y (compileU (w := 64) L x next).2.2 hc.2
      (Nat.lt_of_lt_of_le hLn h₁.1)
    exact ⟨Nat.le_trans h₁.1 (Nat.le_trans h₂.1 (Nat.le_succ _)), Nat.lt_succ_self _⟩
  | .flt x y, next, hc, hLn => by
    simp only [BExpr.compilable, Bool.and_eq_true] at hc
    have h₁ := compileF_bounds L hΓ x next hc.1 hLn
    have h₂ := compileF_bounds L hΓ y (compileF (w := 64) L x next).2.2 hc.2
      (Nat.lt_of_lt_of_le hLn h₁.1)
    exact ⟨Nat.le_trans h₁.1 (Nat.le_trans h₂.1 (Nat.le_succ _)), Nat.lt_succ_self _⟩
  | .bit x _, next, hc, hLn => by
    simp only [BExpr.compilable, Bool.and_eq_true] at hc
    have h₁ := compileF_bounds L hΓ x next hc.1 hLn
    exact ⟨Nat.le_trans h₁.1 (Nat.le_add_right _ 4), Nat.lt_succ_self _⟩
  | .not b, next, hc, hLn =>
    have h₁ := compileB_bounds L hΓ b next hc hLn
    ⟨Nat.le_trans h₁.1 (Nat.le_succ _), Nat.lt_succ_self _⟩
  | .and x y, next, hc, hLn => by
    simp only [BExpr.compilable, Bool.and_eq_true] at hc
    have h₁ := compileB_bounds L hΓ x next hc.1 hLn
    have h₂ := compileB_bounds L hΓ y (compileB (w := 64) L x next).2.2 hc.2
      (Nat.lt_of_lt_of_le hLn h₁.1)
    exact ⟨Nat.le_trans h₁.1 (Nat.le_trans h₂.1 (Nat.le_succ _)), Nat.lt_succ_self _⟩

end

/-! ## The simulation theorems -/

section Sim

variable {C : CostModel} (p : ℕ) [Fact p.Prime] (hp2 : 2 < p) (hpw : p * p ≤ 2 ^ 64)
variable (env : ProverEnvironment (F p)) (N : ℕ) (envArr : Array (Word 64))
variable (henv : EnvEnc env N envArr) (hN : N ≤ 2 ^ 64)

omit [Fact p.Prime] in
/-- `StateEnc` is stable under raising the temporary bound and executing code that
preserves the registers below the old bound and the buffers. This is the threading
step of the compiler induction: after running a compiled subexpression (which only
writes registers in `[next, next')`), the state still encodes the context at the
subexpression's returned counter. -/
theorem StateEnc_mono {Γ : List VSort} {locals : Array (F p ⊕ UInt64)}
    {idx L next next' : ℕ} {s s' : State 64}
    (hs : StateEnc envArr Γ locals idx L next s) (hle : next ≤ next')
    (hpres : ∀ q, q < next → s'.regs q = s.regs q) (hbufs : s'.bufs = s.bufs) :
    StateEnc envArr Γ locals idx L next' s' := by
  obtain ⟨hbuf, h1, h2, h3, h4⟩ := hs
  refine ⟨by rw [hbufs]; exact hbuf, h1, by omega, fun i hi => ?_, ?_⟩
  · rw [hpres i (by omega)]; exact h3 i hi
  · rw [hpres L h2]; exact h4

/-- Composition glue for the two-operand one-instruction nodes: run two compiled
subexpressions, then one `bin` on their result registers into `n₂`. -/
private theorem binop_glue {C : CostModel} {op : BinOp} {c₁ c₂ : Stmt 64}
    {next n₁ n₂ r₁ r₂ : ℕ} (hr₁n : r₁ < n₁) (h₁₂ : n₁ ≤ n₂)
    (hn₁ : next ≤ n₁)
    {s s₁ s₂ : State 64} {t₁ t₂ : ℕ} {d₁ d₂ pp₁ pp₂ : ℤ} {v₁ v₂ : Word 64}
    (hex₁ : Exec C c₁ s s₁ t₁ d₁ pp₁) (hex₂ : Exec C c₂ s₁ s₂ t₂ d₂ pp₂)
    (hv₁ : s₁.regs r₁ = v₁) (hv₂ : s₂.regs r₂ = v₂)
    (hp₁ : ∀ q, q < next → s₁.regs q = s.regs q)
    (hp₂ : ∀ q, q < n₁ → s₂.regs q = s₁.regs q)
    (hb₁ : s₁.bufs = s.bufs) (hb₂ : s₂.bufs = s₁.bufs)
    (hc₁ : s₁.caps = s.caps) (hc₂ : s₂.caps = s₁.caps) :
    ∃ s' t d pp, Exec C (c₁ ;; c₂ ;; .bin op n₂ r₁ r₂) s s' t d pp ∧
      s'.regs n₂ = op.eval v₁ v₂ ∧
      (∀ q, q < next → s'.regs q = s.regs q) ∧ s'.bufs = s.bufs ∧ s'.caps = s.caps := by
  refine ⟨_, _, _, _, .seq hex₁ (.seq hex₂ .bin), ?_, ?_, ?_, ?_⟩
  · rw [regs_setReg_self, hp₂ r₁ hr₁n, hv₁, hv₂]
  · intro q hq
    rw [regs_setReg_ne _ _ (show q ≠ n₂ by omega), hp₂ q (by omega), hp₁ q hq]
  · rw [bufs_setReg, hb₂, hb₁]
  · rw [caps_setReg, hc₂, hc₁]

/-- Composition glue for the strict `ite` nodes: run the compiled condition and both
compiled branches, then the branch-free mask select on their result registers. -/
private theorem select_glue {C : CostModel} {c₁ c₂ c₃ : Stmt 64}
    {next n₁ n₂ n₃ rc rt re : ℕ}
    (hrc : rc < n₁) (h₁₂ : n₁ ≤ n₂) (hrt : rt < n₂) (h₂₃ : n₂ ≤ n₃) (hre : re < n₃)
    (hn₁ : next ≤ n₁)
    {s s₁ s₂ s₃ : State 64} {t₁ t₂ t₃ : ℕ} {d₁ d₂ d₃ pp₁ pp₂ pp₃ : ℤ}
    {cv : Bool} {v₁ v₂ : Word 64}
    (hex₁ : Exec C c₁ s s₁ t₁ d₁ pp₁) (hex₂ : Exec C c₂ s₁ s₂ t₂ d₂ pp₂)
    (hex₃ : Exec C c₃ s₂ s₃ t₃ d₃ pp₃)
    (hc : s₁.regs rc = encB cv) (ht : s₂.regs rt = v₁) (he : s₃.regs re = v₂)
    (hp₁ : ∀ q, q < next → s₁.regs q = s.regs q)
    (hp₂ : ∀ q, q < n₁ → s₂.regs q = s₁.regs q)
    (hp₃ : ∀ q, q < n₂ → s₃.regs q = s₂.regs q)
    (hb₁ : s₁.bufs = s.bufs) (hb₂ : s₂.bufs = s₁.bufs) (hb₃ : s₃.bufs = s₂.bufs)
    (hc₁ : s₁.caps = s.caps) (hc₂ : s₂.caps = s₁.caps) (hc₃ : s₃.caps = s₂.caps) :
    ∃ s' t d pp,
      Exec C (c₁ ;; c₂ ;; c₃ ;; (selectCode (w := 64) rc rt re n₃).1) s s' t d pp ∧
        s'.regs (n₃ + 4) = (if cv then v₁ else v₂) ∧
        (∀ q, q < next → s'.regs q = s.regs q) ∧
        s'.bufs = s.bufs ∧ s'.caps = s.caps := by
  obtain ⟨s₄, t₄, d₄, p₄, hex₄, hr₄, hp₄, hb₄, hc₄⟩ :=
    selectCode_exec (C := C) (flag := rc) (ra := rt) (rb := re) (next := n₃)
      (by omega) (by omega) hre
      ((hp₃ rc (by omega)).trans ((hp₂ rc hrc).trans hc))
      ((hp₃ rt hrt).trans ht) he
  refine ⟨_, _, _, _, .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)), hr₄, ?_, ?_, ?_⟩
  · intro q hq
    rw [hp₄ q (by omega), hp₃ q (by omega), hp₂ q (by omega), hp₁ q hq]
  · rw [hb₄, hb₃, hb₂, hb₁]
  · rw [hc₄, hc₃, hc₂, hc₁]

/-- Composition glue for the u64 shift nodes: run two compiled subexpressions, then
the mask immediate, the mask `and`, and the shift instruction. -/
private theorem shift_glue {C : CostModel} {op : BinOp} {c₁ c₂ : Stmt 64}
    {next n₁ n₂ r₁ r₂ : ℕ} (hr₁n : r₁ < n₁) (h₁₂ : n₁ ≤ n₂) (hr₂n : r₂ < n₂)
    (hn₁ : next ≤ n₁)
    {s s₁ s₂ : State 64} {t₁ t₂ : ℕ} {d₁ d₂ pp₁ pp₂ : ℤ} {v₁ v₂ : Word 64}
    (hex₁ : Exec C c₁ s s₁ t₁ d₁ pp₁) (hex₂ : Exec C c₂ s₁ s₂ t₂ d₂ pp₂)
    (hv₁ : s₁.regs r₁ = v₁) (hv₂ : s₂.regs r₂ = v₂)
    (hp₁ : ∀ q, q < next → s₁.regs q = s.regs q)
    (hp₂ : ∀ q, q < n₁ → s₂.regs q = s₁.regs q)
    (hb₁ : s₁.bufs = s.bufs) (hb₂ : s₂.bufs = s₁.bufs)
    (hc₁ : s₁.caps = s.caps) (hc₂ : s₂.caps = s₁.caps) :
    ∃ s' t d pp,
      Exec C (c₁ ;; c₂ ;; .imm n₂ (BitVec.ofNat 64 (64 - 1)) ;;
          .bin .and (n₂ + 1) r₂ n₂ ;; .bin op (n₂ + 2) r₁ (n₂ + 1)) s s' t d pp ∧
        s'.regs (n₂ + 2) = op.eval v₁ (v₂ &&& BitVec.ofNat 64 (64 - 1)) ∧
        (∀ q, q < next → s'.regs q = s.regs q) ∧
        s'.bufs = s.bufs ∧ s'.caps = s.caps := by
  refine ⟨_, _, _, _, .seq hex₁ (.seq hex₂ (.seq .imm (.seq .bin .bin))), ?_, ?_, ?_, ?_⟩
  · rw [regs_setReg_self,
      regs_setReg_ne _ _ (show r₁ ≠ n₂ + 1 by omega),
      regs_setReg_ne _ _ (show r₁ ≠ n₂ by omega), hp₂ r₁ hr₁n, hv₁,
      regs_setReg_self]
    simp only [BinOp.eval]
    rw [regs_setReg_ne _ _ (show r₂ ≠ n₂ by omega), hv₂, regs_setReg_self]
  · intro q hq
    rw [regs_setReg_ne _ _ (show q ≠ n₂ + 2 by omega),
      regs_setReg_ne _ _ (show q ≠ n₂ + 1 by omega),
      regs_setReg_ne _ _ (show q ≠ n₂ by omega),
      hp₂ q (by omega), hp₁ q hq]
  · rw [bufs_setReg, bufs_setReg, bufs_setReg, hb₂, hb₁]
  · rw [caps_setReg, caps_setReg, caps_setReg, hc₂, hc₁]

omit [Fact p.Prime] in
/-- Glue for the two-operand `bin` nodes of the mutual simulation theorems. Takes the
child compilations through their component equations, register bounds, the first
child's simulation result, the second child's simulation statement as a function of
the intermediate state, and the word-level fact `hword`. Each `bin` case is one
application of this lemma plus its `encU_*`/`encB_*` fact. -/
private theorem binop_sim {C : CostModel} {op : BinOp} {Γ : List VSort}
    {locals : Array (F p ⊕ UInt64)} {idx L next : ℕ} {s : State 64}
    {P₁ P₂ : Stmt 64 × ℕ × ℕ} {cx cy : Stmt 64} {rx ry n₁ n₂ : ℕ} {v₁ v₂ v : Word 64}
    (hs : StateEnc envArr Γ locals idx L next s)
    (hE₁ : P₁ = (cx, rx, n₁)) (hE₂ : P₂ = (cy, ry, n₂))
    (hbd₁ : LT.lt (α := ℕ) L next →
      next ≤ P₁.2.2 ∧ LT.lt (α := ℕ) P₁.2.1 P₁.2.2)
    (hbd₂ : LT.lt (α := ℕ) L n₁ →
      n₁ ≤ P₂.2.2 ∧ LT.lt (α := ℕ) P₂.2.1 P₂.2.2)
    (h₁ : ∃ s' t d pp, Exec C P₁.1 s s' t d pp ∧ s'.regs P₁.2.1 = v₁ ∧
      (∀ q, q < next → s'.regs q = s.regs q) ∧ s'.bufs = s.bufs ∧ s'.caps = s.caps)
    (h₂ : ∀ s₁ : State 64, StateEnc envArr Γ locals idx L n₁ s₁ →
      ∃ s' t d pp, Exec C P₂.1 s₁ s' t d pp ∧ s'.regs P₂.2.1 = v₂ ∧
        (∀ q, q < n₁ → s'.regs q = s₁.regs q) ∧
        s'.bufs = s₁.bufs ∧ s'.caps = s₁.caps)
    (hword : op.eval v₁ v₂ = v) :
    ∃ s' t d pp, Exec C (cx ;; cy ;; .bin op n₂ rx ry) s s' t d pp ∧
      s'.regs n₂ = v ∧ (∀ q, q < next → s'.regs q = s.regs q) ∧
      s'.bufs = s.bufs ∧ s'.caps = s.caps := by
  subst hE₁ hE₂
  have hLn : LT.lt (α := ℕ) L next := hs.2.2.1
  have hb₁ := hbd₁ hLn
  have hb₂ := hbd₂ (Nat.lt_of_lt_of_le hLn hb₁.1)
  obtain ⟨s₁, t₁, d₁, p₁, hex₁, hr₁, hp₁, hbf₁, hcp₁⟩ := h₁
  obtain ⟨s₂, t₂, d₂, p₂, hex₂, hr₂, hp₂, hbf₂, hcp₂⟩ :=
    h₂ s₁ (StateEnc_mono p envArr hs hb₁.1 hp₁ hbf₁)
  obtain ⟨s', t', d', pp', hex', hr', hp', hbf', hcp'⟩ :=
    binop_glue hb₁.2 hb₂.1 hb₁.1 hex₁ hex₂ hr₁ hr₂ hp₁ hp₂ hbf₁ hbf₂ hcp₁ hcp₂
  exact ⟨s', t', d', pp', hex', hword ▸ hr', hp', hbf', hcp'⟩

omit [Fact p.Prime] in
/-- As `binop_sim`, for the two u64 shift nodes of `compileU_sim` (mask immediate,
`and`, then the shift instruction — `shift_glue` internally). -/
private theorem shiftop_sim {C : CostModel} {op : BinOp} {Γ : List VSort}
    {locals : Array (F p ⊕ UInt64)} {idx L next : ℕ} {s : State 64}
    {P₁ P₂ : Stmt 64 × ℕ × ℕ} {cx cy : Stmt 64} {rx ry n₁ n₂ : ℕ} {v₁ v₂ v : Word 64}
    (hs : StateEnc envArr Γ locals idx L next s)
    (hE₁ : P₁ = (cx, rx, n₁)) (hE₂ : P₂ = (cy, ry, n₂))
    (hbd₁ : LT.lt (α := ℕ) L next →
      next ≤ P₁.2.2 ∧ LT.lt (α := ℕ) P₁.2.1 P₁.2.2)
    (hbd₂ : LT.lt (α := ℕ) L n₁ →
      n₁ ≤ P₂.2.2 ∧ LT.lt (α := ℕ) P₂.2.1 P₂.2.2)
    (h₁ : ∃ s' t d pp, Exec C P₁.1 s s' t d pp ∧ s'.regs P₁.2.1 = v₁ ∧
      (∀ q, q < next → s'.regs q = s.regs q) ∧ s'.bufs = s.bufs ∧ s'.caps = s.caps)
    (h₂ : ∀ s₁ : State 64, StateEnc envArr Γ locals idx L n₁ s₁ →
      ∃ s' t d pp, Exec C P₂.1 s₁ s' t d pp ∧ s'.regs P₂.2.1 = v₂ ∧
        (∀ q, q < n₁ → s'.regs q = s₁.regs q) ∧
        s'.bufs = s₁.bufs ∧ s'.caps = s₁.caps)
    (hword : op.eval v₁ (v₂ &&& BitVec.ofNat 64 (64 - 1)) = v) :
    ∃ s' t d pp,
      Exec C (cx ;; cy ;; .imm n₂ (BitVec.ofNat 64 (64 - 1)) ;;
          .bin .and (n₂ + 1) ry n₂ ;; .bin op (n₂ + 2) rx (n₂ + 1)) s s' t d pp ∧
        s'.regs (n₂ + 2) = v ∧ (∀ q, q < next → s'.regs q = s.regs q) ∧
        s'.bufs = s.bufs ∧ s'.caps = s.caps := by
  subst hE₁ hE₂
  have hLn : LT.lt (α := ℕ) L next := hs.2.2.1
  have hb₁ := hbd₁ hLn
  have hb₂ := hbd₂ (Nat.lt_of_lt_of_le hLn hb₁.1)
  obtain ⟨s₁, t₁, d₁, p₁, hex₁, hr₁, hp₁, hbf₁, hcp₁⟩ := h₁
  obtain ⟨s₂, t₂, d₂, p₂, hex₂, hr₂, hp₂, hbf₂, hcp₂⟩ :=
    h₂ s₁ (StateEnc_mono p envArr hs hb₁.1 hp₁ hbf₁)
  obtain ⟨s', t', d', pp', hex', hr', hp', hbf', hcp'⟩ :=
    shift_glue hb₁.2 hb₂.1 hb₂.2 hb₁.1
      hex₁ hex₂ hr₁ hr₂ hp₁ hp₂ hbf₁ hbf₂ hcp₁ hcp₂
  exact ⟨s', t', d', pp', hex', hword ▸ hr', hp', hbf', hcp'⟩

include hpw henv hN

/-- Simulation for circuit expressions: the code `compileExpr` emits for an
environment-bounded `Expression` runs from any state whose buffer `0` encodes the
environment (`EnvEnc`, via `hbuf`), leaves the canonical word of the reference
evaluation in the result register, and preserves registers `< next`, all buffers and
all capacities. -/
theorem compileExpr_sim :
    ∀ (e : Expression (F p)) (next : ℕ) (s : State 64),
      Expression.envBound N e = true → s.bufs 0 = envArr →
      ∃ s' t d pp, Exec C (compileExpr (w := 64) e next).1 s s' t d pp ∧
        s'.regs (compileExpr (w := 64) e next).2.1 = encF (e.eval env.toEnvironment) ∧
        (∀ q, q < next → s'.regs q = s.regs q) ∧ s'.bufs = s.bufs ∧ s'.caps = s.caps
  | .var v, next, s, hb, hbuf => by
    simp only [Expression.envBound, decide_eq_true_eq] at hb
    simp only [compileExpr]
    have hidx : (BitVec.ofNat 64 v.index).toNat = v.index := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
    have hlt : ((s.setReg next (BitVec.ofNat 64 v.index)).regs next).toNat <
        ((s.setReg next (BitVec.ofNat 64 v.index)).bufs 0).size := by
      rw [bufs_setReg, regs_setReg_self, hidx, hbuf, henv.1]
      exact hb
    refine ⟨_, _, _, _, .seq .imm (.memLoad hlt), ?_, ?_, rfl, rfl⟩
    · rw [regs_setReg_self, ← getElem!_pos]
      simp only [bufs_setReg, regs_setReg_self, hidx, hbuf]
      exact henv.2 v.index hb
    · intro q hq
      rw [regs_setReg_ne _ _ (show q ≠ next + 1 by omega),
        regs_setReg_ne _ _ (show q ≠ next by omega)]
  | .const c, next, s, _, _ => by
    simp only [compileExpr]
    refine ⟨_, _, _, _, .imm, ?_,
      fun q hq => regs_setReg_ne _ _ (show q ≠ next by omega), rfl, rfl⟩
    rw [regs_setReg_self]
    rfl
  | .add x y, next, s, hb, hbuf => by
    simp only [Expression.envBound, Bool.and_eq_true] at hb
    rcases hE₁ : compileExpr (w := 64) x next with ⟨cx, rx, n₁⟩
    rcases hE₂ : compileExpr (w := 64) y n₁ with ⟨cy, ry, n₂⟩
    have hbd₁ := compileExpr_bounds x next
    have hbd₂ := compileExpr_bounds y n₁
    simp only [hE₁] at hbd₁
    simp only [hE₂] at hbd₂
    obtain ⟨s₁, t₁, d₁, p₁, hex₁, hr₁, hp₁, hbf₁, hcp₁⟩ :=
      compileExpr_sim x next s hb.1 hbuf
    simp only [hE₁] at hex₁ hr₁
    obtain ⟨s₂, t₂, d₂, p₂, hex₂, hr₂, hp₂, hbf₂, hcp₂⟩ :=
      compileExpr_sim y n₁ s₁ hb.2 (by rw [hbf₁]; exact hbuf)
    simp only [hE₂] at hex₂ hr₂
    have hrx : s₂.regs rx = encF (x.eval env.toEnvironment) := by
      rw [hp₂ rx hbd₁.2]; exact hr₁
    obtain ⟨s₃, t₃, d₃, p₃, hex₃, hr₃, hp₃, hbf₃, hcp₃⟩ :=
      fieldOp_exec_add (p := p) hpw (a := rx) (b := ry) (next := n₂)
        (by omega) hbd₂.2 hrx hr₂
    simp only [compileExpr, hE₁, hE₂, fieldOp]
    refine ⟨_, _, _, _, .seq hex₁ (.seq hex₂ hex₃), hr₃, ?_, ?_, ?_⟩
    · intro q hq
      rw [hp₃ q (by omega), hp₂ q (by omega), hp₁ q hq]
    · rw [hbf₃, hbf₂, hbf₁]
    · rw [hcp₃, hcp₂, hcp₁]
  | .mul x y, next, s, hb, hbuf => by
    simp only [Expression.envBound, Bool.and_eq_true] at hb
    rcases hE₁ : compileExpr (w := 64) x next with ⟨cx, rx, n₁⟩
    rcases hE₂ : compileExpr (w := 64) y n₁ with ⟨cy, ry, n₂⟩
    have hbd₁ := compileExpr_bounds x next
    have hbd₂ := compileExpr_bounds y n₁
    simp only [hE₁] at hbd₁
    simp only [hE₂] at hbd₂
    obtain ⟨s₁, t₁, d₁, p₁, hex₁, hr₁, hp₁, hbf₁, hcp₁⟩ :=
      compileExpr_sim x next s hb.1 hbuf
    simp only [hE₁] at hex₁ hr₁
    obtain ⟨s₂, t₂, d₂, p₂, hex₂, hr₂, hp₂, hbf₂, hcp₂⟩ :=
      compileExpr_sim y n₁ s₁ hb.2 (by rw [hbf₁]; exact hbuf)
    simp only [hE₂] at hex₂ hr₂
    have hrx : s₂.regs rx = encF (x.eval env.toEnvironment) := by
      rw [hp₂ rx hbd₁.2]; exact hr₁
    obtain ⟨s₃, t₃, d₃, p₃, hex₃, hr₃, hp₃, hbf₃, hcp₃⟩ :=
      fieldOp_exec_mul (p := p) hpw (a := rx) (b := ry) (next := n₂)
        (by omega) hbd₂.2 hrx hr₂
    simp only [compileExpr, hE₁, hE₂, fieldOp]
    refine ⟨_, _, _, _, .seq hex₁ (.seq hex₂ hex₃), hr₃, ?_, ?_, ?_⟩
    · intro q hq
      rw [hp₃ q (by omega), hp₂ q (by omega), hp₁ q hq]
    · rw [hbf₃, hbf₂, hbf₁]
    · rw [hcp₃, hcp₂, hcp₁]

include hp2

/-! ### The mutual scalar-compiler induction

The context is fixed throughout: step-sort context `Γ` matching the reference locals,
environment `env` encoded in buffer `0`, locals in registers `0 .. locals.size - 1`,
the `mapRange` index in register `L`, temporaries free from `next`.

The `unusedSectionVars` linter is disabled for the block: `compileU_sim` uses the
included hypotheses only through the mutual recursion, which the linter does not
count, and `omit` cannot be applied to one member of a `mutual`. -/

set_option linter.unusedSectionVars false in
mutual

/-- Simulation for field-sorted expressions: the code `compileF` emits for a
compilable, environment-bounded `FExpr` runs from any state encoding the context,
leaves the canonical word of the reference evaluation in the result register, and
preserves registers `< next`, all buffers and all capacities. -/
theorem compileF_sim (Γ : List VSort) (locals : Array (F p ⊕ UInt64)) (idx L : ℕ)
    (hL : LocalsMatch Γ locals) :
    ∀ (e : FExpr (F p)) (next : ℕ) (s : State 64),
      FExpr.compilable Γ e = true → FExpr.envBound N e = true →
      StateEnc envArr Γ locals idx L next s →
      ∃ s' t d pp, Exec C (compileF (w := 64) L e next).1 s s' t d pp ∧
        s'.regs (compileF (w := 64) L e next).2.1 =
          encF (FExpr.eval { env, locals, idx } e) ∧
        (∀ q, q < next → s'.regs q = s.regs q) ∧
        s'.bufs = s.bufs ∧ s'.caps = s.caps
  | .expr e, next, s, _, hb, hs =>
    compileExpr_sim p hpw env N envArr henv hN e next s hb hs.1
  | .const c, next, s, _, _, _ => by
    simp only [compileF]
    refine ⟨_, _, _, _, .imm, ?_,
      fun q hq => regs_setReg_ne _ _ (show q ≠ next by omega), rfl, rfl⟩
    rw [regs_setReg_self]
    rfl
  | .localVar i, next, s, hc, _, hs => by
    simp only [FExpr.compilable, beq_iff_eq] at hc
    obtain ⟨hbuf0, hszL, hLn, hlocals, hidx⟩ := hs
    have hiΓ : i < Γ.length := by
      by_contra hge
      rw [List.getElem?_eq_none (by omega)] at hc
      exact absurd hc (by simp)
    have hlen := hL.1
    have hi : i < locals.size := by omega
    have hsort := hL.2 i hi
    rw [hc] at hsort
    rcases hx : locals[i] with x | u
    · -- no code: the local's register *is* the result
      simp only [compileF]
      refine ⟨s, 0, 0, 0, .skip, ?_, fun q _ => rfl, rfl, rfl⟩
      rw [hlocals i hi, hx]
      simp only [FExpr.eval, Array.getElem?_eq_getElem hi, hx, encLocal]
    · rw [hx] at hsort
      simp at hsort
  | .add x y, next, s, hc, hb, hs => by
    simp only [FExpr.compilable, Bool.and_eq_true] at hc
    simp only [FExpr.envBound, Bool.and_eq_true] at hb
    rcases hE₁ : compileF (w := 64) L x next with ⟨cx, rx, n₁⟩
    rcases hE₂ : compileF (w := 64) L y n₁ with ⟨cy, ry, n₂⟩
    have hΓ : Γ.length ≤ L := Nat.le_trans (Nat.le_of_eq hL.1) hs.2.1
    have hbd₁ := compileF_bounds L hΓ x next hc.1 hs.2.2.1
    simp only [hE₁] at hbd₁
    have hbd₂ := compileF_bounds L hΓ y n₁ hc.2
      (Nat.lt_of_lt_of_le hs.2.2.1 hbd₁.1)
    simp only [hE₂] at hbd₂
    obtain ⟨s₁, t₁, d₁, p₁, hex₁, hr₁, hp₁, hbf₁, hcp₁⟩ :=
      compileF_sim Γ locals idx L hL x next s hc.1 hb.1 hs
    simp only [hE₁] at hex₁ hr₁
    obtain ⟨s₂, t₂, d₂, p₂, hex₂, hr₂, hp₂, hbf₂, hcp₂⟩ :=
      compileF_sim Γ locals idx L hL y n₁ s₁ hc.2 hb.2
        (StateEnc_mono p envArr hs hbd₁.1 hp₁ hbf₁)
    simp only [hE₂] at hex₂ hr₂
    obtain ⟨s₃, t₃, d₃, p₃, hex₃, hr₃, hp₃, hbf₃, hcp₃⟩ :=
      fieldOp_exec_add (p := p) hpw (a := rx) (b := ry) (next := n₂)
        (by omega) hbd₂.2 ((hp₂ rx hbd₁.2).trans hr₁) hr₂
    simp only [compileF, hE₁, hE₂, fieldOp, FExpr.eval]
    refine ⟨_, _, _, _, .seq hex₁ (.seq hex₂ hex₃), hr₃, ?_, ?_, ?_⟩
    · intro q hq
      rw [hp₃ q (by omega), hp₂ q (by omega), hp₁ q hq]
    · rw [hbf₃, hbf₂, hbf₁]
    · rw [hcp₃, hcp₂, hcp₁]
  | .mul x y, next, s, hc, hb, hs => by
    simp only [FExpr.compilable, Bool.and_eq_true] at hc
    simp only [FExpr.envBound, Bool.and_eq_true] at hb
    rcases hE₁ : compileF (w := 64) L x next with ⟨cx, rx, n₁⟩
    rcases hE₂ : compileF (w := 64) L y n₁ with ⟨cy, ry, n₂⟩
    have hΓ : Γ.length ≤ L := Nat.le_trans (Nat.le_of_eq hL.1) hs.2.1
    have hbd₁ := compileF_bounds L hΓ x next hc.1 hs.2.2.1
    simp only [hE₁] at hbd₁
    have hbd₂ := compileF_bounds L hΓ y n₁ hc.2
      (Nat.lt_of_lt_of_le hs.2.2.1 hbd₁.1)
    simp only [hE₂] at hbd₂
    obtain ⟨s₁, t₁, d₁, p₁, hex₁, hr₁, hp₁, hbf₁, hcp₁⟩ :=
      compileF_sim Γ locals idx L hL x next s hc.1 hb.1 hs
    simp only [hE₁] at hex₁ hr₁
    obtain ⟨s₂, t₂, d₂, p₂, hex₂, hr₂, hp₂, hbf₂, hcp₂⟩ :=
      compileF_sim Γ locals idx L hL y n₁ s₁ hc.2 hb.2
        (StateEnc_mono p envArr hs hbd₁.1 hp₁ hbf₁)
    simp only [hE₂] at hex₂ hr₂
    obtain ⟨s₃, t₃, d₃, p₃, hex₃, hr₃, hp₃, hbf₃, hcp₃⟩ :=
      fieldOp_exec_mul (p := p) hpw (a := rx) (b := ry) (next := n₂)
        (by omega) hbd₂.2 ((hp₂ rx hbd₁.2).trans hr₁) hr₂
    simp only [compileF, hE₁, hE₂, fieldOp, FExpr.eval]
    refine ⟨_, _, _, _, .seq hex₁ (.seq hex₂ hex₃), hr₃, ?_, ?_, ?_⟩
    · intro q hq
      rw [hp₃ q (by omega), hp₂ q (by omega), hp₁ q hq]
    · rw [hbf₃, hbf₂, hbf₁]
    · rw [hcp₃, hcp₂, hcp₁]
  | .inv x, next, s, hc, hb, hs => by
    rcases hE₁ : compileF (w := 64) L x next with ⟨cx, rx, n₁⟩
    have hbd₁ := compileF_bounds L (Nat.le_trans (Nat.le_of_eq hL.1) hs.2.1) x next
      hc hs.2.2.1
    simp only [hE₁] at hbd₁
    obtain ⟨s₁, t₁, d₁, p₁, hex₁, hr₁, hp₁, hbf₁, hcp₁⟩ :=
      compileF_sim Γ locals idx L hL x next s hc hb hs
    simp only [hE₁] at hex₁ hr₁
    obtain ⟨s₃, t₃, d₃, p₃, hex₃, hr₃, hp₃, hbf₃, hcp₃⟩ :=
      invLadder_exec_inv (p := p) hp2 hpw (acc := n₁ + 1) (xr := rx) (tr := n₁)
        (show Ne (α := ℕ) rx (n₁ + 1) by omega)
        (show Ne (α := ℕ) n₁ (n₁ + 1) by omega)
        (s := (s₁.setReg n₁ (BitVec.ofNat 64 p)).setReg (n₁ + 1) 1)
        (v := FExpr.eval { env, locals, idx } x)
        (by rw [regs_setReg_self]; exact encF_one.symm)
        (by rw [regs_setReg_ne _ _ (show Ne (α := ℕ) rx (n₁ + 1) by omega),
              regs_setReg_ne _ _ (show Ne (α := ℕ) rx n₁ by omega)]
            exact hr₁)
        (by rw [regs_setReg_ne _ _ (show Ne (α := ℕ) n₁ (n₁ + 1) by omega),
              regs_setReg_self])
    simp only [compileF, hE₁, FExpr.eval]
    refine ⟨_, _, _, _, .seq hex₁ (.seq .imm (.seq .imm hex₃)), hr₃, ?_, ?_, ?_⟩
    · intro q hq
      rw [hp₃ q (show q ≠ n₁ + 1 by omega),
        regs_setReg_ne _ _ (show q ≠ n₁ + 1 by omega),
        regs_setReg_ne _ _ (show q ≠ n₁ by omega), hp₁ q hq]
    · rw [hbf₃, bufs_setReg, bufs_setReg, hbf₁]
    · rw [hcp₃, caps_setReg, caps_setReg, hcp₁]
  | .ofU64 n, next, s, hc, hb, hs => by
    rcases hE₁ : compileU (w := 64) L n next with ⟨cn, rn, n₁⟩
    have hbd₁ := compileU_bounds L (Nat.le_trans (Nat.le_of_eq hL.1) hs.2.1) n next
      hc hs.2.2.1
    simp only [hE₁] at hbd₁
    obtain ⟨s₁, t₁, d₁, p₁, hex₁, hr₁, hp₁, hbf₁, hcp₁⟩ :=
      compileU_sim Γ locals idx L hL n next s hc hb hs
    simp only [hE₁] at hex₁ hr₁
    simp only [compileF, hE₁, FExpr.eval, FiniteField.fromNat_F]
    refine ⟨_, _, _, _, .seq hex₁ (.seq .imm .bin), ?_, ?_, ?_, ?_⟩
    · rw [regs_setReg_self]
      simp only [BinOp.eval]
      rw [regs_setReg_ne _ _ (show Ne (α := ℕ) rn n₁ by omega), hr₁, regs_setReg_self]
      exact encU_umod_p hpw _
    · intro q hq
      rw [regs_setReg_ne _ _ (show q ≠ n₁ + 1 by omega),
        regs_setReg_ne _ _ (show q ≠ n₁ by omega), hp₁ q hq]
    · rw [bufs_setReg, bufs_setReg, hbf₁]
    · rw [caps_setReg, caps_setReg, hcp₁]
  | .ite c t e, next, s, hc, hb, hs => by
    simp only [FExpr.compilable, Bool.and_eq_true] at hc
    simp only [FExpr.envBound, Bool.and_eq_true] at hb
    obtain ⟨⟨hcc, hct⟩, hce⟩ := hc
    obtain ⟨⟨hbc, hbt⟩, hbe⟩ := hb
    rcases hE₁ : compileB (w := 64) L c next with ⟨cc, rc, n₁⟩
    rcases hE₂ : compileF (w := 64) L t n₁ with ⟨ct, rt, n₂⟩
    rcases hE₃ : compileF (w := 64) L e n₂ with ⟨ce, re, n₃⟩
    have hΓ : Γ.length ≤ L := Nat.le_trans (Nat.le_of_eq hL.1) hs.2.1
    have hbd₁ := compileB_bounds L hΓ c next hcc hs.2.2.1
    simp only [hE₁] at hbd₁
    have hbd₂ := compileF_bounds L hΓ t n₁ hct
      (Nat.lt_of_lt_of_le hs.2.2.1 hbd₁.1)
    simp only [hE₂] at hbd₂
    have hbd₃ := compileF_bounds L hΓ e n₂ hce
      (Nat.lt_of_lt_of_le hs.2.2.1 (Nat.le_trans hbd₁.1 hbd₂.1))
    simp only [hE₃] at hbd₃
    obtain ⟨s₁, t₁, d₁, p₁, hex₁, hr₁, hp₁, hbf₁, hcp₁⟩ :=
      compileB_sim Γ locals idx L hL c next s hcc hbc hs
    simp only [hE₁] at hex₁ hr₁
    obtain ⟨s₂, t₂, d₂, p₂, hex₂, hr₂, hp₂, hbf₂, hcp₂⟩ :=
      compileF_sim Γ locals idx L hL t n₁ s₁ hct hbt
        (StateEnc_mono p envArr hs hbd₁.1 hp₁ hbf₁)
    simp only [hE₂] at hex₂ hr₂
    obtain ⟨s₃, t₃, d₃, p₃, hex₃, hr₃, hp₃, hbf₃, hcp₃⟩ :=
      compileF_sim Γ locals idx L hL e n₂ s₂ hce hbe
        (StateEnc_mono p envArr (StateEnc_mono p envArr hs hbd₁.1 hp₁ hbf₁)
          hbd₂.1 hp₂ hbf₂)
    simp only [hE₃] at hex₃ hr₃
    obtain ⟨s', t', d', pp', hex', hr', hp', hbf', hcp'⟩ :=
      select_glue hbd₁.2 hbd₂.1 hbd₂.2 hbd₃.1 hbd₃.2 hbd₁.1
        hex₁ hex₂ hex₃ hr₁ hr₂ hr₃ hp₁ hp₂ hp₃ hbf₁ hbf₂ hbf₃ hcp₁ hcp₂ hcp₃
    simp only [compileF, hE₁, hE₂, hE₃, selectCode, FExpr.eval]
    refine ⟨_, _, _, _, hex', ?_, hp', hbf', hcp'⟩
    rw [hr', apply_ite encF]
  | .listGet .., _, _, hc, _, _ => by simp [FExpr.compilable] at hc
  | .dataGet .., _, _, hc, _, _ => by simp [FExpr.compilable] at hc
  | .hintGet .., _, _, hc, _, _ => by simp [FExpr.compilable] at hc

/-- Simulation for u64-sorted expressions: as `compileF_sim`, with the result
register holding the bit pattern of the reference `UInt64` evaluation. -/
theorem compileU_sim (Γ : List VSort) (locals : Array (F p ⊕ UInt64)) (idx L : ℕ)
    (hL : LocalsMatch Γ locals) :
    ∀ (e : U64Expr (F p)) (next : ℕ) (s : State 64),
      U64Expr.compilable Γ e = true → U64Expr.envBound N e = true →
      StateEnc envArr Γ locals idx L next s →
      ∃ s' t d pp, Exec C (compileU (w := 64) L e next).1 s s' t d pp ∧
        s'.regs (compileU (w := 64) L e next).2.1 =
          encU (U64Expr.eval { env, locals, idx } e) ∧
        (∀ q, q < next → s'.regs q = s.regs q) ∧
        s'.bufs = s.bufs ∧ s'.caps = s.caps
  | .const n, next, s, _, _, _ => by
    simp only [compileU]
    refine ⟨_, _, _, _, .imm, ?_,
      fun q hq => regs_setReg_ne _ _ (show q ≠ next by omega), rfl, rfl⟩
    rw [regs_setReg_self]
    simp only [U64Expr.eval]
    exact encU_ofNat_toNat n
  | .val x, next, s, hc, hb, hs => by
    -- no code, no copy: the child's canonical word *is* the u64 bit pattern
    obtain ⟨s₁, t₁, d₁, p₁, hex₁, hr₁, hp₁, hbf₁, hcp₁⟩ :=
      compileF_sim Γ locals idx L hL x next s hc hb hs
    simp only [compileU, U64Expr.eval, FiniteField.val_F]
    refine ⟨s₁, t₁, d₁, p₁, hex₁, ?_, hp₁, hbf₁, hcp₁⟩
    rw [hr₁]
    exact (encU_ofNat_val _).symm
  | .idx, next, s, _, _, hs => by
    -- no code: the idx register *is* the result
    obtain ⟨hbuf0, hszL, hLn, hlocals, hidx⟩ := hs
    simp only [compileU]
    refine ⟨s, 0, 0, 0, .skip, ?_, fun q _ => rfl, rfl, rfl⟩
    rw [hidx]
    simp only [U64Expr.eval]
    exact encU_ofNat idx
  | .localVar i, next, s, hc, _, hs => by
    simp only [U64Expr.compilable, beq_iff_eq] at hc
    obtain ⟨hbuf0, hszL, hLn, hlocals, hidx⟩ := hs
    have hiΓ : i < Γ.length := by
      by_contra hge
      rw [List.getElem?_eq_none (by omega)] at hc
      exact absurd hc (by simp)
    have hlen := hL.1
    have hi : i < locals.size := by omega
    have hsort := hL.2 i hi
    rw [hc] at hsort
    rcases hx : locals[i] with x | u
    · rw [hx] at hsort
      simp at hsort
    · -- no code: the local's register *is* the result
      simp only [compileU]
      refine ⟨s, 0, 0, 0, .skip, ?_, fun q _ => rfl, rfl, rfl⟩
      rw [hlocals i hi, hx]
      simp only [U64Expr.eval, Array.getElem?_eq_getElem hi, hx, encLocal]
  | .add x y, next, s, hc, hb, hs => by
    simp only [U64Expr.compilable, Bool.and_eq_true] at hc
    simp only [U64Expr.envBound, Bool.and_eq_true] at hb
    rcases hE₁ : compileU (w := 64) L x next with ⟨cx, rx, n₁⟩
    rcases hE₂ : compileU (w := 64) L y n₁ with ⟨cy, ry, n₂⟩
    simp only [compileU, hE₁, hE₂, U64Expr.eval]
    have hΓ : Γ.length ≤ L := Nat.le_trans (Nat.le_of_eq hL.1) hs.2.1
    exact binop_sim p envArr hs hE₁ hE₂ (compileU_bounds L hΓ x next hc.1)
      (compileU_bounds L hΓ y n₁ hc.2)
      (compileU_sim Γ locals idx L hL x next s hc.1 hb.1 hs)
      (fun s₁ hs₁ => compileU_sim Γ locals idx L hL y n₁ s₁ hc.2 hb.2 hs₁)
      (encU_add _ _)
  | .mul x y, next, s, hc, hb, hs => by
    simp only [U64Expr.compilable, Bool.and_eq_true] at hc
    simp only [U64Expr.envBound, Bool.and_eq_true] at hb
    rcases hE₁ : compileU (w := 64) L x next with ⟨cx, rx, n₁⟩
    rcases hE₂ : compileU (w := 64) L y n₁ with ⟨cy, ry, n₂⟩
    simp only [compileU, hE₁, hE₂, U64Expr.eval]
    have hΓ : Γ.length ≤ L := Nat.le_trans (Nat.le_of_eq hL.1) hs.2.1
    exact binop_sim p envArr hs hE₁ hE₂ (compileU_bounds L hΓ x next hc.1)
      (compileU_bounds L hΓ y n₁ hc.2)
      (compileU_sim Γ locals idx L hL x next s hc.1 hb.1 hs)
      (fun s₁ hs₁ => compileU_sim Γ locals idx L hL y n₁ s₁ hc.2 hb.2 hs₁)
      (encU_mul _ _)
  | .div x y, next, s, hc, hb, hs => by
    simp only [U64Expr.compilable, Bool.and_eq_true] at hc
    simp only [U64Expr.envBound, Bool.and_eq_true] at hb
    rcases hE₁ : compileU (w := 64) L x next with ⟨cx, rx, n₁⟩
    rcases hE₂ : compileU (w := 64) L y n₁ with ⟨cy, ry, n₂⟩
    simp only [compileU, hE₁, hE₂, U64Expr.eval]
    have hΓ : Γ.length ≤ L := Nat.le_trans (Nat.le_of_eq hL.1) hs.2.1
    exact binop_sim p envArr hs hE₁ hE₂ (compileU_bounds L hΓ x next hc.1)
      (compileU_bounds L hΓ y n₁ hc.2)
      (compileU_sim Γ locals idx L hL x next s hc.1 hb.1 hs)
      (fun s₁ hs₁ => compileU_sim Γ locals idx L hL y n₁ s₁ hc.2 hb.2 hs₁)
      (encU_div _ _)
  | .mod x y, next, s, hc, hb, hs => by
    simp only [U64Expr.compilable, Bool.and_eq_true] at hc
    simp only [U64Expr.envBound, Bool.and_eq_true] at hb
    rcases hE₁ : compileU (w := 64) L x next with ⟨cx, rx, n₁⟩
    rcases hE₂ : compileU (w := 64) L y n₁ with ⟨cy, ry, n₂⟩
    simp only [compileU, hE₁, hE₂, U64Expr.eval]
    have hΓ : Γ.length ≤ L := Nat.le_trans (Nat.le_of_eq hL.1) hs.2.1
    exact binop_sim p envArr hs hE₁ hE₂ (compileU_bounds L hΓ x next hc.1)
      (compileU_bounds L hΓ y n₁ hc.2)
      (compileU_sim Γ locals idx L hL x next s hc.1 hb.1 hs)
      (fun s₁ hs₁ => compileU_sim Γ locals idx L hL y n₁ s₁ hc.2 hb.2 hs₁)
      (encU_mod _ _)
  | .land x y, next, s, hc, hb, hs => by
    simp only [U64Expr.compilable, Bool.and_eq_true] at hc
    simp only [U64Expr.envBound, Bool.and_eq_true] at hb
    rcases hE₁ : compileU (w := 64) L x next with ⟨cx, rx, n₁⟩
    rcases hE₂ : compileU (w := 64) L y n₁ with ⟨cy, ry, n₂⟩
    simp only [compileU, hE₁, hE₂, U64Expr.eval]
    have hΓ : Γ.length ≤ L := Nat.le_trans (Nat.le_of_eq hL.1) hs.2.1
    exact binop_sim p envArr hs hE₁ hE₂ (compileU_bounds L hΓ x next hc.1)
      (compileU_bounds L hΓ y n₁ hc.2)
      (compileU_sim Γ locals idx L hL x next s hc.1 hb.1 hs)
      (fun s₁ hs₁ => compileU_sim Γ locals idx L hL y n₁ s₁ hc.2 hb.2 hs₁)
      (encU_and _ _)
  | .lor x y, next, s, hc, hb, hs => by
    simp only [U64Expr.compilable, Bool.and_eq_true] at hc
    simp only [U64Expr.envBound, Bool.and_eq_true] at hb
    rcases hE₁ : compileU (w := 64) L x next with ⟨cx, rx, n₁⟩
    rcases hE₂ : compileU (w := 64) L y n₁ with ⟨cy, ry, n₂⟩
    simp only [compileU, hE₁, hE₂, U64Expr.eval]
    have hΓ : Γ.length ≤ L := Nat.le_trans (Nat.le_of_eq hL.1) hs.2.1
    exact binop_sim p envArr hs hE₁ hE₂ (compileU_bounds L hΓ x next hc.1)
      (compileU_bounds L hΓ y n₁ hc.2)
      (compileU_sim Γ locals idx L hL x next s hc.1 hb.1 hs)
      (fun s₁ hs₁ => compileU_sim Γ locals idx L hL y n₁ s₁ hc.2 hb.2 hs₁)
      (encU_or _ _)
  | .lxor x y, next, s, hc, hb, hs => by
    simp only [U64Expr.compilable, Bool.and_eq_true] at hc
    simp only [U64Expr.envBound, Bool.and_eq_true] at hb
    rcases hE₁ : compileU (w := 64) L x next with ⟨cx, rx, n₁⟩
    rcases hE₂ : compileU (w := 64) L y n₁ with ⟨cy, ry, n₂⟩
    simp only [compileU, hE₁, hE₂, U64Expr.eval]
    have hΓ : Γ.length ≤ L := Nat.le_trans (Nat.le_of_eq hL.1) hs.2.1
    exact binop_sim p envArr hs hE₁ hE₂ (compileU_bounds L hΓ x next hc.1)
      (compileU_bounds L hΓ y n₁ hc.2)
      (compileU_sim Γ locals idx L hL x next s hc.1 hb.1 hs)
      (fun s₁ hs₁ => compileU_sim Γ locals idx L hL y n₁ s₁ hc.2 hb.2 hs₁)
      (encU_xor _ _)
  | .shiftL x y, next, s, hc, hb, hs => by
    simp only [U64Expr.compilable, Bool.and_eq_true] at hc
    simp only [U64Expr.envBound, Bool.and_eq_true] at hb
    rcases hE₁ : compileU (w := 64) L x next with ⟨cx, rx, n₁⟩
    rcases hE₂ : compileU (w := 64) L y n₁ with ⟨cy, ry, n₂⟩
    simp only [compileU, hE₁, hE₂, U64Expr.eval]
    have hΓ : Γ.length ≤ L := Nat.le_trans (Nat.le_of_eq hL.1) hs.2.1
    exact shiftop_sim p envArr hs hE₁ hE₂ (compileU_bounds L hΓ x next hc.1)
      (compileU_bounds L hΓ y n₁ hc.2)
      (compileU_sim Γ locals idx L hL x next s hc.1 hb.1 hs)
      (fun s₁ hs₁ => compileU_sim Γ locals idx L hL y n₁ s₁ hc.2 hb.2 hs₁)
      (encU_shiftL _ _)
  | .shiftR x y, next, s, hc, hb, hs => by
    simp only [U64Expr.compilable, Bool.and_eq_true] at hc
    simp only [U64Expr.envBound, Bool.and_eq_true] at hb
    rcases hE₁ : compileU (w := 64) L x next with ⟨cx, rx, n₁⟩
    rcases hE₂ : compileU (w := 64) L y n₁ with ⟨cy, ry, n₂⟩
    simp only [compileU, hE₁, hE₂, U64Expr.eval]
    have hΓ : Γ.length ≤ L := Nat.le_trans (Nat.le_of_eq hL.1) hs.2.1
    exact shiftop_sim p envArr hs hE₁ hE₂ (compileU_bounds L hΓ x next hc.1)
      (compileU_bounds L hΓ y n₁ hc.2)
      (compileU_sim Γ locals idx L hL x next s hc.1 hb.1 hs)
      (fun s₁ hs₁ => compileU_sim Γ locals idx L hL y n₁ s₁ hc.2 hb.2 hs₁)
      (encU_shiftR _ _)
  | .ite c t e, next, s, hc, hb, hs => by
    simp only [U64Expr.compilable, Bool.and_eq_true] at hc
    simp only [U64Expr.envBound, Bool.and_eq_true] at hb
    obtain ⟨⟨hcc, hct⟩, hce⟩ := hc
    obtain ⟨⟨hbc, hbt⟩, hbe⟩ := hb
    rcases hE₁ : compileB (w := 64) L c next with ⟨cc, rc, n₁⟩
    rcases hE₂ : compileU (w := 64) L t n₁ with ⟨ct, rt, n₂⟩
    rcases hE₃ : compileU (w := 64) L e n₂ with ⟨ce, re, n₃⟩
    have hΓ : Γ.length ≤ L := Nat.le_trans (Nat.le_of_eq hL.1) hs.2.1
    have hbd₁ := compileB_bounds L hΓ c next hcc hs.2.2.1
    simp only [hE₁] at hbd₁
    have hbd₂ := compileU_bounds L hΓ t n₁ hct
      (Nat.lt_of_lt_of_le hs.2.2.1 hbd₁.1)
    simp only [hE₂] at hbd₂
    have hbd₃ := compileU_bounds L hΓ e n₂ hce
      (Nat.lt_of_lt_of_le hs.2.2.1 (Nat.le_trans hbd₁.1 hbd₂.1))
    simp only [hE₃] at hbd₃
    obtain ⟨s₁, t₁, d₁, p₁, hex₁, hr₁, hp₁, hbf₁, hcp₁⟩ :=
      compileB_sim Γ locals idx L hL c next s hcc hbc hs
    simp only [hE₁] at hex₁ hr₁
    obtain ⟨s₂, t₂, d₂, p₂, hex₂, hr₂, hp₂, hbf₂, hcp₂⟩ :=
      compileU_sim Γ locals idx L hL t n₁ s₁ hct hbt
        (StateEnc_mono p envArr hs hbd₁.1 hp₁ hbf₁)
    simp only [hE₂] at hex₂ hr₂
    obtain ⟨s₃, t₃, d₃, p₃, hex₃, hr₃, hp₃, hbf₃, hcp₃⟩ :=
      compileU_sim Γ locals idx L hL e n₂ s₂ hce hbe
        (StateEnc_mono p envArr (StateEnc_mono p envArr hs hbd₁.1 hp₁ hbf₁)
          hbd₂.1 hp₂ hbf₂)
    simp only [hE₃] at hex₃ hr₃
    obtain ⟨s', t', d', pp', hex', hr', hp', hbf', hcp'⟩ :=
      select_glue hbd₁.2 hbd₂.1 hbd₂.2 hbd₃.1 hbd₃.2 hbd₁.1
        hex₁ hex₂ hex₃ hr₁ hr₂ hr₃ hp₁ hp₂ hp₃ hbf₁ hbf₂ hbf₃ hcp₁ hcp₂ hcp₃
    simp only [compileU, hE₁, hE₂, hE₃, selectCode, U64Expr.eval]
    refine ⟨_, _, _, _, hex', ?_, hp', hbf', hcp'⟩
    rw [hr', apply_ite encU]

/-- Simulation for conditions: as `compileF_sim`, with the result register
holding the `{0, 1}` word of the reference `Bool` evaluation. -/
theorem compileB_sim (Γ : List VSort) (locals : Array (F p ⊕ UInt64)) (idx L : ℕ)
    (hL : LocalsMatch Γ locals) :
    ∀ (e : BExpr (F p)) (next : ℕ) (s : State 64),
      BExpr.compilable Γ e = true → BExpr.envBound N e = true →
      StateEnc envArr Γ locals idx L next s →
      ∃ s' t d pp, Exec C (compileB (w := 64) L e next).1 s s' t d pp ∧
        s'.regs (compileB (w := 64) L e next).2.1 =
          encB (BExpr.eval { env, locals, idx } e) ∧
        (∀ q, q < next → s'.regs q = s.regs q) ∧
        s'.bufs = s.bufs ∧ s'.caps = s.caps
  | .true, next, s, _, _, _ => by
    simp only [compileB]
    refine ⟨_, _, _, _, .imm, ?_,
      fun q hq => regs_setReg_ne _ _ (show q ≠ next by omega), rfl, rfl⟩
    rw [regs_setReg_self]
    rfl
  | .false, next, s, _, _, _ => by
    simp only [compileB]
    refine ⟨_, _, _, _, .imm, ?_,
      fun q hq => regs_setReg_ne _ _ (show q ≠ next by omega), rfl, rfl⟩
    rw [regs_setReg_self]
    rfl
  | .feq x y, next, s, hc, hb, hs => by
    simp only [BExpr.compilable, Bool.and_eq_true] at hc
    simp only [BExpr.envBound, Bool.and_eq_true] at hb
    rcases hE₁ : compileF (w := 64) L x next with ⟨cx, rx, n₁⟩
    rcases hE₂ : compileF (w := 64) L y n₁ with ⟨cy, ry, n₂⟩
    simp only [compileB, hE₁, hE₂, BExpr.eval]
    have hΓ : Γ.length ≤ L := Nat.le_trans (Nat.le_of_eq hL.1) hs.2.1
    exact binop_sim p envArr hs hE₁ hE₂ (compileF_bounds L hΓ x next hc.1)
      (compileF_bounds L hΓ y n₁ hc.2)
      (compileF_sim Γ locals idx L hL x next s hc.1 hb.1 hs)
      (fun s₁ hs₁ => compileF_sim Γ locals idx L hL y n₁ s₁ hc.2 hb.2 hs₁)
      (encB_feq hpw _ _)
  | .neq x y, next, s, hc, hb, hs => by
    simp only [BExpr.compilable, Bool.and_eq_true] at hc
    simp only [BExpr.envBound, Bool.and_eq_true] at hb
    rcases hE₁ : compileU (w := 64) L x next with ⟨cx, rx, n₁⟩
    rcases hE₂ : compileU (w := 64) L y n₁ with ⟨cy, ry, n₂⟩
    simp only [compileB, hE₁, hE₂, BExpr.eval]
    have hΓ : Γ.length ≤ L := Nat.le_trans (Nat.le_of_eq hL.1) hs.2.1
    exact binop_sim p envArr hs hE₁ hE₂ (compileU_bounds L hΓ x next hc.1)
      (compileU_bounds L hΓ y n₁ hc.2)
      (compileU_sim Γ locals idx L hL x next s hc.1 hb.1 hs)
      (fun s₁ hs₁ => compileU_sim Γ locals idx L hL y n₁ s₁ hc.2 hb.2 hs₁)
      (encB_ueq _ _)
  | .lt x y, next, s, hc, hb, hs => by
    simp only [BExpr.compilable, Bool.and_eq_true] at hc
    simp only [BExpr.envBound, Bool.and_eq_true] at hb
    rcases hE₁ : compileU (w := 64) L x next with ⟨cx, rx, n₁⟩
    rcases hE₂ : compileU (w := 64) L y n₁ with ⟨cy, ry, n₂⟩
    simp only [compileB, hE₁, hE₂, BExpr.eval]
    have hΓ : Γ.length ≤ L := Nat.le_trans (Nat.le_of_eq hL.1) hs.2.1
    exact binop_sim p envArr hs hE₁ hE₂ (compileU_bounds L hΓ x next hc.1)
      (compileU_bounds L hΓ y n₁ hc.2)
      (compileU_sim Γ locals idx L hL x next s hc.1 hb.1 hs)
      (fun s₁ hs₁ => compileU_sim Γ locals idx L hL y n₁ s₁ hc.2 hb.2 hs₁)
      (encB_ult _ _)
  | .flt x y, next, s, hc, hb, hs => by
    simp only [BExpr.compilable, Bool.and_eq_true] at hc
    simp only [BExpr.envBound, Bool.and_eq_true] at hb
    rcases hE₁ : compileF (w := 64) L x next with ⟨cx, rx, n₁⟩
    rcases hE₂ : compileF (w := 64) L y n₁ with ⟨cy, ry, n₂⟩
    simp only [compileB, hE₁, hE₂, BExpr.eval, FiniteField.val_F]
    have hΓ : Γ.length ≤ L := Nat.le_trans (Nat.le_of_eq hL.1) hs.2.1
    exact binop_sim p envArr hs hE₁ hE₂ (compileF_bounds L hΓ x next hc.1)
      (compileF_bounds L hΓ y n₁ hc.2)
      (compileF_sim Γ locals idx L hL x next s hc.1 hb.1 hs)
      (fun s₁ hs₁ => compileF_sim Γ locals idx L hL y n₁ s₁ hc.2 hb.2 hs₁)
      (encB_flt hpw _ _)
  | .bit x i, next, s, hc, hb, hs => by
    simp only [BExpr.compilable, Bool.and_eq_true, decide_eq_true_eq] at hc
    rcases hE₁ : compileF (w := 64) L x next with ⟨cx, rx, n₁⟩
    have hbd₁ := compileF_bounds L (Nat.le_trans (Nat.le_of_eq hL.1) hs.2.1) x next
      hc.1 hs.2.2.1
    simp only [hE₁] at hbd₁
    obtain ⟨s₁, t₁, d₁, p₁, hex₁, hr₁, hp₁, hbf₁, hcp₁⟩ :=
      compileF_sim Γ locals idx L hL x next s hc.1 hb hs
    simp only [hE₁] at hex₁ hr₁
    simp only [compileB, hE₁, BExpr.eval, FiniteField.val_F]
    refine ⟨_, _, _, _, .seq hex₁ (.seq .imm (.seq .bin (.seq .imm .bin))),
      ?_, ?_, ?_, ?_⟩
    · simp only [regs_setReg_self, BinOp.eval,
        regs_setReg_ne _ _ (show Ne (α := ℕ) (n₁ + 1) (n₁ + 2) by omega),
        regs_setReg_ne _ _ (show Ne (α := ℕ) rx n₁ by omega), hr₁]
      exact encF_testBit hpw _ hc.2
    · intro q hq
      rw [regs_setReg_ne _ _ (show q ≠ n₁ + 3 by omega),
        regs_setReg_ne _ _ (show q ≠ n₁ + 2 by omega),
        regs_setReg_ne _ _ (show q ≠ n₁ + 1 by omega),
        regs_setReg_ne _ _ (show q ≠ n₁ by omega), hp₁ q hq]
    · rw [bufs_setReg, bufs_setReg, bufs_setReg, bufs_setReg, hbf₁]
    · rw [caps_setReg, caps_setReg, caps_setReg, caps_setReg, hcp₁]
  | .not b, next, s, hc, hb, hs => by
    rcases hE₁ : compileB (w := 64) L b next with ⟨cb, rb, n₁⟩
    have hbd₁ := compileB_bounds L (Nat.le_trans (Nat.le_of_eq hL.1) hs.2.1) b next
      hc hs.2.2.1
    simp only [hE₁] at hbd₁
    obtain ⟨s₁, t₁, d₁, p₁, hex₁, hr₁, hp₁, hbf₁, hcp₁⟩ :=
      compileB_sim Γ locals idx L hL b next s hc hb hs
    simp only [hE₁] at hex₁ hr₁
    simp only [compileB, hE₁, BExpr.eval]
    refine ⟨_, _, _, _, .seq hex₁ .un, ?_, ?_, ?_, ?_⟩
    · rw [regs_setReg_self, hr₁]
      simp only [UnOp.eval]
      exact encB_not _
    · intro q hq
      rw [regs_setReg_ne _ _ (show q ≠ n₁ by omega), hp₁ q hq]
    · rw [bufs_setReg, hbf₁]
    · rw [caps_setReg, hcp₁]
  | .and x y, next, s, hc, hb, hs => by
    simp only [BExpr.compilable, Bool.and_eq_true] at hc
    simp only [BExpr.envBound, Bool.and_eq_true] at hb
    rcases hE₁ : compileB (w := 64) L x next with ⟨cx, rx, n₁⟩
    rcases hE₂ : compileB (w := 64) L y n₁ with ⟨cy, ry, n₂⟩
    simp only [compileB, hE₁, hE₂, BExpr.eval]
    have hΓ : Γ.length ≤ L := Nat.le_trans (Nat.le_of_eq hL.1) hs.2.1
    exact binop_sim p envArr hs hE₁ hE₂ (compileB_bounds L hΓ x next hc.1)
      (compileB_bounds L hΓ y n₁ hc.2)
      (compileB_sim Γ locals idx L hL x next s hc.1 hb.1 hs)
      (fun s₁ hs₁ => compileB_sim Γ locals idx L hL y n₁ s₁ hc.2 hb.2 hs₁)
      (encB_and _ _)

end

end Sim

end Caliper.WitgenCompile
