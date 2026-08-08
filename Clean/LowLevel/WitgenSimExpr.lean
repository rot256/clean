import Clean.LowLevel.WitgenSim

/-!
# Scalar-expression simulation for the witgen compiler

Phase 3b of the witgen compiler correctness proof: the **scalar compiler induction**.
For every compilable, environment-bounded scalar expression of the witness IR
(`Expression`, `FExpr`, `U64Expr`, `BExpr`), the code emitted by
`Clean/LowLevel/WitgenCompile.lean` executes from any state satisfying the
state-encoding invariant (`StateEnc`, resp. an environment buffer for `Expression`),
terminates, leaves the encoded value of the reference evaluation
(`Clean/Circuit/WitnessIR.lean`) in the compiler's result register, and preserves all
registers below the free-register counter `next` as well as all buffers and
capacities.

The theorems are `compileExpr_sim` (standalone — circuit expressions are a separate
AST) and the mutual `compileF_sim` / `compileU_sim` / `compileB_sim`, by structural
induction mirroring the mutual compilers `compileF` / `compileU` / `compileB`. The
field-arithmetic leaf gadgets (`fieldOp`, `selectCode`, `invLadder`) are handled by
the `Exec`-level leaf lemmas of `Clean/LowLevel/WitgenSim.lean`; this file contains
the induction glue and the word-level facts for the remaining instructions.

Everything is at the compiler's design point: word size `w = 64`, `F = F p` for a
prime `p` with `2 < p` and `p * p ≤ 2 ^ 64`. The environment is encoded in buffer `0`
(`EnvEnc`); its length `N` must satisfy `N ≤ 2 ^ 64` so that the static `bufGet`
indices baked as 64-bit immediates read back exactly (`Expression.envBound` bounds
every environment read by `N`, and the immediate wraps mod `2 ^ 64`).
-/

namespace LowLevel.WitgenCompile

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

/-- The `eq`-comparison of bit-pattern words decides u64 equality. -/
private theorem encB_ueq (x y : UInt64) :
    (if encU x = encU y then 1 else 0 : Word 64) = encB (decide (x = y)) := by
  by_cases h : x = y
  · simp [h, encB]
  · rw [if_neg fun he => h (encU_injective he)]
    simp [h, encB]

/-- The `ult`-comparison of bit-pattern words decides u64 `<`. -/
private theorem encB_ult (x y : UInt64) :
    (if (encU x).toNat < (encU y).toNat then 1 else 0 : Word 64) =
      encB (decide (x < y)) := by
  rw [encU_toNat, encU_toNat]
  by_cases h : x < y
  · rw [if_pos (UInt64.lt_iff_toNat_lt.mp h)]
    simp [h, encB]
  · rw [if_neg fun hlt => h (UInt64.lt_iff_toNat_lt.mpr hlt)]
    simp [h, encB]

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

/-- The `eq`-comparison of canonical words decides field equality. -/
private theorem encB_feq (hpw : p * p ≤ 2 ^ 64) (x y : F p) :
    (if encF x = encF y then 1 else 0 : Word 64) = encB (decide (x = y)) := by
  by_cases h : x = y
  · simp [h, encB]
  · rw [if_neg fun he => h (encF_injective hpw he)]
    simp [h, encB]

/-- The `ult`-comparison of canonical words decides the field-value `<`. -/
private theorem encB_flt (hpw : p * p ≤ 2 ^ 64) (x y : F p) :
    (if (encF x).toNat < (encF y).toNat then 1 else 0 : Word 64) =
      encB (decide (ZMod.val x < ZMod.val y)) := by
  rw [encF_toNat hpw, encF_toNat hpw]
  by_cases h : ZMod.val x < ZMod.val y <;> simp [h, encB]

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

The scalar compilers thread `next` monotonically and allocate the result register
below the returned counter: `next ≤ next'` and `resultReg < next'`. These purely
syntactic facts justify the operand-survival steps of the simulation proofs.

All register inequalities here (and in the simulation theorems below) are stated
over bare `ℕ`, not the `Reg` abbrev: `omega` does not unfold `Reg`, so a hypothesis
whose relation is elaborated at type `Reg` is invisible to it. -/

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

/-- `compileF` register bounds: `next ≤ next'` and `resultReg < next'`. -/
theorem compileF_bounds {F : Type} [FiniteField F] (L : ℕ) :
    ∀ (e : FExpr F) (next : ℕ),
    next ≤ (compileF (w := 64) L e next).2.2 ∧
      LT.lt (α := ℕ) (compileF (w := 64) L e next).2.1 (compileF (w := 64) L e next).2.2
  | .expr e, next => compileExpr_bounds e next
  | .const _, next => ⟨Nat.le_succ next, Nat.lt_succ_self next⟩
  | .localVar _, next => ⟨Nat.le_succ next, Nat.lt_succ_self next⟩
  | .add x y, next =>
    have h₁ := compileF_bounds L x next
    have h₂ := compileF_bounds L y (compileF (w := 64) L x next).2.2
    ⟨Nat.le_trans h₁.1 (Nat.le_trans h₂.1 (Nat.le_add_right _ 2)), Nat.lt_succ_self _⟩
  | .mul x y, next =>
    have h₁ := compileF_bounds L x next
    have h₂ := compileF_bounds L y (compileF (w := 64) L x next).2.2
    ⟨Nat.le_trans h₁.1 (Nat.le_trans h₂.1 (Nat.le_add_right _ 2)), Nat.lt_succ_self _⟩
  | .inv x, next =>
    have h₁ := compileF_bounds L x next
    ⟨Nat.le_trans h₁.1 (Nat.le_add_right _ 2), Nat.lt_succ_self _⟩
  | .ofU64 n, next =>
    have h₁ := compileU_bounds L n next
    ⟨Nat.le_trans h₁.1 (Nat.le_add_right _ 2), Nat.lt_succ_self _⟩
  | .ite c t e, next =>
    have h₁ := compileB_bounds L c next
    have h₂ := compileF_bounds L t (compileB (w := 64) L c next).2.2
    have h₃ := compileF_bounds L e
      (compileF (w := 64) L t (compileB (w := 64) L c next).2.2).2.2
    ⟨Nat.le_trans h₁.1 (Nat.le_trans h₂.1 (Nat.le_trans h₃.1 (Nat.le_add_right _ 5))),
      Nat.lt_succ_self _⟩
  | .listGet .., next => ⟨Nat.le_succ next, Nat.lt_succ_self next⟩
  | .dataGet .., next => ⟨Nat.le_succ next, Nat.lt_succ_self next⟩
  | .hintGet .., next => ⟨Nat.le_succ next, Nat.lt_succ_self next⟩

/-- `compileU` register bounds: `next ≤ next'` and `resultReg < next'`. -/
theorem compileU_bounds {F : Type} [FiniteField F] (L : ℕ) :
    ∀ (e : U64Expr F) (next : ℕ),
    next ≤ (compileU (w := 64) L e next).2.2 ∧
      LT.lt (α := ℕ) (compileU (w := 64) L e next).2.1 (compileU (w := 64) L e next).2.2
  | .const _, next => ⟨Nat.le_succ next, Nat.lt_succ_self next⟩
  | .val x, next =>
    have h₁ := compileF_bounds L x next
    ⟨Nat.le_trans h₁.1 (Nat.le_succ _), Nat.lt_succ_self _⟩
  | .idx, next => ⟨Nat.le_succ next, Nat.lt_succ_self next⟩
  | .localVar _, next => ⟨Nat.le_succ next, Nat.lt_succ_self next⟩
  | .add x y, next =>
    have h₁ := compileU_bounds L x next
    have h₂ := compileU_bounds L y (compileU (w := 64) L x next).2.2
    ⟨Nat.le_trans h₁.1 (Nat.le_trans h₂.1 (Nat.le_succ _)), Nat.lt_succ_self _⟩
  | .mul x y, next =>
    have h₁ := compileU_bounds L x next
    have h₂ := compileU_bounds L y (compileU (w := 64) L x next).2.2
    ⟨Nat.le_trans h₁.1 (Nat.le_trans h₂.1 (Nat.le_succ _)), Nat.lt_succ_self _⟩
  | .div x y, next =>
    have h₁ := compileU_bounds L x next
    have h₂ := compileU_bounds L y (compileU (w := 64) L x next).2.2
    ⟨Nat.le_trans h₁.1 (Nat.le_trans h₂.1 (Nat.le_succ _)), Nat.lt_succ_self _⟩
  | .mod x y, next =>
    have h₁ := compileU_bounds L x next
    have h₂ := compileU_bounds L y (compileU (w := 64) L x next).2.2
    ⟨Nat.le_trans h₁.1 (Nat.le_trans h₂.1 (Nat.le_succ _)), Nat.lt_succ_self _⟩
  | .land x y, next =>
    have h₁ := compileU_bounds L x next
    have h₂ := compileU_bounds L y (compileU (w := 64) L x next).2.2
    ⟨Nat.le_trans h₁.1 (Nat.le_trans h₂.1 (Nat.le_succ _)), Nat.lt_succ_self _⟩
  | .lor x y, next =>
    have h₁ := compileU_bounds L x next
    have h₂ := compileU_bounds L y (compileU (w := 64) L x next).2.2
    ⟨Nat.le_trans h₁.1 (Nat.le_trans h₂.1 (Nat.le_succ _)), Nat.lt_succ_self _⟩
  | .lxor x y, next =>
    have h₁ := compileU_bounds L x next
    have h₂ := compileU_bounds L y (compileU (w := 64) L x next).2.2
    ⟨Nat.le_trans h₁.1 (Nat.le_trans h₂.1 (Nat.le_succ _)), Nat.lt_succ_self _⟩
  | .shiftL x y, next =>
    have h₁ := compileU_bounds L x next
    have h₂ := compileU_bounds L y (compileU (w := 64) L x next).2.2
    ⟨Nat.le_trans h₁.1 (Nat.le_trans h₂.1 (Nat.le_add_right _ 3)), Nat.lt_succ_self _⟩
  | .shiftR x y, next =>
    have h₁ := compileU_bounds L x next
    have h₂ := compileU_bounds L y (compileU (w := 64) L x next).2.2
    ⟨Nat.le_trans h₁.1 (Nat.le_trans h₂.1 (Nat.le_add_right _ 3)), Nat.lt_succ_self _⟩
  | .ite c t e, next =>
    have h₁ := compileB_bounds L c next
    have h₂ := compileU_bounds L t (compileB (w := 64) L c next).2.2
    have h₃ := compileU_bounds L e
      (compileU (w := 64) L t (compileB (w := 64) L c next).2.2).2.2
    ⟨Nat.le_trans h₁.1 (Nat.le_trans h₂.1 (Nat.le_trans h₃.1 (Nat.le_add_right _ 5))),
      Nat.lt_succ_self _⟩

/-- `compileB` register bounds: `next ≤ next'` and `resultReg < next'`. -/
theorem compileB_bounds {F : Type} [FiniteField F] (L : ℕ) :
    ∀ (e : BExpr F) (next : ℕ),
    next ≤ (compileB (w := 64) L e next).2.2 ∧
      LT.lt (α := ℕ) (compileB (w := 64) L e next).2.1 (compileB (w := 64) L e next).2.2
  | .true, next => ⟨Nat.le_succ next, Nat.lt_succ_self next⟩
  | .false, next => ⟨Nat.le_succ next, Nat.lt_succ_self next⟩
  | .feq x y, next =>
    have h₁ := compileF_bounds L x next
    have h₂ := compileF_bounds L y (compileF (w := 64) L x next).2.2
    ⟨Nat.le_trans h₁.1 (Nat.le_trans h₂.1 (Nat.le_succ _)), Nat.lt_succ_self _⟩
  | .neq x y, next =>
    have h₁ := compileU_bounds L x next
    have h₂ := compileU_bounds L y (compileU (w := 64) L x next).2.2
    ⟨Nat.le_trans h₁.1 (Nat.le_trans h₂.1 (Nat.le_succ _)), Nat.lt_succ_self _⟩
  | .lt x y, next =>
    have h₁ := compileU_bounds L x next
    have h₂ := compileU_bounds L y (compileU (w := 64) L x next).2.2
    ⟨Nat.le_trans h₁.1 (Nat.le_trans h₂.1 (Nat.le_succ _)), Nat.lt_succ_self _⟩
  | .flt x y, next =>
    have h₁ := compileF_bounds L x next
    have h₂ := compileF_bounds L y (compileF (w := 64) L x next).2.2
    ⟨Nat.le_trans h₁.1 (Nat.le_trans h₂.1 (Nat.le_succ _)), Nat.lt_succ_self _⟩
  | .bit x _, next =>
    have h₁ := compileF_bounds L x next
    ⟨Nat.le_trans h₁.1 (Nat.le_add_right _ 4), Nat.lt_succ_self _⟩
  | .not b, next =>
    have h₁ := compileB_bounds L b next
    ⟨Nat.le_trans h₁.1 (Nat.le_succ _), Nat.lt_succ_self _⟩
  | .and x y, next =>
    have h₁ := compileB_bounds L x next
    have h₂ := compileB_bounds L y (compileB (w := 64) L x next).2.2
    ⟨Nat.le_trans h₁.1 (Nat.le_trans h₂.1 (Nat.le_succ _)), Nat.lt_succ_self _⟩

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

include hpw henv hN

/-- **Simulation for circuit expressions**: the code `compileExpr` emits for an
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
    refine ⟨_, _, _, _, .seq .imm (.bufGet hlt), ?_, ?_, rfl, rfl⟩
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

end Sim

end LowLevel.WitgenCompile
