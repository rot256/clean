import Clean.Caliper.MultiLimbSim

/-!
# Register bounds of the multi-limb compilers

The multi-limb compilers thread `next` monotonically. A field-sorted node returns a
`k`-register block ending at or below `next'`; a u64-sorted node or a condition returns
a single register below `next'`. As in the single-word compiler the result bound is not
purely syntactic — the copy-eliding arms return a local block or the index register,
both *below* `next` — so it needs the expression compilable against `Γ`,
`Γ.length ≤ L`, and `tmpBase k L ≤ next`.

These are what justify the operand-survival steps of the simulation: a child's result
block sits below its sibling's base, and every gadget preserves the registers below its
own frame.

Register inequalities are stated over bare `ℕ`, and proved by composing `Nat` lemmas
rather than by `omega`: the compilers return `Reg`-typed components, which `omega` does
not see through.
-/

namespace Caliper.MultiLimb

open Caliper Caliper.Limbs Caliper.WitgenCompile Witgen

section Generic

variable {F : Type} [FiniteField F]

/-! ## Arithmetic of the frames

One lemma per gadget, saying its result block fits inside the frame it was given. -/

theorem le_add_of_le {a b c : ℕ} (h : a ≤ b) : a ≤ b + c :=
  Nat.le_trans h (Nat.le_add_right _ _)

theorem montAddOut_le (k n : ℕ) : montAddOut k n + k ≤ n + montAddFrame k := by
  simp only [montAddOut, montAddFrame]; omega

theorem montOut_le (k n : ℕ) : montOut k n + k ≤ n + montFrame k := by
  simp only [montOut, montFrame]; omega

theorem montMulConstOut_le (k n : ℕ) :
    montMulConstOut k n + k ≤ n + montMulConstFrame k := by
  simp only [montMulConstOut, montMulConstFrame, montOut, montFrame]; omega

theorem montMulConstOut_lt (k n : ℕ) (hk : 0 < k) :
    LT.lt (α := ℕ) (montMulConstOut k n) (n + montMulConstFrame k) := by
  simp only [montMulConstOut, montMulConstFrame, montOut, montFrame]; omega

theorem eqOut_lt (n : ℕ) : LT.lt (α := ℕ) (eqOut n) (n + eqFrame) := by
  simp only [eqOut, eqFrame]; omega

theorem ltOut_lt (k n : ℕ) : LT.lt (α := ℕ) (ltOut k n) (n + ltFrame k) := by
  simp only [ltOut, ltFrame]; omega

theorem bitOut_lt (n : ℕ) : LT.lt (α := ℕ) (bitOut n) (n + bitFrame) := by
  simp only [bitOut, bitFrame]; omega

theorem localReg_le {k i L : ℕ} (h : i < L) : localReg k i + k ≤ tmpBase k L := by
  simp only [localReg, tmpBase]
  have hm : (i + 1) * k ≤ L * k := Nat.mul_le_mul_right k (by omega)
  have he : k + 2 + i * k + k = k + 2 + (i + 1) * k := by ring
  omega

theorem localReg_lt {k i L : ℕ} (h : i ≤ L) :
    LT.lt (α := ℕ) (localReg k i) (tmpBase k L) := by
  simp only [localReg, tmpBase]
  have hm : i * k ≤ L * k := Nat.mul_le_mul_right k h
  omega

theorem idxReg_lt (k L : ℕ) : LT.lt (α := ℕ) (idxReg k L) (tmpBase k L) := by
  simp only [idxReg, tmpBase]; omega

/-- A compilable local reference names a step of the context. -/
theorem lt_length_of_getElem?_fld {Γ : List VSort} {i : ℕ} {v : VSort}
    (hc : Γ[i]? = some v) : i < Γ.length := by
  by_contra hge
  rw [List.getElem?_eq_none (by omega)] at hc
  exact absurd hc (by simp)

/-! ## Bounds -/

/-- `compileExprML` register bounds: the result block ends exactly at `next'`. -/
theorem compileExprML_bounds (k pReg pinv : ℕ) :
    ∀ (e : Expression F) (next : ℕ),
      next ≤ (compileExprML k pReg pinv e next).2.2 ∧
        (compileExprML k pReg pinv e next).2.1 + k
          ≤ (compileExprML k pReg pinv e next).2.2
  | .var _, next => ⟨le_add_of_le (le_add_of_le (Nat.le_refl next)), Nat.le_refl _⟩
  | .const _, _ => ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
  | .add x y, next =>
    have h₁ := compileExprML_bounds k pReg pinv x next
    have h₂ := compileExprML_bounds k pReg pinv y
      (compileExprML k pReg pinv x next).2.2
    ⟨le_add_of_le (Nat.le_trans h₁.1 h₂.1), montAddOut_le k _⟩
  | .mul x y, next =>
    have h₁ := compileExprML_bounds k pReg pinv x next
    have h₂ := compileExprML_bounds k pReg pinv y
      (compileExprML k pReg pinv x next).2.2
    ⟨le_add_of_le (Nat.le_trans h₁.1 h₂.1), montOut_le k _⟩

mutual

/-- `compileFML` register bounds. -/
theorem compileFML_bounds {Γ : List VSort} (k L : ℕ) (hk : 0 < k) (hΓ : Γ.length ≤ L) :
    ∀ (e : FExpr F) (next : ℕ), FExpr.compilable Γ e = true →
      LE.le (α := ℕ) (tmpBase k L) next →
      next ≤ (compileFML k L e next).2.2 ∧
        (compileFML k L e next).2.1 + k ≤ (compileFML k L e next).2.2
  | .expr e, next, _, _ => compileExprML_bounds k 0 (k + 1) e next
  | .const _, next, _, _ => ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
  | .localVar i, next, hc, hLn => by
    simp only [FExpr.compilable, beq_iff_eq] at hc
    exact ⟨Nat.le_refl next,
      Nat.le_trans (localReg_le (Nat.lt_of_lt_of_le
        (lt_length_of_getElem?_fld hc) hΓ)) hLn⟩
  | .add x y, next, hc, hLn => by
    simp only [FExpr.compilable, Bool.and_eq_true] at hc
    have h₁ := compileFML_bounds k L hk hΓ x next hc.1 hLn
    have h₂ := compileFML_bounds k L hk hΓ y (compileFML k L x next).2.2 hc.2
      (Nat.le_trans hLn h₁.1)
    exact ⟨le_add_of_le (Nat.le_trans h₁.1 h₂.1), montAddOut_le k _⟩
  | .mul x y, next, hc, hLn => by
    simp only [FExpr.compilable, Bool.and_eq_true] at hc
    have h₁ := compileFML_bounds k L hk hΓ x next hc.1 hLn
    have h₂ := compileFML_bounds k L hk hΓ y (compileFML k L x next).2.2 hc.2
      (Nat.le_trans hLn h₁.1)
    exact ⟨le_add_of_le (Nat.le_trans h₁.1 h₂.1), montOut_le k _⟩
  | .inv x, next, hc, hLn =>
    have h₁ := compileFML_bounds k L hk hΓ x next hc hLn
    ⟨le_add_of_le (le_add_of_le (le_add_of_le h₁.1)), montMulConstOut_le k _⟩
  | .ofU64 n, next, hc, hLn =>
    have h₁ := compileUML_bounds k L hk hΓ n next hc hLn
    ⟨le_add_of_le (le_add_of_le h₁.1), montMulConstOut_le k _⟩
  | .ite c t e, next, hc, hLn => by
    simp only [FExpr.compilable, Bool.and_eq_true] at hc
    have h₁ := compileBML_bounds k L hk hΓ c next hc.1.1 hLn
    have h₂ := compileFML_bounds k L hk hΓ t (compileBML k L c next).2.2 hc.1.2
      (Nat.le_trans hLn h₁.1)
    have h₃ := compileFML_bounds k L hk hΓ e
      (compileFML k L t (compileBML k L c next).2.2).2.2 hc.2
      (Nat.le_trans hLn (Nat.le_trans h₁.1 h₂.1))
    exact ⟨le_add_of_le (le_add_of_le
      (Nat.le_trans h₁.1 (Nat.le_trans h₂.1 h₃.1))), Nat.le_refl _⟩
  | .listGet .., next, _, _ => ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
  | .dataGet .., next, _, _ => ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
  | .hintGet .., next, _, _ => ⟨Nat.le_add_right _ _, Nat.le_refl _⟩

/-- `compileUML` register bounds. -/
theorem compileUML_bounds {Γ : List VSort} (k L : ℕ) (hk : 0 < k) (hΓ : Γ.length ≤ L) :
    ∀ (e : U64Expr F) (next : ℕ), U64Expr.compilable Γ e = true →
      LE.le (α := ℕ) (tmpBase k L) next →
      next ≤ (compileUML k L e next).2.2 ∧
        LT.lt (α := ℕ) (compileUML k L e next).2.1 (compileUML k L e next).2.2
  | .const _, next, _, _ => ⟨Nat.le_succ _, Nat.lt_succ_self _⟩
  | .val x, next, hc, hLn =>
    have h₁ := compileFML_bounds k L hk hΓ x next hc hLn
    ⟨le_add_of_le h₁.1, montMulConstOut_lt k _ hk⟩
  | .idx, next, _, hLn =>
    ⟨Nat.le_refl next, Nat.lt_of_lt_of_le (idxReg_lt k L) hLn⟩
  | .localVar i, next, hc, hLn => by
    simp only [U64Expr.compilable, beq_iff_eq] at hc
    exact ⟨Nat.le_refl next,
      Nat.lt_of_lt_of_le (localReg_lt (Nat.le_of_lt (Nat.lt_of_lt_of_le
        (lt_length_of_getElem?_fld hc) hΓ))) hLn⟩
  | .add x y, next, hc, hLn
  | .mul x y, next, hc, hLn
  | .div x y, next, hc, hLn
  | .mod x y, next, hc, hLn
  | .land x y, next, hc, hLn
  | .lor x y, next, hc, hLn
  | .lxor x y, next, hc, hLn => by
    simp only [U64Expr.compilable, Bool.and_eq_true] at hc
    have h₁ := compileUML_bounds k L hk hΓ x next hc.1 hLn
    have h₂ := compileUML_bounds k L hk hΓ y (compileUML k L x next).2.2 hc.2
      (Nat.le_trans hLn h₁.1)
    exact ⟨Nat.le_trans (Nat.le_trans h₁.1 h₂.1) (Nat.le_succ _), Nat.lt_succ_self _⟩
  | .shiftL x y, next, hc, hLn
  | .shiftR x y, next, hc, hLn => by
    simp only [U64Expr.compilable, Bool.and_eq_true] at hc
    have h₁ := compileUML_bounds k L hk hΓ x next hc.1 hLn
    have h₂ := compileUML_bounds k L hk hΓ y (compileUML k L x next).2.2 hc.2
      (Nat.le_trans hLn h₁.1)
    exact ⟨Nat.le_trans (Nat.le_trans h₁.1 h₂.1) (Nat.le_add_right _ 3),
      Nat.lt_succ_self _⟩
  | .ite c t e, next, hc, hLn => by
    simp only [U64Expr.compilable, Bool.and_eq_true] at hc
    have h₁ := compileBML_bounds k L hk hΓ c next hc.1.1 hLn
    have h₂ := compileUML_bounds k L hk hΓ t (compileBML k L c next).2.2 hc.1.2
      (Nat.le_trans hLn h₁.1)
    have h₃ := compileUML_bounds k L hk hΓ e
      (compileUML k L t (compileBML k L c next).2.2).2.2 hc.2
      (Nat.le_trans hLn (Nat.le_trans h₁.1 h₂.1))
    exact ⟨Nat.le_trans (Nat.le_trans h₁.1 (Nat.le_trans h₂.1 h₃.1))
      (Nat.le_add_right _ 2), Nat.lt_succ_self _⟩

/-- `compileBML` register bounds. -/
theorem compileBML_bounds {Γ : List VSort} (k L : ℕ) (hk : 0 < k) (hΓ : Γ.length ≤ L) :
    ∀ (e : BExpr F) (next : ℕ), BExpr.compilable Γ e = true →
      LE.le (α := ℕ) (tmpBase k L) next →
      next ≤ (compileBML k L e next).2.2 ∧
        LT.lt (α := ℕ) (compileBML k L e next).2.1 (compileBML k L e next).2.2
  | .true, next, _, _ => ⟨Nat.le_succ _, Nat.lt_succ_self _⟩
  | .false, next, _, _ => ⟨Nat.le_succ _, Nat.lt_succ_self _⟩
  | .feq x y, next, hc, hLn => by
    simp only [BExpr.compilable, Bool.and_eq_true] at hc
    have h₁ := compileFML_bounds k L hk hΓ x next hc.1 hLn
    have h₂ := compileFML_bounds k L hk hΓ y (compileFML k L x next).2.2 hc.2
      (Nat.le_trans hLn h₁.1)
    exact ⟨le_add_of_le (Nat.le_trans h₁.1 h₂.1), eqOut_lt _⟩
  | .neq x y, next, hc, hLn
  | .lt x y, next, hc, hLn => by
    simp only [BExpr.compilable, Bool.and_eq_true] at hc
    have h₁ := compileUML_bounds k L hk hΓ x next hc.1 hLn
    have h₂ := compileUML_bounds k L hk hΓ y (compileUML k L x next).2.2 hc.2
      (Nat.le_trans hLn h₁.1)
    exact ⟨Nat.le_trans (Nat.le_trans h₁.1 h₂.1) (Nat.le_succ _), Nat.lt_succ_self _⟩
  | .flt x y, next, hc, hLn => by
    simp only [BExpr.compilable, Bool.and_eq_true] at hc
    have h₁ := compileFML_bounds k L hk hΓ x next hc.1 hLn
    have h₂ := compileFML_bounds k L hk hΓ y (compileFML k L x next).2.2 hc.2
      (Nat.le_trans hLn h₁.1)
    exact ⟨le_add_of_le (le_add_of_le (le_add_of_le (Nat.le_trans h₁.1 h₂.1))),
      ltOut_lt k _⟩
  | .bit x i, next, hc, hLn => by
    simp only [BExpr.compilable, Bool.and_eq_true] at hc
    have h₁ := compileFML_bounds k L hk hΓ x next hc.1 hLn
    exact ⟨le_add_of_le (le_add_of_le h₁.1), bitOut_lt _⟩
  | .not b, next, hc, hLn =>
    have h₁ := compileBML_bounds k L hk hΓ b next hc hLn
    ⟨Nat.le_trans h₁.1 (Nat.le_succ _), Nat.lt_succ_self _⟩
  | .and x y, next, hc, hLn => by
    simp only [BExpr.compilable, Bool.and_eq_true] at hc
    have h₁ := compileBML_bounds k L hk hΓ x next hc.1 hLn
    have h₂ := compileBML_bounds k L hk hΓ y (compileBML k L x next).2.2 hc.2
      (Nat.le_trans hLn h₁.1)
    exact ⟨Nat.le_trans (Nat.le_trans h₁.1 h₂.1) (Nat.le_succ _), Nat.lt_succ_self _⟩

end

end Generic

/-! ## The state encoding -/

section Enc

variable {p : ℕ} [Fact p.Prime]

/-- The generation-time facts about the modulus that the lowering's proofs need — the
`fieldOkML` checks, in propositional form. -/
structure FieldOkML (p pv k : ℕ) : Prop where
  two_lt : 2 < p
  limbs_pos : 0 < k
  bound : p < 2 ^ (64 * k)
  const : (p * pv + 1) % 2 ^ 64 = 0
  budget : 128 * k < 2 ^ 64

/-- The environment buffer holds `k` words per element, in Montgomery form: element
`j`'s limbs occupy words `j*k .. j*k + k - 1`. -/
def EnvEncML (k : ℕ) (env : ProverEnvironment (F p)) (N : ℕ)
    (arr : Array (Word 64)) : Prop :=
  arr.size = N * k ∧
    ∀ j, j < N → ∀ i, i < k →
      arr[j * k + i]! = BitVec.ofNat 64 (limb 64 (montVal k (env.get j)) i)

/-- What a scalar local holds: a field local is a `k`-limb Montgomery block, a u64
local a single word in the first register of its block. -/
def LocalEncML (k : ℕ) (s : State 64) (r : ℕ) : F p ⊕ UInt64 → Prop
  | .inl x => RegsEnc s r k (montVal k x)
  | .inr n => s.regs r = Caliper.WitgenCompile.encU n

/-- The machine state encodes the reference evaluation context: buffer `0` is the
environment, the modulus and the Montgomery constant are in place, the local blocks
hold the reference locals, the index register holds the `mapRange` index, and
temporaries live at `≥ next ≥ tmpBase k L`. -/
structure StateEncML (k pv L : ℕ) (envArr : Array (Word 64))
    (locals : Array (F p ⊕ UInt64)) (idx next : ℕ) (s : State 64) : Prop where
  env : s.bufs 0 = envArr
  size : locals.size ≤ L
  frame : LE.le (α := ℕ) (tmpBase k L) next
  pre : PreludeEnc p pv k s
  loc : ∀ i, (h : i < locals.size) → LocalEncML k s (localReg k i) locals[i]
  index : s.regs (idxReg k L) = BitVec.ofNat 64 idx

omit [Fact p.Prime] in
/-- `StateEncML` survives raising the temporary bound and running code that preserves
the registers below the old bound and buffer `0`. This is the threading step of the
compiler induction. -/
theorem StateEncML_mono {k pv L : ℕ} {envArr : Array (Word 64)}
    {locals : Array (F p ⊕ UInt64)} {idx next next' : ℕ} {s s' : State 64}
    (hs : StateEncML k pv L envArr locals idx next s)
    (hle : LE.le (α := ℕ) next next')
    (hpres : ∀ q, q < next → s'.regs q = s.regs q) (hbufs : s'.bufs 0 = s.bufs 0) :
    StateEncML k pv L envArr locals idx next' s' := by
  obtain ⟨henv, hsz, hfr, hpre, hloc, hidx⟩ := hs
  have hfr' : k + 3 + L * k ≤ next := by simpa only [tmpBase] using hfr
  refine ⟨by rw [hbufs]; exact henv, hsz, Nat.le_trans hfr hle,
    ⟨fun j hj => by rw [hpres _ (by omega)]; exact hpre.modulus j hj,
      by rw [hpres _ (by omega)]; exact hpre.const⟩, fun i hi => ?_, ?_⟩
  · have hlt : localReg k i + k ≤ next :=
      Nat.le_trans (localReg_le (Nat.lt_of_lt_of_le hi hsz)) hfr
    have hlt' : k + 2 + i * k + k ≤ next := by simpa only [localReg] using hlt
    have := hloc i hi
    rcases hv : locals[i] with x | n
    · rw [hv] at this
      intro j hj
      rw [hpres _ (show localReg k i + j < next by simp only [localReg] at *; omega)]
      exact this j hj
    · rw [hv] at this
      show s'.regs (localReg k i) = Caliper.WitgenCompile.encU n
      rw [hpres _ (Nat.lt_of_lt_of_le
        (localReg_lt (Nat.le_of_lt (Nat.lt_of_lt_of_le hi hsz))) hfr)]
      exact this
  · rw [hpres _ (Nat.lt_of_lt_of_le (idxReg_lt k L) hfr)]; exact hidx

end Enc

end Caliper.MultiLimb
