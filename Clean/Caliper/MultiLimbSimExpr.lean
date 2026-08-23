import Clean.Caliper.MultiLimbSim
import Clean.Caliper.WitgenSimExpr

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
        LE.le (α := ℕ) ((compileExprML k pReg pinv e next).2.1 + k)
          (compileExprML k pReg pinv e next).2.2
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
        LE.le (α := ℕ) ((compileFML k L e next).2.1 + k) (compileFML k L e next).2.2
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

/-! ## Glue for the one-instruction u64 nodes -/

section Glue

variable {C : CostModel}

/-- Run two compiled subexpressions, then one `bin` on their result registers. -/
theorem binW_glue {op : BinOp} {c₁ c₂ : Stmt 64} {next n₁ n₂ rx ry : ℕ}
    (hrx : LT.lt (α := ℕ) rx n₁) (h₁₂ : n₁ ≤ n₂) (hn₁ : next ≤ n₁)
    {s s₁ s₂ : State 64} {t₁ t₂ : ℕ} {d₁ d₂ pp₁ pp₂ : ℤ} {v₁ v₂ w : Word 64}
    (hex₁ : Exec C c₁ s s₁ t₁ d₁ pp₁) (hex₂ : Exec C c₂ s₁ s₂ t₂ d₂ pp₂)
    (hv₁ : s₁.regs rx = v₁) (hv₂ : s₂.regs ry = v₂)
    (hop : BinOp.eval op v₁ v₂ = w)
    (hp₁ : ∀ q, q < next → s₁.regs q = s.regs q)
    (hp₂ : ∀ q, q < n₁ → s₂.regs q = s₁.regs q)
    (hb₁ : s₁.bufs = s.bufs) (hb₂ : s₂.bufs = s₁.bufs)
    (hc₁ : s₁.caps = s.caps) (hc₂ : s₂.caps = s₁.caps) :
    ∃ s' t d pp, Exec C (c₁ ;; c₂ ;; .bin op n₂ rx ry) s s' t d pp ∧
      s'.regs n₂ = w ∧
      (∀ q, q < next → s'.regs q = s.regs q) ∧
      s'.bufs = s.bufs ∧ s'.caps = s.caps := by
  refine ⟨_, _, _, _, .seq hex₁ (.seq hex₂ .bin), ?_, ?_, ?_, ?_⟩
  · rw [regs_setReg_self]
    show BinOp.eval op (s₂.regs rx) (s₂.regs ry) = w
    rw [hp₂ rx hrx, hv₁, hv₂]
    exact hop
  · intro q hq
    rw [regs_setReg_ne _ _ (show q ≠ n₂ by omega), hp₂ q (by omega), hp₁ q hq]
  · rw [bufs_setReg, hb₂, hb₁]
  · rw [caps_setReg, hc₂, hc₁]

/-- As `binW_glue`, for the two shift nodes: the amount is masked to six bits first. -/
theorem shiftW_glue {op : BinOp} {c₁ c₂ : Stmt 64} {next n₁ n₂ rx ry : ℕ}
    (hrx : LT.lt (α := ℕ) rx n₁) (h₁₂ : n₁ ≤ n₂) (hn₁ : next ≤ n₁)
    (hry : LT.lt (α := ℕ) ry n₂)
    {s s₁ s₂ : State 64} {t₁ t₂ : ℕ} {d₁ d₂ pp₁ pp₂ : ℤ} {v₁ v₂ w : Word 64}
    (hex₁ : Exec C c₁ s s₁ t₁ d₁ pp₁) (hex₂ : Exec C c₂ s₁ s₂ t₂ d₂ pp₂)
    (hv₁ : s₁.regs rx = v₁) (hv₂ : s₂.regs ry = v₂)
    (hop : BinOp.eval op v₁ (v₂ &&& BitVec.ofNat 64 63) = w)
    (hp₁ : ∀ q, q < next → s₁.regs q = s.regs q)
    (hp₂ : ∀ q, q < n₁ → s₂.regs q = s₁.regs q)
    (hb₁ : s₁.bufs = s.bufs) (hb₂ : s₂.bufs = s₁.bufs)
    (hc₁ : s₁.caps = s.caps) (hc₂ : s₂.caps = s₁.caps) :
    ∃ s' t d pp,
      Exec C (c₁ ;; c₂ ;; .imm n₂ (BitVec.ofNat 64 63) ;;
        .bin .and (n₂ + 1) ry n₂ ;; .bin op (n₂ + 2) rx (n₂ + 1)) s s' t d pp ∧
      s'.regs (n₂ + 2) = w ∧
      (∀ q, q < next → s'.regs q = s.regs q) ∧
      s'.bufs = s.bufs ∧ s'.caps = s.caps := by
  refine ⟨_, _, _, _,
    .seq hex₁ (.seq hex₂ (.seq .imm (.seq .bin .bin))), ?_, ?_, ?_, ?_⟩
  · rw [regs_setReg_self]
    show BinOp.eval op _ _ = w
    rw [regs_setReg_ne _ _ (show rx ≠ n₂ + 1 by omega),
      regs_setReg_ne _ _ (show rx ≠ n₂ by omega), hp₂ rx hrx, hv₁,
      regs_setReg_self]
    show BinOp.eval op v₁ (BinOp.eval .and _ _) = w
    rw [regs_setReg_ne _ _ (show ry ≠ n₂ by omega), hv₂, regs_setReg_self]
    exact hop
  · intro q hq
    rw [regs_setReg_ne _ _ (show q ≠ n₂ + 2 by omega),
      regs_setReg_ne _ _ (show q ≠ n₂ + 1 by omega),
      regs_setReg_ne _ _ (show q ≠ n₂ by omega), hp₂ q (by omega), hp₁ q hq]
  · rw [bufs_setReg, bufs_setReg, bufs_setReg, hb₂, hb₁]
  · rw [caps_setReg, caps_setReg, caps_setReg, hc₂, hc₁]

end Glue

/-! ## Circuit expressions -/

section Sim

variable {C : CostModel} {p : ℕ} [Fact p.Prime] {k pv : ℕ} (hf : FieldOkML p pv k)
variable (env : ProverEnvironment (F p)) (N : ℕ) (envArr : Array (Word 64))
variable (henv : EnvEncML k env N envArr) (hNk : N * k ≤ 2 ^ 64)

include hf henv hNk

/-- Simulation for circuit expressions: the code `compileExprML` emits for an
environment-bounded `Expression` runs from any state whose buffer `0` encodes the
environment and whose prelude registers are in place, leaves the Montgomery block of
the reference evaluation at the result register, and preserves everything below
`next`. -/
theorem compileExprML_sim :
    ∀ (e : Expression (F p)) (next : ℕ) (s : State 64),
      Expression.envBound N e = true → s.bufs 0 = envArr →
      PreludeEnc p pv k s → LE.le (α := ℕ) (k + 3) next →
      ∃ s' t d pp, Exec C (compileExprML k 0 (k + 1) e next).1 s s' t d pp ∧
        RegsEnc s' (compileExprML k 0 (k + 1) e next).2.1 k
          (montVal k (e.eval env.toEnvironment)) ∧
        (∀ q, q < next → s'.regs q = s.regs q) ∧
        s'.bufs = s.bufs ∧ s'.caps = s.caps
  | .var v, next, s, hb, hbuf, _, hn => by
    simp only [Expression.envBound, decide_eq_true_eq] at hb
    have hmul : (v.index + 1) * k ≤ N * k := Nat.mul_le_mul_right k (by omega)
    have hexp : (v.index + 1) * k = v.index * k + k := by ring
    have hsz : v.index * k + k ≤ (s.bufs 0).size := by
      rw [hbuf, henv.1]; omega
    simp only [compileExprML]
    obtain ⟨s', t, d, pp, hex, hval, hlow, hhigh, hbufs, hcaps⟩ :=
      loadLimbs_exec (C := C) (base := next + 1) (idx := v.index * k) (sc := next)
        (by omega) k (show v.index * k + k ≤ 2 ^ 64 by omega) hsz
    refine ⟨s', t, d, pp, hex, fun j hj => ?_,
      fun q hq => hlow q (by omega) (by omega), hbufs, hcaps⟩
    rw [hval j hj, hbuf]
    exact henv.2 v.index hb j hj
  | .const c, next, s, _, _, _, _ => by
    obtain ⟨s', t, d, pp, hex, hval, hlow, hhigh, hbufs, hcaps⟩ :=
      immLimbs_exec (C := C) next
        (FiniteField.val c * 2 ^ (64 * k) % FiniteField.size (F p)) (s := s) k
    exact ⟨s', t, d, pp, hex, hval, fun q hq => hlow q hq, hbufs, hcaps⟩
  | .add x y, next, s, hb, hbuf, hpre, hn => by
    simp only [Expression.envBound, Bool.and_eq_true] at hb
    rcases hE₁ : compileExprML k 0 (k + 1) x next with ⟨cx, rx, n₁⟩
    rcases hE₂ : compileExprML k 0 (k + 1) y n₁ with ⟨cy, ry, n₂⟩
    have hbd₁ := compileExprML_bounds k 0 (k + 1) x next
    have hbd₂ := compileExprML_bounds k 0 (k + 1) y n₁
    simp only [hE₁] at hbd₁
    simp only [hE₂] at hbd₂
    obtain ⟨s₁, t₁, d₁, p₁, hex₁, hr₁, hp₁, hbf₁, hcp₁⟩ :=
      compileExprML_sim x next s hb.1 hbuf hpre hn
    simp only [hE₁] at hex₁ hr₁
    have hpre₁ : PreludeEnc p pv k s₁ :=
      ⟨fun j hj => by rw [hp₁ _ (by omega)]; exact hpre.modulus j hj,
        by rw [hp₁ _ (by omega)]; exact hpre.const⟩
    obtain ⟨s₂, t₂, d₂, p₂, hex₂, hr₂, hp₂, hbf₂, hcp₂⟩ :=
      compileExprML_sim y n₁ s₁ hb.2 (by rw [hbf₁]; exact hbuf) hpre₁
        (Nat.le_trans hn hbd₁.1)
    simp only [hE₂] at hex₂ hr₂
    have hpre₂ : PreludeEnc p pv k s₂ :=
      ⟨fun j hj => by rw [hp₂ _ (by omega)]; exact hpre₁.modulus j hj,
        by rw [hp₂ _ (by omega)]; exact hpre₁.const⟩
    have hrx : RegsEnc s₂ rx k (montVal k (x.eval env.toEnvironment)) := fun j hj => by
      rw [hp₂ _ (by omega)]; exact hr₁ j hj
    obtain ⟨s₃, t₃, d₃, p₃, hex₃, hr₃, hp₃, hbf₃, hcp₃⟩ :=
      montAdd_field (C := C) (w := n₂) (a := rx) (b := ry) hf.bound hpre₂
        (by omega) (by omega) (by omega) hrx hr₂
    simp only [compileExprML, hE₁, hE₂]
    refine ⟨s₃, _, _, _, .seq hex₁ (.seq hex₂ hex₃), hr₃, ?_, ?_, ?_⟩
    · intro q hq
      rw [hp₃ q (by omega), hp₂ q (by omega), hp₁ q hq]
    · rw [hbf₃, hbf₂, hbf₁]
    · rw [hcp₃, hcp₂, hcp₁]
  | .mul x y, next, s, hb, hbuf, hpre, hn => by
    simp only [Expression.envBound, Bool.and_eq_true] at hb
    rcases hE₁ : compileExprML k 0 (k + 1) x next with ⟨cx, rx, n₁⟩
    rcases hE₂ : compileExprML k 0 (k + 1) y n₁ with ⟨cy, ry, n₂⟩
    have hbd₁ := compileExprML_bounds k 0 (k + 1) x next
    have hbd₂ := compileExprML_bounds k 0 (k + 1) y n₁
    simp only [hE₁] at hbd₁
    simp only [hE₂] at hbd₂
    obtain ⟨s₁, t₁, d₁, p₁, hex₁, hr₁, hp₁, hbf₁, hcp₁⟩ :=
      compileExprML_sim x next s hb.1 hbuf hpre hn
    simp only [hE₁] at hex₁ hr₁
    have hpre₁ : PreludeEnc p pv k s₁ :=
      ⟨fun j hj => by rw [hp₁ _ (by omega)]; exact hpre.modulus j hj,
        by rw [hp₁ _ (by omega)]; exact hpre.const⟩
    obtain ⟨s₂, t₂, d₂, p₂, hex₂, hr₂, hp₂, hbf₂, hcp₂⟩ :=
      compileExprML_sim y n₁ s₁ hb.2 (by rw [hbf₁]; exact hbuf) hpre₁
        (Nat.le_trans hn hbd₁.1)
    simp only [hE₂] at hex₂ hr₂
    have hpre₂ : PreludeEnc p pv k s₂ :=
      ⟨fun j hj => by rw [hp₂ _ (by omega)]; exact hpre₁.modulus j hj,
        by rw [hp₂ _ (by omega)]; exact hpre₁.const⟩
    have hrx : RegsEnc s₂ rx k (montVal k (x.eval env.toEnvironment)) := fun j hj => by
      rw [hp₂ _ (by omega)]; exact hr₁ j hj
    obtain ⟨s₃, t₃, d₃, p₃, hex₃, hr₃, hp₃, hbf₃, hcp₃⟩ :=
      montMul_field (C := C) (w := n₂) (a := rx) (b := ry) hf.limbs_pos hf.two_lt
        hf.bound hf.const hpre₂ (by omega) (by omega) (by omega) hrx hr₂
    simp only [compileExprML, hE₁, hE₂]
    refine ⟨s₃, _, _, _, .seq hex₁ (.seq hex₂ hex₃), hr₃, ?_, ?_, ?_⟩
    · intro q hq
      rw [hp₃ q (by omega), hp₂ q (by omega), hp₁ q hq]
    · rw [hbf₃, hbf₂, hbf₁]
    · rw [hcp₃, hcp₂, hcp₁]

/-! ## The mutual scalar-compiler induction

Three theorems by simultaneous structural induction, one per sort. A field-sorted node
leaves the Montgomery block of its value; a u64-sorted node and a condition each leave
a single word. The shape of every case is the same: run the children, note that each
child's result block sits below the next child's base (the register bounds), then apply
the gadget's semantic lemma. -/

-- the u64 and condition compilers reach the environment only through `compileFML_sim`,
-- so the linter sees their own `henv`/`hNk` as unused
set_option linter.unusedSectionVars false in
mutual

/-- Simulation for field-sorted expressions. -/
theorem compileFML_sim (Γ : List VSort) (locals : Array (F p ⊕ UInt64)) (idx L : ℕ)
    (hL : LocalsMatch Γ locals) :
    ∀ (e : FExpr (F p)) (next : ℕ) (s : State 64),
      FExpr.compilable Γ e = true → FExpr.envBound N e = true →
      StateEncML k pv L envArr locals idx next s →
      ∃ s' t d pp, Exec C (compileFML k L e next).1 s s' t d pp ∧
        RegsEnc s' (compileFML k L e next).2.1 k
          (montVal k (FExpr.eval { env, locals, idx } e)) ∧
        (∀ q, q < next → s'.regs q = s.regs q) ∧
        s'.bufs = s.bufs ∧ s'.caps = s.caps
  | .expr e, next, s, _, hb, hs =>
    compileExprML_sim hf env N envArr henv hNk e next s hb hs.env hs.pre
      (Nat.le_trans (by simp only [tmpBase]; omega) hs.frame)
  | .const c, next, s, _, _, _ => by
    obtain ⟨s', t, d, pp, hex, hval, hlow, hhigh, hbufs, hcaps⟩ :=
      immLimbs_exec (C := C) next
        (FiniteField.val c * 2 ^ (64 * k) % FiniteField.size (F p)) (s := s) k
    exact ⟨s', t, d, pp, hex, hval, fun q hq => hlow q hq, hbufs, hcaps⟩
  | .localVar i, next, s, hc, _, hs => by
    simp only [FExpr.compilable, beq_iff_eq] at hc
    have hiΓ : i < Γ.length := lt_length_of_getElem?_fld hc
    have hi : i < locals.size := by rw [← hL.1]; exact hiΓ
    have hsort := hL.2 i hi
    rw [hc] at hsort
    rcases hx : locals[i] with x | u
    · refine ⟨s, 0, 0, 0, .skip, ?_, fun _ _ => rfl, rfl, rfl⟩
      have hloc := hs.loc i hi
      rw [hx] at hloc
      simp only [compileFML, FExpr.eval, Array.getElem?_eq_getElem hi, hx]
      exact hloc
    · rw [hx] at hsort
      exact absurd hsort (by simp)
  | .add x y, next, s, hc, hb, hs => by
    simp only [FExpr.compilable, Bool.and_eq_true] at hc
    simp only [FExpr.envBound, Bool.and_eq_true] at hb
    have hΓ : Γ.length ≤ L := by rw [hL.1]; exact hs.size
    rcases hE₁ : compileFML k L x next with ⟨cx, rx, n₁⟩
    rcases hE₂ : compileFML k L y n₁ with ⟨cy, ry, n₂⟩
    have hbd₁ := compileFML_bounds k L hf.limbs_pos hΓ x next hc.1 hs.frame
    have hbd₂ := compileFML_bounds k L hf.limbs_pos hΓ y n₁ hc.2
      (Nat.le_trans hs.frame (by simp only [hE₁] at hbd₁; exact hbd₁.1))
    simp only [hE₁] at hbd₁
    simp only [hE₂] at hbd₂
    obtain ⟨s₁, t₁, d₁, p₁, hex₁, hr₁, hp₁, hbf₁, hcp₁⟩ :=
      compileFML_sim Γ locals idx L hL x next s hc.1 hb.1 hs
    simp only [hE₁] at hex₁ hr₁
    have hs₁ := StateEncML_mono hs hbd₁.1 hp₁ (by rw [hbf₁])
    obtain ⟨s₂, t₂, d₂, p₂, hex₂, hr₂, hp₂, hbf₂, hcp₂⟩ :=
      compileFML_sim Γ locals idx L hL y n₁ s₁ hc.2 hb.2 hs₁
    simp only [hE₂] at hex₂ hr₂
    have hs₂ := StateEncML_mono hs₁ hbd₂.1 hp₂ (by rw [hbf₂])
    have hfr₂ : k + 3 + L * k ≤ n₂ := by
      have := hs₂.frame; simp only [tmpBase] at this; exact this
    have hrx : RegsEnc s₂ rx k (montVal k (FExpr.eval { env, locals, idx } x)) :=
      fun j hj => by rw [hp₂ _ (by omega)]; exact hr₁ j hj
    obtain ⟨s₃, t₃, d₃, p₃, hex₃, hr₃, hp₃, hbf₃, hcp₃⟩ :=
      montAdd_field (C := C) (w := n₂) (a := rx) (b := ry) hf.bound hs₂.pre
        (by omega) (by omega) (by omega) hrx hr₂
    simp only [compileFML, hE₁, hE₂]
    refine ⟨s₃, _, _, _, .seq hex₁ (.seq hex₂ hex₃), hr₃, ?_, ?_, ?_⟩
    · intro q hq
      rw [hp₃ q (by omega), hp₂ q (by omega), hp₁ q hq]
    · rw [hbf₃, hbf₂, hbf₁]
    · rw [hcp₃, hcp₂, hcp₁]
  | .mul x y, next, s, hc, hb, hs => by
    simp only [FExpr.compilable, Bool.and_eq_true] at hc
    simp only [FExpr.envBound, Bool.and_eq_true] at hb
    have hΓ : Γ.length ≤ L := by rw [hL.1]; exact hs.size
    rcases hE₁ : compileFML k L x next with ⟨cx, rx, n₁⟩
    rcases hE₂ : compileFML k L y n₁ with ⟨cy, ry, n₂⟩
    have hbd₁ := compileFML_bounds k L hf.limbs_pos hΓ x next hc.1 hs.frame
    have hbd₂ := compileFML_bounds k L hf.limbs_pos hΓ y n₁ hc.2
      (Nat.le_trans hs.frame (by simp only [hE₁] at hbd₁; exact hbd₁.1))
    simp only [hE₁] at hbd₁
    simp only [hE₂] at hbd₂
    obtain ⟨s₁, t₁, d₁, p₁, hex₁, hr₁, hp₁, hbf₁, hcp₁⟩ :=
      compileFML_sim Γ locals idx L hL x next s hc.1 hb.1 hs
    simp only [hE₁] at hex₁ hr₁
    have hs₁ := StateEncML_mono hs hbd₁.1 hp₁ (by rw [hbf₁])
    obtain ⟨s₂, t₂, d₂, p₂, hex₂, hr₂, hp₂, hbf₂, hcp₂⟩ :=
      compileFML_sim Γ locals idx L hL y n₁ s₁ hc.2 hb.2 hs₁
    simp only [hE₂] at hex₂ hr₂
    have hs₂ := StateEncML_mono hs₁ hbd₂.1 hp₂ (by rw [hbf₂])
    have hfr₂ : k + 3 + L * k ≤ n₂ := by
      have := hs₂.frame; simp only [tmpBase] at this; exact this
    have hrx : RegsEnc s₂ rx k (montVal k (FExpr.eval { env, locals, idx } x)) :=
      fun j hj => by rw [hp₂ _ (by omega)]; exact hr₁ j hj
    obtain ⟨s₃, t₃, d₃, p₃, hex₃, hr₃, hp₃, hbf₃, hcp₃⟩ :=
      montMul_field (C := C) (w := n₂) (a := rx) (b := ry) hf.limbs_pos hf.two_lt
        hf.bound hf.const hs₂.pre (by omega) (by omega) (by omega) hrx hr₂
    simp only [compileFML, hE₁, hE₂]
    refine ⟨s₃, _, _, _, .seq hex₁ (.seq hex₂ hex₃), hr₃, ?_, ?_, ?_⟩
    · intro q hq
      rw [hp₃ q (by omega), hp₂ q (by omega), hp₁ q hq]
    · rw [hbf₃, hbf₂, hbf₁]
    · rw [hcp₃, hcp₂, hcp₁]
  | .inv x, next, s, hc, hb, hs => by
    have hΓ : Γ.length ≤ L := by rw [hL.1]; exact hs.size
    rcases hE₁ : compileFML k L x next with ⟨cx, rx, n₁⟩
    have hbd₁ := compileFML_bounds k L hf.limbs_pos hΓ x next hc hs.frame
    simp only [hE₁] at hbd₁
    obtain ⟨s₁, t₁, d₁, p₁, hex₁, hr₁, hp₁, hbf₁, hcp₁⟩ :=
      compileFML_sim Γ locals idx L hL x next s hc hb hs
    simp only [hE₁] at hex₁ hr₁
    have hs₁ := StateEncML_mono hs hbd₁.1 hp₁ (by rw [hbf₁])
    have hfr₁ : k + 3 + L * k ≤ n₁ := by
      have := hs₁.frame; simp only [tmpBase] at this; exact this
    obtain ⟨s₂, t₂, d₂, p₂, hex₂, hr₂, hp₂, hbf₂, hcp₂⟩ :=
      montInv_field (C := C) (w := n₁) (a := rx) hf.limbs_pos hf.two_lt hf.bound
        hf.const hf.budget hs₁.pre (by omega) (by omega) hr₁
    simp only [compileFML, hE₁]
    refine ⟨s₂, _, _, _, .seq hex₁ hex₂, hr₂, ?_, ?_, ?_⟩
    · intro q hq
      rw [hp₂ q (by omega), hp₁ q hq]
    · rw [hbf₂, hbf₁]
    · rw [hcp₂, hcp₁]
  | .ofU64 n, next, s, hc, hb, hs => by
    have hΓ : Γ.length ≤ L := by rw [hL.1]; exact hs.size
    rcases hE₁ : compileUML k L n next with ⟨cn, rn, n₁⟩
    have hbd₁ := compileUML_bounds k L hf.limbs_pos hΓ n next hc hs.frame
    simp only [hE₁] at hbd₁
    obtain ⟨s₁, t₁, d₁, p₁, hex₁, hr₁, hp₁, hbf₁, hcp₁⟩ :=
      compileUML_sim Γ locals idx L hL n next s hc hb hs
    simp only [hE₁] at hex₁ hr₁
    have hs₁ := StateEncML_mono hs hbd₁.1 hp₁ (by rw [hbf₁])
    have hfr₁ : k + 3 + L * k ≤ n₁ := by
      have := hs₁.frame; simp only [tmpBase] at this; exact this
    obtain ⟨s₂, t₂, d₂, p₂, hex₂, hz₂, hlow₂, hhigh₂, hbf₂, hcp₂⟩ :=
      immLimbs_exec (C := C) n₁ 0 (s := s₁) k
    set u := U64Expr.eval { env, locals, idx } n with hu
    have hutn : u.toNat < 2 ^ 64 := u.toBitVec.isLt
    have hrn₂ : s₂.regs rn = encU u := by rw [hlow₂ rn hbd₁.2]; exact hr₁
    set s₃ := s₂.setReg n₁ (s₂.regs rn) with h₃
    have hblk : RegsEnc s₃ n₁ k u.toNat := by
      intro j hj
      rcases Nat.eq_zero_or_pos j with rfl | hjp
      · rw [Nat.add_zero, h₃, regs_setReg_self, hrn₂, limb_low, ofNat_mod]
        exact (encU_ofNat_toNat u).symm
      · have hlt : u.toNat < 2 ^ (64 * j) :=
          lt_of_lt_of_le hutn
            (Nat.pow_le_pow_right (by norm_num) (show 64 ≤ 64 * j by omega))
        have hz : limb 64 u.toNat j = 0 := by
          simp only [limb, Nat.div_eq_of_lt hlt]
          simp
        have hne : n₁ + j ≠ n₁ := (Nat.lt_add_of_pos_right hjp).ne'
        rw [h₃, regs_setReg_ne _ _ hne, hz₂ j hj, hz]
        simp
    have hpre₃ : PreludeEnc p pv k s₃ :=
      ⟨fun j hj => by
          have hne : ¬ (0 + j = n₁) := by omega
          rw [h₃, regs_setReg_ne _ _ hne, hlow₂ _ (show 0 + j < n₁ by omega)]
          exact hs₁.pre.modulus j hj,
        by
          have hne : ¬ (k + 1 = n₁) := by omega
          rw [h₃, regs_setReg_ne _ _ hne, hlow₂ _ (show k + 1 < n₁ by omega)]
          exact hs₁.pre.const⟩
    obtain ⟨s₄, t₄, d₄, p₄, hex₄, hr₄, hp₄, hbf₄, hcp₄⟩ :=
      enterMont_field (C := C) (w := n₁ + k) (a := n₁) (A := u.toNat)
        (x := FiniteField.fromNat u.toNat) hf.limbs_pos hf.two_lt hf.bound hf.const
        hpre₃ (by omega) (by omega)
        (lt_of_lt_of_le hutn (Nat.pow_le_pow_right (by norm_num)
          (show 64 ≤ 64 * k by have := hf.limbs_pos; omega)))
        (FiniteField.fromNat_F u.toNat).symm hblk
    simp only [compileFML, hE₁]
    refine ⟨s₄, _, _, _, .seq hex₁ (.seq hex₂ (.seq .mov hex₄)), hr₄, ?_, ?_, ?_⟩
    · intro q hq
      rw [hp₄ q (by omega), h₃, regs_setReg_ne _ _ (show q ≠ n₁ by omega),
        hlow₂ q (by omega), hp₁ q hq]
    · rw [hbf₄, h₃, bufs_setReg, hbf₂, hbf₁]
    · rw [hcp₄, h₃, caps_setReg, hcp₂, hcp₁]
  | .ite c t e, next, s, hc, hb, hs => by
    simp only [FExpr.compilable, Bool.and_eq_true] at hc
    simp only [FExpr.envBound, Bool.and_eq_true] at hb
    have hΓ : Γ.length ≤ L := by rw [hL.1]; exact hs.size
    rcases hE₁ : compileBML k L c next with ⟨cc, rc, n₁⟩
    rcases hE₂ : compileFML k L t n₁ with ⟨ct, rt, n₂⟩
    rcases hE₃ : compileFML k L e n₂ with ⟨ce, re, n₃⟩
    have hbd₁ := compileBML_bounds k L hf.limbs_pos hΓ c next hc.1.1 hs.frame
    have hbd₂ := compileFML_bounds k L hf.limbs_pos hΓ t n₁ hc.1.2
      (Nat.le_trans hs.frame (by simp only [hE₁] at hbd₁; exact hbd₁.1))
    have hbd₃ := compileFML_bounds k L hf.limbs_pos hΓ e n₂ hc.2
      (Nat.le_trans hs.frame (Nat.le_trans
        (by simp only [hE₁] at hbd₁; exact hbd₁.1)
        (by simp only [hE₂] at hbd₂; exact hbd₂.1)))
    simp only [hE₁] at hbd₁
    simp only [hE₂] at hbd₂
    simp only [hE₃] at hbd₃
    obtain ⟨s₁, t₁, d₁, p₁, hex₁, hr₁, hp₁, hbf₁, hcp₁⟩ :=
      compileBML_sim Γ locals idx L hL c next s hc.1.1 hb.1.1 hs
    simp only [hE₁] at hex₁ hr₁
    have hs₁ := StateEncML_mono hs hbd₁.1 hp₁ (by rw [hbf₁])
    obtain ⟨s₂, t₂, d₂, p₂, hex₂, hr₂, hp₂, hbf₂, hcp₂⟩ :=
      compileFML_sim Γ locals idx L hL t n₁ s₁ hc.1.2 hb.1.2 hs₁
    simp only [hE₂] at hex₂ hr₂
    have hs₂ := StateEncML_mono hs₁ hbd₂.1 hp₂ (by rw [hbf₂])
    obtain ⟨s₃, t₃, d₃, p₃, hex₃, hr₃, hp₃, hbf₃, hcp₃⟩ :=
      compileFML_sim Γ locals idx L hL e n₂ s₂ hc.2 hb.2 hs₂
    simp only [hE₃] at hex₃ hr₃
    set cv := BExpr.eval { env, locals, idx } c with hcv
    have hflag : s₃.regs rc = BitVec.ofNat 64 (if cv then 1 else 0) := by
      rw [hp₃ rc (by omega), hp₂ rc (by omega), hr₁]
      cases cv <;> rfl
    have hrt : RegsEnc s₃ rt k (montVal k (FExpr.eval { env, locals, idx } t)) :=
      fun j hj => by rw [hp₃ _ (by omega)]; exact hr₂ j hj
    obtain ⟨s₄, t₄, d₄, p₄, hex₄, hr₄, hp₄, hbf₄, hcp₄⟩ :=
      selectLimbs_exec (C := C) (k := k) (d := n₃ + 1) (a := rt) (b := re)
        (f := rc) (sc := n₃) ⟨by omega, by omega, by omega, by omega⟩
        (show (if cv then 1 else 0) ≤ 1 by cases cv <;> simp) hrt hr₃ hflag
    simp only [compileFML, hE₁, hE₂, hE₃]
    refine ⟨s₄, _, _, _, .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)), ?_, ?_, ?_, ?_⟩
    · have : (if (if cv then 1 else 0) = 1 then
          montVal k (FExpr.eval { env, locals, idx } t)
        else montVal k (FExpr.eval { env, locals, idx } e))
          = montVal k (FExpr.eval { env, locals, idx } (.ite c t e)) := by
        simp only [FExpr.eval, ← hcv]
        cases cv <;> simp
      rwa [this] at hr₄
    · intro q hq
      rw [hp₄ q (by omega), hp₃ q (by omega), hp₂ q (by omega), hp₁ q hq]
    · rw [hbf₄, hbf₃, hbf₂, hbf₁]
    · rw [hcp₄, hcp₃, hcp₂, hcp₁]
  | .listGet .., _, _, hc, _, _ => absurd hc (by simp [FExpr.compilable])
  | .dataGet .., _, _, hc, _, _ => absurd hc (by simp [FExpr.compilable])
  | .hintGet .., _, _, hc, _, _ => absurd hc (by simp [FExpr.compilable])

/-- Simulation for u64-sorted expressions. -/
theorem compileUML_sim (Γ : List VSort) (locals : Array (F p ⊕ UInt64)) (idx L : ℕ)
    (hL : LocalsMatch Γ locals) :
    ∀ (e : U64Expr (F p)) (next : ℕ) (s : State 64),
      U64Expr.compilable Γ e = true → U64Expr.envBound N e = true →
      StateEncML k pv L envArr locals idx next s →
      ∃ s' t d pp, Exec C (compileUML k L e next).1 s s' t d pp ∧
        s'.regs (compileUML k L e next).2.1 =
          encU (U64Expr.eval { env, locals, idx } e) ∧
        (∀ q, q < next → s'.regs q = s.regs q) ∧
        s'.bufs = s.bufs ∧ s'.caps = s.caps
  | .const n, next, s, _, _, _ => by
    simp only [compileUML]
    refine ⟨_, _, _, _, .imm, ?_,
      fun q hq => regs_setReg_ne _ _ (show q ≠ next by omega), rfl, rfl⟩
    rw [regs_setReg_self]
    exact encU_ofNat_toNat n
  | .val x, next, s, hc, hb, hs => by
    have hΓ : Γ.length ≤ L := by rw [hL.1]; exact hs.size
    rcases hE₁ : compileFML k L x next with ⟨cx, rx, n₁⟩
    have hbd₁ := compileFML_bounds k L hf.limbs_pos hΓ x next hc hs.frame
    simp only [hE₁] at hbd₁
    obtain ⟨s₁, t₁, d₁, p₁, hex₁, hr₁, hp₁, hbf₁, hcp₁⟩ :=
      compileFML_sim Γ locals idx L hL x next s hc hb hs
    simp only [hE₁] at hex₁ hr₁
    have hs₁ := StateEncML_mono hs hbd₁.1 hp₁ (by rw [hbf₁])
    have hfr₁ : k + 3 + L * k ≤ n₁ := by
      have := hs₁.frame; simp only [tmpBase] at this; exact this
    obtain ⟨s₂, t₂, d₂, p₂, hex₂, hr₂, hp₂, hbf₂, hcp₂⟩ :=
      leaveMont_field (C := C) (w := n₁) (a := rx) hf.limbs_pos hf.two_lt hf.bound
        hf.const hs₁.pre (by omega) (by omega) hr₁
    simp only [compileUML, hE₁]
    refine ⟨s₂, _, _, _, .seq hex₁ hex₂, ?_, ?_, ?_, ?_⟩
    · have h0 := hr₂ 0 hf.limbs_pos
      rw [Nat.add_zero, limb_low, ofNat_mod] at h0
      rw [h0]
      rfl
    · intro q hq
      rw [hp₂ q (by omega), hp₁ q hq]
    · rw [hbf₂, hbf₁]
    · rw [hcp₂, hcp₁]
  | .idx, next, s, _, _, hs =>
    ⟨s, 0, 0, 0, .skip, hs.index, fun _ _ => rfl, rfl, rfl⟩
  | .localVar i, next, s, hc, _, hs => by
    simp only [U64Expr.compilable, beq_iff_eq] at hc
    have hiΓ : i < Γ.length := lt_length_of_getElem?_fld hc
    have hi : i < locals.size := by rw [← hL.1]; exact hiΓ
    have hsort := hL.2 i hi
    rw [hc] at hsort
    rcases hx : locals[i] with x | u
    · rw [hx] at hsort
      exact absurd hsort (by simp)
    · refine ⟨s, 0, 0, 0, .skip, ?_, fun _ _ => rfl, rfl, rfl⟩
      have hloc := hs.loc i hi
      rw [hx] at hloc
      simp only [compileUML, U64Expr.eval, Array.getElem?_eq_getElem hi, hx]
      exact hloc
  | .add x y, next, s, hc, hb, hs => by
    simp only [U64Expr.compilable, Bool.and_eq_true] at hc
    simp only [U64Expr.envBound, Bool.and_eq_true] at hb
    have hΓ : Γ.length ≤ L := by rw [hL.1]; exact hs.size
    rcases hE₁ : compileUML k L x next with ⟨cx, rx, n₁⟩
    rcases hE₂ : compileUML k L y n₁ with ⟨cy, ry, n₂⟩
    have hbd₁ := compileUML_bounds k L hf.limbs_pos hΓ x next hc.1 hs.frame
    have hbd₂ := compileUML_bounds k L hf.limbs_pos hΓ y n₁ hc.2
      (Nat.le_trans hs.frame (by simp only [hE₁] at hbd₁; exact hbd₁.1))
    simp only [hE₁] at hbd₁
    simp only [hE₂] at hbd₂
    obtain ⟨s₁, t₁, d₁, p₁, hex₁, hr₁, hp₁, hbf₁, hcp₁⟩ :=
      compileUML_sim Γ locals idx L hL x next s hc.1 hb.1 hs
    simp only [hE₁] at hex₁ hr₁
    have hs₁ := StateEncML_mono hs hbd₁.1 hp₁ (by rw [hbf₁])
    obtain ⟨s₂, t₂, d₂, p₂, hex₂, hr₂, hp₂, hbf₂, hcp₂⟩ :=
      compileUML_sim Γ locals idx L hL y n₁ s₁ hc.2 hb.2 hs₁
    simp only [hE₂] at hex₂ hr₂
    simp only [compileUML, hE₁, hE₂]
    exact binW_glue hbd₁.2 hbd₂.1 hbd₁.1 hex₁ hex₂ hr₁ hr₂ (encU_add _ _)
      hp₁ hp₂ hbf₁ hbf₂ hcp₁ hcp₂
  | .mul x y, next, s, hc, hb, hs => by
    simp only [U64Expr.compilable, Bool.and_eq_true] at hc
    simp only [U64Expr.envBound, Bool.and_eq_true] at hb
    have hΓ : Γ.length ≤ L := by rw [hL.1]; exact hs.size
    rcases hE₁ : compileUML k L x next with ⟨cx, rx, n₁⟩
    rcases hE₂ : compileUML k L y n₁ with ⟨cy, ry, n₂⟩
    have hbd₁ := compileUML_bounds k L hf.limbs_pos hΓ x next hc.1 hs.frame
    have hbd₂ := compileUML_bounds k L hf.limbs_pos hΓ y n₁ hc.2
      (Nat.le_trans hs.frame (by simp only [hE₁] at hbd₁; exact hbd₁.1))
    simp only [hE₁] at hbd₁
    simp only [hE₂] at hbd₂
    obtain ⟨s₁, t₁, d₁, p₁, hex₁, hr₁, hp₁, hbf₁, hcp₁⟩ :=
      compileUML_sim Γ locals idx L hL x next s hc.1 hb.1 hs
    simp only [hE₁] at hex₁ hr₁
    have hs₁ := StateEncML_mono hs hbd₁.1 hp₁ (by rw [hbf₁])
    obtain ⟨s₂, t₂, d₂, p₂, hex₂, hr₂, hp₂, hbf₂, hcp₂⟩ :=
      compileUML_sim Γ locals idx L hL y n₁ s₁ hc.2 hb.2 hs₁
    simp only [hE₂] at hex₂ hr₂
    simp only [compileUML, hE₁, hE₂]
    exact binW_glue hbd₁.2 hbd₂.1 hbd₁.1 hex₁ hex₂ hr₁ hr₂ (encU_mul _ _)
      hp₁ hp₂ hbf₁ hbf₂ hcp₁ hcp₂
  | .div x y, next, s, hc, hb, hs => by
    simp only [U64Expr.compilable, Bool.and_eq_true] at hc
    simp only [U64Expr.envBound, Bool.and_eq_true] at hb
    have hΓ : Γ.length ≤ L := by rw [hL.1]; exact hs.size
    rcases hE₁ : compileUML k L x next with ⟨cx, rx, n₁⟩
    rcases hE₂ : compileUML k L y n₁ with ⟨cy, ry, n₂⟩
    have hbd₁ := compileUML_bounds k L hf.limbs_pos hΓ x next hc.1 hs.frame
    have hbd₂ := compileUML_bounds k L hf.limbs_pos hΓ y n₁ hc.2
      (Nat.le_trans hs.frame (by simp only [hE₁] at hbd₁; exact hbd₁.1))
    simp only [hE₁] at hbd₁
    simp only [hE₂] at hbd₂
    obtain ⟨s₁, t₁, d₁, p₁, hex₁, hr₁, hp₁, hbf₁, hcp₁⟩ :=
      compileUML_sim Γ locals idx L hL x next s hc.1 hb.1 hs
    simp only [hE₁] at hex₁ hr₁
    have hs₁ := StateEncML_mono hs hbd₁.1 hp₁ (by rw [hbf₁])
    obtain ⟨s₂, t₂, d₂, p₂, hex₂, hr₂, hp₂, hbf₂, hcp₂⟩ :=
      compileUML_sim Γ locals idx L hL y n₁ s₁ hc.2 hb.2 hs₁
    simp only [hE₂] at hex₂ hr₂
    simp only [compileUML, hE₁, hE₂]
    exact binW_glue hbd₁.2 hbd₂.1 hbd₁.1 hex₁ hex₂ hr₁ hr₂ (encU_div _ _)
      hp₁ hp₂ hbf₁ hbf₂ hcp₁ hcp₂
  | .mod x y, next, s, hc, hb, hs => by
    simp only [U64Expr.compilable, Bool.and_eq_true] at hc
    simp only [U64Expr.envBound, Bool.and_eq_true] at hb
    have hΓ : Γ.length ≤ L := by rw [hL.1]; exact hs.size
    rcases hE₁ : compileUML k L x next with ⟨cx, rx, n₁⟩
    rcases hE₂ : compileUML k L y n₁ with ⟨cy, ry, n₂⟩
    have hbd₁ := compileUML_bounds k L hf.limbs_pos hΓ x next hc.1 hs.frame
    have hbd₂ := compileUML_bounds k L hf.limbs_pos hΓ y n₁ hc.2
      (Nat.le_trans hs.frame (by simp only [hE₁] at hbd₁; exact hbd₁.1))
    simp only [hE₁] at hbd₁
    simp only [hE₂] at hbd₂
    obtain ⟨s₁, t₁, d₁, p₁, hex₁, hr₁, hp₁, hbf₁, hcp₁⟩ :=
      compileUML_sim Γ locals idx L hL x next s hc.1 hb.1 hs
    simp only [hE₁] at hex₁ hr₁
    have hs₁ := StateEncML_mono hs hbd₁.1 hp₁ (by rw [hbf₁])
    obtain ⟨s₂, t₂, d₂, p₂, hex₂, hr₂, hp₂, hbf₂, hcp₂⟩ :=
      compileUML_sim Γ locals idx L hL y n₁ s₁ hc.2 hb.2 hs₁
    simp only [hE₂] at hex₂ hr₂
    simp only [compileUML, hE₁, hE₂]
    exact binW_glue hbd₁.2 hbd₂.1 hbd₁.1 hex₁ hex₂ hr₁ hr₂ (encU_mod _ _)
      hp₁ hp₂ hbf₁ hbf₂ hcp₁ hcp₂
  | .land x y, next, s, hc, hb, hs => by
    simp only [U64Expr.compilable, Bool.and_eq_true] at hc
    simp only [U64Expr.envBound, Bool.and_eq_true] at hb
    have hΓ : Γ.length ≤ L := by rw [hL.1]; exact hs.size
    rcases hE₁ : compileUML k L x next with ⟨cx, rx, n₁⟩
    rcases hE₂ : compileUML k L y n₁ with ⟨cy, ry, n₂⟩
    have hbd₁ := compileUML_bounds k L hf.limbs_pos hΓ x next hc.1 hs.frame
    have hbd₂ := compileUML_bounds k L hf.limbs_pos hΓ y n₁ hc.2
      (Nat.le_trans hs.frame (by simp only [hE₁] at hbd₁; exact hbd₁.1))
    simp only [hE₁] at hbd₁
    simp only [hE₂] at hbd₂
    obtain ⟨s₁, t₁, d₁, p₁, hex₁, hr₁, hp₁, hbf₁, hcp₁⟩ :=
      compileUML_sim Γ locals idx L hL x next s hc.1 hb.1 hs
    simp only [hE₁] at hex₁ hr₁
    have hs₁ := StateEncML_mono hs hbd₁.1 hp₁ (by rw [hbf₁])
    obtain ⟨s₂, t₂, d₂, p₂, hex₂, hr₂, hp₂, hbf₂, hcp₂⟩ :=
      compileUML_sim Γ locals idx L hL y n₁ s₁ hc.2 hb.2 hs₁
    simp only [hE₂] at hex₂ hr₂
    simp only [compileUML, hE₁, hE₂]
    exact binW_glue hbd₁.2 hbd₂.1 hbd₁.1 hex₁ hex₂ hr₁ hr₂ (encU_and _ _)
      hp₁ hp₂ hbf₁ hbf₂ hcp₁ hcp₂
  | .lor x y, next, s, hc, hb, hs => by
    simp only [U64Expr.compilable, Bool.and_eq_true] at hc
    simp only [U64Expr.envBound, Bool.and_eq_true] at hb
    have hΓ : Γ.length ≤ L := by rw [hL.1]; exact hs.size
    rcases hE₁ : compileUML k L x next with ⟨cx, rx, n₁⟩
    rcases hE₂ : compileUML k L y n₁ with ⟨cy, ry, n₂⟩
    have hbd₁ := compileUML_bounds k L hf.limbs_pos hΓ x next hc.1 hs.frame
    have hbd₂ := compileUML_bounds k L hf.limbs_pos hΓ y n₁ hc.2
      (Nat.le_trans hs.frame (by simp only [hE₁] at hbd₁; exact hbd₁.1))
    simp only [hE₁] at hbd₁
    simp only [hE₂] at hbd₂
    obtain ⟨s₁, t₁, d₁, p₁, hex₁, hr₁, hp₁, hbf₁, hcp₁⟩ :=
      compileUML_sim Γ locals idx L hL x next s hc.1 hb.1 hs
    simp only [hE₁] at hex₁ hr₁
    have hs₁ := StateEncML_mono hs hbd₁.1 hp₁ (by rw [hbf₁])
    obtain ⟨s₂, t₂, d₂, p₂, hex₂, hr₂, hp₂, hbf₂, hcp₂⟩ :=
      compileUML_sim Γ locals idx L hL y n₁ s₁ hc.2 hb.2 hs₁
    simp only [hE₂] at hex₂ hr₂
    simp only [compileUML, hE₁, hE₂]
    exact binW_glue hbd₁.2 hbd₂.1 hbd₁.1 hex₁ hex₂ hr₁ hr₂ (encU_or _ _)
      hp₁ hp₂ hbf₁ hbf₂ hcp₁ hcp₂
  | .lxor x y, next, s, hc, hb, hs => by
    simp only [U64Expr.compilable, Bool.and_eq_true] at hc
    simp only [U64Expr.envBound, Bool.and_eq_true] at hb
    have hΓ : Γ.length ≤ L := by rw [hL.1]; exact hs.size
    rcases hE₁ : compileUML k L x next with ⟨cx, rx, n₁⟩
    rcases hE₂ : compileUML k L y n₁ with ⟨cy, ry, n₂⟩
    have hbd₁ := compileUML_bounds k L hf.limbs_pos hΓ x next hc.1 hs.frame
    have hbd₂ := compileUML_bounds k L hf.limbs_pos hΓ y n₁ hc.2
      (Nat.le_trans hs.frame (by simp only [hE₁] at hbd₁; exact hbd₁.1))
    simp only [hE₁] at hbd₁
    simp only [hE₂] at hbd₂
    obtain ⟨s₁, t₁, d₁, p₁, hex₁, hr₁, hp₁, hbf₁, hcp₁⟩ :=
      compileUML_sim Γ locals idx L hL x next s hc.1 hb.1 hs
    simp only [hE₁] at hex₁ hr₁
    have hs₁ := StateEncML_mono hs hbd₁.1 hp₁ (by rw [hbf₁])
    obtain ⟨s₂, t₂, d₂, p₂, hex₂, hr₂, hp₂, hbf₂, hcp₂⟩ :=
      compileUML_sim Γ locals idx L hL y n₁ s₁ hc.2 hb.2 hs₁
    simp only [hE₂] at hex₂ hr₂
    simp only [compileUML, hE₁, hE₂]
    exact binW_glue hbd₁.2 hbd₂.1 hbd₁.1 hex₁ hex₂ hr₁ hr₂ (encU_xor _ _)
      hp₁ hp₂ hbf₁ hbf₂ hcp₁ hcp₂
  | .shiftL x y, next, s, hc, hb, hs => by
    simp only [U64Expr.compilable, Bool.and_eq_true] at hc
    simp only [U64Expr.envBound, Bool.and_eq_true] at hb
    have hΓ : Γ.length ≤ L := by rw [hL.1]; exact hs.size
    rcases hE₁ : compileUML k L x next with ⟨cx, rx, n₁⟩
    rcases hE₂ : compileUML k L y n₁ with ⟨cy, ry, n₂⟩
    have hbd₁ := compileUML_bounds k L hf.limbs_pos hΓ x next hc.1 hs.frame
    have hbd₂ := compileUML_bounds k L hf.limbs_pos hΓ y n₁ hc.2
      (Nat.le_trans hs.frame (by simp only [hE₁] at hbd₁; exact hbd₁.1))
    simp only [hE₁] at hbd₁
    simp only [hE₂] at hbd₂
    obtain ⟨s₁, t₁, d₁, p₁, hex₁, hr₁, hp₁, hbf₁, hcp₁⟩ :=
      compileUML_sim Γ locals idx L hL x next s hc.1 hb.1 hs
    simp only [hE₁] at hex₁ hr₁
    have hs₁ := StateEncML_mono hs hbd₁.1 hp₁ (by rw [hbf₁])
    obtain ⟨s₂, t₂, d₂, p₂, hex₂, hr₂, hp₂, hbf₂, hcp₂⟩ :=
      compileUML_sim Γ locals idx L hL y n₁ s₁ hc.2 hb.2 hs₁
    simp only [hE₂] at hex₂ hr₂
    simp only [compileUML, hE₁, hE₂]
    exact shiftW_glue hbd₁.2 hbd₂.1 hbd₁.1 hbd₂.2 hex₁ hex₂ hr₁ hr₂
      (encU_shiftL _ _) hp₁ hp₂ hbf₁ hbf₂ hcp₁ hcp₂
  | .shiftR x y, next, s, hc, hb, hs => by
    simp only [U64Expr.compilable, Bool.and_eq_true] at hc
    simp only [U64Expr.envBound, Bool.and_eq_true] at hb
    have hΓ : Γ.length ≤ L := by rw [hL.1]; exact hs.size
    rcases hE₁ : compileUML k L x next with ⟨cx, rx, n₁⟩
    rcases hE₂ : compileUML k L y n₁ with ⟨cy, ry, n₂⟩
    have hbd₁ := compileUML_bounds k L hf.limbs_pos hΓ x next hc.1 hs.frame
    have hbd₂ := compileUML_bounds k L hf.limbs_pos hΓ y n₁ hc.2
      (Nat.le_trans hs.frame (by simp only [hE₁] at hbd₁; exact hbd₁.1))
    simp only [hE₁] at hbd₁
    simp only [hE₂] at hbd₂
    obtain ⟨s₁, t₁, d₁, p₁, hex₁, hr₁, hp₁, hbf₁, hcp₁⟩ :=
      compileUML_sim Γ locals idx L hL x next s hc.1 hb.1 hs
    simp only [hE₁] at hex₁ hr₁
    have hs₁ := StateEncML_mono hs hbd₁.1 hp₁ (by rw [hbf₁])
    obtain ⟨s₂, t₂, d₂, p₂, hex₂, hr₂, hp₂, hbf₂, hcp₂⟩ :=
      compileUML_sim Γ locals idx L hL y n₁ s₁ hc.2 hb.2 hs₁
    simp only [hE₂] at hex₂ hr₂
    simp only [compileUML, hE₁, hE₂]
    exact shiftW_glue hbd₁.2 hbd₂.1 hbd₁.1 hbd₂.2 hex₁ hex₂ hr₁ hr₂
      (encU_shiftR _ _) hp₁ hp₂ hbf₁ hbf₂ hcp₁ hcp₂
  | .ite c t e, next, s, hc, hb, hs => by
    simp only [U64Expr.compilable, Bool.and_eq_true] at hc
    simp only [U64Expr.envBound, Bool.and_eq_true] at hb
    have hΓ : Γ.length ≤ L := by rw [hL.1]; exact hs.size
    rcases hE₁ : compileBML k L c next with ⟨cc, rc, n₁⟩
    rcases hE₂ : compileUML k L t n₁ with ⟨ct, rt, n₂⟩
    rcases hE₃ : compileUML k L e n₂ with ⟨ce, re, n₃⟩
    have hbd₁ := compileBML_bounds k L hf.limbs_pos hΓ c next hc.1.1 hs.frame
    have hbd₂ := compileUML_bounds k L hf.limbs_pos hΓ t n₁ hc.1.2
      (Nat.le_trans hs.frame (by simp only [hE₁] at hbd₁; exact hbd₁.1))
    have hbd₃ := compileUML_bounds k L hf.limbs_pos hΓ e n₂ hc.2
      (Nat.le_trans hs.frame (Nat.le_trans
        (by simp only [hE₁] at hbd₁; exact hbd₁.1)
        (by simp only [hE₂] at hbd₂; exact hbd₂.1)))
    simp only [hE₁] at hbd₁
    simp only [hE₂] at hbd₂
    simp only [hE₃] at hbd₃
    obtain ⟨s₁, t₁, d₁, p₁, hex₁, hr₁, hp₁, hbf₁, hcp₁⟩ :=
      compileBML_sim Γ locals idx L hL c next s hc.1.1 hb.1.1 hs
    simp only [hE₁] at hex₁ hr₁
    have hs₁ := StateEncML_mono hs hbd₁.1 hp₁ (by rw [hbf₁])
    obtain ⟨s₂, t₂, d₂, p₂, hex₂, hr₂, hp₂, hbf₂, hcp₂⟩ :=
      compileUML_sim Γ locals idx L hL t n₁ s₁ hc.1.2 hb.1.2 hs₁
    simp only [hE₂] at hex₂ hr₂
    have hs₂ := StateEncML_mono hs₁ hbd₂.1 hp₂ (by rw [hbf₂])
    obtain ⟨s₃, t₃, d₃, p₃, hex₃, hr₃, hp₃, hbf₃, hcp₃⟩ :=
      compileUML_sim Γ locals idx L hL e n₂ s₂ hc.2 hb.2 hs₂
    simp only [hE₃] at hex₃ hr₃
    set cv := BExpr.eval { env, locals, idx } c with hcv
    set tv := U64Expr.eval { env, locals, idx } t with htv
    set ev := U64Expr.eval { env, locals, idx } e with hev
    have hflag : s₃.regs rc = BitVec.ofNat 64 (if cv then 1 else 0) := by
      rw [hp₃ rc (by omega), hp₂ rc (by omega), hr₁]
      cases cv <;> rfl
    have hrt : RegsEnc s₃ rt 1 tv.toNat :=
      regsEnc_one (by rw [hp₃ rt (by omega)]; exact hr₂)
    obtain ⟨s₄, t₄, d₄, p₄, hex₄, hr₄, hp₄, hbf₄, hcp₄⟩ :=
      selectLimbs_exec (C := C) (k := 1) (d := n₃ + 1) (a := rt) (b := re)
        (f := rc) (sc := n₃) ⟨by omega, by omega, by omega, by omega⟩
        (show (if cv then 1 else 0) ≤ 1 by cases cv <;> simp) hrt
        (regsEnc_one hr₃) hflag
    simp only [compileUML, hE₁, hE₂, hE₃]
    refine ⟨s₄, _, _, _, .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)), ?_, ?_, ?_, ?_⟩
    · rw [word_of_regsEnc_one hr₄]
      simp only [U64Expr.eval, ← hcv, ← htv, ← hev]
      cases cv <;> simp [encU]
    · intro q hq
      rw [hp₄ q (by omega), hp₃ q (by omega), hp₂ q (by omega), hp₁ q hq]
    · rw [hbf₄, hbf₃, hbf₂, hbf₁]
    · rw [hcp₄, hcp₃, hcp₂, hcp₁]

/-- Simulation for conditions. -/
theorem compileBML_sim (Γ : List VSort) (locals : Array (F p ⊕ UInt64)) (idx L : ℕ)
    (hL : LocalsMatch Γ locals) :
    ∀ (e : BExpr (F p)) (next : ℕ) (s : State 64),
      BExpr.compilable Γ e = true → BExpr.envBound N e = true →
      StateEncML k pv L envArr locals idx next s →
      ∃ s' t d pp, Exec C (compileBML k L e next).1 s s' t d pp ∧
        s'.regs (compileBML k L e next).2.1 =
          encB (BExpr.eval { env, locals, idx } e) ∧
        (∀ q, q < next → s'.regs q = s.regs q) ∧
        s'.bufs = s.bufs ∧ s'.caps = s.caps
  | .true, next, s, _, _, _ => by
    simp only [compileBML]
    exact ⟨_, _, _, _, .imm, regs_setReg_self _ _ _,
      fun q hq => regs_setReg_ne _ _ (show q ≠ next by omega), rfl, rfl⟩
  | .false, next, s, _, _, _ => by
    simp only [compileBML]
    exact ⟨_, _, _, _, .imm, regs_setReg_self _ _ _,
      fun q hq => regs_setReg_ne _ _ (show q ≠ next by omega), rfl, rfl⟩
  | .feq x y, next, s, hc, hb, hs => by
    simp only [BExpr.compilable, Bool.and_eq_true] at hc
    simp only [BExpr.envBound, Bool.and_eq_true] at hb
    have hΓ : Γ.length ≤ L := by rw [hL.1]; exact hs.size
    rcases hE₁ : compileFML k L x next with ⟨cx, rx, n₁⟩
    rcases hE₂ : compileFML k L y n₁ with ⟨cy, ry, n₂⟩
    have hbd₁ := compileFML_bounds k L hf.limbs_pos hΓ x next hc.1 hs.frame
    have hbd₂ := compileFML_bounds k L hf.limbs_pos hΓ y n₁ hc.2
      (Nat.le_trans hs.frame (by simp only [hE₁] at hbd₁; exact hbd₁.1))
    simp only [hE₁] at hbd₁
    simp only [hE₂] at hbd₂
    obtain ⟨s₁, t₁, d₁, p₁, hex₁, hr₁, hp₁, hbf₁, hcp₁⟩ :=
      compileFML_sim Γ locals idx L hL x next s hc.1 hb.1 hs
    simp only [hE₁] at hex₁ hr₁
    have hs₁ := StateEncML_mono hs hbd₁.1 hp₁ (by rw [hbf₁])
    obtain ⟨s₂, t₂, d₂, p₂, hex₂, hr₂, hp₂, hbf₂, hcp₂⟩ :=
      compileFML_sim Γ locals idx L hL y n₁ s₁ hc.2 hb.2 hs₁
    simp only [hE₂] at hex₂ hr₂
    have hrx : RegsEnc s₂ rx k (montVal k (FExpr.eval { env, locals, idx } x)) :=
      fun j hj => by rw [hp₂ _ (by omega)]; exact hr₁ j hj
    obtain ⟨s₃, t₃, d₃, p₃, hex₃, hr₃, hp₃, hbf₃, hcp₃⟩ :=
      eqLimbs_exec (C := C) (k := k) (a := rx) (b := ry) (w := n₂)
        (by omega) (by omega)
        (lt_trans (montVal_lt k _) hf.bound) (lt_trans (montVal_lt k _) hf.bound)
        hrx hr₂
    simp only [compileBML, hE₁, hE₂]
    refine ⟨s₃, _, _, _, .seq hex₁ (.seq hex₂ hex₃), ?_, ?_, ?_, ?_⟩
    · rw [hr₃]
      exact encB_montEq hf.two_lt _ _
    · intro q hq
      rw [hp₃ q (by omega), hp₂ q (by omega), hp₁ q hq]
    · rw [hbf₃, hbf₂, hbf₁]
    · rw [hcp₃, hcp₂, hcp₁]
  | .neq x y, next, s, hc, hb, hs => by
    simp only [BExpr.compilable, Bool.and_eq_true] at hc
    simp only [BExpr.envBound, Bool.and_eq_true] at hb
    have hΓ : Γ.length ≤ L := by rw [hL.1]; exact hs.size
    rcases hE₁ : compileUML k L x next with ⟨cx, rx, n₁⟩
    rcases hE₂ : compileUML k L y n₁ with ⟨cy, ry, n₂⟩
    have hbd₁ := compileUML_bounds k L hf.limbs_pos hΓ x next hc.1 hs.frame
    have hbd₂ := compileUML_bounds k L hf.limbs_pos hΓ y n₁ hc.2
      (Nat.le_trans hs.frame (by simp only [hE₁] at hbd₁; exact hbd₁.1))
    simp only [hE₁] at hbd₁
    simp only [hE₂] at hbd₂
    obtain ⟨s₁, t₁, d₁, p₁, hex₁, hr₁, hp₁, hbf₁, hcp₁⟩ :=
      compileUML_sim Γ locals idx L hL x next s hc.1 hb.1 hs
    simp only [hE₁] at hex₁ hr₁
    have hs₁ := StateEncML_mono hs hbd₁.1 hp₁ (by rw [hbf₁])
    obtain ⟨s₂, t₂, d₂, p₂, hex₂, hr₂, hp₂, hbf₂, hcp₂⟩ :=
      compileUML_sim Γ locals idx L hL y n₁ s₁ hc.2 hb.2 hs₁
    simp only [hE₂] at hex₂ hr₂
    simp only [compileBML, hE₁, hE₂]
    exact binW_glue hbd₁.2 hbd₂.1 hbd₁.1 hex₁ hex₂ hr₁ hr₂ (encB_ueq _ _)
      hp₁ hp₂ hbf₁ hbf₂ hcp₁ hcp₂
  | .lt x y, next, s, hc, hb, hs => by
    simp only [BExpr.compilable, Bool.and_eq_true] at hc
    simp only [BExpr.envBound, Bool.and_eq_true] at hb
    have hΓ : Γ.length ≤ L := by rw [hL.1]; exact hs.size
    rcases hE₁ : compileUML k L x next with ⟨cx, rx, n₁⟩
    rcases hE₂ : compileUML k L y n₁ with ⟨cy, ry, n₂⟩
    have hbd₁ := compileUML_bounds k L hf.limbs_pos hΓ x next hc.1 hs.frame
    have hbd₂ := compileUML_bounds k L hf.limbs_pos hΓ y n₁ hc.2
      (Nat.le_trans hs.frame (by simp only [hE₁] at hbd₁; exact hbd₁.1))
    simp only [hE₁] at hbd₁
    simp only [hE₂] at hbd₂
    obtain ⟨s₁, t₁, d₁, p₁, hex₁, hr₁, hp₁, hbf₁, hcp₁⟩ :=
      compileUML_sim Γ locals idx L hL x next s hc.1 hb.1 hs
    simp only [hE₁] at hex₁ hr₁
    have hs₁ := StateEncML_mono hs hbd₁.1 hp₁ (by rw [hbf₁])
    obtain ⟨s₂, t₂, d₂, p₂, hex₂, hr₂, hp₂, hbf₂, hcp₂⟩ :=
      compileUML_sim Γ locals idx L hL y n₁ s₁ hc.2 hb.2 hs₁
    simp only [hE₂] at hex₂ hr₂
    simp only [compileBML, hE₁, hE₂]
    exact binW_glue hbd₁.2 hbd₂.1 hbd₁.1 hex₁ hex₂ hr₁ hr₂ (encB_ult _ _)
      hp₁ hp₂ hbf₁ hbf₂ hcp₁ hcp₂
  | .flt x y, next, s, hc, hb, hs => by
    simp only [BExpr.compilable, Bool.and_eq_true] at hc
    simp only [BExpr.envBound, Bool.and_eq_true] at hb
    have hΓ : Γ.length ≤ L := by rw [hL.1]; exact hs.size
    rcases hE₁ : compileFML k L x next with ⟨cx, rx, n₁⟩
    rcases hE₂ : compileFML k L y n₁ with ⟨cy, ry, n₂⟩
    have hbd₁ := compileFML_bounds k L hf.limbs_pos hΓ x next hc.1 hs.frame
    have hbd₂ := compileFML_bounds k L hf.limbs_pos hΓ y n₁ hc.2
      (Nat.le_trans hs.frame (by simp only [hE₁] at hbd₁; exact hbd₁.1))
    simp only [hE₁] at hbd₁
    simp only [hE₂] at hbd₂
    obtain ⟨s₁, t₁, d₁, p₁, hex₁, hr₁, hp₁, hbf₁, hcp₁⟩ :=
      compileFML_sim Γ locals idx L hL x next s hc.1 hb.1 hs
    simp only [hE₁] at hex₁ hr₁
    have hs₁ := StateEncML_mono hs hbd₁.1 hp₁ (by rw [hbf₁])
    obtain ⟨s₂, t₂, d₂, p₂, hex₂, hr₂, hp₂, hbf₂, hcp₂⟩ :=
      compileFML_sim Γ locals idx L hL y n₁ s₁ hc.2 hb.2 hs₁
    simp only [hE₂] at hex₂ hr₂
    have hs₂ := StateEncML_mono hs₁ hbd₂.1 hp₂ (by rw [hbf₂])
    have hfr₂ : k + 3 + L * k ≤ n₂ := by
      have := hs₂.frame; simp only [tmpBase] at this; exact this
    have hrx : RegsEnc s₂ rx k (montVal k (FExpr.eval { env, locals, idx } x)) :=
      fun j hj => by rw [hp₂ _ (by omega)]; exact hr₁ j hj
    obtain ⟨s₃, t₃, d₃, p₃, hex₃, hr₃, hp₃, hbf₃, hcp₃⟩ :=
      leaveMont_field (C := C) (w := n₂) (a := rx) hf.limbs_pos hf.two_lt hf.bound
        hf.const hs₂.pre (by omega) (by omega) hrx
    have hpre₃ : PreludeEnc p pv k s₃ :=
      ⟨fun j hj => by rw [hp₃ _ (by omega)]; exact hs₂.pre.modulus j hj,
        by rw [hp₃ _ (by omega)]; exact hs₂.pre.const⟩
    have hry : RegsEnc s₃ ry k (montVal k (FExpr.eval { env, locals, idx } y)) :=
      fun j hj => by rw [hp₃ _ (by omega)]; exact hr₂ j hj
    obtain ⟨s₄, t₄, d₄, p₄, hex₄, hr₄, hp₄, hbf₄, hcp₄⟩ :=
      leaveMont_field (C := C) (w := n₂ + montMulConstFrame k) (a := ry)
        hf.limbs_pos hf.two_lt hf.bound hf.const hpre₃
        (by simp only [montMulConstFrame, montFrame]; omega)
        (by omega) hry
    have hxv : RegsEnc s₄ (montMulConstOut k n₂) k
        (ZMod.val (FExpr.eval { env, locals, idx } x)) := fun j hj => by
      rw [hp₄ _ (by
        have := montMulConstOut_le k n₂; simp only [montMulConstOut] at *; omega)]
      exact hr₃ j hj
    obtain ⟨s₅, t₅, d₅, p₅, hex₅, hr₅, hp₅, hbf₅, hcp₅⟩ :=
      ltLimbs_exec (C := C) (k := k) (a := montMulConstOut k n₂)
        (b := montMulConstOut k (n₂ + montMulConstFrame k))
        (w := n₂ + montMulConstFrame k + montMulConstFrame k)
        ⟨by have := montMulConstOut_le k n₂; omega,
          by have := montMulConstOut_le k (n₂ + montMulConstFrame k); omega⟩
        (lt_trans (ZMod.val_lt _) hf.bound) (lt_trans (ZMod.val_lt _) hf.bound)
        hxv hr₄
    simp only [compileBML, hE₁, hE₂]
    refine ⟨s₅, _, _, _,
      .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅))), ?_, ?_, ?_, ?_⟩
    · rw [hr₅]
      exact encB_valLt _ _
    · intro q hq
      rw [hp₅ q (by omega), hp₄ q (by omega), hp₃ q (by omega), hp₂ q (by omega),
        hp₁ q hq]
    · rw [hbf₅, hbf₄, hbf₃, hbf₂, hbf₁]
    · rw [hcp₅, hcp₄, hcp₃, hcp₂, hcp₁]
  | .bit x i, next, s, hc, hb, hs => by
    simp only [BExpr.compilable, Bool.and_eq_true] at hc
    have hΓ : Γ.length ≤ L := by rw [hL.1]; exact hs.size
    rcases hE₁ : compileFML k L x next with ⟨cx, rx, n₁⟩
    have hbd₁ := compileFML_bounds k L hf.limbs_pos hΓ x next hc.1 hs.frame
    simp only [hE₁] at hbd₁
    obtain ⟨s₁, t₁, d₁, p₁, hex₁, hr₁, hp₁, hbf₁, hcp₁⟩ :=
      compileFML_sim Γ locals idx L hL x next s hc.1 hb hs
    simp only [hE₁] at hex₁ hr₁
    have hs₁ := StateEncML_mono hs hbd₁.1 hp₁ (by rw [hbf₁])
    have hfr₁ : k + 3 + L * k ≤ n₁ := by
      have := hs₁.frame; simp only [tmpBase] at this; exact this
    obtain ⟨s₂, t₂, d₂, p₂, hex₂, hr₂, hp₂, hbf₂, hcp₂⟩ :=
      leaveMont_field (C := C) (w := n₁) (a := rx) hf.limbs_pos hf.two_lt hf.bound
        hf.const hs₁.pre (by omega) (by omega) hr₁
    obtain ⟨s₃, t₃, d₃, p₃, hex₃, hr₃, hp₃, hbf₃, hcp₃⟩ :=
      bitLimb_exec (C := C) (k := k) (a := montMulConstOut k n₁) (i := i)
        (w := n₁ + montMulConstFrame k)
        (by have := montMulConstOut_le k n₁; omega)
        (lt_trans (ZMod.val_lt _) hf.bound) hr₂
    simp only [compileBML, hE₁]
    refine ⟨s₃, _, _, _, .seq hex₁ (.seq hex₂ hex₃), ?_, ?_, ?_, ?_⟩
    · rw [hr₃]
      exact encB_bit _ _
    · intro q hq
      rw [hp₃ q (by omega), hp₂ q (by omega), hp₁ q hq]
    · rw [hbf₃, hbf₂, hbf₁]
    · rw [hcp₃, hcp₂, hcp₁]
  | .not b, next, s, hc, hb, hs => by
    have hΓ : Γ.length ≤ L := by rw [hL.1]; exact hs.size
    rcases hE₁ : compileBML k L b next with ⟨cb, rb, n₁⟩
    have hbd₁ := compileBML_bounds k L hf.limbs_pos hΓ b next hc hs.frame
    simp only [hE₁] at hbd₁
    obtain ⟨s₁, t₁, d₁, p₁, hex₁, hr₁, hp₁, hbf₁, hcp₁⟩ :=
      compileBML_sim Γ locals idx L hL b next s hc hb hs
    simp only [hE₁] at hex₁ hr₁
    simp only [compileBML, hE₁]
    refine ⟨_, _, _, _, .seq hex₁ .un, ?_,
      fun q hq => by
        rw [regs_setReg_ne _ _ (show q ≠ n₁ by omega), hp₁ q hq], ?_, ?_⟩
    · rw [regs_setReg_self]
      show (if s₁.regs rb = 0 then 1 else 0 : Word 64) = _
      rw [hr₁]
      exact encB_not _
    · rw [bufs_setReg, hbf₁]
    · rw [caps_setReg, hcp₁]
  | .and x y, next, s, hc, hb, hs => by
    simp only [BExpr.compilable, Bool.and_eq_true] at hc
    simp only [BExpr.envBound, Bool.and_eq_true] at hb
    have hΓ : Γ.length ≤ L := by rw [hL.1]; exact hs.size
    rcases hE₁ : compileBML k L x next with ⟨cx, rx, n₁⟩
    rcases hE₂ : compileBML k L y n₁ with ⟨cy, ry, n₂⟩
    have hbd₁ := compileBML_bounds k L hf.limbs_pos hΓ x next hc.1 hs.frame
    have hbd₂ := compileBML_bounds k L hf.limbs_pos hΓ y n₁ hc.2
      (Nat.le_trans hs.frame (by simp only [hE₁] at hbd₁; exact hbd₁.1))
    simp only [hE₁] at hbd₁
    simp only [hE₂] at hbd₂
    obtain ⟨s₁, t₁, d₁, p₁, hex₁, hr₁, hp₁, hbf₁, hcp₁⟩ :=
      compileBML_sim Γ locals idx L hL x next s hc.1 hb.1 hs
    simp only [hE₁] at hex₁ hr₁
    have hs₁ := StateEncML_mono hs hbd₁.1 hp₁ (by rw [hbf₁])
    obtain ⟨s₂, t₂, d₂, p₂, hex₂, hr₂, hp₂, hbf₂, hcp₂⟩ :=
      compileBML_sim Γ locals idx L hL y n₁ s₁ hc.2 hb.2 hs₁
    simp only [hE₂] at hex₂ hr₂
    simp only [compileBML, hE₁, hE₂]
    refine ⟨_, _, _, _, .seq hex₁ (.seq hex₂ .bin), ?_, ?_, ?_, ?_⟩
    · rw [regs_setReg_self]
      show BinOp.eval .and (s₂.regs rx) (s₂.regs ry) = _
      rw [hp₂ rx hbd₁.2, hr₁, hr₂]
      exact encB_and _ _
    · intro q hq
      rw [regs_setReg_ne _ _ (show q ≠ n₂ by omega), hp₂ q (by omega), hp₁ q hq]
    · rw [bufs_setReg, hbf₂, hbf₁]
    · rw [caps_setReg, hcp₂, hcp₁]

end

end Sim

end Caliper.MultiLimb
