import Clean.LowLevel.WitgenCompile
import Mathlib.FieldTheory.Finite.Basic

/-!
# Encodings and leaf lemmas for witgen compiler correctness

Phase 3a of the witgen compiler correctness proof: the **trusted encoding layer**.
This file contains no compiler induction — only

* the encodings relating IR-level values (`F p`, `UInt64`, `Bool`) to machine words,
* syntactic environment-bound checks mirroring `compilable`'s structure,
* the state-encoding relations that phases 3b/3c thread through the compiler induction,
* the pure specification of the generation-time bit decomposition `toBits`,
* Fermat's little theorem in the `x ^ (p - 2) = x⁻¹` form and the square-and-multiply
  ladder algebra, and
* `Exec`-level correctness lemmas for the three leaf gadget generators of
  `WitgenCompile.lean`: `fieldOp`, `selectCode` and `invLadder`.

Everything is at word size `w = 64` and `F = F p` for a prime `p` with
`p * p ≤ 2 ^ 64` (single-word moduli), matching the compiler's design point.
-/

namespace LowLevel.WitgenCompile

open Witgen

/-! ## Encodings -/

/-- The machine word of a u64 value: its bit pattern. -/
def encU (n : UInt64) : Word 64 := n.toBitVec

/-- The machine word of a condition: `1` for true, `0` for false. -/
def encB (b : Bool) : Word 64 := if b then 1 else 0

/-- The word of a u64 value reads back as its `toNat`. -/
theorem encU_toNat (n : UInt64) : (encU n).toNat = n.toNat := rfl

/-- A condition word is `1` (with the condition true) or `0` (with it false). -/
theorem encB_cases (b : Bool) : encB b = 1 ∧ b = true ∨ encB b = 0 ∧ b = false := by
  cases b <;> simp [encB]

section Encodings

variable {p : ℕ} [Fact p.Prime]

/-- The canonical machine word of a field element: its value `< p` as a 64-bit word. -/
def encF (x : F p) : Word 64 := BitVec.ofNat 64 x.val

/-- The machine word of a scalar local: field-sorted locals hold canonical words,
u64-sorted locals hold bit patterns. -/
def encLocal : F p ⊕ UInt64 → Word 64
  | .inl x => encF x
  | .inr n => encU n

/-- A single-word modulus fits in a word. -/
theorem p_lt_two_pow_64 (hpw : p * p ≤ 2 ^ 64) : p < 2 ^ 64 := by
  have h2 := (Fact.out : p.Prime).two_le
  nlinarith

/-- The canonical word of a field element reads back as its value. -/
theorem encF_toNat (hpw : p * p ≤ 2 ^ 64) (x : F p) : (encF x).toNat = x.val := by
  rw [encF, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (lt_trans (ZMod.val_lt x) (p_lt_two_pow_64 hpw))

/-- Distinct field elements have distinct canonical words. -/
theorem encF_injective (hpw : p * p ≤ 2 ^ 64) : Function.Injective (encF (p := p)) := by
  intro x y h
  have h' := congrArg BitVec.toNat h
  rw [encF_toNat hpw, encF_toNat hpw] at h'
  exact FieldUtils.ext h'

end Encodings

/-! ## Environment-bound checks

Syntactic, `Bool`-valued checks that every environment read (`Expression.var`,
`VExpr.envRange`) stays below `N`, mirroring the structure of `compilable`. The
constructors excluded by `compilable` (`listGet`/`dataGet`/`hintGet`, `native`)
return `false`. -/

section EnvBound

variable {F : Type}

/-- Environment-boundedness of a circuit expression: every `var` index is `< N`. -/
def Expression.envBound (N : ℕ) : Expression F → Bool
  | .var v => decide (v.index < N)
  | .const _ => true
  | .add x y => Expression.envBound N x && Expression.envBound N y
  | .mul x y => Expression.envBound N x && Expression.envBound N y

mutual

/-- Environment-boundedness of a field-sorted expression. -/
def FExpr.envBound (N : ℕ) : FExpr F → Bool
  | .expr e => Expression.envBound N e
  | .const _ => true
  | .localVar _ => true
  | .add x y | .mul x y => FExpr.envBound N x && FExpr.envBound N y
  | .inv x => FExpr.envBound N x
  | .ofU64 n => U64Expr.envBound N n
  | .ite c t e => BExpr.envBound N c && FExpr.envBound N t && FExpr.envBound N e
  | .listGet .. | .dataGet .. | .hintGet .. => false

/-- Environment-boundedness of a u64-sorted expression. -/
def U64Expr.envBound (N : ℕ) : U64Expr F → Bool
  | .const _ => true
  | .val x => FExpr.envBound N x
  | .idx => true
  | .localVar _ => true
  | .add x y | .mul x y | .div x y | .mod x y | .land x y | .lor x y | .lxor x y
  | .shiftL x y | .shiftR x y => U64Expr.envBound N x && U64Expr.envBound N y
  | .ite c t e => BExpr.envBound N c && U64Expr.envBound N t && U64Expr.envBound N e

/-- Environment-boundedness of a condition. -/
def BExpr.envBound (N : ℕ) : BExpr F → Bool
  | .true | .false => true
  | .feq x y | .flt x y => FExpr.envBound N x && FExpr.envBound N y
  | .neq x y | .lt x y => U64Expr.envBound N x && U64Expr.envBound N y
  | .bit x _ => FExpr.envBound N x
  | .not b => BExpr.envBound N b
  | .and x y => BExpr.envBound N x && BExpr.envBound N y

end

/-- Environment-boundedness of one `let`-step. -/
def Step.envBound (N : ℕ) : Step F → Bool
  | .letF e => FExpr.envBound N e
  | .letU e => U64Expr.envBound N e

/-- Environment-boundedness of a vector output expression. `envRange offset` reads
cells `offset .. offset + n - 1`, so it needs `offset + n ≤ N`. -/
def VExpr.envBound (N : ℕ) : {n : ℕ} → VExpr F n → Bool
  | _, .lit es => es.toList.all (FExpr.envBound N)
  | _, .mapRange _ body => FExpr.envBound N body
  | n, .envRange offset => decide (offset + n ≤ N)
  | _, .bitsOf x => FExpr.envBound N x
  | _, .append a b => VExpr.envBound N a && VExpr.envBound N b

/-- Environment-boundedness of a whole witness program. -/
def WitgenIR.envBound (N : ℕ) : {m : ℕ} → WitgenIR F m → Bool
  | _, .native _ => false
  | _, .ir steps out => steps.all (Step.envBound N) && VExpr.envBound N out

end EnvBound

/-! ## State-encoding relations

The invariants threaded through the compiler induction of phases 3b/3c. -/

section StateEncoding

variable {p : ℕ}

/-- The environment buffer encodes the first `N` cells of the reference environment:
cell `j` holds the canonical word of `env.get j`. -/
def EnvEnc (env : ProverEnvironment (F p)) (N : ℕ) (arr : Array (Word 64)) : Prop :=
  arr.size = N ∧ ∀ j, j < N → arr[j]! = encF (env.get j)

/-- The step-sort context matches the reference locals: same length, and each
position's sort agrees with the side of the sum the local lives in. -/
def LocalsMatch (Γ : List VSort) (locals : Array (F p ⊕ UInt64)) : Prop :=
  Γ.length = locals.size ∧
  ∀ i, (h : i < locals.size) →
    Γ[i]? = some (match locals[i] with | .inl _ => VSort.fld | .inr _ => VSort.u64)

/-- The machine state encodes the reference evaluation context: buffer `0` is the
environment, registers `< locals.size` hold the encoded locals, register `L` holds
the `mapRange` index, and temporaries live at `≥ next > L`. The step-sort context is
carried as a parameter (it constrains `locals` via `LocalsMatch` in phases 3b/3c) but
does not itself constrain the machine state. -/
def StateEnc (envArr : Array (Word 64)) (_Γ : List VSort) (locals : Array (F p ⊕ UInt64))
    (idx : ℕ) (L next : ℕ) (s : State 64) : Prop :=
  s.bufs 0 = envArr ∧ locals.size ≤ L ∧ L < next ∧
  (∀ i, (h : i < locals.size) → s.regs i = encLocal locals[i]) ∧
  s.regs L = BitVec.ofNat 64 idx

theorem EnvEnc_def (env : ProverEnvironment (F p)) (N : ℕ) (arr : Array (Word 64)) :
    EnvEnc env N arr ↔
      arr.size = N ∧ ∀ j, j < N → arr[j]! = encF (env.get j) := Iff.rfl

theorem LocalsMatch_def (Γ : List VSort) (locals : Array (F p ⊕ UInt64)) :
    LocalsMatch Γ locals ↔
      Γ.length = locals.size ∧
      ∀ i, (h : i < locals.size) →
        Γ[i]? = some (match locals[i] with | .inl _ => VSort.fld | .inr _ => VSort.u64) :=
  Iff.rfl

theorem StateEnc_def (envArr : Array (Word 64)) (Γ : List VSort)
    (locals : Array (F p ⊕ UInt64)) (idx : ℕ) (L next : ℕ) (s : State 64) :
    StateEnc envArr Γ locals idx L next s ↔
      s.bufs 0 = envArr ∧ locals.size ≤ L ∧ L < next ∧
      (∀ i, (h : i < locals.size) → s.regs i = encLocal locals[i]) ∧
      s.regs L = BitVec.ofNat 64 idx := Iff.rfl

end StateEncoding

/-! ## The `toBits` spec -/

/-- The little-endian value of a bit list — the inverse reading of `toBits`. -/
def ofBits : List Bool → ℕ
  | [] => 0
  | b :: bs => b.toNat + 2 * ofBits bs

theorem ofBits_append (l₁ l₂ : List Bool) :
    ofBits (l₁ ++ l₂) = ofBits l₁ + 2 ^ l₁.length * ofBits l₂ := by
  induction l₁ with
  | nil => simp [ofBits]
  | cons b l ih =>
    simp only [List.cons_append, ofBits, ih, List.length_cons, pow_succ]
    ring

/-- `toBits` is a correct binary expansion: reading its bits back gives the number. -/
theorem ofBits_toBits : ∀ n : ℕ, ofBits (toBits n) = n
  | 0 => by rw [toBits]; rfl
  | n + 1 => by
    rw [toBits, ofBits, ofBits_toBits ((n + 1) / 2)]
    rcases Nat.mod_two_eq_zero_or_one (n + 1) with h | h <;> simp [h] <;> omega
decreasing_by omega

/-! ## Fermat and the square-and-multiply ladder -/

/-- Fermat inverse: `x ^ (p - 2) = x⁻¹` for every `x`, including `0 ↦ 0`
(the witness IR's `inv` convention), provided `2 < p`. -/
theorem pow_card_sub_two {p : ℕ} [Fact p.Prime] (hp2 : 2 < p) (x : F p) :
    x ^ (p - 2) = x⁻¹ := by
  by_cases hx : x = 0
  · subst hx
    rw [zero_pow (show p - 2 ≠ 0 by omega), inv_zero]
  · apply eq_inv_of_mul_eq_one_left
    calc x ^ (p - 2) * x = x ^ (p - 1) := by rw [← pow_succ]; congr 1; omega
    _ = 1 := ZMod.pow_card_sub_one_eq_one hx

/-- The value computed by the MSB-first square-and-multiply ladder: one step per bit,
square then (for a set bit) multiply by the base — exactly the per-bit block that
`invLadder` emits. -/
def ladderVal {p : ℕ} (x : F p) : F p → List Bool → F p
  | acc, [] => acc
  | acc, b :: bs => ladderVal x (if b then acc ^ 2 * x else acc ^ 2) bs

/-- The ladder algebra: processing bits `bs` raises the accumulator to `2 ^ |bs|` and
multiplies in `x` to the little-endian value of the reversed bits. -/
theorem ladderVal_eq {p : ℕ} (x : F p) : ∀ (bs : List Bool) (acc : F p),
    ladderVal x acc bs = acc ^ 2 ^ bs.length * x ^ ofBits bs.reverse
  | [], acc => by simp [ladderVal, ofBits]
  | b :: bs, acc => by
    rw [ladderVal, ladderVal_eq x bs, List.reverse_cons, ofBits_append,
      List.length_reverse, List.length_cons, pow_succ,
      show ofBits [b] = b.toNat by simp [ofBits]]
    cases b <;> simp <;> ring

/-- The ladder over the (reversed, hence MSB-first) bits of `e`, started at `1`,
computes `x ^ e`. -/
theorem ladderVal_one_toBits {p : ℕ} (x : F p) (e : ℕ) :
    ladderVal x 1 ((toBits e).reverse) = x ^ e := by
  rw [ladderVal_eq, one_pow, one_mul, List.reverse_reverse, ofBits_toBits]

/-! ## Exec-level leaf-gadget lemmas

Correctness of the three leaf code generators, stated as raw `Exec` existentials
(phase 3b threads raw `Exec` derivations, not `Triple`s): the emitted code runs, the
result register holds the encoded result, registers below `next` (resp. other than the
accumulator) are untouched, and buffers and capacities are unchanged. -/

section LeafGadgets

variable {C : CostModel} {p : ℕ} [Fact p.Prime]

/-- `fieldOp .add`: from canonical operands in `a`, `b` (both `< next`), the result
register `next + 1` holds the canonical word of the field sum. -/
theorem fieldOp_exec_add (hpw : p * p ≤ 2 ^ 64) {a b next : ℕ}
    (ha : a < next) (hb : b < next) {s : State 64} {x y : F p}
    (hx : s.regs a = encF x) (hy : s.regs b = encF y) :
    ∃ s' t d pp, Exec C (fieldOp (w := 64) p .add a b next).1 s s' t d pp ∧
      s'.regs (next + 1) = encF (x + y) ∧
      (∀ q, q < next → s'.regs q = s.regs q) ∧
      s'.bufs = s.bufs ∧ s'.caps = s.caps := by
  have hxv := ZMod.val_lt x
  have hyv := ZMod.val_lt y
  have h2 := (Fact.out : p.Prime).two_le
  have hplt : p < 2 ^ 64 := p_lt_two_pow_64 hpw
  refine ⟨_, _, _, _, .seq .imm (.seq .bin .bin), ?_, ?_, rfl, rfl⟩
  · apply BitVec.eq_of_toNat_eq
    simp only [regs_setReg_self, BinOp.eval,
      regs_setReg_ne _ _ (show a ≠ next by omega),
      regs_setReg_ne _ _ (show b ≠ next by omega),
      regs_setReg_ne _ _ (show next ≠ next + 1 by omega),
      hx, hy, BitVec.toNat_umod, BitVec.toNat_add, BitVec.toNat_ofNat,
      encF_toNat hpw]
    rw [Nat.mod_eq_of_lt hplt,
      Nat.mod_eq_of_lt (show x.val + y.val < 2 ^ 64 by nlinarith), ZMod.val_add]
  · intro q hq
    rw [regs_setReg_ne _ _ (show q ≠ next + 1 by omega),
      regs_setReg_ne _ _ (show q ≠ next + 1 by omega),
      regs_setReg_ne _ _ (show q ≠ next by omega)]

/-- `fieldOp .mul`: from canonical operands in `a`, `b` (both `< next`), the result
register `next + 1` holds the canonical word of the field product. -/
theorem fieldOp_exec_mul (hpw : p * p ≤ 2 ^ 64) {a b next : ℕ}
    (ha : a < next) (hb : b < next) {s : State 64} {x y : F p}
    (hx : s.regs a = encF x) (hy : s.regs b = encF y) :
    ∃ s' t d pp, Exec C (fieldOp (w := 64) p .mul a b next).1 s s' t d pp ∧
      s'.regs (next + 1) = encF (x * y) ∧
      (∀ q, q < next → s'.regs q = s.regs q) ∧
      s'.bufs = s.bufs ∧ s'.caps = s.caps := by
  have hxv := ZMod.val_lt x
  have hyv := ZMod.val_lt y
  have h2 := (Fact.out : p.Prime).two_le
  have hplt : p < 2 ^ 64 := p_lt_two_pow_64 hpw
  refine ⟨_, _, _, _, .seq .imm (.seq .bin .bin), ?_, ?_, rfl, rfl⟩
  · apply BitVec.eq_of_toNat_eq
    simp only [regs_setReg_self, BinOp.eval,
      regs_setReg_ne _ _ (show a ≠ next by omega),
      regs_setReg_ne _ _ (show b ≠ next by omega),
      regs_setReg_ne _ _ (show next ≠ next + 1 by omega),
      hx, hy, BitVec.toNat_umod, BitVec.toNat_mul, BitVec.toNat_ofNat,
      encF_toNat hpw]
    rw [Nat.mod_eq_of_lt hplt,
      Nat.mod_eq_of_lt (show x.val * y.val < 2 ^ 64 by nlinarith), ZMod.val_mul]
  · intro q hq
    rw [regs_setReg_ne _ _ (show q ≠ next + 1 by omega),
      regs_setReg_ne _ _ (show q ≠ next + 1 by omega),
      regs_setReg_ne _ _ (show q ≠ next by omega)]

/-- `selectCode`: from a `{0, 1}` flag word in `flag` and arbitrary words in `ra`,
`rb` (all `< next`), the result register `next + 4` holds the selected word. -/
theorem selectCode_exec {flag ra rb next : ℕ}
    (_hf : flag < next) (ha : ra < next) (hb : rb < next) {s : State 64}
    {c : Bool} {v₁ v₂ : Word 64}
    (hc : s.regs flag = encB c) (h₁ : s.regs ra = v₁) (h₂ : s.regs rb = v₂) :
    ∃ s' t d pp, Exec C (selectCode (w := 64) flag ra rb next).1 s s' t d pp ∧
      s'.regs (next + 4) = (if c then v₁ else v₂) ∧
      (∀ q, q < next → s'.regs q = s.regs q) ∧
      s'.bufs = s.bufs ∧ s'.caps = s.caps := by
  refine ⟨_, _, _, _, .seq .un (.seq .un (.seq .bin (.seq .bin .bin))), ?_, ?_, rfl, rfl⟩
  · simp only [regs_setReg_self, UnOp.eval, BinOp.eval,
      regs_setReg_ne _ _ (show ra ≠ next by omega),
      regs_setReg_ne _ _ (show ra ≠ next + 1 by omega),
      regs_setReg_ne _ _ (show rb ≠ next by omega),
      regs_setReg_ne _ _ (show rb ≠ next + 1 by omega),
      regs_setReg_ne _ _ (show rb ≠ next + 2 by omega),
      regs_setReg_ne _ _ (show next ≠ next + 1 by omega),
      regs_setReg_ne _ _ (show next + 1 ≠ next + 2 by omega),
      regs_setReg_ne _ _ (show next + 2 ≠ next + 3 by omega),
      hc, h₁, h₂]
    cases c <;>
      simp [encB] <;>
      rw [show (18446744073709551615#64 : Word 64) = BitVec.allOnes 64 from rfl,
        BitVec.and_allOnes]
  · intro q hq
    rw [regs_setReg_ne _ _ (show q ≠ next + 4 by omega),
      regs_setReg_ne _ _ (show q ≠ next + 3 by omega),
      regs_setReg_ne _ _ (show q ≠ next + 2 by omega),
      regs_setReg_ne _ _ (show q ≠ next + 1 by omega),
      regs_setReg_ne _ _ (show q ≠ next by omega)]

/-- One multiply-reduce block of the Fermat ladder, appended to already-executed code
`c`: `acc ← acc * r mod p`. The operand register `r` may be `acc` itself (the squaring
step); only the modulus register must be distinct from `acc`. -/
theorem mulReduce_exec (hpw : p * p ≤ 2 ^ 64) {acc r tr : ℕ} (htr : tr ≠ acc)
    {c : Stmt 64} {s s₀ : State 64} {t₀ : ℕ} {d₀ p₀ : ℤ} {a u : F p}
    (hexec : Exec C c s s₀ t₀ d₀ p₀)
    (hacc : s₀.regs acc = encF a) (hr : s₀.regs r = encF u)
    (htv : s₀.regs tr = BitVec.ofNat 64 p) :
    ∃ s₁ t₁ d₁ p₁,
      Exec C (c ;; .bin .mul acc acc r ;; .bin .umod acc acc tr) s s₁ t₁ d₁ p₁ ∧
      s₁.regs acc = encF (a * u) ∧
      (∀ q, q ≠ acc → s₁.regs q = s₀.regs q) ∧
      s₁.bufs = s₀.bufs ∧ s₁.caps = s₀.caps := by
  have hav := ZMod.val_lt a
  have huv := ZMod.val_lt u
  have h2 := (Fact.out : p.Prime).two_le
  have hplt : p < 2 ^ 64 := p_lt_two_pow_64 hpw
  refine ⟨_, _, _, _, .seq hexec (.seq .bin .bin), ?_, ?_, rfl, rfl⟩
  · apply BitVec.eq_of_toNat_eq
    simp only [regs_setReg_self, BinOp.eval, regs_setReg_ne _ _ htr, hacc, hr, htv,
      BitVec.toNat_umod, BitVec.toNat_mul, BitVec.toNat_ofNat, encF_toNat hpw]
    rw [Nat.mod_eq_of_lt hplt,
      Nat.mod_eq_of_lt (show a.val * u.val < 2 ^ 64 by nlinarith), ZMod.val_mul]
  · intro q hq
    rw [regs_setReg_ne _ _ hq, regs_setReg_ne _ _ hq]

/-- The ladder invariant, over the fold that `invLadder` emits: extending an executed
prefix `c₀` by the per-bit blocks for `bs` multiplies the accumulator's encoded value
through `ladderVal`, touching no register but `acc`. -/
theorem invLadder_fold_exec (hpw : p * p ≤ 2 ^ 64) {acc xr tr : ℕ}
    (hax : xr ≠ acc) (hat : tr ≠ acc) (v : F p) (bs : List Bool) :
    ∀ {c₀ : Stmt 64} {s s₀ : State 64} {t₀ : ℕ} {d₀ p₀ : ℤ} {a₀ : F p},
      Exec C c₀ s s₀ t₀ d₀ p₀ →
      s₀.regs acc = encF a₀ → s₀.regs xr = encF v →
      s₀.regs tr = BitVec.ofNat 64 p →
      ∃ s' t d pp,
        Exec C (bs.foldl (fun c b =>
            let sq := c ;; .bin .mul acc acc acc ;; .bin .umod acc acc tr
            if b then sq ;; .bin .mul acc acc xr ;; .bin .umod acc acc tr else sq)
          c₀) s s' t d pp ∧
        s'.regs acc = encF (ladderVal v a₀ bs) ∧
        (∀ q, q ≠ acc → s'.regs q = s₀.regs q) ∧
        s'.bufs = s₀.bufs ∧ s'.caps = s₀.caps := by
  induction bs with
  | nil =>
    intro c₀ s s₀ t₀ d₀ p₀ a₀ hexec hacc hx ht
    exact ⟨s₀, t₀, d₀, p₀, hexec, hacc, fun _ _ => rfl, rfl, rfl⟩
  | cons b bs ih =>
    intro c₀ s s₀ t₀ d₀ p₀ a₀ hexec hacc hx ht
    obtain ⟨s₁, t₁, d₁, p₁, hexec₁, hacc₁, hpres₁, hbufs₁, hcaps₁⟩ :=
      mulReduce_exec hpw hat hexec hacc hacc ht
    have hacc₁' : s₁.regs acc = encF (a₀ ^ 2) := by rw [pow_two]; exact hacc₁
    have hx₁ : s₁.regs xr = encF v := (hpres₁ xr hax).trans hx
    have ht₁ : s₁.regs tr = BitVec.ofNat 64 p := (hpres₁ tr hat).trans ht
    cases b with
    | false =>
      obtain ⟨s', t', d', pp, hexec', hacc', hpres', hbufs', hcaps'⟩ :=
        ih hexec₁ hacc₁' hx₁ ht₁
      refine ⟨s', t', d', pp, hexec', hacc', ?_, ?_, ?_⟩
      · intro q hq; rw [hpres' q hq, hpres₁ q hq]
      · rw [hbufs', hbufs₁]
      · rw [hcaps', hcaps₁]
    | true =>
      obtain ⟨s₂, t₂, d₂, p₂, hexec₂, hacc₂, hpres₂, hbufs₂, hcaps₂⟩ :=
        mulReduce_exec hpw hat hexec₁ hacc₁' hx₁ ht₁
      obtain ⟨s', t', d', pp, hexec', hacc', hpres', hbufs', hcaps'⟩ :=
        ih hexec₂ hacc₂ ((hpres₂ xr hax).trans hx₁) ((hpres₂ tr hat).trans ht₁)
      refine ⟨s', t', d', pp, hexec', hacc', ?_, ?_, ?_⟩
      · intro q hq; rw [hpres' q hq, hpres₂ q hq, hpres₁ q hq]
      · rw [hbufs', hbufs₂, hbufs₁]
      · rw [hcaps', hcaps₂, hcaps₁]

/-- `invLadder` computes the Fermat power: from the base's canonical word in `xr`, the
modulus immediate in `tr` and the accumulator initialized to `1`, the accumulator ends
holding the canonical word of `x ^ (p - 2)`, and no other register changes. -/
theorem invLadder_exec_pow (hpw : p * p ≤ 2 ^ 64) {acc xr tr : ℕ}
    (hax : xr ≠ acc) (hat : tr ≠ acc) {s : State 64} {v : F p}
    (hacc : s.regs acc = encF (1 : F p)) (hx : s.regs xr = encF v)
    (ht : s.regs tr = BitVec.ofNat 64 p) :
    ∃ s' t d pp, Exec C (invLadder (w := 64) p acc xr tr) s s' t d pp ∧
      s'.regs acc = encF (v ^ (p - 2)) ∧
      (∀ q, q ≠ acc → s'.regs q = s.regs q) ∧
      s'.bufs = s.bufs ∧ s'.caps = s.caps := by
  obtain ⟨s', t, d, pp, hexec, hacc', hpres, hbufs, hcaps⟩ :=
    invLadder_fold_exec hpw hax hat v ((toBits (p - 2)).reverse)
      (Exec.skip (s := s)) hacc hx ht
  exact ⟨s', t, d, pp, hexec, by rw [hacc', ladderVal_one_toBits], hpres, hbufs, hcaps⟩

/-- `invLadder` computes the field inverse (with `0⁻¹ = 0`), by `invLadder_exec_pow`
and Fermat's little theorem. -/
theorem invLadder_exec_inv (hp2 : 2 < p) (hpw : p * p ≤ 2 ^ 64) {acc xr tr : ℕ}
    (hax : xr ≠ acc) (hat : tr ≠ acc) {s : State 64} {v : F p}
    (hacc : s.regs acc = encF (1 : F p)) (hx : s.regs xr = encF v)
    (ht : s.regs tr = BitVec.ofNat 64 p) :
    ∃ s' t d pp, Exec C (invLadder (w := 64) p acc xr tr) s s' t d pp ∧
      s'.regs acc = encF v⁻¹ ∧
      (∀ q, q ≠ acc → s'.regs q = s.regs q) ∧
      s'.bufs = s.bufs ∧ s'.caps = s.caps := by
  obtain ⟨s', t, d, pp, hexec, hacc', hpres, hbufs, hcaps⟩ :=
    invLadder_exec_pow hpw hax hat hacc hx ht
  rw [pow_card_sub_two hp2] at hacc'
  exact ⟨s', t, d, pp, hexec, hacc', hpres, hbufs, hcaps⟩

end LeafGadgets

end LowLevel.WitgenCompile
