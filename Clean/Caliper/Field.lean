import Clean.Caliper.Triple
import Clean.Caliper.Builder

/-!
# Generic prime-field arithmetic, from the modulus alone

`Fp w p` is a field element of `ZMod p` held canonically (value `< p`) in one
register. Everything below is generic in `p`: the modulus is a *generation-time* Lean
value, so it is baked into the emitted code as immediates, and derived constants —
here, the bits of `p - 2` for the Fermat inverse — are computed by ordinary Lean
evaluation while the code is being emitted. The machine never learns about fields.

The implementation is deliberately the simplest sound one: for any `p` with
`p * p ≤ 2 ^ w` (single-word moduli — BabyBear, Mersenne31, …), products don't wrap,
so reduction is the machine's native `umod` instruction. Consequences:

* **Cost is independent of `p`**: `add` and `mul` are exactly 3 instructions
  (`imm`, the ALU op, `umod`) for every modulus, and the specs say so literally.
* The raw `addCode`/`mulCode` `Stmt` values are straight-line and contain no
  allocation instructions at all, so they are constant-time (`straight_time_eq`)
  with a zero memory profile (`Stmt.AllocFree`, `allocFree_space`). The `Build`
  wrappers below (`Fp.add`/`Fp.mul`/`Fp.inv`) additionally *acquire* their
  registers — `freshReg` emits a priced `regAlloc` per register — and release the
  scratch at the scope boundary (`Build.scope` emits `regFree`), so the emitted
  gadget code is not `AllocFree`: it carries a scoped register lifecycle, net-zero
  for scratch, still straight-line and heap-free. See the Register-lifecycle
  paragraphs on the wrappers.
* `umod` is the expensive row of the cost table (`CostModel.cycles` prices it 30).
  A specialized field (Montgomery, or a Mersenne-style reduction) is a *better
  instance of the same interface*, not a different design — swap the gadget, keep
  the spec shape, bounds only improve.

Correctness specs (`addCode_spec`, `mulCode_spec`) relate machine registers to
`ZMod p` values: canonical inputs in, canonical outputs out — the same
assumptions/spec discipline as Clean's circuit layer, one level down. The Fermat
`inv` is provided as a code generator with an executable check; its correctness spec
is the standard exponentiation-ladder proof and is deferred.

Registers are parameters with explicit distinctness hypotheses; call sites with
builder-allocated (hence distinct) registers discharge them by `omega`/`decide`.
-/

namespace Caliper

variable {w : ℕ}

/-- A canonical element of `ZMod p` (value `< p`) in a register. The phantom `p`
prevents mixing elements of different fields at generation time. -/
structure Fp (w p : ℕ) where
  val : Reg

/-- A field element keeps its one value register live. -/
instance {p : ℕ} : RegCarrier (Fp w p) := ⟨fun x => [x.val]⟩

namespace Fp

/-! ## The gadgets

`t` is a scratch register for the modulus; it must be distinct from the operands and
the destination (`d` may alias `a` or `b` freely). -/

/-- `d ← (a + b) mod p`. Three instructions, any modulus. The witgen compiler's
`WitgenCompile.fieldOp` emits this same pattern (at `d := next + 1`, `t := next`),
kept separate there to remain `rfl`-transparent at a generic `BinOp`. -/
def addCode (p : ℕ) (d a b t : Reg) : Stmt w :=
  .imm t (BitVec.ofNat w p) ;;
  .bin .add d a b ;;
  .bin .umod d d t

/-- `d ← (a * b) mod p`. Three instructions, any modulus with `p * p ≤ 2 ^ w`.
Same pattern as `WitgenCompile.fieldOp` at `.mul` — see the note on `addCode`. -/
def mulCode (p : ℕ) (d a b t : Reg) : Stmt w :=
  .imm t (BitVec.ofNat w p) ;;
  .bin .mul d a b ;;
  .bin .umod d d t

/-! ## Specs

Canonical values are relayed through `ZMod.val`. The `p * p ≤ 2 ^ w` hypothesis is
what makes the unreduced sum/product wrap-free. -/

theorem addCode_spec {C : CostModel} {p : ℕ} (hp : 1 < p) (hpw : p * p ≤ 2 ^ w)
    {d a b t : Reg} (hta : t ≠ a) (htb : t ≠ b) (htd : t ≠ d) (x y : ZMod p) :
    Triple C (fun s => (s.regs a).toNat = x.val ∧ (s.regs b).toNat = y.val)
      (addCode (w := w) p d a b t)
      (fun s => (s.regs d).toNat = (x + y).val)
      (C.imm + (C.bin .add + C.bin .umod)) 0 0 := by
  haveI : NeZero p := ⟨by omega⟩
  intro s ⟨ha, hb⟩
  have hxv := ZMod.val_lt x
  have hyv := ZMod.val_lt y
  have hplt : p < 2 ^ w := by nlinarith
  refine ⟨_, _, _, _, .seq .imm (.seq .bin .bin), ?_, le_refl _, le_refl _, le_refl _⟩
  simp only [regs_setReg_self, BinOp.eval,
    regs_setReg_ne _ _ (Ne.symm hta), regs_setReg_ne _ _ (Ne.symm htb),
    regs_setReg_ne _ _ htd,
    BitVec.toNat_umod, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [ha, hb, Nat.mod_eq_of_lt hplt,
    Nat.mod_eq_of_lt (show x.val + y.val < 2 ^ w by nlinarith),
    (ZMod.val_add x y).symm]

theorem mulCode_spec {C : CostModel} {p : ℕ} (hp : 1 < p) (hpw : p * p ≤ 2 ^ w)
    {d a b t : Reg} (hta : t ≠ a) (htb : t ≠ b) (htd : t ≠ d) (x y : ZMod p) :
    Triple C (fun s => (s.regs a).toNat = x.val ∧ (s.regs b).toNat = y.val)
      (mulCode (w := w) p d a b t)
      (fun s => (s.regs d).toNat = (x * y).val)
      (C.imm + (C.bin .mul + C.bin .umod)) 0 0 := by
  haveI : NeZero p := ⟨by omega⟩
  intro s ⟨ha, hb⟩
  have hxv := ZMod.val_lt x
  have hyv := ZMod.val_lt y
  have hplt : p < 2 ^ w := by nlinarith
  refine ⟨_, _, _, _, .seq .imm (.seq .bin .bin), ?_, le_refl _, le_refl _, le_refl _⟩
  simp only [regs_setReg_self, BinOp.eval,
    regs_setReg_ne _ _ (Ne.symm hta), regs_setReg_ne _ _ (Ne.symm htb),
    regs_setReg_ne _ _ htd,
    BitVec.toNat_umod, BitVec.toNat_mul, BitVec.toNat_ofNat]
  rw [ha, hb, Nat.mod_eq_of_lt hplt,
    Nat.mod_eq_of_lt (show x.val * y.val < 2 ^ w by nlinarith),
    (ZMod.val_mul x y).symm]

/-! ## Builder interface

Fresh destination and scratch registers make the distinctness side conditions true
by construction at every call site. The raw `addCode`/`mulCode` (and their specs
above) take caller-provided registers and contain **no** `regAlloc`/`regFree` —
the register lifecycle lives entirely in these `Build` wrappers, which acquire
their registers through `freshReg` (emitting `regAlloc`) and release the internal
scratch through `Build.scope` (emitting `regFree`). -/

/-- `x + y` in `ZMod p`. Register lifecycle: acquires the modulus scratch `t` and
the destination `d` (`regAlloc t; regAlloc d`), emits the 3-instruction
`addCode`, and frees `t` at the end of the scope (`regFree t`); `d` — the result
register — stays live. Net one register. -/
def add {p : ℕ} (x y : Fp w p) : Build w (Fp w p) := Build.scope do
  let t ← Build.freshReg
  let d ← Build.freshReg
  Build.emit (addCode p d x.val y.val t)
  return ⟨d⟩

/-- `x * y` in `ZMod p`. Register lifecycle: as `Fp.add` — the modulus scratch `t`
is freed when the scope ends, only the result register `d` stays live. -/
def mul {p : ℕ} (x y : Fp w p) : Build w (Fp w p) := Build.scope do
  let t ← Build.freshReg
  let d ← Build.freshReg
  Build.emit (mulCode p d x.val y.val t)
  return ⟨d⟩

/-- `x⁻¹` in `ZMod p` by Fermat: `x ^ (p - 2)`, as a square-and-multiply ladder over
the bits of `p - 2`. For prime `p > 2` this matches the witness IR's convention
`0⁻¹ = 0` (the ladder multiplies by `x` at least once, so `0 ↦ 0`); at `p = 2` the
exponent is 0, the ladder is empty, and every input maps to 1 — the correctness
contract is scoped to `2 < p`.

The exponent bits are computed *by Lean at generation time* — the emitted code is
straight-line (`~2·log p` multiply/reduce steps, a per-field constant), so it is
constant-time by `straight_time_eq`. It is *not* allocation-free: the two
`freshReg` acquisitions below emit priced `regAlloc`s, and the scope's closing
`regFree` credits the scratch word back — the register lifecycle described below.
Correctness spec (the exponentiation-ladder argument, requiring `p` prime) is
deferred; `Examples.lean` checks it executably.

The witgen compiler has its own copy of this ladder, `WitgenCompile.invLadder`
(built over `WitgenCompile.toBits` rather than `Nat.bits`): that one carries the
correctness proof — `invLadder_exec_inv` in `WitgenSim.lean` — while this builder
version keeps the executable check only.

Register lifecycle: acquires the modulus scratch `t` and the accumulator `acc`
(the ladder itself works in place, no per-step temporaries); `t` is freed when
the scope ends, `acc` — the result — stays live. Net one register. -/
def inv {p : ℕ} (x : Fp w p) : Build w (Fp w p) := Build.scope do
  let t ← Build.var (Exp.lit (BitVec.ofNat w p))
  let acc ← Build.var 1
  for bit in (p - 2).bits.reverse do
    Build.assign acc ((acc : Exp w) * acc)
    Build.emit (.bin .umod acc acc t)
    if bit then
      Build.assign acc ((acc : Exp w) * x.val)
      Build.emit (.bin .umod acc acc t)
  return ⟨acc⟩

end Fp

end Caliper
