import Caliper.Triple
import Caliper.Builder
import Caliper.W64

/-!
# Prime-field arithmetic from the modulus alone

`Fp w p` holds an element of `ZMod p` canonically (value `< p`) in one register. The
modulus is a generation-time Lean value, baked into the emitted code as immediates;
derived constants, such as the bits of `p - 2` for the Fermat inverse, are computed
by Lean while emitting. The machine never learns about fields.

For `p * p ≤ 2 ^ w` (BabyBear, Mersenne31, …) products do not wrap, so reduction is
the machine's `umod`. `add` and `mul` are then 3 instructions for every modulus,
straight-line and allocation-free.

Registers are parameters with explicit distinctness hypotheses; call sites with
builder-allocated registers discharge them by `omega`/`decide`.
-/

namespace Caliper

variable {w : ℕ}

/-- A canonical element of `ZMod p` (value `< p`) in a register. The phantom `p`
prevents mixing elements of different fields at generation time. -/
structure Fp (w p : ℕ) where
  val : Reg

namespace Fp

/-! ## The gadgets

`t` is a scratch register for the modulus; it must be distinct from the operands and
the destination (`d` may alias `a` or `b` freely). -/

/-- `d ← (a + b) mod p`. `WitgenCompile.fieldOp` emits the same pattern, kept
separate there to stay `rfl`-transparent at a generic `BinOp`. -/
def addCode (p : ℕ) (d a b t : Reg) : Stmt w :=
  .imm t (BitVec.ofNat w p) ;;
  .bin .add d a b ;;
  .bin .umod d d t

/-- `d ← (a * b) mod p`, for `p * p ≤ 2 ^ w`. -/
def mulCode (p : ℕ) (d a b t : Reg) : Stmt w :=
  .imm t (BitVec.ofNat w p) ;;
  .bin .mul d a b ;;
  .bin .umod d d t

/-! ## Specs

`p * p ≤ 2 ^ w` is what makes the unreduced sum/product wrap-free. -/

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

Fresh registers make the distinctness side conditions true by construction. -/

/-- `x + y` in `ZMod p`. -/
def add {p : ℕ} (x y : Fp w p) : Build w (Fp w p) := do
  let t ← Build.freshReg
  let d ← Build.freshReg
  Build.emit (addCode p d x.val y.val t)
  return ⟨d⟩

/-- `x * y` in `ZMod p`. -/
def mul {p : ℕ} (x y : Fp w p) : Build w (Fp w p) := do
  let t ← Build.freshReg
  let d ← Build.freshReg
  Build.emit (mulCode p d x.val y.val t)
  return ⟨d⟩

/-- `x⁻¹` in `ZMod p` by Fermat: `x ^ (p - 2)` as a square-and-multiply ladder over
the bits of `p - 2`, computed by Lean at generation time. Scoped to `2 < p`: there
the ladder multiplies by `x` at least once, matching the witness IR's `0⁻¹ = 0`,
while at `p = 2` the exponent is 0 and every input maps to 1.

Unproved. The compiler's own ladder `WitgenCompile.invLadder` is the one carrying a
correctness proof (`invLadder_exec_inv`, `WitgenSim.lean`); this version is checked
only by the demo below. -/
def inv {p : ℕ} (x : Fp w p) : Build w (Fp w p) := do
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

/-! ## Fixed 64-bit surface

The field addendum to `Caliper.W64`, which pins `w := 64` for the machine's types. -/

namespace Caliper64

abbrev Fp (p : ℕ) := Caliper.Fp 64 p

end Caliper64

/-! ## Demo

At BabyBear: compute `5⁻¹` via the generated ladder, then multiply back. -/

namespace Caliper.FieldDemo

open Caliper

def babybear : ℕ := 2 ^ 31 - 2 ^ 27 + 1

def fieldDemo : Option (Word 64 × Word 64 × ℕ) :=
  let (rs, prog) := Build.build (w := 64) do
    let x : Fp 64 babybear := ⟨← Build.var 5⟩
    let xi ← Fp.inv x
    let chk ← Fp.mul xi x
    return (xi.val, chk.val)
  (run .unit 10000 prog (State.init 64)).map fun (s, t, _, _) =>
    (s.regs rs.1, s.regs rs.2, t)

/-- info: some (1610612737#64, 1#64, 128) -/
#guard_msgs in
#eval fieldDemo

end Caliper.FieldDemo
