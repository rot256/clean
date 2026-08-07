import Clean.Circuit.WitnessIR
import Clean.LowLevel.Core
import Clean.Utils.Primes

/-!
# Compiling the witness-generation IR to the unit-cost machine

This is the (unverified, for now) lowering from Clean's witness-generation IR
(`Clean/Circuit/WitnessIR.lean`) to the unit-cost machine (`Clean/LowLevel/Core.lean`).
The compiler is generic over `{F : Type} [FiniteField F]` and the word width `w`: the
modulus `p := FiniteField.size F` and every field constant are *generation-time* Lean
values, baked into the emitted code as immediates — exactly the `Fp` discipline of
`Clean/LowLevel/Field.lean`. The design targets single-word fields (`p * p ≤ 2 ^ w`),
so field reduction is the machine's native `umod` after each `add`/`mul`.

## Register and buffer layout

Given `L` = the number of `let`-steps of the program:

* registers `0 .. L-1` hold the values of steps `0 .. L-1` (the IR's `localVar`s),
* register `L` is the `mapRange` index register (`U64Expr.idx` reads it; it is `0`
  outside any `mapRange`),
* temporaries are allocated from `L+1` upward by explicit `next`-register threading,
* buffer `0` is the environment (input, pre-existing: cell `j` holds the canonical
  word of `env.get j`), buffer `1` is the output, allocated by the compiled program.

Values are represented as follows: field elements as their canonical word
`BitVec.ofNat w (FiniteField.val x)`, u64 values as the `UInt64` bit pattern
(truncation-free for `w ≥ 64`; the design value is `w = 64`), conditions as `{0, 1}`
words.

## Everything is straight-line

The emitted code contains no `ifNZ` and no `whileNZ`, anywhere:

* `ite` compiles *strictly* — condition, both branches, then a branch-free mask
  select (`mask ← -flag`; `r ← t &&& mask ||| e &&& ~~~mask`). This is sound because
  every IR operation is total.
* `VExpr.mapRange`, `VExpr.envRange` and `VExpr.bitsOf` are *unrolled*: their length
  is a static type index, so the compiler emits one copy of the body/read per
  element, setting the idx register `L` before each `mapRange` body instance and
  resetting it to `0` afterwards.
* `FExpr.inv` is Fermat's little theorem, `x ^ (p - 2)`, as a square-and-multiply
  ladder over the bits of `p - 2` — computed by Lean at generation time (`toBits`),
  so the ladder too is straight-line.

Consequently every compiled program is constant-time (`Exec.straight_time_eq`) and,
apart from the single output-buffer `bufAlloc`, allocation-free.

## Compilability

Not all of the IR is compilable: `FExpr.listGet`, `FExpr.dataGet`, `FExpr.hintGet`
(computed-index reads into expression lists / prover data, which have no
finite-buffer representation here yet) and `WitgenIR.native` (an arbitrary Lean
closure) are excluded. The compiler stays *total* on the syntax — excluded scalar
constructors compile to a dead `.imm r 0` — and a decidable `compilable` check
(against a context `Γ : List VSort` of step sorts, which also enforces that
`localVar` references are well-sorted) rules them out for the correctness theorem of
phase 3. `WitgenIR.native` makes `compileIR` return `none`.
-/

namespace LowLevel.WitgenCompile

open Witgen

variable {F : Type} {w : ℕ}

/-! ## Sorts and compilability -/

/-- The two scalar sorts of the witness IR: field-sorted and u64-sorted. -/
inductive VSort where
  | fld
  | u64
deriving DecidableEq, Repr

mutual

/-- Compilability (well-sortedness) of a field-sorted expression against the step-sort
context `Γ`. `listGet`/`dataGet`/`hintGet` are excluded (see the module docstring). -/
def FExpr.compilable (Γ : List VSort) : FExpr F → Bool
  | .expr _ => true
  | .const _ => true
  | .localVar i => Γ[i]? == some .fld
  | .add x y => FExpr.compilable Γ x && FExpr.compilable Γ y
  | .mul x y => FExpr.compilable Γ x && FExpr.compilable Γ y
  | .inv x => FExpr.compilable Γ x
  | .ofU64 n => U64Expr.compilable Γ n
  | .ite c t e => BExpr.compilable Γ c && FExpr.compilable Γ t && FExpr.compilable Γ e
  | .listGet .. => false
  | .dataGet .. => false
  | .hintGet .. => false

/-- Compilability of a u64-sorted expression against the step-sort context `Γ`. -/
def U64Expr.compilable (Γ : List VSort) : U64Expr F → Bool
  | .const _ => true
  | .val x => FExpr.compilable Γ x
  | .idx => true
  | .localVar i => Γ[i]? == some .u64
  | .add x y | .mul x y | .div x y | .mod x y | .land x y | .lor x y | .lxor x y
  | .shiftL x y | .shiftR x y => U64Expr.compilable Γ x && U64Expr.compilable Γ y
  | .ite c t e =>
    BExpr.compilable Γ c && U64Expr.compilable Γ t && U64Expr.compilable Γ e

/-- Compilability of a condition against the step-sort context `Γ`. -/
def BExpr.compilable (Γ : List VSort) : BExpr F → Bool
  | .true | .false => true
  | .feq x y | .flt x y => FExpr.compilable Γ x && FExpr.compilable Γ y
  | .neq x y | .lt x y => U64Expr.compilable Γ x && U64Expr.compilable Γ y
  | .bit x _ => FExpr.compilable Γ x
  | .not b => BExpr.compilable Γ b
  | .and x y => BExpr.compilable Γ x && BExpr.compilable Γ y

end

/-- The sort of the value a `let`-step produces. -/
def Step.sort : Step F → VSort
  | .letF _ => .fld
  | .letU _ => .u64

/-- Compilability of one `let`-step against the sorts of the previous steps. -/
def Step.compilable (Γ : List VSort) : Step F → Bool
  | .letF e => FExpr.compilable Γ e
  | .letU e => U64Expr.compilable Γ e

/-- Compilability of a step list: step `j` is checked against the sorts of steps
`0 .. j-1`, i.e. `Γ` grows as the list is traversed. -/
def stepsCompilable (Γ : List VSort) : List (Step F) → Bool
  | [] => true
  | s :: rest => Step.compilable Γ s && stepsCompilable (Γ ++ [Step.sort s]) rest

/-- Compilability of a vector output expression against the step-sort context `Γ`. -/
def VExpr.compilable (Γ : List VSort) : {n : ℕ} → VExpr F n → Bool
  | _, .lit es => es.toList.all (FExpr.compilable Γ)
  | _, .mapRange _ body => FExpr.compilable Γ body
  | _, .envRange _ => true
  | _, .bitsOf x => FExpr.compilable Γ x
  | _, .append a b => VExpr.compilable Γ a && VExpr.compilable Γ b

/-- Compilability of a whole witness program. `native` closures are not compilable. -/
def WitgenIR.compilable : {m : ℕ} → WitgenIR F m → Bool
  | _, .native _ => false
  | _, .ir steps out =>
    stepsCompilable [] steps && VExpr.compilable (steps.map Step.sort) out

/-! ## Generation-time bit decomposition

`toBits n` is the little-endian binary expansion of `n`, defined by plain binary
recursion so that phase 3 can state and prove its spec directly (deliberately *not*
`Nat.bits`). Used for the Fermat inverse ladder. -/

/-- Little-endian bits of a natural number (`toBits 0 = []`). -/
def toBits : ℕ → List Bool
  | 0 => []
  | n + 1 => ((n + 1) % 2 == 1) :: toBits ((n + 1) / 2)
decreasing_by omega

/-! ## Scalar compilation

All scalar compilers thread an explicit `next` free-register counter and return
`(code, resultReg, next')` with `next ≤ next'`, `resultReg < next'`, and the emitted
code writing only registers in `[next, next')`. Every node allocates its result
register fresh. -/

/-- `d ← (a ⟨op⟩ b) % p` with `d := next + 1` and the modulus immediate in
`t := next`: the single-word field reduction pattern of `Fp.addCode`/`Fp.mulCode`. -/
def fieldOp (p : ℕ) (op : BinOp) (a b : Reg) (next : Reg) : Stmt w × Reg × Reg :=
  (.imm next (BitVec.ofNat w p) ;;
     .bin op (next + 1) a b ;;
     .bin .umod (next + 1) (next + 1) next,
   next + 1, next + 2)

/-- Branch-free select of `t`/`e` (any words) by the `{0, 1}` flag `flag`:
`mask ← -flag` (all-ones or `0`), then `r ← (t &&& mask) ||| (e &&& ~~~mask)`. -/
def selectCode (flag t e : Reg) (next : Reg) : Stmt w × Reg × Reg :=
  (.un .neg next flag ;;
     .un .not (next + 1) next ;;
     .bin .and (next + 2) t next ;;
     .bin .and (next + 3) e (next + 1) ;;
     .bin .or (next + 4) (next + 2) (next + 3),
   next + 4, next + 5)

/-- Straight-line Fermat ladder: `acc ← acc ^ (p - 2) * ...` — precisely, MSB-first
square-and-multiply over the generation-time bits of `p - 2`, with `x` the base
register, `t` holding the modulus immediate, and `acc` initialized to `1` by the
caller. Every step reduces mod `p` via `umod`. -/
def invLadder (p : ℕ) (acc x t : Reg) : Stmt w :=
  (toBits (p - 2)).reverse.foldl (init := .skip) fun c b =>
    let sq := c ;; .bin .mul acc acc acc ;; .bin .umod acc acc t
    if b then sq ;; .bin .mul acc acc x ;; .bin .umod acc acc t else sq

variable [FiniteField F]

/-- Compile a circuit `Expression`: `var v` is a `bufGet` from the environment
buffer `0` at the static index `v.index`; `add`/`mul` reduce mod `p`. -/
def compileExpr (e : Expression F) (next : Reg) : Stmt w × Reg × Reg :=
  match e with
  | .var v =>
    (.imm next (BitVec.ofNat w v.index) ;; .bufGet (next + 1) 0 next,
     next + 1, next + 2)
  | .const c => (.imm next (BitVec.ofNat w (FiniteField.val c)), next, next + 1)
  | .add x y =>
    let (cx, rx, n₁) := compileExpr x next
    let (cy, ry, n₂) := compileExpr y n₁
    let (cop, r, n₃) := fieldOp (w := w) (FiniteField.size F) .add rx ry n₂
    (cx ;; cy ;; cop, r, n₃)
  | .mul x y =>
    let (cx, rx, n₁) := compileExpr x next
    let (cy, ry, n₂) := compileExpr y n₁
    let (cop, r, n₃) := fieldOp (w := w) (FiniteField.size F) .mul rx ry n₂
    (cx ;; cy ;; cop, r, n₃)

mutual

/-- Compile a field-sorted expression (canonical-word representation). `L` is the
number of `let`-steps: registers `< L` are locals, register `L` is the idx register.
The excluded constructors (`listGet`, `dataGet`, `hintGet`) compile to a dead
`.imm _ 0` to keep the compiler total; `compilable` rules them out. -/
def compileF (L : ℕ) : FExpr F → Reg → Stmt w × Reg × Reg
  | .expr e, next => compileExpr e next
  | .const c, next => (.imm next (BitVec.ofNat w (FiniteField.val c)), next, next + 1)
  | .localVar i, next => (.mov next i, next, next + 1)
  | .add x y, next =>
    let (cx, rx, n₁) := compileF L x next
    let (cy, ry, n₂) := compileF L y n₁
    let (cop, r, n₃) := fieldOp (w := w) (FiniteField.size F) .add rx ry n₂
    (cx ;; cy ;; cop, r, n₃)
  | .mul x y, next =>
    let (cx, rx, n₁) := compileF L x next
    let (cy, ry, n₂) := compileF L y n₁
    let (cop, r, n₃) := fieldOp (w := w) (FiniteField.size F) .mul rx ry n₂
    (cx ;; cy ;; cop, r, n₃)
  | .inv x, next =>
    let (cx, rx, n₁) := compileF L x next
    -- modulus in t := n₁, accumulator (result) in n₁ + 1, initialized to 1
    (cx ;; .imm n₁ (BitVec.ofNat w (FiniteField.size F)) ;;
       .imm (n₁ + 1) 1 ;; invLadder (FiniteField.size F) (n₁ + 1) rx n₁,
     n₁ + 1, n₁ + 2)
  | .ofU64 n, next =>
    let (cn, rn, n₁) := compileU L n next
    -- `fromNat` on values < 2^w ≡ reduction mod p (Nat.cast on prime fields)
    (cn ;; .imm n₁ (BitVec.ofNat w (FiniteField.size F)) ;;
       .bin .umod (n₁ + 1) rn n₁,
     n₁ + 1, n₁ + 2)
  | .ite c t e, next =>
    let (cc, rc, n₁) := compileB L c next
    let (ct, rt, n₂) := compileF L t n₁
    let (ce, re, n₃) := compileF L e n₂
    let (cs, r, n₄) := selectCode (w := w) rc rt re n₃
    (cc ;; ct ;; ce ;; cs, r, n₄)
  | .listGet .., next => (.imm next 0, next, next + 1)
  | .dataGet .., next => (.imm next 0, next, next + 1)
  | .hintGet .., next => (.imm next 0, next, next + 1)

/-- Compile a u64-sorted expression (the `UInt64` bit pattern as the word value).
u64 shifts mask the shift amount with `w - 1` first, matching `UInt64`'s mod-64
semantics (the machine's shifts zero out for amounts `≥ w`). -/
def compileU (L : ℕ) : U64Expr F → Reg → Stmt w × Reg × Reg
  | .const n, next => (.imm next (BitVec.ofNat w n.toNat), next, next + 1)
  | .val x, next =>
    -- the canonical word of `x` *is* the value (`val x < p ≤ 2 ^ w`)
    let (cx, rx, n₁) := compileF L x next
    (cx ;; .mov n₁ rx, n₁, n₁ + 1)
  | .idx, next => (.mov next L, next, next + 1)
  | .localVar i, next => (.mov next i, next, next + 1)
  | .add x y, next =>
    let (cx, rx, n₁) := compileU L x next
    let (cy, ry, n₂) := compileU L y n₁
    (cx ;; cy ;; .bin .add n₂ rx ry, n₂, n₂ + 1)
  | .mul x y, next =>
    let (cx, rx, n₁) := compileU L x next
    let (cy, ry, n₂) := compileU L y n₁
    (cx ;; cy ;; .bin .mul n₂ rx ry, n₂, n₂ + 1)
  | .div x y, next =>
    let (cx, rx, n₁) := compileU L x next
    let (cy, ry, n₂) := compileU L y n₁
    (cx ;; cy ;; .bin .udiv n₂ rx ry, n₂, n₂ + 1)
  | .mod x y, next =>
    let (cx, rx, n₁) := compileU L x next
    let (cy, ry, n₂) := compileU L y n₁
    (cx ;; cy ;; .bin .umod n₂ rx ry, n₂, n₂ + 1)
  | .land x y, next =>
    let (cx, rx, n₁) := compileU L x next
    let (cy, ry, n₂) := compileU L y n₁
    (cx ;; cy ;; .bin .and n₂ rx ry, n₂, n₂ + 1)
  | .lor x y, next =>
    let (cx, rx, n₁) := compileU L x next
    let (cy, ry, n₂) := compileU L y n₁
    (cx ;; cy ;; .bin .or n₂ rx ry, n₂, n₂ + 1)
  | .lxor x y, next =>
    let (cx, rx, n₁) := compileU L x next
    let (cy, ry, n₂) := compileU L y n₁
    (cx ;; cy ;; .bin .xor n₂ rx ry, n₂, n₂ + 1)
  | .shiftL x y, next =>
    let (cx, rx, n₁) := compileU L x next
    let (cy, ry, n₂) := compileU L y n₁
    (cx ;; cy ;; .imm n₂ (BitVec.ofNat w (w - 1)) ;;
       .bin .and (n₂ + 1) ry n₂ ;; .bin .shl (n₂ + 2) rx (n₂ + 1),
     n₂ + 2, n₂ + 3)
  | .shiftR x y, next =>
    let (cx, rx, n₁) := compileU L x next
    let (cy, ry, n₂) := compileU L y n₁
    (cx ;; cy ;; .imm n₂ (BitVec.ofNat w (w - 1)) ;;
       .bin .and (n₂ + 1) ry n₂ ;; .bin .shr (n₂ + 2) rx (n₂ + 1),
     n₂ + 2, n₂ + 3)
  | .ite c t e, next =>
    let (cc, rc, n₁) := compileB L c next
    let (ct, rt, n₂) := compileU L t n₁
    let (ce, re, n₃) := compileU L e n₂
    let (cs, r, n₄) := selectCode (w := w) rc rt re n₃
    (cc ;; ct ;; ce ;; cs, r, n₄)

/-- Compile a condition (`{0, 1}`-word representation). Note `BExpr.neq` is u64
*equality* (despite the name), so it compiles to `.eq` like `feq`. -/
def compileB (L : ℕ) : BExpr F → Reg → Stmt w × Reg × Reg
  | .true, next => (.imm next 1, next, next + 1)
  | .false, next => (.imm next 0, next, next + 1)
  | .feq x y, next =>
    let (cx, rx, n₁) := compileF L x next
    let (cy, ry, n₂) := compileF L y n₁
    (cx ;; cy ;; .bin .eq n₂ rx ry, n₂, n₂ + 1)
  | .neq x y, next =>
    let (cx, rx, n₁) := compileU L x next
    let (cy, ry, n₂) := compileU L y n₁
    (cx ;; cy ;; .bin .eq n₂ rx ry, n₂, n₂ + 1)
  | .lt x y, next =>
    let (cx, rx, n₁) := compileU L x next
    let (cy, ry, n₂) := compileU L y n₁
    (cx ;; cy ;; .bin .ult n₂ rx ry, n₂, n₂ + 1)
  | .flt x y, next =>
    -- canonical words compare like the `ℕ` values
    let (cx, rx, n₁) := compileF L x next
    let (cy, ry, n₂) := compileF L y n₁
    (cx ;; cy ;; .bin .ult n₂ rx ry, n₂, n₂ + 1)
  | .bit x i, next =>
    let (cx, rx, n₁) := compileF L x next
    (cx ;; .imm n₁ (BitVec.ofNat w i) ;; .bin .shr (n₁ + 1) rx n₁ ;;
       .imm (n₁ + 2) 1 ;; .bin .and (n₁ + 3) (n₁ + 1) (n₁ + 2),
     n₁ + 3, n₁ + 4)
  | .not b, next =>
    let (cb, rb, n₁) := compileB L b next
    (cb ;; .un .isZero n₁ rb, n₁, n₁ + 1)
  | .and x y, next =>
    let (cx, rx, n₁) := compileB L x next
    let (cy, ry, n₂) := compileB L y n₁
    (cx ;; cy ;; .bin .and n₂ rx ry, n₂, n₂ + 1)

end

/-! ## Program compilation -/

/-- Compile one `let`-step into register `j`: the step expression is compiled with
temporaries from `L + 1`, then the result is moved into the step's local register. -/
def compileStep (L : ℕ) (j : Reg) : Step F → Stmt w
  | .letF e =>
    let (c, r, _) := compileF (w := w) L e (L + 1)
    c ;; .mov j r
  | .letU e =>
    let (c, r, _) := compileU (w := w) L e (L + 1)
    c ;; .mov j r

/-- Compile the `let`-steps left to right, step `j` into register `j`. -/
def compileSteps (L : ℕ) (steps : List (Step F)) (j : ℕ) : Stmt w :=
  match steps with
  | [] => .skip
  | s :: rest => compileStep L j s ;; compileSteps L rest (j + 1)

/-- Compile a vector output: per element, compile (temporaries from `L + 1`) and
`bufPush` the result to the output buffer `1`. `mapRange`, `envRange` and `bitsOf`
are unrolled; `mapRange` sets the idx register `L` before each body instance and
resets it to `0` after the loop. -/
def compileV (L : ℕ) : {n : ℕ} → VExpr F n → Stmt w
  | _, .lit es =>
    es.toList.foldl (init := .skip) fun c e =>
      let (ce, r, _) := compileF (w := w) L e (L + 1)
      c ;; ce ;; .bufPush 1 r
  | _, .mapRange n body =>
    ((List.range n).foldl (init := .skip) fun c i =>
      let (cb, r, _) := compileF (w := w) L body (L + 1)
      c ;; .imm L (BitVec.ofNat w i) ;; cb ;; .bufPush 1 r) ;;
    .imm L 0
  | n, .envRange offset =>
    (List.range n).foldl (init := .skip) fun c i =>
      c ;; .imm (L + 1) (BitVec.ofNat w (offset + i)) ;;
        .bufGet (L + 2) 0 (L + 1) ;; .bufPush 1 (L + 2)
  | n, .bitsOf x =>
    let (cx, rx, n₁) := compileF (w := w) L x (L + 1)
    cx ;;
    (List.range n).foldl (init := .skip) fun c i =>
      c ;; .imm n₁ (BitVec.ofNat w i) ;; .bin .shr (n₁ + 1) rx n₁ ;;
        .imm (n₁ + 2) 1 ;; .bin .and (n₁ + 3) (n₁ + 1) (n₁ + 2) ;;
        .bufPush 1 (n₁ + 3)
  | _, .append a b => compileV L a ;; compileV L b

/-- Compile a whole witness program. Call with `L := steps.length`. The emitted code
allocates the output buffer `1` with capacity `m`, zeroes the idx register `L`,
computes the `let`-steps into registers `0 .. L-1`, then pushes the `m` output
elements. `native` closures are not compilable. -/
def compileIR (L : ℕ) {m : ℕ} : WitgenIR F m → Option (Stmt w)
  | .native _ => none
  | .ir steps out => some (
      .imm (L + 1) (BitVec.ofNat w m) ;;
      .bufAlloc 1 (L + 1) ;;
      .imm L 0 ;;
      compileSteps L steps 0 ;;
      compileV L out)

/-! ## Differential tests

Concrete runs at `w = 64`, `F = F pBabybear`, comparing the machine's output buffer
against the reference `WitgenIR.eval` elementwise (machine `toNat` vs
`FiniteField.val`). The environment is a small array, encoded for the machine as
buffer `0` of the start state. -/

section Tests

abbrev Fb := _root_.F pBabybear

/-- The test environment's variable assignment. -/
private def testRow : Array Fb := #[3, 5, 7, 0]

/-- Reference-side environment: `get` from `testRow`, no data, no hints. -/
private def testEnv : ProverEnvironment Fb where
  get j := testRow[j]?.getD 0
  data _ _ := #[]
  hint _ _ := #[]

/-- Machine-side start state: `testRow`'s canonical words in buffer `0`. -/
private def testState : State 64 where
  regs _ := 0
  bufs b := if b = 0 then testRow.map (fun x => BitVec.ofNat 64 (FiniteField.val x)) else #[]
  caps b := if b = 0 then testRow.size else 0

/-- The `L` (step count) to compile a test program with. -/
private def numSteps {m : ℕ} : WitgenIR Fb m → ℕ
  | .native _ => 0
  | .ir steps _ => steps.length

/-- Compile, run (fuel 100000), and return `(machine output, reference output)`,
both as lists of naturals — equality of the two components is the test. -/
private def diffOutputs {m : ℕ} (prog : WitgenIR Fb m) : Option (List ℕ) × List ℕ :=
  let machine : Option (List ℕ) := do
    let code ← compileIR (w := 64) (numSteps prog) prog
    let (s', _, _, _) ← run CostModel.unit 100000 code testState
    pure ((s'.bufs 1).toList.map (·.toNat))
  (machine, (prog.eval testEnv).toList.map FiniteField.val)

/-- Elementwise machine-vs-reference agreement. -/
private def diffOk {m : ℕ} (prog : WitgenIR Fb m) : Bool :=
  match diffOutputs prog with
  | (some ms, rs) => ms == rs
  | (none, _) => false

/-- Time cost of a compiled test program under the uniform cost model. -/
private def timeCost {m : ℕ} (prog : WitgenIR Fb m) : Option ℕ := do
  let code ← compileIR (w := 64) (numSteps prog) prog
  let (_, t, _, _) ← run CostModel.unit 100000 code testState
  pure t

/-- Test 1 — the `IsZeroField` witness shape: exercises `expr`, `const`, `feq`,
`ite` (mask select) and `inv` (Fermat ladder). `var ⟨0⟩ = 3`, so the output is
`3⁻¹ mod pBabybear = 1342177281`. -/
def testIsZero : WitgenIR Fb 1 :=
  .ir [] (.lit #v[.ite (.feq (.expr (var ⟨0⟩)) (.const 0)) (.const 0)
    (.inv (.expr (var ⟨0⟩)))])

/-- Test 2 — u64 xor of two environment variables: exercises `val`, `lxor`,
`ofU64`. `3 ^^^ 5 = 6`. -/
def testXor : WitgenIR Fb 1 :=
  .ir [] (.lit #v[.ofU64 (.lxor (.val (.expr (var ⟨0⟩))) (.val (.expr (var ⟨1⟩))))])

/-- Test 3 — one `letU` step (`var ⟨1⟩ + 1 = 6`) shared by two outputs via
`localVar`: exercises steps, the local registers, and field `add`. Output `[6, 7]`. -/
def testSteps : WitgenIR Fb 2 :=
  .ir [.letU (.add (.val (.expr (var ⟨1⟩))) (.const 1))]
    (.lit #v[.ofU64 (.localVar 0), .add (.ofU64 (.localVar 0)) (.const 1)])

/-- Test 4a — unrolled `bitsOf`: the 8 low bits of `var ⟨2⟩ = 7`. -/
def testBits : WitgenIR Fb 8 :=
  .ir [] (.bitsOf (.expr (var ⟨2⟩)))

/-- Test 4b — unrolled `mapRange` with the idx register: `i * i` for `i < 4`. -/
def testMapRange : WitgenIR Fb 4 :=
  .ir [] (.mapRange 4 (.ofU64 (.mul .idx .idx)))

/-- info: (some [1342177281], [1342177281]) -/
#guard_msgs in #eval diffOutputs testIsZero

/-- info: true -/
#guard_msgs in #eval diffOk testIsZero

/-- info: (some [6], [6]) -/
#guard_msgs in #eval diffOutputs testXor

/-- info: true -/
#guard_msgs in #eval diffOk testXor

/-- info: (some [6, 7], [6, 7]) -/
#guard_msgs in #eval diffOutputs testSteps

/-- info: true -/
#guard_msgs in #eval diffOk testSteps

/-- info: (some [1, 1, 1, 0, 0, 0, 0, 0], [1, 1, 1, 0, 0, 0, 0, 0]) -/
#guard_msgs in #eval diffOutputs testBits

/-- info: true -/
#guard_msgs in #eval diffOk testBits

/-- info: (some [0, 1, 4, 9], [0, 1, 4, 9]) -/
#guard_msgs in #eval diffOutputs testMapRange

/-- info: true -/
#guard_msgs in #eval diffOk testMapRange

/- The inv ladder dominates test 1's running time. -/
/-- info: some 140 -/
#guard_msgs in #eval timeCost testIsZero

/- All test programs pass the compilability check. -/
/-- info: true -/
#guard_msgs in #eval
  WitgenIR.compilable testIsZero && WitgenIR.compilable testXor &&
  WitgenIR.compilable testSteps && WitgenIR.compilable testBits &&
  WitgenIR.compilable testMapRange

end Tests

end LowLevel.WitgenCompile
