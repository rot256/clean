# Bounding witness generation with Caliper (`Clean/Caliper/`)

[**Caliper**](https://github.com/zksecurity/caliper) is a Lean DSL for reasoning
about the concrete running time and memory of algorithms: a deep-embedded
imperative language, modelled on RISC-V, whose every instruction runs in constant
time. Clean depends on it as a library (`require caliper` in `lakefile.lean`), and
this directory is the layer on top: **the compiler from Clean's witness-generation
IR (`Clean/Circuit/WitnessIR.lean`) to the Caliper machine, with the cost and
correctness theorems about what it emits.**

What that buys is the property the whole exercise is for: a witness generator
cannot secretly do expensive work. "This circuit's witness generation takes fewer
than `2^40` steps" becomes a machine-checked theorem about the compiled artifact,
so a generator that wanted to compute a discrete log, factor an RSA modulus, or
otherwise smuggle a super-polynomial computation into the prover has nowhere to
hide: either it compiles, and its step count is a certified constant you can read
off, or it does not compile at all.

Caliper itself — syntax, cost semantics (`Exec`), the `CostModel` tables and their
admissibility, the Hoare-triple program logic, the builder surface, the static
liveness/register analysis, the reference interpreter, and the trust boundary of
the whole model (`doc/caliper.md` in that repository) — is documented upstream and
is **not** restated here. Read that document for what "unit time" means and what
the model does and does not claim; read this one for the witgen pipeline built on
it.

## Files

| File | Contents |
|---|---|
| `Field.lean` | Generic prime-field arithmetic from the modulus alone (`Fp w p`): 3-instruction add/mul via the machine's native `umod`, with proved `ZMod`-correctness specs, and a Fermat inverse whose ladder is generated from the bits of `p - 2` at generation time. Also the `Caliper64.Fp` abbreviation and a BabyBear demo through the reference interpreter |
| `WitgenCompile.lean` | **Phase 1**: the witgen-IR → `Stmt` compiler (Expression/FExpr/U64Expr/BExpr, let-steps, VExpr), generic over `FiniteField`; straight-line by design (mask-select `ite`, unrolled `mapRange`/`envRange`/`bitsOf`); decidable `compilable`/`envBound`/field-size checks and the **checked entry point `compile`**; differential and trust-boundary regression tests against `WitgenIR.eval` at BabyBear; the headline program `testIsZero` is proved to be the witness IR extracted from `Gadgets.IsZeroField.circuit` (`isZeroCircuitIR_eq_testIsZero`); certified native witnesses compile as their IR reimplementation (`compile_certified_eq_ir`) |
| `WitgenCost.lean` | **Phase 2**: straightness/alloc-freeness of all compiled code; `compile_time_eq` (every execution takes *exactly* `staticTime`, hence `compile_time_data_independent`), the Option-valued static clock `witgenTime` (defined through `staticTime?`, so it cannot quote a number for loopy code), `compile_space_le` (buffer memory ≤ output length), the register footprint (`compile_total_footprint_le`, `compile_regPeak₀_le`) and concrete certified bounds: `isZero_witgen_lt_2_40` and the certified-native pins |
| `WitgenSim.lean` + `WitgenSimExpr.lean` + `WitgenSimIR.lean` | **Phase 3**: verified lowering, end to end — encodings (`encF`/`encU`/`encB`), state relations, Fermat-ladder correctness, the scalar-expression simulation theorems, and the program-level simulation `compile_sim`; on certified programs the equivalence transports this to the native closure itself (`compile_sim_certified`); combined with phase 2 in `isZero_witgen_correct_139` |
| `WitgenComputable.lean` | **The checks → circuit-layer bridge**: `compilable` + `envBound N` imply `ProverEnvironment.OnlyAccessedBelow N`, lifted per-offset to whole circuits (`circuit_computableWitnesses_of_checks`) so `Circuit.ComputableWitnesses` obligations discharge by one boolean evaluation |
| `TimedCircuit.lean` | **`TimedCircuit`: budgeted witgen as a type** — per-operation certified cost (`FlatOperation.witgenCost`), the offset-threaded whole-circuit fold (`FlatOperation.witgenTime`), its per-generator meaning theorem (`WitnessCosts`, `witgenTime_sound`, `WitnessCosts.forAll_exec`), and the `TimedCircuit` structure whose `witgen_bounded` obligation is one `native_decide` |

## The witgen pipeline: `witgen in < 2^N steps`, machine-checked

The end-to-end story the five `Witgen*` files deliver: a witness-generation program
in Clean's IR compiles to straight-line machine code that provably **computes the
right answer** and whose running time is a *syntactic constant* — the same number on
every input, computable by `#eval` and certified by evaluation. (That
data-independence is a statement about the abstract time counter; what it does and
does not say about side channels is spelled out in Caliper's own "What is NOT
proved".)

**The entry point** is `compile` (`WitgenCompile.lean`):

    compile (N : ℕ) (ir : WitgenIR F m) : Option (Stmt 64)

with `N` the environment size. It returns `some code` only when every
generation-time check passes — `ir` carries structured IR (a `.ir` program, or a
`.certified` program compiled as its IR reimplementation; bare `native` closures →
`none`), `WitgenIR.compilable ir` (no `listGet`/`dataGet`/`hintGet`, well-sorted
`localVar`s), `WitgenIR.envBound N ir` (every environment read below `N`), and
`N ≤ 2^64`, `m < 2^64` (environment indices and per-output-element immediates
survive their 64-bit encodings; the output buffer's capacity itself is a
`memAllocI` immediate — a bare `ℕ`, so the capacity *accounting* never wraps, while
`memLen` exactness on the output buffer needs the same `m < 2^64`), and the
field-size side conditions `2 < p` and `p * p ≤ 2^64` (the single-word-reduction
design point; the modulus `p = FiniteField.size F` is a generation-time value, so
both are decided right there) — and it computes the local-register count from the
program itself (`L := steps.length`), so no caller-supplied `L` can corrupt the
register layout. The raw compiler `compileIR` is internal and unchecked; it exists
as the object the proofs do induction over. All user-facing theorems are stated
about `compile`.

Of the field side conditions, only **primality** cannot be decided at generation
time (not at cryptographic sizes); it remains the `[Fact p.Prime]` hypothesis of the
correctness theorems. The size conditions are checked: a field outside the design
point — where the emitted single-`umod` reduction would overflow and return wrong
answers while the cost theorems still applied — is rejected outright. The
field-size rejection tests pin this: the ~40-bit prime `2^40 + 15`, Goldilocks
(`2^64 − 2^32 + 1`) and the BN254 scalar field all get `none` (`testIsZero40`,
`compile_goldilocks_none`, `compile_bn254_none`, `WitgenCompile.lean`), while
BabyBear (`p² ≈ 2^62`) passes — the positive control is every pinned BabyBear
number. Downstream, `compile … = some code` itself certifies `2 < p` and
`p * p ≤ 2^64` (`compile_size_checks`), so `compile_sim` and its corollaries no
longer ask callers to supply them.

The simulation is end to end: `compile_sim` (`WitgenSimIR.lean`) proves that for
every witness program the checked entry accepts, from any start state whose buffer
`0` encodes the environment, the compiled code has an execution ending with the
output buffer holding exactly the encoded reference output `WitgenIR.eval`
(elementwise canonical words). Because out-of-range buffer accesses have no `Exec`
derivation, that existence theorem is simultaneously a memory-safety proof; by
determinism, its costs and output are those of *every* execution.

Concretely, for the BabyBear `IsZeroField` witness, correctness and the phase-2 cost
bounds combine into the headline corollary

    theorem isZero_witgen_correct_139
        (henv : EnvEnc env N envArr) (hN0 : 0 < N) (hN : N ≤ 2 ^ 64)
        (hbuf : s.bufs 0 = envArr) :
        ∃ s' d pp, Exec .unit isZeroCompiled s s' 139 d pp ∧
          s'.bufs 1 = (Vector.map encF (testIsZero.eval env)).toArray ∧
          pp ≤ 1

— an execution computing the **correct encoded witness output** in **exactly 139
unit-cost steps** (2040 under the calibrated cycles table; both far below `2^40`,
see `isZero_witgen_correct_lt_2_40`) with **peak buffer memory 1 word**.

The witness program is not a hand-written fixture: Clean circuits embed their
witness generators structurally (each `witness` is a `FlatOperation.witness m ir`
carrying its `WitgenIR` payload), and `testIsZero` is the payload extracted from the
bundled circuit `Gadgets.IsZeroField.circuit` itself. `isZeroCircuitIR`
(`WitgenCompile.lean`) is that extraction — via `FlatOperation.witnessOperations` on
the circuit's flat operations at input `var ⟨0⟩` — and `isZeroCircuitIR_eq_testIsZero`
proves the two are definitionally equal (`rfl`), so the headline is a theorem about
the circuit's own witness program; the circuit-anchored statement is
`isZero_witgen_correct_139_circuit` (`WitgenSimIR.lean`). The circuit's only other
witness generator is the trivial `<==` copy for its output `b`;
`isZeroCircuit_witnessIRs` certifies these two are *all* of its witness operations
(the equality-assertion subcircuits carry none). That copy generator is priced too
(`isZeroCopyCompiled`, exactly 18 unit steps / 119 cycles), and
`isZeroCircuit_total_witgen_time_unit` (`WitgenCost.lean`) sums the two into
`139 + 18 = 157` unit steps with the `< 2^40` corollary
`isZeroCircuit_total_witgen_lt_2_40` — so the headline covers the circuit's complete
witness list.

Costs scale linearly in circuit size (each IR node compiles to O(1) instructions,
`mapRange n` to n copies of its body, field inverse to ~2·log p multiply-reduce
steps), so full-circuit witgen bounds are sums of per-gadget constants — evaluated,
not estimated. Exclusions: `.native` closures (not compilable, by construction — but
see "Certified native witnesses" below for the sanctioned way to keep a native
closure *and* get certified compilation), `listGet` computed-index reads (deferred
plumbing; additional buffers/select-chains, no new machinery), and
`dataGet`/`hintGet` prover-data reads — which are **not** deferred plumbing: pricing
hints is an open modeling question. A hint is unpriced oracle work, and relocating
cost into an oracle is the standard way provers move work off the books (compute a
value outside the priced path, have the priced path merely read it back). Admitting
a one-tick `hintGet` into a unit-cost table would let arbitrary computation hide
behind it; until hint provenance carries its own cost story, hints stay outside the
compilable fragment.

### Memory: buffers *and* registers

Caliper accounts memory in two summands (see `SpaceBound` upstream): the dynamic
buffer profile metered by `Exec`, plus the statically inferred peak register
pressure `Stmt.regPeak₀`. Quoting only the first would be a real understatement
here, because the compiler emits one register per IR let-step plus scratch — so
`compile_space_le`'s "≤ m words" is a *buffer* claim, not "the memory".

`WitgenCost.lean` closes that gap on the compiled code:

* `compile_regPeak₀_le` — the emitted code's inferred register peak is at most its
  live-ins plus its own static time, since compiled witgen code is straight-line;
* `compile_total_footprint_le` — buffer peak plus register peak is at most live-ins
  plus the *single* running time `t`, so one time certificate bounds the total
  footprint, not just the buffers;
* `compile_spaceBound` (`WitgenSimIR.lean`, where the simulation theorem supplies
  the execution a total-correctness `SpaceTriple` needs) — the packaged `SpaceBound`
  form, `m + code.regPeak₀` words.

For the headline program the register peak is pinned by evaluation
(`isZeroCompiled_regPeak₀ = 5`, live-ins `∅`), giving the concrete totals
`isZero_witgen_total_footprint_le_six` and `isZero_witgen_spaceBound`: the
`IsZeroField` witness program runs in **6 words of memory, total** — one output word
plus five live registers — where the buffers-only figure would have said 1.

The practical reading: a `< 2^40`-step witgen certificate is simultaneously a
`< 2^40`-word total-memory certificate.

### Certified native witnesses

`compile` rejects `WitgenIR.native` closures for a fundamental reason, not an
implementation gap: a cost bound is a claim about *how* a value is computed, but a
Lean function is only its input-output graph — functions are extensional, cost is
intensional. A "running time of this closure" is not even expressible, let alone
provable.

The sanctioned path for witnesses that want native Lean evaluation is a
**reimplementation in the IR plus a proof of equivalence**:
`WitgenIR.certified f steps out h` (smart constructor `WitgenIR.certify`;
provable-value form `WitgenIR.certifiedValue`, mirroring `nativeValue`) bundles

* the native closure `f` — kept as the evaluation fast path:
  `eval (certified f ..) = f` holds definitionally, so the Lean prover still runs
  the closure, never the IR interpreter;
* an IR reimplementation (`steps`, `out`, carried directly, so no nested-`WitgenIR`
  junk terms exist); and
* the equivalence proof `h : ∀ env, f env = (WitgenIR.ir steps out).eval env` — a
  pure-function lemma, typically by `funext`/`Vector.ext` plus `simp` over the
  evaluators.

Compilation, cost, export and the computability checks all go through the IR fields;
the equivalence transports each guarantee to the closure:

* **compilation** — `compile` accepts a certified program iff it accepts its IR
  reimplementation, and emits literally the same code (`compile_certified_eq_ir`,
  definitional);
* **cost** — `compile_time_eq`, `witgenTime`, `compile_space_le` apply unchanged:
  the certified program's step count is the syntactic constant of its IR's code;
* **correctness against the closure itself** — `compile_sim` is stated in terms of
  the IR reference semantics `WitgenIR.irEval` (definitionally `eval` on `.ir`
  programs); on a certified program the packed equivalence rewrites `irEval` to `f`,
  giving `compile_sim_certified`: the machine's output buffer provably holds the
  encoded output **of the native closure** — the guarantee a bare `.native f` can
  never have;
* **computability** — the decidable checks discharge
  `ProverEnvironment.OnlyAccessedBelow N f` for the bare closure
  (`onlyAccessedBelow_certified` / `onlyAccessedBelow_of_ir_equiv`), and
  `computableChecks` / `circuit_computableWitnesses_of_checks` accept certified
  witness operations for free;
* **export** — `#assert_exportable` / `#witgen_json` (`WitnessExport.lean`)
  serialize the IR reimplementation, which computes exactly what the closure the
  Lean prover runs computes.

To be blunt about what the equivalence proof transports: **access and output
properties, not cost**. The quoted time is the time of the *compiled artifact*; the
native closure's own Lean evaluation is unpriced, and nothing here bounds it. This
is a design rule, not an omission to be fixed: no cost-transfer analogue of
`onlyAccessedBelow_of_ir_equiv` must ever be added. The packed equivalence is
*extensional* — it constrains only the closure's input-output graph — while cost is
*intensional*: a slow closure extensionally equal to a fast IR satisfies exactly the
same equivalence proof, so any rule deriving a cost claim about the closure from the
equivalence would certify the slow closure too, i.e. would be unsound by
construction.

Worked instance, end to end: `isZeroNative` — the `IsZeroField` conditional-inverse
witness written as an ordinary Lean closure — is certified against `testIsZero`'s IR
program as `isZeroCertified` (`WitgenCompile.lean`, equivalence lemma
`isZeroNative_eq_testIsZero`). The differential test compares the machine against the
*closure*; `compile` emits `isZeroCompiled` with the pinned 139-unit-step /
2040-cycle cost (`compile_isZeroCertified`, `isZeroCertified_witgen_time_unit`,
`WitgenCost.lean`); the machine provably computes the closure's own output in exactly
139 steps with peak buffer memory ≤ 1 word (`isZeroCertified_witgen_correct_139`,
`WitgenSimIR.lean`); and `OnlyAccessedBelow 1 isZeroNative` discharges by
`native_decide` (`WitgenComputable.lean`).

Bare `.native` remains the visibly-uncertified escape hatch: `compile`, the export
commands and the computability checks all reject it, so an uncertified closure can
never silently acquire a cost claim.

## TimedCircuit: budgeted witgen as a type

`TimedCircuit.lean` turns the pipeline's cost story into a *type*: a
`TimedCircuit F Input Output` is a `FormalCircuit` that cannot be constructed
without a machine-checked bound on its witness-generation cost.

    structure TimedCircuit ... extends FormalCircuit F Input Output where
      costModel : CostModel := .unit
      witgenBudget : ℕ := 2 ^ 40
      witgen_bounded : underBudget costModel (size Input) witgenBudget
        ((main (varFromOffset Input 0)).operations (size Input)).toFlat = true

**The obligation is decidable.** `FlatOperation.witgenTime` folds
`FlatOperation.witgenCost` — `compile` followed by the honest partial clock
`staticTime?` — over the circuit's flat operations, threading the offset exactly like
`FlatOperation.localLength` and `computableChecks`: each generator is priced, and its
`envBound` checked, at its own accumulated offset. `underBudget` is one boolean, so at
a concrete circuit `witgen_bounded := by native_decide` (the default field tactic) is
the entire proof. `IsZeroField` upgrades to `isZeroTimed` this way, with pinned total
`139 + 18 = 157` unit steps.

**The number carries meaning.** `witgenTime_sound` reifies `witgenTime = some T` into
a per-generator certificate (`WitnessCosts`): every witness generator, at its own
offset, is accepted by `compile` with a static time `tᵢ`, and `Σ tᵢ = T`. Via the
phase-2/3 machinery, each certified `tᵢ` is the exact running time of every execution
of that generator's compiled code, with live-memory peak `≤ tᵢ`
(`WitnessCosts.forAll_exec`, citing `Exec.staticTime?_time_eq` and
`Exec.peak_le_time`), and `compile_sim` supplies the execution computing the encoded
reference output. `TimedCircuit.witgen_lt_budget` packages this: every generator of a
`TimedCircuit` runs in exactly its certified time, strictly below the budget.

**`.native` makes the type unattainable; `.certified` restores it.** `compile` rejects
bare native closures, so one uncertified witness poisons `witgenTime` to `none` and no
budget check can pass. Certifying the closure against an IR reimplementation
(`WitgenIR.certified`) re-admits it — and the cost certificate then applies to the very
closure the prover runs.

**Scope.** The obligation is stated at the canonical instantiation (fresh input
variables `varFromOffset Input 0`, witnesses from offset `size Input`): compiled cost
depends on the syntactic shape of embedded input expressions, so a single number
cannot cover arbitrary compound-expression instantiations. Future work:
input-congruence over variable-only instantiations, and whole-circuit sequential
composition — budgets already sum over composition by construction (the fold of an
append is the sum), but the composed machine-level run is not yet stated.

## What is NOT proved, on top of Caliper's own list

Caliper's `doc/caliper.md` states the machine's limits (no verified backend, the
`CostModel` is a parameter and not a fact about hardware, abstract states are
mathematical functions, generation-time staging is unpriced, and time
data-independence is not a side-channel proof). All of those apply here unchanged.
The Clean layer adds:

- **Only the compiled artifact is priced.** A `WitgenIR` program also has a Lean
  reference semantics (`WitgenIR.eval`) which the prover actually runs. The cost
  theorems price the Caliper program `compile` emits; the ratio between the two
  engines is not a constant, and `compile_sim` relates them only by *output*
  equality.
- **`.native` closures are unpriced by design**, as is the Lean evaluation of a
  `.certified` witness's closure. See "Certified native witnesses" above for why no
  cost-transfer rule may be added there.
- **`TimedCircuit` budgets are per-generator at the canonical instantiation**, not a
  whole-prover figure: the composed machine-level run over a circuit's whole witness
  list is not yet a single theorem (the per-generator sum is).
- **Hints and computed-index reads are excluded rather than priced.** A circuit whose
  witnesses use `hintGet`/`dataGet`/`listGet` gets no bound at all; it does not get a
  cheap one.
