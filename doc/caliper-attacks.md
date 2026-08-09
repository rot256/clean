# Attacking the Caliper cost model

An adversarial pass over `Clean/Caliper/`, asking one question: **how do I get a
machine-checked Caliper certificate that says an algorithm is much cheaper — in time
or in memory — than it really is?**

Every attack below is a *theorem*, not a bug in a proof. The Lean file
`Clean/Caliper/Attacks.lean` machine-checks the demonstrations; this document explains
the mechanism, rates the severity, and proposes a fix. The severity is about the gap
between the certificate and the physical resource, not about the internal consistency
of the formalism — which, as far as this pass could tell, is sound.

Two structural remarks first, because they frame everything else:

* Caliper's guarantee is a conditional: *if* the compilation contract holds (each
  `Stmt` instruction is O(1) machine operations, each reserved word is a machine
  word), *then* `t` and `p` bound real time and real memory. Every attack works by
  breaking a hypothesis of that contract while staying inside the formalism. The
  contract is prose (`doc/caliper.md`, "The compilation contract"), so nothing checks
  it.
* The certificates cover **buffer capacity** and **instruction counts** of the
  *emitted machine program*. Registers, code, the caller's memory, the word width,
  the environment's materialisation, and everything Lean actually runs today are
  outside the metric.

Summary:

| # | Attack | Resource | Severity |
|---|---|---|---|
| A1 | Registers are unmetered memory | space | high |
| A2 | `compile_space_le` ignores the emitted register file | space | high |
| A3 | Code size is unmetered memory | space | medium |
| A4 | The word width `w` is unbounded | time + space | high (core) |
| A5 | Peak is *growth*: let the caller pre-allocate | space | medium |
| B1 | `CostModel` has no sanity condition | time | high |
| B2 | `p ≤ t` rests on one unchecked field | space | high |
| B3 | `compile` never checks the single-word field condition | time | high |
| B4 | Preconditions need not be satisfiable | both | low |
| C1 | No backend: what runs today is `WitgenIR.eval` in Lean | both | high |
| C2 | Cost does not transfer along extensional equality | both | high |
| C3 | Environment materialisation is unpriced | both | medium |
| C4 | `hintGet`/`dataGet`, when added, move the work off-budget | time | high (future) |
| C5 | Per-witness-block sums are not prover time | time | medium |

---

## A. Space: what the memory metric does not see

### A1. Registers are unmetered memory — `n` live words at certified peak `0`

`Reg := ℕ`: a program may use unboundedly many registers, and *none of them is
memory*. `State.liveMem` sums reserved buffer capacities; the `d`/`p` indices of
`Exec` move only at `bufAlloc`/`bufAllocI`/`bufFree`. `Exec.allocFree_space` therefore
certifies `d ≤ 0 ∧ p ≤ 0` for **every** allocation-free program, no matter how much
live data it holds.

Demonstration (`Attacks.registers_are_free_memory`): a program that loads the first
`n` words of the input buffer into `n` distinct registers ends with all `n` values
live — the postcondition observes each of them, so no register allocator could
eliminate them — and its certified profile is `d ≤ 0 ∧ p ≤ 0`.

`Exec.peak_le_time` does not save this: the program's time is `2n`, and `0 ≤ 2n`. Nor
do the `WellFormed`/`liveMem` theorems, which are *about* `liveMem`, i.e. about
buffers.

This also weakens the framing of `Exec.peak_le_time` itself ("one certificate bounds
both resources"): the resource it bounds is buffer capacity, and any program can move
its working set into registers.

**Fix.** Registers are statically known, so the honest number is available: add a
syntactic `regFileSize` (`Attacks.lean` defines one for measurement) and either
(a) include it in `State.liveMem` and in the space judgments, or (b) state every
space claim as `regFileSize c + p` words, or (c) charge a `bufAlloc`-style per-register
cost by making the register bank an explicit, allocated resource. (a) is the honest
one; (b) is a one-line change to the user-facing corollaries and would already stop
the certificate from reading as a footprint.

### A2. The same hole inside the witgen pipeline

`compile_space_le` is stated as "code accepted by `compile` needs at most `m` words of
memory", with `m` the static output length. The emitted code keeps the program's
`L = steps.length` local values in registers `0 … L-1` and its temporaries from `L+1`
upward, so its real footprint is `m + L + O(expression depth)` words.

Demonstration (`Attacks.chainIR`): a witness program with 200 `let`-steps and **one**
output element compiles to code needing a **203-register** file, against a certified
peak of **one word**. The gap is unbounded in the program size; the time certificate
(606 steps) is honest, because time and code size coincide for straight-line code.

This is not hypothetical for real gadgets: `L` is the number of `let`-steps, which for
a hash round or a byte decomposition is in the tens to hundreds.

**Fix.** As A1; concretely, restate `compile_space_le` as
`p ≤ m` *plus* `regFileSize code = L + O(depth)`, or fold the register file into the
bound. The compiler already knows `L`.

### A3. Code size is unmetered memory

Generated code is instructions, and instructions live in memory. `mapRange`,
`envRange`, `bitsOf` and the Fermat inverse ladder are unrolled at generation time, so
code size grows with the static parameters; a program of `N` instructions has a
certified peak of `0` words. `doc/caliper.md` notes that generation-time staging is
unpriced *in time*; the space consequence is not stated. (Time is not affected: for
straight-line code, `staticTime` under the unit model *is* the instruction count.)

**Fix.** Report `Stmt` size next to `staticTime` in the user-facing summary, and say
in the space theorems that they bound *data* memory only.

### A4. The word width `w` is unbounded

`Word w := BitVec w`, and every cost is a function of the instruction alone —
`bin_cost_indep_of_width` is `rfl`. The core is generic in `w`; `Caliper64` is an
opt-in surface, not a restriction, and the "no bignum arithmetic can hide inside an
instruction" argument of the compilation contract is true only at `w = 64`.

Demonstrations:

* `wide_mul_in_one_step`: for every `n`, a program whose `staticTime?` is `some 1` and
  which multiplies two `n`-bit words. At `n = 2^20` that is a million-bit multiply for
  one tick. `udiv`/`umod`/`mulhi` are the same.
* `one_certified_word_holds_4096_bits`: a certified peak of `1` word storing an
  arbitrary 4096-bit value — 64 machine words. Every Caliper space certificate has to
  be multiplied by `w / 64` before it means anything physical.

This affects the general-purpose DSL, not the witgen pipeline (which pins `w = 64`).

**Fix.** Make the width part of the contract: give the contract-facing theorems a
`w ≤ 64` hypothesis, or state them only for `Caliper64`, or introduce a
`MachineWord w` class instantiated at `w = 64` that the cost interpretation requires.
A `w`-generic *semantics* is fine; a `w`-generic *cost claim* is not.

### A5. Peak is growth, so let the caller pay

`p` bounds live memory relative to the start state, and preconditions almost never pin
the start state's capacities. The headline `isZero_witgen_correct_140` constrains
`s.bufs 0` and says nothing about `s.caps`, so "peak memory 1 word" means "grows by at
most one word above whatever the caller was already holding".

Demonstration (`Attacks.caller_funded_memory`): a program that fills `n` words of
scratch space in a buffer whose capacity is a *precondition* has certified `d ≤ 0 ∧
p ≤ 0`. This is precisely the calling convention a real prover uses — allocate scratch
once, reuse it — so it is not a contrived attack.

**Fix.** State the headline space claims about the *absolute* footprint: either add
`s.liveMem B = 0` (or an explicit budget) to the precondition, or report
`liveMem s + p` rather than `p`. The `liveMem` machinery is already there; only the
user-facing statements need to use it.

---

## B. Time: what the cost model does not constrain

### B1. `CostModel` has no sanity condition

Every theorem is generic in `C : CostModel`, and `CostModel` is a bare record of
naturals. Nothing — no typeclass, no `Prop` field, no theorem hypothesis — requires an
entry to be positive.

Demonstration (`Attacks.isZero_witgen_zero_steps`): under `CostModel.zero`, the
headline witgen program runs in **0 steps**, by the same `compile_time_eq` that gives
140 under `CostModel.unit`. Both tables are equally well-formed.

The credibility of every quoted numeral therefore rests entirely on the *choice* of
table, which no theorem constrains and no check inspects.

**Fix.** Add `structure CostModel.Sane (C : CostModel) : Prop` requiring `1 ≤` each
entry, prove it for `.unit` and `.cycles`, and take it as a hypothesis in the
user-facing bound corollaries (`isZero_witgen_lt_2_40` and friends). Cheap, and it
turns "we chose a sane table" into a checked fact.

### B2. `p ≤ t` rests on one unchecked field

`Exec.peak_le_time` needs `1 ≤ C.allocPerWord` — a charge the documentation openly
calls an over-provision, since a real `malloc` reserves in O(1). Anyone who
"calibrates" the model toward reality by setting `allocPerWord := 0` silently loses
the theorem.

Demonstration (`Attacks.terabyte_in_one_step`): under `CostModel.freeMalloc` (the
uniform table with `allocPerWord := 0`), one instruction acquires `2^40` words in
**one** time step. A `t < 2^40` certificate then bounds nothing about memory.

Note the interaction with A1: even *with* `allocPerWord ≥ 1`, `p ≤ t` only bounds
buffer capacity, which a program can avoid using altogether.

**Fix.** Fold `1 ≤ allocPerWord` into `CostModel.Sane` (B1) so it cannot be dropped by
accident, and state in `doc/caliper.md` that `p ≤ t` is a consequence of a *deliberate
over-charge*, not of the machine's structure.

### B3. `compile` never checks the single-word field condition

The compiler's design point is a field with `p * p ≤ 2^w`, so that a field operation is
`imm p ;; op ;; umod` — three instructions. `compile`'s generation-time checks are
compilability, `envBound N`, `N ≤ 2^64` and `m < 2^64`. The field condition is **not**
among them. `doc/caliper.md` says the field conditions "cannot be decided at generation
time for a generic `FiniteField`", but `FiniteField.size F` is a plain `ℕ`, so
`p * p ≤ 2^64` is exactly as decidable as `m < 2^64`, which *is* checked. Only
primality genuinely needs to stay a hypothesis.

Demonstration (`Attacks.pOversized`, the smallest prime above `2^40`):

* `compile_accepts_oversized_field` — the checked entry accepts it;
* `#eval (compile 1 bigInvIR).map (·.staticTime CostModel.unit)` quotes **98** steps —
  *fewer* than the same program over 31-bit BabyBear (130), because the ladder length
  follows the Hamming weight of `p - 2`, not the width of `p`. On a real machine each
  of those multiplies needs a multi-limb product plus a reduction; for the 254/255-bit
  scalar fields of BN254 and BLS12-381 — and for Goldilocks, `2^64 - 2^32 + 1`, which
  also violates `p * p ≤ 2^64` — the quoted number under-states the truth by an order
  of magnitude or more;
* `bigDiff` (a differential test in the shape of the honest ones in
  `WitgenCompile.lean`) shows the compiled program returns **the wrong answer**:
  `938154445348` where the reference says `733007751861`. The cost certificate is
  unaffected: `compile_time_eq` has no field hypotheses at all.

So the trust boundary leaks in both directions: a wrong program gets a certified cost,
and the cost is quoted for arithmetic the machine cannot do.

**Fix.** Add `decide (FiniteField.size F * FiniteField.size F ≤ 2 ^ 64)` and
`decide (2 < FiniteField.size F)` to `compile`'s conditions. This is a two-line change
that moves everything except primality inside the checked entry point, and makes
`compile`'s acceptance imply the hypotheses of `compile_sim`.

### B4. Preconditions need not be satisfiable

`Triple C P c Q T D M` quantifies over states satisfying `P`; nothing asks for `P` to
be inhabited, so `Triple C (fun _ => False) c Q 0 0 0` holds for every program
(`Attacks.vacuous_triple`). Standard Hoare-logic hygiene, but worth a line in the
guide, since Caliper's triples are *resource* claims and the examples carry no
satisfiability lemmas.

**Fix.** Document the obligation; optionally ship a `Triple.nonvacuous` wrapper
bundling a witness `∃ s, P s`.

---

## C. Scope: what is priced is not what runs

This section is the answer to "what about native Lean witgen?".

### C1. There is no backend: the priced program is run by nobody

`doc/caliper.md` states this plainly ("No verified backend exists"), but the
consequence for the headline deserves to be spelled out. There are **three** witgen
execution engines in play, and the cost model describes none of them:

1. `WitgenIR.eval` — the Lean reference evaluator, which is what Clean itself runs;
2. the Rust witgen interpreter that consumes `Operations.witgenJson?`
   (`Clean/Circuit/WitnessExport.lean`) — the production path;
3. the Caliper `Stmt` program — the only one that carries a cost certificate, and the
   only one nothing executes.

The gap is not a constant factor. `WitgenIR.eval` walks the IR tree with an
`Array (F ⊕ UInt64)` of locals rather than `L` registers, computes field operations in
`ZMod p` (`Nat` arithmetic through GMP, with allocation, not `imm p ;; mul ;; umod`),
computes `.inv` as `ZMod`'s inverse — extended Euclid, *not* the 130-step Fermat
ladder the compiler emits and prices — and materialises `Vector`s for
`mapRange`/`bitsOf`. A tree-walking Rust interpreter over the exported JSON has its
own profile again, with per-node dispatch that the straight-line compiled form does
not have. The ratio to the certified number depends on `p`, on the IR's sharing
structure, and on the runtime's allocator.

So "witgen in 140 steps" is a property of a compilation target. Caliper's own
reference interpreter `run` is likewise explicitly not performance-realizing.

**Fix.** No proof can close this — a backend has to exist. What *can* be fixed is the
framing: say in `doc/caliper.md`'s headline (not only under "What is NOT proved")
which of the three engines the number describes, and that the other two are unmodelled.

### C2. Cost does not transfer along extensional equality

`compile` rejects `WitgenIR.native` closures outright (`Attacks.compile_native_none`),
so no cost theorem covers them — the pipeline is honest here. The trap is the shape of
the bridge that *does* exist: `onlyAccessedBelow_of_ir_equiv` transfers the *access*
property from a checked IR program to any closure extensionally equal to it. That is
correct (it is a statement about which cells are read), but extensional equality is
precisely the relation that preserves values and destroys costs.

Demonstration (`Attacks.slowIsZero`): a native closure that computes the `IsZeroField`
witness and then burns `2^k` steps satisfies the bridge's hypothesis for every `k`. A
"cost bridge" of the same shape would certify 140 steps for it.

The composite risk: a circuit may carry `.native` witnesses (`Circuit.witnessNative`),
discharge `ComputableWitnesses` through the bridge, and have no cost story at all —
while the surrounding prose reads "witgen in `< 2^40` steps, machine-checked". Today
Clean's gadgets use structured IR, so this is a live trap rather than a live bug.

**Fix.** A comment at `onlyAccessedBelow_of_ir_equiv` saying the hypothesis transfers
values only, and — if a `.native` cost story is ever wanted — a *refinement* relation
(the closure is implemented by the IR) rather than pointwise equality.

### C3. Environment materialisation is unpriced

The headline theorem's precondition is `EnvEnc env N envArr` with `s.bufs 0 = envArr`:
the whole environment is *assumed* to be sitting in buffer 0 as canonical 64-bit
words. Producing that array costs `N` conversions out of `F` (a Montgomery reduction
per cell in a real prover), and `ProverEnvironment.get` is an arbitrary Lean closure —
a lazily-recomputing environment satisfies `EnvEnc` just as well as an array-backed
one. All of it is outside the certificate, and `N` is the size of the whole witness,
so it is not a small constant.

**Fix.** State the input-encoding cost alongside the program cost, or make the
certificate cover a program that reads the environment through a priced interface.

### C4. `hintGet`/`dataGet`, when added, move the work off-budget

`doc/caliper.md` lists prover-data reads as deferred, "additional buffers/select-chains,
no new machinery". That is right for *compilation* and wrong for *cost*: a hint is an
oracle answer that the prover computed. Witnessing `x⁻¹` by hint is one buffer read;
the inversion still happened. Adding `hintGet` without an accompanying obligation on
the hint producer would make witgen cost arbitrarily under-reportable — this is the
standard way real provers move work around, and it would be the single easiest attack
on this model once the constructor is supported.

**Fix.** When `hintGet` lands, require a cost certificate for the hint-producing
program and add it to the total; or classify hint-reading programs as carrying an
explicit *unpriced oracle* marker that the total surfaces.

### C5. Per-witness-block sums are not prover time

`isZeroCircuit_total_witgen_time_unit` sums the circuit's two witness generators to
159 unit steps. That is a sum over `FlatOperation.witness` payloads; a prover's
witness-generation phase also builds lookup multiplicity tables, runs `interact`
operations, evaluates assertions during debugging, and assembles the trace.
`computableChecks` skips `.lookup`/`.interact` — correctly, for the computability
question — and nothing prices them.

**Fix.** Name the quantity precisely (`witness-generator time`, not "total witgen
time") and list the excluded phases where the total is stated.

---

## What holds up

Worth recording, since the point of an adversarial pass is also to say what resisted:

* The operational semantics is deterministic and the profile algebra is consistent;
  `Exec.deterministic`, `peak_nonneg`, `net_le_peak` and the frame rules survived
  attempts to find a rule that credits more than it charges.
* `State.WellFormed`/`liveMem` do close the phantom-capacity and hidden-storage holes
  they claim to close: `bufFree` cannot credit capacity that is not in the footprint,
  and `p` really is a high-water mark over every state an execution reaches — *for
  buffers*.
* `staticTime?` is a genuinely safe quoting API: it refuses to produce a number for
  branchy, loopy or dynamically-allocating code, and where it produces one, that number
  is exact.
* Charging allocation per word does close the "constant-time giant allocation" hole
  in the *time* counter, as claimed — subject to B2.
* The compiler's checked entry point does what it says about compilability, register
  layout and index widths; the differential tests and `compile_sim` are real. Its one
  gap is the field size (B3).

## Suggested order of work

1. **B3** — two lines in `compile`, closes a correctness *and* a cost hole.
2. **B1/B2** — `CostModel.Sane`, and use it in the headline corollaries.
3. **A1/A2** — put the register file into the space certificate (or into its
   statement); this is the largest quantitative gap.
4. **A4** — pin the width in the contract-facing theorems.
5. **A5, C1, C3, C5** — statement and documentation changes.
6. **C4** — a design constraint to fix *before* `hintGet` is implemented.
