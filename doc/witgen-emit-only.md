# Design note: emit-only witness generation

**Status: proposal, not implemented.** Captures a design discussion for later
consideration. Nothing in the current pipeline (`doc/caliper.md`) depends on it;
conversely, adopting it would restructure the witgen interfaces described there.

## The principle

The witness is an **output** of witness generation. An output should be *emitted*,
not read back: witgen should have a single output operation — `emit` — and no way to
access the witness vector it is producing. Whatever a later gadget needs from an
earlier one should be handed over through **named, typed values** (registers, structs,
gadget-level interfaces), not smuggled through indices into the output stream.

Under this principle, the witness vector is a write-only stream leaving the machine,
and inter-gadget dataflow is ordinary program dataflow.

## The current model, and why it looks the way it does

Today, a circuit's witness generators read the *environment*: generator at offset `n`
may read cells `< n` — the values emitted before it. This is a stream machine whose
internal state is the emitted prefix itself. Two forces produced this design:

1. **Composition for free.** Gadget inputs are wire indices into earlier cells; the
   shared trace is the calling convention. Independently verified gadget fragments
   compose with zero plumbing.
2. **In zk, hidden state is useless state.** Constraints see only trace cells, so any
   state the constraints must check ends up emitted anyway; making the prefix *be*
   the state avoids duplicating it and carrying a coherence invariant.

The cost of this convenience is the entire causality apparatus: `envBound` at
threaded offsets, `AgreesBelow`/`OnlyAccessedBelow`, `ComputableWitnesses`, and the
bridge lemmas connecting them — all of it exists solely to police read-back
(no forward references, well-defined sequential construction).

## The proposed model

- **`emit v`** is the only interaction with the witness output: append `v` to the
  output stream. In Caliper terms this is `memPush` into a **write-only** buffer —
  which is already how compiled generators treat their output buffer today. The only
  change is removing the *read* side (currently, reads of the environment buffer at
  the inter-generator interface).
- **Gadgets exchange state through typed interfaces.** A gadget is a function from
  typed inputs to typed outputs at generation time — exactly the shape the Caliper
  builder already uses (`Fp p → Build (Fp p)`, `PairBuf`, register-backed structs).
  The value a later gadget needs is *kept alive in a register/struct* from producer
  to consumer, under a name and a type, instead of being re-fetched by index from
  the output.
- **Whole-circuit witgen is one program**, assembled from gadget fragments by a
  compilation pass that performs liveness analysis / register allocation over the
  circuit's dataflow: every wire consumed later is assigned a local kept alive over
  its live range; everything else dies immediately after emission.

## What it buys

1. **Causality machinery dissolves by construction.** A program that cannot read the
   witness vector cannot read it out of order. `envBound`, offset threading,
   `ComputableWitnesses` and its bridge become unnecessary for emit-only programs —
   the checks, the proofs, and the per-circuit discharge obligations all vanish.
2. **A real memory story for large traces.** If the trace is only emitted, witgen
   never needs it resident: the stream can flow directly into its consumer (hash,
   commitment, file). Witgen's live memory becomes *its live locals only*, which for
   typical circuits is far below trace size. In the current model, memory is at
   least the environment buffer by construction. With Caliper's per-word allocation
   charge and `Exec.peak_le_time`, emit-only is the layout under which
   "witgen in small memory" is even statable — the peak bounds something genuinely
   small rather than trace-sized.
3. **Typed interfaces instead of index conventions.** Inter-gadget contracts become
   named types checked at generation time (the `Fp`/`Buf`/struct discipline the
   builder already enforces), rather than "cell `i₀ + 2k + 1` holds the carry" —
   the class of off-by-one wiring bugs that index-based composition invites.

## What it costs

1. **An assembler.** The trace-read model's free calling convention must be replaced
   by a computed one: liveness analysis and register allocation over the circuit's
   dataflow graph, assembling per-gadget fragments into one program. Mechanical, but
   it is a compiler pass whose output is what the cost theorems will be about.
2. **A new top-level equivalence obligation.** Correctness becomes: *the emitted
   stream equals the reference witness vector* (the concatenation of the per-op
   generators' outputs, i.e. `FlatOperation.localWitnesses`). This replaces — not
   augments — the per-generator obligations; it is one global simulation theorem for
   the assembled program, in the style of the existing `compile_sim`.
3. **Worst cases converge.** A gadget that needs a value from long ago forces the
   assembler to keep it alive the whole time; in the degenerate case the live set is
   the entire prefix and the environment buffer has been rebuilt under another name.
   Trace-read is exactly that degenerate strategy, made free because the output
   buffer exists anyway. The models diverge (in emit-only's favor) precisely when
   most values die young and the output need not be materialized — both typical for
   zk witgen. Structures with genuinely long-range or data-dependent access
   (permutation/grand-product-style passes, table lookups into earlier regions)
   are the stress test; they may warrant explicitly materialized, *named* scratch
   buffers — which is still the principle at work: state a gadget needs is state it
   owns, under a name, not a view into the output.
4. **Interface restructuring in Clean.** The circuit layer's witness story
   (`FlatOperation.witness` fragments read the shared environment; constraints and
   `UsesLocalWitnesses` reference the same cells) is built around the trace as the
   composition interface. Emit-only witgen would coexist with it as a *compilation
   target*: the read-back model stays the reference semantics, and the assembled
   emit-only program is proved to produce the same stream.

## Relation to the existing pipeline

The compiled Caliper artifact is already emit-only **per generator**: output goes
through `memPush` and is never read; intermediates live in registers; reads touch
only the environment buffer — i.e. read-back survives *only at the inter-generator
seam*. The planned whole-circuit compilation phase is therefore exactly the fork:

- **Conservative path:** merge output and environment buffers; later generators
  `memLoad` earlier emissions. Trivial to assemble; memory = trace size.
- **Emit-only path (this proposal):** keep the output write-only; thread
  inter-gadget values through an assembler-computed register map. Requires the
  liveness pass and the global equivalence theorem; memory = live locals.

A staged adoption is natural: implement the conservative path first (it reuses
`compile_sim` almost unchanged), then treat emit-only as an optimizing pass over it —
replace each environment read with the register that provably holds the same value,
with the replacement lemma (`memLoad` of cell `j` = register `r` under the assembler's
allocation invariant) as the only new proof content. Cost only improves (reads become
register references); memory improves from trace-sized to live-set-sized.

## Open questions

- **Hints and prover data** (`.hint`/`.data`): genuinely external inputs, not
  read-back — they remain input channels in either model, and remain outside the
  certified fragment.
- **Streaming interface:** what consumes `emit` — a buffer (current semantics), or a
  modeled sink with its own cost (e.g. a hash absorb per element)? The latter would
  let end-to-end prover phases (witgen → commitment) share one cost account.
- **Spill policy:** when the live set exceeds the register budget one is willing to
  certify, the assembler spills to named scratch buffers; the memory bound becomes
  `live registers + spill buffers`, still independent of trace length. Choosing and
  certifying the spill strategy is the main engineering freedom.
- **Circuit-layer ergonomics:** whether gadget authors ever see the difference, or
  the emit-only program is purely a back-end artifact derived from the existing
  circuit definitions (the likely answer: purely derived — authors keep writing
  circuits; the assembler and its theorem are invisible).
