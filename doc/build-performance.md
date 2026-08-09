# Build Performance

Where `lake build` time actually goes, how it was measured, and which levers were tried.
This is about whole-build throughput; for individual proofs that blow up, see
`doc/performance-problems.md`.

## Measurement setup

Reference machine: 4 cores, 15 GB RAM, Lean 4.32.2, Mathlib prebuilt from cache.
The benchmark is a full rebuild of the `Clean` library alone with a warm page cache:

```bash
rm -rf .lake/build/lib/lean/Clean .lake/build/ir/Clean
lake build
```

A *cold* first build after checkout is much slower (476 s here) purely because Mathlib's
~1800 oleans have to come off disk. Always compare warm-to-warm; run-to-run variance on
the warm benchmark is about 1 s.

Two tools carry most of the signal:

- **Per-module category breakdown.** `lake env lean -Dprofiler=true <file>` re-elaborates
  one module against prebuilt imports and prints `cumulative profiling times` — `import`,
  `simp`, `typeclass inference`, `type checking`, `interpretation`, … Running it over
  every module and summing the categories gives the global picture.
- **Instance-search attribution.** `lake env lean -Ddiagnostics=true
  -Ddiagnostics.threshold=400 <file>` prints which instances are used how often. This is
  what identifies a typeclass cascade; the profiler only says "typeclass inference".

`-Dtrace.profiler=true -Dtrace.profiler.output=<file>` gives a Firefox-profiler JSON with
per-tactic timings. Careful: with `Elab.async` on it sums per-thread durations, so the
totals are inflated (≈2.3× here) — the *relative* shares are meaningful, the absolute
seconds are not. Add `-DElab.async=false` when you need real CPU numbers for one module.

## Where the time goes

Summed over all 176 modules (job time, so ~4× the wall time on 4 cores):

| category | seconds | share |
|---|---|---|
| import | 255 | 24 % |
| simp | 230 | 22 % |
| typeclass inference | 216 | 21 % |
| tactic execution | 199 | 19 % |
| interpretation | 131 | 13 % |
| type checking (kernel) | 94 | 9 % |
| elaboration | 51 | 5 % |

The categories overlap — typeclass inference happens *inside* simp and tactic execution —
so they do not sum to 100 %.

The important structural facts:

- **There is no hotspot.** No tactic invocation in the whole library exceeds ~1 s. The
  cost is spread across ~200 proofs that are each individually reasonable.
- **The build is already compute-bound and near-perfectly parallel.** Total work is
  ~1040 s, the dependency critical path is ~206 s, so the theoretical floor on 4 cores is
  ~261 s — and the measured build is ~257 s. At 4 cores, one second of elaboration work
  saved is 0.25 s of wall clock; nothing is gained from restructuring the module graph.
  The critical path only becomes the binding constraint at 8+ cores.
- **`import` is per-process fixed cost.** Each of the 176 `lean` processes reloads the
  whole import closure: ~0.9 s for the `ZMod` floor, ~0.3 s for Clean's own modules.
  Since `F p = ZMod p`, `Mathlib.Data.ZMod.Basic` (1810 transitive modules) is the floor —
  Clean's closure is now within ~25 modules of it, so this line item is spent.
- **Peak RSS is the memory story.** Every `lean` process resides at ~2.7 GB, almost all of
  it the mapped import closure; with `-j4` that is ~11 GB. `LEAN_NUM_THREADS` trades this
  against time (see below).

## What was tried

Measured against a 270 s baseline.

| change | result |
|---|---|
| Trim `Mathlib.Analysis.Normed.Ring.Lemmas` / `Order.Star.Basic` / `Enumerative.Composition` | **270 s → 257 s**, peak RSS 12.0 → 10.9 GB |
| `NeZero p` instance at `priority := high` | 255 s / 257 s on two runs — inside the noise band, kept because it halves the `NeZero` instance-application count and is a one-word change |
| Move Clean's simprocs out of the default simp set (`simproc_decl`) | no change; breaks a proof that relied on `u64Wrap` firing under a plain `simp` |
| Batch `circuit_proof_start`'s six `dsimp only [...] at *` passes into two | **15 s slower** — one `dsimp` with a 4-name unfold set costs more per context traversal than four passes that mostly no-op |
| `precompileModules := true` on the `Clean` lib | not viable: Lake then compiles *all of Mathlib* to object files (17 807 jobs) |
| `LEAN_NUM_THREADS=1` | 594 s (2.3× slower), peak RSS 3.6 GB — most parallelism is Lean's in-process async elaboration, not Lake's `-j`. Useful only as a memory-pressure escape hatch |

Two dead ends worth not repeating: adding a broad Mathlib import "to make it work" costs
both import time *and* typeclass search (the removed `Analysis.Normed` import put
`NormedCommRing.toNormedRing` into the `NeZero` search cascade); and consolidating tactic
scripts is not automatically cheaper than letting cheap no-op passes run.

## If a bigger win is needed

The remaining blocks are import (irreducible given `ZMod`), and simp + typeclass inference.
For the latter, the diagnostics point at one specific cascade: a `NeZero ?n` goal drags in
`NeZero.of_gt'` → `Fin.completeLinearOrder` → the whole
`CompleteAtomicBooleanAlgebra`/`Frame`/`BiheytingAlgebra` hierarchy, ~25 instances per
goal, and there are ~600–1300 such goals in a single core module. Killing that cascade —
by having fewer `Fin`-numeral and `ZMod`-modulus goals reach instance search at all — is
the largest identified target that has not been attempted.
