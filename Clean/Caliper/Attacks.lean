import Clean.Caliper.Triple
import Clean.Caliper.WitgenCost
import Clean.Caliper.WitgenComputable

/-!
# Attacks on the Caliper cost model

An adversarial pass over `Clean/Caliper/`: **machine-checked demonstrations that a
Caliper time or memory certificate can be much smaller than the resources the
algorithm really needs.**

Every theorem below is a genuine theorem — nothing here is a bug in a proof. That is
the point: each one is an *honest* consequence of the definitions and a *dishonest*
description of reality. The gap always lives in the informal bridge between the
model and a machine ("the compilation contract" of `doc/caliper.md`), which is
exactly where a cost model can be attacked.

The companion write-up, with severities and suggested fixes, is
`doc/caliper-attacks.md`.

Index:

1. `§1` — the word width `w` is unbounded: one unit step per arbitrarily wide
   multiply, and one certified "word" of memory per arbitrarily wide value.
2. `§2` — the register file is unmetered memory: `n` live words at certified peak `0`.
3. `§3` — the same at the witgen layer: `compile`'s space certificate ignores the
   `L` local registers the emitted code allocates.
4. `§4` — `CostModel` has no sanity condition: the headline witgen program "runs in
   0 steps" under a legal table, and `Exec.peak_le_time` is bought by a single
   unchecked field.
5. `§5` — peak is *growth*: make the caller pre-allocate the scratch space and the
   certificate reads 0.
6. `§6` — nothing demands a satisfiable precondition.
7. `§7` — the checked entry point `compile` never checks the field size, so it
   prices (and mis-compiles) fields far outside its single-word design point.
8. `§8` — cost never transfers along extensional equality, which is exactly how the
   native-closure bridge is shaped.
-/

namespace Caliper.Attacks

open Caliper Caliper.WitgenCompile Witgen

/-! ## §1 The word width is unbounded

`Word w := BitVec w` and every cost is a function of the *instruction*, never of
`w`. The core is generic in `w`; only the witgen backend pins `w = 64`, and
`Caliper64` is an opt-in surface, not a restriction. So every "unit time" theorem
holds verbatim for arbitrarily wide words. -/

/-- The cost of an ALU instruction does not mention the word width — the cost table
is indexed by `BinOp` alone. -/
theorem bin_cost_indep_of_width (C : CostModel) (op : BinOp) (w : ℕ) (d a b : Reg) :
    (Stmt.bin op d a b : Stmt w).staticTime C = C.bin op := rfl

/-- **A multiply of two `n`-bit integers in one certified unit step**, for every `n`.
`staticTime?` — the *safe* way to quote a static time — returns `some 1`, so by
`Exec.staticTime?_time_eq` every execution takes exactly one time unit. At `n = 2^20`
this is a million-bit multiplication priced at one tick.

`udiv`/`umod` (`CostModel.cycles` prices them at 30) and `mulhi` are the same
story. -/
theorem wide_mul_in_one_step (n : ℕ) :
    ∃ c : Stmt n, c.staticTime? CostModel.unit = some 1 ∧
      ∀ s : State n, Exec CostModel.unit c s (s.setReg 2 (s.regs 0 * s.regs 1)) 1 0 0 :=
  ⟨.bin .mul 2 0 1, rfl, fun _ => .bin⟩

/-- **One certified word of memory holds an arbitrarily wide value.** `State.liveMem`
counts reserved *words*, and a word is `w` bits, so a peak of `1` at `w = 4096` is
512 bytes — 64 machine words — of physical footprint. Multiply any Caliper space
certificate by `w / 64` before believing it.

The program allocates one word, stores an arbitrary 4096-bit value in it, and its
certified peak is `1`. -/
theorem one_certified_word_holds_4096_bits (x : Word 4096) :
    ∃ (s' : State 4096) (t : ℕ) (d p : ℤ),
      Exec CostModel.unit (.imm 0 x ;; .bufAllocI 1 1 ;; .bufPush 1 0)
        (State.init 4096) s' t d p ∧
      p = 1 ∧ s'.bufs 1 = #[x] := by
  refine ⟨_, _, _, _, .seq .imm (.seq .bufAllocI (.bufPush ?_)), ?_, ?_⟩
  · simp [State.init, State.allocBuf, State.setReg]
  · simp [State.init]
  · simp [State.init, State.allocBuf, State.setReg, State.setBuf]

/-! ## §2 The register file is unmetered memory

`Reg := ℕ` — a program may use as many registers as it likes — and the memory
metric (`State.liveMem`, and the `d`/`p` indices of `Exec`) counts *buffer
capacities only*. `Exec.allocFree_space` therefore certifies `d ≤ 0 ∧ p ≤ 0` for
*every* allocation-free program, however much live data it is holding in registers. -/

/-- Load the first `n` words of the input buffer `0` into the `n` distinct registers
`1, …, n` (register `0` is the index scratch). Allocation-free by construction. -/
def spill : ℕ → Stmt 64
  | 0 => .skip
  | n + 1 => spill n ;; (.imm 0 (BitVec.ofNat 64 n) ;; .bufGet (n + 1) 0 0)

theorem spill_allocFree : ∀ n, (spill n).AllocFree
  | 0 => trivial
  | n + 1 => ⟨spill_allocFree n, trivial, trivial⟩

theorem spill_touches_nothing : ∀ (n : ℕ) (b : BufId), ¬ (spill n).Touches b
  | 0, _ => id
  | n + 1, b => by
    rintro (h | h | h)
    · exact spill_touches_nothing n b h
    · exact h
    · exact h

/-- The load loop runs and leaves the `n` input words in the `n` registers. -/
theorem spill_exec (n : ℕ) (hn : n < 2 ^ 64) (s : State 64) (hs : n ≤ (s.bufs 0).size) :
    ∃ (s' : State 64) (t : ℕ) (d p : ℤ),
      Exec CostModel.unit (spill n) s s' t d p ∧ s'.bufs = s.bufs ∧
        ∀ i, i < n → s'.regs (i + 1) = (s.bufs 0)[i]! := by
  induction n with
  | zero => exact ⟨s, 0, 0, 0, .skip, rfl, by omega⟩
  | succ n ih =>
    obtain ⟨s₁, t₁, d₁, p₁, hex, hbufs, hregs⟩ := ih (by omega) (by omega)
    have hb0 : s₁.bufs 0 = s.bufs 0 := by rw [hbufs]
    have htoNat : (BitVec.ofNat 64 n).toNat = n := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
    have hidx : ((s₁.setReg 0 (BitVec.ofNat 64 n)).regs 0).toNat
        < ((s₁.setReg 0 (BitVec.ofNat 64 n)).bufs 0).size := by
      rw [regs_setReg_self, bufs_setReg, hb0, htoNat]; omega
    refine ⟨_, _, _, _, .seq hex (.seq .imm (.bufGet hidx)), ?_, ?_⟩
    · simp only [bufs_setReg, hbufs]
    · intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
      · have h₁ : i + 1 ≠ n + 1 := by omega
        have h₂ : i + 1 ≠ 0 := by omega
        rw [regs_setReg_ne _ _ h₁, regs_setReg_ne _ _ h₂]
        exact hregs i hlt
      · rw [regs_setReg_self]
        simp only [bufs_setReg, hb0, regs_setReg_self, htoNat]
        exact (getElem!_pos _ _ (by omega)).symm

/-- **`n` words of live data at certified peak memory `0`.** The program ends with
the `n` input words sitting in `n` distinct registers — a footprint of `n` machine
words that no compiler can eliminate, since the postcondition observes all of them —
and the memory profile certifies `d ≤ 0 ∧ p ≤ 0`.

`Exec.peak_le_time` does not help: the time is `2n`, and `0 ≤ 2n`. Neither does
`State.liveMem`: the absolute-footprint theorems are *about* `liveMem`, which counts
buffer capacities and nothing else. -/
theorem registers_are_free_memory (n : ℕ) (hn : n < 2 ^ 64) (s : State 64)
    (hs : n ≤ (s.bufs 0).size) :
    ∃ (s' : State 64) (t : ℕ) (d p : ℤ),
      Exec CostModel.unit (spill n) s s' t d p ∧
        d ≤ 0 ∧ p ≤ 0 ∧ ∀ i, i < n → s'.regs (i + 1) = (s.bufs 0)[i]! := by
  obtain ⟨s', t, d, p, hex, -, hregs⟩ := spill_exec n hn s hs
  obtain ⟨hd, hp⟩ := hex.allocFree_space (spill_allocFree n)
  exact ⟨s', t, d, p, hex, hd, hp, hregs⟩

/-! ## §3 The same hole, inside the witgen pipeline

`compile_space_le` is advertised as "code accepted by `compile` needs at most `m`
words of memory". What it bounds is the *buffer* profile. The emitted code keeps the
program's `L = steps.length` local values in registers `0 … L-1`, plus temporaries
from `L+1` — none of which the metric sees. So the certificate is `m` while the
emitted code's real footprint is `m + L + O(expression depth)` words. -/

/-- A strict upper bound on the register names a statement mentions — the static
size of the register file the emitted code needs. Not part of Caliper: it exists
here only to measure what the space certificate omits. -/
def regFileSize {w : ℕ} : Stmt w → ℕ
  | .skip | .bufAllocI .. | .bufFree _ | .bufPop _ => 0
  | .seq c₁ c₂ => max (regFileSize c₁) (regFileSize c₂)
  | .imm d _ => d + 1
  | .mov d a | .un _ d a => max (d + 1) (a + 1)
  | .bin _ d a b => max (d + 1) (max (a + 1) (b + 1))
  | .bufAlloc _ n => n + 1
  | .bufLen d _ => d + 1
  | .bufGet d _ i => max (d + 1) (i + 1)
  | .bufSet _ i src => max (i + 1) (src + 1)
  | .bufPush _ src => src + 1
  | .ifNZ c thn els => max (c + 1) (max (regFileSize thn) (regFileSize els))
  | .whileNZ g c body => max (c + 1) (max (regFileSize g) (regFileSize body))

/-- A witness program with `n` `let`-steps and a **single** output element. Every
step is compilable and reads only environment cell `0`, so `compile 1` accepts it. -/
def chainIR (n : ℕ) : WitgenIR Fb 1 :=
  .ir (List.replicate n (.letF (.expr (var ⟨0⟩)))) (.lit #v[.expr (var ⟨0⟩)])

/-- The certificate: one word, whatever `n` is. -/
theorem chainIR_space_le_one {n : ℕ} {code : Stmt 64} (hc : compile 1 (chainIR n) = some code)
    {s s' : State 64} {t : ℕ} {d p : ℤ} (h : Exec CostModel.unit code s s' t d p) :
    p ≤ 1 :=
  (compile_space_le hc h).2

/- The reality, for `n = 200`: the emitted code needs a 203-register file — 203
words of live storage — against a certified peak of one word. -/

/-- info: true -/
#guard_msgs in #eval (compile 1 (chainIR 200)).isSome

/-- info: some 203 -/
#guard_msgs in #eval (compile 1 (chainIR 200)).map regFileSize

/- For comparison, the certified time — which *is* honest, since time and code size
coincide for straight-line code. Only the space certificate is off by `L`. -/
/-- info: some 606 -/
#guard_msgs in #eval (compile 1 (chainIR 200)).map (·.staticTime CostModel.unit)

/-! ## §4 `CostModel` is an unconstrained record

Every cost theorem is generic in `C : CostModel`, and `CostModel` is a bare record of
naturals with no positivity condition anywhere in the API. Any table is a legal
table. -/

/-- A perfectly legal cost model in which every instruction is free. -/
def CostModel.zero : CostModel where
  imm := 0
  mov := 0
  un _ := 0
  bin _ := 0
  bufAlloc := 0
  allocPerWord := 0
  bufFree := 0
  bufLen := 0
  bufGet := 0
  bufSet := 0
  bufPush := 0
  bufPop := 0
  branch := 0

theorem staticTime_zero {w : ℕ} (c : Stmt w) : c.staticTime CostModel.zero = 0 := by
  induction c with
  | seq _ _ ih₁ ih₂ => simp only [Stmt.staticTime, ih₁, ih₂]
  | ifNZ _ _ _ ih₁ ih₂ =>
    simp only [Stmt.staticTime, ih₁, ih₂, Nat.max_self, Nat.add_zero]; rfl
  | _ => simp [Stmt.staticTime, CostModel.zero]

/-- **The headline witgen program runs in zero steps.** Same theorem
(`compile_time_eq`), same program, a different — and equally well-formed — cost
table. Nothing in the API distinguishes `CostModel.zero` from `CostModel.unit`: the
credibility of every quoted numeral rests entirely on the *choice* of table, which no
theorem constrains. -/
theorem isZero_witgen_zero_steps {s s' : State 64} {t : ℕ} {d p : ℤ}
    (h : Exec CostModel.zero isZeroCompiled s s' t d p) : t = 0 := by
  rw [compile_time_eq compile_testIsZero h, staticTime_zero]

/-- A model that "corrects" the deliberately-unrealistic per-word allocation charge
to what a real `malloc` fast path costs: O(1), independent of the size. Every other
entry is the uniform model's. -/
def CostModel.freeMalloc : CostModel := { allocPerWord := 0 }

/-- **`Exec.peak_le_time` is bought by one unchecked field.** Under `freeMalloc` — a
model no more arbitrary than `unit` or `cycles` — a single instruction acquires a
terabyte of memory in one time step, so a `t < 2^40` certificate says nothing at all
about memory. The hypothesis `1 ≤ C.allocPerWord` is doing all the work, and no
theorem, check, or type forces a user's model to satisfy it. -/
theorem terabyte_in_one_step :
    ∃ (s' : State 64) (t : ℕ) (d p : ℤ),
      Exec CostModel.freeMalloc (.bufAllocI 1 (2 ^ 40)) (State.init 64) s' t d p ∧
        t = 1 ∧ p = 2 ^ 40 := by
  refine ⟨_, _, _, _, .bufAllocI, ?_, ?_⟩ <;> simp [State.init, CostModel.freeMalloc]

/-! ## §5 Peak memory is *growth*, so let the caller pay

`Exec`'s `p` bounds live memory relative to the start state, and preconditions
almost never pin the start state's capacities down (the headline
`isZero_witgen_correct_140` constrains `s.bufs 0` and says nothing about `s.caps`).
An algorithm needing `n` words of scratch can therefore be certified at peak `0` by
making "buffer 3 has capacity `n`" a precondition — the standard calling convention
of a real prover, where scratch space is allocated once and reused. -/

/-- Fill `n` words of caller-provided scratch space in buffer `3`. -/
def fillScratch : ℕ → Stmt 64
  | 0 => .skip
  | n + 1 => fillScratch n ;; .bufPush 3 0

theorem fillScratch_allocFree : ∀ n, (fillScratch n).AllocFree
  | 0 => trivial
  | n + 1 => ⟨fillScratch_allocFree n, trivial⟩

/-- **`n` words in use, certified peak `0`.** The program stores `n` words; because
the capacity was reserved by someone else, the profile charges nothing. Any
"algorithm X runs in `M` words" claim has to be read as "…*above whatever its
precondition already assumes*". -/
theorem caller_funded_memory (n : ℕ) (s : State 64)
    (hcap : n ≤ s.caps 3) (hsize : (s.bufs 3).size = 0) :
    ∃ (s' : State 64) (t : ℕ) (d p : ℤ),
      Exec CostModel.unit (fillScratch n) s s' t d p ∧
        d ≤ 0 ∧ p ≤ 0 ∧ (s'.bufs 3).size = n := by
  have main : ∀ n, n ≤ s.caps 3 → ∃ (s' : State 64) (t : ℕ) (d p : ℤ),
      Exec CostModel.unit (fillScratch n) s s' t d p ∧ s'.caps = s.caps ∧
        (s'.bufs 3).size = n := by
    intro n
    induction n with
    | zero => exact fun _ => ⟨s, 0, 0, 0, .skip, rfl, hsize⟩
    | succ n ih =>
      intro hn
      obtain ⟨s₁, t₁, d₁, p₁, hex, hcaps, hsz⟩ := ih (by omega)
      have hpush : (s₁.bufs 3).size < s₁.caps 3 := by rw [hsz, hcaps]; omega
      refine ⟨_, _, _, _, .seq hex (.bufPush hpush), ?_, ?_⟩
      · simp only [caps_setBuf, hcaps]
      · simp only [bufs_setBuf_self, Array.size_push, hsz]
  obtain ⟨s', t, d, p, hex, -, hsz⟩ := main n hcap
  obtain ⟨hd, hp⟩ := hex.allocFree_space (fillScratch_allocFree n)
  exact ⟨s', t, d, p, hex, hd, hp, hsz⟩

/-! ## §6 Preconditions are not required to be satisfiable

`Triple C P c Q T D M` quantifies over states satisfying `P`. Nothing anywhere asks
for a witness that `P` is inhabited, so an unsatisfiable precondition certifies every
bound for every program. This is standard Hoare-logic hygiene, but Caliper's
`Triple`s are *resource* claims, and the examples do not carry satisfiability
lemmas. -/

theorem vacuous_triple {w : ℕ} (C : CostModel) (c : Stmt w) (Q : State w → Prop) :
    Triple C (fun _ => False) c Q 0 0 0 := fun _ h => h.elim

/-! ## §7 `compile` never checks the field size

The compiler's design point is a **single-word** field: `p * p ≤ 2 ^ w`, so that a
field operation is `imm p ;; op ;; umod` — three instructions. That side condition is
*not* one of `compile`'s generation-time checks; `doc/caliper.md` says the field
conditions "cannot be decided at generation time for a generic `FiniteField`", but
`FiniteField.size F` is a plain `ℕ`, so `p * p ≤ 2 ^ 64` is as decidable as
`m < 2 ^ 64` (which *is* checked). Only primality genuinely needs a hypothesis.

The consequence: `compile` accepts a field outside its design point, `witgenTime`
quotes a number for it, and `compile_time_eq` certifies that number — for code that
computes the wrong answer, and whose real per-operation cost is many machine
instructions, not three. -/

/-- The smallest prime above `2 ^ 40`. Small enough for `native_decide`, large enough
that `p * p` overflows a 64-bit word — like Goldilocks (`2^64 - 2^32 + 1`, Plonky2)
and the 254/255-bit scalar fields of BN254 and BLS12-381, where a field multiply
costs tens of machine instructions rather than three. -/
def pOversized : ℕ := 2 ^ 40 + 15

instance : Fact (Nat.Prime pOversized) := ⟨by native_decide⟩

abbrev Fbig := F pOversized

/-- The design point is violated: two field elements do not multiply inside a word. -/
theorem pOversized_violates_single_word : 2 ^ 64 < pOversized * pOversized := by
  norm_num [pOversized]

/-- A one-line witness program over the oversized field: invert environment cell 0. -/
def bigInvIR : WitgenIR Fbig 1 :=
  .ir [] (.lit #v[.inv (.expr (var ⟨0⟩))])

/-- The same program over BabyBear, where the single-word design point holds. -/
def smallInvIR : WitgenIR Fb 1 :=
  .ir [] (.lit #v[.inv (.expr (var ⟨0⟩))])

/-- **The checked entry point accepts it.** -/
theorem compile_accepts_oversized_field : (compile 1 bigInvIR).isSome = true := by
  native_decide

/- …and a static time is quoted for it, by the same `#eval` the honest examples use.
Next to it, the same program over BabyBear, where the single-word design point really
does hold. The oversized field is quoted **fewer** steps than the 31-bit one (the
ladder length follows the Hamming weight of `p - 2`, not the width of `p`), because
the model charges three instructions for a field multiply *whatever the field is*.
On a real 64-bit machine the oversized field's multiply needs a multi-limb product
plus a reduction; for the 254-bit fields real proof systems use, tens of
instructions. The certificate is blind to all of it. -/
/-- info: some 98 -/
#guard_msgs in #eval (compile 1 bigInvIR).map (·.staticTime CostModel.unit)

/-- info: some 130 -/
#guard_msgs in #eval (compile 1 smallInvIR).map (·.staticTime CostModel.unit)

section OversizedDifferential

private def bigRow : Array Fbig := #[3]

private def bigEnv : ProverEnvironment Fbig where
  get j := bigRow[j]?.getD 0
  data _ _ := #[]
  hint _ _ := #[]

private def bigState : State 64 where
  regs _ := 0
  bufs b := if b = 0 then bigRow.map (fun x => BitVec.ofNat 64 (FiniteField.val x)) else #[]
  caps b := if b = 0 then bigRow.size else 0

/-- Machine output vs. reference output, as in the honest differential tests of
`WitgenCompile.lean`. -/
private def bigDiff : Option (List ℕ) × List ℕ :=
  let machine : Option (List ℕ) := do
    let code ← compile bigRow.size bigInvIR
    let (s', _, _, _) ← run CostModel.unit 100000 code bigState
    pure ((s'.bufs 1).toList.map (·.toNat))
  (machine, (bigInvIR.eval bigEnv).toList.map FiniteField.val)

/- The two disagree: the compiled code's `mul` wraps modulo `2^64` before the
`umod p` reduction. The cost certificate is unaffected — it never mentions
correctness. -/
/-- info: (some [938154445348], [733007751861]) -/
#guard_msgs in #eval bigDiff

end OversizedDifferential

/-! ## §8 Cost does not transfer along extensional equality

`compile` rejects `WitgenIR.native` closures outright, so no Caliper cost theorem
covers them — the pipeline is honest here. The trap is the shape of the bridge that
*does* exist for native closures: `onlyAccessedBelow_of_ir_equiv` transfers the
*access* property from a checked IR program to any closure that is extensionally
equal to it. Extensional equality is exactly the relation that preserves values and
destroys costs, so the same hypothesis must never be used to transfer `140 steps`.

Below, `slowIsZero k` computes the `IsZeroField` witness and then burns `2 ^ k`
steps. It satisfies the bridge's hypothesis for every `k`. -/

/-- `2 ^ k` wasted steps, value-preserving. -/
def slowdown {α : Type} (k : ℕ) (a : α) : α := (List.range (2 ^ k)).foldl (fun x _ => x) a

theorem slowdown_eq {α : Type} (k : ℕ) (a : α) : slowdown k a = a :=
  List.foldl_fixed _

/-- A native witness closure that is exponentially slower than the IR it agrees
with. -/
def slowIsZero (k : ℕ) : ProverEnvironment Fb → Vector Fb 1 :=
  fun env => slowdown k (testIsZero.eval env)

theorem slowIsZero_eq (k : ℕ) : ∀ env, slowIsZero k env = testIsZero.eval env :=
  fun _ => slowdown_eq _ _

/-- The access bridge applies to the slow closure, for every `k` — correctly, since
it is a statement about *which cells are read*. A cost bridge of the same shape would
be unsound, and there is nothing in the API marking the difference. -/
example (k : ℕ) : ProverEnvironment.OnlyAccessedBelow 1 (slowIsZero k) :=
  onlyAccessedBelow_of_ir_equiv (by native_decide) (by native_decide) (slowIsZero_eq k)

/-- The compiler itself is not fooled: native closures have no compiled form, hence
no cost certificate. The gap is that a *circuit* may carry `.native` witnesses
(`Circuit.witnessNative`), discharge its `ComputableWitnesses` obligation through the
bridge above, and still have no cost story at all — while the surrounding prose says
"witgen in < 2^40 steps". -/
theorem compile_native_none (k : ℕ) :
    compile (F := Fb) 1 (WitgenIR.native (slowIsZero k)) = none := rfl

end Caliper.Attacks
