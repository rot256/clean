import Clean.Caliper.WitgenCompile

/-!
# Cost bounds for compiled witness generation: "witgen in < 2^40 steps, machine-checked"

Phase 2 of the witgen compiler: machine-checked *cost* bounds for the code that
`Clean/Caliper/WitgenCompile.lean` emits.

The whole file rests on one structural fact, proved here by syntactic induction over
the compiler and packaged as `CodeShape`: **everything the compiler emits is
straight-line** (no `ifNZ`, no `whileNZ`, no dynamic `memAlloc` — `ite` is a mask
select, `mapRange`/`envRange`/`bitsOf` are unrolled, the Fermat inverse ladder is
unrolled over the generation-time bits of `p - 2`, and the single output-buffer
allocation in `compileIR`'s prologue is a `memAllocI` whose capacity is the *static*
output length `m`, hence statically priced at `C.memAlloc + m * C.allocPerWord`),
and, apart from that prologue `memAllocI`, **heap-allocation-free**: the only other
acquisitions are single-word register acquisitions (`regAlloc`), and the compiler's
register lifecycle is *scoped* — expression code for temp range `[next, next')`
contains exactly one `regAlloc` per register of the range and no `regFree`
(`CodeShape`), and every step / output element releases its temps at its boundary
(`freeTemps`), as do the locals + idx register at program end.

Consequences, all machine-checked below:

* **Time is a syntactic constant.** By `Exec.straight_time_eq`, every execution of a
  compiled program takes *exactly* `code.staticTime C` time units — an *equality*,
  not just a bound, and the same number on every input (`witgenTime_data_independent`;
  data-independence of the abstract time counter — an ingredient of a constant-time
  argument, not by itself a side-channel guarantee). `staticTime` is a plain
  recursive function of the syntax, so the cost of a concrete compiled program is a
  numeral: computable by `#eval` and certified by evaluation (`native_decide` here,
  since `toBits` is well-founded recursion, which `rfl` cannot reduce) — no
  execution, no semantics, no fuel involved. Register acquisitions are paid
  (`C.regAlloc + C.allocPerWord` each — one tick in both shipped tables); releases
  are free.
* **Memory is bounded by output length + the register live set.** The prologue's
  single `memAllocI` charges at most `m` words; every register acquisition is
  matched by a scope-boundary release, so the register file's contribution to the
  peak is the honest live set: the `L + 1` always-live locals + idx plus the
  *maximum* temps live within any single step or output element — never the total
  acquisition count. Both the net live-memory change (`d ≤ m`: every register the
  program acquires it also releases) and the peak
  (`p ≤ m + L + 1 + maxTempsPerScope`, `compile_space_le` via `irRegPeak`) are
  certified. The peak bound is exactly what a register allocator needs; scoped
  (bracket-nested) lifetimes make it interval-colorable. Independently,
  `Exec.peak_le_time` bounds the peak by the running time in any per-word-charging
  model.
* **Concrete `< 2^40` bounds.** For the BabyBear test programs of
  `WitgenCompile.lean` the pinned numbers are evaluated by `#eval`, certified by
  `native_decide`, and turned into end-to-end theorems of the shape

      theorem isZero_witgen_lt_2_40 (h : Exec .unit isZeroCompiled s s' t d p) :
          t < 2 ^ 40

  under both the uniform cost model and the calibrated `CostModel.cycles` table —
  the bound is model-generic because everything above is proved for an arbitrary
  `CostModel`.
-/

namespace Caliper.WitgenCompile

open Witgen

variable {F : Type} {w : ℕ}

/-! ## Syntactic register-accounting predicates

Three new syntactic gadgets alongside `Stmt.Straight`/`Stmt.AllocFree` (`Core.lean`):
heap-allocation-freeness (register instructions allowed), absence of `regFree`, and
the `regAlloc` count. Together with `Stmt.RegAllocTouches` they are the raw material
of `CodeShape` below. -/

/-- `c` contains no heap-memory management: no `memAlloc`, no `memAllocI`, no
`memFree` — anywhere. Register instructions are allowed (their space effect is
tracked by `Stmt.regAllocs` and the coverage lemma `exec_regsAlloc_of_touches`). -/
def _root_.Caliper.Stmt.HeapFree : Stmt w → Prop
  | .seq c₁ c₂ => c₁.HeapFree ∧ c₂.HeapFree
  | .ifNZ _ t e => t.HeapFree ∧ e.HeapFree
  | .whileNZ g _ b => g.HeapFree ∧ b.HeapFree
  | .memAlloc .. | .memAllocI .. | .memFree _ => False
  | _ => True

/-- `c` contains no `regFree` — anywhere. Expression code satisfies this: the
compiler releases temps only at step/element boundaries, outside expression code. -/
def _root_.Caliper.Stmt.NoRegFree : Stmt w → Prop
  | .seq c₁ c₂ => c₁.NoRegFree ∧ c₂.NoRegFree
  | .ifNZ _ t e => t.NoRegFree ∧ e.NoRegFree
  | .whileNZ g _ b => g.NoRegFree ∧ b.NoRegFree
  | .regFree _ => False
  | _ => True

/-- The number of `regAlloc` instructions in `c` (branches: the worst arm; loops:
meaningless, like `staticTime` — every use below is on straight-line code). -/
def _root_.Caliper.Stmt.regAllocs : Stmt w → ℕ
  | .seq c₁ c₂ => c₁.regAllocs + c₂.regAllocs
  | .ifNZ _ t e => max t.regAllocs e.regAllocs
  | .regAlloc _ => 1
  | _ => 0

/-! Build performance: pre-realize the unfolding lemmas of the new recursive
definitions at the definition site (realizations made inside a retained theorem
ship in the `.olean`). -/
set_option linter.unusedSimpArgs false in
private theorem regAccounting_eq_lemmas_realized : True := by
  simp -failIfUnchanged only [Stmt.HeapFree, Stmt.NoRegFree, Stmt.regAllocs]

/-! ## Generic space lemmas for straight-line, heap-free code -/

/-- **The register-count space bound**: straight-line heap-free code moves live
memory by at most one word per `regAlloc` it contains — both net and peak.
(`regFree` may push the net below zero; freeing is allowed and free.) -/
theorem exec_space_le_regAllocs {C : CostModel} {c : Stmt w} {s s' : State w}
    {t : ℕ} {d p : ℤ} (h : Exec C c s s' t d p) (hs : c.Straight)
    (hh : c.HeapFree) : d ≤ (c.regAllocs : ℤ) ∧ p ≤ (c.regAllocs : ℤ) := by
  induction h with
  | seq _ _ ih₁ ih₂ =>
    obtain ⟨h1, h2⟩ := ih₁ hs.1 hh.1
    obtain ⟨h3, h4⟩ := ih₂ hs.2 hh.2
    simp only [Stmt.regAllocs]
    push_cast
    omega
  | memAlloc | ifNZ_true | ifNZ_false | while_done | while_step => exact hs.elim
  | memAllocI | memFree => exact hh.elim
  | @regAlloc r s =>
    simp only [Stmt.regAllocs]
    rcases s.regsAlloc r with - | - <;> norm_num
  | @regFree r s =>
    refine ⟨le_trans ?_ (Int.natCast_nonneg _), Int.natCast_nonneg _⟩
    split <;> omega
  | _ => exact ⟨Int.natCast_nonneg _, Int.natCast_nonneg _⟩

/-- **The coverage lemma**: after straight-line code containing no `regFree`, every
register whose allocation status the code touches is *allocated* — straight-line
code executes all of its instructions, and the only status-touching instruction
left is `regAlloc`. This is what makes the scope-boundary `regFree`s credit their
full word (`freeTemps_exec_net`). -/
theorem exec_regsAlloc_of_touches {C : CostModel} {c : Stmt w} {s s' : State w}
    {t : ℕ} {d p : ℤ} {q : Reg} (h : Exec C c s s' t d p) (hs : c.Straight)
    (hf : c.NoRegFree) (hq : c.RegAllocTouches q) : s'.regsAlloc q = true := by
  induction h with
  | @seq c₁ c₂ _ _ _ _ _ _ _ _ _ _ h₂ ih₁ ih₂ =>
    by_cases h2 : c₂.RegAllocTouches q
    · exact ih₂ hs.2 hf.2 h2
    · rw [h₂.frame_regAlloc h2]
      rcases (RegAllocTouches_seq c₁ c₂ q).mp hq with hq₁ | hq₁
      · exact ih₁ hs.1 hf.1 hq₁
      · exact absurd hq₁ h2
  | @regAlloc r s =>
    have hqr : q = r := hq
    exact hqr ▸ regsAlloc_setRegAlloc_self s r true
  | regFree => exact hf.elim
  | memAlloc | ifNZ_true | ifNZ_false | while_done | while_step => exact hs.elim
  | _ => exact absurd hq (fun hh => hh)

/-! ## `CodeShape`: the register discipline of compiled expression code

`CodeShape c lo hi` packages everything the space and straightness theorems need to
know about a piece of compiled *expression* code with temp range `[lo, hi)`: it is
straight-line, heap-free, contains no `regFree`, contains exactly `hi - lo`
`regAlloc`s, and touches the allocation status of exactly the registers in
`[lo, hi)`. The scalar compilers produce `CodeShape (code) next next'` by the
mutual induction `compileF_shape`/`compileU_shape`/`compileB_shape` below. -/

/-- The register discipline of compiled expression code with temp range `[lo, hi)`.
The alloc count is stated additively (`regAllocs + lo = hi`) to avoid `ℕ`
subtraction. -/
structure CodeShape (c : Stmt w) (lo hi : ℕ) : Prop where
  straight : c.Straight
  heapFree : c.HeapFree
  noRegFree : c.NoRegFree
  allocs_eq : c.regAllocs + lo = hi
  /-- Register bounds live at `ℕ` (not the `Reg` abbrev): `omega` does not unfold
  `Reg`, so a `Reg`-typed relation would be invisible to it. -/
  touches_iff : ∀ q : ℕ, c.RegAllocTouches q ↔ lo ≤ q ∧ q < hi

theorem CodeShape.mono {c : Stmt w} {lo hi : ℕ} (h : CodeShape c lo hi) : lo ≤ hi := by
  have := h.allocs_eq
  omega

/-- Sequencing composes adjacent temp ranges. -/
theorem CodeShape.seq {c₁ c₂ : Stmt w} {a b c : ℕ}
    (h₁ : CodeShape c₁ a b) (h₂ : CodeShape c₂ b c) : CodeShape (c₁ ;; c₂) a c where
  straight := ⟨h₁.straight, h₂.straight⟩
  heapFree := ⟨h₁.heapFree, h₂.heapFree⟩
  noRegFree := ⟨h₁.noRegFree, h₂.noRegFree⟩
  allocs_eq := by
    have e₁ := h₁.allocs_eq
    have e₂ := h₂.allocs_eq
    simp only [Stmt.regAllocs]
    omega
  touches_iff q := by
    have e₁ := h₁.touches_iff q
    have e₂ := h₂.touches_iff q
    have m₁ := h₁.mono
    have m₂ := h₂.mono
    rw [RegAllocTouches_seq, e₁, e₂]
    omega

/-- Any single register-untouching instruction (or `skip`) is a `CodeShape` at the
empty range — dischargeable by `rfl`-level tactics, so uses are bare `.atom`. -/
theorem CodeShape.atom {c : Stmt w} {a : ℕ}
    (hs : c.Straight := by trivial) (hh : c.HeapFree := by trivial)
    (hn : c.NoRegFree := by trivial) (ha : c.regAllocs = 0 := by rfl)
    (ht : ∀ q, ¬ c.RegAllocTouches q := by exact fun _ h => h) :
    CodeShape c a a where
  straight := hs
  heapFree := hh
  noRegFree := hn
  allocs_eq := by omega
  touches_iff q := ⟨fun h => absurd h (ht q), fun h => absurd h (by omega)⟩

/-- `regAlloc a` is the one-register `CodeShape`. -/
theorem CodeShape.alloc {a : ℕ} : CodeShape (w := w) (.regAlloc a) a (a + 1) where
  straight := trivial
  heapFree := trivial
  noRegFree := trivial
  allocs_eq := by show 1 + a = a + 1; omega
  touches_iff q := by show @Eq ℕ q a ↔ a ≤ q ∧ q < a + 1; omega

/-- A `List.foldl` whose step preserves an empty-range `CodeShape` preserves it —
the induction skeleton for the register-free `invLadder`. -/
theorem foldl_shape {α : Type} {f : Stmt w → α → Stmt w} {a : ℕ}
    (hf : ∀ c x, CodeShape c a a → CodeShape (f c x) a a) :
    ∀ (l : List α) (init : Stmt w), CodeShape init a a →
      CodeShape (l.foldl f init) a a
  | [], _, h => h
  | x :: l, init, h => foldl_shape hf l (f init x) (hf init x h)

/-- The field-reduction pattern acquires and writes exactly `[next, next + 2)`. -/
theorem fieldOp_shape (p : ℕ) (op : BinOp) (a b next : Reg) :
    CodeShape (fieldOp (w := w) p op a b next).1 next (next + 2) :=
  .seq .alloc (.seq .atom (.seq .alloc (.seq .atom .atom)))

/-- The mask select acquires and writes exactly `[next, next + 5)`. -/
theorem selectCode_shape (flag t e next : Reg) :
    CodeShape (selectCode (w := w) flag t e next).1 next (next + 5) :=
  .seq .alloc (.seq .atom (.seq .alloc (.seq .atom (.seq .alloc (.seq .atom
    (.seq .alloc (.seq .atom (.seq .alloc .atom))))))))

/-- The Fermat inverse ladder is register-lifecycle-free: it only rewrites its
caller-acquired accumulator. -/
theorem invLadder_shape (p : ℕ) (acc x t : Reg) {a : ℕ} :
    CodeShape (invLadder (w := w) p acc x t) a a := by
  unfold invLadder
  refine foldl_shape (fun c b hc => ?_) _ _ .atom
  cases b
  · exact hc.seq (.seq .atom .atom)
  · exact (hc.seq (.seq .atom .atom)).seq (.seq .atom .atom)

/-! ### The scope-boundary emitters -/

theorem freeTemps_straight (base : ℕ) : ∀ k, (freeTemps (w := w) base k).Straight
  | 0 => trivial
  | k + 1 => ⟨trivial, freeTemps_straight base k⟩

theorem freeTemps_heapFree (base : ℕ) : ∀ k, (freeTemps (w := w) base k).HeapFree
  | 0 => trivial
  | k + 1 => ⟨trivial, freeTemps_heapFree base k⟩

theorem freeTemps_regAllocs (base : ℕ) : ∀ k, (freeTemps (w := w) base k).regAllocs = 0
  | 0 => rfl
  | k + 1 => by
    simp only [freeTemps, Stmt.regAllocs, freeTemps_regAllocs base k]

theorem freeTemps_touches_iff (base : ℕ) :
    ∀ (k q : ℕ),
      (freeTemps (w := w) base k).RegAllocTouches q ↔ base ≤ q ∧ q < base + k
  | 0, q => ⟨fun h => h.elim, fun h => absurd h (by omega)⟩
  | k + 1, q => by
    rw [freeTemps, RegAllocTouches_seq, freeTemps_touches_iff base k q,
      show (Stmt.regFree (w := w) (base + k)).RegAllocTouches q ↔ @Eq ℕ q (base + k)
        from Iff.rfl]
    omega

/-- `freeTemps` always executes, changing nothing but allocation statuses. -/
theorem freeTemps_exec {C : CostModel} (base : ℕ) :
    ∀ (k : ℕ) (s : State w), ∃ s' t d p, Exec C (freeTemps base k) s s' t d p ∧
      s'.regs = s.regs ∧ s'.bufs = s.bufs ∧ s'.caps = s.caps
  | 0, s => ⟨s, 0, 0, 0, .skip, rfl, rfl, rfl⟩
  | k + 1, s => by
    obtain ⟨s', t, d, p, hex, hr, hb, hc⟩ :=
      freeTemps_exec (C := C) base k (s.setRegAlloc (base + k) false)
    exact ⟨s', _, _, _, .seq .regFree hex, hr, hb, hc⟩

/-- `freeTemps` never grows live memory. -/
theorem freeTemps_space {C : CostModel} {base k : ℕ} {s s' : State w} {t : ℕ}
    {d p : ℤ} (h : Exec C (freeTemps base k) s s' t d p) : d ≤ 0 ∧ p ≤ 0 := by
  have := exec_space_le_regAllocs h (freeTemps_straight base k)
    (freeTemps_heapFree base k)
  rw [freeTemps_regAllocs base k] at this
  exact_mod_cast this

/-- **No phantom scope credit, exactly**: freeing a fully-allocated temp range
credits exactly its `k` words. -/
theorem freeTemps_exec_net {C : CostModel} {base : ℕ} :
    ∀ {k : ℕ} {s s' : State w} {t : ℕ} {d p : ℤ},
      Exec C (freeTemps base k) s s' t d p →
      (∀ j, j < k → s.regsAlloc (base + j) = true) → d = -(k : ℤ) := by
  intro k
  induction k with
  | zero =>
    intro s s' t d p h _
    cases h
    rfl
  | succ k ih =>
    intro s s' t d p h hcov
    cases h with
    | seq h₁ h₂ =>
      cases h₁
      rw [hcov k (by omega), if_pos rfl]
      have hcov' : ∀ j, j < k →
          (s.setRegAlloc (base + k) false).regsAlloc (base + j) = true := by
        intro j hj
        rw [regsAlloc_setRegAlloc_ne _ _ (show base + j ≠ base + k by omega)]
        exact hcov j (by omega)
      have := ih h₂ hcov'
      push_cast
      omega

theorem allocRegs_shape : ∀ k, CodeShape (allocRegs (w := w) k) 0 k
  | 0 => .atom
  | k + 1 => (allocRegs_shape k).seq .alloc

/-- `allocRegs` always executes, changing nothing but allocation statuses. -/
theorem allocRegs_exec {C : CostModel} : ∀ (k : ℕ) (s : State w),
    ∃ s' t d p, Exec C (allocRegs k) s s' t d p ∧
      s'.regs = s.regs ∧ s'.bufs = s.bufs ∧ s'.caps = s.caps
  | 0, s => ⟨s, 0, 0, 0, .skip, rfl, rfl, rfl⟩
  | k + 1, s => by
    obtain ⟨s₁, t, d, p, hex, hr, hb, hc⟩ := allocRegs_exec (C := C) k s
    exact ⟨s₁.setRegAlloc k true, _, _, _, .seq hex .regAlloc, hr, hb, hc⟩

/-- After the prologue, all of `0 .. k - 1` is allocated. -/
theorem allocRegs_exec_cov {C : CostModel} {k : ℕ} {s s' : State w} {t : ℕ}
    {d p : ℤ} (h : Exec C (allocRegs k) s s' t d p) :
    ∀ q, q < k → s'.regsAlloc q = true := fun q hq =>
  exec_regsAlloc_of_touches h (allocRegs_shape k).straight
    (allocRegs_shape k).noRegFree (((allocRegs_shape k).touches_iff q).mpr
      ⟨Nat.zero_le q, hq⟩)

variable [instF : FiniteField F]

/-! ### The shapes of the scalar compilers -/

/-- Compiled circuit expressions have the scoped register discipline. -/
theorem compileExpr_shape : ∀ (e : Expression F) (next : Reg),
    CodeShape (compileExpr (w := w) e next).1 next (compileExpr (w := w) e next).2.2
  | .var _, _ => .seq .alloc (.seq .atom (.seq .alloc .atom))
  | .const _, _ => .seq .alloc .atom
  | .add x y, next =>
    (compileExpr_shape x next).seq
      ((compileExpr_shape y (compileExpr (w := w) x next).2.2).seq
        (fieldOp_shape _ _ _ _ _))
  | .mul x y, next =>
    (compileExpr_shape x next).seq
      ((compileExpr_shape y (compileExpr (w := w) x next).2.2).seq
        (fieldOp_shape _ _ _ _ _))

mutual

/-- Compiled field-sorted expressions have the scoped register discipline. -/
theorem compileF_shape (L : ℕ) : ∀ (e : FExpr F) (next : Reg),
    CodeShape (compileF (w := w) L e next).1 next (compileF (w := w) L e next).2.2
  | .expr e, next => compileExpr_shape e next
  | .const _, _ => .seq .alloc .atom
  | .localVar _, _ => .atom
  | .add x y, next =>
    (compileF_shape L x next).seq
      ((compileF_shape L y (compileF (w := w) L x next).2.2).seq
        (fieldOp_shape _ _ _ _ _))
  | .mul x y, next =>
    (compileF_shape L x next).seq
      ((compileF_shape L y (compileF (w := w) L x next).2.2).seq
        (fieldOp_shape _ _ _ _ _))
  | .inv x, next =>
    (compileF_shape L x next).seq
      (.seq .alloc (.seq .atom (.seq .alloc (.seq .atom
        (invLadder_shape _ _ _ _)))))
  | .ofU64 n, next =>
    (compileU_shape L n next).seq
      (.seq .alloc (.seq .atom (.seq .alloc .atom)))
  | .ite c t e, next =>
    (compileB_shape L c next).seq
      ((compileF_shape L t (compileB (w := w) L c next).2.2).seq
        ((compileF_shape L e
            (compileF (w := w) L t (compileB (w := w) L c next).2.2).2.2).seq
          (selectCode_shape _ _ _ _)))
  | .listGet .., _ => .seq .alloc .atom
  | .dataGet .., _ => .seq .alloc .atom
  | .hintGet .., _ => .seq .alloc .atom

/-- Compiled u64-sorted expressions have the scoped register discipline. -/
theorem compileU_shape (L : ℕ) : ∀ (e : U64Expr F) (next : Reg),
    CodeShape (compileU (w := w) L e next).1 next (compileU (w := w) L e next).2.2
  | .const _, _ => .seq .alloc .atom
  | .val x, next => compileF_shape L x next
  | .idx, _ => .atom
  | .localVar _, _ => .atom
  | .add x y, next =>
    (compileU_shape L x next).seq
      ((compileU_shape L y (compileU (w := w) L x next).2.2).seq
        (.seq .alloc .atom))
  | .mul x y, next =>
    (compileU_shape L x next).seq
      ((compileU_shape L y (compileU (w := w) L x next).2.2).seq
        (.seq .alloc .atom))
  | .div x y, next =>
    (compileU_shape L x next).seq
      ((compileU_shape L y (compileU (w := w) L x next).2.2).seq
        (.seq .alloc .atom))
  | .mod x y, next =>
    (compileU_shape L x next).seq
      ((compileU_shape L y (compileU (w := w) L x next).2.2).seq
        (.seq .alloc .atom))
  | .land x y, next =>
    (compileU_shape L x next).seq
      ((compileU_shape L y (compileU (w := w) L x next).2.2).seq
        (.seq .alloc .atom))
  | .lor x y, next =>
    (compileU_shape L x next).seq
      ((compileU_shape L y (compileU (w := w) L x next).2.2).seq
        (.seq .alloc .atom))
  | .lxor x y, next =>
    (compileU_shape L x next).seq
      ((compileU_shape L y (compileU (w := w) L x next).2.2).seq
        (.seq .alloc .atom))
  | .shiftL x y, next =>
    (compileU_shape L x next).seq
      ((compileU_shape L y (compileU (w := w) L x next).2.2).seq
        (.seq .alloc (.seq .atom (.seq .alloc (.seq .atom
          (.seq .alloc .atom))))))
  | .shiftR x y, next =>
    (compileU_shape L x next).seq
      ((compileU_shape L y (compileU (w := w) L x next).2.2).seq
        (.seq .alloc (.seq .atom (.seq .alloc (.seq .atom
          (.seq .alloc .atom))))))
  | .ite c t e, next =>
    (compileB_shape L c next).seq
      ((compileU_shape L t (compileB (w := w) L c next).2.2).seq
        ((compileU_shape L e
            (compileU (w := w) L t (compileB (w := w) L c next).2.2).2.2).seq
          (selectCode_shape _ _ _ _)))

/-- Compiled conditions have the scoped register discipline. -/
theorem compileB_shape (L : ℕ) : ∀ (e : BExpr F) (next : Reg),
    CodeShape (compileB (w := w) L e next).1 next (compileB (w := w) L e next).2.2
  | .true, _ => .seq .alloc .atom
  | .false, _ => .seq .alloc .atom
  | .feq x y, next =>
    (compileF_shape L x next).seq
      ((compileF_shape L y (compileF (w := w) L x next).2.2).seq
        (.seq .alloc .atom))
  | .neq x y, next =>
    (compileU_shape L x next).seq
      ((compileU_shape L y (compileU (w := w) L x next).2.2).seq
        (.seq .alloc .atom))
  | .lt x y, next =>
    (compileU_shape L x next).seq
      ((compileU_shape L y (compileU (w := w) L x next).2.2).seq
        (.seq .alloc .atom))
  | .flt x y, next =>
    (compileF_shape L x next).seq
      ((compileF_shape L y (compileF (w := w) L x next).2.2).seq
        (.seq .alloc .atom))
  | .bit x _, next =>
    (compileF_shape L x next).seq
      (.seq .alloc (.seq .atom (.seq .alloc (.seq .atom (.seq .alloc
        (.seq .atom (.seq .alloc .atom)))))))
  | .not b, next =>
    (compileB_shape L b next).seq (.seq .alloc .atom)
  | .and x y, next =>
    (compileB_shape L x next).seq
      ((compileB_shape L y (compileB (w := w) L x next).2.2).seq
        (.seq .alloc .atom))

end

/-! ## Straightness of the program-level emitters -/

/-- A `List.foldl` whose step preserves straightness preserves it. -/
private theorem foldl_straight {α : Type} {f : Stmt w → α → Stmt w}
    (hf : ∀ c a, c.Straight → (f c a).Straight) :
    ∀ (l : List α) (init : Stmt w), init.Straight → (l.foldl f init).Straight
  | [], _, h => h
  | a :: l, init, h => foldl_straight hf l (f init a) (hf init a h)

/-- Compiled `let`-steps are straight-line. -/
theorem compileStep_straight (L : ℕ) (j : Reg) : ∀ (st : Step F),
    (compileStep (w := w) L j st).Straight
  | .letF e =>
    ⟨(compileF_shape L e (L + 1)).straight, trivial, freeTemps_straight _ _⟩
  | .letU e =>
    ⟨(compileU_shape L e (L + 1)).straight, trivial, freeTemps_straight _ _⟩

/-- Compiled step lists are straight-line. -/
theorem compileSteps_straight (L : ℕ) : ∀ (steps : List (Step F)) (j : ℕ),
    (compileSteps (w := w) L steps j).Straight
  | [], _ => trivial
  | st :: rest, j =>
    ⟨compileStep_straight L j st, compileSteps_straight L rest (j + 1)⟩

/-- Compiled vector outputs are straight-line. -/
theorem compileV_straight (L : ℕ) : ∀ {n : ℕ} (v : VExpr F n),
    (compileV (w := w) L v).Straight
  | _, .lit es => by
    refine foldl_straight (fun c e hc => ?_) es.toList .skip trivial
    exact ⟨hc, (compileF_shape L e (L + 1)).straight, trivial,
      freeTemps_straight _ _⟩
  | _, .mapRange n body => by
    refine ⟨foldl_straight (fun c i hc => ?_) (List.range n) .skip trivial, trivial⟩
    exact ⟨hc, ⟨trivial, (compileF_shape L body (L + 1)).straight⟩, trivial,
      freeTemps_straight _ _⟩
  | n, .envRange offset => by
    refine foldl_straight (fun c i hc => ?_) (List.range n) .skip trivial
    exact ⟨hc, ⟨trivial, trivial, trivial, trivial⟩, trivial, freeTemps_straight _ _⟩
  | n, .bitsOf x => by
    refine ⟨(compileF_shape L x (L + 1)).straight,
      foldl_straight (fun c i hc => ?_) (List.range n) .skip trivial,
      freeTemps_straight _ _⟩
    exact ⟨hc, ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial,
      trivial⟩, trivial, freeTemps_straight _ _⟩
  | _, .append a b => ⟨compileV_straight L a, compileV_straight L b⟩

/-- The shared codegen body `compileIRCode` is straight-line. -/
theorem compileIRCode_straight (L : ℕ) {m : ℕ} (steps : List (Step F))
    (out : VExpr F m) : (compileIRCode (w := w) L steps out).Straight :=
  ⟨trivial, (allocRegs_shape (L + 1)).straight, trivial,
    compileSteps_straight L steps 0, compileV_straight L out,
    freeTemps_straight 0 (L + 1)⟩

/-- **Everything `compileIR` emits is straight-line**: no `ifNZ`, no `whileNZ`,
anywhere. This is the fact that turns running time into a syntactic constant. -/
theorem compileIR_straight {L : ℕ} {m : ℕ} {ir : WitgenIR F m} {code : Stmt w}
    (h : compileIR (w := w) L ir = some code) : code.Straight := by
  cases ir with
  | native f => simp [compileIR] at h
  | ir steps out =>
    simp only [compileIR, Option.some.injEq] at h
    exact h ▸ compileIRCode_straight L steps out
  | certified f steps out hcert =>
    -- the compiled code is literally the IR reimplementation's (at the ambient
    -- `FiniteField` instance; drop the constructor's packed instance so instance
    -- synthesis below picks the ambient one)
    simp only [compileIR, Option.some.injEq] at h
    rename_i instP
    clear hcert f instP
    exact h ▸ compileIRCode_straight L steps out

/-! ## The time theorem: witgen time is a syntactic constant -/

/-- The running time of a compiled witness program, read off the *syntax* by the
partial static clock `Stmt.staticTime?` — no execution involved. Compiled code is
always straight-line (`compileIR_straight`), so `staticTime?` always succeeds on it
and this agrees with mapping the raw `staticTime` over the compiler's output
(`witgenTime_eq_map_staticTime`); routing through `staticTime?` keeps the definition
honest by construction — it cannot produce a number for code containing loops. By
`witgenTime_eq` below, whatever number it computes is the exact running time of
every execution. -/
def witgenTime (C : CostModel) (L : ℕ) {m : ℕ} (ir : WitgenIR F m) : Option ℕ :=
  (compileIR (w := w) L ir).bind (·.staticTime? C)

/-- Everything `compileIR` emits is straight-line, so the partial static clock
never fails on it: `witgenTime` is the raw `staticTime` mapped over the compiler's
output. -/
theorem witgenTime_eq_map_staticTime {C : CostModel} {L m : ℕ} {ir : WitgenIR F m} :
    witgenTime (w := w) C L ir = (compileIR (w := w) L ir).map (·.staticTime C) := by
  cases hc : compileIR (w := w) L ir with
  | none => simp only [witgenTime, hc, Option.bind_none, Option.map_none]
  | some code =>
    simp only [witgenTime, hc, Option.bind_some, Option.map_some,
      (compileIR_straight hc).staticTime?_eq]

/-- **Compiled witgen code runs in exactly its static time**, on every input: an
equality, not just an upper bound. -/
theorem compileIR_time_eq {C : CostModel} {L m : ℕ} {ir : WitgenIR F m} {code : Stmt w}
    {s s' : State w} {t : ℕ} {d p : ℤ} (hc : compileIR (w := w) L ir = some code)
    (hx : Exec C code s s' t d p) : t = code.staticTime C :=
  hx.straight_time_eq (compileIR_straight hc)

/-- The `witgenTime` form of `compileIR_time_eq`: whatever number `witgenTime`
computes is the exact running time of every execution of the compiled program. -/
theorem witgenTime_eq {C : CostModel} {L m : ℕ} {ir : WitgenIR F m} {code : Stmt w}
    {T : ℕ} {s s' : State w} {t : ℕ} {d p : ℤ}
    (hc : compileIR (w := w) L ir = some code)
    (hT : witgenTime (w := w) C L ir = some T) (hx : Exec C code s s' t d p) : t = T := by
  rw [witgenTime, hc, Option.bind_some] at hT
  exact hx.staticTime?_time_eq hT

/-- **Data independence**: two executions of the same compiled witness program take
the same time, whatever their inputs. (Data-independence of the abstract time
counter — an ingredient of a constant-time argument, not by itself a side-channel
guarantee.) -/
theorem witgenTime_data_independent {C : CostModel} {L m : ℕ} {ir : WitgenIR F m}
    {code : Stmt w} {s₁ s₁' s₂ s₂' : State w} {t₁ t₂ : ℕ} {d₁ p₁ d₂ p₂ : ℤ}
    (hc : compileIR (w := w) L ir = some code)
    (h₁ : Exec C code s₁ s₁' t₁ d₁ p₁) (h₂ : Exec C code s₂ s₂' t₂ d₂ p₂) : t₁ = t₂ :=
  h₁.straight_data_independent h₂ (compileIR_straight hc)

/-! ## The memory theorem: witgen space is output length + the register live set

The register component of the peak is the *live set*, not the acquisition count:
temps die at step/element boundaries, so the bound is `L + 1` (locals + idx, live
for the whole program) plus the maximum temp count of any single step or output
element. The measures below read that maximum off the compiler's own register
threading. -/

/-- The temp count of one `let`-step: how many registers `[L+1, next')` its
compiled expression acquires — all released at the step boundary. -/
def stepTemps (L : ℕ) : Step F → ℕ
  | .letF e => ((compileF (w := w) L e (L + 1)).2.2 : ℕ) - (L + 1)
  | .letU e => ((compileU (w := w) L e (L + 1)).2.2 : ℕ) - (L + 1)

/-- The maximum temp count over a step list — the steps' contribution to the
register live-set peak. -/
def stepsPeak (L : ℕ) (steps : List (Step F)) : ℕ :=
  steps.foldr (fun st acc => max (stepTemps (w := w) L st) acc) 0

/-- The maximum temp count over the output elements — `envRange` reads through two
fixed temps, `bitsOf` holds its decomposed value's temps across the per-bit blocks
(each of which scopes four more). -/
def outTemps (L : ℕ) : {n : ℕ} → VExpr F n → ℕ
  | _, .lit es =>
    es.toList.foldr
      (fun e acc => max (((compileF (w := w) L e (L + 1)).2.2 : ℕ) - (L + 1)) acc) 0
  | _, .mapRange _ body => ((compileF (w := w) L body (L + 1)).2.2 : ℕ) - (L + 1)
  | _, .envRange _ => 2
  | _, .bitsOf x => (((compileF (w := w) L x (L + 1)).2.2 : ℕ) - (L + 1)) + 4
  | _, .append a b => max (outTemps L a) (outTemps L b)

/-- **The certified register-file requirement** of a compiled program: the `L + 1`
always-live locals + idx plus the worst single-scope temp count. `compile`-accepted
code's live-memory peak is `m` (the output buffer) plus this number
(`compile_space_le`) — exactly the register file a register allocator must provide,
and interval-colorable since all lifetimes are bracket-nested. -/
def irRegPeak (L : ℕ) {m : ℕ} (steps : List (Step F)) (out : VExpr F m) : ℕ :=
  L + 1 + max (stepsPeak (w := w) L steps) (outTemps (w := w) L out)

/-- Membership bounds a `foldr max`. -/
private theorem le_foldr_max {α : Type} (g : α → ℕ) :
    ∀ (l : List α) (x : α), x ∈ l → g x ≤ l.foldr (fun e acc => max (g e) acc) 0
  | e :: l, x, hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact le_max_left _ _
    · exact le_trans (le_foldr_max g l x hx) (le_max_right _ _)

/-! ### The scope-block space lemma

`c ;; mid ;; freeTemps lo k` — expression code with temp range `[lo, lo + k)`, a
register-neutral middle instruction (the binding `mov` or the output `memPush`),
and the scope exit. The net vanishes (every acquired temp is provably allocated at
its release — the coverage lemma — so each release credits its word), and the peak
is the scope's temp count. -/

private theorem block_space {C : CostModel} {c mid : Stmt w} {lo hi k : ℕ}
    {s s' : State w} {t : ℕ} {d p : ℤ}
    (h : Exec C (c ;; mid ;; freeTemps lo k) s s' t d p)
    (hc : CodeShape c lo hi) (hk : lo + k = hi) (hma : mid.AllocFree)
    (hmt : ∀ q, ¬ mid.RegAllocTouches q) :
    d ≤ 0 ∧ p ≤ (k : ℤ) := by
  cases h with
  | seq h₁ hrest =>
    cases hrest with
    | @seq _ _ s₁ s₂ _ _ _ _ _ _ _ h₂ h₃ =>
      have hka : c.regAllocs = k := by have := hc.allocs_eq; omega
      obtain ⟨hd₁, hp₁⟩ := exec_space_le_regAllocs h₁ hc.straight hc.heapFree
      rw [hka] at hd₁ hp₁
      obtain ⟨hd₂, hp₂⟩ := h₂.allocFree_space hma
      have hp₂' := h₂.peak_nonneg
      have hcov : ∀ j, j < k → s₂.regsAlloc (lo + j) = true := by
        intro j hj
        rw [h₂.frame_regAlloc (hmt _)]
        exact exec_regsAlloc_of_touches h₁ hc.straight hc.noRegFree
          ((hc.touches_iff _).mpr ⟨by omega, by omega⟩)
      have hd₃ := freeTemps_exec_net h₃ hcov
      obtain ⟨-, hp₃⟩ := freeTemps_space h₃
      have hp₃' := h₃.peak_nonneg
      constructor <;> omega

/-- The scope block touches only its own temp range. -/
private theorem block_touches {c mid : Stmt w} {lo hi k : ℕ} {q : ℕ}
    (h : (c ;; mid ;; freeTemps lo k).RegAllocTouches q)
    (hc : CodeShape c lo hi) (hk : lo + k = hi)
    (hmt : ∀ q, ¬ mid.RegAllocTouches q) : lo ≤ q ∧ q < hi := by
  rcases h with h | h | h
  · exact (hc.touches_iff q).mp h
  · exact absurd h (hmt q)
  · have := (freeTemps_touches_iff lo k q).mp h
    omega

/-- The fold skeleton for the per-element space bounds of `compileV`: extending a
`d ≤ 0 ∧ p ≤ P` prefix by `d ≤ 0 ∧ p ≤ P` blocks stays within the bound. -/
private theorem foldl_space {C : CostModel} {α : Type} {f : Stmt w → α → Stmt w}
    {P : ℤ} :
    ∀ (l : List α) (init : Stmt w),
      (∀ x ∈ l, ∀ (c : Stmt w),
        (∀ {s s' : State w} {t : ℕ} {d p : ℤ},
          Exec C c s s' t d p → d ≤ 0 ∧ p ≤ P) →
        ∀ {s s' : State w} {t : ℕ} {d p : ℤ},
          Exec C (f c x) s s' t d p → d ≤ 0 ∧ p ≤ P) →
      (∀ {s s' : State w} {t : ℕ} {d p : ℤ},
        Exec C init s s' t d p → d ≤ 0 ∧ p ≤ P) →
      ∀ {s s' : State w} {t : ℕ} {d p : ℤ},
        Exec C (l.foldl f init) s s' t d p → d ≤ 0 ∧ p ≤ P
  | [], _, _, hinit, _, _, _, _, _ => hinit
  | x :: l, init, hf, hinit, _, _, _, _, _ =>
    foldl_space l (f init x)
      (fun y hy => hf y (List.mem_cons_of_mem _ hy))
      (hf x (List.mem_cons_self ..) init hinit)

/-- The fold skeleton for register-status framing: a fold of blocks none of which
touches `q` does not touch `q`. -/
private theorem foldl_not_touches {α : Type} {f : Stmt w → α → Stmt w} {q : ℕ}
    (hf : ∀ x (c : Stmt w), ¬ c.RegAllocTouches q → ¬ (f c x).RegAllocTouches q) :
    ∀ (l : List α) (init : Stmt w), ¬ init.RegAllocTouches q →
      ¬ (l.foldl f init).RegAllocTouches q
  | [], _, h => h
  | x :: l, init, h => foldl_not_touches hf l (f init x) (hf x init h)

/-- One `let`-step's compiled block: net-zero live memory, peak at most its temp
count. -/
theorem compileStep_space {C : CostModel} {L : ℕ} {j : Reg} {st : Step F}
    {s s' : State w} {t : ℕ} {d p : ℤ}
    (h : Exec C (compileStep (w := w) L j st) s s' t d p) :
    d ≤ 0 ∧ p ≤ (stepTemps (w := w) L st : ℤ) := by
  cases st with
  | letF e =>
    exact block_space h (compileF_shape L e (L + 1))
      (Nat.add_sub_cancel' (compileF_shape (w := w) L e (L + 1)).mono)
      trivial (fun _ hh => hh)
  | letU e =>
    exact block_space h (compileU_shape L e (L + 1))
      (Nat.add_sub_cancel' (compileU_shape (w := w) L e (L + 1)).mono)
      trivial (fun _ hh => hh)

/-- A compiled step touches no register below `L + 1`. -/
theorem compileStep_not_touches {L : ℕ} {j : Reg} {st : Step F} {q : ℕ}
    (hq : q < L + 1) : ¬ (compileStep (w := w) L j st).RegAllocTouches q := by
  cases st with
  | letF e =>
    intro h
    have := block_touches h (compileF_shape L e (L + 1))
      (Nat.add_sub_cancel' (compileF_shape (w := w) L e (L + 1)).mono)
      (fun _ hh => hh)
    omega
  | letU e =>
    intro h
    have := block_touches h (compileU_shape L e (L + 1))
      (Nat.add_sub_cancel' (compileU_shape (w := w) L e (L + 1)).mono)
      (fun _ hh => hh)
    omega

/-- The compiled step list: net-zero live memory, peak at most the worst step. -/
theorem compileSteps_space {C : CostModel} {L : ℕ} :
    ∀ {steps : List (Step F)} {j : ℕ} {s s' : State w} {t : ℕ} {d p : ℤ},
      Exec C (compileSteps (w := w) L steps j) s s' t d p →
      d ≤ 0 ∧ p ≤ (stepsPeak (w := w) L steps : ℤ)
  | [], j, s, s', t, d, p, h => by cases h; exact ⟨le_refl 0, le_refl 0⟩
  | st :: rest, j, s, s', t, d, p, h => by
    cases h with
    | seq h₁ h₂ =>
      obtain ⟨hd₁, hp₁⟩ := compileStep_space h₁
      obtain ⟨hd₂, hp₂⟩ := compileSteps_space h₂
      have hl : (stepTemps (w := w) L st : ℤ) ≤ stepsPeak (w := w) L (st :: rest) := by
        exact_mod_cast le_max_left (stepTemps (w := w) L st) (stepsPeak (w := w) L rest)
      have hr : (stepsPeak (w := w) L rest : ℤ) ≤ stepsPeak (w := w) L (st :: rest) := by
        exact_mod_cast le_max_right (stepTemps (w := w) L st) (stepsPeak (w := w) L rest)
      omega

/-- The compiled step list touches no register below `L + 1`. -/
theorem compileSteps_not_touches {L : ℕ} {q : ℕ} (hq : q < L + 1) :
    ∀ (steps : List (Step F)) (j : ℕ),
      ¬ (compileSteps (w := w) L steps j).RegAllocTouches q
  | [], _ => fun h => h
  | st :: rest, j => fun h => by
    rcases h with h | h
    · exact compileStep_not_touches hq h
    · exact compileSteps_not_touches hq rest (j + 1) h

/-- The compiled output code: net-zero live memory, peak at most the worst
element's temp count. -/
theorem compileV_space {C : CostModel} {L : ℕ} :
    ∀ {n : ℕ} {v : VExpr F n} {s s' : State w} {t : ℕ} {d p : ℤ},
      Exec C (compileV (w := w) L v) s s' t d p →
      d ≤ 0 ∧ p ≤ (outTemps (w := w) L v : ℤ) := by
  intro n v
  match v with
  | .lit es =>
    intro s s' t d p h
    refine foldl_space es.toList .skip (fun e he c hc s s' t d p hex => ?_)
      (fun hex => by cases hex; exact ⟨le_refl 0, Int.natCast_nonneg _⟩) h
    cases hex with
    | seq h₁ h₂ =>
      obtain ⟨hd₁, hp₁⟩ := hc h₁
      obtain ⟨hd₂, hp₂⟩ := block_space
        (k := ((compileF (w := w) L e (L + 1)).2.2 : ℕ) - (L + 1))
        h₂ (compileF_shape L e (L + 1))
        (Nat.add_sub_cancel' (compileF_shape (w := w) L e (L + 1)).mono)
        trivial (fun _ hh => hh)
      have hle : (((compileF (w := w) L e (L + 1)).2.2 : ℕ) - (L + 1))
          ≤ outTemps (w := w) L (.lit es) := by
        simp only [outTemps]
        exact le_foldr_max
          (fun e => ((compileF (w := w) L e (L + 1)).2.2 : ℕ) - (L + 1))
          es.toList e he
      have hle' : ((((compileF (w := w) L e (L + 1)).2.2 : ℕ) - (L + 1) : ℕ) : ℤ)
          ≤ (outTemps (w := w) L (.lit es) : ℤ) := by exact_mod_cast hle
      omega
  | .mapRange nn body =>
    intro s s' t d p h
    cases h with
    | @seq _ _ _ _ _ _ d₁ p₁ _ d₂ p₂ h₁ h₂ =>
      cases h₂  -- the trailing `.imm L 0`
      have hfold : d₁ ≤ 0 ∧ p₁ ≤ (outTemps (w := w) L (.mapRange nn body) : ℤ) := by
        refine foldl_space (List.range nn) .skip
          (fun i hi c hc s s' t d p hex => ?_)
          (fun hex => by cases hex; exact ⟨le_refl 0, Int.natCast_nonneg _⟩) h₁
        cases hex with
        | seq hx₁ hx₂ =>
          obtain ⟨hd₁, hp₁⟩ := hc hx₁
          obtain ⟨hd₂, hp₂⟩ := block_space
            (k := ((compileF (w := w) L body (L + 1)).2.2 : ℕ) - (L + 1))
            hx₂ ((CodeShape.atom (a := L + 1)).seq (compileF_shape L body (L + 1)))
            (Nat.add_sub_cancel' (compileF_shape (w := w) L body (L + 1)).mono)
            trivial (fun _ hh => hh)
          have hbr : ((((compileF (w := w) L body (L + 1)).2.2 : ℕ) - (L + 1) : ℕ) : ℤ)
              = (outTemps (w := w) L (.mapRange nn body) : ℤ) := rfl
          omega
      obtain ⟨hd, hp⟩ := hfold
      omega
  | .envRange offset =>
    intro s s' t d p h
    refine foldl_space (List.range n) .skip (fun i hi c hc s s' t d p hex => ?_)
      (fun hex => by cases hex; exact ⟨le_refl 0, by norm_num [outTemps]⟩) h
    cases hex with
    | seq h₁ h₂ =>
      obtain ⟨hd₁, hp₁⟩ := hc h₁
      obtain ⟨hd₂, hp₂⟩ := block_space h₂
        (.seq .alloc (.seq .atom (.seq .alloc .atom)) : CodeShape _ (L + 1) (L + 3))
        (by omega) trivial (fun _ hh => hh)
      simp only [outTemps] at hp₁ ⊢
      omega
  | .bitsOf x =>
    intro s s' t d p h
    cases h with
    | @seq _ _ _ s₁ _ _ d₁ p₁ _ _ _ h₁ hrest =>
      cases hrest with
      | @seq _ _ _ s₂ _ _ df pf _ dr pr h₂ h₃ =>
        have hshape := compileF_shape (w := w) L x (L + 1)
        have hmono := hshape.mono
        obtain ⟨hd₁, hp₁⟩ := exec_space_le_regAllocs h₁ hshape.straight hshape.heapFree
        have hka : (compileF (w := w) L x (L + 1)).1.regAllocs
            = ((compileF (w := w) L x (L + 1)).2.2 : ℕ) - (L + 1) := by
          have := hshape.allocs_eq; omega
        rw [hka] at hd₁ hp₁
        -- the per-bit fold: net ≤ 0, peak ≤ 4, and it does not touch [L+1, n₁)
        have hfold : df ≤ (0:ℤ) ∧ pf ≤ (4 : ℤ) := by
          refine foldl_space (List.range n) .skip
            (fun i hi c hc s s' t d p hex => ?_)
            (fun hex => by cases hex; exact ⟨le_refl 0, by norm_num⟩) h₂
          cases hex with
          | seq hx₁ hx₂ =>
            obtain ⟨hd₁', hp₁'⟩ := hc hx₁
            obtain ⟨hd₂', hp₂'⟩ := block_space hx₂
              (.seq .alloc (.seq .atom (.seq .alloc (.seq .atom (.seq .alloc
                  (.seq .atom (.seq .alloc .atom)))))) :
                CodeShape _ (compileF (w := w) L x (L + 1)).2.2
                  ((compileF (w := w) L x (L + 1)).2.2 + 4))
              rfl trivial (fun _ hh => hh)
            omega
        obtain ⟨hd₂, hp₂⟩ := hfold
        -- the fold does not touch the decomposed value's temps
        have hframe : ∀ q : ℕ, q < (compileF (w := w) L x (L + 1)).2.2 →
            s₂.regsAlloc q = s₁.regsAlloc q := by
          intro q hq
          refine h₂.frame_regAlloc (foldl_not_touches (fun i c hct hh => ?_)
            (List.range n) .skip (fun hh => hh))
          rcases hh with hh | hh
          · exact hct hh
          · have := block_touches (lo := (compileF (w := w) L x (L + 1)).2.2) hh
              (.seq .alloc (.seq .atom (.seq .alloc (.seq .atom (.seq .alloc
                  (.seq .atom (.seq .alloc .atom)))))) :
                CodeShape _ (compileF (w := w) L x (L + 1)).2.2
                  ((compileF (w := w) L x (L + 1)).2.2 + 4))
              rfl (fun _ hh => hh)
            omega
        -- so the coverage established by the expression code survives it
        have hcov : ∀ j : ℕ, j < ((compileF (w := w) L x (L + 1)).2.2 : ℕ) - (L + 1) →
            s₂.regsAlloc (L + 1 + j) = true := by
          intro j hj
          have hjq : L + 1 + j < (compileF (w := w) L x (L + 1)).2.2 := by
            omega
          rw [hframe (L + 1 + j) hjq]
          exact exec_regsAlloc_of_touches h₁ hshape.straight hshape.noRegFree
            ((hshape.touches_iff _).mpr ⟨by omega, hjq⟩)
        have hd₃ : dr = -((((compileF (w := w) L x (L + 1)).2.2 : ℕ) - (L + 1) : ℕ) : ℤ) :=
          freeTemps_exec_net h₃ hcov
        obtain ⟨-, hp₃⟩ := freeTemps_space h₃
        have hp₃' := h₃.peak_nonneg
        simp only [outTemps]
        push_cast
        omega
  | .append a b =>
    intro s s' t d p h
    cases h with
    | seq h₁ h₂ =>
      obtain ⟨hd₁, hp₁⟩ := compileV_space h₁
      obtain ⟨hd₂, hp₂⟩ := compileV_space h₂
      have hl : (outTemps (w := w) L a : ℤ) ≤ outTemps (w := w) L (.append a b) := by
        exact_mod_cast le_max_left (outTemps (w := w) L a) (outTemps (w := w) L b)
      have hr : (outTemps (w := w) L b : ℤ) ≤ outTemps (w := w) L (.append a b) := by
        exact_mod_cast le_max_right (outTemps (w := w) L a) (outTemps (w := w) L b)
      omega

/-- The compiled output code touches no register below `L + 1`. -/
theorem compileV_not_touches {L : ℕ} {q : ℕ} (hq : q < L + 1) :
    ∀ {n : ℕ} (v : VExpr F n), ¬ (compileV (w := w) L v).RegAllocTouches q
  | _, .lit es => by
    refine foldl_not_touches (fun e c hc h => ?_) es.toList .skip (fun h => h)
    rcases h with h | h
    · exact hc h
    · have := block_touches h (compileF_shape L e (L + 1))
        (Nat.add_sub_cancel' (compileF_shape (w := w) L e (L + 1)).mono)
        (fun _ hh => hh)
      omega
  | _, .mapRange nn body => by
    intro h
    rcases h with h | h
    · refine foldl_not_touches (fun i c hc h => ?_) (List.range nn) .skip
        (fun h => h) h
      rcases h with h | h
      · exact hc h
      · have := block_touches h
          ((CodeShape.atom (a := L + 1)).seq (compileF_shape L body (L + 1)))
          (Nat.add_sub_cancel' (compileF_shape (w := w) L body (L + 1)).mono)
          (fun _ hh => hh)
        omega
    · exact h
  | _, .envRange offset => by
    refine foldl_not_touches (fun i c hc h => ?_) _ .skip (fun h => h)
    rcases h with h | h
    · exact hc h
    · have := block_touches h
        (.seq .alloc (.seq .atom (.seq .alloc .atom)) : CodeShape _ (L + 1) (L + 3))
        (by omega) (fun _ hh => hh)
      omega
  | _, .bitsOf x => by
    intro h
    have hshape := compileF_shape (w := w) L x (L + 1)
    have hmono := hshape.mono
    rcases h with h | h | h
    · have := (hshape.touches_iff q).mp h
      omega
    · refine foldl_not_touches (fun i c hc h => ?_) _ .skip (fun h => h) h
      rcases h with h | h
      · exact hc h
      · have := block_touches (lo := (compileF (w := w) L x (L + 1)).2.2) h
          (.seq .alloc (.seq .atom (.seq .alloc (.seq .atom (.seq .alloc
              (.seq .atom (.seq .alloc .atom)))))) :
            CodeShape _ (compileF (w := w) L x (L + 1)).2.2
              ((compileF (w := w) L x (L + 1)).2.2 + 4))
          rfl (fun _ hh => hh)
        omega
    · have := (freeTemps_touches_iff (L + 1) _ q).mp h
      omega
  | _, .append a b => by
    intro h
    rcases h with h | h
    · exact compileV_not_touches hq a h
    · exact compileV_not_touches hq b h

/-- **Compiled witgen code needs at most `m + irRegPeak` words of live memory** —
`m` for the output buffer, `L + 1` for the always-live locals + idx, and the worst
single-scope temp count. The *net* is still at most `m`: every register the program
acquires it also releases, and the scope-exit releases provably credit their full
words (the coverage lemma). -/
theorem compileIRCode_space_le {C : CostModel} {L m : ℕ} {steps : List (Step F)}
    {out : VExpr F m} {s s' : State w} {t : ℕ} {d p : ℤ}
    (hx : Exec C (compileIRCode (w := w) L steps out) s s' t d p) :
    d ≤ (m : ℤ) ∧ p ≤ (m : ℤ) + (irRegPeak (w := w) L steps out : ℤ) := by
  simp only [compileIRCode] at hx
  cases hx with
  | seq h₁ hr₁ =>
    cases h₁  -- memAllocI
    cases hr₁ with
    | @seq _ _ s₁ s₂ _ _ _ _ _ _ _ h₂ hr₂ =>
      cases hr₂ with
      | seq h₃ hr₃ =>
        cases h₃  -- imm L 0
        cases hr₃ with
        | @seq _ _ s₃ s₄ _ _ _ _ _ _ _ h₄ hr₄ =>
          cases hr₄ with
          | @seq _ _ _ s₅ _ _ _ _ _ _ _ h₅ h₆ =>
            -- allocRegs: bounded by its count, covers 0 .. L
            have hasha := allocRegs_shape (w := w) (L + 1)
            obtain ⟨hd₂, hp₂⟩ := exec_space_le_regAllocs h₂ hasha.straight
              hasha.heapFree
            have hka : (allocRegs (w := w) (L + 1)).regAllocs = L + 1 := by
              have := hasha.allocs_eq; omega
            rw [hka] at hd₂ hp₂
            have hcov₂ := allocRegs_exec_cov h₂
            -- steps and output: net-zero, peak = live set; both frame 0 .. L
            obtain ⟨hd₄, hp₄⟩ := compileSteps_space h₄
            obtain ⟨hd₅, hp₅⟩ := compileV_space h₅
            -- 0 .. L stay allocated to the end, so the epilogue credits exactly
            have hcov : ∀ j, j < L + 1 → s₅.regsAlloc (0 + j) = true := by
              intro j hj
              rw [Nat.zero_add,
                h₅.frame_regAlloc (compileV_not_touches (by omega) out),
                h₄.frame_regAlloc (compileSteps_not_touches (by omega) steps 0)]
              show (s₂.setReg L 0).regsAlloc j = true
              exact hcov₂ j hj
            have hd₆ := freeTemps_exec_net h₆ hcov
            obtain ⟨-, hp₆⟩ := freeTemps_space h₆
            have hp₆' := h₆.peak_nonneg
            -- assemble
            have hS : (stepsPeak (w := w) L steps : ℤ)
                ≤ (max (stepsPeak (w := w) L steps) (outTemps (w := w) L out) : ℕ) := by
              exact_mod_cast le_max_left _ _
            have hO : (outTemps (w := w) L out : ℤ)
                ≤ (max (stepsPeak (w := w) L steps) (outTemps (w := w) L out) : ℕ) := by
              exact_mod_cast le_max_right _ _
            simp only [irRegPeak]
            push_cast at hd₆ hS hO ⊢
            constructor <;> omega

/-- The certified register-file requirement of a whole witness program, read off
its structured IR (0 for the uncompilable `native`; the carried reimplementation's
for `certified`, pinned — like `compileIR` — to the ambient `FiniteField`
instance). -/
def WitgenIR.regPeak {m : ℕ} : WitgenIR F m → ℕ
  | .native _ => 0
  | .ir steps out
  | @Witgen.WitgenIR.certified _ _ _ _ steps out _ =>
    @irRegPeak F w instF steps.length m steps out

/-- The `compileIR` form of `compileIRCode_space_le`, at the compiler's own
`L = steps.length` (the only `L` the checked entry point ever uses): net at most
`m`, peak at most `m + regPeak`. -/
theorem compileIR_space_le {C : CostModel} {m : ℕ} {ir : WitgenIR F m} {code : Stmt w}
    {s s' : State w} {t : ℕ} {d p : ℤ}
    (hc : ∃ steps out, ir.irEval = (WitgenIR.ir steps out).eval ∧
        compileIR (w := w) steps.length (WitgenIR.ir steps out) = some code ∧
        WitgenIR.regPeak (w := w) ir = irRegPeak (w := w) steps.length steps out)
    (hx : Exec C code s s' t d p) :
    d ≤ (m : ℤ) ∧ p ≤ (m : ℤ) + (WitgenIR.regPeak (w := w) ir : ℤ) := by
  obtain ⟨steps, out, -, hIR, hpk⟩ := hc
  simp only [compileIR, Option.some.injEq] at hIR
  subst hIR
  rw [hpk]
  exact compileIRCode_space_le hx

/-! ## Checked-entry corollaries

The user-facing forms of the phase-2 theorems, stated about the checked entry point
`compile` (`WitgenCompile.lean`). `compile N ir = some code` already carries the
structure the raw theorems need, so these are thin corollaries of the `compileIR`
versions above. -/

/-- Everything the checked entry point emits is straight-line. -/
theorem compile_straight {N m : ℕ} {ir : WitgenIR F m} {code : Stmt 64}
    (hc : compile N ir = some code) : code.Straight := by
  obtain ⟨_, _, -, -, -, hIR⟩ := compile_toCompileIR hc
  exact compileIR_straight hIR

/-- **Checked-entry time exactness**: code accepted by `compile` runs in exactly its
static time, on every input. -/
theorem compile_time_eq {C : CostModel} {N m : ℕ} {ir : WitgenIR F m} {code : Stmt 64}
    {s s' : State 64} {t : ℕ} {d p : ℤ} (hc : compile N ir = some code)
    (hx : Exec C code s s' t d p) : t = code.staticTime C :=
  hx.straight_time_eq (compile_straight hc)

/-- **Checked-entry data independence**: two executions of code accepted by
`compile` take the same time, whatever their inputs (data-independence of the
abstract time counter — an ingredient of a constant-time argument, not by itself a
side-channel guarantee). -/
theorem compile_time_data_independent {C : CostModel} {N m : ℕ} {ir : WitgenIR F m}
    {code : Stmt 64} {s₁ s₁' s₂ s₂' : State 64} {t₁ t₂ : ℕ} {d₁ p₁ d₂ p₂ : ℤ}
    (hc : compile N ir = some code)
    (h₁ : Exec C code s₁ s₁' t₁ d₁ p₁) (h₂ : Exec C code s₂ s₂' t₂ d₂ p₂) : t₁ = t₂ :=
  h₁.straight_data_independent h₂ (compile_straight hc)

/-- **Checked-entry space bound, with the certified register component**: code
accepted by `compile` moves live memory by at most the output length `m` net (every
acquired register is released, and each release provably credits its word), and
peaks at most `m + regPeak` — the output buffer plus the honest register live set
(`L + 1` always-live locals + idx, plus the worst single step/element temp count),
exactly the register file a register allocator must provide. -/
theorem compile_space_le {C : CostModel} {N m : ℕ} {ir : WitgenIR F m} {code : Stmt 64}
    {s s' : State 64} {t : ℕ} {d p : ℤ} (hc : compile N ir = some code)
    (hx : Exec C code s s' t d p) :
    d ≤ (m : ℤ) ∧ p ≤ (m : ℤ) + (WitgenIR.regPeak (w := 64) ir : ℤ) := by
  refine compileIR_space_le ?_ hx
  cases ir with
  | native f => simp [compile] at hc
  | ir steps out =>
    simp only [compile] at hc
    obtain ⟨-, -, -, -, -, -, hIR⟩ := compileChecked_checks hc
    exact ⟨steps, out, rfl, hIR, rfl⟩
  | certified f steps out hcert =>
    simp only [compile] at hc
    obtain ⟨-, -, -, -, -, -, hIR⟩ := compileChecked_checks (instF := instF) hc
    exact ⟨steps, out, rfl, hIR, rfl⟩

/-! ## Concrete `< 2^40` bounds for the BabyBear test programs

The numbers below are *syntactic constants* of the compiled code — `#eval`ed here,
certified by `native_decide`, and equal to the running time of **every** execution
by `compileIR_time_eq`. -/

/-- The compiled `IsZeroField` witness program (test 1 of `WitgenCompile.lean` —
provably the witness IR of the Clean circuit `Gadgets.IsZeroField.circuit` itself,
see `isZeroCircuitIR_eq_testIsZero`), produced by the **checked entry point**
`compile` (environment size `N = 1`: the program reads only `var ⟨0⟩`):
mask-select `ite`, `feq`, and the unrolled Fermat inverse ladder over BabyBear. -/
def isZeroCompiled : Stmt 64 :=
  (compile 1 testIsZero).getD .skip

/-- On `testIsZero` all checks pass, so the checked entry agrees with the raw
compiler at `L = 0`. The `compilable`/`envBound` side conditions are certified by
`native_decide` (well-founded mutual recursions, which `rfl` cannot reduce). -/
private theorem compile_isZero_eq_compileIR :
    compile 1 testIsZero = compileIR (w := 64) 0 testIsZero :=
  compile_eq_compileIR_of_checks (by native_decide) (by native_decide)
    (by norm_num) (by norm_num) (by native_decide) (by native_decide)

/-- The checked entry point accepts `testIsZero` and emits `isZeroCompiled`. -/
theorem compile_testIsZero : compile 1 testIsZero = some isZeroCompiled := by
  show _ = some ((compile 1 testIsZero).getD .skip)
  rw [compile_isZero_eq_compileIR]
  rfl

/-- The raw-compiler form, used to relate the two paths. -/
theorem compileIR_testIsZero : compileIR (w := 64) 0 testIsZero = some isZeroCompiled :=
  compile_isZero_eq_compileIR ▸ compile_testIsZero

/-- The static time of the compiled `IsZero` witness under the uniform cost model —
the same 155 the differential test of `WitgenCompile.lean` measured by running it:
the 140 arithmetic ticks of the free-register era plus 15 register acquisitions
(1 idx + 14 temps; the matching releases are free). (`rfl` cannot evaluate this
because `toBits` — the ladder's bit list — is defined by well-founded recursion,
which does not reduce definitionally; `native_decide` does.) -/
theorem isZeroCompiled_staticTime_unit : isZeroCompiled.staticTime .unit = 155 := by
  native_decide

/-- The static time of the compiled `IsZero` witness under the calibrated
`CostModel.cycles` table (the 15 register acquisitions cost one cycle each there
too — `regAlloc + allocPerWord = 0 + 1`). -/
theorem isZeroCompiled_staticTime_cycles : isZeroCompiled.staticTime .cycles = 2105 := by
  native_decide

/-- info: some 155 -/
#guard_msgs in #eval witgenTime (w := 64) CostModel.unit 0 testIsZero

/-- info: some 2105 -/
#guard_msgs in #eval witgenTime (w := 64) CostModel.cycles 0 testIsZero

/- The same numbers through the checked entry point (no `L` to supply). -/
/-- info: some 155 -/
#guard_msgs in #eval (compile 1 testIsZero).map (·.staticTime CostModel.unit)

/-- info: some 2105 -/
#guard_msgs in #eval (compile 1 testIsZero).map (·.staticTime CostModel.cycles)

/- The output allocation is charged per word (`m * C.allocPerWord`) and every
register acquisition costs a tick, so relative to the free-register era each
program pays its acquisition count: `testXor` 11 → 19, `testSteps` 19 → 32,
`testBits` (idx + 2 expr temps + 4 temps per bit block, re-acquired per bit)
52 → 87, `testMapRange` (idx + 3 temps per element, re-acquired per element)
27 → 40. -/
/-- info: some 19 -/
#guard_msgs in #eval witgenTime (w := 64) CostModel.unit 0 testXor

/-- info: some 32 -/
#guard_msgs in #eval witgenTime (w := 64) CostModel.unit 1 testSteps

/-- info: some 87 -/
#guard_msgs in #eval witgenTime (w := 64) CostModel.unit 0 testBits

/-- info: some 40 -/
#guard_msgs in #eval witgenTime (w := 64) CostModel.unit 0 testMapRange

/- The certified register-file requirements (live set, not acquisition count):
`testIsZero` holds idx + all 14 temps of its one big expression; `testBits` holds
idx + the 2 expression temps + 4 per-bit temps; `testMapRange` idx + 3;
`testSteps` 2 (local + idx) + at most 5 in a scope. -/
/-- info: 15 -/
#guard_msgs in #eval WitgenIR.regPeak (w := 64) testIsZero

/-- info: 7 -/
#guard_msgs in #eval WitgenIR.regPeak (w := 64) testBits

/-- info: 4 -/
#guard_msgs in #eval WitgenIR.regPeak (w := 64) testMapRange

/-- info: 7 -/
#guard_msgs in #eval WitgenIR.regPeak (w := 64) testSteps

/-- **The headline, end to end**: every execution of the compiled `IsZero` witness
program terminates in fewer than `2^40` steps — in fact in exactly 155. -/
theorem isZero_witgen_lt_2_40 {s s' : State 64} {t : ℕ} {d p : ℤ}
    (h : Exec .unit isZeroCompiled s s' t d p) : t < 2 ^ 40 := by
  have ht := compile_time_eq compile_testIsZero h
  rw [isZeroCompiled_staticTime_unit] at ht
  omega

/-- The same bound under the calibrated cycles model: the reasoning is generic in
the cost model, only the pinned constant changes. -/
theorem isZero_witgen_cycles_lt_2_40 {s s' : State 64} {t : ℕ} {d p : ℤ}
    (h : Exec .cycles isZeroCompiled s s' t d p) : t < 2 ^ 40 := by
  have ht := compile_time_eq compile_testIsZero h
  rw [isZeroCompiled_staticTime_cycles] at ht
  omega

/-- The pinned register-file requirement of the `IsZero` witness: idx register plus
the 14 temporaries of its single output expression, all live at once inside the
mask-select/inverse computation. -/
theorem isZero_regPeak : WitgenIR.regPeak (w := 64) testIsZero = 15 := by
  native_decide

/-- Memory, exactly quantified: the compiled `IsZero` witness never grows live
memory by more than its one output word **plus its 15-register live set** — the
certified register-file requirement — and nets at most the single output word
(every register it acquires, it releases). -/
theorem isZero_witgen_space_le {s s' : State 64} {t : ℕ} {d p : ℤ}
    (h : Exec .unit isZeroCompiled s s' t d p) : d ≤ 1 ∧ p ≤ 16 := by
  have := compile_space_le compile_testIsZero h
  rw [isZero_regPeak] at this
  omega

/-- The `< 2^40` form of the memory bound. -/
theorem isZero_witgen_space_lt_2_40 {s s' : State 64} {t : ℕ} {d p : ℤ}
    (h : Exec .unit isZeroCompiled s s' t d p) : p < 2 ^ 40 := by
  have := (isZero_witgen_space_le h).2
  omega

/-! ### The complete witness list: pricing the copy generator, and the circuit total

`isZeroCircuit_witnessIRs` (`WitgenCompile.lean`) certifies that `testIsZero` and the
`<==` copy generator `isZeroCircuitCopyIR` are *all* the witness generators of the
Clean circuit `Gadgets.IsZeroField.circuit`. Pricing the copy generator too turns the
per-generator numbers into a certified total for the circuit's complete witness
list. -/

/-- The compiled `<==` copy generator of the `IsZeroField` circuit
(`isZeroCircuitCopyIR`, evaluating the circuit expression `1 - x * z`), produced by
the checked entry point. Environment size `N = 2`: at its offset 2, the generator
reads cells 0 (the input `x`) and 1 (the first witness `z`). -/
def isZeroCopyCompiled : Stmt 64 :=
  (compile 2 isZeroCircuitCopyIR).getD .skip

/-- On the copy generator all checks pass, so the checked entry agrees with the raw
compiler at `L = 0`. -/
private theorem compile_isZeroCopy_eq_compileIR :
    compile 2 isZeroCircuitCopyIR = compileIR (w := 64) 0 isZeroCircuitCopyIR :=
  compile_eq_compileIR_of_checks (by native_decide) (by native_decide)
    (by norm_num) (by norm_num) (by native_decide) (by native_decide)

/-- The checked entry point accepts the copy generator and emits
`isZeroCopyCompiled`. -/
theorem compile_isZeroCircuitCopyIR :
    compile 2 isZeroCircuitCopyIR = some isZeroCopyCompiled := by
  show _ = some ((compile 2 isZeroCircuitCopyIR).getD .skip)
  rw [compile_isZeroCopy_eq_compileIR]
  rfl

/-- The static time of the compiled copy generator under the uniform cost model:
32 unit steps (two environment reads, the constants, and two field
multiply/add-reduce patterns — no inverse ladder — at 19 arithmetic ticks, plus
13 register acquisitions: 1 idx + 12 temps). -/
theorem isZeroCopyCompiled_staticTime_unit :
    isZeroCopyCompiled.staticTime .unit = 32 := by
  native_decide

/-- The static time of the compiled copy generator under the calibrated
`CostModel.cycles` table. -/
theorem isZeroCopyCompiled_staticTime_cycles :
    isZeroCopyCompiled.staticTime .cycles = 182 := by
  native_decide

/- The same numbers through the checked entry point and the honest partial clock
(`staticTime?` cannot quote a number for loopy code). -/
/-- info: some (some 32) -/
#guard_msgs in #eval (compile 2 isZeroCircuitCopyIR).map (·.staticTime? CostModel.unit)

/-- info: some (some 182) -/
#guard_msgs in #eval (compile 2 isZeroCircuitCopyIR).map (·.staticTime? CostModel.cycles)

/-- **Total witgen time for the complete `IsZeroField` circuit**: by
`isZeroCircuit_witnessIRs`, `testIsZero` (= the extracted `isZeroCircuitIR`) and
`isZeroCircuitCopyIR` are *all* the witness generators of
`Gadgets.IsZeroField.circuit`, so executing their two compiled programs is the
circuit's entire witness generation — and it takes exactly `155 + 32 = 187` unit
steps, on every input. -/
theorem isZeroCircuit_total_witgen_time_unit {s₁ s₁' s₂ s₂' : State 64}
    {t₁ t₂ : ℕ} {d₁ p₁ d₂ p₂ : ℤ}
    (h₁ : Exec .unit isZeroCompiled s₁ s₁' t₁ d₁ p₁)
    (h₂ : Exec .unit isZeroCopyCompiled s₂ s₂' t₂ d₂ p₂) :
    t₁ + t₂ = 155 + 32 := by
  rw [compile_time_eq compile_testIsZero h₁, isZeroCompiled_staticTime_unit,
    compile_time_eq compile_isZeroCircuitCopyIR h₂, isZeroCopyCompiled_staticTime_unit]

/-- The `< 2 ^ 40` corollary for the circuit's complete witness generation. -/
theorem isZeroCircuit_total_witgen_lt_2_40 {s₁ s₁' s₂ s₂' : State 64}
    {t₁ t₂ : ℕ} {d₁ p₁ d₂ p₂ : ℤ}
    (h₁ : Exec .unit isZeroCompiled s₁ s₁' t₁ d₁ p₁)
    (h₂ : Exec .unit isZeroCopyCompiled s₂ s₂' t₂ d₂ p₂) :
    t₁ + t₂ < 2 ^ 40 := by
  have := isZeroCircuit_total_witgen_time_unit h₁ h₂
  omega

/-! ### Certified native witnesses: the cost bound transports to the closure

`isZeroCertified` (`WitgenCompile.lean`) keeps the native closure `isZeroNative` as
its evaluation fast path, but `compile` accepts it — through its certified IR
reimplementation — and emits *literally* `testIsZero`'s code. So the exact-cost
theorems apply verbatim: a witness whose Lean-side evaluation is an arbitrary
closure now carries a machine-checked, input-independent step count, something a
bare `.native` closure can never have (cost is intensional; Lean functions are
extensional). -/

/-- The checked entry point accepts the certified program and emits exactly the code
of its IR reimplementation — `isZeroCompiled`. The first step is definitional
(`compile_certified_eq_ir`). -/
theorem compile_isZeroCertified : compile 1 isZeroCertified = some isZeroCompiled :=
  compile_testIsZero

/- The certified program's pinned cost numerals: the same 155 unit steps / 2105
cycles as `testIsZero`, now certified *for the native closure's witness*. -/
/-- info: some 155 -/
#guard_msgs in #eval (compile 1 isZeroCertified).map (·.staticTime CostModel.unit)

/-- info: some 2105 -/
#guard_msgs in #eval (compile 1 isZeroCertified).map (·.staticTime CostModel.cycles)

/-- **Exact time for a certified native witness**: every execution of the code
compiled from `isZeroCertified` — the program whose prover-side evaluation is the
native closure `isZeroNative` — takes exactly 155 unit steps. -/
theorem isZeroCertified_witgen_time_unit {s s' : State 64} {t : ℕ} {d p : ℤ}
    (h : Exec .unit isZeroCompiled s s' t d p) : t = 155 := by
  rw [compile_time_eq compile_isZeroCertified h, isZeroCompiled_staticTime_unit]

/-- The `< 2^40` form for the certified native witness. -/
theorem isZeroCertified_witgen_lt_2_40 {s s' : State 64} {t : ℕ} {d p : ℤ}
    (h : Exec .unit isZeroCompiled s s' t d p) : t < 2 ^ 40 := by
  have := isZeroCertified_witgen_time_unit h
  omega

end Caliper.WitgenCompile
