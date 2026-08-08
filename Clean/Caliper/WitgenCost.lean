import Clean.Caliper.WitgenCompile

/-!
# Cost bounds for compiled witness generation: "witgen in < 2^40 steps, machine-checked"

Phase 2 of the witgen compiler: machine-checked *cost* bounds for the code that
`Clean/Caliper/WitgenCompile.lean` emits.

The whole file rests on one structural fact, proved here by syntactic induction over
the compiler: **everything the compiler emits is straight-line** (no `ifNZ`, no
`whileNZ` — `ite` is a mask select, `mapRange`/`envRange`/`bitsOf` are unrolled, the
Fermat inverse ladder is unrolled over the generation-time bits of `p - 2`), and,
apart from the single output-buffer `bufAlloc` in `compileIR`'s prologue,
**allocation-free** (`bufPush` moves the fill level inside already-charged capacity,
so it is alloc-free by definition).

Consequences, all machine-checked below:

* **Time is a syntactic constant.** By `Exec.straight_time_eq`, every execution of a
  compiled program takes *exactly* `code.staticTime C` time units — an *equality*,
  not just a bound, and the same number on every input (`witgenTime_data_independent`;
  this is also a constant-time / side-channel statement). `staticTime` is a plain
  recursive function of the syntax, so the cost of a concrete compiled program is a
  numeral: computable by `#eval` and certified by evaluation (`native_decide` here,
  since `toBits` is well-founded recursion, which `rfl` cannot reduce) — no
  execution, no semantics, no fuel involved.
* **Memory is bounded by the output length.** The prologue's single `bufAlloc`
  charges at most `m` words (the static output length); everything after it is
  alloc-free, so both the net live-memory change and the peak stay `≤ m`
  (`compileIR_space_le`).
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

/-! ## Straight-line, allocation-free code

`Stmt.Straight` and `Stmt.AllocFree` have the same conjunction structure over `seq`,
and every instruction the scalar compilers emit satisfies both, so we prove the two
predicates together in one induction and project at the end. -/

/-- `seq` preserves straight-line-and-alloc-free. -/
theorem straightAF_seq {c₁ c₂ : Stmt w} (h₁ : c₁.Straight ∧ c₁.AllocFree)
    (h₂ : c₂.Straight ∧ c₂.AllocFree) :
    (c₁ ;; c₂).Straight ∧ (c₁ ;; c₂).AllocFree :=
  ⟨⟨h₁.1, h₂.1⟩, ⟨h₁.2, h₂.2⟩⟩

/-- A `List.foldl` whose step preserves straight-line-and-alloc-free preserves it.
This is the induction skeleton for `invLadder` and the unrolled `compileV` loops. -/
theorem foldl_straightAF {α : Type} {f : Stmt w → α → Stmt w}
    (hf : ∀ c a, c.Straight ∧ c.AllocFree → (f c a).Straight ∧ (f c a).AllocFree) :
    ∀ (l : List α) (init : Stmt w), init.Straight ∧ init.AllocFree →
      (l.foldl f init).Straight ∧ (l.foldl f init).AllocFree
  | [], _, h => h
  | a :: l, init, h => foldl_straightAF hf l (f init a) (hf init a h)

/-- The field-reduction pattern is straight-line and alloc-free. -/
theorem fieldOp_straightAF (p : ℕ) (op : BinOp) (a b next : Reg) :
    (fieldOp (w := w) p op a b next).1.Straight ∧
      (fieldOp (w := w) p op a b next).1.AllocFree :=
  ⟨⟨trivial, trivial, trivial⟩, ⟨trivial, trivial, trivial⟩⟩

/-- The mask select is straight-line and alloc-free. -/
theorem selectCode_straightAF (flag t e next : Reg) :
    (selectCode (w := w) flag t e next).1.Straight ∧
      (selectCode (w := w) flag t e next).1.AllocFree :=
  ⟨⟨trivial, trivial, trivial, trivial, trivial⟩,
   ⟨trivial, trivial, trivial, trivial, trivial⟩⟩

/-- The Fermat inverse ladder is straight-line and alloc-free (induction over the
generation-time bit list). -/
theorem invLadder_straightAF (p : ℕ) (acc x t : Reg) :
    (invLadder (w := w) p acc x t).Straight ∧ (invLadder (w := w) p acc x t).AllocFree := by
  unfold invLadder
  refine foldl_straightAF (fun c b hc => ?_) _ _ ⟨trivial, trivial⟩
  cases b
  · exact ⟨⟨hc.1, trivial, trivial⟩, ⟨hc.2, trivial, trivial⟩⟩
  · exact ⟨⟨⟨hc.1, trivial, trivial⟩, trivial, trivial⟩,
      ⟨⟨hc.2, trivial, trivial⟩, trivial, trivial⟩⟩

variable [FiniteField F]

/-- Compiled circuit expressions are straight-line and alloc-free. -/
theorem compileExpr_straightAF : ∀ (e : Expression F) (next : Reg),
    (compileExpr (w := w) e next).1.Straight ∧ (compileExpr (w := w) e next).1.AllocFree
  | .var _, _ => ⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩⟩
  | .const _, _ => ⟨trivial, trivial⟩
  | .add x y, next =>
    straightAF_seq (compileExpr_straightAF x next)
      (straightAF_seq (compileExpr_straightAF y (compileExpr (w := w) x next).2.2)
        (fieldOp_straightAF _ _ _ _ _))
  | .mul x y, next =>
    straightAF_seq (compileExpr_straightAF x next)
      (straightAF_seq (compileExpr_straightAF y (compileExpr (w := w) x next).2.2)
        (fieldOp_straightAF _ _ _ _ _))

mutual

/-- Compiled field-sorted expressions are straight-line and alloc-free. -/
theorem compileF_straightAF (L : ℕ) : ∀ (e : FExpr F) (next : Reg),
    (compileF (w := w) L e next).1.Straight ∧ (compileF (w := w) L e next).1.AllocFree
  | .expr e, next => compileExpr_straightAF e next
  | .const _, _ => ⟨trivial, trivial⟩
  | .localVar _, _ => ⟨trivial, trivial⟩
  | .add x y, next =>
    straightAF_seq (compileF_straightAF L x next)
      (straightAF_seq (compileF_straightAF L y (compileF (w := w) L x next).2.2)
        (fieldOp_straightAF _ _ _ _ _))
  | .mul x y, next =>
    straightAF_seq (compileF_straightAF L x next)
      (straightAF_seq (compileF_straightAF L y (compileF (w := w) L x next).2.2)
        (fieldOp_straightAF _ _ _ _ _))
  | .inv x, next =>
    straightAF_seq (compileF_straightAF L x next)
      (straightAF_seq ⟨trivial, trivial⟩
        (straightAF_seq ⟨trivial, trivial⟩ (invLadder_straightAF _ _ _ _)))
  | .ofU64 n, next =>
    straightAF_seq (compileU_straightAF L n next)
      ⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩⟩
  | .ite c t e, next =>
    straightAF_seq (compileB_straightAF L c next)
      (straightAF_seq (compileF_straightAF L t (compileB (w := w) L c next).2.2)
        (straightAF_seq
          (compileF_straightAF L e (compileF (w := w) L t (compileB (w := w) L c next).2.2).2.2)
          (selectCode_straightAF _ _ _ _)))
  | .listGet .., _ => ⟨trivial, trivial⟩
  | .dataGet .., _ => ⟨trivial, trivial⟩
  | .hintGet .., _ => ⟨trivial, trivial⟩

/-- Compiled u64-sorted expressions are straight-line and alloc-free. -/
theorem compileU_straightAF (L : ℕ) : ∀ (e : U64Expr F) (next : Reg),
    (compileU (w := w) L e next).1.Straight ∧ (compileU (w := w) L e next).1.AllocFree
  | .const _, _ => ⟨trivial, trivial⟩
  | .val x, next =>
    straightAF_seq (compileF_straightAF L x next) ⟨trivial, trivial⟩
  | .idx, _ => ⟨trivial, trivial⟩
  | .localVar _, _ => ⟨trivial, trivial⟩
  | .add x y, next =>
    straightAF_seq (compileU_straightAF L x next)
      (straightAF_seq (compileU_straightAF L y (compileU (w := w) L x next).2.2)
        ⟨trivial, trivial⟩)
  | .mul x y, next =>
    straightAF_seq (compileU_straightAF L x next)
      (straightAF_seq (compileU_straightAF L y (compileU (w := w) L x next).2.2)
        ⟨trivial, trivial⟩)
  | .div x y, next =>
    straightAF_seq (compileU_straightAF L x next)
      (straightAF_seq (compileU_straightAF L y (compileU (w := w) L x next).2.2)
        ⟨trivial, trivial⟩)
  | .mod x y, next =>
    straightAF_seq (compileU_straightAF L x next)
      (straightAF_seq (compileU_straightAF L y (compileU (w := w) L x next).2.2)
        ⟨trivial, trivial⟩)
  | .land x y, next =>
    straightAF_seq (compileU_straightAF L x next)
      (straightAF_seq (compileU_straightAF L y (compileU (w := w) L x next).2.2)
        ⟨trivial, trivial⟩)
  | .lor x y, next =>
    straightAF_seq (compileU_straightAF L x next)
      (straightAF_seq (compileU_straightAF L y (compileU (w := w) L x next).2.2)
        ⟨trivial, trivial⟩)
  | .lxor x y, next =>
    straightAF_seq (compileU_straightAF L x next)
      (straightAF_seq (compileU_straightAF L y (compileU (w := w) L x next).2.2)
        ⟨trivial, trivial⟩)
  | .shiftL x y, next =>
    straightAF_seq (compileU_straightAF L x next)
      (straightAF_seq (compileU_straightAF L y (compileU (w := w) L x next).2.2)
        ⟨⟨trivial, trivial, trivial⟩, ⟨trivial, trivial, trivial⟩⟩)
  | .shiftR x y, next =>
    straightAF_seq (compileU_straightAF L x next)
      (straightAF_seq (compileU_straightAF L y (compileU (w := w) L x next).2.2)
        ⟨⟨trivial, trivial, trivial⟩, ⟨trivial, trivial, trivial⟩⟩)
  | .ite c t e, next =>
    straightAF_seq (compileB_straightAF L c next)
      (straightAF_seq (compileU_straightAF L t (compileB (w := w) L c next).2.2)
        (straightAF_seq
          (compileU_straightAF L e (compileU (w := w) L t (compileB (w := w) L c next).2.2).2.2)
          (selectCode_straightAF _ _ _ _)))

/-- Compiled conditions are straight-line and alloc-free. -/
theorem compileB_straightAF (L : ℕ) : ∀ (e : BExpr F) (next : Reg),
    (compileB (w := w) L e next).1.Straight ∧ (compileB (w := w) L e next).1.AllocFree
  | .true, _ => ⟨trivial, trivial⟩
  | .false, _ => ⟨trivial, trivial⟩
  | .feq x y, next =>
    straightAF_seq (compileF_straightAF L x next)
      (straightAF_seq (compileF_straightAF L y (compileF (w := w) L x next).2.2)
        ⟨trivial, trivial⟩)
  | .neq x y, next =>
    straightAF_seq (compileU_straightAF L x next)
      (straightAF_seq (compileU_straightAF L y (compileU (w := w) L x next).2.2)
        ⟨trivial, trivial⟩)
  | .lt x y, next =>
    straightAF_seq (compileU_straightAF L x next)
      (straightAF_seq (compileU_straightAF L y (compileU (w := w) L x next).2.2)
        ⟨trivial, trivial⟩)
  | .flt x y, next =>
    straightAF_seq (compileF_straightAF L x next)
      (straightAF_seq (compileF_straightAF L y (compileF (w := w) L x next).2.2)
        ⟨trivial, trivial⟩)
  | .bit x _, next =>
    straightAF_seq (compileF_straightAF L x next)
      ⟨⟨trivial, trivial, trivial, trivial⟩, ⟨trivial, trivial, trivial, trivial⟩⟩
  | .not b, next =>
    straightAF_seq (compileB_straightAF L b next) ⟨trivial, trivial⟩
  | .and x y, next =>
    straightAF_seq (compileB_straightAF L x next)
      (straightAF_seq (compileB_straightAF L y (compileB (w := w) L x next).2.2)
        ⟨trivial, trivial⟩)

end

/-- Compiled `let`-steps are straight-line and alloc-free. -/
theorem compileStep_straightAF (L : ℕ) (j : Reg) : ∀ (s : Step F),
    (compileStep (w := w) L j s).Straight ∧ (compileStep (w := w) L j s).AllocFree
  | .letF e => straightAF_seq (compileF_straightAF L e (L + 1)) ⟨trivial, trivial⟩
  | .letU e => straightAF_seq (compileU_straightAF L e (L + 1)) ⟨trivial, trivial⟩

/-- Compiled step lists are straight-line and alloc-free. -/
theorem compileSteps_straightAF (L : ℕ) : ∀ (steps : List (Step F)) (j : ℕ),
    (compileSteps (w := w) L steps j).Straight ∧ (compileSteps (w := w) L steps j).AllocFree
  | [], _ => ⟨trivial, trivial⟩
  | s :: rest, j =>
    straightAF_seq (compileStep_straightAF L j s) (compileSteps_straightAF L rest (j + 1))

/-- Compiled vector outputs are straight-line and alloc-free — in particular the
output `bufPush`es are alloc-free, since pushed words were charged at `bufAlloc`. -/
theorem compileV_straightAF (L : ℕ) : ∀ {n : ℕ} (v : VExpr F n),
    (compileV (w := w) L v).Straight ∧ (compileV (w := w) L v).AllocFree
  | _, .lit es => by
    refine foldl_straightAF (fun c e hc => ?_) es.toList .skip ⟨trivial, trivial⟩
    exact straightAF_seq hc
      (straightAF_seq (compileF_straightAF L e (L + 1)) ⟨trivial, trivial⟩)
  | _, .mapRange n body => by
    refine straightAF_seq
      (foldl_straightAF (fun c i hc => ?_) (List.range n) .skip ⟨trivial, trivial⟩)
      ⟨trivial, trivial⟩
    exact straightAF_seq hc
      (straightAF_seq ⟨trivial, trivial⟩
        (straightAF_seq (compileF_straightAF L body (L + 1)) ⟨trivial, trivial⟩))
  | n, .envRange offset => by
    refine foldl_straightAF (fun c i hc => ?_) (List.range n) .skip ⟨trivial, trivial⟩
    exact straightAF_seq hc
      ⟨⟨trivial, trivial, trivial⟩, ⟨trivial, trivial, trivial⟩⟩
  | n, .bitsOf x => by
    refine straightAF_seq (compileF_straightAF L x (L + 1))
      (foldl_straightAF (fun c i hc => ?_) (List.range n) .skip ⟨trivial, trivial⟩)
    exact straightAF_seq hc
      ⟨⟨trivial, trivial, trivial, trivial, trivial⟩,
       ⟨trivial, trivial, trivial, trivial, trivial⟩⟩
  | _, .append a b =>
    straightAF_seq (compileV_straightAF L a) (compileV_straightAF L b)

/-- **Everything `compileIR` emits is straight-line**: no `ifNZ`, no `whileNZ`,
anywhere. This is the fact that turns running time into a syntactic constant. -/
theorem compileIR_straight {L : ℕ} {m : ℕ} {ir : WitgenIR F m} {code : Stmt w}
    (h : compileIR (w := w) L ir = some code) : code.Straight := by
  cases ir with
  | native f => simp [compileIR] at h
  | ir steps out =>
    simp only [compileIR, Option.some.injEq] at h
    subst h
    exact ⟨trivial, trivial, trivial, (compileSteps_straightAF L steps 0).1,
      (compileV_straightAF L out).1⟩

/-! ## The time theorem: witgen time is a syntactic constant -/

/-- The running time of a compiled witness program, read off the *syntax* by
`Stmt.staticTime` — no execution involved. By `witgenTime_eq` below, this is the
exact running time of every execution. -/
def witgenTime (C : CostModel) (L : ℕ) {m : ℕ} (ir : WitgenIR F m) : Option ℕ :=
  (compileIR (w := w) L ir).map (·.staticTime C)

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
  rw [witgenTime, hc, Option.map_some, Option.some.injEq] at hT
  rw [compileIR_time_eq hc hx, hT]

/-- **Data independence**: two executions of the same compiled witness program take
the same time, whatever their inputs. (This is also a constant-time / side-channel
statement.) -/
theorem witgenTime_data_independent {C : CostModel} {L m : ℕ} {ir : WitgenIR F m}
    {code : Stmt w} {s₁ s₁' s₂ s₂' : State w} {t₁ t₂ : ℕ} {d₁ p₁ d₂ p₂ : ℤ}
    (hc : compileIR (w := w) L ir = some code)
    (h₁ : Exec C code s₁ s₁' t₁ d₁ p₁) (h₂ : Exec C code s₂ s₂' t₂ d₂ p₂) : t₁ = t₂ :=
  h₁.straight_data_independent h₂ (compileIR_straight hc)

/-! ## The memory theorem: witgen space is bounded by the output length -/

/-- **Compiled witgen code needs at most `m` words of memory** (`m` = the static
output length): the single prologue `bufAlloc` charges at most `m`, and everything
else is alloc-free. Both the net live-memory change and the peak are bounded. -/
theorem compileIR_space_le {C : CostModel} {L m : ℕ} {ir : WitgenIR F m} {code : Stmt w}
    {s s' : State w} {t : ℕ} {d p : ℤ} (hc : compileIR (w := w) L ir = some code)
    (hx : Exec C code s s' t d p) : d ≤ (m : ℤ) ∧ p ≤ (m : ℤ) := by
  cases ir with
  | native f => simp [compileIR] at hc
  | ir steps out =>
    simp only [compileIR, Option.some.injEq] at hc
    subst hc
    -- destructure `imm ;; (bufAlloc ;; rest)` and its costs
    cases hx with
    | seq h₁ hrest =>
      cases h₁
      cases hrest with
      | seq h₂ hrest₂ =>
        cases h₂
        -- the rest (idx-zeroing, steps, output pushes) is alloc-free
        obtain ⟨hd, hp⟩ := hrest₂.allocFree_space
          ⟨trivial, (compileSteps_straightAF L steps 0).2, (compileV_straightAF L out).2⟩
        -- the single bufAlloc charges `(ofNat w m).toNat - oldCap ≤ m`
        have hm : (BitVec.ofNat w m).toNat ≤ m := by
          rw [BitVec.toNat_ofNat]; exact Nat.mod_le _ _
        simp only [regs_setReg_self, caps_setReg]
        omega

/-! ## Checked-entry corollaries

The user-facing forms of the phase-2 theorems, stated about the checked entry point
`compile` (`WitgenCompile.lean`). `compile N ir = some code` already carries the
structure the raw theorems need, so these are thin corollaries of the `compileIR`
versions above. -/

/-- Everything the checked entry point emits is straight-line. -/
theorem compile_straight {N m : ℕ} {ir : WitgenIR F m} {code : Stmt 64}
    (hc : compile N ir = some code) : code.Straight := by
  obtain ⟨_, _, -, hIR⟩ := compile_toCompileIR hc
  exact compileIR_straight hIR

/-- **Checked-entry time exactness**: code accepted by `compile` runs in exactly its
static time, on every input. -/
theorem compile_time_eq {C : CostModel} {N m : ℕ} {ir : WitgenIR F m} {code : Stmt 64}
    {s s' : State 64} {t : ℕ} {d p : ℤ} (hc : compile N ir = some code)
    (hx : Exec C code s s' t d p) : t = code.staticTime C :=
  hx.straight_time_eq (compile_straight hc)

/-- **Checked-entry data independence**: two executions of code accepted by
`compile` take the same time, whatever their inputs (a constant-time / side-channel
statement). -/
theorem compile_time_data_independent {C : CostModel} {N m : ℕ} {ir : WitgenIR F m}
    {code : Stmt 64} {s₁ s₁' s₂ s₂' : State 64} {t₁ t₂ : ℕ} {d₁ p₁ d₂ p₂ : ℤ}
    (hc : compile N ir = some code)
    (h₁ : Exec C code s₁ s₁' t₁ d₁ p₁) (h₂ : Exec C code s₂ s₂' t₂ d₂ p₂) : t₁ = t₂ :=
  h₁.straight_data_independent h₂ (compile_straight hc)

/-- **Checked-entry space bound**: code accepted by `compile` needs at most `m`
words of memory (`m` = the static output length), both net and peak. -/
theorem compile_space_le {C : CostModel} {N m : ℕ} {ir : WitgenIR F m} {code : Stmt 64}
    {s s' : State 64} {t : ℕ} {d p : ℤ} (hc : compile N ir = some code)
    (hx : Exec C code s s' t d p) : d ≤ (m : ℤ) ∧ p ≤ (m : ℤ) := by
  obtain ⟨_, _, -, hIR⟩ := compile_toCompileIR hc
  exact compileIR_space_le hIR hx

/-! ## Concrete `< 2^40` bounds for the BabyBear test programs

The numbers below are *syntactic constants* of the compiled code — `#eval`ed here,
certified by `native_decide`, and equal to the running time of **every** execution
by `compileIR_time_eq`. -/

/-- The compiled `IsZeroField` witness program (test 1 of `WitgenCompile.lean`),
produced by the **checked entry point** `compile` (environment size `N = 1`: the
program reads only `var ⟨0⟩`): mask-select `ite`, `feq`, and the unrolled Fermat
inverse ladder over BabyBear. -/
def isZeroCompiled : Stmt 64 :=
  (compile 1 testIsZero).getD .skip

/-- On `testIsZero` all checks pass, so the checked entry agrees with the raw
compiler at `L = 0`. The `compilable`/`envBound` side conditions are certified by
`native_decide` (well-founded mutual recursions, which `rfl` cannot reduce). -/
private theorem compile_isZero_eq_compileIR :
    compile 1 testIsZero = compileIR (w := 64) 0 testIsZero :=
  compile_eq_compileIR_of_checks (by native_decide) (by native_decide)
    (by norm_num) (by norm_num)

/-- The checked entry point accepts `testIsZero` and emits `isZeroCompiled`. -/
theorem compile_testIsZero : compile 1 testIsZero = some isZeroCompiled := by
  show _ = some ((compile 1 testIsZero).getD .skip)
  rw [compile_isZero_eq_compileIR]
  rfl

/-- The raw-compiler form, used to relate the two paths. -/
theorem compileIR_testIsZero : compileIR (w := 64) 0 testIsZero = some isZeroCompiled :=
  compile_isZero_eq_compileIR ▸ compile_testIsZero

/-- The static time of the compiled `IsZero` witness under the uniform cost model —
the same 140 the differential test of `WitgenCompile.lean` measured by running it.
(`rfl` cannot evaluate this because `toBits` — the ladder's bit list — is defined by
well-founded recursion, which does not reduce definitionally; `native_decide` does.) -/
theorem isZeroCompiled_staticTime_unit : isZeroCompiled.staticTime .unit = 140 := by
  native_decide

/-- The static time of the compiled `IsZero` witness under the calibrated
`CostModel.cycles` table. -/
theorem isZeroCompiled_staticTime_cycles : isZeroCompiled.staticTime .cycles = 2090 := by
  native_decide

/-- info: some 140 -/
#guard_msgs in #eval witgenTime (w := 64) CostModel.unit 0 testIsZero

/-- info: some 2090 -/
#guard_msgs in #eval witgenTime (w := 64) CostModel.cycles 0 testIsZero

/- The same numbers through the checked entry point (no `L` to supply). -/
/-- info: some 140 -/
#guard_msgs in #eval (compile 1 testIsZero).map (·.staticTime CostModel.unit)

/-- info: some 2090 -/
#guard_msgs in #eval (compile 1 testIsZero).map (·.staticTime CostModel.cycles)

/-- info: some 13 -/
#guard_msgs in #eval witgenTime (w := 64) CostModel.unit 0 testXor

/-- info: some 21 -/
#guard_msgs in #eval witgenTime (w := 64) CostModel.unit 1 testSteps

/-- info: some 45 -/
#guard_msgs in #eval witgenTime (w := 64) CostModel.unit 0 testBits

/-- info: some 32 -/
#guard_msgs in #eval witgenTime (w := 64) CostModel.unit 0 testMapRange

/-- **The headline, end to end**: every execution of the compiled `IsZero` witness
program terminates in fewer than `2^40` steps — in fact in exactly 140. -/
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

/-- Memory, same shape: the compiled `IsZero` witness never grows live memory by
more than its single output word — in particular far below `2^40`. -/
theorem isZero_witgen_peak_le_one {s s' : State 64} {t : ℕ} {d p : ℤ}
    (h : Exec .unit isZeroCompiled s s' t d p) : p ≤ 1 := by
  have := (compile_space_le compile_testIsZero h).2
  omega

/-- The `< 2^40` form of the memory bound. -/
theorem isZero_witgen_space_lt_2_40 {s s' : State 64} {t : ℕ} {d p : ℤ}
    (h : Exec .unit isZeroCompiled s s' t d p) : p < 2 ^ 40 := by
  have := isZero_witgen_peak_le_one h
  omega

end Caliper.WitgenCompile
