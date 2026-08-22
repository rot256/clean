import Caliper.Core
import Caliper.Triple
import Mathlib.Tactic

/-!
# Register-only code

`Stmt.RegOnly` is code built from `skip`, `seq`, `imm`, `mov`, `un`, `bin` and `ifNZ`:
no memory, no allocation, no loop. Two things are true of it that are not true of
`Stmt` in general, and both are what make a *time bound* for a gadget free of any
hypothesis about the data it operates on.

* It always executes (`RegOnly.exec`). Every other instruction can get stuck —
  `memLoad` needs its index in range, `memPush` needs capacity — so an execution has
  to be constructed alongside a proof that the data is well formed. Register code
  cannot fail, so its `Triple`s carry no data precondition.
* Its time is at most `staticTime` and it moves no memory, so its `Triple` bounds are
  `(staticTime, 0, 0)` no matter which branches run.

That combination is what a counted loop needs: the loop's time bound follows from the
counter alone, and the body's contribution is a number read off the syntax.
-/

namespace Caliper

variable {w : ℕ} {C : CostModel}

/-- Registers only: no memory, no allocation, no loop. -/
def Stmt.RegOnly : Stmt w → Prop
  | .skip => True
  | .seq c₁ c₂ => c₁.RegOnly ∧ c₂.RegOnly
  | .imm .. => True
  | .mov .. => True
  | .un .. => True
  | .bin .. => True
  | .ifNZ _ t e => t.RegOnly ∧ e.RegOnly
  | _ => False

@[simp] theorem RegOnly_skip : (Stmt.skip (w := w)).RegOnly := trivial
@[simp] theorem RegOnly_seq (c₁ c₂ : Stmt w) :
    (c₁ ;; c₂).RegOnly ↔ c₁.RegOnly ∧ c₂.RegOnly := Iff.rfl
@[simp] theorem RegOnly_imm (d : Reg) (v : Word w) : (Stmt.imm d v).RegOnly := trivial
@[simp] theorem RegOnly_mov (d a : Reg) : (Stmt.mov (w := w) d a).RegOnly := trivial
@[simp] theorem RegOnly_un (op : UnOp) (d a : Reg) :
    (Stmt.un (w := w) op d a).RegOnly := trivial
@[simp] theorem RegOnly_bin (op : BinOp) (d a b : Reg) :
    (Stmt.bin (w := w) op d a b).RegOnly := trivial
@[simp] theorem RegOnly_ifNZ (r : Reg) (t e : Stmt w) :
    (Stmt.ifNZ r t e).RegOnly ↔ t.RegOnly ∧ e.RegOnly := Iff.rfl

/-- **Register-only code always executes**, within its static time and moving no
memory. No hypothesis about the state appears: that is the whole point. -/
theorem Stmt.RegOnly.exec {c : Stmt w} (h : c.RegOnly) (s : State w) :
    ∃ s' t, Exec C c s s' t 0 0 ∧ t ≤ c.staticTime C := by
  induction c generalizing s with
  | skip => exact ⟨s, 0, .skip, by simp [Stmt.staticTime]⟩
  | seq c₁ c₂ ih₁ ih₂ =>
    obtain ⟨s₁, t₁, he₁, ht₁⟩ := ih₁ h.1 s
    obtain ⟨s₂, t₂, he₂, ht₂⟩ := ih₂ h.2 s₁
    refine ⟨s₂, t₁ + t₂, ?_, by simp [Stmt.staticTime]; omega⟩
    simpa using Exec.seq he₁ he₂
  | imm => exact ⟨_, _, .imm, le_refl _⟩
  | mov => exact ⟨_, _, .mov, le_refl _⟩
  | un => exact ⟨_, _, .un, le_refl _⟩
  | bin => exact ⟨_, _, .bin, le_refl _⟩
  | ifNZ r t e iht ihe =>
    by_cases hr : s.regs r = 0
    · obtain ⟨s', t', he, ht⟩ := ihe h.2 s
      exact ⟨s', C.branch + t', .ifNZ_false hr he,
        by simp [Stmt.staticTime]; omega⟩
    · obtain ⟨s', t', he, ht⟩ := iht h.1 s
      exact ⟨s', C.branch + t', .ifNZ_true hr he,
        by simp [Stmt.staticTime]; omega⟩
  | memAlloc | memAllocI | memFree | memLen | memLoad | memStore | memPush
  | memPop | whileNZ => exact absurd h not_false

/-- A register-only block satisfies any postcondition its executions establish, in
`(staticTime, 0, 0)`. This is the bridge from a gadget's syntax to a `Triple`. -/
theorem Stmt.RegOnly.triple {c : Stmt w} (h : c.RegOnly) {P Q : State w → Prop}
    (hQ : ∀ s s' t, P s → Exec C c s s' t 0 0 → Q s') :
    Triple C P c Q (c.staticTime C) 0 0 := by
  intro s hs
  obtain ⟨s', t, he, ht⟩ := h.exec (C := C) s
  exact ⟨s', t, 0, 0, he, hQ s s' t hs he, ht, le_refl _, le_refl _⟩

/-- The common case: a block that does not write the registers a predicate depends on
preserves it. -/
theorem Stmt.RegOnly.triple_frame {c : Stmt w} (h : c.RegOnly) {P : State w → Prop}
    {R : Reg → Prop} (hR : ∀ r, R r → ¬ c.Writes r)
    (hP : ∀ s s' : State w, (∀ r, R r → s'.regs r = s.regs r) → P s → P s') :
    Triple C P c P (c.staticTime C) 0 0 :=
  h.triple fun s s' _ hs he => hP s s' (fun r hr => he.frame_reg (hR r hr)) hs

/-- Register-only code is in particular loop-free, so `staticTime` bounds it. -/
theorem Stmt.RegOnly.loopFree {c : Stmt w} (h : c.RegOnly) : c.LoopFree := by
  induction c with
  | seq _ _ ih₁ ih₂ => exact ⟨ih₁ h.1, ih₂ h.2⟩
  | ifNZ _ _ _ iht ihe => exact ⟨iht h.1, ihe h.2⟩
  | memAlloc | whileNZ => exact absurd h not_false
  | _ => trivial

/-! ## Writing above a watermark

The one frame fact a counted loop needs: the body does not touch the counter. Every
gadget here writes only registers at or above its own frame base, and the counter sits
below all of them, so `WritesAbove` composes down the syntax and the counter's
preservation falls out. -/

/-- `c` writes no register below `lo`. -/
def Stmt.WritesAbove (c : Stmt w) (lo : Reg) : Prop := ∀ q, q < lo → ¬ c.Writes q

theorem Stmt.WritesAbove.mono {c : Stmt w} {lo lo' : Reg} (h : c.WritesAbove lo)
    (hle : lo' ≤ lo) : c.WritesAbove lo' := fun q hq => h q (Nat.lt_of_lt_of_le hq hle)

@[simp] theorem writesAbove_skip (lo : Reg) : (Stmt.skip (w := w)).WritesAbove lo :=
  fun _ _ h => h

theorem Stmt.WritesAbove.seq {c₁ c₂ : Stmt w} {lo : Reg}
    (h₁ : c₁.WritesAbove lo) (h₂ : c₂.WritesAbove lo) : (c₁ ;; c₂).WritesAbove lo :=
  fun q hq h => h.elim (h₁ q hq) (h₂ q hq)

theorem Stmt.WritesAbove.ifNZ {r : Reg} {t e : Stmt w} {lo : Reg}
    (ht : t.WritesAbove lo) (he : e.WritesAbove lo) : (Stmt.ifNZ r t e).WritesAbove lo :=
  fun q hq h => h.elim (ht q hq) (he q hq)

theorem writesAbove_imm {d : Reg} {v : Word w} {lo : Reg} (h : lo ≤ d) :
    (Stmt.imm d v).WritesAbove lo := fun _ hq hd => absurd h (Nat.not_le.mpr (hd ▸ hq))

theorem writesAbove_mov {d a : Reg} {lo : Reg} (h : lo ≤ d) :
    (Stmt.mov (w := w) d a).WritesAbove lo := fun _ hq hd => absurd h (Nat.not_le.mpr (hd ▸ hq))

theorem writesAbove_un {op : UnOp} {d a : Reg} {lo : Reg} (h : lo ≤ d) :
    (Stmt.un (w := w) op d a).WritesAbove lo := fun _ hq hd => absurd h (Nat.not_le.mpr (hd ▸ hq))

theorem writesAbove_bin {op : BinOp} {d a b : Reg} {lo : Reg} (h : lo ≤ d) :
    (Stmt.bin (w := w) op d a b).WritesAbove lo := fun _ hq hd => absurd h (Nat.not_le.mpr (hd ▸ hq))

/-- What a frame condition is for: a block that writes above `lo` leaves everything
below `lo` alone. -/
theorem Exec.regs_of_writesAbove {c : Stmt w} {s s' : State w} {t : ℕ} {d p : ℤ}
    {lo q : Reg} (h : Exec C c s s' t d p) (hw : c.WritesAbove lo) (hq : q < lo) :
    s'.regs q = s.regs q :=
  h.frame_reg (hw q hq)

/-! ## Bounding a run

`TimeLe c T` says every execution of `c` takes at most `T` steps. Unlike a `Triple` it
asserts nothing about the code running at all, so a `memLoad` costs no
index-in-range obligation and a `memPush` no capacity obligation — the bound is over
whatever runs. Unlike `staticTime` it survives a loop, because the loop's contribution
comes from a `Triple` and `Exec.deterministic` carries that bound to every execution.

Those are exactly the two things the witgen lowering needs to compose: the bulk of the
compiled code is loop-free but touches memory, and inversion loops but touches
none. -/

/-- Every execution of `c` takes at most `T` steps. -/
def TimeLe (C : CostModel) (c : Stmt w) (T : ℕ) : Prop :=
  ∀ s s' t d p, Exec C c s s' t d p → t ≤ T

theorem TimeLe.mono {c : Stmt w} {T T' : ℕ} (h : TimeLe C c T) (hT : T ≤ T') :
    TimeLe C c T' := fun s s' t d p he => (h s s' t d p he).trans hT

theorem TimeLe.seq {c₁ c₂ : Stmt w} {T₁ T₂ : ℕ}
    (h₁ : TimeLe C c₁ T₁) (h₂ : TimeLe C c₂ T₂) : TimeLe C (c₁ ;; c₂) (T₁ + T₂) := by
  rintro s s' t d p he
  cases he with
  | seq he₁ he₂ => exact Nat.add_le_add (h₁ _ _ _ _ _ he₁) (h₂ _ _ _ _ _ he₂)

theorem TimeLe.ifNZ {r : Reg} {t e : Stmt w} {T : ℕ}
    (ht : TimeLe C t T) (he : TimeLe C e T) : TimeLe C (.ifNZ r t e) (C.branch + T) := by
  rintro s s' tt d p hex
  cases hex with
  | ifNZ_true _ h => exact Nat.add_le_add_left (ht _ _ _ _ _ h) _
  | ifNZ_false _ h => exact Nat.add_le_add_left (he _ _ _ _ _ h) _

/-- Loop-free code is bounded by its static time, memory instructions included. -/
theorem TimeLe.of_loopFree {c : Stmt w} (h : c.LoopFree) :
    TimeLe C c (c.staticTime C) :=
  fun _ _ _ _ _ he => he.time_le_staticTime_of_loopFree h

/-- A `Triple` with no precondition bounds *every* execution, the machine being
deterministic. This is how a loop's bound reaches the surrounding straight-line
code. -/
theorem Triple.timeLe {Q : State w → Prop} {c : Stmt w} {T : ℕ} {D M : ℤ}
    (h : Triple C (fun _ => True) c Q T D M) : TimeLe C c T := by
  intro s s' t d p hex
  obtain ⟨s₁, t₁, d₁, p₁, he, -, ht, -, -⟩ := h s trivial
  obtain ⟨-, rfl, -, -⟩ := Exec.deterministic hex he
  exact ht

end Caliper
