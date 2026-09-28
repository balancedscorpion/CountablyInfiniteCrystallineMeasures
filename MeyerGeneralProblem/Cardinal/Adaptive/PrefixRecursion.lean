module

public import Mathlib.Order.Filter.AtTopBot.Basic
import all Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.Finite
import all Mathlib.Order.Filter.Finite
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import all Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic

@[expose] public section

/-!
# Deterministic recursion from finite-prefix tail estimates

The exact three-tail estimates remain explicit hypotheses in this generic
construction. At stage M+1 only the M+1 already chosen gaps are supplied to
the parameter and budget functions. The least acceptable next integer pays
the three finite families and the exponential/doubling/translation demands.
This is the recursion mechanism of the source §7, not a construction of its
analytic estimates or a good scale witness.
-/

namespace MeyerGeneralProblem.Adaptive
noncomputable section
open Filter

/-- A stage has access only to the already chosen gaps. -/
abbrev GapPrefix (M : ℕ) := Fin M → ℕ

/-- The whole sequence from a deterministic next-gap rule on finite gapses.
The zero-based entry n is the paper's positive gap R_(n+1). -/
def recursiveGaps (next : ∀ M, GapPrefix (M+1) → ℕ) : ℕ → ℕ :=
  Nat.strongRec fun n prev => match n with
  | 0 => 2
  | M+1 => next M (fun i => prev i i.isLt)

@[simp] theorem recursiveGaps_zero (next : ∀ M, GapPrefix (M+1) → ℕ) :
    recursiveGaps next 0 = 2 := by
  unfold recursiveGaps
  rw [Nat.strongRec_eq]

/-- The next gap uses exactly the previous gaps, not a future completion. -/
theorem recursiveGaps_succ (next : ∀ M, GapPrefix (M+1) → ℕ) (M : ℕ) :
    recursiveGaps next (M+1) = next M (fun i => recursiveGaps next i) := by
  unfold recursiveGaps
  rw [Nat.strongRec_eq]

/-- Three finite families of eventual budgets can be paid at one integer,
after an arbitrary deterministic lower bound has already been fixed. -/
theorem exists_nextGap (M B : ℕ) (tail : Fin 3 → Fin (M+1) → ℕ → Prop)
    (htail : ∀ j p, ∀ᶠ R in atTop, tail j p R) :
    ∃ R : ℕ, B ≤ R ∧ ∀ j p, tail j p R := by
  have h : ∀ᶠ R in atTop, ∀ j p, tail j p R :=
    eventually_all.mpr fun j => eventually_all.mpr (htail j)
  exact ((eventually_ge_atTop B).and h).exists

/-- A single integer lower bound pays all three non-analytic growth demands. -/
def nextGapFloor (M previous : ℕ) (H : ℝ) : ℕ :=
  max (2^(M+2)) (max (2*previous) ⌈6*(H+(M+1)+2)⌉₊)

theorem nextGapFloor_spec (M previous R : ℕ) (H : ℝ)
    (h : nextGapFloor M previous H ≤ R) :
    2^(M+2) ≤ R ∧ 2*previous ≤ R ∧ 6*(H+(M+1)+2) ≤ (R:ℝ) := by
  unfold nextGapFloor at h
  have h1 := (max_le_iff.mp h).1
  have h2 := (max_le_iff.mp (max_le_iff.mp h).2).1
  have h3 := (max_le_iff.mp (max_le_iff.mp h).2).2
  exact ⟨h1,h2,(Nat.le_ceil _).trans (by exact_mod_cast h3)⟩

/-- The least next gap pays the already fixed radius and the three families.
The estimates are deliberately explicit inputs; the analytic tails are not
asserted by this generic recursion lemma. -/
def budgetedNext
    (H : ∀ M, GapPrefix (M+1) → ℝ)
    (tail : ∀ M, GapPrefix (M+1) → Fin 3 → Fin (M+1) → ℕ → Prop)
    (htail : ∀ M gaps j p, ∀ᶠ R in atTop, tail M gaps j p R)
    (M : ℕ) (gaps : GapPrefix (M+1)) : ℕ := by
  classical
  exact Nat.find (exists_nextGap M (nextGapFloor M (gaps (Fin.last M)) (H M gaps))
    (tail M gaps) (htail M gaps))

theorem budgetedNext_spec
    (H : ∀ M, GapPrefix (M+1) → ℝ)
    (tail : ∀ M, GapPrefix (M+1) → Fin 3 → Fin (M+1) → ℕ → Prop)
    (htail : ∀ M gaps j p, ∀ᶠ R in atTop, tail M gaps j p R)
    (M : ℕ) (gaps : GapPrefix (M+1)) :
    nextGapFloor M (gaps (Fin.last M)) (H M gaps) ≤ budgetedNext H tail htail M gaps ∧
      ∀ j p, tail M gaps j p (budgetedNext H tail htail M gaps) := by
  classical
  exact Nat.find_spec (exists_nextGap M (nextGapFloor M (gaps (Fin.last M)) (H M gaps))
    (tail M gaps) (htail M gaps))

/-- One deterministic sequence, chosen before any scale tuple or source. -/
def budgetedGaps
    (H : ∀ M, GapPrefix (M+1) → ℝ)
    (tail : ∀ M, GapPrefix (M+1) → Fin 3 → Fin (M+1) → ℕ → Prop)
    (htail : ∀ M gaps j p, ∀ᶠ R in atTop, tail M gaps j p R) : ℕ → ℕ :=
  recursiveGaps (budgetedNext H tail htail)

/-- Every gaps is the actual initial segment of the same completed sequence. -/
theorem budgetedGaps_step
    (H : ∀ M, GapPrefix (M+1) → ℝ)
    (tail : ∀ M, GapPrefix (M+1) → Fin 3 → Fin (M+1) → ℕ → Prop)
    (htail : ∀ M gaps j p, ∀ᶠ R in atTop, tail M gaps j p R) (M : ℕ) :
    let R := budgetedGaps H tail htail
    let gaps : GapPrefix (M+1) := fun i => R i
    2^(M+2) ≤ R (M+1) ∧ 2*R M ≤ R (M+1) ∧
      6*(H M gaps+(M+1)+2) ≤ (R (M+1):ℝ) ∧
        ∀ j p, tail M gaps j p (R (M+1)) := by
  dsimp only
  have h := budgetedNext_spec H tail htail M (fun i => budgetedGaps H tail htail i)
  have hs : budgetedGaps H tail htail (M+1) =
      budgetedNext H tail htail M (fun i => budgetedGaps H tail htail i) :=
    recursiveGaps_succ _ M
  rw [← hs] at h
  have hg := nextGapFloor_spec M (budgetedGaps H tail htail M)
    (budgetedGaps H tail htail (M+1))
    (H M (fun i => budgetedGaps H tail htail i)) h.1
  exact ⟨hg.1,hg.2.1,hg.2.2,h.2⟩

/-- Exponential escape holds at every positive block, including R_1=2. -/
theorem budgetedGaps_exponential
    (H : ∀ M, GapPrefix (M+1) → ℝ)
    (tail : ∀ M, GapPrefix (M+1) → Fin 3 → Fin (M+1) → ℕ → Prop)
    (htail : ∀ M gaps j p, ∀ᶠ R in atTop, tail M gaps j p R) (n : ℕ) :
    2^(n+1) ≤ budgetedGaps H tail htail n := by
  cases n with
  | zero => simp [budgetedGaps]
  | succ M => exact (budgetedGaps_step H tail htail M).1

/-- Translate the internal zero-based sequence to the actual positive labels. -/
def budgetedPositiveGaps
    (H : ∀ M, GapPrefix (M+1) → ℝ)
    (tail : ∀ M, GapPrefix (M+1) → Fin 3 → Fin (M+1) → ℕ → Prop)
    (htail : ∀ M gaps j p, ∀ᶠ R in atTop, tail M gaps j p R) (i : ℕ+) : ℕ :=
  budgetedGaps H tail htail (i-1)

theorem budgetedPositiveGaps_exponential
    (H : ∀ M, GapPrefix (M+1) → ℝ)
    (tail : ∀ M, GapPrefix (M+1) → Fin 3 → Fin (M+1) → ℕ → Prop)
    (htail : ∀ M gaps j p, ∀ᶠ R in atTop, tail M gaps j p R) (i : ℕ+) :
    2^(i:ℕ) ≤ budgetedPositiveGaps H tail htail i := by
  have h := budgetedGaps_exponential H tail htail (i-1)
  have hi : (i:ℕ)-1+1 = i := by have := i.pos; omega
  simpa only [budgetedPositiveGaps,hi] using h

/-- Any two completions with the same initial segment select the same next
integer. No later deterministic gap enters the selection function. -/
theorem budgetedNext_initialSegment
    (H : ∀ M, GapPrefix (M+1) → ℝ)
    (tail : ∀ M, GapPrefix (M+1) → Fin 3 → Fin (M+1) → ℕ → Prop)
    (htail : ∀ M gaps j p, ∀ᶠ R in atTop, tail M gaps j p R)
    (M : ℕ) (R S : ℕ → ℕ) (h : ∀ i ≤ M, R i = S i) :
    budgetedNext H tail htail M (fun i => R i) =
      budgetedNext H tail htail M (fun i => S i) := by
  congr 1
  funext i
  exact h i (by omega)

end
end MeyerGeneralProblem.Adaptive
