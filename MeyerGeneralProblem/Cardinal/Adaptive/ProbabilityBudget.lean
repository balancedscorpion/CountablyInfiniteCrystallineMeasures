module

public import Mathlib.Analysis.SpecificLimits.Basic
import all Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import all Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.MeasureTheory.Measure.MeasureSpace
import all Mathlib.MeasureTheory.Measure.MeasureSpace
public import Mathlib.Tactic
import all Mathlib.Tactic

@[expose] public section

/-!
# The three adaptive failure budgets

For each positive stage there are three bad events, each of probability at most
`2^(-M-4)`. Their countable union has measure at most `3/16`, without any
independence assumption. Constructing the concrete measurable events and proving
their stage bounds are separate obligations; this lemma does not assume that
they already exist for the adaptive carrier.
-/

namespace MeyerGeneralProblem.Adaptive

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

/-- The stage indexing starts at one, so the first budget is `1/32`. -/
def failureBudget (n : ℕ) : ℝ≥0∞ := (2⁻¹ : ℝ≥0∞) ^ (n + 5)

/-- One family of positive-stage failures has total budget `1/16`. -/
theorem tsum_failureBudget : ∑' n, failureBudget n = 1 / 16 := by
  simp only [failureBudget, pow_add, ENNReal.tsum_mul_right, ENNReal.tsum_geometric_two]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv]

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)

/-- The full union of all three bad-event families. -/
def allBadEvents (bad : Fin 3 → ℕ → Set α) : Set α := ⋃ j, ⋃ n, bad j n

/-- A countable union bound includes every stage and all three error families. -/
theorem measure_allBadEvents_le (bad : Fin 3 → ℕ → Set α)
    (hbudget : ∀ j n, μ (bad j n) ≤ failureBudget n) :
    μ (allBadEvents bad) ≤ 3 / 16 := by
  have hfamily (j : Fin 3) : μ (⋃ n, bad j n) ≤ 1 / 16 := by
    calc
      μ (⋃ n, bad j n) ≤ ∑' n, μ (bad j n) := measure_iUnion_le _
      _ ≤ ∑' n, failureBudget n := ENNReal.tsum_le_tsum (hbudget j)
      _ = 1 / 16 := tsum_failureBudget
  calc
    μ (allBadEvents bad) ≤ ∑ j : Fin 3, μ (⋃ n, bad j n) :=
      measure_iUnion_fintype_le μ _
    _ ≤ ∑ _ : Fin 3, (1 / 16 : ℝ≥0∞) := Finset.sum_le_sum fun j _ => hfamily j
    _ = 3 / 16 := by norm_num [div_eq_mul_inv]

/-- One full-measure geometric condition and the entire event catalogue leave
a good set of measure at least `13/16`. The same point satisfies every stage. -/
theorem measure_goodEvents_ge [IsProbabilityMeasure μ]
    (bad : Fin 3 → ℕ → Set α) (hmeas : ∀ j n, MeasurableSet (bad j n))
    (hbudget : ∀ j n, μ (bad j n) ≤ failureBudget n)
    (full : Set α) (hfull : ∀ᵐ x ∂μ, x ∈ full) :
    (13 / 16 : ℝ≥0∞) ≤ μ (full ∩ (allBadEvents bad)ᶜ) := by
  rw [Measure.measure_inter_eq_of_ae hfull]
  have hbadmeas : MeasurableSet (allBadEvents bad) :=
    MeasurableSet.iUnion fun j => MeasurableSet.iUnion (hmeas j)
  rw [measure_compl hbadmeas (measure_ne_top μ _), measure_univ]
  have h := measure_allBadEvents_le μ bad hbudget
  calc
    (13 / 16 : ℝ≥0∞) = 1 - 3 / 16 := by
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      rw [ENNReal.toReal_sub_of_le (by norm_num [ENNReal.div_le_iff]) (by finiteness)]
      norm_num [ENNReal.toReal_div]
    _ ≤ 1 - μ (allBadEvents bad) := tsub_le_tsub_left h 1

/-- Positive remaining measure supplies one point for all positive stages.
The hypotheses are explicit probability estimates, not independent-event claims. -/
theorem exists_goodEvents [IsProbabilityMeasure μ]
    (bad : Fin 3 → ℕ → Set α) (hmeas : ∀ j n, MeasurableSet (bad j n))
    (hbudget : ∀ j n, μ (bad j n) ≤ failureBudget n)
    (full : Set α) (hfull : ∀ᵐ x ∂μ, x ∈ full) :
    ∃ x ∈ full, ∀ j n, x ∉ bad j n := by
  have hpos : 0 < μ (full ∩ (allBadEvents bad)ᶜ) :=
    lt_of_lt_of_le (by norm_num) (measure_goodEvents_ge μ bad hmeas hbudget full hfull)
  obtain ⟨x, hxfull, hxgood⟩ := nonempty_of_measure_ne_zero hpos.ne'
  refine ⟨x, hxfull, ?_⟩
  intro j n hbad
  exact hxgood (Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨n, hbad⟩⟩)

end

end MeyerGeneralProblem.Adaptive
