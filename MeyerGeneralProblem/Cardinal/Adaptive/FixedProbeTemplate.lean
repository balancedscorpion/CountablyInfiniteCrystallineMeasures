module

public import MeyerGeneralProblem.Cardinal.Adaptive.ActualGoodScales

@[expose] public section

/-! # A single fixed compact probe template for the actual adaptive construction -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section

/-- The fixed template is one near zero and supported strictly inside the unit interval. -/
def fixedProbeTemplate : SchwartzMap ℝ ℂ :=
  combSchwartzDilation 4 (by norm_num) compactSchwartzCutoff

/-- The template is exactly one throughout a fixed neighbourhood of zero. -/
theorem fixedProbeTemplate_eq_one (x : ℝ) (hx : |x| ≤ 1/4) :
    fixedProbeTemplate x = 1 := by
  rw [fixedProbeTemplate,combSchwartzDilation_apply]
  apply compactSchwartzCutoff_eq_one
  rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<4)]
  linarith

/-- The template vanishes outside the half-unit interval, including its boundary. -/
theorem fixedProbeTemplate_eq_zero (x : ℝ) (hx : 1/2 ≤ |x|) :
    fixedProbeTemplate x = 0 := by
  rw [fixedProbeTemplate,combSchwartzDilation_apply,compactSchwartzCutoff_apply]
  have hz := compactSchwartzCutoffBump.zero_of_le_dist (x := 4*x)
  rw [hz]
  · norm_num
  · simpa only [compactSchwartzCutoffBump,Real.dist_eq,sub_zero,abs_mul,
      abs_of_pos (by norm_num : (0:ℝ)<4)] using (show (2:ℝ) ≤ 4*|x| by linarith)

/-- The fixed template's whole topological support is compact and lies inside(-1,1). -/
theorem fixedProbeTemplate_support :
    tsupport fixedProbeTemplate ⊆ Set.Icc (-(1/2:ℝ)) (1/2) := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  by_contra hn
  have habs : 1/2 ≤ |x| := by
    rw [Set.mem_Icc] at hn
    have hh := abs_nonneg x
    rcases not_and_or.mp hn with h|h
    · have h' : x < -(1/2:ℝ) := lt_of_not_ge h
      rw [abs_of_neg (by linarith)]
      linarith
    · exact (lt_of_not_ge h).le.trans (le_abs_self x)
  exact hx (fixedProbeTemplate_eq_zero x habs)

/-- Compact support is proved for the chosen template, not assumed of all Schwartz functions. -/
theorem fixedProbeTemplate_hasCompactSupport : HasCompactSupport fixedProbeTemplate :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) fixedProbeTemplate_support

/-- The concrete gap sequence used by the construction, with the fixed template chosen once. -/
def constructedGaps : ℕ+ → ℕ := actualPositiveGaps fixedProbeTemplate

/-- The concrete sequence starts with exactly the source's first gap. -/
theorem constructedGaps_one : constructedGaps 1 = 2 := by
  simp [constructedGaps,actualPositiveGaps,actualGaps]

/-- One measurable positive-measure set works for the concrete construction. -/
theorem constructed_good_set :
    ∃ E : Set (ℕ+ → ℝ), MeasurableSet E ∧
      (13/16 : ENNReal) ≤ scaleProbability E ∧ ∀ s ∈ E, ActualGoodScale fixedProbeTemplate s :=
  exists_actual_good_set fixedProbeTemplate

/-- A fixed scale tuple is now chosen once for all stages and all native orders. -/
def constructedScales : ℕ+ → ℝ := Classical.choose (exists_actualGoodScale fixedProbeTemplate)

/-- The single chosen tuple has all proved geometry and stage properties. -/
theorem constructedScales_good : ActualGoodScale fixedProbeTemplate constructedScales :=
  Classical.choose_spec (exists_actualGoodScale fixedProbeTemplate)

/-- The actual reciprocal carrier, with both choices fully constructed. -/
def constructedCarrier : LocallyFiniteCarrier :=
  adaptiveCarrier constructedGaps constructedScales
    (linearGap_of_exponential _ (actualPositiveGaps_exponential fixedProbeTemplate))
    constructedScales_good.1.1

/-- The carrier uses exactly the source's block union, with no added seam atoms. -/
theorem constructedCarrier_carrier :
    constructedCarrier.carrier = carrierSet constructedGaps constructedScales :=
  adaptiveCarrier_carrier _ _ _ _

end
end MeyerGeneralProblem.Adaptive
