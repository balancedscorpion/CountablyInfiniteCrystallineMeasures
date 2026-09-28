module

public import MeyerGeneralProblem.Cardinal.Adaptive.CatalogueNonresonance
public import MeyerGeneralProblem.Cardinal.Adaptive.ProbabilityBudget

@[expose] public section

/-! # Measurability of actual prefix nonresonance events -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open MeasureTheory

/-- Each reciprocal-label scale is a measurable function of the actual product tuple. -/
theorem measurable_labelScale (b : Label) : Measurable (fun s : ℕ+ → ℝ => labelScale s b) := by
  rcases b with ⟨i,σ⟩
  cases σ <;> simp only [labelScale] <;> fun_prop

/-- Every literal finite-prefix comparison is measurable on the original
infinite product scale space, including dependent reciprocal coordinates. -/
theorem measurable_prefixComparisonValue {M : ℕ} (target : Fin M × ReciprocalSign)
    (origin : Label) (n n' : ℤ) (β β' : ℝ) (k : Fin M × ReciprocalSign → ℤ) :
    Measurable (prefixComparisonValue target origin n n' β β' k) := by
  have ht : Measurable (fun s : ℕ+ → ℝ => scaleFactor target.2 (s (prefixScaleIndex target.1))) := by
    cases target.2 <;> simp only [scaleFactor] <;> fun_prop
  have ho := measurable_labelScale origin
  unfold prefixComparisonValue reciprocalLaurentValue
  fun_prop

/-- Decoding a literal catalogue entry preserves actual measurability. -/
theorem measurable_descriptorComparisonValue {M : ℕ} (R : ℕ+ → ℕ) (c : ComparisonDescriptor M) :
    Measurable (descriptorComparisonValue R c) :=
  measurable_prefixComparisonValue _ _ _ _ _ _ _

/-- The actual unexpected-comparison sublevel event is measurable. -/
theorem descriptorBadEvent_measurable {M : ℕ} (R : ℕ+ → ℕ)
    (c : ComparisonDescriptor M) (u : ℝ) : MeasurableSet (descriptorBadEvent R c u) := by
  classical
  by_cases h : descriptorExpected R c
  · simp only [descriptorBadEvent, h, not_true_eq_false, false_and, Set.ofPred_false,
      MeasurableSet.empty]
  · simp only [descriptorBadEvent, h, not_false_eq_true, true_and]
    exact measurableSet_lt (continuous_abs.measurable.comp (measurable_descriptorComparisonValue R c)) measurable_const

/-- The complete finite catalogue union is a measurable event. -/
theorem catalogueBadEvent_measurable (R : ℕ+ → ℕ) (M L : ℕ) (u : ℝ) :
    MeasurableSet (catalogueBadEvent R M L u) := by
  exact MeasurableSet.iUnion fun c => MeasurableSet.iUnion fun _ =>
    descriptorBadEvent_measurable R c u

/-- Every dyadic catalogue is retained in one measurable bad event. -/
theorem dyadicCatalogueBadEvent_measurable (R : ℕ+ → ℕ) (M : ℕ) (c : ℝ) :
    MeasurableSet (dyadicCatalogueBadEvent R M c) :=
  MeasurableSet.iUnion fun _ => catalogueBadEvent_measurable R M _ _

/-- The exact real stage budget agrees with the indexed summable probability budget. -/
theorem stageFailureBudget_eq (n : ℕ) :
    ENNReal.ofReal ((2:ℝ)^(-((n+1)+4:ℤ))) = failureBudget n := by
  have he : -((n+1)+4:ℤ) = -((n+5:ℕ):ℤ) := by omega
  rw [he, zpow_neg, zpow_natCast, ENNReal.ofReal_inv_of_pos (by positivity),
    ENNReal.ofReal_pow (by norm_num : (0:ℝ)≤2)]
  norm_num only [ENNReal.ofReal_ofNat, failureBudget]
  exact ENNReal.inv_pow


/-- An almost-everywhere geometric property can be retained on a measurable
conull subset, so the final good carrier set can itself be measurable. -/
theorem exists_measurable_conull_subset {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (S : Set α) (hS : ∀ᵐ x ∂μ, x ∈ S) :
    ∃ F : Set α, MeasurableSet F ∧ F ⊆ S ∧ ∀ᵐ x ∂μ, x ∈ F := by
  have hz : μ Sᶜ = 0 := ae_iff.mp hS
  obtain ⟨N,hSN,hN,hμN⟩ := exists_measurable_superset_of_null hz
  refine ⟨Nᶜ,hN.compl,?_,?_⟩
  · intro x hx
    by_contra hs
    exact hx (hSN hs)
  · apply ae_iff.mpr
    simpa only [Set.notMem_compl_iff, Set.ofPred_mem_eq] using hμN

end
end MeyerGeneralProblem.Adaptive
