module

public import MeyerGeneralProblem.Cardinal.Adaptive.ActualRecursion
public import MeyerGeneralProblem.Cardinal.Adaptive.QuantitativeSectorSeparation

@[expose] public section

/-! # One measurable good set for the actual deterministic recursion -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open MeasureTheory

/-- Exactly the three proved bad-event families, on the single completed gap
sequence. Every event uses its own previously fixed stage parameters. -/
def actualBadEvents (ψ : SchwartzMap ℝ ℂ) : Fin 3 → ℕ → Set (ℕ+ → ℝ) :=
  ![fun n => dyadicCatalogueBadEvent (actualPositiveGaps ψ) (n+1) (actualStage ψ n).catalogueConstant,
    fun n => finitePeriodicCloseEvent (actualPositiveGaps ψ) (finitePrefixLabels (n+1))
      ((n+1:ℝ)+2) (actualStage ψ n).closureGap,
    fun n => (prefixSegmentNetEvent (n+1) (actualStage ψ n).translationStart
      (actualStage ψ n).translationBound ((actualStage ψ n).phaseTolerance/4))ᶜ]

/-- All actual events in the complete countable catalogue are measurable. -/
theorem actualBadEvents_measurable (ψ : SchwartzMap ℝ ℂ) (j : Fin 3) (n : ℕ) :
    MeasurableSet (actualBadEvents ψ j n) := by
  fin_cases j
  · exact dyadicCatalogueBadEvent_measurable _ _ _
  · exact finitePeriodicCloseEvent_measurable _ _ _ _
  · exact (prefixSegmentNetEvent_measurable _ _ _ _).compl

/-- The stage estimates apply to the actual completion because they were proved
uniformly over every completion of the selected prefix. -/
theorem actualBadEvents_budget (ψ : SchwartzMap ℝ ℂ) (j : Fin 3) (n : ℕ) :
    scaleProbability (actualBadEvents ψ j n) ≤ failureBudget n := by
  rw [← stageFailureBudget_eq]
  fin_cases j
  · exact (actualStage_laws ψ n).catalogue (actualPositiveGaps ψ) (actualPositiveGaps_prefix ψ)
  · change scaleProbability (finitePeriodicCloseEvent (actualPositiveGaps ψ) (finitePrefixLabels (n+1))
        ((n+1:ℝ)+2) (actualStage ψ n).closureGap) ≤ ENNReal.ofReal ((2:ℝ)^(-((n+1)+4:ℤ)))
    simpa only [PNat.mk_coe,Nat.cast_add,Nat.cast_one] using
      (actualStage_laws ψ n).closures (actualPositiveGaps ψ) (actualPositiveGaps_prefix ψ)
  · exact (actualStage_laws ψ n).net

/-- All geometric properties needed before source splitting. The sector estimate
includes one positive constant for every pair of actual atoms. -/
def ActualScaleGeometry (ψ : SchwartzMap ℝ ℂ) (s : ℕ+ → ℝ) : Prop :=
  (∀ i, s i ∈ Set.Icc (1:ℝ) 2) ∧
  (∀ c d : Label, c ≠ d → Disjoint
    (physicalPeriodicSet (actualPositiveGaps ψ) s c) (physicalPeriodicSet (actualPositiveGaps ψ) s d)) ∧
  (∃ σ : ℝ, 0 < σ ∧ ∀ b d : Label, b ≠ d →
    ∀ x ∈ sectorSet (actualPositiveGaps ψ) s b, ∀ y ∈ sectorSet (actualPositiveGaps ψ) s d,
      σ/(1+|x|+|y|)^6 ≤ |x-y|)

/-- The actual whole geometric condition holds almost everywhere. -/
theorem ae_actualScaleGeometry (ψ : SchwartzMap ℝ ℂ) :
    ∀ᵐ s ∂scaleProbability, ActualScaleGeometry ψ s := by
  filter_upwards [ae_all_scales_mem,
    ae_physical_periodic_sets_disjoint (actualPositiveGaps ψ) (actualPositiveGaps_pos ψ),
    ae_actual_sectors_power_six_separated (actualPositiveGaps ψ) (actualPositiveGaps_exponential ψ)]
    with s hs hd hsep
  exact ⟨hs,hd,hsep⟩

/-- A good tuple has actual geometry and avoids every bad event at every stage. -/
def ActualGoodScale (ψ : SchwartzMap ℝ ℂ) (s : ℕ+ → ℝ) : Prop :=
  ActualScaleGeometry ψ s ∧ ∀ j n, s ∉ actualBadEvents ψ j n

/-- The actual deterministic recursion has a measurable good set of measure at
least13/16. This is an unconditional assembly of the three proved budgets and
actual geometric almost-everywhere theorems; no independence is assumed. -/
theorem exists_actual_good_set (ψ : SchwartzMap ℝ ℂ) :
    ∃ E : Set (ℕ+ → ℝ), MeasurableSet E ∧
      (13/16 : ENNReal) ≤ scaleProbability E ∧ ∀ s ∈ E, ActualGoodScale ψ s := by
  obtain ⟨F,hFmeas,hFsub,hF⟩ := exists_measurable_conull_subset scaleProbability
    {s | ActualScaleGeometry ψ s} (ae_actualScaleGeometry ψ)
  refine ⟨F ∩ (allBadEvents (actualBadEvents ψ))ᶜ,?_,?_,?_⟩
  · exact hFmeas.inter (MeasurableSet.iUnion fun j =>
      MeasurableSet.iUnion (actualBadEvents_measurable ψ j)).compl
  · exact measure_goodEvents_ge scaleProbability (actualBadEvents ψ)
      (actualBadEvents_measurable ψ) (actualBadEvents_budget ψ) F hF
  · rintro s ⟨hsF,hsbad⟩
    refine ⟨hFsub hsF,fun j n hbad => ?_⟩
    exact hsbad (Set.mem_iUnion.mpr ⟨j,Set.mem_iUnion.mpr ⟨n,hbad⟩⟩)

/-- One tuple works at every native order, test window and stage. -/
theorem exists_actualGoodScale (ψ : SchwartzMap ℝ ℂ) : ∃ s, ActualGoodScale ψ s := by
  obtain ⟨E,_,hE,hgood⟩ := exists_actual_good_set ψ
  have hpos : 0 < scaleProbability E := lt_of_lt_of_le (by norm_num) hE
  obtain ⟨s,hs⟩ := nonempty_of_measure_ne_zero hpos.ne'
  exact ⟨s,hgood s hs⟩

/-- Every tuple in the constructed good set satisfies the literal complete
nonresonance catalogue simultaneously at all stages. -/
theorem ActualGoodScale.nonresonance (ψ : SchwartzMap ℝ ℂ) (s : ℕ+ → ℝ)
    (hs : ActualGoodScale ψ s) (n : ℕ) :
    ActualPrefixNonresonance (actualPositiveGaps ψ) (n+1) (actualStage ψ n).catalogueConstant s :=
  actualPrefixNonresonance_of_not_bad _ _ (actualPositiveGaps_exponential ψ) _
    (actualStage ψ n).catalogueConstant_pos (actualStage ψ n).catalogueConstant_le_one
    s hs.1.1 (hs.2 0 n)

/-- Every good tuple has all finite-prefix closure gaps on their full windows. -/
theorem ActualGoodScale.closure_separation (ψ : SchwartzMap ℝ ℂ) (s : ℕ+ → ℝ)
    (hs : ActualGoodScale ψ s) (n : ℕ) :
    ∀ b ∈ finitePrefixLabels (n+1), ∀ d ∈ finitePrefixLabels (n+1), b ≠ d →
      ∀ x ∈ physicalPeriodicSet (actualPositiveGaps ψ) s b,
      ∀ y ∈ physicalPeriodicSet (actualPositiveGaps ψ) s d,
        |x| ≤ (n+1:ℝ)+2 → |y| ≤ (n+1:ℝ)+2 → (actualStage ψ n).closureGap ≤ |x-y| :=
  (not_mem_finitePeriodicCloseEvent_iff _ _ _ _ _).mp (hs.2 1 n)

/-- Every good tuple realizes the actual bounded torus net at every stage. -/
theorem ActualGoodScale.net (ψ : SchwartzMap ℝ ℂ) (s : ℕ+ → ℝ)
    (hs : ActualGoodScale ψ s) (n : ℕ) :
    s ∈ prefixSegmentNetEvent (n+1) (actualStage ψ n).translationStart
      (actualStage ψ n).translationBound ((actualStage ψ n).phaseTolerance/4) := by
  have h := hs.2 2 n
  change ¬ ¬ s ∈ prefixSegmentNetEvent (n+1) (actualStage ψ n).translationStart
    (actualStage ψ n).translationBound ((actualStage ψ n).phaseTolerance/4) at h
  exact not_not.mp h

/-- The actual carrier is locally finite at every tuple in the same good set. -/
theorem ActualGoodScale.locally_finite (ψ : SchwartzMap ℝ ℂ) (s : ℕ+ → ℝ)
    (hs : ActualGoodScale ψ s) (a b : ℝ) :
    (carrierSet (actualPositiveGaps ψ) s ∩ Set.Icc a b).Finite :=
  carrierSet_finite_inter_Icc _ _ (actualPositiveGaps_exponential ψ) hs.1.1 a b

end
end MeyerGeneralProblem.Adaptive
