module

public import MeyerGeneralProblem.Cardinal.Adaptive.EndpointRecurrence
public import MeyerGeneralProblem.Cardinal.Adaptive.EndpointDeletedSource

@[expose] public section

/-! # Complete endpoint sources are exhausted by the whole Poisson basis -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open scoped FourierTransform BigOperators

/-- An integer translate of an actual isolation test reads the corresponding
whole coefficient; equality is proved on the entire carrier vanishing ideal. -/
theorem endpointCoefficient_translation {k : ℕ} (α : Fin k → ℝ)
    (ha : Function.Injective α) (hi : ∀ i, 0 < α i ∧ α i < 1/2)
    (T : TemperedDistribution ℝ ℂ) (hT : AtomicOnCarrier (endpointCosetCarrier α) T)
    (a : EndpointPhaseIndex k) (n : ℤ) :
    T (combSchwartzTranslation (n : ℝ) ((endpointCosetCarrier α).isolationSchwartz (endpointPoint α a 0))) =
      endpointCoefficient α a (-n) T := by
  change T _ = T _
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply hT
  rintro x ⟨b,m,rfl⟩
  simp only [SchwartzMap.sub_apply,combSchwartzTranslation_apply]
  have he : (n : ℝ)+(endpointPhase α b+(m : ℝ))=endpointPhase α b+((m+n : ℤ) : ℝ) := by
    push_cast
    ring
  rw [he,endpointIsolation_apply α ha hi,endpointIsolation_apply α ha hi]
  rw [sub_eq_zero]
  apply ite_congr
  · exact propext (by constructor <;> rintro ⟨hb,hm⟩ <;> exact ⟨hb,by omega⟩)
  · intro _; rfl
  · intro _; rfl

/-- The exact number of consecutive readings on each physical coset. -/
def endpointRectangleObservation {k : ℕ} (α : Fin k → ℝ) :
    TemperedDistribution ℝ ℂ →ₗ[ℂ]
      (EndpointPhaseIndex k → Fin (Fintype.card (EndpointPhaseIndex k)) → ℂ) :=
  LinearMap.pi (fun a => LinearMap.pi (fun r => endpointCoefficient α a (-(r.val : ℤ))))

/-- Complete source uniqueness follows from the genuine bilateral recurrence,
including at the single endpoint and without restrictions on distribution order. -/
theorem endpointRectangle_kernel {k : ℕ} (α β : Fin k → ℝ)
    (ha : Function.Injective α) (hi : ∀ i, 0 < α i ∧ α i < 1/2)
    (T : TemperedDistribution ℝ ℂ) (hT : AtomicOnCarrier (endpointCosetCarrier α) T)
    (hFT : AtomicOnCarrier (endpointCosetCarrier β) (𝓕 T))
    (hz : endpointRectangleObservation α T = 0) : T=0 := by
  have hall (a : EndpointPhaseIndex k) (n : ℤ) : endpointCoefficient α a (-n) T=0 := by
    let f := (endpointCosetCarrier α).isolationSchwartz (endpointPoint α a 0)
    have hrec := endpoint_test_recurrence β T hFT f
    have he := bilateralRecurrence_eq_zero
      (d := Fintype.card (EndpointPhaseIndex k)) (by simp [EndpointPhaseIndex])
      (endpointDifferenceCoeff β) (endpointDifferenceCoeff_extremes β).1
      (endpointDifferenceCoeff_extremes β).2
      (fun n => T (combSchwartzTranslation (n : ℝ) f)) hrec
      (fun i => by
        rw [endpointCoefficient_translation α ha hi T hT]
        exact congrFun (congrFun hz a) i)
    rw [← endpointCoefficient_translation α ha hi T hT]
    exact he n
  apply atomicOnCarrier_eq_zero_of_isolation_zero _ T hT
  rintro ⟨x,a,n,rfl⟩
  change endpointCoefficient α a n T=0
  simpa only [neg_neg] using hall a (-n)

/-- All whole two-sided finite endpoint sources, with no representation assumption. -/
def endpointSourceSpace {k : ℕ} (α β : Fin k → ℝ) : Submodule ℂ (TemperedDistribution ℝ ℂ) :=
  pairedAtomicSource (endpointCosetCarrier α) (endpointCosetCarrier β)

/-- Consecutive coefficient observations restricted to the complete paired source. -/
def endpointSourceObservation {k : ℕ} (α β : Fin k → ℝ) :
    endpointSourceSpace α β →ₗ[ℂ]
      (EndpointPhaseIndex k → Fin (Fintype.card (EndpointPhaseIndex k)) → ℂ) :=
  (endpointRectangleObservation α).comp (endpointSourceSpace α β).subtype

theorem endpointSourceObservation_injective {k : ℕ} (α β : Fin k → ℝ)
    (ha : Function.Injective α) (hi : ∀ i, 0 < α i ∧ α i < 1/2) :
    Function.Injective (endpointSourceObservation α β) := by
  intro T U h
  apply sub_eq_zero.mp
  apply Subtype.ext
  change (T : TemperedDistribution ℝ ℂ)-(U : TemperedDistribution ℝ ℂ)=0
  apply endpointRectangle_kernel α β ha hi _ (T-U).property.1 (T-U).property.2
  change endpointRectangleObservation α ((T : TemperedDistribution ℝ ℂ)-U)=0
  rw [map_sub]
  exact sub_eq_zero.mpr h

theorem endpointSourceSpace_finiteDimensional {k : ℕ} (α β : Fin k → ℝ)
    (ha : Function.Injective α) (hi : ∀ i, 0 < α i ∧ α i < 1/2) :
    FiniteDimensional ℂ (endpointSourceSpace α β) :=
  FiniteDimensional.of_injective (endpointSourceObservation α β)
    (endpointSourceObservation_injective α β ha hi)

/-- Whole Poisson synthesis taking values in the complete paired endpoint source. -/
def endpointSourceSynthesis {k : ℕ} (α β : Fin k → ℝ) :
    EndpointMatrix k →ₗ[ℂ] endpointSourceSpace α β :=
  (endpointPoissonSynthesis α β).codRestrict _ (endpointPoissonSynthesis_atomic α β)

theorem endpointSourceSynthesis_injective {k : ℕ} (α β : Fin k → ℝ)
    (ha : Function.Injective α) (hb : Function.Injective β)
    (hia : ∀ i, 0 < α i ∧ α i < 1/2) (hib : ∀ i, 0 < β i ∧ β i < 1/2) :
    Function.Injective (endpointSourceSynthesis α β) := by
  intro c d h
  exact endpointPoissonSynthesis_injective α β ha hb hia hib (congrArg Subtype.val h)

/-- The entire actual endpoint source is the whole Poisson span. Finite
dimensionality is proved first by an actual observation injection. -/
def endpointSourceEquiv {k : ℕ} (α β : Fin k → ℝ)
    (ha : Function.Injective α) (hb : Function.Injective β)
    (hia : ∀ i, 0 < α i ∧ α i < 1/2) (hib : ∀ i, 0 < β i ∧ β i < 1/2) :
    EndpointMatrix k ≃ₗ[ℂ] endpointSourceSpace α β := by
  letI := endpointSourceSpace_finiteDimensional α β ha hia
  apply LinearEquiv.ofInjectiveOfFinrankEq (endpointSourceSynthesis α β)
    (endpointSourceSynthesis_injective α β ha hb hia hib)
  apply le_antisymm
  · exact LinearMap.finrank_le_finrank_of_injective (endpointSourceSynthesis_injective α β ha hb hia hib)
  · have he := LinearMap.finrank_le_finrank_of_injective (endpointSourceObservation_injective α β ha hia)
    have hd : Module.finrank ℂ (EndpointPhaseIndex k → Fin (Fintype.card (EndpointPhaseIndex k)) → ℂ)=
        Module.finrank ℂ (EndpointMatrix k) := by
      simp [EndpointMatrix,Module.finrank_pi_fintype]
    exact he.trans_eq hd

/-- An arbitrary whole source with the complete two finite endpoint records
has unique Poisson coefficients. -/
theorem endpointSource_existsUnique_poisson {k : ℕ} (α β : Fin k → ℝ)
    (ha : Function.Injective α) (hb : Function.Injective β)
    (hia : ∀ i, 0 < α i ∧ α i < 1/2) (hib : ∀ i, 0 < β i ∧ β i < 1/2)
    (T : TemperedDistribution ℝ ℂ) (hT : AtomicOnCarrier (endpointCosetCarrier α) T)
    (hFT : AtomicOnCarrier (endpointCosetCarrier β) (𝓕 T)) :
    ∃! c : EndpointMatrix k, endpointPoissonSynthesis α β c=T := by
  let e := endpointSourceEquiv α β ha hb hia hib
  let U : endpointSourceSpace α β := ⟨T,hT,hFT⟩
  refine ⟨e.symm U,?_,?_⟩
  · exact congrArg Subtype.val (e.apply_symm_apply U)
  · intro c hc
    apply endpointPoissonSynthesis_injective α β ha hb hia hib
    exact hc.trans (congrArg Subtype.val (e.apply_symm_apply U)).symm

end
end MeyerGeneralProblem.Adaptive
