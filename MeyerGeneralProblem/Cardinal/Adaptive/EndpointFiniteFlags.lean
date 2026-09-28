module

public import MeyerGeneralProblem.Cardinal.Adaptive.EndpointFiniteClusters

@[expose] public section

/-! Complete triangular flags of actual finite zero-padded endpoint sources. -/
noncomputable section
open scoped BigOperators FourierTransform
namespace MeyerGeneralProblem.Adaptive

/-- Exact upper triangular flag for the complete actual finite Newton coordinate. -/
theorem endpointNewtonCoordinate_upper_flag {P R : ℕ} (hP : 1 ≤ P) (hR : 1 ≤ R)
    (k : ℕ) (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier ((endpointDeletedCarrier (rapidEndpointPhaseData P R k)).translate (-1/2)) T)
    (hFT : AtomicOnCarrier ((endpointDeletedCarrier (rapidEndpointPhaseData P R k)).translate (-1/2)) (𝓕 T))
    (i j : ℕ) (e f : Bool) (hij : j < i) :
    halfNewtonCoordinate (endpointPaddedDistance P R k) (endpointPaddedDistance P R k) T i e j f=0 := by
  unfold halfNewtonCoordinate halfNewtonBilinear
  rw [halfNewtonTest_characteristic_expansion]
  rw [← zakTensorSlice_apply,map_sum]
  apply Finset.sum_eq_zero
  intro r _
  rw [map_smul,map_add,map_smul,map_smul]
  have hr : (r : ℕ) ≤ 2*j := by
    have hh := r.isLt
    simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool] at hh
    omega
  have hfirst : ((r : ℤ)-(j : ℤ)).natAbs ≤ i ∧ (((r : ℤ)-(j : ℤ))+1).natAbs ≤ i := by omega
  have hsecond : ((r : ℤ)-(j : ℤ)-1).natAbs ≤ i ∧ (((r : ℤ)-(j : ℤ)-1)+1).natAbs ≤ i := by omega
  rw [zakTensorSlice_apply,zakTensorSlice_apply,
    endpointNewtonRow_chartProbe_zero hP hR k T hT hFT i e _ hfirst.1 hfirst.2,
    endpointNewtonRow_chartProbe_zero hP hR k T hT hFT i e _ hsecond.1 hsecond.2]
  simp only [smul_zero,zero_add]

/-- Fixed normalization preserves the complete actual finite upper flag. -/
theorem endpointNewtonMoment_upper_flag {P R : ℕ} (hP : 1 ≤ P) (hR : 1 ≤ R)
    (k : ℕ) (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier ((endpointDeletedCarrier (rapidEndpointPhaseData P R k)).translate (-1/2)) T)
    (hFT : AtomicOnCarrier ((endpointDeletedCarrier (rapidEndpointPhaseData P R k)).translate (-1/2)) (𝓕 T))
    (i j : ℕ) (e f : Bool) (hij : j < i) :
    halfNewtonMoment (endpointPaddedDistance P R k) (endpointPaddedDistance P R k) T i e j f=0 := by
  rw [halfNewtonMoment_eq_zero_iff]
  exact endpointNewtonCoordinate_upper_flag hP hR k T hT hFT i j e f hij

/-- Genuine half-Weyl recentering preserves both actual finite deleted records. -/
theorem halfWeylEndpoint_atomic_records {k : ℕ} (α β : Fin k → ℝ)
    (T : TemperedDistribution ℝ ℂ) (hT : AtomicOnCarrier (endpointDeletedCarrier α) T)
    (hFT : AtomicOnCarrier (endpointDeletedCarrier β) (𝓕 T)) :
    AtomicOnCarrier ((endpointDeletedCarrier α).translate (-1/2)) (halfWeylDistributionCLM T) ∧
    AtomicOnCarrier ((endpointDeletedCarrier β).translate (-1/2)) (𝓕 (halfWeylDistributionCLM T)) := by
  constructor
  · exact atomicOnCarrier_combDistributionModulation _ _
      (atomicOnCarrier_combDistributionTranslation _ T hT (-1/2)) (-1/2)
  · rw [fourier_halfWeylDistribution]
    exact atomicOnCarrier_combDistributionTranslation _ _
      (atomicOnCarrier_combDistributionModulation _ (𝓕 T) hFT (1/2)) (-1/2)

/-- The actual double Fourier transform retains the finite deleted carrier,
including the endpoint reflection n ↦ -n-1. -/
theorem endpointDeletedCarrier_atomic_fourier_sq {k : ℕ} (α : Fin k → ℝ)
    (T : TemperedDistribution ℝ ℂ) (hT : AtomicOnCarrier (endpointDeletedCarrier α) T) :
    AtomicOnCarrier (endpointDeletedCarrier α) (𝓕 (𝓕 T)) := by
  intro f hf
  rw [fourier_sq_eq_reflection,temperedReflectionCLM_apply]
  apply hT
  intro x hx
  rw [schwartzReflectionCLM_apply]
  exact hf _ (endpointDeletedCarrier_neg α hx)

/-- Actual Fourier companions have both reversed finite deleted records,
derived through the exact reflected endpoint carrier. -/
theorem halfWeylEndpointFourierCompanion_atomic_records {k : ℕ} (α β : Fin k → ℝ)
    (T : TemperedDistribution ℝ ℂ) (hT : AtomicOnCarrier (endpointDeletedCarrier α) T)
    (hFT : AtomicOnCarrier (endpointDeletedCarrier β) (𝓕 T)) :
    AtomicOnCarrier ((endpointDeletedCarrier β).translate (-1/2)) (halfWeylFourierCompanion T) ∧
    AtomicOnCarrier ((endpointDeletedCarrier α).translate (-1/2)) (𝓕 (halfWeylFourierCompanion T)) := by
  have hw := halfWeylEndpoint_atomic_records β α (𝓕 T) hFT
    (endpointDeletedCarrier_atomic_fourier_sq α T hT)
  unfold halfWeylFourierCompanion
  rw [halfWeyl_fourier_conjugation,FourierTransform.fourier_smul]
  constructor
  · intro f hf
    simp only [_root_.smul_apply,hw.1 f hf,smul_zero]
  · intro f hf
    simp only [_root_.smul_apply,hw.2 f hf,smul_zero]

/-- The complete actual Fourier moment family has the opposite finite flag. -/
theorem endpointNewtonFourierMoment_lower_flag {P R : ℕ} (hP : 1 ≤ P) (hR : 1 ≤ R)
    (k : ℕ) (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier (endpointDeletedCarrier (rapidEndpointPhaseData P R k)) T)
    (hFT : AtomicOnCarrier (endpointDeletedCarrier (rapidEndpointPhaseData P R k)) (𝓕 T))
    (i j : ℕ) (e f : Bool) (hij : i < j) :
    halfNewtonFourierMoment (endpointPaddedDistance P R k) (endpointPaddedDistance P R k) T i e j f=0 := by
  obtain ⟨hp,hq⟩ := halfWeylEndpointFourierCompanion_atomic_records _ _ T hT hFT
  rw [halfNewtonFourierMoment_eq_transposed,
    endpointNewtonMoment_upper_flag hP hR k (halfWeylFourierCompanion T) hp hq j i f e hij,mul_zero]

end MeyerGeneralProblem.Adaptive
