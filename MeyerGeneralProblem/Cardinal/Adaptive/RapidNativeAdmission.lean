module

public import MeyerGeneralProblem.Cardinal.Adaptive.EndpointUniformAdmission
public import MeyerGeneralProblem.Cardinal.Adaptive.EndpointNativeLimit
public import MeyerGeneralProblem.Cardinal.Adaptive.BlockTailEquivalence

@[expose] public section

/-! Actual nonzero original-native rapid critical sources from complete finite endpoint limits. -/
noncomputable section
open scoped FourierTransform
namespace MeyerGeneralProblem.Adaptive

/-- The literal infinite rapid phases are injective. -/
theorem rapidTailPhase_injective (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) :
    Function.Injective (rapidTailPhase P R) := by
  intro i j hij
  apply Subtype.ext
  apply (rapidDistance_strictAnti hP hR).injective
  unfold rapidTailPhase at hij
  exact sub_right_injective hij

/-- The actual infinite-family prefix is exactly the finite phase data used in admission. -/
theorem endpointPhasePrefix_rapidTailPhase (P R k : ℕ) :
    endpointPhasePrefix (rapidTailPhase P R) k=rapidEndpointPhaseData P R k := rfl

/-- The complete finite source in the native compactness theorem is the actual
finite source bounded by the original-native interpolation theorem. -/
theorem endpointApproximation_rapidTailPhase (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) (k : ℕ) :
    endpointApproximation (rapidTailPhase P R) (rapidTailPhase_injective P R hP hR)
      (rapidTailPhase_inside P R hP hR) k=endpointFiniteSource P R hP hR k := rfl

/-- A concrete finite interpolation order follows from Bernoulli's inequality,
with strict slack: the actual rapid base to power9P exceeds4. -/
theorem rapidBase_nine_mul_gt_four (P : ℕ) (hP : 1 ≤ P) :
    4 < rapidBase P^(9*P) := by
  have hp : (P:ℝ) ≠ 0 := by exact_mod_cast (show P ≠ 0 by omega)
  have hnonneg : (0:ℝ) ≤ 1/(6*(P:ℝ)) := by positivity
  have hb := one_add_mul_le_pow (a := 1/(6*(P:ℝ))) ((by norm_num : (-2:ℝ) ≤ 0).trans hnonneg) P
  have he : (1:ℝ)+(P:ℝ)*(1/(6*(P:ℝ)))=7/6 := by field_simp; ring
  rw [he] at hb
  change (7/6:ℝ) ≤ rapidBase P^P at hb
  calc
    (4:ℝ) < (7/6:ℝ)^9 := by norm_num
    _ ≤ (rapidBase P^P)^9 := pow_le_pow_left₀ (by norm_num) hb 9
    _ = rapidBase P^(9*P) := by rw [←pow_mul,Nat.mul_comm]

/-- Uniform original-native admission and literal finite carrier convergence
construct a nonzero rapid critical source at the same fixed order2L+2. -/
theorem exists_rapidNativeSource (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R)
    (L : ℕ) (hL : 4 < rapidBase P^L) :
    ∃ U : HermiteScale (-((2*L+2:ℕ):ℤ)), U ≠ 0 ∧
      AtomicOnCarrier (criticalPhaseTailCarrier (rapidTailPhase P R) (rapidTailPhase_inside P R hP hR) 0 0)
        (hermiteScaleDistribution (2*L+2) U) ∧
      AtomicOnCarrier (criticalPhaseTailCarrier (rapidTailPhase P R) (rapidTailPhase_inside P R hP hR) 0 0)
        (𝓕 (hermiteScaleDistribution (2*L+2) U)) ∧
      hermiteScaleDistribution (2*L+2) U endpointZerothObservation=1 ∧
      𝓕 (hermiteScaleDistribution (2*L+2) U)= -Complex.I •hermiteScaleDistribution (2*L+2) U := by
  obtain ⟨C,hC,hbound⟩ := exists_endpointFiniteSource_uniform_native_bound hP hR L hL
  have hb (k : ℕ) : ‖endpointObservationScalar P R hP hR k •
      endpointNativeApproximation (rapidTailPhase P R) (rapidTailPhase_injective P R hP hR)
        (rapidTailPhase_inside P R hP hR) (2*L+2) (by omega) k‖ ≤ C := by
    apply hbound k
    rw [endpointNativeApproximation_realizes,endpointApproximation_rapidTailPhase]
  have ho (k : ℕ) : endpointObservationScalar P R hP hR k*
      endpointApproximation (rapidTailPhase P R) (rapidTailPhase_injective P R hP hR)
        (rapidTailPhase_inside P R hP hR) k endpointZerothObservation=1 := by
    rw [endpointApproximation_rapidTailPhase]
    exact endpointObservationScalar_realizes P R hP hR k
  obtain ⟨U,hU,hne,hT,hFT,hobs,hF⟩ := endpointNativeLimit_of_uniform_bound
    (rapidTailPhase P R) (rapidTailPhase_injective P R hP hR) (rapidTailPhase_inside P R hP hR)
    (2*L+2) (by omega) (endpointObservationScalar P R hP hR) C hb endpointZerothObservation 1 (by norm_num) ho
  exact ⟨U,hne,hT,hFT,hobs,hF⟩

/-- The actual rapid critical source has a nonzero original-native vector at
explicit order18P+2 with one fixed observation and the exact Fourier eigenvalue. -/
theorem exists_rapidNativeSource_explicit (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) :
    ∃ U : HermiteScale (-((18*P+2:ℕ):ℤ)), U ≠ 0 ∧
      AtomicOnCarrier (criticalPhaseTailCarrier (rapidTailPhase P R) (rapidTailPhase_inside P R hP hR) 0 0)
        (hermiteScaleDistribution (18*P+2) U) ∧
      AtomicOnCarrier (criticalPhaseTailCarrier (rapidTailPhase P R) (rapidTailPhase_inside P R hP hR) 0 0)
        (𝓕 (hermiteScaleDistribution (18*P+2) U)) ∧
      hermiteScaleDistribution (18*P+2) U endpointZerothObservation=1 ∧
      𝓕 (hermiteScaleDistribution (18*P+2) U)= -Complex.I •hermiteScaleDistribution (18*P+2) U := by
  have hh := exists_rapidNativeSource P R hP hR (9*P) (rapidBase_nine_mul_gt_four P hP)
  have he : 2*(9*P)+2=18*P+2 := by omega
  rw [he] at hh
  exact hh

/-- The actual complete rapid source has a nonzero member in its original native
layer at the explicit finite order; this is the literal B08 source-space interface. -/
theorem actualRapidNativeSource_nonzero (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) :
    ∃ T ∈ actualRapidNativeSource P R hP hR (18*P+2), T ≠ 0 := by
  obtain ⟨U,hU,hT,hFT,hobs,hF⟩ := exists_rapidNativeSource_explicit P R hP hR
  refine ⟨hermiteScaleDistribution (18*P+2) U,⟨?_,⟨U,rfl⟩⟩,?_⟩
  · exact ⟨hT,hFT⟩
  · intro hz
    have he := congrArg (fun T : TemperedDistribution ℝ ℂ => T endpointZerothObservation) hz
    simp only [hobs,_root_.zero_apply] at he
    exact one_ne_zero he

end MeyerGeneralProblem.Adaptive
