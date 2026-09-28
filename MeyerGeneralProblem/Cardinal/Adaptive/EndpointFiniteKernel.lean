module

public import MeyerGeneralProblem.Cardinal.Adaptive.EndpointFiniteGauge
public import MeyerGeneralProblem.Cardinal.Adaptive.SeamCompleteKernel

@[expose] public section

/-! Actual finite endpoint flag kernels, their nonzero observation and full product decay. -/
noncomputable section
namespace MeyerGeneralProblem.Adaptive

/-- The genuine reference flag part of the complete physical finite source array. -/
def endpointFiniteFlagVector (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) (k : ℕ) : SeamMomentArray :=
  seamPProjection (endpointFinitePhysicalVector P R hP hR k)

/-- Actual source diagonal equations reconstruct the complete physical vector. -/
theorem endpointFinitePhysicalVector_reconstruct (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) (k : ℕ) :
    endpointFinitePhysicalVector P R hP hR k=endpointFiniteFlagVector P R hP hR k+
      seamPhysicalGraph (endpointOperatorTangent P R k) (endpointOperatorTangent_norm hP hR k)
        (endpointFiniteFlagVector P R hP hR k) :=
  seamPhysicalGraph_reconstruct _ _ _ (endpointFinitePhysicalArray_upper P R hP hR k)
    (endpointFinitePhysicalArray_diagonal P R hP hR k)

/-- The actual finite flag part belongs to the reference flag space. -/
theorem endpointFiniteFlagVector_projection (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) (k : ℕ) :
    seamPProjection (endpointFiniteFlagVector P R hP hR k)=endpointFiniteFlagVector P R hP hR k :=
  momentProjection_idempotent _ _

/-- The concrete full corrected gauge kills the actual finite flag vector. -/
theorem endpointFiniteFlagVector_kernel (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) (k : ℕ) :
    seamFullOperator (endpointOperatorNode P R k) (endpointOperatorNode P R k)
      (endpointOperatorTangent P R k) (endpointOperatorTangent P R k)
      (endpointOperatorNode_norm hP hR k) (endpointOperatorNode_norm hP hR k)
      (endpointOperatorTangent_norm hP hR k) (endpointOperatorTangent_norm hP hR k)
      (endpointFiniteFlagVector P R hP hR k)=0 :=
  seamFullGraph_kernel _ _ _ _ _ _ _ (endpointFinitePhysicalVector_reconstruct P R hP hR k)
    (seamSpectralGraph_equation _ _ _ (endpointFiniteFourierArray_lower P R hP hR k)
      (endpointFiniteFourierArray_diagonal P R hP hR k))
    (endpointFiniteGauge_action P R hP hR k)

/-- The reference flag projection keeps the true zeroth source moment. -/
theorem endpointFiniteFlagVector_corner (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) (k : ℕ) :
    endpointFiniteFlagVector P R hP hR k ((0,false),(0,false))=
      endpointFinitePhysicalArray P R hP hR k ((0,false),(0,false)) := by
  simp [endpointFiniteFlagVector,seamPProjection,momentProjection_apply,seamDIndices]
  rfl

/-- The actual finite zeroth moment is nonzero, as a consequence of the complete
source, gauge and Schur equations; it is not an imposed normalization premise. -/
theorem endpointFinitePhysicalArray_corner_ne_zero (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) (k : ℕ) :
    endpointFinitePhysicalArray P R hP hR k ((0,false),(0,false)) ≠ 0 := by
  intro hz
  have hzero := seamFull_flag_zero _ _ _ _ _ _ _ _ _
    (endpointFiniteFlagVector_projection P R hP hR k) (endpointFiniteFlagVector_kernel P R hP hR k)
    (by rw [endpointFiniteFlagVector_corner,hz])
  apply endpointFinitePhysicalVector_ne_zero P R hP hR k
  rw [endpointFinitePhysicalVector_reconstruct,hzero,map_zero,add_zero]

/-- The actual full physical array satisfies the accepted maximum-index phase
product estimate, with both arms, every parity and the zero tail retained. -/
theorem endpointFinitePhysicalArray_phase_product (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R)
    (k i j : ℕ) (e f : Bool) :
    ‖endpointFinitePhysicalArray P R hP hR k ((i,e),(j,f))‖ ≤
      5*(1099511627776 : ℝ)^(max i j)*
      (∏ n ∈ Finset.range (max i j), endpointOperatorDistance P R k n)*
      ‖endpointFinitePhysicalArray P R hP hR k ((0,false),(0,false))‖ := by
  have hh := seamFull_array_phase_product _ _ _ _ _ _ _ _ _
    (endpointFiniteFlagVector_projection P R hP hR k) (endpointFiniteFlagVector_kernel P R hP hR k)
    (endpointOperatorDistance P R k) (endpointOperator_weight_linear hP hR k) i j e f
  rw [←endpointFinitePhysicalVector_reconstruct,endpointFiniteFlagVector_corner] at hh
  exact hh

/-- Every retained moment has the original unpadded rapid-product bound used by
finite-smoothness interpolation and original native admission. -/
theorem endpointFinitePhysicalArray_rapid_product (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R)
    (k : ℕ) (i j : Fin (k+1)) (e f : Bool) :
    ‖endpointFinitePhysicalArray P R hP hR k ((i.val,e),(j.val,f))‖ ≤
      5*(1099511627776 : ℝ)^(max i.val j.val)*shrinkingNewtonWeight (rapidDistance P R) (max i.val j.val)*
      ‖endpointFinitePhysicalArray P R hP hR k ((0,false),(0,false))‖ := by
  have hh := endpointFinitePhysicalArray_phase_product P R hP hR k i.val j.val e f
  have hp : (∏ n ∈ Finset.range (max i.val j.val), endpointOperatorDistance P R k n)=
      shrinkingNewtonWeight (rapidDistance P R) (max i.val j.val) := by
    unfold shrinkingNewtonWeight
    apply Finset.prod_congr rfl
    intro n hn
    have hn' := Finset.mem_range.mp hn
    have hm : max i.val j.val ≤ k := max_le (by omega) (by omega)
    simp [endpointOperatorDistance,endpointPaddedDistance,show n+1 ≤ k by omega]
  rwa [hp] at hh

end MeyerGeneralProblem.Adaptive
