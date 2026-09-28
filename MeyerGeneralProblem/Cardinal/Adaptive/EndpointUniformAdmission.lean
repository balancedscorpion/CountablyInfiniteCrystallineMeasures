module

public import MeyerGeneralProblem.Cardinal.Adaptive.EndpointFiniteKernel
public import MeyerGeneralProblem.Cardinal.Adaptive.NativePairingNorm

@[expose] public section

/-! Uniform original-native admission of the actual finite endpoint sources. -/
noncomputable section
namespace MeyerGeneralProblem.Adaptive

/-- The actual nonzero scalar used to normalize finite sources by one fixed test. -/
def endpointObservationScalar (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) (k : ℕ) : ℂ :=
  (endpointFinitePhysicalArray P R hP hR k ((0,false),(0,false)))⁻¹

/-- Every finite source has exactly the same nonzero fixed Schwartz observation
after the actual, proved nonzero, moment-corner normalization. -/
theorem endpointObservationScalar_realizes (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) (k : ℕ) :
    endpointObservationScalar P R hP hR k*endpointFiniteSource P R hP hR k endpointZerothObservation=1 := by
  rw [endpointZerothObservation_realizes (endpointPaddedDistance P R k) (endpointPaddedDistance P R k)]
  exact inv_mul_cancel₀ (endpointFinitePhysicalArray_corner_ne_zero P R hP hR k)

/-- The actual finite moment bound in exactly the unpadded normalization consumed
by the fixed-smoothness reverse Zak interpolation theorem. -/
theorem endpointFiniteSource_admission_moments (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R)
    (k : ℕ) (e f : Bool) (i j : Fin (k+1)) :
    ‖halfNewtonMoment (fun r => rapidDistance P R r.val) (fun r => rapidDistance P R r.val)
      (halfWeylDistributionCLM (endpointFiniteSource P R hP hR k)) i.val e j.val f‖ ≤
      (5*‖endpointFinitePhysicalArray P R hP hR k ((0,false),(0,false))‖)*
        (1099511627776 : ℝ)^(max i.val j.val)*shrinkingNewtonWeight (rapidDistance P R) (max i.val j.val) := by
  have hh := endpointFinitePhysicalArray_rapid_product P R hP hR k i j e f
  change ‖halfNewtonMoment (endpointPaddedDistance P R k) (endpointPaddedDistance P R k) _ _ _ _ _‖ ≤ _ at hh
  rw [halfNewtonMoment_endpointPadded_prefix P R k i.val j.val (by omega) (by omega)] at hh
  convert hh using 1
  ring

/-- Complete actual endpoint sources have a uniform original test bound after
normalization, at the exact finite-smoothness order2L+2. -/
theorem exists_endpointFiniteSource_uniform_pairing_bound {P R : ℕ}
    (hP : 1 ≤ P) (hR : 1 ≤ R) (L : ℕ) (hL : 4 < rapidBase P^L) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, ∀ f : SchwartzMap ℝ ℂ,
      ‖(endpointObservationScalar P R hP hR k •endpointFiniteSource P R hP hR k) f‖ ≤
        C*‖schwartzToHermiteScale (2*L+2) f‖ := by
  obtain ⟨C,hC,hbound⟩ := exists_rapidEndpointSource_actualMoment_pairing_bound hP hR L hL
    (1099511627776 : ℝ) (by norm_num)
  refine ⟨5*C,by positivity,?_⟩
  intro k f
  have hb := hbound k (normalizedEndpointMatrix (rapidEndpointPhaseData P R k) (rapidEndpointPhaseData P R k)
      (rapidEndpointPhaseData_injective hP hR k) (rapidEndpointPhaseData_injective hP hR k)
      (rapidEndpointPhaseData_interior hP hR k) (rapidEndpointPhaseData_interior hP hR k))
    (5*‖endpointFinitePhysicalArray P R hP hR k ((0,false),(0,false))‖) (by positivity)
    (endpointFiniteSource_admission_moments P R hP hR k) f
  change ‖endpointFiniteSource P R hP hR k f‖ ≤ _ at hb
  change ‖endpointObservationScalar P R hP hR k*endpointFiniteSource P R hP hR k f‖ ≤ _
  rw [norm_mul]
  apply (mul_le_mul_of_nonneg_left hb (norm_nonneg _)).trans_eq
  unfold endpointObservationScalar
  rw [norm_inv]
  have hn : ‖endpointFinitePhysicalArray P R hP hR k ((0,false),(0,false))‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (endpointFinitePhysicalArray_corner_ne_zero P R hP hR k)
  field_simp

/-- The same uniform constant bounds every genuine native representative of the
actual normalized finite source, without increasing the original norm order. -/
theorem exists_endpointFiniteSource_uniform_native_bound {P R : ℕ}
    (hP : 1 ≤ P) (hR : 1 ≤ R) (L : ℕ) (hL : 4 < rapidBase P^L) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, ∀ U : HermiteScale (-((2*L+2:ℕ):ℤ)),
      hermiteScaleDistribution (2*L+2) U=endpointFiniteSource P R hP hR k →
      ‖endpointObservationScalar P R hP hR k •U‖ ≤ C := by
  obtain ⟨C,hC,hbound⟩ := exists_endpointFiniteSource_uniform_pairing_bound hP hR L hL
  refine ⟨C,hC,?_⟩
  intro k U hU
  apply native_norm_le_of_schwartz_pairing (2*L+2) _ C hC.le
  intro f
  have he : hermiteScaleDistribution (2*L+2) (endpointObservationScalar P R hP hR k •U)=
      endpointObservationScalar P R hP hR k •endpointFiniteSource P R hP hR k := by
    change hermiteScaleDistributionCLM (2*L+2) (_ •U)=_
    rw [map_smul,hermiteScaleDistributionCLM_apply,hU]
  rw [he]
  exact hbound k f

end MeyerGeneralProblem.Adaptive
