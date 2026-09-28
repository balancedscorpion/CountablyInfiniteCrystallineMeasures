module

public import MeyerGeneralProblem.Cardinal.Adaptive.SeamCoordinateOperator

@[expose] public section

/-! # Complete lower parity coordinate block and its leading approximation -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section

/-- Every power of an operator preserves its exact commuting coordinate projection. -/
theorem seamArcsineFactor_commute (C P : SeamMomentArray →L[ℂ] SeamMomentArray)
    (h : Commute C P) : Commute (seamArcsineFactor C) P := by
  apply Commute.tsum_left
  intro n
  rw [Algebra.smul_def]
  exact (Algebra.commute_algebraMap_left _ P).mul_left (h.pow_left n)

theorem seamNewtonRow_parity_commute (R : ℂ) (a : ℕ → ℂ) (K : ℝ)
    (hK : 0 ≤ K) (ha : ∀ i, ‖a i‖ ≤ K) (e : Bool) :
    Commute (seamNewtonRow R a K hK ha) (momentProjection (seamRowParity e)) := by
  change seamNewtonRow R a K hK ha*momentProjection (seamRowParity e)=
    momentProjection (seamRowParity e)*seamNewtonRow R a K hK ha
  ext u p
  rcases p with ⟨⟨i,b⟩,j,f⟩
  change seamNewtonRow R a K hK ha (momentProjection (seamRowParity e) u) ((i,b),(j,f))=
    momentProjection (seamRowParity e) (seamNewtonRow R a K hK ha u) ((i,b),(j,f))
  simp only [seamNewtonRow_apply,momentProjection_apply,seamRowParity,Set.mem_setOf_eq]
  by_cases h : b=e <;> simp [h]

theorem seamSineRow_square_parity_commute (κ R : ℂ) (hκ : κ ≠ 0) (a : ℕ → ℂ)
    (K : ℝ) (hK : 0 ≤ K) (ha : ∀ i, ‖a i‖ ≤ K) (e : Bool) :
    Commute (seamSineRow κ R a K hK ha*seamSineRow κ R a K hK ha)
      (momentProjection (seamRowParity e)) := by
  change Commute ((seamSineRow κ R a K hK ha).comp (seamSineRow κ R a K hK ha)) _
  rw [seamSineRow_square κ R hκ]
  have h := seamNewtonRow_parity_commute R a K hK ha e
  have htwo : Commute ((2 : ℂ) • (1 : SeamMomentArray →L[ℂ] SeamMomentArray))
      (momentProjection (seamRowParity e)) := by
    change ((2 : ℂ) • (1 : SeamMomentArray →L[ℂ] SeamMomentArray)) * _ =
      _ * ((2 : ℂ) • (1 : SeamMomentArray →L[ℂ] SeamMomentArray))
    rw [seamOperator_smul_mul, seamOperator_mul_smul, one_mul, mul_one]
  exact h.mul_left (htwo.sub_left h)

/-- Exact extraction of the full lower sine block, on the whole Hilbert space. -/
theorem seamSineRow_lower_projection (κ R : ℂ) (a : ℕ → ℂ) (K : ℝ)
    (hK : 0 ≤ K) (ha : ∀ i, ‖a i‖ ≤ K) :
    momentProjection (seamRowParity true)*seamSineRow κ R a K hK ha*
      momentProjection (seamRowParity false)=seamSineLower κ R a K hK ha := by
  ext u p
  rcases p with ⟨⟨i,e⟩,j,f⟩
  change momentProjection (seamRowParity true)
    (seamSineRow κ R a K hK ha (momentProjection (seamRowParity false) u)) ((i,e),(j,f))=_
  cases e <;> simp [momentProjection_apply,seamRowParity,seamSineRow_apply,seamSineLower_apply]

/-- The actual lower parity block of the complete coordinate operator. -/
def seamLowerCoordinate (S : SeamMomentArray →L[ℂ] SeamMomentArray) : SeamMomentArray →L[ℂ] SeamMomentArray :=
  momentProjection (seamRowParity true)*seamCoordinateOperator S*momentProjection (seamRowParity false)

/-- The leading J/(2πκ) lower block, with its true zero-extension to the full array. -/
def seamLeadingLower (κ R : ℂ) (a : ℕ → ℂ) (K : ℝ) (hK : 0 ≤ K) (ha : ∀ i, ‖a i‖ ≤ K) :
    SeamMomentArray →L[ℂ] SeamMomentArray := (2*(Real.pi : ℂ))⁻¹ •seamSineLower κ R a K hK ha

/-- The entire lower coordinate factor is Y h(C); no power-series term is dropped. -/
theorem seamLowerCoordinate_factor (κ R : ℂ) (hκ : κ ≠ 0) (a : ℕ → ℂ)
    (K : ℝ) (hK : 0 ≤ K) (ha : ∀ i, ‖a i‖ ≤ K) :
    let S := seamSineRow κ R a K hK ha
    seamLowerCoordinate S=seamLeadingLower κ R a K hK ha*seamArcsineFactor (S*S) := by
  dsimp only
  let S := seamSineRow κ R a K hK ha
  let hC := seamArcsineFactor (S*S)
  have hc : hC*momentProjection (seamRowParity false)=momentProjection (seamRowParity false)*hC :=
    (seamArcsineFactor_commute _ _ (seamSineRow_square_parity_commute κ R hκ a K hK ha false)).eq
  change momentProjection (seamRowParity true)*((2*(Real.pi : ℂ))⁻¹ •(S*hC))*
      momentProjection (seamRowParity false)=((2*(Real.pi : ℂ))⁻¹ •seamSineLower κ R a K hK ha)*hC
  calc
    _ = (2*(Real.pi : ℂ))⁻¹ •(momentProjection (seamRowParity true)*S*(hC*momentProjection (seamRowParity false))) := by
      simp only [seamOperator_mul_smul,seamOperator_smul_mul,mul_assoc]
    _ = (2*(Real.pi : ℂ))⁻¹ •(momentProjection (seamRowParity true)*S*(momentProjection (seamRowParity false)*hC)) := by rw [hc]
    _ = (2*(Real.pi : ℂ))⁻¹ •((momentProjection (seamRowParity true)*S*momentProjection (seamRowParity false))*hC) := by simp only [mul_assoc]
    _ = _ := by rw [seamSineRow_lower_projection,seamOperator_smul_mul]

/-- The leading lower block has norm at most κ/3 in the full Hilbert space. -/
theorem seamLeadingLower_constant_norm (a : ℕ → ℂ) (ha : ∀ i, ‖a i‖ ≤ (1/4096 : ℝ)^2) :
    ‖seamLeadingLower (1/64) (1/4096) a ((1/4096)^2) (by positivity) ha‖ ≤ (1/64 : ℝ)/3 := by
  have hJ : ‖seamNewtonRow (1/4096) a ((1/4096)^2) (by positivity) ha‖ ≤
      (1/4096 : ℝ)+(1/4096 : ℝ)^2 := by
    simpa only [norm_div,norm_one,Complex.norm_ofNat] using
      seamNewtonRow_norm_le (1/4096) a ((1/4096)^2) (by positivity) ha
  have hp : ‖(2*(Real.pi : ℂ))⁻¹‖ ≤ (1/6 : ℝ) := by
    rw [norm_inv,norm_mul]
    norm_num only [Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
    rw [one_div]
    exact inv_anti₀ (by norm_num) (by nlinarith [Real.pi_gt_three])
  have hP : ‖seamRowFlip.comp (momentProjection (seamRowParity false))‖ ≤ 1 := by
    apply (seamRowFlip.opNorm_comp_le _).trans
    have hf := seamRowFlip_norm_le_one
    have hp := momentProjection_norm_le_one (seamRowParity false)
    nlinarith [norm_nonneg seamRowFlip,norm_nonneg (momentProjection (seamRowParity false))]
  rw [seamLeadingLower,seamSineLower,norm_smul,norm_smul]
  calc
    _ ≤ ‖(2*(Real.pi : ℂ))⁻¹‖*(‖(1/64 : ℂ)⁻¹‖*(‖seamNewtonRow (1/4096) a ((1/4096)^2) (by positivity) ha‖*
      ‖seamRowFlip.comp (momentProjection (seamRowParity false))‖)) := by
      gcongr
      apply ContinuousLinearMap.opNorm_comp_le
    _ ≤ (1/6 : ℝ)*(64*(((1/4096 : ℝ)+(1/4096 : ℝ)^2)*1)) := by
      have hi : ‖(1/64 : ℂ)⁻¹‖=64 := by norm_num
      rw [hi]
      apply mul_le_mul hp _ (by positivity) (by norm_num)
      exact mul_le_mul_of_nonneg_left (mul_le_mul hJ hP (norm_nonneg _) (by positivity)) (by norm_num)
    _ ≤ _ := by norm_num

/-- The lower block replacement error is bounded before any diagonal compression. -/
theorem seamLowerCoordinate_constant_error (a : ℕ → ℂ) (ha : ∀ i, ‖a i‖ ≤ (1/4096 : ℝ)^2) :
    let S := seamSineRow (1/64) (1/4096) a ((1/4096)^2) (by positivity) ha
    ‖seamLowerCoordinate S-seamLeadingLower (1/64) (1/4096) a ((1/4096)^2) (by positivity) ha‖ ≤
      2*(1/4096 : ℝ)*(1/64 : ℝ) := by
  dsimp only
  rw [seamLowerCoordinate_factor _ _ (by norm_num)]
  rw [← mul_sub_one]
  calc
    _ ≤ ‖seamLeadingLower (1/64) (1/4096) a ((1/4096)^2) (by positivity) ha‖*
      ‖seamArcsineFactor (seamSineRow (1/64) (1/4096) a ((1/4096)^2) (by positivity) ha*
        seamSineRow (1/64) (1/4096) a ((1/4096)^2) (by positivity) ha)-1‖ := norm_mul_le _ _
    _ ≤ ((1/64 : ℝ)/3)*(6*(1/4096 : ℝ)) := by
      gcongr
      · exact seamLeadingLower_constant_norm a ha
      · exact seamArcsineFactor_close _ (seamSineRow_square_norm a ha)
    _ = _ := by norm_num

/-- The whole lower parity coordinate block has norm at most κ/2. -/
theorem seamLowerCoordinate_constant_norm (a : ℕ → ℂ) (ha : ∀ i, ‖a i‖ ≤ (1/4096 : ℝ)^2) :
    let S := seamSineRow (1/64) (1/4096) a ((1/4096)^2) (by positivity) ha
    ‖seamLowerCoordinate S‖ ≤ (1/64 : ℝ)/2 := by
  have h := norm_le_norm_sub_add
    (seamLowerCoordinate (seamSineRow (1/64) (1/4096) a ((1/4096)^2) (by positivity) ha))
    (seamLeadingLower (1/64) (1/4096) a ((1/4096)^2) (by positivity) ha)
  have he := seamLowerCoordinate_constant_error a ha
  have hy := seamLeadingLower_constant_norm a ha
  dsimp only at he ⊢
  linarith

end
end MeyerGeneralProblem.Adaptive
