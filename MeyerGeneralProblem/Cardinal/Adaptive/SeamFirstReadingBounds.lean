module

public import MeyerGeneralProblem.Cardinal.Adaptive.SeamFirstResidual

@[expose] public section

/-! # The full Schur kernel retains the first-phase residual -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open scoped ENNReal

/-- The complete Schur residual at the first diagonal is controlled by the whole graph residual. -/
theorem seamSchur_first_residual (F : SeamMomentArray →L[ℂ] SeamMomentArray)
    (hF : ‖F-seamQProjection‖ ≤ 10*(1/4096 : ℝ)) :
    ‖seamSchur F (hF.trans_lt (by norm_num)) seamFirstVector‖ ≤ 2*‖F seamFirstArray‖ := by
  have hA : ‖seamSchurA F seamFirstVector‖ ≤ ‖F seamFirstArray‖ := by
    change ‖seamCProjection (F seamFirstArray-seamQProjection seamFirstArray)‖ ≤ _
    have hz : seamQProjection seamFirstArray=0 := seamQProjection_D _
    rw [hz,sub_zero]
    exact (seamCProjection.le_opNorm _).trans (by nlinarith [seamCProjection_norm_le_one,norm_nonneg (F seamFirstArray)])
  have hH : ‖seamSchurH F seamFirstVector‖ ≤ ‖F seamFirstArray‖ := by
    change ‖seamDiagonalReading true true (F seamFirstArray)‖ ≤ _
    exact ((seamDiagonalReading true true).le_opNorm _).trans
      (by nlinarith [seamDiagonalReading_norm_le_one true true,norm_nonneg (F seamFirstArray)])
  have hb := fullNearIdentityEquiv_symm_bound (seamSchurB F) (10*(1/4096 : ℝ)) (by norm_num)
    ((seamSchurB_close F).trans hF) (seamSchurA F seamFirstVector)
  have hj := (seamSchurJ_norm F).trans hF
  change ‖seamSchurH F seamFirstVector-seamSchurJ F
    ((fullNearIdentityEquiv (seamSchurB F) ((seamSchurB_close F).trans_lt (hF.trans_lt (by norm_num)))).symm
      (seamSchurA F seamFirstVector))‖ ≤ _
  apply (norm_sub_le _ _).trans
  calc
    _ ≤ ‖F seamFirstArray‖+(10*(1/4096 : ℝ))*((1-10*(1/4096 : ℝ))⁻¹*‖F seamFirstArray‖) := by
      apply add_le_add hH
      apply (ContinuousLinearMap.le_opNorm _ _).trans
      apply mul_le_mul hj _ (norm_nonneg _) (by norm_num)
      exact hb.trans (mul_le_mul_of_nonneg_left hA (by norm_num))
    _ ≤ _ := by nlinarith [norm_nonneg (F seamFirstArray)]

/-- Explicit uniform control of the complete right-block inverse at the source constants. -/
theorem seamSchur_inverse_gap (T : SeamSequence →L[ℂ] SeamSequence)
    (hT : ‖T‖ ≤ 300*(1/4096 : ℝ)^2) :
    (‖seamLeadingCoefficient‖-‖T‖)⁻¹ ≤ (131072 : ℝ) := by
  have hc : (1/32768 : ℝ) ≤ ‖seamLeadingCoefficient‖ := by
    rw [seamLeadingCoefficient_norm]
    apply (le_div_iff₀ (by positivity : 0 < 2*Real.pi)).mpr
    nlinarith [Real.pi_lt_four]
  have hd : (1/131072 : ℝ) ≤ ‖seamLeadingCoefficient‖-‖T‖ := by linarith
  have hi := inv_anti₀ (by norm_num : (0 : ℝ) < 1/131072) hd
  norm_num at hi
  exact hi

/-- The normalized full kernel stays close to the actual first vector by its actual full residual. -/
theorem seamSchur_normalized_first_bound (F : SeamMomentArray →L[ℂ] SeamMomentArray)
    (hF : ‖F-seamQProjection‖ ≤ 10*(1/4096 : ℝ))
    (hH : ‖seamSchurH F-seamLeadingCoefficient •seamBackwardShift‖ ≤ 100*(1/4096 : ℝ)^2) :
    let T := seamSchur F (hF.trans_lt (by norm_num))-seamLeadingCoefficient •seamBackwardShift
    ‖seamCanonicalKernelVector T (seamSchur_error F hF hH)-seamFirstVector‖ ≤
      262144*‖F seamFirstArray‖ := by
  dsimp only
  have hr : ‖(seamSchur F (hF.trans_lt (by norm_num))-seamLeadingCoefficient •seamBackwardShift) seamFirstVector‖ ≤
      2*‖F seamFirstArray‖ := by
    simpa only [sub_apply,smul_apply,seamBackward_first,smul_zero,sub_zero] using seamSchur_first_residual F hF
  apply (seamCanonicalKernelVector_stability _ (seamSchur_error F hF hH)).trans
  calc
    _ ≤ 131072*(2*‖F seamFirstArray‖) := mul_le_mul
      (seamSchur_inverse_gap _ (seamSchur_error F hF hH)) hr (norm_nonneg _) (by norm_num)
    _ = _ := by ring

/-- Every full flag-kernel has its next diagonal reading controlled by the true first residual. -/
theorem seamSchur_next_reading_bound (F : SeamMomentArray →L[ℂ] SeamMomentArray)
    (hF : ‖F-seamQProjection‖ ≤ 10*(1/4096 : ℝ))
    (hH : ‖seamSchurH F-seamLeadingCoefficient •seamBackwardShift‖ ≤ 100*(1/4096 : ℝ)^2)
    (u : SeamMomentArray) (hu : seamPProjection u=u) (hFu : F u=0) :
    ‖u ((1,false),(1,false))‖ ≤ 262144*‖F seamFirstArray‖*‖u ((0,false),(0,false))‖ := by
  let T := seamSchur F (hF.trans_lt (by norm_num))-seamLeadingCoefficient •seamBackwardShift
  let g := seamCanonicalKernelVector T (seamSchur_error F hF hH)
  have hg : ‖g 1‖ ≤ 262144*‖F seamFirstArray‖ := by
    have he := lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) (g-seamFirstVector) 1
    have hz : (g-seamFirstVector) 1=g 1 := by simp [seamFirstVector]
    rw [hz] at he
    exact he.trans (seamSchur_normalized_first_bound F hF hH)
  have he := congrArg (fun v : SeamSequence => v 1) (seamSchur_diagonal_eq_smul F hF hH u hu hFu)
  change u ((1,false),(1,false))=u ((0,false),(0,false))*g 1 at he
  rw [he,norm_mul,mul_comm]
  exact mul_le_mul_of_nonneg_right hg (norm_nonneg _)

/-- The complete corrected kernel's next reading vanishes linearly with the actual first phases. -/
theorem seamFullOperator_next_reading_bound (a b ta tb : ℕ → ℂ)
    (ha : ∀ i, ‖a i‖ ≤ (1/4096 : ℝ)^2) (hb : ∀ i, ‖b i‖ ≤ (1/4096 : ℝ)^2)
    (hta : ∀ i, ‖ta i‖ ≤ (1/4096 : ℝ)^3) (htb : ∀ i, ‖tb i‖ ≤ (1/4096 : ℝ)^3)
    (hH : ‖seamSchurH (seamFullOperator a b ta tb ha hb hta htb)-seamLeadingCoefficient •seamBackwardShift‖ ≤ 100*(1/4096 : ℝ)^2)
    (u : SeamMomentArray) (hu : seamPProjection u=u)
    (hFu : seamFullOperator a b ta tb ha hb hta htb u=0) :
    ‖u ((1,false),(1,false))‖ ≤ 8589934592*(‖ta 0‖+‖tb 0‖+‖b 0‖)*‖u ((0,false),(0,false))‖ := by
  apply (seamSchur_next_reading_bound _ (seamFullOperator_close a b ta tb ha hb hta htb) hH u hu hFu).trans
  calc
    _ ≤ 262144*(32768*(‖ta 0‖+‖tb 0‖+‖b 0‖))*‖u ((0,false),(0,false))‖ := by
      gcongr
      exact seamFullOperator_first_bound a b ta tb ha hb hta htb
    _ = _ := by ring

end
end MeyerGeneralProblem.Adaptive
