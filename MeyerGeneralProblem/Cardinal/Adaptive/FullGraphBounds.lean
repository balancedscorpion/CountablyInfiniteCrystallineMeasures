module

public import MeyerGeneralProblem.Cardinal.Adaptive.FullSchurComplement

@[expose] public section

/-! # Full graph corrections and quantitative Schur feedback -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section

section Graph
variable {A : Type*} [NormedRing A] [NormOneClass A]

/-- The complete two graph corrections around the actual full gauge. -/
def fullGraphOperator (Q E CA CB : A) : A := (Q-CB)*E*(1+CA)

/-- Exact expansion retaining both graph corrections and their cross term. -/
theorem fullGraphOperator_correction (Q E CA CB : A) :
    fullGraphOperator Q E CA CB-Q*E=Q*E*CA-CB*E*(1+CA) := by
  unfold fullGraphOperator
  noncomm_ring

/-- The accepted graph correction bound applies to the whole bounded algebra. -/
theorem fullGraphOperator_seam_correction (Q E CA CB : A)
    (hQ : ‖Q‖ ≤ 1) (hE : ‖E‖ ≤ 1+9*(1/4096 : ℝ))
    (hA : ‖CA‖ ≤ (1/4096 : ℝ)^2) (hB : ‖CB‖ ≤ (1/4096 : ℝ)^2) :
    ‖fullGraphOperator Q E CA CB-Q*E‖ ≤ 3*(1/4096 : ℝ)^2 := by
  have hI : ‖1+CA‖ ≤ 1+(1/4096 : ℝ)^2 := by
    calc
      _ ≤ ‖(1 : A)‖+‖CA‖ := norm_add_le _ _
      _ ≤ _ := by rw [norm_one]; linarith
  rw [fullGraphOperator_correction]
  calc
    _ ≤ ‖Q*E*CA‖+‖CB*E*(1+CA)‖ := norm_sub_le _ _
    _ ≤ (‖Q‖*‖E‖)*‖CA‖+(‖CB‖*‖E‖)*‖1+CA‖ := by
      apply add_le_add
      · exact (norm_mul_le (Q*E) CA).trans (mul_le_mul_of_nonneg_right (norm_mul_le Q E) (norm_nonneg CA))
      · exact (norm_mul_le (CB*E) (1+CA)).trans (mul_le_mul_of_nonneg_right (norm_mul_le CB E) (norm_nonneg (1+CA)))
    _ ≤ (1*(1+9*(1/4096 : ℝ)))*(1/4096 : ℝ)^2+
        ((1/4096 : ℝ)^2*(1+9*(1/4096 : ℝ)))*(1+(1/4096 : ℝ)^2) := by gcongr
    _ ≤ _ := by norm_num

/-- The full corrected map is close to its reference projection. -/
theorem fullGraphOperator_seam_close (Q E CA CB : A)
    (hQ : ‖Q‖ ≤ 1) (hE : ‖E‖ ≤ 1+9*(1/4096 : ℝ))
    (hEI : ‖E-1‖ ≤ 9*(1/4096 : ℝ))
    (hA : ‖CA‖ ≤ (1/4096 : ℝ)^2) (hB : ‖CB‖ ≤ (1/4096 : ℝ)^2) :
    ‖fullGraphOperator Q E CA CB-Q‖ ≤ 10*(1/4096 : ℝ) := by
  have he : fullGraphOperator Q E CA CB-Q=
      (fullGraphOperator Q E CA CB-Q*E)+Q*(E-1) := by noncomm_ring
  rw [he]
  calc
    _ ≤ ‖fullGraphOperator Q E CA CB-Q*E‖+‖Q*(E-1)‖ := norm_add_le _ _
    _ ≤ 3*(1/4096 : ℝ)^2+‖Q‖*‖E-1‖ :=
      add_le_add (fullGraphOperator_seam_correction Q E CA CB hQ hE hA hB) (norm_mul_le _ _)
    _ ≤ 3*(1/4096 : ℝ)^2+1*(9*(1/4096 : ℝ)) := by gcongr
    _ ≤ _ := by norm_num
end Graph

section Schur
variable {D C G : Type*}
variable [NormedAddCommGroup D] [NormedSpace ℂ D]
variable [NormedAddCommGroup C] [NormedSpace ℂ C] [CompleteSpace C]
variable [NormedAddCommGroup G] [NormedSpace ℂ G]

/-- Operator norm of the constructed complete inverse. -/
theorem fullNearIdentityEquiv_symm_norm_le (B : C →L[ℂ] C) (δ : ℝ) (hδ : δ < 1)
    (hB : ‖B-ContinuousLinearMap.id ℂ C‖ ≤ δ) :
    ‖(fullNearIdentityEquiv B (hB.trans_lt hδ)).symm.toContinuousLinearMap‖ ≤ (1-δ)⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  exact fullNearIdentityEquiv_symm_bound B δ hδ hB

/-- The entire Schur feedback, with no finite or first-iteration truncation. -/
theorem fullSchurOperator_feedback_bound (A : D →L[ℂ] C) (B : C →L[ℂ] C)
    (H : D →L[ℂ] G) (J : C →L[ℂ] G) (δ : ℝ) (hδ : δ < 1)
    (hB : ‖B-ContinuousLinearMap.id ℂ C‖ ≤ δ) :
    ‖fullSchurOperator A B H J (hB.trans_lt hδ)-H‖ ≤ ‖J‖*((1-δ)⁻¹*‖A‖) := by
  rw [fullSchurOperator,sub_sub_cancel_left,norm_neg]
  calc
    _ ≤ ‖J‖*‖(fullNearIdentityEquiv B (hB.trans_lt hδ)).symm.toContinuousLinearMap.comp A‖ := J.opNorm_comp_le _
    _ ≤ ‖J‖*(‖(fullNearIdentityEquiv B (hB.trans_lt hδ)).symm.toContinuousLinearMap‖*‖A‖) := by
      gcongr
      apply ContinuousLinearMap.opNorm_comp_le
    _ ≤ _ := by gcongr; exact fullNearIdentityEquiv_symm_norm_le B δ hδ hB

/-- The checked source constants give the complete 300R² Schur error. -/
theorem fullSchurOperator_seam_error (A : D →L[ℂ] C) (B : C →L[ℂ] C)
    (H L : D →L[ℂ] G) (J : C →L[ℂ] G)
    (hB : ‖B-ContinuousLinearMap.id ℂ C‖ ≤ 10*(1/4096 : ℝ))
    (hA : ‖A‖ ≤ 10*(1/4096 : ℝ)) (hJ : ‖J‖ ≤ 10*(1/4096 : ℝ))
    (hH : ‖H-L‖ ≤ 100*(1/4096 : ℝ)^2) :
    ‖fullSchurOperator A B H J (hB.trans_lt (by norm_num))-L‖ ≤ 300*(1/4096 : ℝ)^2 := by
  have hb := fullSchurOperator_feedback_bound A B H J (10*(1/4096 : ℝ)) (by norm_num) hB
  have hfb : ‖fullSchurOperator A B H J (hB.trans_lt (by norm_num))-H‖ ≤ 200*(1/4096 : ℝ)^2 := by
    apply hb.trans
    calc
      _ ≤ (10*(1/4096 : ℝ))*((1-10*(1/4096 : ℝ))⁻¹*(10*(1/4096 : ℝ))) := by gcongr
      _ ≤ _ := by norm_num
  calc
    _ ≤ ‖fullSchurOperator A B H J (hB.trans_lt (by norm_num))-H‖+‖H-L‖ := norm_sub_le_norm_sub_add_norm_sub _ H L
    _ ≤ _ := by linarith
end Schur
end
end MeyerGeneralProblem.Adaptive
