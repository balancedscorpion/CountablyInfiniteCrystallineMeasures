module

public import MeyerGeneralProblem.Cardinal.Adaptive.FullSchurComplement

@[expose] public section

/-! # Bounds retaining the complete complementary feedback on a projected arm -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section

variable {C : Type*} [NormedAddCommGroup C] [NormedSpace ℂ C]

/-- A contractive coordinate projection and an invariant output arm preserve
 the full inverse estimate. The hypothesis is a whole-operator identity, so
 the estimate includes every complementary feedback term. -/
theorem projectedComplement_bound (P B : C →L[ℂ] C)
    (hP : ‖P‖ ≤ 1) (hPP : ∀ x, P (P x)=P x)
    (hPB : ∀ x, P (B x)=P (B (P x)))
    (δ : ℝ) (hδ : δ < 1) (hB : ‖B-ContinuousLinearMap.id ℂ C‖ ≤ δ)
    (y c : C) (heq : y+B c=0) :
    ‖P c‖ ≤ (1-δ)⁻¹*‖P y‖ := by
  have hPy : P (B (P c)) = -P y := by
    rw [← hPB]
    have h := congrArg P heq
    simp only [map_add,map_zero] at h
    exact eq_neg_of_add_eq_zero_right h
  have herr : ‖P ((B-ContinuousLinearMap.id ℂ C) (P c))‖ ≤ δ*‖P c‖ := by
    calc
      _ ≤ ‖P‖*‖(B-ContinuousLinearMap.id ℂ C) (P c)‖ := P.le_opNorm _
      _ ≤ 1*‖(B-ContinuousLinearMap.id ℂ C) (P c)‖ :=
        mul_le_mul_of_nonneg_right hP (norm_nonneg _)
      _ ≤ δ*‖P c‖ := by
        rw [one_mul]
        exact ((B-ContinuousLinearMap.id ℂ C).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right hB (norm_nonneg _))
  have hident : P c=P (B (P c))-P ((B-ContinuousLinearMap.id ℂ C) (P c)) := by
    simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.id_apply,map_sub,hPP]
    abel
  have hnorm : ‖P c‖ ≤ ‖P y‖+δ*‖P c‖ := by
    calc
      ‖P c‖ = ‖P (B (P c))-P ((B-ContinuousLinearMap.id ℂ C) (P c))‖ := congrArg norm hident
      _ ≤ ‖P (B (P c))‖+‖P ((B-ContinuousLinearMap.id ℂ C) (P c))‖ := norm_sub_le _ _
      _ ≤ ‖P y‖+δ*‖P c‖ := by rw [hPy,norm_neg]; exact add_le_add le_rfl herr
  have hpos : 0 < 1-δ := by linarith
  rw [inv_mul_eq_div,le_div_iff₀ hpos]
  nlinarith

/-- The exact Schur complementary solution obeys the projected estimate;
 no truncation of its geometric inverse is used. -/
theorem fullSchurComplementCoordinate_projected_bound
    {D : Type*} [NormedAddCommGroup D] [NormedSpace ℂ D] [CompleteSpace C]
    (A : D →L[ℂ] C) (B P : C →L[ℂ] C)
    (hP : ‖P‖ ≤ 1) (hPP : ∀ x, P (P x)=P x)
    (hPB : ∀ x, P (B x)=P (B (P x)))
    (δ : ℝ) (hδ : δ < 1) (hB : ‖B-ContinuousLinearMap.id ℂ C‖ ≤ δ) (u : D) :
    ‖P (fullSchurComplementCoordinate A B (hB.trans_lt hδ) u)‖ ≤
      (1-δ)⁻¹*‖P (A u)‖ :=
  projectedComplement_bound P B hP hPP hPB δ hδ hB _ _
    (fullSchurComplementCoordinate_equation A B (hB.trans_lt hδ) u)

end
end MeyerGeneralProblem.Adaptive
