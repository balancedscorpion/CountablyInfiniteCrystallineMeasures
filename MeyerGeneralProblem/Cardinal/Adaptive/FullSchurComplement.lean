module

public import Mathlib.Analysis.Complex.Basic
import all Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import Mathlib.Analysis.Normed.Ring.Units
import all Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.Analysis.Normed.Operator.Banach
import all Mathlib.Analysis.Normed.Operator.Banach

@[expose] public section

/-! # Constructed inverse of the full complementary block and exact Schur reduction

These reusable operator statements retain the entire complementary inverse.
They impose no source realization or diagonal-only model assumption.
-/
namespace MeyerGeneralProblem.Adaptive
noncomputable section

section NearIdentity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- The geometric-series inverse of an actual bounded operator near identity. -/
def fullNearIdentityEquiv (A : E →L[ℂ] E) (hA : ‖A-ContinuousLinearMap.id ℂ E‖ < 1) : E ≃L[ℂ] E :=
  ContinuousLinearEquiv.ofUnit (Units.oneSub (1-A) (by
    change ‖(1 : E →L[ℂ] E)-A‖ < 1
    rw [norm_sub_rev]
    exact hA))

@[simp] theorem fullNearIdentityEquiv_apply (A : E →L[ℂ] E)
    (hA : ‖A-ContinuousLinearMap.id ℂ E‖ < 1) (x : E) : fullNearIdentityEquiv A hA x=A x := by
  change (1-(1-A) : E →L[ℂ] E) x=A x
  rw [sub_sub_cancel]

/-- The full inverse has the usual quantitative bound, proved from the original
operator norm rather than from a supplied inverse estimate. -/
theorem fullNearIdentityEquiv_symm_bound (A : E →L[ℂ] E)
    (δ : ℝ) (hδ : δ < 1) (hA : ‖A-ContinuousLinearMap.id ℂ E‖ ≤ δ) (y : E) :
    ‖(fullNearIdentityEquiv A (hA.trans_lt hδ)).symm y‖ ≤ (1-δ)⁻¹*‖y‖ := by
  let x := (fullNearIdentityEquiv A (hA.trans_lt hδ)).symm y
  have hAx : A x=y := by
    simpa only [fullNearIdentityEquiv_apply] using (fullNearIdentityEquiv A (hA.trans_lt hδ)).apply_symm_apply y
  have ht : ‖x‖ ≤ ‖y‖+δ*‖x‖ := by
    calc
      ‖x‖ = ‖A x-(A x-x)‖ := by congr 1; abel
      _ ≤ ‖A x‖+‖A x-x‖ := norm_sub_le _ _
      _ ≤ ‖A x‖+δ*‖x‖ := by
        apply add_le_add le_rfl
        have hb := (A-ContinuousLinearMap.id ℂ E).le_opNorm x
        exact hb.trans (mul_le_mul_of_nonneg_right hA (norm_nonneg _))
      _ = ‖y‖+δ*‖x‖ := by rw [hAx]
  have hp : 0 < 1-δ := by linarith
  change ‖x‖ ≤ _
  rw [inv_mul_eq_div,le_div_iff₀ hp]
  nlinarith

end NearIdentity

section Schur
variable {D C G : Type*}
variable [NormedAddCommGroup D] [NormedSpace ℂ D]
variable [NormedAddCommGroup C] [NormedSpace ℂ C] [CompleteSpace C]
variable [NormedAddCommGroup G] [NormedSpace ℂ G]

/-- Exact reduced operator after eliminating the full complementary block. -/
def fullSchurOperator (A : D →L[ℂ] C) (B : C →L[ℂ] C)
    (H : D →L[ℂ] G) (J : C →L[ℂ] G)
    (hB : ‖B-ContinuousLinearMap.id ℂ C‖ < 1) : D →L[ℂ] G :=
  H-J.comp ((fullNearIdentityEquiv B hB).symm.toContinuousLinearMap.comp A)

/-- The actual complementary coordinate, with every feedback term inverted. -/
def fullSchurComplementCoordinate (A : D →L[ℂ] C) (B : C →L[ℂ] C)
    (hB : ‖B-ContinuousLinearMap.id ℂ C‖ < 1) (u : D) : C :=
  -(fullNearIdentityEquiv B hB).symm (A u)

theorem fullSchurComplementCoordinate_equation (A : D →L[ℂ] C) (B : C →L[ℂ] C)
    (hB : ‖B-ContinuousLinearMap.id ℂ C‖ < 1) (u : D) :
    A u+B (fullSchurComplementCoordinate A B hB u)=0 := by
  have he : B ((fullNearIdentityEquiv B hB).symm (A u))=A u :=
    by simpa only [fullNearIdentityEquiv_apply] using (fullNearIdentityEquiv B hB).apply_symm_apply (A u)
  simp only [fullSchurComplementCoordinate,map_neg,he,add_neg_cancel]

/-- The two complete block equations are equivalent to the Schur equation
and the uniquely constructed complementary coordinate. -/
theorem fullSchur_kernel_iff (A : D →L[ℂ] C) (B : C →L[ℂ] C)
    (H : D →L[ℂ] G) (J : C →L[ℂ] G)
    (hB : ‖B-ContinuousLinearMap.id ℂ C‖ < 1) (u : D) (c : C) :
    (A u+B c=0 ∧ H u+J c=0) ↔
      fullSchurOperator A B H J hB u=0 ∧ c=fullSchurComplementCoordinate A B hB u := by
  constructor
  · rintro ⟨hC,hG⟩
    have hc : c=fullSchurComplementCoordinate A B hB u := by
      apply (fullNearIdentityEquiv B hB).injective
      simp only [fullNearIdentityEquiv_apply,fullSchurComplementCoordinate,map_neg]
      have he : B ((fullNearIdentityEquiv B hB).symm (A u))=A u :=
        by simpa only [fullNearIdentityEquiv_apply] using (fullNearIdentityEquiv B hB).apply_symm_apply (A u)
      rw [he]
      exact eq_neg_of_add_eq_zero_right hC
    refine ⟨?_,hc⟩
    rw [hc] at hG
    simpa [fullSchurOperator,fullSchurComplementCoordinate,sub_eq_add_neg] using hG
  · rintro ⟨hK,rfl⟩
    refine ⟨fullSchurComplementCoordinate_equation A B hB u,?_⟩
    simpa [fullSchurOperator,fullSchurComplementCoordinate,sub_eq_add_neg] using hK

/-- A quantitative estimate for the actual full complementary solution. -/
theorem fullSchurComplementCoordinate_bound (A : D →L[ℂ] C) (B : C →L[ℂ] C)
    (δ : ℝ) (hδ : δ < 1) (hB : ‖B-ContinuousLinearMap.id ℂ C‖ ≤ δ) (u : D) :
    ‖fullSchurComplementCoordinate A B (hB.trans_lt hδ) u‖ ≤ (1-δ)⁻¹*‖A‖*‖u‖ := by
  rw [fullSchurComplementCoordinate,norm_neg]
  calc
    _ ≤ (1-δ)⁻¹*‖A u‖ := fullNearIdentityEquiv_symm_bound B δ hδ hB _
    _ ≤ (1-δ)⁻¹*‖A‖*‖u‖ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (A.le_opNorm u) (by positivity)

end Schur
end
end MeyerGeneralProblem.Adaptive
