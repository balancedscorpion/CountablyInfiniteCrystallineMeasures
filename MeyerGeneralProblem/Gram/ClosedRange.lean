module

public import MeyerGeneralProblem.Gram.CoefficientModel

@[expose] public section

/-!
# Closed range from strict coefficient-Gram positivity

The inverse-square-root whitener turns a synthesis map with strictly positive
coefficient Gram into an isometry with the same range. Consequently the
original synthesis range is closed. This generic operator fact lives below
both the carrier Gram and endpoint support layers.
-/

namespace MeyerGeneralProblem

noncomputable section

variable {C H : Type*}
  [NormedAddCommGroup C] [InnerProductSpace ℂ C] [CompleteSpace C]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The inverse-square-root Gram whitener is invertible whenever the Gram
operator is strictly positive. -/
theorem gramWhitener_isUnit
    (G : C →L[ℂ] C) (hG : IsStrictlyPositive G) :
    IsUnit (gramWhitener G) := by
  rw [gramWhitener]
  exact (CFC.isUnit_rpow_iff G (-(1 / 2) : ℝ) (by norm_num) hG.nonneg).mpr
    hG.isUnit

/-- The inverse-square-root Gram whitener as a continuous linear
equivalence. -/
def gramWhitenerEquiv
    (G : C →L[ℂ] C) (hG : IsStrictlyPositive G) : C ≃L[ℂ] C :=
  ContinuousLinearEquiv.unitsEquiv ℂ C (gramWhitener_isUnit G hG).unit

@[simp]
theorem gramWhitenerEquiv_apply
    (G : C →L[ℂ] C) (hG : IsStrictlyPositive G) (c : C) :
    gramWhitenerEquiv G hG c = gramWhitener G c := by
  simp only [gramWhitenerEquiv, ContinuousLinearEquiv.unitsEquiv_apply]
  rw [IsUnit.unit_spec]

/-- Gram-whitened synthesis, bundled as a linear isometry. -/
def whitenedSynthesisIsometry
    (S : C →L[ℂ] H) (hS : IsStrictlyPositive (coefficientGram S)) :
    C →ₗᵢ[ℂ] H :=
  (whitenedSynthesis S).toLinearMap.toLinearIsometry
    ((whitenedSynthesis S).isometry_iff_adjoint_comp_self.mpr
      (whitenedSynthesis_adjoint_comp_self S hS))

@[simp]
theorem whitenedSynthesisIsometry_apply
    (S : C →L[ℂ] H) (hS : IsStrictlyPositive (coefficientGram S))
    (c : C) :
    whitenedSynthesisIsometry S hS c = whitenedSynthesis S c :=
  rfl

/-- Whitening changes coefficient coordinates but not the synthesis range. -/
theorem whitenedSynthesis_range_eq
    (S : C →L[ℂ] H) (hS : IsStrictlyPositive (coefficientGram S)) :
    (whitenedSynthesis S).range = S.range := by
  apply le_antisymm
  · rintro _ ⟨c, rfl⟩
    exact ⟨gramWhitener (coefficientGram S) c, rfl⟩
  · rintro _ ⟨c, rfl⟩
    obtain ⟨d, hd⟩ := (gramWhitenerEquiv
      (coefficientGram S) hS).surjective c
    refine ⟨d, ?_⟩
    change S (gramWhitener (coefficientGram S) d) = S c
    simpa only [gramWhitenerEquiv_apply] using congrArg S hd

/-- The range of a synthesis map with strictly positive Gram is closed. -/
theorem isClosed_range_of_coefficientGram_strictlyPositive
    (S : C →L[ℂ] H) (hS : IsStrictlyPositive (coefficientGram S)) :
    IsClosed (S.range : Set H) := by
  rw [← whitenedSynthesis_range_eq S hS]
  exact (whitenedSynthesisIsometry S hS).isometry.antilipschitz.isClosed_range
    (whitenedSynthesis S).uniformContinuous

end

end MeyerGeneralProblem
