module

public import MeyerGeneralProblem.Basic

@[expose] public section

/-!
# Fourier normalisation

Mathlib's real Fourier transform has kernel `exp (-2 * π * I * ⟨x, ξ⟩)`.
Consequently its square is reflection and its fourth power is the identity.
-/

namespace MeyerGeneralProblem

noncomputable section

open scoped FourierTransform

/-- Reflection through the origin on complex-valued Schwartz functions on `ℝ`. -/
def schwartzReflectionCLM : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (LinearIsometryEquiv.neg ℝ (E := ℝ)).toContinuousLinearEquiv

@[simp]
theorem schwartzReflectionCLM_apply (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    schwartzReflectionCLM f x = f (-x) := by
  rfl

@[simp]
theorem schwartzReflectionCLM_involutive (f : SchwartzMap ℝ ℂ) :
    schwartzReflectionCLM (schwartzReflectionCLM f) = f := by
  ext x
  simp

/-- Reflection through the origin on complex-valued tempered distributions. -/
def temperedReflectionCLM :
    TemperedDistribution ℝ ℂ →L[ℂ] TemperedDistribution ℝ ℂ :=
  PointwiseConvergenceCLM.precomp ℂ schwartzReflectionCLM

@[simp]
theorem temperedReflectionCLM_apply (T : TemperedDistribution ℝ ℂ)
    (f : SchwartzMap ℝ ℂ) :
    temperedReflectionCLM T f = T (schwartzReflectionCLM f) :=
  rfl

@[simp]
theorem temperedReflectionCLM_involutive (T : TemperedDistribution ℝ ℂ) :
    temperedReflectionCLM (temperedReflectionCLM T) = T := by
  ext f
  simp

@[simp]
theorem temperedReflectionCLM_delta (x : ℝ) :
    temperedReflectionCLM (TemperedDistribution.delta x) = TemperedDistribution.delta (-x) := by
  ext f
  simp [TemperedDistribution.delta_apply]

/-- The square of the Fourier transform is reflection on Schwartz functions. -/
theorem schwartz_fourier_sq_eq_reflection (f : SchwartzMap ℝ ℂ) :
    FourierTransform.fourier (FourierTransform.fourier f) = schwartzReflectionCLM f := by
  have h : f = schwartzReflectionCLM
      (FourierTransform.fourier (FourierTransform.fourier f)) := by
    simpa [schwartzReflectionCLM] using
      (SchwartzMap.fourierInv_apply_eq (FourierTransform.fourier f))
  calc
    FourierTransform.fourier (FourierTransform.fourier f) =
        schwartzReflectionCLM (schwartzReflectionCLM
          (FourierTransform.fourier (FourierTransform.fourier f))) := by
      rw [schwartzReflectionCLM_involutive]
    _ = schwartzReflectionCLM f := (congrArg schwartzReflectionCLM h).symm

/-- The square of the Fourier transform is reflection on tempered distributions. -/
theorem fourier_sq_eq_reflection (T : TemperedDistribution ℝ ℂ) :
    FourierTransform.fourier (FourierTransform.fourier T) = temperedReflectionCLM T := by
  ext f
  simp only [TemperedDistribution.fourier_apply, temperedReflectionCLM_apply,
    schwartz_fourier_sq_eq_reflection]

/-- Four Fourier transforms give the identity on complex tempered distributions. -/
theorem fourier_pow_four (T : TemperedDistribution ℝ ℂ) :
    FourierTransform.fourier (FourierTransform.fourier
      (FourierTransform.fourier (FourierTransform.fourier T))) = T := by
  calc
    FourierTransform.fourier (FourierTransform.fourier
        (FourierTransform.fourier (FourierTransform.fourier T))) =
        temperedReflectionCLM
          (FourierTransform.fourier (FourierTransform.fourier T)) :=
      fourier_sq_eq_reflection _
    _ = temperedReflectionCLM (temperedReflectionCLM T) :=
      congrArg temperedReflectionCLM (fourier_sq_eq_reflection T)
    _ = T := temperedReflectionCLM_involutive T

end

end MeyerGeneralProblem
