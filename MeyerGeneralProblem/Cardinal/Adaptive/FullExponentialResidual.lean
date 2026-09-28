module

public import MeyerGeneralProblem.Cardinal.Adaptive.FullExponentialBounds

@[expose] public section

/-! # Exact full exponential residual on a fixed vector -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section

variable {A : Type*} [NormedRing A] [NormOneClass A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- The entire exponential residual factors by the original generator, with
all higher powers retained in an absolutely convergent operator series. -/
theorem fullExponential_sub_one_factor (Z : A) (hZ : ‖Z‖ < 1) :
    NormedSpace.exp Z-1=boundedOperatorSeries (fun n => ((n+1).factorial : ℂ)⁻¹) Z*Z := by
  have h := boundedOperatorSeries_sub_constant (fun n => (n.factorial : ℂ)⁻¹)
    inverseFactorial_norm_le_one Z hZ
  simp only [Nat.factorial_zero,Nat.cast_one,inv_one,one_smul,←fullExponential_eq_series] at h
  rw [h]
  have hs := (boundedOperatorSeries_hasSum (fun n => ((n+1).factorial : ℂ)⁻¹)
    (fun n => inverseFactorial_norm_le_one (n+1)) Z hZ).mul_right Z
  rw [← hs.tsum_eq]
  apply tsum_congr
  intro n
  rw [pow_succ,smul_mul_assoc]

/-- A small actual residual Zx controls the entire exponential residual;
no bound for x is substituted in place of that residual. -/
theorem fullExponential_apply_sub_self_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] [NontrivialTopology E]
    (Z : E →L[ℂ] E) (hZ : ‖Z‖ < 1) (x : E) :
    ‖NormedSpace.exp Z x-x‖ ≤ (1-‖Z‖)⁻¹*‖Z x‖ := by
  have h := fullExponential_sub_one_factor Z hZ
  have hx := congrArg (fun A : E →L[ℂ] E => A x) h
  change NormedSpace.exp Z x-x=boundedOperatorSeries (fun n => ((n+1).factorial : ℂ)⁻¹) Z (Z x) at hx
  rw [hx]
  calc
    _ ≤ ‖boundedOperatorSeries (fun n => ((n+1).factorial : ℂ)⁻¹) Z‖*‖Z x‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (boundedOperatorSeries_norm_le _ (fun n => inverseFactorial_norm_le_one (n+1)) Z hZ) (norm_nonneg _)

end
end MeyerGeneralProblem.Adaptive
