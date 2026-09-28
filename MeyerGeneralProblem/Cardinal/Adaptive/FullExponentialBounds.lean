module

public import MeyerGeneralProblem.Cardinal.Adaptive.BoundedOperatorSeries
public import Mathlib.Analysis.Normed.Algebra.Exponential
import all Mathlib.Analysis.Normed.Algebra.Exponential

@[expose] public section

/-! # Complete operator exponential and quantitative quadratic remainder -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
variable {A : Type*} [NormedRing A] [NormOneClass A] [NormedAlgebra ℂ A] [CompleteSpace A]

theorem inverseFactorial_norm_le_one (n : ℕ) : ‖((n.factorial : ℂ)⁻¹)‖ ≤ 1 := by
  rw [norm_inv,Complex.norm_natCast]
  have hn : (1 : ℝ) ≤ n.factorial := by exact_mod_cast Nat.factorial_pos n
  exact inv_le_one_of_one_le₀ hn

/-- The usual full Banach-algebra exponential is exactly the constructed
power series with inverse factorial coefficients. -/
theorem fullExponential_eq_series (X : A) :
    NormedSpace.exp X=boundedOperatorSeries (fun n => (n.factorial : ℂ)⁻¹) X :=
  (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) X).tsum_eq.symm

theorem fullExponential_sub_one_bound (X : A) (hX : ‖X‖ < 1) :
    ‖NormedSpace.exp X-1‖ ≤ ‖X‖/(1-‖X‖) := by
  rw [fullExponential_eq_series]
  exact boundedOperatorSeries_sub_one_bound _ inverseFactorial_norm_le_one (by norm_num) X hX

theorem fullExponential_quadratic_bound (X : A) (hX : ‖X‖ < 1) :
    ‖NormedSpace.exp X-1-X‖ ≤ ‖X‖^2/(1-‖X‖) := by
  rw [fullExponential_eq_series]
  exact boundedOperatorSeries_sub_linear_bound _ inverseFactorial_norm_le_one (by norm_num) (by norm_num) X hX

/-- The exact accepted small-gauge estimate includes every exponential term. -/
theorem fullExponential_seam_close (X : A) (hX : ‖X‖ ≤ 8*(1/4096 : ℝ)) :
    ‖NormedSpace.exp X-1‖ ≤ 9*(1/4096 : ℝ) := by
  have hp : 0 < 1-‖X‖ := by linarith
  apply (fullExponential_sub_one_bound X (by linarith)).trans
  apply (div_le_iff₀ hp).mpr
  linarith

/-- The entire second-order remainder has the source's 65R² bound. -/
theorem fullExponential_seam_quadratic (X : A) (hX : ‖X‖ ≤ 8*(1/4096 : ℝ)) :
    ‖NormedSpace.exp X-1-X‖ ≤ 65*(1/4096 : ℝ)^2 := by
  have hp : 0 < 1-‖X‖ := by linarith
  apply (fullExponential_quadratic_bound X (by linarith)).trans
  apply (div_le_iff₀ hp).mpr
  nlinarith [norm_nonneg X]

/-- Original operator-norm control of the complete seam gauge. -/
theorem fullExponential_seam_norm (X : A) (hX : ‖X‖ ≤ 8*(1/4096 : ℝ)) :
    ‖NormedSpace.exp X‖ ≤ 1+9*(1/4096 : ℝ) := by
  calc
    ‖NormedSpace.exp X‖=‖(NormedSpace.exp X-1)+1‖ := by rw [sub_add_cancel]
    _ ≤ ‖NormedSpace.exp X-1‖+‖(1 : A)‖ := norm_add_le _ _
    _ ≤ _ := by rw [norm_one]; linarith [fullExponential_seam_close X hX]

end
end MeyerGeneralProblem.Adaptive
