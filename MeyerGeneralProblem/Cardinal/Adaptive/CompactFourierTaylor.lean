module

public import MeyerGeneralProblem.Cardinal.Adaptive.NativeSchwartzSeries

@[expose] public section

/-! # Exact compact Fourier Taylor kernels for the complete Zak gauge -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open MeasureTheory
open scoped FourierTransform

/-- The actual Schwartz Fourier value in the repository's positive-character
notation, with the required negative frequency. -/
theorem schwartz_fourier_integral_character (g : SchwartzMap ℝ ℂ) (a : ℝ) :
    𝓕 g a=∫ y : ℝ, combModulationCharacter (-a) y*g y := by
  simp only [SchwartzMap.fourier_coe,Real.fourier_real_eq_integral_exp_smul,
    combModulationCharacter_eq_exp,smul_eq_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  congr 2
  push_cast
  ring

private theorem compact_monomial_norm_le (g : SchwartzMap ℝ ℂ)
    (hg : ∀ y : ℝ, 1 ≤ |y| → g y=0) (r : ℕ) (y : ℝ) :
    ‖(y : ℂ)^r*g y‖ ≤ ‖g y‖ := by
  by_cases hy : |y| < 1
  · rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right (pow_le_one₀ (abs_nonneg y) hy.le) (norm_nonneg _)).trans_eq (one_mul _)
  · rw [hg y (le_of_not_gt hy),mul_zero,norm_zero]

/-- Compact support permits the entire Fourier Taylor shift at every real
increment; no finite Taylor truncation replaces the original Fourier value. -/
theorem compact_fourier_taylor (g : SchwartzMap ℝ ℂ)
    (hg : ∀ y : ℝ, 1 ≤ |y| → g y=0) (a t : ℝ) :
    (𝓕 g) (a+t)=∑' r : ℕ,
      ((-2*(Real.pi : ℂ)*Complex.I*(t : ℂ))^r/(r.factorial : ℂ)) *
        (𝓕 (mixedSchwartz r 0 g)) a := by
  let z : ℂ := -2*(Real.pi : ℂ)*Complex.I*(t : ℂ)
  let F (r : ℕ) (y : ℝ) : ℂ := (z^r/(r.factorial : ℂ))*
    (combModulationCharacter (-a) y*((y : ℂ)^r*g y))
  have hi (r : ℕ) : Integrable (F r) := by
    have h : Integrable (combSchwartzModulation (-a) (mixedSchwartz r 0 g) : ℝ → ℂ) volume :=
      (combSchwartzModulation (-a) (mixedSchwartz r 0 g)).integrable
    convert h.const_mul (z^r/(r.factorial : ℂ)) using 1
    funext y
    simp only [F,combSchwartzModulation_apply,mixedSchwartz_apply,iteratedDeriv_zero]
  have hbound (r : ℕ) (y : ℝ) : ‖F r y‖ ≤ (‖z‖^r/(r.factorial : ℝ))*‖g y‖ := by
    simp only [F,norm_mul,norm_div,norm_pow,Complex.norm_natCast,
      norm_combModulationCharacter,one_mul]
    simpa only [norm_mul,norm_pow] using
      mul_le_mul_of_nonneg_left (compact_monomial_norm_le g hg r y)
        (show 0 ≤ ‖z‖^r/(r.factorial : ℝ) by positivity)
  have hm : Summable (fun r : ℕ => ∫ y : ℝ, ‖F r y‖) := by
    apply Summable.of_nonneg_of_le (fun r => integral_nonneg (fun y => norm_nonneg _)) _
      ((Real.summable_pow_div_factorial ‖z‖).mul_right (∫ y : ℝ, ‖g y‖))
    intro r
    apply (integral_mono_ae (hi r).norm (g.integrable.norm.const_mul _)
      (Filter.Eventually.of_forall (hbound r))).trans_eq
    rw [integral_const_mul]
  have hpoint (y : ℝ) : (∑' r : ℕ, F r y)=combModulationCharacter (-(a+t)) y*g y := by
    have he := NormedSpace.expSeries_div_hasSum_exp (z*(y : ℂ))
    have ht := he.mul_right (combModulationCharacter (-a) y*g y)
    have hf : (fun r : ℕ => F r y)=fun r : ℕ =>
        ((z*(y : ℂ))^r/(r.factorial : ℂ))*(combModulationCharacter (-a) y*g y) := by
      funext r
      simp only [F,mul_pow]
      ring
    rw [hf,ht.tsum_eq]
    rw [← Complex.exp_eq_exp_ℂ]
    rw [combModulationCharacter_eq_exp,combModulationCharacter_eq_exp,← mul_assoc,← Complex.exp_add]
    congr 2
    dsimp only [z]
    push_cast
    ring
  rw [schwartz_fourier_integral_character]
  calc
    _ = ∫ y : ℝ, ∑' r : ℕ, F r y := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun y => (hpoint y).symm)
    _ = ∑' r : ℕ, ∫ y : ℝ, F r y := (integral_tsum_of_summable_integral_norm hi hm).symm
    _ = _ := by
      apply tsum_congr
      intro r
      rw [schwartz_fourier_integral_character]
      simp only [F,mixedSchwartz_apply,iteratedDeriv_zero,integral_const_mul]
      rfl

end
end MeyerGeneralProblem.Adaptive
