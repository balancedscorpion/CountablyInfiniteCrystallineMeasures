module

public import MeyerGeneralProblem.Cardinal.Adaptive.ZakDistributionFamily

@[expose] public section

/-! # Exact integer covariance of the actual whole Zak family -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open scoped FourierTransform

/-- The actual Fourier character at an integer pair is exactly one. -/
theorem combModulationCharacter_int_int (m n : ℤ) :
    combModulationCharacter (m : ℝ) (n : ℝ)=1 := by
  rw [combModulationCharacter_eq_exp]
  push_cast
  have he : 2*(Real.pi : ℂ)*Complex.I*(m : ℂ)*(n : ℂ)=
      ((m*n : ℤ) : ℂ)*(2*(Real.pi : ℂ)*Complex.I) := by push_cast; ring
  rw [he,Complex.exp_int_mul,Complex.exp_two_pi_mul_I,one_zpow]

/-- Integer translation of the frequency test leaves the complete Zak action
unchanged, proving its actual frequency periodicity. -/
theorem zakTensorAction_periodic_frequency (T : TemperedDistribution ℝ ℂ)
    (f g : SchwartzMap ℝ ℂ) (m : ℤ) :
    zakTensorAction T f (combSchwartzTranslation (m : ℝ) g)=zakTensorAction T f g := by
  unfold zakTensorAction
  apply tsum_congr
  intro n
  rw [fourier_combSchwartzTranslation,combModulationCharacter_int_int,one_mul]

/-- Each genuine tempered frequency slice is integer-periodic as an original
distribution, rather than merely having periodic formal Fourier coefficients. -/
theorem zakTensorSlice_integer_periodic (T : TemperedDistribution ℝ ℂ)
    (f : SchwartzMap ℝ ℂ) (m : ℤ) :
    combDistributionTranslation (m : ℝ) (zakTensorSlice T f)=zakTensorSlice T f := by
  ext g
  rw [combDistributionTranslation_apply,zakTensorSlice_apply,zakTensorSlice_apply]
  exact zakTensorAction_periodic_frequency T f g m

/-- Exact integer physical shift of the whole Zak tensor action, with the
negative frequency modulation prescribed by the original Fourier convention. -/
theorem zakTensorAction_integer_shift (T : TemperedDistribution ℝ ℂ)
    (f g : SchwartzMap ℝ ℂ) (m : ℤ) :
    zakTensorAction T (combSchwartzTranslation (m : ℝ) f) g=
      zakTensorAction T f (combSchwartzModulation (-(m : ℝ)) g) := by
  unfold zakTensorAction
  calc
    _ = ∑' n : ℤ, (𝓕 g) ((n+m : ℤ) : ℝ)*T
        (combSchwartzTranslation (-((n+m : ℤ) : ℝ)) (combSchwartzTranslation (m : ℝ) f)) :=
      ((Equiv.addRight m).tsum_eq (fun n : ℤ =>
        (𝓕 g) (n : ℝ)*T (combSchwartzTranslation (-(n : ℝ))
          (combSchwartzTranslation (m : ℝ) f)))).symm
    _ = _ := by
      apply tsum_congr
      intro n
      rw [fourier_combSchwartzModulation_neg]
      simp only [Int.cast_add,combSchwartzTranslation_apply]
      congr 1
      · congr 1
        ring
      · congr 1
        ext x
        simp only [combSchwartzTranslation_apply]
        congr 1
        ring

/-- The genuine Schwartz-to-distribution family has the exact Zak twisted
integer boundary law; this includes the whole original source. -/
theorem zakTensorSlice_integer_shift (T : TemperedDistribution ℝ ℂ)
    (f : SchwartzMap ℝ ℂ) (m : ℤ) :
    zakTensorSlice T (combSchwartzTranslation (m : ℝ) f)=
      combDistributionModulation (-(m : ℝ)) (zakTensorSlice T f) := by
  ext g
  rw [combDistributionModulation_apply,zakTensorSlice_apply,zakTensorSlice_apply]
  exact zakTensorAction_integer_shift T f g m

end
end MeyerGeneralProblem.Adaptive
