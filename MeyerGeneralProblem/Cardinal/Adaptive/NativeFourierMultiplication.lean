module

public import MeyerGeneralProblem.Cardinal.Adaptive.AnnihilatorFourierSeries
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
import all Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

/-! # Whole native Fourier series and multiplication

Identify the strong native sum from its actual Hermite coefficient integrals.
This avoids imposing convergence in an unproved Schwartz topology.
-/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open MeasureTheory
open scoped BigOperators FourierTransform

private theorem summable_norm_of_frequency_moment {ι : Type*} (c : ι → ℂ)
    (freq : ι → ℝ) (m : ℕ)
    (h : Summable (fun i => (1+|freq i|)^m * ‖c i‖)) :
    Summable (fun i => ‖c i‖) := by
  apply Summable.of_nonneg_of_le (fun i => norm_nonneg _) _ h
  intro i
  have hp : 1 ≤ (1+|freq i|)^m := one_le_pow₀ (by linarith [abs_nonneg (freq i)])
  nlinarith [norm_nonneg (c i)]

/-- Full modulated Schwartz tests converge in every original norm controlled
by the corresponding actual frequency moment. -/
theorem summable_native_modulated_tests {ι : Type*} (m : ℕ)
    (c : ι → ℂ) (freq : ι → ℝ)
    (h : Summable (fun i => (1+|freq i|)^(2*m) * ‖c i‖)) (f : SchwartzMap ℝ ℂ) :
    Summable (fun i => c i • schwartzToHermiteScale m (combSchwartzModulation (freq i) f)) := by
  obtain ⟨C,hC,hbound⟩ := exists_hermite_modulation_bound m
  apply Summable.of_norm_bounded (h.mul_left (C*‖schwartzToHermiteScale m f‖))
  intro i
  rw [norm_smul]
  apply (mul_le_mul_of_nonneg_left (hbound (freq i) f) (norm_nonneg _)).trans_eq
  ring

private theorem coefficient_sum_of_pointwise {ι : Type*} [Countable ι]
    (c : ι → ℂ) (freq : ι → ℝ) (h : Summable (fun i => ‖c i‖))
    (f u : SchwartzMap ℝ ℂ)
    (hu : ∀ x, u x = ∑' i, c i * combSchwartzModulation (freq i) f x) (n : ℕ) :
    schwartzHermiteCoefficients u n =
      ∑' i, c i * schwartzHermiteCoefficients (combSchwartzModulation (freq i) f) n := by
  let F (i : ι) (x : ℝ) := c i *
    (normalizedHermiteSchwartz n x * combSchwartzModulation (freq i) f x)
  have hi (i : ι) : Integrable (F i) :=
    (((normalizedHermiteSchwartz n).memLp 2 volume).integrable_mul
      ((combSchwartzModulation (freq i) f).memLp 2 volume)).const_mul (c i)
  have hm : Summable (fun i => ∫ x : ℝ, ‖F i x‖) := by
    have he (i : ι) : (∫ x : ℝ, ‖F i x‖) =
        ‖c i‖ * ∫ x : ℝ, ‖normalizedHermiteSchwartz n x‖ * ‖f x‖ := by
      simp only [F, combSchwartzModulation_apply, norm_mul,
        norm_combModulationCharacter, one_mul]
      rw [integral_const_mul]
    simpa only [he] using h.mul_right (∫ x : ℝ, ‖normalizedHermiteSchwartz n x‖ * ‖f x‖)
  have hs := integral_tsum_of_summable_integral_norm hi hm
  rw [schwartzHermiteCoefficients_apply_integral]
  calc
    _ = ∫ x : ℝ, ∑' i, F i x := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [hu x, ← tsum_mul_left]
      apply tsum_congr
      intro i
      dsimp [F]
      ring
    _ = ∑' i, ∫ x : ℝ, F i x := hs.symm
    _ = _ := by
      apply tsum_congr
      intro i
      rw [schwartzHermiteCoefficients_apply_integral, ← integral_const_mul]

/-- Pointwise identification and the actual moment bound determine the strong
native sum, at the original order and on the complete test function. -/
theorem hasSum_native_modulated_tests {ι : Type*} [Countable ι] (m : ℕ)
    (c : ι → ℂ) (freq : ι → ℝ)
    (h : Summable (fun i => (1+|freq i|)^(2*m) * ‖c i‖)) (f u : SchwartzMap ℝ ℂ)
    (hu : ∀ x, u x = ∑' i, c i * combSchwartzModulation (freq i) f x) :
    HasSum (fun i => c i • schwartzToHermiteScale m (combSchwartzModulation (freq i) f))
      (schwartzToHermiteScale m u) := by
  have hn := summable_native_modulated_tests m c freq h f
  apply hn.hasSum_iff.mpr
  apply lp.ext
  funext n
  have he := (lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 n).hasSum hn.hasSum
  change HasSum (fun i => (c i • schwartzToHermiteScale m
    (combSchwartzModulation (freq i) f)) n)
    ((∑' i, c i • schwartzToHermiteScale m (combSchwartzModulation (freq i) f)) n) at he
  rw [← he.tsum_eq]
  simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
    schwartzToHermiteScale_apply, normalizeHermiteCoefficients]
  rw [coefficient_sum_of_pointwise c freq
    (summable_norm_of_frequency_moment c freq (2*m) h) f u hu n, ← tsum_mul_left]
  apply tsum_congr
  intro i
  ring

private theorem summable_native_modulation_series {ι : Type*} (m : ℕ)
    (c : ι → ℂ) (freq : ι → ℝ)
    (h : Summable (fun i => (1+|freq i|)^(2*m) * ‖c i‖)) :
    Summable (fun i => c i • nativeModulation m (freq i)) := by
  obtain ⟨C,hC,hbound⟩ := exists_nativeModulation_norm_bound m
  apply Summable.of_norm_bounded (h.mul_left C)
  intro i
  rw [norm_smul]
  apply (mul_le_mul_of_nonneg_left (hbound (freq i)) (norm_nonneg _)).trans_eq
  ring

/-- The full modulation series equals actual multiplication on every native
distribution. Only its genuine frequency moment and pointwise expansion are used. -/
theorem hasSum_distribution_modulation {ι : Type*} [Countable ι] (m : ℕ)
    (c : ι → ℂ) (freq : ι → ℝ)
    (h : Summable (fun i => (1+|freq i|)^(2*m) * ‖c i‖))
    (χ : ℝ → ℂ) (hχ : χ.HasTemperateGrowth)
    (hexp : ∀ x, χ x = ∑' i, c i * combModulationCharacter (freq i) x)
    (T : HermiteScale (-(m:ℤ))) :
    HasSum (fun i => c i • combDistributionModulation (freq i) (hermiteScaleDistribution m T))
      (TemperedDistribution.smulLeftCLM ℂ χ (hermiteScaleDistribution m T)) := by
  have hs := summable_native_modulation_series m c freq h
  have hv := (ContinuousLinearMap.apply ℂ (HermiteScale (-(m:ℤ))) T).hasSum hs.hasSum
  have hd := (hermiteScaleDistributionCLM m).hasSum hv
  have hd' : HasSum
      (fun i => c i • combDistributionModulation (freq i) (hermiteScaleDistribution m T))
      (hermiteScaleDistribution m ((∑' i, c i • nativeModulation m (freq i)) T)) := by
    simpa only [ContinuousLinearMap.apply_apply, smul_apply, map_smul,
      hermiteScaleDistributionCLM_apply, nativeModulation_realizes] using hd
  suffices heq : hermiteScaleDistribution m ((∑' i, c i • nativeModulation m (freq i)) T) =
      TemperedDistribution.smulLeftCLM ℂ χ (hermiteScaleDistribution m T) by
    exact heq ▸ hd'
  ext f
  have he := (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ f).hasSum hd'
  have ht := hasSum_native_modulated_tests m c freq h f (SchwartzMap.smulLeftCLM ℂ χ f) (by
    intro x
    rw [SchwartzMap.smulLeftCLM_apply_apply hχ, smul_eq_mul, hexp x, ← tsum_mul_right]
    apply tsum_congr
    intro i
    rw [combSchwartzModulation_apply]
    ring)
  have hp := (hermiteScalePairingLeftCLM m T).hasSum ht
  have hp' : HasSum
      (fun i => c i * combDistributionModulation (freq i) (hermiteScaleDistribution m T) f)
      (TemperedDistribution.smulLeftCLM ℂ χ (hermiteScaleDistribution m T) f) := by
    simpa only [map_smul, smul_eq_mul, hermiteScalePairingLeftCLM_apply,
      ← hermiteScaleDistribution_apply, TemperedDistribution.smulLeftCLM_apply_apply,
      combDistributionModulation_apply] using hp
  exact he.unique hp'

/-- Positive modulation becomes positive distributional translation under
Fourier transform, with the sign checked on the complete Schwartz test. -/
theorem fourier_combDistributionModulation (a : ℝ) (T : TemperedDistribution ℝ ℂ) :
    𝓕 (combDistributionModulation a T) = combDistributionTranslation a (𝓕 T) := by
  ext f
  simp only [TemperedDistribution.fourier_apply, combDistributionModulation_apply,
    combDistributionTranslation_apply]
  congr 1
  ext x
  rw [combSchwartzModulation_apply, fourier_combSchwartzTranslation]

/-- Full Fourier multiplication/translation identity for a genuine native
source, proved as convergence of the entire distributional series. -/
theorem hasSum_fourier_multiplier_translations {ι : Type*} [Countable ι] (m : ℕ)
    (c : ι → ℂ) (freq : ι → ℝ)
    (h : Summable (fun i => (1+|freq i|)^(2*m) * ‖c i‖))
    (χ : ℝ → ℂ) (hχ : χ.HasTemperateGrowth)
    (hexp : ∀ x, χ x = ∑' i, c i * combModulationCharacter (freq i) x)
    (T : HermiteScale (-(m:ℤ))) :
    HasSum (fun i => c i • combDistributionTranslation (freq i) (𝓕 (hermiteScaleDistribution m T)))
      (𝓕 (TemperedDistribution.smulLeftCLM ℂ χ (hermiteScaleDistribution m T))) := by
  simpa only [map_smul, FourierTransform.fourierCLM_apply,
    fourier_combDistributionModulation] using
    (FourierTransform.fourierCLM ℂ (TemperedDistribution ℝ ℂ)).hasSum
      (hasSum_distribution_modulation m c freq h χ hχ hexp T)

/-- Inverse Fourier transforms have the opposite translation sign. -/
theorem fourierInv_combDistributionModulation (a : ℝ) (T : TemperedDistribution ℝ ℂ) :
    𝓕⁻ (combDistributionModulation a T) = combDistributionTranslation (-a) (𝓕⁻ T) := by
  have he : 𝓕 (combDistributionTranslation (-a) (𝓕⁻ T)) = combDistributionModulation a T := by
    rw [fourier_combDistributionTranslation, neg_neg, FourierTransform.fourier_fourierInv_eq]
  rw [← he, FourierTransform.fourierInv_fourier_eq]

/-- The complete inverse-Fourier multiplier series retains all negative
translations with exactly the same original frequency-moment assumption. -/
theorem hasSum_fourierInv_multiplier_translations {ι : Type*} [Countable ι] (m : ℕ)
    (c : ι → ℂ) (freq : ι → ℝ)
    (h : Summable (fun i => (1+|freq i|)^(2*m) * ‖c i‖))
    (χ : ℝ → ℂ) (hχ : χ.HasTemperateGrowth)
    (hexp : ∀ x, χ x = ∑' i, c i * combModulationCharacter (freq i) x)
    (T : HermiteScale (-(m:ℤ))) :
    HasSum (fun i => c i • combDistributionTranslation (-freq i) (𝓕⁻ (hermiteScaleDistribution m T)))
      (𝓕⁻ (TemperedDistribution.smulLeftCLM ℂ χ (hermiteScaleDistribution m T))) := by
  simpa only [map_smul, FourierTransform.fourierInvCLM_apply,
    fourierInv_combDistributionModulation] using
    (FourierTransform.fourierInvCLM ℂ (TemperedDistribution ℝ ℂ)).hasSum
      (hasSum_distribution_modulation m c freq h χ hχ hexp T)

end
end MeyerGeneralProblem.Adaptive
