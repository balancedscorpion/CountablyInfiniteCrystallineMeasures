module

public import MeyerGeneralProblem.Sampling.KNSGraphSpaceFourier
public import MeyerGeneralProblem.Sampling.SignedSquareSobolevDomain

@[expose] public section

/-!
# Actual smooth functions in the complete KNS graph

The Fourier weight follows from the actual top classical derivative, with
its exact 2π normalization and genuine L2 reflection. This adapter does not
impose smoothness on arbitrary elements of the complete graph.
-/

namespace MeyerGeneralProblem

noncomputable section

set_option maxHeartbeats 4000000

open MeasureTheory
open scoped FourierTransform ContDiff

/-- Inverse L2 Fourier transformation is actual real reflection of the
forward transform, with no representative chosen in advance. -/
theorem knsL2_fourierInv_eq_reflection (f : KNSL2) :
    𝓕⁻ f = knsL2Reflection (𝓕 f : KNSL2) := by
  have h : (𝓕⁻ f : KNSL2) = 𝓕 (𝓕 (𝓕 f : KNSL2) : KNSL2) := by
    apply (Lp.fourierTransformₗᵢ ℝ ℂ).injective
    change 𝓕 (𝓕⁻ f : KNSL2) = 𝓕 (𝓕 (𝓕 (𝓕 f : KNSL2) : KNSL2) : KNSL2)
    rw [FourierTransform.fourier_fourierInv_eq, knsL2_fourier_four]
  rw [h, knsL2_fourier_fourier]

private theorem smooth_power_reflection_ae (k : ℕ) (f g : KNSL2)
    (hw : (fun x : ℝ => (x : ℂ) ^ k * f x) =ᵐ[volume] g) :
    (fun x : ℝ => (x : ℂ) ^ k * knsL2Reflection f x) =ᵐ[volume]
      ((-1 : ℂ) ^ k • knsL2Reflection g : KNSL2) := by
  have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae_eq_comp hw
  filter_upwards [knsL2Reflection_ae f, knsL2Reflection_ae g, h,
    Lp.coeFn_smul ((-1 : ℂ) ^ k) (knsL2Reflection g)] with x hf hg hw hs
  simp only [Function.comp_apply] at hw
  rw [hf, hs]
  simp only [Pi.smul_apply, smul_eq_mul, hg, ← hw, Complex.ofReal_neg]
  have hp : (-1 : ℂ) ^ k * (-(x : ℂ)) ^ k = (x : ℂ) ^ k := by
    rw [← mul_pow]
    congr 1
    ring
  rw [← mul_assoc, hp]

/-- The actual forward Fourier power weight of a smooth function is in
L2, with norm exactly `(2π)^(-k)` times the top classical derivative norm.
Only zeroth and top physical derivatives are assumed in L2. -/
theorem memLp_forward_power_of_top_classical_derivative {f : ℝ → ℂ} (k : ℕ)
    (hf : ContDiff ℝ ∞ f) (hF : MemLp f 2) (hD : MemLp (iteratedDeriv k f) 2) :
    ∃ hW : MemLp (fun x : ℝ => (x : ℂ) ^ k * (𝓕 hF.toLp : KNSL2) x) 2,
      ‖hW.toLp‖ = ((2 * Real.pi) ^ k)⁻¹ * ‖hD.toLp‖ := by
  obtain ⟨hK, _, hn⟩ := memLp_fourierDerivativeData_of_top_classical_derivative k hf hF hD
  let G : KNSL2 := 𝓕⁻ hF.toLp
  let a : ℂ := -2 * (Real.pi : ℂ) * Complex.I
  have ha : a ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  have he (x : ℝ) : (a ^ k)⁻¹ * fourierDerivativeData k (G : ℝ → ℂ) x =
      (x : ℂ) ^ k * G x := by
    change (a ^ k)⁻¹ * ((a * (x : ℂ)) ^ k * G x) = _
    rw [mul_pow]
    calc
      _ = ((a ^ k)⁻¹ * a ^ k) * ((x : ℂ) ^ k * G x) := by ring
      _ = _ := by rw [inv_mul_cancel₀ (pow_ne_zero k ha), one_mul]
  have hw : MemLp (fun x : ℝ => (x : ℂ) ^ k * G x) 2 := by
    have hw₀ := hK.const_smul ((a ^ k)⁻¹)
    change MemLp (fun x : ℝ => (a ^ k)⁻¹ * fourierDerivativeData k (G : ℝ → ℂ) x) 2 at hw₀
    simpa only [he] using hw₀
  have hweq : hw.toLp = (a ^ k)⁻¹ • hK.toLp := by
    apply Lp.ext
    filter_upwards [hw.coeFn_toLp, Lp.coeFn_smul ((a ^ k)⁻¹) hK.toLp,
      hK.coeFn_toLp] with x hx hy hz
    rw [hx, hy]
    simp only [Pi.smul_apply, smul_eq_mul, hz]
    exact (he x).symm
  have hanorm : ‖a‖ = 2 * Real.pi := by
    simp [a, abs_of_pos Real.pi_pos]
  have hnorm : ‖hw.toLp‖ = ((2 * Real.pi) ^ k)⁻¹ * ‖hD.toLp‖ := by
    rw [hweq, norm_smul, norm_inv, norm_pow, hanorm, hn]
  have hG : knsL2Reflection G = (𝓕 hF.toLp : KNSL2) := by
    dsimp [G]
    rw [knsL2_fourierInv_eq_reflection, knsL2Reflection_involutive]
  have hae := smooth_power_reflection_ae k G hw.toLp hw.coeFn_toLp.symm
  rw [hG] at hae
  have hW := (memLp_congr_ae hae).mpr (Lp.memLp _)
  have heq : hW.toLp = (-1 : ℂ) ^ k • knsL2Reflection hw.toLp :=
    Lp.ext (hW.coeFn_toLp.trans hae)
  refine ⟨hW, ?_⟩
  rw [heq, norm_smul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    knsL2Reflection.norm_map, hnorm]

namespace KNSGraphSpace

/-- Lift a genuinely smooth physical function with actual mass, power
weight and top derivative in L2 into the complete graph domain. -/
def ofSmooth (k : ℕ) {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (hF : MemLp f 2)
    (hW : MemLp (fun x : ℝ => (x : ℂ) ^ k * f x) 2)
    (hD : MemLp (iteratedDeriv k f) 2) : KNSGraphSpace k :=
  ofLp k hF.toLp
    (by
      apply (memLp_congr_ae ?_).mpr hW
      filter_upwards [hF.coeFn_toLp] with x hx
      rw [hx])
    (memLp_forward_power_of_top_classical_derivative k hf hF hD).choose

/-- The smooth adapter preserves the original actual L2 function exactly. -/
theorem physical_ofSmooth (k : ℕ) {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (hF : MemLp f 2)
    (hW : MemLp (fun x : ℝ => (x : ℂ) ^ k * f x) 2)
    (hD : MemLp (iteratedDeriv k f) 2) :
    physical k (ofSmooth k hf hF hW hD) = hF.toLp := rfl

/-- The smooth graph adapter retains the exact Fourier normalization in
the graph norm, rather than replacing the top derivative by an unrelated bound. -/
theorem norm_ofSmooth_sq (k : ℕ) {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (hF : MemLp f 2)
    (hW : MemLp (fun x : ℝ => (x : ℂ) ^ k * f x) 2)
    (hD : MemLp (iteratedDeriv k f) 2) :
    ‖ofSmooth k hf hF hW hD‖ ^ 2 = 2 * ‖hF.toLp‖ ^ 2 + ‖hW.toLp‖ ^ 2 +
      (((2 * Real.pi) ^ k)⁻¹ * ‖hD.toLp‖) ^ 2 := by
  have hp : physicalWeight k (ofSmooth k hf hF hW hD) = hW.toLp := by
    apply Lp.ext
    filter_upwards [physicalWeight_ae (ofSmooth k hf hF hW hD), hF.coeFn_toLp,
      hW.coeFn_toLp] with x hx hy hz
    rw [← hx, hz]
    change (x : ℂ) ^ k * (hF.toLp : KNSL2) x = _
    rw [hy]
  rw [norm_sq, physical_ofSmooth, hp]
  congr 1
  change ‖(memLp_forward_power_of_top_classical_derivative k hf hF hD).choose.toLp‖ ^ 2 = _
  rw [(memLp_forward_power_of_top_classical_derivative k hf hF hD).choose_spec]

/-- A convenient genuine graph bound for interpolation: unweighted mass
is retained, and the sharp Fourier factor is harmlessly bounded by one. -/
theorem norm_ofSmooth_sq_le (k : ℕ) {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (hF : MemLp f 2)
    (hW : MemLp (fun x : ℝ => (x : ℂ) ^ k * f x) 2)
    (hD : MemLp (iteratedDeriv k f) 2) :
    ‖ofSmooth k hf hF hW hD‖ ^ 2 ≤ 2 * ‖hF.toLp‖ ^ 2 + ‖hW.toLp‖ ^ 2 + ‖hD.toLp‖ ^ 2 := by
  rw [norm_ofSmooth_sq]
  have hpow : 1 ≤ (2 * Real.pi) ^ k := one_le_pow₀ (by linarith [Real.two_le_pi])
  have hi : ((2 * Real.pi) ^ k)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hpow
  have hp := mul_le_mul_of_nonneg_right hi (norm_nonneg hD.toLp)
  have hn : 0 ≤ ((2 * Real.pi) ^ k)⁻¹ * ‖hD.toLp‖ := by positivity
  nlinarith [norm_nonneg hD.toLp]

end KNSGraphSpace

end

end MeyerGeneralProblem
