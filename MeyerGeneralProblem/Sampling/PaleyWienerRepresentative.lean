module

public import MeyerGeneralProblem.Sampling.BernsteinLocalizer
public import Mathlib.Analysis.Fourier.LpSpace
import all Mathlib.Analysis.Fourier.LpSpace

@[expose] public section

/-!
# Actual integral representatives for band-limited L2 functions

The Fourier integral of an integrable L2 function agrees almost everywhere
with its Hilbert-space Fourier transform. Compact frequency support then
gives a genuine entire representative with the exact angular type.
-/

namespace MeyerGeneralProblem

noncomputable section

open MeasureTheory Set Filter
open scoped Topology FourierTransform SchwartzMap ContDiff

/-- The classical Fourier integral and the L2 Fourier isometry agree on
their actual common domain. The proof uses Schwartz test functions and
the already proved distributional Fourier compatibility. -/
theorem fourierIntegral_ae_eq_L2 {G : ℝ → ℂ} (hG : Integrable G)
    (hG2 : MemLp G 2) :
    (𝓕 G : ℝ → ℂ) =ᵐ[volume] (𝓕 hG2.toLp : Lp ℂ 2 volume) := by
  have hc : Continuous (𝓕 G : ℝ → ℂ) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hG
  apply ae_eq_of_integral_contDiff_smul_eq hc.locallyIntegrable
    ((Lp.memLp (𝓕 hG2.toLp)).locallyIntegrable (by norm_num))
  intro g hg hgc
  let φ : SchwartzMap ℝ ℂ :=
    (hgc.comp_left (show Complex.ofRealCLM 0 = 0 from rfl)).toSchwartzMap
      (show ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) by fun_prop)
  have hφ (x : ℝ) : φ x = (g x : ℂ) := rfl
  have hswap : (∫ x, φ x * (𝓕 G) x) = ∫ x, (𝓕 φ) x * G x := by
    simpa using! (VectorFourier.integral_bilin_fourierIntegral_eq_flip
      (ContinuousLinearMap.mul ℂ ℂ) (L := innerₗ ℝ)
      Real.continuous_fourierChar continuous_inner φ.integrable hG).symm
  have hdist := congrArg (fun T : TemperedDistribution ℝ ℂ => T φ)
    (Lp.fourier_toTemperedDistribution_eq hG2.toLp)
  simp only [Lp.toTemperedDistribution_apply, TemperedDistribution.fourier_apply,
    smul_eq_mul] at hdist
  calc
    _ = ∫ x, φ x * (𝓕 G) x := by simp only [hφ, Complex.real_smul]
    _ = ∫ x, (𝓕 φ) x * G x := hswap
    _ = ∫ x, (𝓕 φ) x * (hG2.toLp : Lp ℂ 2 volume) x := by
      apply integral_congr_ae
      filter_upwards [hG2.coeFn_toLp] with x hx
      rw [hx]
    _ = ∫ x, φ x * (𝓕 hG2.toLp : Lp ℂ 2 volume) x := hdist
    _ = _ := by simp only [hφ, Complex.real_smul]

/-- The actual complex Fourier integral for arbitrary frequency data. -/
def bandFourierExtension (G : ℝ → ℂ) (z : ℂ) : ℂ :=
  ∫ t : ℝ, Complex.exp (((-2 * Real.pi * t : ℝ) : ℂ) * Complex.I * z) * G t

private theorem bandFourierPhase_bound {r t : ℝ} (ht : |t| ≤ r) (z : ℂ) :
    ‖Complex.exp (((-2 * Real.pi * t : ℝ) : ℂ) * Complex.I * z)‖ ≤
      Real.exp (2 * Real.pi * r * ‖z‖) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ ‖(((-2 * Real.pi * t : ℝ) : ℂ) * Complex.I * z)‖ := Complex.re_le_norm _
    _ = 2 * Real.pi * |t| * ‖z‖ := by simp [abs_of_pos Real.pi_pos]
    _ ≤ _ := by gcongr

private theorem integrable_bandFourierExtension_integrand
    {G : ℝ → ℂ} (hG : Integrable G) {r : ℝ}
    (hs : Function.support G ⊆ Icc (-r) r) (z : ℂ) :
    Integrable (fun t : ℝ =>
      Complex.exp (((-2 * Real.pi * t : ℝ) : ℂ) * Complex.I * z) * G t) := by
  apply (hG.norm.const_mul (Real.exp (2 * Real.pi * r * ‖z‖))).mono
    ((show Continuous (fun t : ℝ =>
      Complex.exp (((-2 * Real.pi * t : ℝ) : ℂ) * Complex.I * z)) by
        fun_prop).aestronglyMeasurable.mul hG.aestronglyMeasurable)
  filter_upwards [] with t
  simp only [Pi.mul_apply, norm_mul, norm_norm, Real.norm_of_nonneg (Real.exp_pos _).le]
  by_cases ht : G t = 0
  · simp [ht]
  · exact mul_le_mul_of_nonneg_right (bandFourierPhase_bound (abs_le.mpr (hs ht)) z)
      (norm_nonneg (G t))

/-- The actual L1 mass bounds the entire integral at the sharp radial type
given by its compact frequency radius. -/
theorem norm_bandFourierExtension_le {G : ℝ → ℂ} (hG : Integrable G)
    {r : ℝ} (hs : Function.support G ⊆ Icc (-r) r) (z : ℂ) :
    ‖bandFourierExtension G z‖ ≤
      (∫ t : ℝ, ‖G t‖) * Real.exp (2 * Real.pi * r * ‖z‖) := by
  unfold bandFourierExtension
  calc
    _ ≤ ∫ t : ℝ, ‖Complex.exp (((-2 * Real.pi * t : ℝ) : ℂ) *
        Complex.I * z) * G t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ, Real.exp (2 * Real.pi * r * ‖z‖) * ‖G t‖ := by
      apply integral_mono (integrable_bandFourierExtension_integrand hG hs z).norm
        (hG.norm.const_mul _)
      intro t
      dsimp only
      rw [norm_mul]
      by_cases ht : G t = 0
      · simp [ht]
      · exact mul_le_mul_of_nonneg_right (bandFourierPhase_bound (abs_le.mpr (hs ht)) z)
          (norm_nonneg _)
    _ = _ := by rw [integral_const_mul, mul_comm]

/-- Compactly supported L1 data have a genuinely entire Fourier integral;
frequency smoothness is not required. -/
theorem differentiable_bandFourierExtension {G : ℝ → ℂ} (hG : Integrable G)
    {r : ℝ} (hr : 0 ≤ r) (hs : Function.support G ⊆ Icc (-r) r) :
    Differentiable ℂ (bandFourierExtension G) := by
  intro z
  let a : ℝ → ℂ := fun t => ((-2 * Real.pi * t : ℝ) : ℂ) * Complex.I
  let F : ℂ → ℝ → ℂ := fun w t => Complex.exp (a t * w) * G t
  let F' : ℂ → ℝ → ℂ := fun w t => (Complex.exp (a t * w) * a t) * G t
  let B := 2 * Real.pi * r * Real.exp (2 * Real.pi * r * (‖z‖ + 1))
  have hFm (w : ℂ) : AEStronglyMeasurable (F w) volume :=
    (show Continuous (fun t : ℝ => Complex.exp (a t * w)) by dsimp [a]; fun_prop
      ).aestronglyMeasurable.mul hG.aestronglyMeasurable
  have hF'm (w : ℂ) : AEStronglyMeasurable (F' w) volume :=
    (show Continuous (fun t : ℝ => Complex.exp (a t * w) * a t) by dsimp [a]; fun_prop
      ).aestronglyMeasurable.mul hG.aestronglyMeasurable
  have hdiff : ∀ t w, HasDerivAt (fun u => F u t) (F' w t) w := by
    intro t w
    simpa only [F, F', mul_one, id_eq] using
      (((hasDerivAt_id w).const_mul (a t)).cexp.mul_const (G t))
  have hbound : ∀ᵐ t : ℝ, ∀ w ∈ Metric.ball z 1, ‖F' w t‖ ≤ B * ‖G t‖ := by
    filter_upwards [] with t w hw
    by_cases ht : G t = 0
    · simp [F', ht]
    have ht' : |t| ≤ r := abs_le.mpr (hs ht)
    have hw' : ‖w‖ ≤ ‖z‖ + 1 := by
      have htriangle := norm_le_norm_sub_add w z
      have hball : ‖w - z‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using hw
      linarith
    have ha : ‖a t‖ ≤ 2 * Real.pi * r := by
      dsimp [a]
      norm_num [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
      gcongr
    have he := bandFourierPhase_bound ht' w
    change ‖Complex.exp (a t * w)‖ ≤ _ at he
    have he' : ‖Complex.exp (a t * w)‖ ≤
        Real.exp (2 * Real.pi * r * (‖z‖ + 1)) := he.trans (by gcongr)
    simp only [F', norm_mul]
    calc
      _ ≤ (Real.exp (2 * Real.pi * r * (‖z‖ + 1)) * (2 * Real.pi * r)) * ‖G t‖ := by gcongr
      _ = _ := by dsimp [B]; ring
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := fun t => B * ‖G t‖)
    (Metric.ball_mem_nhds z zero_lt_one) (Eventually.of_forall hFm)
    (integrable_bandFourierExtension_integrand hG hs z) (hF'm z)
    hbound (hG.norm.const_mul B) (Eventually.of_forall fun t w _ => hdiff t w)
  exact h.2.differentiableAt

/-- Real values of the entire extension are exactly the classical Fourier
integral, with the repository's negative-frequency convention. -/
theorem bandFourierExtension_ofReal (G : ℝ → ℂ) (x : ℝ) :
    bandFourierExtension G (x : ℂ) = (𝓕 G) x := by
  rw [bandFourierExtension, Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [smul_eq_mul]
  congr 2
  push_cast
  ring

/-- Finite frequency bandwidth turns genuine L2 data into integrable data. -/
theorem integrable_of_memLp_two_band {G : ℝ → ℂ} (hG : MemLp G 2)
    {r : ℝ} (hs : Function.support G ⊆ Icc (-r) r) : Integrable G := by
  apply (integrableOn_iff_integrable_of_support_subset hs).mp
  exact (hG.mono_measure Measure.restrict_le_self).integrable (by norm_num)

/-- A genuine band-limited L2 frequency function has a bounded entire
representative of its Hilbert Fourier transform, with exact Plancherel norm.
The frequency input need not be continuous or Schwartz. -/
theorem exists_bandLimited_L2_entire_representative
    {G : ℝ → ℂ} (hG2 : MemLp G 2) {r : ℝ} (hr : 0 ≤ r)
    (hs : Function.support G ⊆ Icc (-r) r) :
    ∃ E : ℂ → ℂ, Differentiable ℂ E ∧
      (∀ t : ℝ, E (t : ℂ) = (𝓕 G) t) ∧
      BddAbove (Set.range (fun t : ℝ => ‖E (t : ℂ)‖)) ∧
      (∀ ε > 0, ∃ C > 0, ∀ z : ℂ,
        ‖E z‖ ≤ C * Real.exp ((2 * Real.pi * r + ε) * ‖z‖)) ∧
      ((fun t : ℝ => E (t : ℂ)) =ᵐ[volume] (𝓕 hG2.toLp : Lp ℂ 2 volume)) ∧
      ∃ hE : MemLp (fun t : ℝ => E (t : ℂ)) 2,
        ‖hE.toLp‖ = ‖hG2.toLp‖ := by
  have hG := integrable_of_memLp_two_band hG2 hs
  let E := bandFourierExtension G
  have he (t : ℝ) : E (t : ℂ) = (𝓕 G) t := bandFourierExtension_ofReal G t
  have heae : (fun t : ℝ => E (t : ℂ)) =ᵐ[volume] (𝓕 hG2.toLp : Lp ℂ 2 volume) := by
    simpa only [he] using fourierIntegral_ae_eq_L2 hG hG2
  have hE : MemLp (fun t : ℝ => E (t : ℂ)) 2 :=
    (memLp_congr_ae heae).mpr (Lp.memLp _)
  refine ⟨E, differentiable_bandFourierExtension hG hr hs, he, ?_, ?_, heae, hE, ?_⟩
  · refine ⟨∫ t : ℝ, ‖G t‖, ?_⟩
    rintro _ ⟨t, rfl⟩
    dsimp only
    rw [he, Real.fourier_eq]
    apply (norm_integral_le_integral_norm _).trans
    simp only [Circle.norm_smul, le_refl]
  · intro ε hε
    let C := 1 + ∫ t : ℝ, ‖G t‖
    have hmass : 0 ≤ ∫ t : ℝ, ‖G t‖ := integral_nonneg (fun _ => norm_nonneg _)
    refine ⟨C, by dsimp [C]; linarith, ?_⟩
    intro z
    apply (norm_bandFourierExtension_le hG hs z).trans
    apply mul_le_mul
    · dsimp [C]; linarith
    · apply Real.exp_le_exp.mpr
      nlinarith [norm_nonneg z]
    · positivity
    · dsimp [C]; linarith
  · have hEq : hE.toLp = (𝓕 hG2.toLp : Lp ℂ 2 volume) := by
      apply Lp.ext
      exact hE.coeFn_toLp.trans heae
    rw [hEq, Lp.norm_fourier_eq]

/-- Every actual L2 class with almost-everywhere compact frequency support
has a bounded entire representative of its Fourier transform. The angular
bandwidth, almost-everywhere equality and Plancherel norm are exact. -/
theorem exists_L2_fourier_entire_representative
    (g : Lp ℂ 2 (volume : Measure ℝ)) {Ω : ℝ} (hΩ : 0 ≤ Ω)
    (hs : ∀ᵐ t : ℝ, t ∉ Icc (-Ω / (2 * Real.pi)) (Ω / (2 * Real.pi)) → g t = 0) :
    ∃ E : ℂ → ℂ, Differentiable ℂ E ∧
      BddAbove (Set.range (fun t : ℝ => ‖E (t : ℂ)‖)) ∧
      (∀ ε > 0, ∃ C > 0, ∀ z : ℂ,
        ‖E z‖ ≤ C * Real.exp ((Ω + ε) * ‖z‖)) ∧
      ((fun t : ℝ => E (t : ℂ)) =ᵐ[volume] (𝓕 g : Lp ℂ 2 volume)) ∧
      ∃ hE : MemLp (fun t : ℝ => E (t : ℂ)) 2, ‖hE.toLp‖ = ‖g‖ := by
  classical
  let r := Ω / (2 * Real.pi)
  have hr : 0 ≤ r := by dsimp [r]; positivity
  let G : ℝ → ℂ := (Icc (-r) r).indicator (g : ℝ → ℂ)
  have hG2 : MemLp G 2 := (Lp.memLp g).indicator measurableSet_Icc
  have hGs : Function.support G ⊆ Icc (-r) r := by
    intro t ht
    by_contra hnot
    exact ht (indicator_of_notMem hnot _)
  have hGeq : G =ᵐ[volume] (g : ℝ → ℂ) := by
    filter_upwards [hs] with t ht
    dsimp [G]
    by_cases hmem : t ∈ Icc (-r) r
    · simp only [indicator_of_mem hmem]
    · rw [indicator_of_notMem hmem]
      exact (ht (by simpa only [r, neg_div] using hmem)).symm
  have hGclass : hG2.toLp = g := by
    apply Lp.ext
    exact hG2.coeFn_toLp.trans hGeq
  obtain ⟨E, hE, _hreal, hb, ht, hae, heL2⟩ :=
    exists_bandLimited_L2_entire_representative hG2 hr hGs
  have hscale : 2 * Real.pi * r = Ω := by dsimp [r]; field_simp
  rw [hGclass] at hae heL2
  rw [hscale] at ht
  exact ⟨E, hE, hb, ht, hae, heL2⟩

/-- Multiplication by a real monomial preserves integrability on a bounded
frequency band, with no smoothness requirement on the data. -/
theorem integrable_real_moment_of_band {G : ℝ → ℂ} (hG : Integrable G)
    {r : ℝ} (hr : 0 ≤ r) (hs : Function.support G ⊆ Icc (-r) r) (n : ℕ) :
    Integrable (fun t : ℝ => t^n • G t) := by
  apply (hG.norm.const_mul (r^n)).mono
    ((continuous_id.pow n).aestronglyMeasurable.smul hG.aestronglyMeasurable)
  filter_upwards [] with t
  change ‖t^n • G t‖ ≤ ‖r^n * ‖G t‖‖
  simp only [norm_smul, norm_pow, norm_mul,
    Real.norm_of_nonneg hr, Real.norm_eq_abs, abs_norm]
  by_cases ht : G t = 0
  · simp [ht]
  · exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (abs_nonneg t) (abs_le.mpr (hs ht)) n) (norm_nonneg (G t))

/-- Exact real derivatives of the actual band-limited Fourier integral. -/
theorem iteratedDeriv_fourier_of_band {G : ℝ → ℂ} (hG : Integrable G)
    {r : ℝ} (hr : 0 ≤ r) (hs : Function.support G ⊆ Icc (-r) r) (n : ℕ) :
    iteratedDeriv n (𝓕 G) =
      𝓕 (fun t : ℝ => (-2 * (Real.pi : ℂ) * Complex.I * (t : ℂ))^n * G t) := by
  simpa only [smul_eq_mul] using Real.iteratedDeriv_fourier
    (N := (n : ℕ∞)) (fun k _hk => integrable_real_moment_of_band hG hr hs k) le_rfl

/-- Exact frequency derivative multipliers are bounded by the angular
bandwidth to the same derivative order. -/
theorem norm_band_frequency_derivative_le {G : ℝ → ℂ} {r : ℝ} (_hr : 0 ≤ r)
    (hs : Function.support G ⊆ Icc (-r) r) (n : ℕ) (t : ℝ) :
    ‖(-2 * (Real.pi : ℂ) * Complex.I * (t : ℂ))^n * G t‖ ≤
      (2 * Real.pi * r)^n * ‖G t‖ := by
  by_cases ht : G t = 0
  · simp [ht]
  have ht' : |t| ≤ r := abs_le.mpr (hs ht)
  simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_I, mul_one, norm_neg, Complex.norm_ofNat, abs_of_pos Real.pi_pos]
  gcongr

/-- Every derivative of a genuine band-limited L2 Fourier integral is L2
and obeys the exact Bernstein derivative bound. -/
theorem memLp_iteratedDeriv_fourier_of_band
    {G : ℝ → ℂ} (hG2 : MemLp G 2) {r : ℝ} (hr : 0 ≤ r)
    (hs : Function.support G ⊆ Icc (-r) r) (n : ℕ) :
    ∃ hD : MemLp (iteratedDeriv n (𝓕 G)) 2,
      ‖hD.toLp‖ ≤ (2 * Real.pi * r)^n * ‖hG2.toLp‖ := by
  let M : ℝ → ℂ := fun t => (-2 * (Real.pi : ℂ) * Complex.I * (t : ℂ))^n * G t
  have hpoint (t : ℝ) : ‖M t‖ ≤ (2 * Real.pi * r)^n * ‖G t‖ :=
    norm_band_frequency_derivative_le hr hs n t
  have hM : MemLp M 2 := hG2.of_le_mul
    ((show Continuous (fun t : ℝ => (-2 * (Real.pi : ℂ) * Complex.I * (t : ℂ))^n) by
      fun_prop).aestronglyMeasurable.mul hG2.aestronglyMeasurable)
    (Eventually.of_forall hpoint)
  have hMs : Function.support M ⊆ Icc (-r) r := by
    intro t ht
    apply hs
    intro hz
    exact ht (by simp [M, hz])
  have heq : iteratedDeriv n (𝓕 G) = (𝓕 M : ℝ → ℂ) :=
    iteratedDeriv_fourier_of_band (integrable_of_memLp_two_band hG2 hs) hr hs n
  have hae : iteratedDeriv n (𝓕 G) =ᵐ[volume] (𝓕 hM.toLp : Lp ℂ 2 volume) := by
    rw [heq]
    exact fourierIntegral_ae_eq_L2 (integrable_of_memLp_two_band hM hMs) hM
  have hD : MemLp (iteratedDeriv n (𝓕 G)) 2 := (memLp_congr_ae hae).mpr (Lp.memLp _)
  refine ⟨hD, ?_⟩
  have hclass : hD.toLp = (𝓕 hM.toLp : Lp ℂ 2 volume) :=
    Lp.ext (hD.coeFn_toLp.trans hae)
  rw [hclass, Lp.norm_fourier_eq]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [hM.coeFn_toLp, hG2.coeFn_toLp] with t hmt hgt
  rw [hmt, hgt]
  exact hpoint t

end

end MeyerGeneralProblem
