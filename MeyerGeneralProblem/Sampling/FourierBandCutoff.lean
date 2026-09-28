module

public import MeyerGeneralProblem.Sampling.PaleyWienerRepresentative

@[expose] public section

/-!
# Actual Fourier band cutoffs and derivative tail estimates

Frequency indicators give an exact low/high decomposition. Outside the
closed band, multiplication by the Fourier derivative symbol gives the
sharp order-uniform tail estimate. These are actual functions and L2
classes, not assumed sampling or zero-set spectral-gap certificates.
-/

namespace MeyerGeneralProblem

noncomputable section

open MeasureTheory Set Filter
open scoped FourierTransform SchwartzMap Topology ContDiff

/-- The actual closed-band frequency cutoff. -/
def lowFrequencyBand (r : ℝ) (G : ℝ → ℂ) : ℝ → ℂ := (Icc (-r) r).indicator G

/-- The actual complementary frequency cutoff. -/
def highFrequencyBand (r : ℝ) (G : ℝ → ℂ) : ℝ → ℂ := (Icc (-r) r)ᶜ.indicator G

/-- Low and high frequency cutoffs recover the original data pointwise. -/
theorem lowFrequencyBand_add_highFrequencyBand (r : ℝ) (G : ℝ → ℂ) :
    lowFrequencyBand r G + highFrequencyBand r G = G := by
  ext t
  by_cases ht : t ∈ Icc (-r) r <;> simp [lowFrequencyBand, highFrequencyBand, ht]

/-- The low cutoff has genuine pointwise band support. -/
theorem support_lowFrequencyBand_subset (r : ℝ) (G : ℝ → ℂ) :
    Function.support (lowFrequencyBand r G) ⊆ Icc (-r) r := by
  intro t ht
  by_contra hnot
  exact ht (by simp [lowFrequencyBand, hnot])

/-- The multiplier producing the n-th derivative of the negative Fourier integral. -/
def fourierDerivativeData (n : ℕ) (G : ℝ → ℂ) (t : ℝ) : ℂ :=
  (-2 * (Real.pi : ℂ) * Complex.I * (t : ℂ))^n * G t

/-- The exact norm of the Fourier derivative multiplier. -/
theorem norm_fourierDerivativeData (n : ℕ) (G : ℝ → ℂ) (t : ℝ) :
    ‖fourierDerivativeData n G t‖ = (2 * Real.pi * |t|)^n * ‖G t‖ := by
  simp [fourierDerivativeData, norm_pow, abs_of_pos Real.pi_pos]

/-- Frequency truncation commutes with every derivative multiplier. -/
theorem fourierDerivativeData_highFrequencyBand (n : ℕ) (r : ℝ) (G : ℝ → ℂ) :
    fourierDerivativeData n (highFrequencyBand r G) =
      highFrequencyBand r (fourierDerivativeData n G) := by
  ext t
  by_cases ht : t ∈ Icc (-r) r <;> simp [fourierDerivativeData, highFrequencyBand, ht]

/-- The derivative tail comparison has constant exactly one, for all k≥j. -/
theorem norm_fourierDerivativeData_highFrequencyBand_le
    {r : ℝ} (hr : 0 < r) (G : ℝ → ℂ) {j k : ℕ} (hjk : j ≤ k) (t : ℝ) :
    ‖fourierDerivativeData j (highFrequencyBand r G) t‖ ≤
      ((2 * Real.pi * r)^(k-j))⁻¹ * ‖fourierDerivativeData k G t‖ := by
  by_cases ht : t ∈ Icc (-r) r
  · simp [fourierDerivativeData, highFrequencyBand, ht]
    positivity
  have hrt : r ≤ |t| := le_of_not_ge (by
    intro h
    exact ht (abs_le.mp h))
  have hbase : 0 < 2 * Real.pi * r := by positivity
  have hpow : (2 * Real.pi * r)^(k-j) * (2 * Real.pi * |t|)^j ≤
      (2 * Real.pi * |t|)^k := by
    calc
      _ ≤ (2 * Real.pi * |t|)^(k-j) * (2 * Real.pi * |t|)^j := by gcongr
      _ = _ := by rw [← pow_add, Nat.sub_add_cancel hjk]
  rw [norm_fourierDerivativeData, norm_fourierDerivativeData]
  simp only [highFrequencyBand, indicator_of_mem (show t ∈ (Icc (-r) r)ᶜ from ht)]
  rw [← div_eq_inv_mul]
  exact (le_div_iff₀ (pow_pos hbase _)).mpr (by
    nlinarith [mul_le_mul_of_nonneg_right hpow (norm_nonneg (G t))])

/-- The genuine high-frequency derivative data are L2 whenever the full
k-th derivative data are L2; its norm has the same sharp order factor. -/
theorem memLp_fourierDerivativeData_highFrequencyBand
    {r : ℝ} (hr : 0 < r) {G : ℝ → ℂ} (hG : AEStronglyMeasurable G volume)
    {j k : ℕ} (hjk : j ≤ k) (hK : MemLp (fourierDerivativeData k G) 2) :
    ∃ hJ : MemLp (fourierDerivativeData j (highFrequencyBand r G)) 2,
      ‖hJ.toLp‖ ≤ ((2 * Real.pi * r)^(k-j))⁻¹ * ‖hK.toLp‖ := by
  have hm : AEStronglyMeasurable (fourierDerivativeData j (highFrequencyBand r G)) volume :=
    (show Continuous (fun t : ℝ => (-2 * (Real.pi : ℂ) * Complex.I * (t : ℂ))^j) by
      fun_prop).aestronglyMeasurable.mul (hG.indicator measurableSet_Icc.compl)
  have hJ : MemLp (fourierDerivativeData j (highFrequencyBand r G)) 2 := hK.of_le_mul hm
    (Eventually.of_forall (norm_fourierDerivativeData_highFrequencyBand_le hr G hjk))
  refine ⟨hJ, ?_⟩
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [hJ.coeFn_toLp, hK.coeFn_toLp] with t hJt hKt
  rw [hJt, hKt]
  exact norm_fourierDerivativeData_highFrequencyBand_le hr G hjk t

/-- All real moments of actual Schwartz data are integrable. -/
theorem integrable_real_moment_schwartz (G : SchwartzMap ℝ ℂ) (n : ℕ) :
    Integrable (fun t : ℝ => t^n • G t) := by
  apply (G.integrable_pow_mul volume n).mono (by fun_prop)
  filter_upwards [] with t
  simp [norm_pow, norm_mul]

/-- Every Fourier derivative datum of a Schwartz function is itself a
genuine Schwartz function; in particular, it belongs to L2. -/
theorem memLp_fourierDerivativeData_schwartz (G : SchwartzMap ℝ ℂ) (n : ℕ) :
    MemLp (fourierDerivativeData n G) 2 := by
  let M := SchwartzMap.smulLeftCLM ℂ
    (fun t : ℝ => (-2 * (Real.pi : ℂ) * Complex.I * (t : ℂ))^n) G
  have htemp : Function.HasTemperateGrowth
      (fun t : ℝ => (-2 * (Real.pi : ℂ) * Complex.I * (t : ℂ))^n) := by fun_prop
  have hM : (M : ℝ → ℂ) = fourierDerivativeData n G := by
    ext t
    exact SchwartzMap.smulLeftCLM_apply_apply htemp G t
  rw [← hM]
  exact M.memLp 2

/-- Integrable real moments give integrable exact Fourier derivative data. -/
theorem integrable_fourierDerivativeData_of_moment {G : ℝ → ℂ} (n : ℕ)
    (h : Integrable (fun t : ℝ => t^n • G t)) :
    Integrable (fourierDerivativeData n G) := by
  convert h.const_mul ((-2 * (Real.pi : ℂ) * Complex.I)^n) using 1
  ext t
  change ((-2 * (Real.pi : ℂ) * Complex.I) * (t : ℂ))^n * G t =
    (-2 * (Real.pi : ℂ) * Complex.I)^n * (t^n • G t)
  rw [mul_pow, Complex.real_smul, Complex.ofReal_pow, mul_assoc]

/-- All-order moment integrability gives the actual derivative Fourier formula. -/
theorem iteratedDeriv_fourier_of_integrable_moments {G : ℝ → ℂ}
    (hG : ∀ n : ℕ, Integrable (fun t : ℝ => t^n • G t)) (n : ℕ) :
    iteratedDeriv n (𝓕 G) = (𝓕 (fourierDerivativeData n G) : ℝ → ℂ) := by
  change iteratedDeriv n (𝓕 G) =
    𝓕 (fun t : ℝ => (-2 * (Real.pi : ℂ) * Complex.I * (t : ℂ))^n * G t)
  simpa only [smul_eq_mul] using
    Real.iteratedDeriv_fourier (N := ⊤) (fun j _ => hG j) le_top

/-- Plancherel identifies every actual derivative norm with its frequency
multiplier norm, with only integrability and L2 data hypotheses. -/
theorem memLp_iteratedDeriv_fourier_of_integrable_moments {G : ℝ → ℂ}
    (hG : ∀ n : ℕ, Integrable (fun t : ℝ => t^n • G t))
    (n : ℕ) (hM : MemLp (fourierDerivativeData n G) 2) :
    ∃ hD : MemLp (iteratedDeriv n (𝓕 G)) 2, ‖hD.toLp‖ = ‖hM.toLp‖ := by
  have hae : iteratedDeriv n (𝓕 G) =ᵐ[volume] (𝓕 hM.toLp : Lp ℂ 2 volume) := by
    rw [iteratedDeriv_fourier_of_integrable_moments hG n]
    exact fourierIntegral_ae_eq_L2 (integrable_fourierDerivativeData_of_moment n (hG n)) hM
  have hD : MemLp (iteratedDeriv n (𝓕 G)) 2 := (memLp_congr_ae hae).mpr (Lp.memLp _)
  refine ⟨hD, ?_⟩
  have hc : hD.toLp = (𝓕 hM.toLp : Lp ℂ 2 volume) := Lp.ext (hD.coeFn_toLp.trans hae)
  rw [hc, Lp.norm_fourier_eq]

/-- The actual high-frequency cutoff retains every integrable moment. -/
theorem integrable_real_moment_highFrequencyBand {G : ℝ → ℂ}
    (r : ℝ) (n : ℕ) (h : Integrable (fun t : ℝ => t^n • G t)) :
    Integrable (fun t : ℝ => t^n • highFrequencyBand r G t) := by
  have he : (fun t : ℝ => t^n • highFrequencyBand r G t) =
      (Icc (-r) r)ᶜ.indicator (fun t : ℝ => t^n • G t) := by
    ext t
    by_cases ht : t ∈ Icc (-r) r <;> simp [highFrequencyBand, ht]
  rw [he]
  exact h.indicator measurableSet_Icc.compl

/-- Integrable moments of every order give an actually smooth Fourier integral. -/
theorem contDiff_fourier_of_integrable_moments {G : ℝ → ℂ}
    (hG : ∀ n : ℕ, Integrable (fun t : ℝ => t^n • G t)) :
    ContDiff ℝ ∞ (𝓕 G) := by
  apply Real.contDiff_fourier
  intro n _hn
  convert (hG n).norm using 1
  ext t
  simp [norm_pow]

/-- The actual high-pass Fourier integral of Schwartz data is smooth,
although its sharply truncated frequency function need not be smooth. -/
theorem contDiff_fourier_highFrequencyBand (G : SchwartzMap ℝ ℂ) (r : ℝ) :
    ContDiff ℝ ∞ (𝓕 (highFrequencyBand r G)) :=
  contDiff_fourier_of_integrable_moments (fun n =>
    integrable_real_moment_highFrequencyBand r n (integrable_real_moment_schwartz G n))

/-- Low and high actual Fourier integrals add pointwise, not merely as L2 classes. -/
theorem fourier_lowFrequencyBand_add_highFrequencyBand {G : ℝ → ℂ}
    (hG : Integrable G) (r : ℝ) :
    (𝓕 (lowFrequencyBand r G) : ℝ → ℂ) + 𝓕 (highFrequencyBand r G) = 𝓕 G := by
  have h := VectorFourier.fourierIntegral_add
    (f := lowFrequencyBand r G) (g := highFrequencyBand r G) Real.continuous_fourierChar
    (innerSL ℝ).continuous₂ (hG.indicator measurableSet_Icc)
      (hG.indicator measurableSet_Icc.compl)
  change (𝓕 (lowFrequencyBand r G + highFrequencyBand r G) : ℝ → ℂ) = _ at h
  rw [lowFrequencyBand_add_highFrequencyBand] at h
  exact h.symm

/-- Genuine sharp high-pass derivative decay for Schwartz data. The
constant one is uniform in k and j; only the bandwidth power changes. -/
theorem exists_highFrequencyBand_fourier_derivative_bound
    (G : SchwartzMap ℝ ℂ) {r : ℝ} (hr : 0 < r) {j k : ℕ} (hjk : j ≤ k) :
    ∃ hJ : MemLp (iteratedDeriv j (𝓕 (highFrequencyBand r G))) 2,
      ∃ hK : MemLp (iteratedDeriv k (𝓕 (G : ℝ → ℂ))) 2,
        ‖hJ.toLp‖ ≤ ((2 * Real.pi * r)^(k-j))⁻¹ * ‖hK.toLp‖ := by
  have hM := memLp_fourierDerivativeData_schwartz G k
  obtain ⟨hT, hbound⟩ := memLp_fourierDerivativeData_highFrequencyBand hr
    G.continuous.aestronglyMeasurable hjk hM
  obtain ⟨hJ, hJnorm⟩ := memLp_iteratedDeriv_fourier_of_integrable_moments
    (fun n => integrable_real_moment_highFrequencyBand r n (integrable_real_moment_schwartz G n)) j hT
  obtain ⟨hK, hKnorm⟩ := memLp_iteratedDeriv_fourier_of_integrable_moments
    (integrable_real_moment_schwartz G) k hM
  exact ⟨hJ, hK, by rw [hJnorm, hKnorm]; exact hbound⟩

end

end MeyerGeneralProblem
