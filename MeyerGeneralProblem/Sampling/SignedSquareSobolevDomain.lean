module

public import MeyerGeneralProblem.Sampling.SignedSquareCutoffTransfer
public import MeyerGeneralProblem.Sampling.ClassicalFourierSobolev
public import MeyerGeneralProblem.Distribution.CompactSchwartzDensity

@[expose] public section

/-!
# Genuine Sobolev domains for localized signed-square charts

Compact-test integration by parts identifies the top distributional
derivative from the actual function and its actual top derivative in L2.
Intermediate L2 derivatives are conclusions, not domain certificates.
-/

namespace MeyerGeneralProblem

noncomputable section

open MeasureTheory Set Filter LineDeriv
open scoped Topology FourierTransform SchwartzMap ContDiff

private theorem sobolev_contDiff_iteratedDeriv {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (j : ℕ) : ContDiff ℝ ∞ (iteratedDeriv j f) := by
  induction j with
  | zero => simpa using hf
  | succ j ih =>
    rw [iteratedDeriv_succ]
    exact (show ContDiff ℝ (∞ + 1) (iteratedDeriv j f) by simpa using ih).deriv'

private theorem compact_test_integration_by_parts (φ : SchwartzMap ℝ ℂ)
    (hφ : HasCompactSupport (φ : ℝ → ℂ)) {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (k : ℕ) :
    (∫ x : ℝ, φ x * iteratedDeriv k f x) =
      (-1 : ℂ) ^ k * (∫ x : ℝ, iteratedDeriv k φ x * f x) := by
  induction k generalizing φ with
  | zero => simp
  | succ k ih =>
    let ψ := SchwartzMap.derivCLM ℂ ℂ φ
    have hψ : HasCompactSupport (ψ : ℝ → ℂ) := hφ.deriv
    have hc := sobolev_contDiff_iteratedDeriv hf k
    have hcd := sobolev_contDiff_iteratedDeriv hf (k + 1)
    have hparts := integral_mul_deriv_eq_deriv_mul_of_integrable
      (u := (φ : ℝ → ℂ)) (u' := deriv φ)
      (v := iteratedDeriv k f) (v' := iteratedDeriv (k + 1) f)
      (fun x _ => φ.hasDerivAt x)
      (fun x _ => by rw [iteratedDeriv_succ]; exact (hc.differentiable (by simp) x).hasDerivAt)
      ((φ.continuous.mul hcd.continuous).integrable_of_hasCompactSupport hφ.mul_right)
      ((ψ.continuous.mul hc.continuous).integrable_of_hasCompactSupport hψ.mul_right)
      ((φ.continuous.mul hc.continuous).integrable_of_hasCompactSupport hφ.mul_right)
    rw [hparts]
    change -(∫ x : ℝ, ψ x * iteratedDeriv k f x) = _
    rw [ih ψ hψ, pow_succ, iteratedDeriv_succ']
    change -((-1 : ℂ) ^ k * ∫ x : ℝ, iteratedDeriv k (deriv φ) x * f x) = _
    ring

private theorem lineDeriv_one_schwartz_eq (φ : SchwartzMap ℝ ℂ) :
    lineDerivOp (1 : ℝ) φ = SchwartzMap.derivCLM ℂ ℂ φ := by
  ext x
  simp [SchwartzMap.lineDerivOp_apply_eq_fderiv]

private theorem schwartz_deriv_iterate_apply (k : ℕ) (φ : SchwartzMap ℝ ℂ) (x : ℝ) :
    (((SchwartzMap.derivCLM ℂ ℂ)^[k]) φ) x = iteratedDeriv k φ x := by
  induction k generalizing φ with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih, iteratedDeriv_succ']
    rfl

private theorem distribution_iterated_deriv_apply (k : ℕ)
    (T : TemperedDistribution ℝ ℂ) (φ : SchwartzMap ℝ ℂ) :
    (((lineDerivOp (1 : ℝ))^[k]) T) φ =
      (-1 : ℂ) ^ k * T (((SchwartzMap.derivCLM ℂ ℂ)^[k]) φ) := by
  induction k generalizing φ with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', TemperedDistribution.lineDerivOp_apply_apply,
      lineDeriv_one_schwartz_eq, map_neg, ih, Function.iterate_succ_apply, pow_succ]
    ring

private theorem tempered_eq_of_compact_tests (T U : TemperedDistribution ℝ ℂ)
    (h : ∀ φ : SchwartzMap ℝ ℂ, HasCompactSupport (φ : ℝ → ℂ) → T φ = U φ) : T = U := by
  ext φ
  have heq (N : ℕ) : T (compactSchwartzApproximation N φ) = U (compactSchwartzApproximation N φ) :=
    h _ (compactSchwartzApproximation_hasCompactSupport N φ)
  have hT : Tendsto (fun N => T (compactSchwartzApproximation N φ)) atTop (𝓝 (T φ)) :=
    (T.continuous.tendsto φ).comp (compactSchwartzApproximation_tendsto φ)
  have hU : Tendsto (fun N => U (compactSchwartzApproximation N φ)) atTop (𝓝 (U φ)) :=
    (U.continuous.tendsto φ).comp (compactSchwartzApproximation_tendsto φ)
  rw [show (fun N => T (compactSchwartzApproximation N φ)) =
    (fun N => U (compactSchwartzApproximation N φ)) from funext heq] at hT
  exact tendsto_nhds_unique hT hU

/-- The actual top classical derivative in L2 is the top distributional
derivative, without any assumption on intermediate global L2 derivatives. -/
theorem iteratedLineDeriv_L2_of_top_classical_derivative {f : ℝ → ℂ} (k : ℕ)
    (hf : ContDiff ℝ ∞ f) (hF : MemLp f 2) (hK : MemLp (iteratedDeriv k f) 2) :
    ((lineDerivOp (1 : ℝ))^[k]) (hF.toLp : TemperedDistribution ℝ ℂ) =
      (hK.toLp : TemperedDistribution ℝ ℂ) := by
  apply tempered_eq_of_compact_tests
  intro φ hφ
  rw [distribution_iterated_deriv_apply]
  have hleft : (hF.toLp : TemperedDistribution ℝ ℂ)
      (((SchwartzMap.derivCLM ℂ ℂ)^[k]) φ) = ∫ x : ℝ, iteratedDeriv k φ x * f x := by
    rw [Lp.toTemperedDistribution_apply]
    apply integral_congr_ae
    filter_upwards [hF.coeFn_toLp] with x hx
    simp only [schwartz_deriv_iterate_apply, hx, smul_eq_mul]
  have hright : (hK.toLp : TemperedDistribution ℝ ℂ) φ =
      ∫ x : ℝ, φ x * iteratedDeriv k f x := by
    rw [Lp.toTemperedDistribution_apply]
    apply integral_congr_ae
    filter_upwards [hK.coeFn_toLp] with x hx
    simp only [hx, smul_eq_mul]
  rw [hleft, hright]
  exact (compact_test_integration_by_parts φ hφ hf k).symm

private theorem inverseFourier_lineDeriv_multiplier (T : TemperedDistribution ℝ ℂ) :
    𝓕⁻ (lineDerivOp (1 : ℝ) T) = TemperedDistribution.smulLeftCLM ℂ
      (fun t : ℝ => -2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) (𝓕⁻ T) := by
  rw [TemperedDistribution.fourierInv_lineDerivOp_eq]
  simp only [Real.inner_apply, mul_one]
  have hg : (fun t : ℝ => (t : ℂ)).HasTemperateGrowth := by fun_prop
  change (-(2 * (Real.pi : ℂ) * Complex.I)) •
    (TemperedDistribution.smulLeftCLM ℂ (fun t : ℝ => (t : ℂ)) (𝓕⁻ T)) = _
  rw [← smul_apply, ← TemperedDistribution.smulLeftCLM_smul hg]
  have hm : (-(2 * (Real.pi : ℂ) * Complex.I) • (fun t : ℝ => (t : ℂ))) =
      (fun t : ℝ => -2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) := by
    funext t
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [hm]

private theorem inverseFourier_iteratedLineDeriv_multiplier (k : ℕ)
    (T : TemperedDistribution ℝ ℂ) :
    𝓕⁻ (((lineDerivOp (1 : ℝ))^[k]) T) = TemperedDistribution.smulLeftCLM ℂ
      (fun t : ℝ => (-2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) ^ k) (𝓕⁻ T) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', inverseFourier_lineDeriv_multiplier, ih,
      TemperedDistribution.smulLeftCLM_smulLeftCLM_apply (by fun_prop) (by fun_prop)]
    congr 1

/-- Fourier identifies the actual top classical derivative using only
the zeroth and top L2 assumptions. No intermediate domain is postulated. -/
theorem inverseFourier_top_classical_derivative_ae {f : ℝ → ℂ} (k : ℕ)
    (hf : ContDiff ℝ ∞ f) (hF : MemLp f 2) (hK : MemLp (iteratedDeriv k f) 2) :
    fourierDerivativeData k ((𝓕⁻ hF.toLp : Lp ℂ 2 volume) : ℝ → ℂ) =ᵐ[volume]
      (𝓕⁻ hK.toLp : Lp ℂ 2 volume) := by
  have hd := congrArg (fun T : TemperedDistribution ℝ ℂ => 𝓕⁻ T)
    (iteratedLineDeriv_L2_of_top_classical_derivative k hf hF hK)
  rw [inverseFourier_iteratedLineDeriv_multiplier,
    Lp.fourierInv_toTemperedDistribution_eq, Lp.fourierInv_toTemperedDistribution_eq] at hd
  exact ae_mul_eq_of_L2_distribution_eq _ _
    (fun t : ℝ => (-2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) ^ k) (by fun_prop) hd.symm

/-- The actual Fourier-Sobolev multiplier domain follows from smoothness,
L2 mass and the actual top derivative in L2, with the exact top norm. -/
theorem memLp_fourierDerivativeData_of_top_classical_derivative {f : ℝ → ℂ} (k : ℕ)
    (hf : ContDiff ℝ ∞ f) (hF : MemLp f 2) (hD : MemLp (iteratedDeriv k f) 2) :
    ∃ hK : MemLp (fourierDerivativeData k
        ((𝓕⁻ hF.toLp : Lp ℂ 2 volume) : ℝ → ℂ)) 2,
      hK.toLp = (𝓕⁻ hD.toLp : Lp ℂ 2 volume) ∧ ‖hK.toLp‖ = ‖hD.toLp‖ := by
  have hae := inverseFourier_top_classical_derivative_ae k hf hF hD
  have hK := (memLp_congr_ae hae).mpr (Lp.memLp _)
  have heq : hK.toLp = (𝓕⁻ hD.toLp : Lp ℂ 2 volume) := Lp.ext (hK.coeFn_toLp.trans hae)
  refine ⟨hK, heq, ?_⟩
  rw [heq, ← Lp.norm_fourier_eq (𝓕⁻ hD.toLp), FourierTransform.fourier_fourierInv_eq]

/-- Lower angular multipliers are square-integrable whenever the zeroth
and kth multipliers are square-integrable. -/
theorem memLp_fourierDerivativeData_of_le {G : ℝ → ℂ} {j k : ℕ}
    (hG : MemLp G 2) (hK : MemLp (fourierDerivativeData k G) 2) (hjk : j ≤ k) :
    MemLp (fourierDerivativeData j G) 2 := by
  have hsum := hG.norm.add hK.norm
  apply hsum.mono'
  · exact (show Continuous (fun t : ℝ => (-2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) ^ j)
      by fun_prop).aestronglyMeasurable.mul hG.aestronglyMeasurable
  · apply ae_of_all
    intro t
    change ‖fourierDerivativeData j G t‖ ≤ ‖G t‖ + ‖fourierDerivativeData k G t‖
    have he (n : ℕ) : ‖fourierDerivativeData n G t‖ =
        ‖-2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)‖ ^ n * ‖G t‖ := by
      rw [fourierDerivativeData, norm_mul, norm_pow]
    rw [he j, he k]
    have hp : ‖-2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)‖ ^ j ≤
        1 + ‖-2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)‖ ^ k := by
      by_cases ht : 1 ≤ ‖-2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)‖
      · exact (pow_le_pow_right₀ ht hjk).trans (le_add_of_nonneg_left (by norm_num))
      · exact (pow_le_one₀ (norm_nonneg _) (le_of_not_ge ht)).trans
          (le_add_of_nonneg_right (pow_nonneg (norm_nonneg _) _))
    nlinarith [mul_le_mul_of_nonneg_right hp (norm_nonneg (G t))]

/-- Every intermediate actual derivative belongs to L2 from only smoothness,
L2 mass, and the actual top derivative in L2. The Fourier representative
is identified with the original continuous function before differentiating. -/
theorem memLp_iteratedDeriv_of_top_classical_derivative {f : ℝ → ℂ} (k : ℕ)
    (hf : ContDiff ℝ ∞ f) (hF : MemLp f 2) (hD : MemLp (iteratedDeriv k f) 2) :
    ∀ j ≤ k, MemLp (iteratedDeriv j f) 2 := by
  intro j hj
  by_cases heq : j = k
  · simpa only [heq] using hD
  have hjk : j + 1 ≤ k := by omega
  have hk : 1 ≤ k := by omega
  obtain ⟨hK, _, _⟩ := memLp_fourierDerivativeData_of_top_classical_derivative k hf hF hD
  let G : Lp ℂ 2 volume := 𝓕⁻ hF.toLp
  have hM : MemLp (fourierDerivativeData j (G : ℝ → ℂ)) 2 :=
    memLp_fourierDerivativeData_of_le (Lp.memLp G) hK hj
  have hmoment : ∀ i ≤ j, Integrable (fun t : ℝ => t ^ i • G t) :=
    fun i hi => integrable_real_moment_of_fourierSobolev (Lp.memLp G) hK (by omega)
  obtain ⟨hJ, _⟩ := memLp_iteratedDeriv_fourier_of_integrable_moments_le hmoment le_rfl hM
  have hrep : (𝓕 (G : ℝ → ℂ) : ℝ → ℂ) = f :=
    fourierIntegral_inverse_L2_eq_of_fourierSobolev hf.continuous hF hk hK
  rwa [hrep] at hJ

/-- A concrete order-two regression: square-integrability of the first
derivative is derived, not included among the premises. -/
theorem memLp_deriv_of_second_classical_derivative {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (hF : MemLp f 2) (hD : MemLp (iteratedDeriv 2 f) 2) :
    MemLp (deriv f) 2 := by
  simpa only [iteratedDeriv_one] using
    memLp_iteratedDeriv_of_top_classical_derivative 2 hf hF hD 1 (by omega)

private theorem integrable_physical_derivative_ray {h : ℝ → ℂ} {j : ℕ}
    (hD : MemLp (iteratedDeriv j h) 2) {ε : ℝ} (hε : ε ^ 2 = 1) :
    Integrable (fun x : ℝ => ‖iteratedDeriv j h (ε * x)‖ ^ 2) := by
  have hi := (memLp_two_iff_integrable_sq_norm hD.aestronglyMeasurable).mp hD
  rcases sq_eq_one_iff.mp hε with rfl | rfl
  · simpa only [one_mul] using hi
  · simpa only [neg_one_mul] using hi.comp_neg

private theorem integrable_physical_weight_ray (k : ℕ) {h : ℝ → ℂ}
    (hW : Integrable (fun x : ℝ => x ^ (2 * k) * ‖h x‖ ^ 2))
    {ε : ℝ} (hε : ε ^ 2 = 1) :
    Integrable (fun x : ℝ => x ^ (2 * k) * ‖h (ε * x)‖ ^ 2) := by
  rcases sq_eq_one_iff.mp hε with rfl | rfl
  · simpa only [one_mul] using hW
  · simpa only [neg_one_mul, (even_two_mul k).neg_pow] using hW.comp_neg

/-- The actual cutoff chart has its complete classical L2 derivative
tower. The premises are only the smooth physical function, its mass,
its top derivative, and its genuine physical power-weighted mass. -/
theorem signedSquareCutoffChart_memLp_derivatives (k : ℕ) {R : ℝ} (hR : 2 ≤ R)
    {ε : ℝ} (hε : ε ^ 2 = 1) {h : ℝ → ℂ} (hh : ContDiff ℝ ∞ h)
    (hF : MemLp h 2) (hD : MemLp (iteratedDeriv k h) 2)
    (hW : Integrable (fun x : ℝ => x ^ (2 * k) * ‖h x‖ ^ 2)) :
    MemLp (signedSquareCutoffChart k R ε h) 2 ∧
      ∀ j ≤ k, MemLp (iteratedDeriv j (signedSquareCutoffChart k R ε h)) 2 := by
  have htower := memLp_iteratedDeriv_of_top_classical_derivative k hh hF hD
  have hGcont := contDiff_signedSquareCutoffChart k (R := R) (by linarith) ε hh
  have hmass := (integrable_signedSquareCutoffChart_mass_and_tail_le k hR ε hh
    (integrable_physical_weight_ray k hW hε)).1
  have hG : MemLp (signedSquareCutoffChart k R ε h) 2 :=
    (memLp_two_iff_integrable_sq_norm hGcont.continuous.aestronglyMeasurable).mpr hmass
  obtain ⟨_, _, hb⟩ := exists_integral_signedSquareCutoffChart_deriv_le k (by norm_num : (0 : ℝ) < 1) hR
  have htop := (hb ε hε h hh (fun j hj => integrable_physical_derivative_ray (htower j hj) hε)).1
  have hGD : MemLp (iteratedDeriv k (signedSquareCutoffChart k R ε h)) 2 :=
    (memLp_two_iff_integrable_sq_norm
      (hGcont.continuous_iteratedDeriv k (by simp)).aestronglyMeasurable).mpr htop
  exact ⟨hG, memLp_iteratedDeriv_of_top_classical_derivative k hGcont hG hGD⟩

/-- The localized chart enters the actual Fourier-Sobolev domain with
the exact Plancherel normalization of its top derivative energy. -/
theorem signedSquareCutoffChart_fourierSobolev (k : ℕ) {R : ℝ} (hR : 2 ≤ R)
    {ε : ℝ} (hε : ε ^ 2 = 1) {h : ℝ → ℂ} (hh : ContDiff ℝ ∞ h)
    (hF : MemLp h 2) (hD : MemLp (iteratedDeriv k h) 2)
    (hW : Integrable (fun x : ℝ => x ^ (2 * k) * ‖h x‖ ^ 2)) :
    ∃ hG : MemLp (signedSquareCutoffChart k R ε h) 2,
      ∃ hK : MemLp (fourierDerivativeData k
          ((𝓕⁻ hG.toLp : Lp ℂ 2 volume) : ℝ → ℂ)) 2,
        ‖hK.toLp‖ ^ 2 = ∫ σ : ℝ,
          ‖iteratedDeriv k (signedSquareCutoffChart k R ε h) σ‖ ^ 2 := by
  obtain ⟨hG, hGD⟩ := signedSquareCutoffChart_memLp_derivatives k hR hε hh hF hD hW
  obtain ⟨hK, _, hnorm⟩ := memLp_fourierDerivativeData_of_top_classical_derivative k
    (contDiff_signedSquareCutoffChart k (R := R) (by linarith) ε hh) hG (hGD k le_rfl)
  refine ⟨hG, hK, ?_⟩
  rw [hnorm, integral_norm_sq_eq_toLp_norm_sq_complex (hGD k le_rfl)]

end

end MeyerGeneralProblem
