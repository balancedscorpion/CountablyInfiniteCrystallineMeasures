module

public import MeyerGeneralProblem.Sampling.GroupedSobolevSpectralGap
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import all Mathlib.MeasureTheory.Integral.IntegralEqImproper

@[expose] public section

/-!
# Classical L2 derivatives and the actual Fourier multiplier domain

Integration by parts against genuine Schwartz test functions identifies a
classical L2 derivative with the distributional derivative of the same L2
function. Local distributional uniqueness then identifies its inverse Fourier
transform with the actual angular frequency multiplier. No Schwartz regularity
is imposed on the original function.
-/

namespace MeyerGeneralProblem

noncomputable section

open MeasureTheory Set Filter LineDeriv
open scoped Topology FourierTransform SchwartzMap ContDiff

/-- A differentiable function and its actual L2 derivative define exactly
the expected distributional derivative. -/
theorem lineDeriv_L2_of_classical_deriv {f : ℝ → ℂ}
    (hf : Differentiable ℝ f) (hF : MemLp f 2) (hD : MemLp (deriv f) 2) :
    lineDerivOp (1 : ℝ) (hF.toLp : TemperedDistribution ℝ ℂ) =
      (hD.toLp : TemperedDistribution ℝ ℂ) := by
  ext φ
  have hφ : MemLp (fun x : ℝ => deriv φ x) 2 := (SchwartzMap.derivCLM ℂ ℂ φ).memLp 2 volume
  have hparts := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := (φ : ℝ → ℂ)) (u' := deriv φ) (v := f) (v' := deriv f)
    (fun x _ => φ.hasDerivAt x) (fun x _ => (hf x).hasDerivAt)
    (φ.memLp 2 volume |>.integrable_mul hD)
    (hφ.integrable_mul hF) (φ.memLp 2 volume |>.integrable_mul hF)
  simp only [TemperedDistribution.lineDerivOp_apply_apply, Lp.toTemperedDistribution_apply]
  have hleft : (∫ x : ℝ, (-lineDerivOp (1:ℝ) φ) x • (hF.toLp : Lp ℂ 2 volume) x) =
      -(∫ x : ℝ, deriv φ x * f x) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [hF.coeFn_toLp] with x hx
    simp only [neg_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv,
      fderiv_apply_one_eq_deriv, hx, smul_eq_mul, neg_mul]
  rw [hleft]
  calc
    _ = ∫ x : ℝ, φ x * deriv f x := hparts.symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hD.coeFn_toLp] with x hx
      simp [hx, smul_eq_mul]

/-- An equality of L2-induced distributions after multiplication by a
smooth temperate coefficient is an actual almost-everywhere equality of
the coefficient-times-function, even when that product is not initially
known to lie in L2. -/
theorem ae_mul_eq_of_L2_distribution_eq (A B : Lp ℂ 2 (volume : Measure ℝ))
    (m : ℝ → ℂ) (hm : m.HasTemperateGrowth)
    (heq : (A : TemperedDistribution ℝ ℂ) =
      TemperedDistribution.smulLeftCLM ℂ m (B : TemperedDistribution ℝ ℂ)) :
    (fun x : ℝ => m x * B x) =ᵐ[volume] A := by
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp B).locallyIntegrable (by norm_num) |>.continuous_mul hm.1.continuous)
    ((Lp.memLp A).locallyIntegrable (by norm_num))
  intro g hg hgc
  let φ : SchwartzMap ℝ ℂ :=
    (hgc.comp_left (show Complex.ofRealCLM 0 = 0 from rfl)).toSchwartzMap
      (show ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) by fun_prop)
  have hφ (x : ℝ) : φ x = (g x : ℂ) := rfl
  have htest := congrArg (fun T : TemperedDistribution ℝ ℂ => T φ) heq
  simp only [Lp.toTemperedDistribution_apply,
    TemperedDistribution.smulLeftCLM_apply_apply] at htest
  simpa [hm, hφ, smul_eq_mul, Complex.real_smul, mul_comm, mul_left_comm,
    mul_assoc] using htest.symm

/-- The inverse Fourier transform of an actual classical L2 derivative
is the true angular frequency multiplier, with the negative Fourier
integral convention used throughout the sampling modules. -/
theorem inverseFourier_classical_deriv_ae {f : ℝ → ℂ}
    (hf : Differentiable ℝ f) (hF : MemLp f 2) (hD : MemLp (deriv f) 2) :
    (fun t : ℝ => (-2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) *
      (𝓕⁻ hF.toLp : Lp ℂ 2 volume) t) =ᵐ[volume]
        (𝓕⁻ hD.toLp : Lp ℂ 2 volume) := by
  let m : ℝ → ℂ := fun t => -2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)
  have hm : m.HasTemperateGrowth := by dsimp [m]; fun_prop
  apply ae_mul_eq_of_L2_distribution_eq _ _ m hm
  have hdist := congrArg (fun T : TemperedDistribution ℝ ℂ => 𝓕⁻ T)
    (lineDeriv_L2_of_classical_deriv hf hF hD)
  rw [TemperedDistribution.fourierInv_lineDerivOp_eq,
    Lp.fourierInv_toTemperedDistribution_eq,
    Lp.fourierInv_toTemperedDistribution_eq] at hdist
  rw [← hdist]
  ext φ
  have hi : (fun x : ℝ => ((inner ℝ x (1 : ℝ) : ℝ) : ℂ)).HasTemperateGrowth := by fun_prop
  simp only [smul_apply,
    TemperedDistribution.smulLeftCLM_apply_apply, Lp.toTemperedDistribution_apply,
    SchwartzMap.smulLeftCLM_apply hi, SchwartzMap.smulLeftCLM_apply hm,
    smul_eq_mul]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [m, Real.inner_apply, mul_one]
  ring

/-- Every actual classical L2 derivative has the exact inverse-Fourier
angular multiplier representative. The derivative order and all intermediate
L2 assumptions are explicit. -/
theorem inverseFourier_iteratedDeriv_ae {f : ℝ → ℂ} (k : ℕ)
    (hf : ContDiff ℝ k f) (hF : MemLp f 2)
    (hD : ∀ j ≤ k, MemLp (iteratedDeriv j f) 2) :
    fourierDerivativeData k ((𝓕⁻ hF.toLp : Lp ℂ 2 volume) : ℝ → ℂ) =ᵐ[volume]
      (𝓕⁻ (hD k le_rfl).toLp : Lp ℂ 2 volume) := by
  have haux : ∀ j (hj : j ≤ k),
      fourierDerivativeData j ((𝓕⁻ hF.toLp : Lp ℂ 2 volume) : ℝ → ℂ) =ᵐ[volume]
        (𝓕⁻ (hD j hj).toLp : Lp ℂ 2 volume) := by
    intro j
    induction j with
    | zero =>
      intro hj
      have hz : (hD 0 hj).toLp = hF.toLp :=
        MemLp.toLp_congr _ _ (by simpa only [iteratedDeriv_zero] using
          (Filter.EventuallyEq.rfl : f =ᵐ[volume] f))
      rw [hz]
      filter_upwards [] with t
      simp only [fourierDerivativeData, pow_zero, one_mul]
    | succ j ih =>
      intro hj
      have hjk : j ≤ k := by omega
      have hDj : MemLp (deriv (iteratedDeriv j f)) 2 := by
        simpa only [← iteratedDeriv_succ] using hD (j+1) hj
      have hstep := inverseFourier_classical_deriv_ae
        (hf.differentiable_iteratedDeriv j (by exact_mod_cast (show j < k by omega)))
        (hD j hjk) hDj
      have hLp : hDj.toLp = (hD (j+1) hj).toLp :=
        MemLp.toLp_congr _ _ (by rw [iteratedDeriv_succ])
      rw [hLp] at hstep
      filter_upwards [ih hjk, hstep] with t ht hs
      dsimp only [fourierDerivativeData] at ht ⊢
      rw [pow_succ]
      calc
        _ = (-2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) *
            ((-2 * (Real.pi : ℂ) * Complex.I * (t : ℂ))^j *
              (𝓕⁻ hF.toLp : Lp ℂ 2 volume) t) := by ring
        _ = _ := by rw [ht]; exact hs
  exact haux k le_rfl

/-- Classical Sobolev data enter the actual Fourier multiplier domain,
with precisely the Plancherel norm of the classical top derivative. -/
theorem memLp_fourierDerivativeData_of_classical_derivatives {f : ℝ → ℂ} (k : ℕ)
    (hf : ContDiff ℝ k f) (hF : MemLp f 2)
    (hD : ∀ j ≤ k, MemLp (iteratedDeriv j f) 2) :
    ∃ hK : MemLp (fourierDerivativeData k
        ((𝓕⁻ hF.toLp : Lp ℂ 2 volume) : ℝ → ℂ)) 2,
      hK.toLp = (𝓕⁻ (hD k le_rfl).toLp : Lp ℂ 2 volume) ∧
        ‖hK.toLp‖ = ‖(hD k le_rfl).toLp‖ := by
  have hae := inverseFourier_iteratedDeriv_ae k hf hF hD
  have hK := (memLp_congr_ae hae).mpr (Lp.memLp _)
  have heq : hK.toLp = (𝓕⁻ (hD k le_rfl).toLp : Lp ℂ 2 volume) := by
    apply Lp.ext
    exact hK.coeFn_toLp.trans hae
  refine ⟨hK, heq, ?_⟩
  rw [heq, ← Lp.norm_fourier_eq (𝓕⁻ (hD k le_rfl).toLp),
    FourierTransform.fourier_fourierInv_eq]

/-- The actual physical power weight gives the exact angular derivative
multiplier domain of its Fourier transform. -/
theorem memLp_fourierDerivativeData_of_physical_power {f : ℝ → ℂ} (k : ℕ)
    (hW : MemLp (fun x : ℝ => (x : ℂ)^k * f x) 2) :
    MemLp (fourierDerivativeData k f) 2 := by
  convert hW.const_smul ((-2 * (Real.pi : ℂ) * Complex.I)^k) using 1
  funext x
  simp only [fourierDerivativeData, mul_pow, Pi.smul_apply, smul_eq_mul]
  ring

/-- A physical power weight in L2 gives a genuine classical Fourier
integral of class C^(k-1), agreeing with the L2 Fourier transform. In
particular k at least two supplies a C1 representative. -/
theorem fourier_regular_of_physical_power {f : ℝ → ℂ} (k : ℕ) (hk : 1 ≤ k)
    (hF : MemLp f 2) (hW : MemLp (fun x : ℝ => (x : ℂ)^k * f x) 2) :
    Integrable f ∧ ContDiff ℝ (k-1) (𝓕 f : ℝ → ℂ) ∧
      ((𝓕 f : ℝ → ℂ) =ᵐ[volume] (𝓕 hF.toLp : Lp ℂ 2 volume)) ∧
      MemLp (𝓕 f : ℝ → ℂ) 2 := by
  have hK := memLp_fourierDerivativeData_of_physical_power k hW
  have hm : ∀ j ≤ k-1, Integrable (fun t : ℝ => t^j • f t) :=
    fun j hj => integrable_real_moment_of_fourierSobolev hF hK (by omega)
  have hL1 : Integrable f := by simpa only [pow_zero, one_smul] using hm 0 (by omega)
  have hae := fourierIntegral_ae_eq_L2 hL1 hF
  exact ⟨hL1, contDiff_fourier_of_integrable_moments_le hm, hae,
    (memLp_congr_ae hae).mpr (Lp.memLp _)⟩

/-- The grouped spectral bound applies to actual classical Sobolev
functions, with its right side the integral of the genuine top derivative. -/
theorem spectralGap_of_groupedZeros_classicalSobolev
    {q N : ℕ} {d B₀ Ω Ω' : ℝ} (hd : 0 < d) (hΩ : 1 ≤ Ω)
    (hΩΩ' : Ω < Ω') (hgap : Ω' / Real.pi < (N : ℝ) / B₀) :
    ∃ C > 0, ∀ (Λ : TwoSidedCarrier) (_hcluster : BoundedClusterOrder Λ.toLocallyFinite d q),
      (∀ t R, 0 < R → (N : ℝ) * ((⌊2 * R / B₀⌋ : ℝ) - 2) ≤
        ((Λ.toLocallyFinite.carrier ∩ Ioo (t - R) (t + R)).ncard : ℝ)) →
      ∀ (f : ℝ → ℂ) (k : ℕ), q + 1 ≤ k → ContDiff ℝ k f → MemLp f 2 →
      (∀ j ≤ k, MemLp (iteratedDeriv j f) 2) →
      (∀ t ∈ Λ.toLocallyFinite.carrier, f t = 0) →
      (∫ t : ℝ, ‖f t‖^2) ≤ C * (Ω^(2*k))⁻¹ * (∫ t : ℝ, ‖iteratedDeriv k f t‖^2) := by
  obtain ⟨C, hC, hbound⟩ := spectralGap_of_groupedZeros_continuousFourierSobolev
    (q := q) hd hΩ hΩΩ' hgap
  refine ⟨C, hC, ?_⟩
  intro Λ hcluster hblock f k hqk hf hF hD hzero
  obtain ⟨hK, _, hnorm⟩ := memLp_fourierDerivativeData_of_classical_derivatives k hf hF hD
  simpa only [hnorm, integral_norm_sq_eq_toLp_norm_sq_complex (hD k le_rfl)] using
    hbound Λ hcluster hblock f hf.continuous hF k hqk hK hzero

/-- A common cofinal strict spectral gap holds for actual classical
Sobolev functions, with the order threshold fixed before the carrier and
the function. Its derivative energy is the actual real integral. -/
theorem eventual_spectralGap_of_groupedZeros_classicalSobolev
    {q N : ℕ} {d B₀ Ω Ω' : ℝ} (hd : 0 < d) (hπΩ : Real.pi < Ω)
    (hΩΩ' : Ω < Ω') (hgap : Ω' / Real.pi < (N : ℝ) / B₀) :
    ∃ k₀ : ℕ, q + 1 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
      ∀ (Λ : TwoSidedCarrier) (_hcluster : BoundedClusterOrder Λ.toLocallyFinite d q),
      (∀ t R, 0 < R → (N : ℝ) * ((⌊2 * R / B₀⌋ : ℝ) - 2) ≤
        ((Λ.toLocallyFinite.carrier ∩ Ioo (t - R) (t + R)).ncard : ℝ)) →
      ∀ (f : ℝ → ℂ), ContDiff ℝ k f → MemLp f 2 →
      (∀ j ≤ k, MemLp (iteratedDeriv j f) 2) →
      (∀ t ∈ Λ.toLocallyFinite.carrier, f t = 0) →
      Real.pi^(2*k) * (∫ t : ℝ, ‖f t‖^2) ≤
        (1/2 : ℝ) * (∫ t : ℝ, ‖iteratedDeriv k f t‖^2) := by
  obtain ⟨k₀, hqk₀, hbound⟩ := eventual_spectralGap_of_groupedZeros_continuousFourierSobolev
    (q := q) hd hπΩ hΩΩ' hgap
  refine ⟨k₀, hqk₀, ?_⟩
  intro k hk Λ hcluster hblock f hf hF hD hzero
  obtain ⟨hK, _, hnorm⟩ := memLp_fourierDerivativeData_of_classical_derivatives k hf hF hD
  simpa only [hnorm, integral_norm_sq_eq_toLp_norm_sq_complex (hD k le_rfl)] using
    hbound k hk Λ hcluster hblock f hf.continuous hF hK hzero

end

end MeyerGeneralProblem
