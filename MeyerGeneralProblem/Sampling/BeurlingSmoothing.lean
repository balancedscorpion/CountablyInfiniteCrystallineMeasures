module

public import MeyerGeneralProblem.Sampling.BeurlingFiniteKernels
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
import all Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
import all Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import all Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

@[expose] public section

/-!
# Compact smoothing of finite Beurling interpolation kernels

All Fourier transforms below use the negative-`2π` convention.  Compact
smoothing preserves the exact interpolation values and additive support
budget; Schwartz Plancherel supplies the dimension-uniform estimate.
-/

namespace MeyerGeneralProblem

open MeasureTheory
open scoped SchwartzMap FourierTransform ContDiff ComplexConjugate

noncomputable section

/-- The Fourier transform of modulation is translation in frequency. -/
theorem fourier_mul_gramPhase (f : ℝ → ℂ) (s w : ℝ) :
    FourierTransform.fourier (fun t => f t * gramPhase s t) w =
      FourierTransform.fourier f (w - s) := by
  simp only [fourier_eq_integral_gramPhase]
  apply integral_congr_ae
  filter_upwards [] with t
  have h : gramPhase (-(w - s)) t = gramPhase (-w) t * gramPhase s t := by
    rw [show -(w - s) = -w + s by ring, gramPhase_add]
  rw [h]
  ring

/-- The actual pointwise Fourier transform is bounded by the `L¹` mass. -/
theorem norm_fourier_le_integral_norm (f : ℝ → ℂ) (w : ℝ) :
    ‖FourierTransform.fourier f w‖ ≤ ∫ t : ℝ, ‖f t‖ := by
  rw [fourier_eq_integral_gramPhase]
  simpa only [norm_mul, norm_gramPhase, one_mul] using
    norm_integral_le_integral_norm (fun t => gramPhase (-w) t * f t)

/-- Reflection and complex conjugation conjugate the Fourier transform. -/
theorem fourier_conj_reflect (f : ℝ → ℂ) (w : ℝ) :
    FourierTransform.fourier (fun t => conj (f (-t))) w =
      conj (FourierTransform.fourier f w) := by
  simp only [fourier_eq_integral_gramPhase, ← integral_conj]
  rw [← integral_neg_eq_self (fun t => conj (gramPhase (-w) t * f t))]
  apply integral_congr_ae
  filter_upwards [] with t
  have h : gramPhase (-w) (-t) = gramPhase w t := by
    unfold gramPhase
    congr 3
    ring
  simp only [h, map_mul, ← gramPhase_neg_left]

/-- A smooth compactly supported function stays smooth after convolution
with an integrable function, and interval support gives a genuine Schwartz map. -/
theorem exists_schwartz_fourierKernelConvolution
    {f g : ℝ → ℂ} {R r : ℝ} (hf : Integrable f)
    (hfs : Function.support f ⊆ Set.Icc (-R) R)
    (hgs : Function.support g ⊆ Set.Icc (-r) r) (hg : ContDiff ℝ ∞ g) :
    ∃ v : SchwartzMap ℝ ℂ, (v : ℝ → ℂ) = fourierKernelConvolution f g ∧
      Function.support v ⊆ Set.Icc (-(R + r)) (R + r) := by
  have hgc : HasCompactSupport g :=
    HasCompactSupport.intro isCompact_Icc (fun x hx =>
      not_not.mp (fun h => hx (hgs h)))
  have hs := support_fourierKernelConvolution_subset hfs hgs
  have hc : HasCompactSupport (fourierKernelConvolution f g) :=
    HasCompactSupport.intro isCompact_Icc (fun x hx =>
      not_not.mp (fun h => hx (hs h)))
  have hd : ContDiff ℝ ∞ (fourierKernelConvolution f g) :=
    hgc.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℂ) hf.locallyIntegrable hg
  exact ⟨hc.toSchwartzMap hd, rfl, hs⟩

/-- Every positive support budget admits a genuine smooth autocorrelation
with Fourier value one at zero and everywhere nonnegative Fourier transform. -/
theorem exists_compact_positive_fourier_smoothing {r : ℝ} (hr : 0 < r) :
    ∃ G : SchwartzMap ℝ ℂ,
      Function.support G ⊆ Set.Icc (-r) r ∧
      FourierTransform.fourier (G : ℝ → ℂ) 0 = 1 ∧
      ∀ w : ℝ, ∃ z : ℝ, 0 ≤ z ∧ FourierTransform.fourier (G : ℝ → ℂ) w = z := by
  let b : ContDiffBump (0 : ℝ) :=
    ⟨r / 4, r / 2, by positivity, by linarith⟩
  let h : ℝ → ℂ := fun t => (b.normed volume t : ℂ)
  have hh : Integrable h := b.integrable_normed.ofReal
  have hhsm : ContDiff ℝ ∞ h := Complex.ofRealCLM.contDiff.comp b.contDiff_normed
  have hhs : Function.support h ⊆ Set.Icc (-(r / 2)) (r / 2) := by
    intro t ht
    have ht' : t ∈ Function.support (b.normed volume) := by
      simpa only [Function.mem_support, h, ne_eq, Complex.ofReal_eq_zero] using ht
    rw [b.support_normed_eq] at ht'
    have habs : |t| < r / 2 := by simpa [Metric.mem_ball, Real.dist_eq, b] using ht'
    exact ⟨(abs_lt.mp habs).1.le, (abs_lt.mp habs).2.le⟩
  have href : (fun t => conj (h (-t))) = h := by
    funext t
    simp only [h, Complex.conj_ofReal, b.normed_neg]
  obtain ⟨G, hG, hGs⟩ := exists_schwartz_fourierKernelConvolution hh hhs hhs hhsm
  have hfourier (w : ℝ) : FourierTransform.fourier (G : ℝ → ℂ) w =
      (‖FourierTransform.fourier h w‖ ^ 2 : ℝ) := by
    rw [hG, fourier_fourierKernelConvolution hh hh]
    conv_lhs => rhs; rw [← href, fourier_conj_reflect]
    simpa only [Complex.ofReal_pow] using Complex.mul_conj' (FourierTransform.fourier h w)
  refine ⟨G, ?_, ?_, fun w => ⟨_, sq_nonneg _, hfourier w⟩⟩
  · simpa only [show r / 2 + r / 2 = r by ring] using hGs
  · have hz : FourierTransform.fourier h 0 = 1 := by
      rw [fourier_eq_integral_gramPhase]
      simp only [neg_zero, gramPhase_zero_left, one_mul, h]
      rw [integral_complex_ofReal, b.integral_normed]
      norm_num
    rw [hfourier, hz]
    norm_num

/-- Modulation preserves the support budget of a compact Schwartz function. -/
theorem exists_schwartz_modulation (G : SchwartzMap ℝ ℂ) {r : ℝ}
    (hGs : Function.support G ⊆ Set.Icc (-r) r) (s : ℝ) :
    ∃ g : SchwartzMap ℝ ℂ, (∀ t, g t = G t * gramPhase s t) ∧
      Function.support g ⊆ Set.Icc (-r) r := by
  have hs : Function.support (fun t => G t * gramPhase s t) ⊆ Set.Icc (-r) r := by
    intro t ht
    exact hGs (fun h => ht (by simp only [h, zero_mul]))
  have hc : HasCompactSupport (fun t => G t * gramPhase s t) :=
    HasCompactSupport.intro isCompact_Icc (fun x hx => not_not.mp (fun h => hx (hs h)))
  have hd : ContDiff ℝ ∞ (fun t => G t * gramPhase s t) := by
    apply (G.smooth (⊤ : ℕ∞)).mul
    unfold gramPhase
    have hof : ContDiff ℝ ∞ (fun t : ℝ => ((2 * Real.pi * s * t : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_id)
    exact (hof.mul contDiff_const).cexp
  exact ⟨hc.toSchwartzMap hd, fun _ => rfl, hs⟩

/-- A nonnegative complex majorant permits an exact absolute-coefficient
comparison without a factor depending on the number of summands. -/
theorem norm_sum_le_nonnegative_majorant {n : ℕ} (v g c : Fin n → ℂ) (K : ℝ)
    (hpos : ∀ i, ∃ z : ℝ, 0 ≤ z ∧ g i = (z : ℂ))
    (hdom : ∀ i, ‖v i‖ ≤ K * ‖g i‖) :
    ‖∑ i, c i * v i‖ ≤ K * ‖∑ i, (‖c i‖ : ℂ) * g i‖ := by
  have hw : ‖∑ i, (‖c i‖ : ℂ) * g i‖ = ∑ i, ‖c i‖ * ‖g i‖ := by
    choose z hz hzval using hpos
    have hs : 0 ≤ ∑ i, ‖c i‖ * z i :=
      Finset.sum_nonneg (fun i hi => mul_nonneg (norm_nonneg _) (hz i))
    simp only [hzval, ← Complex.ofReal_mul, ← Complex.ofReal_sum, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hs, abs_of_nonneg (hz _)]
  rw [hw]
  calc
    _ ≤ ∑ i, ‖c i * v i‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖c i‖ * (K * ‖g i‖) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hdom i) (norm_nonneg _)
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i hi; ring

/-- Nonnegative Fourier majorants convert individual pointwise multiplier
bounds into a dimension-independent synthesis estimate by Plancherel. -/
theorem schwartz_synthesis_norm_sq_le_of_fourier_domination
    {n : ℕ} (v g : Fin n → SchwartzMap ℝ ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hpos : ∀ i w, ∃ z : ℝ, 0 ≤ z ∧ (𝓕 (g i)) w = (z : ℂ))
    (hdom : ∀ i w, ‖(𝓕 (v i)) w‖ ≤ Real.sqrt C * ‖(𝓕 (g i)) w‖)
    (c : Fin n → ℂ) :
    (∫ t : ℝ, ‖(∑ i, c i • v i : SchwartzMap ℝ ℂ) t‖ ^ 2) ≤
      C * ∫ t : ℝ, ‖(∑ i, (‖c i‖ : ℂ) • g i : SchwartzMap ℝ ℂ) t‖ ^ 2 := by
  let V : SchwartzMap ℝ ℂ := ∑ i, c i • v i
  let W : SchwartzMap ℝ ℂ := ∑ i, (‖c i‖ : ℂ) • g i
  have hpoint (w : ℝ) : ‖(𝓕 V) w‖ ≤ Real.sqrt C * ‖(𝓕 W) w‖ := by
    simpa only [V, W, FourierTransform.fourier_sum, FourierTransform.fourier_smul,
      sum_apply, smul_apply, smul_eq_mul] using
      norm_sum_le_nonnegative_majorant (fun i => (𝓕 (v i)) w) (fun i => (𝓕 (g i)) w) c
        (Real.sqrt C) (fun i => hpos i w) (fun i => hdom i w)
  change (∫ t : ℝ, ‖V t‖ ^ 2) ≤ C * ∫ t : ℝ, ‖W t‖ ^ 2
  rw [← SchwartzMap.integral_norm_sq_fourier V,
    ← SchwartzMap.integral_norm_sq_fourier W, ← integral_const_mul]
  apply integral_mono (((𝓕 V).memLp 2).integrable_norm_pow (by norm_num))
    (((𝓕 W).memLp 2).integrable_norm_pow (by norm_num) |>.const_mul C)
  intro w
  have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 (hpoint w)
  simpa only [mul_pow, Real.sq_sqrt hC] using hsq

/-- The existing upper large sieve controls finite sums of modulated copies
of one compact Schwartz smoother, uniformly in the number of frequencies. -/
theorem schwartz_modulation_synthesis_norm_sq_le
    {n : ℕ} (s : Fin n → ℝ) {d r M : ℝ} (hd : 0 < d) (hr : 0 ≤ r)
    (hsep : PairwiseFrequencySeparated s d) (G : SchwartzMap ℝ ℂ)
    (hGs : Function.support G ⊆ Set.Icc (-r) r) (hM : 0 ≤ M)
    (hGM : ∀ t, ‖G t‖ ≤ M) (g : Fin n → SchwartzMap ℝ ℂ)
    (hg : ∀ i t, g i t = G t * gramPhase (s i) t) (c : Fin n → ℂ) :
    (∫ t : ℝ, ‖(∑ i, c i • g i : SchwartzMap ℝ ℂ) t‖ ^ 2) ≤
      M ^ 2 * (fourierIntervalLargeSieveConstant * (2 * r + d⁻¹)) *
        ∑ i, ‖c i‖ ^ 2 := by
  let W : SchwartzMap ℝ ℂ := ∑ i, c i • g i
  have hW (t : ℝ) : W t = G t * gramFourierPolynomial s c t := by
    simp only [W, sum_apply, smul_apply, smul_eq_mul, hg,
      gramFourierPolynomial, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hz (t : ℝ) (ht : t ∉ Set.Icc (-r) r) : ‖W t‖ ^ 2 = 0 := by
    have hgt : G t = 0 := not_not.mp (fun h => ht (hGs h))
    simp only [hW, hgt, zero_mul, norm_zero, zero_pow (by norm_num : 2 ≠ 0)]
  change (∫ t : ℝ, ‖W t‖ ^ 2) ≤ _
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz]
  have hint : IntegrableOn (fun t => ‖gramFourierPolynomial s c t‖ ^ 2)
      (Set.Icc (-r) r) volume :=
    ((continuous_gramFourierPolynomial s c).norm.pow 2).integrableOn_Icc
  calc
    _ ≤ ∫ t : ℝ in Set.Icc (-r) r, M ^ 2 * ‖gramFourierPolynomial s c t‖ ^ 2 := by
      apply setIntegral_mono_on ((W.memLp 2 volume).integrable_norm_pow (by norm_num)).integrableOn
        (hint.const_mul (M ^ 2)) measurableSet_Icc
      intro t ht
      rw [hW, norm_mul, mul_pow]
      exact mul_le_mul_of_nonneg_right ((sq_le_sq₀ (norm_nonneg _) hM).2 (hGM t))
        (sq_nonneg _)
    _ = M ^ 2 * ∫ t : ℝ in Set.Icc (-r) r, ‖gramFourierPolynomial s c t‖ ^ 2 :=
      integral_const_mul _ _
    _ ≤ M ^ 2 * (fourierIntervalLargeSieveConstant * (2 * r + d⁻¹) * ∑ i, ‖c i‖ ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      simpa only [sub_neg_eq_add, ← two_mul] using
        integral_norm_sq_le_interval_largeSieve hd (by linarith : -r ≤ r) s hsep c
    _ = _ := by ring

/-- Uniformly `L¹`-bounded finite interpolation kernels possess genuine
Schwartz smoothings with a dimension-uniform synthesis bound.  The bound
is chosen before the finite family, and the extra support cost is exactly `r`. -/
theorem exists_uniform_smoothed_interpolation_bessel
    {R r d C : ℝ} (hr : 0 < r) (hd : 0 < d) (hC : 0 < C) :
    ∃ B : ℝ, 0 < B ∧ ∀ (n : ℕ) (s : Fin n → ℝ),
      PairwiseFrequencySeparated s d → ∀ ρ : Fin n → ℝ → ℂ,
      (∀ i, Integrable (ρ i)) →
      (∀ i, Function.support (ρ i) ⊆ Set.Icc (-R) R) →
      (∀ i j, FourierTransform.fourier (ρ i) (s j) = if i = j then 1 else 0) →
      (∀ i, (∫ t : ℝ, ‖ρ i t‖) ^ 2 ≤ C) →
      ∃ v : Fin n → SchwartzMap ℝ ℂ,
        (∀ i, Function.support (v i) ⊆ Set.Icc (-(R + r)) (R + r)) ∧
        (∀ i j, FourierTransform.fourier (v i : ℝ → ℂ) (s j) =
          if i = j then 1 else 0) ∧
        ∀ c : Fin n → ℂ,
          (∫ t : ℝ, ‖(∑ i, c i • v i : SchwartzMap ℝ ℂ) t‖ ^ 2) ≤
            B * ∑ i, ‖c i‖ ^ 2 := by
  classical
  obtain ⟨G, hGs, hGzero, hGpos⟩ := exists_compact_positive_fourier_smoothing hr
  let M := SchwartzMap.seminorm ℝ 0 0 G + 1
  have hM : 0 < M := by
    have := (norm_nonneg (G 0)).trans (G.norm_le_seminorm ℝ 0)
    dsimp [M]
    linarith
  have hGM (t : ℝ) : ‖G t‖ ≤ M := (G.norm_le_seminorm ℝ t).trans (by dsimp [M]; linarith)
  let K := M ^ 2 * (fourierIntervalLargeSieveConstant * (2 * r + d⁻¹))
  have hK : 0 < K := by
    dsimp [K]
    exact mul_pos (sq_pos_of_pos hM) (mul_pos fourierIntervalLargeSieveConstant_pos (by positivity))
  refine ⟨C * K, mul_pos hC hK, fun n s hsep ρ hρint hρs hρfourier hρmass => ?_⟩
  choose g hg hgs using fun i => exists_schwartz_modulation G hGs (s i)
  have hgf (i : Fin n) (w : ℝ) :
      FourierTransform.fourier (g i : ℝ → ℂ) w =
        FourierTransform.fourier (G : ℝ → ℂ) (w - s i) := by
    have heq : (g i : ℝ → ℂ) = fun t => G t * gramPhase (s i) t := funext (hg i)
    rw [heq, fourier_mul_gramPhase]
  choose v hv hvs using fun i => exists_schwartz_fourierKernelConvolution
    (hρint i) (hρs i) (hgs i) ((g i).smooth (⊤ : ℕ∞))
  have hvf (i : Fin n) (w : ℝ) :
      FourierTransform.fourier (v i : ℝ → ℂ) w =
        FourierTransform.fourier (ρ i) w * FourierTransform.fourier (g i : ℝ → ℂ) w := by
    rw [hv i, fourier_fourierKernelConvolution (hρint i) (g i).integrable]
  refine ⟨v, hvs, ?_, ?_⟩
  · intro i j
    rw [hvf, hρfourier]
    by_cases hij : i = j
    · subst j
      simp only [ite_true, one_mul, hgf, sub_self, hGzero]
    · simp only [hij, ite_false, zero_mul]
  · intro c
    have hmass (i : Fin n) : (∫ t : ℝ, ‖ρ i t‖) ≤ Real.sqrt C := by
      apply (sq_le_sq₀ (integral_nonneg (fun t => norm_nonneg _)) (Real.sqrt_nonneg _)).1
      simpa only [Real.sq_sqrt hC.le] using hρmass i
    have hdom (i : Fin n) (w : ℝ) :
        ‖(𝓕 (v i)) w‖ ≤ Real.sqrt C * ‖(𝓕 (g i)) w‖ := by
      change ‖FourierTransform.fourier (v i : ℝ → ℂ) w‖ ≤ _
      rw [hvf, norm_mul]
      exact mul_le_mul_of_nonneg_right
        ((norm_fourier_le_integral_norm (ρ i) w).trans (hmass i)) (norm_nonneg _)
    have hpos (i : Fin n) (w : ℝ) : ∃ z : ℝ, 0 ≤ z ∧ (𝓕 (g i)) w = (z : ℂ) := by
      change ∃ z : ℝ, 0 ≤ z ∧ FourierTransform.fourier (g i : ℝ → ℂ) w = (z : ℂ)
      rw [hgf]
      exact hGpos _
    have hbound := schwartz_modulation_synthesis_norm_sq_le s hd hr.le hsep G hGs hM.le hGM
      g hg (fun i => (‖c i‖ : ℂ))
    have hbound' : (∫ t : ℝ, ‖(∑ i, (‖c i‖ : ℂ) • g i : SchwartzMap ℝ ℂ) t‖ ^ 2) ≤
        K * ∑ i, ‖c i‖ ^ 2 := by
      simpa only [K, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hbound
    exact (schwartz_synthesis_norm_sq_le_of_fourier_domination v g hC.le hpos hdom c).trans
      (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hbound' hC.le)

/-- Strict upper density and positive separation produce actual compact
Schwartz Fourier interpolation kernels with a uniform synthesis Bessel
bound.  All constants are fixed before the finite family is chosen. -/
theorem exists_uniform_schwartz_interpolation_bessel_of_upperDensity_lt
    (S : LocallyFiniteCarrier) {a d : ℝ} (ha : 0 < a) (hd : 0 < d)
    (hS : upperUniformBeurlingDensity S < ENNReal.ofReal (2 * a))
    (hsep : ∀ x ∈ S.carrier, ∀ y ∈ S.carrier, x ≠ y → d ≤ |x - y|) :
    ∃ B : ℝ, 0 < B ∧ ∀ (n : ℕ) (s : Fin n → ℝ),
      (∀ i, s i ∈ S.carrier) → Function.Injective s →
      ∃ v : Fin n → SchwartzMap ℝ ℂ,
        (∀ i, Function.support (v i) ⊆ Set.Icc (-a) a) ∧
        (∀ i j, FourierTransform.fourier (v i : ℝ → ℂ) (s j) =
          if i = j then 1 else 0) ∧
        ∀ c : Fin n → ℂ,
          (∫ t : ℝ, ‖(∑ i, c i • v i : SchwartzMap ℝ ℂ) t‖ ^ 2) ≤
            B * ∑ i, ‖c i‖ ^ 2 := by
  classical
  obtain ⟨R, C, _hR, hRa, hC, hkernels⟩ :=
    exists_uniform_finite_interpolation_kernels_of_upperDensity_lt S ha hd hS hsep
  let r := (a - R) / 2
  have hr : 0 < r := by dsimp [r]; linarith
  have hbudget : R + r ≤ a := by dsimp [r]; linarith
  obtain ⟨B, hB, hsmooth⟩ := exists_uniform_smoothed_interpolation_bessel (R := R) hr hd hC
  refine ⟨B, hB, fun n s hs hsinj => ?_⟩
  let F : Finset ℝ := Finset.univ.image s
  have hF : ∀ x ∈ F, x ∈ S.carrier := by
    intro x hx
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.1 hx
    exact hs i
  obtain ⟨ρ, hρint, hρs, hρfourier, hρmass⟩ := hkernels F hF
  let e : Fin n → F := fun i => ⟨s i, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
  have he : Function.Injective e := fun i j h => hsinj (congrArg Subtype.val h)
  have hsep' : PairwiseFrequencySeparated s d :=
    fun i j hij => hsep (s i) (hs i) (s j) (hs j) (fun h => hij (hsinj h))
  have hρfourier' (i j : Fin n) :
      FourierTransform.fourier (ρ (e i)) (s j) = if i = j then 1 else 0 := by
    simpa only [he.eq_iff] using hρfourier (e i) (e j)
  obtain ⟨v, hvs, hvfourier, hvbound⟩ := hsmooth n s hsep' (fun i => ρ (e i))
    (fun i => hρint (e i)) (fun i => hρs (e i)) hρfourier' (fun i => hρmass (e i))
  refine ⟨v, ?_, hvfourier, hvbound⟩
  intro i t ht
  have ht' := hvs i ht
  exact ⟨by linarith [ht'.1], ht'.2.trans hbudget⟩

end

end MeyerGeneralProblem
