module

public import MeyerGeneralProblem.Sampling.BeurlingInterpolation
public import Mathlib.Analysis.Normed.Module.HahnBanach
import all Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.InnerProductSpace.Dual
import all Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.MeasureTheory.Function.L2Space
import all Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.Fourier.Convolution
import all Mathlib.Analysis.Fourier.Convolution

@[expose] public section

/-!
# Biorthogonal kernels for the Beurling interpolation construction

This module constructs genuine Hilbert-space biorthogonal vectors from the
finite lower inequality.  The bounds are uniform in the finite dimension.
-/

namespace MeyerGeneralProblem

open MeasureTheory ComplexConjugate

noncomputable section

/-- A finite family with a positive quadratic lower bound has actual
biorthogonal vectors with norm at most `1 / sqrt A`, independently of its
cardinality. -/
theorem exists_finite_biorthogonal_of_lowerBound
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {n : ℕ} (v : Fin n → H) {A : ℝ} (hA : 0 < A)
    (hlower : ∀ c : Fin n → ℂ,
      A * ∑ i, ‖c i‖ ^ 2 ≤ ‖∑ i, c i • v i‖ ^ 2) :
    ∃ y : Fin n → H, (∀ i j, inner ℂ (y i) (v j) = if i = j then 1 else 0) ∧
      ∀ i, ‖y i‖ ≤ (Real.sqrt A)⁻¹ := by
  classical
  let S : (Fin n → ℂ) →ₗ[ℂ] H := Fintype.linearCombination ℂ v
  have hsqrt : 0 < Real.sqrt A := Real.sqrt_pos.2 hA
  have hcoordinate (c : Fin n → ℂ) (k : Fin n) :
      ‖c k‖ ≤ (Real.sqrt A)⁻¹ * ‖S c‖ := by
    have hsum : ‖c k‖ ^ 2 ≤ ∑ i, ‖c i‖ ^ 2 :=
      Finset.single_le_sum (fun i hi => sq_nonneg ‖c i‖) (Finset.mem_univ k)
    have hsq : (Real.sqrt A * ‖c k‖) ^ 2 ≤ ‖S c‖ ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hA.le]
      exact (mul_le_mul_of_nonneg_left hsum hA.le).trans (hlower c)
    have h := (sq_le_sq₀ (by positivity) (norm_nonneg (S c))).1 hsq
    calc
      ‖c k‖ ≤ ‖S c‖ / Real.sqrt A :=
        (le_div_iff₀ hsqrt).2 (by simpa only [mul_comm] using h)
      _ = (Real.sqrt A)⁻¹ * ‖S c‖ := by ring
  have hinj : Function.Injective S := by
    intro c e hce
    have hzero : S (c - e) = 0 := by rw [map_sub, hce, sub_self]
    ext i
    have hi := hcoordinate (c - e) i
    rw [hzero, norm_zero, mul_zero] at hi
    exact sub_eq_zero.1 (norm_eq_zero.1 (le_antisymm hi (norm_nonneg _)))
  let R : (Fin n → ℂ) ≃ₗ[ℂ] S.range := LinearEquiv.ofInjective S hinj
  have hex (i : Fin n) : ∃ y : H,
      (∀ j, inner ℂ y (v j) = if i = j then 1 else 0) ∧
        ‖y‖ ≤ (Real.sqrt A)⁻¹ := by
    let coord : S.range →ₗ[ℂ] ℂ := (LinearMap.proj i).comp R.symm.toLinearMap
    have hc (z : S.range) : ‖coord z‖ ≤ (Real.sqrt A)⁻¹ * ‖z‖ := by
      have h := hcoordinate (R.symm z) i
      have hz : S (R.symm z) = (z : H) := congrArg Subtype.val (R.apply_symm_apply z)
      simpa only [coord, LinearMap.comp_apply, LinearMap.proj_apply,
        LinearEquiv.coe_coe, hz, Submodule.norm_coe] using h
    let fc : S.range →L[ℂ] ℂ := coord.mkContinuous (Real.sqrt A)⁻¹ hc
    obtain ⟨g, hg, hgnorm⟩ := exists_extension_norm_eq S.range fc
    refine ⟨(InnerProductSpace.toDual ℂ H).symm g, fun j => ?_, ?_⟩
    · rw [InnerProductSpace.toDual_symm_apply]
      have hSj : S (Pi.single j 1) = v j := by simp [S]
      have hj := hg (R (Pi.single j 1))
      change g (S (Pi.single j 1)) = coord (R (Pi.single j 1)) at hj
      rw [hSj] at hj
      rw [hj]
      simp [coord, Pi.single_apply]
    · rw [(InnerProductSpace.toDual ℂ H).symm.norm_map, hgnorm]
      exact fc.opNorm_le_bound (inv_nonneg.2 hsqrt.le) hc
  choose y hy hnorm using hex
  exact ⟨y, hy, hnorm⟩

/-- The Hilbert space on the actual symmetric Fourier window. -/
abbrev FourierWindowSpace (b : ℝ) := Lp ℂ 2 (volume.restrict (Set.Icc (-b) b))

theorem memLp_gramPhase_window (b ω : ℝ) :
    MemLp (gramPhase ω) 2 (volume.restrict (Set.Icc (-b) b)) := by
  apply MemLp.of_bound (by unfold gramPhase; fun_prop) 1
  exact Filter.Eventually.of_forall (fun t => (norm_gramPhase ω t).le)

/-- The exponential vector in the actual window Hilbert space. -/
def fourierWindowVector (b ω : ℝ) : FourierWindowSpace b :=
  (memLp_gramPhase_window b ω).toLp (gramPhase ω)

/-- The exponential vector agrees almost everywhere with its genuine
pointwise Fourier phase. -/
theorem fourierWindowVector_coeFn (b ω : ℝ) :
    (fourierWindowVector b ω : ℝ → ℂ) =ᵐ[volume.restrict (Set.Icc (-b) b)] gramPhase ω :=
  (memLp_gramPhase_window b ω).coeFn_toLp

/-- The Hilbert norm in the window space is exactly its real energy integral. -/
theorem fourierWindowSpace_norm_sq (b : ℝ) (f : FourierWindowSpace b) :
    ‖f‖ ^ 2 = ∫ t : ℝ in Set.Icc (-b) b, ‖f t‖ ^ 2 := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), L2.inner_def]
  rw [← integral_re (L2.integrable_inner f f)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t => (norm_sq_eq_re_inner (𝕜 := ℂ) (f t)).symm)

/-- A finite linear combination of the window vectors has precisely the
energy of its pointwise exponential polynomial. -/
theorem fourierWindowVector_sum_norm_sq
    {n : ℕ} (b : ℝ) (s : Fin n → ℝ) (c : Fin n → ℂ) :
    ‖∑ i, c i • fourierWindowVector b (s i)‖ ^ 2 =
      ∫ t : ℝ in Set.Icc (-b) b, ‖gramFourierPolynomial s c t‖ ^ 2 := by
  rw [fourierWindowSpace_norm_sq]
  apply integral_congr_ae
  have hterms (i : Fin n) :
      (c i • fourierWindowVector b (s i) : FourierWindowSpace b) =ᵐ[
        volume.restrict (Set.Icc (-b) b)] fun t => c i * gramPhase (s i) t := by
    filter_upwards [Lp.coeFn_smul (c i) (fourierWindowVector b (s i)),
      fourierWindowVector_coeFn b (s i)] with t ht hv
    simp only [ht, Pi.smul_apply, smul_eq_mul, hv]
  filter_upwards [Lp.coeFn_finsetSum Finset.univ
      (fun i => c i • fourierWindowVector b (s i)), Filter.eventually_all.2 hterms] with t ht hterms
  simp only [ht, Finset.sum_apply, hterms, gramFourierPolynomial]

/-- The actual finite exponential lower inequality supplies biorthogonal
vectors in the prescribed window, with its sharp reciprocal-square-root
norm bound and no dependence on the number of frequencies. -/
theorem exists_fourierWindow_biorthogonal_of_lowerBound
    {n : ℕ} (b : ℝ) (s : Fin n → ℝ) {A : ℝ} (hA : 0 < A)
    (hlower : ∀ c : Fin n → ℂ, A * ∑ i, ‖c i‖ ^ 2 ≤
      ∫ t : ℝ in Set.Icc (-b) b, ‖gramFourierPolynomial s c t‖ ^ 2) :
    ∃ y : Fin n → FourierWindowSpace b,
      (∀ i j, inner ℂ (y i) (fourierWindowVector b (s j)) = if i = j then 1 else 0) ∧
      ∀ i, ‖y i‖ ≤ (Real.sqrt A)⁻¹ := by
  apply exists_finite_biorthogonal_of_lowerBound _ hA
  intro c
  simpa only [fourierWindowVector_sum_norm_sq] using hlower c

/-- Zero extension of an actual window Hilbert vector to the real line. -/
def fourierWindowKernel (b : ℝ) (y : FourierWindowSpace b) : ℝ → ℂ :=
  (Set.Icc (-b) b).indicator y

/-- The zero extension has pointwise support inside its prescribed interval. -/
theorem support_fourierWindowKernel_subset (b : ℝ) (y : FourierWindowSpace b) :
    Function.support (fourierWindowKernel b y) ⊆ Set.Icc (-b) b :=
  Set.support_indicator_subset

/-- The zero-extended window vector is a genuine globally integrable kernel. -/
theorem integrable_fourierWindowKernel (b : ℝ) (y : FourierWindowSpace b) :
    Integrable (fourierWindowKernel b y) := by
  apply (integrable_indicator_iff measurableSet_Icc).2
  exact MemLp.integrable (by norm_num : (1 : ENNReal) ≤ 2) (Lp.memLp y)

/-- The zero-extended window vector is square-integrable on the real line. -/
theorem memLp_fourierWindowKernel (b : ℝ) (y : FourierWindowSpace b) :
    MemLp (fourierWindowKernel b y) 2 volume :=
  (memLp_indicator_iff_restrict measurableSet_Icc).2 (Lp.memLp y)

/-- On the real line mathlib's Fourier transform uses the exact negative
`2π` phase appearing in the biorthogonal kernel construction. -/
theorem fourier_eq_integral_gramPhase (f : ℝ → ℂ) (ω : ℝ) :
    FourierTransform.fourier f ω = ∫ t : ℝ, gramPhase (-ω) t * f t := by
  rw [Real.fourier_eq']
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  simp only [smul_eq_mul, gramPhase, RCLike.inner_apply, conj_trivial]
  congr 2
  push_cast
  ring

/-- Fourier evaluation of the actual zero-extended kernel equals pairing
against the corresponding window exponential. -/
theorem fourier_fourierWindowKernel (b : ℝ) (y : FourierWindowSpace b) (ω : ℝ) :
    FourierTransform.fourier (fourierWindowKernel b y) ω =
      inner ℂ (fourierWindowVector b ω) y := by
  rw [fourier_eq_integral_gramPhase]
  have hpoint : (fun t => gramPhase (-ω) t * fourierWindowKernel b y t) =
      (Set.Icc (-b) b).indicator (fun t => gramPhase (-ω) t * y t) := by
    ext t
    by_cases ht : t ∈ Set.Icc (-b) b <;> simp [fourierWindowKernel, ht]
  rw [hpoint, integral_indicator measurableSet_Icc, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [fourierWindowVector_coeFn b ω] with t ht
  rw [ht]
  simp only [RCLike.inner_apply, gramPhase_neg_left, mul_comm]

/-- The `L¹` mass of a window Hilbert vector is controlled by the square
root of the window length times its Hilbert norm. -/
theorem integral_norm_fourierWindowKernel_sq_le
    {b : ℝ} (hb : 0 < b) (y : FourierWindowSpace b) :
    (∫ t : ℝ, ‖fourierWindowKernel b y t‖) ^ 2 ≤ 2 * b * ‖y‖ ^ 2 := by
  have hconv : ConvexOn ℝ Set.univ (fun x : ℝ => x ^ 2) := even_two.convexOn_pow
  have hzero : volume (Set.Icc (-b) b) ≠ 0 := by
    rw [Real.volume_Icc, ne_eq, ENNReal.ofReal_eq_zero]
    linarith
  have htop : volume (Set.Icc (-b) b) ≠ ⊤ := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have hyint := MemLp.integrable (by norm_num : (1 : ENNReal) ≤ 2) (Lp.memLp y)
  have hj := hconv.map_set_average_le (by fun_prop) isClosed_univ hzero htop
    (Filter.Eventually.of_forall (fun t => Set.mem_univ ‖y t‖)) hyint.norm
    (Lp.memLp y).integrable_norm_pow'
  simp only [setAverage_eq, Real.volume_real_Icc_of_le (by linarith : -b ≤ b),
    sub_neg_eq_add, ← two_mul, smul_eq_mul,
    ← fourierWindowSpace_norm_sq] at hj
  have hnorm : (fun t => ‖fourierWindowKernel b y t‖) =
      (Set.Icc (-b) b).indicator (fun t => ‖y t‖) := by
    ext t
    by_cases ht : t ∈ Set.Icc (-b) b <;> simp [fourierWindowKernel, ht]
  rw [hnorm, integral_indicator measurableSet_Icc]
  have hmul := mul_le_mul_of_nonneg_left hj (sq_nonneg (2 * b))
  have heq : (2 * b) ^ 2 * ((2 * b)⁻¹ *
      ∫ t : ℝ in Set.Icc (-b) b, ‖y t‖) ^ 2 =
        (∫ t : ℝ in Set.Icc (-b) b, ‖y t‖) ^ 2 := by field_simp
  have heq' : (2 * b) ^ 2 * ((2 * b)⁻¹ * ‖y‖ ^ 2) = 2 * b * ‖y‖ ^ 2 := by
    field_simp
  rwa [heq, heq'] at hmul

/-- Genuine compactly supported finite interpolation kernels.  Their
Fourier values are exactly Kronecker delta values, and their uniform `L¹`
mass bound depends only on the actual window lower constant and width. -/
theorem exists_supported_fourier_biorthogonal_of_lowerBound
    {n : ℕ} {b : ℝ} (hb : 0 < b) (s : Fin n → ℝ) {A : ℝ} (hA : 0 < A)
    (hlower : ∀ c : Fin n → ℂ, A * ∑ i, ‖c i‖ ^ 2 ≤
      ∫ t : ℝ in Set.Icc (-b) b, ‖gramFourierPolynomial s c t‖ ^ 2) :
    ∃ ψ : Fin n → ℝ → ℂ,
      (∀ i, Integrable (ψ i)) ∧ (∀ i, MemLp (ψ i) 2 volume) ∧
      (∀ i, Function.support (ψ i) ⊆ Set.Icc (-b) b) ∧
      (∀ i j, FourierTransform.fourier (ψ i) (s j) = if i = j then 1 else 0) ∧
      ∀ i, (∫ t : ℝ, ‖ψ i t‖) ^ 2 ≤ 2 * b / A := by
  obtain ⟨y, hy, hynorm⟩ := exists_fourierWindow_biorthogonal_of_lowerBound b s hA hlower
  refine ⟨fun i => fourierWindowKernel b (y i),
    fun i => integrable_fourierWindowKernel b (y i),
    fun i => memLp_fourierWindowKernel b (y i),
    fun i => support_fourierWindowKernel_subset b (y i), ?_, ?_⟩
  · intro i j
    rw [fourier_fourierWindowKernel, ← inner_conj_symm, hy]
    split_ifs <;> simp
  · intro i
    have h := integral_norm_fourierWindowKernel_sq_le hb (y i)
    have hsquare := (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 (hynorm i)
    have hsqrt : (Real.sqrt A)⁻¹ ^ 2 = A⁻¹ := by rw [inv_pow, Real.sq_sqrt hA.le]
    rw [hsqrt] at hsquare
    exact h.trans (by simpa only [div_eq_mul_inv] using
      mul_le_mul_of_nonneg_left hsquare (by positivity : 0 ≤ 2 * b))

/-- Complex convolution used for the actual compact-support kernel product. -/
def fourierKernelConvolution (f g : ℝ → ℂ) : ℝ → ℂ :=
  convolution f g (ContinuousLinearMap.mul ℂ ℂ) volume

/-- The convolution of two integrable interpolation kernels is integrable. -/
theorem integrable_fourierKernelConvolution {f g : ℝ → ℂ}
    (hf : Integrable f) (hg : Integrable g) : Integrable (fourierKernelConvolution f g) :=
  hf.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hg

/-- Kernel convolution uses exactly the sum of the two support half-widths. -/
theorem support_fourierKernelConvolution_subset {f g : ℝ → ℂ} {a b : ℝ}
    (hf : Function.support f ⊆ Set.Icc (-a) a)
    (hg : Function.support g ⊆ Set.Icc (-b) b) :
    Function.support (fourierKernelConvolution f g) ⊆ Set.Icc (-(a + b)) (a + b) := by
  intro x hx
  have h := support_convolution_subset (ContinuousLinearMap.mul ℂ ℂ) hx
  obtain ⟨u, hu, v, hv, rfl⟩ := h
  have hu' := hf hu
  have hv' := hg hv
  constructor <;> linarith [hu'.1, hu'.2, hv'.1, hv'.2]

/-- The `L¹` mass of complex convolution is at most the product of the
two input masses. -/
theorem integral_norm_fourierKernelConvolution_le {f g : ℝ → ℂ}
    (hf : Integrable f) (hg : Integrable g) :
    (∫ x : ℝ, ‖fourierKernelConvolution f g x‖) ≤
      (∫ x : ℝ, ‖f x‖) * ∫ x : ℝ, ‖g x‖ := by
  have hprod := hf.norm.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hg.norm
  calc
    _ ≤ ∫ x : ℝ, ∫ t : ℝ, ‖f t‖ * ‖g (x - t)‖ := by
      apply integral_mono (integrable_fourierKernelConvolution hf hg).norm hprod.integral_prod_left
      intro x
      simpa only [fourierKernelConvolution, convolution_def, ContinuousLinearMap.mul_apply',
        Complex.norm_mul] using norm_integral_le_integral_norm (fun t => f t * g (x - t))
    _ = ∫ t : ℝ, ∫ x : ℝ, ‖f t‖ * ‖g (x - t)‖ := integral_integral_swap hprod
    _ = _ := by
      have hshift (t : ℝ) : (∫ x : ℝ, ‖g (x - t)‖) = ∫ x : ℝ, ‖g x‖ :=
        integral_sub_right_eq_self (fun x => ‖g x‖) t
      simp_rw [integral_const_mul, hshift, integral_mul_const]

/-- The Fourier transform of the actual kernel convolution is the product
of the two Fourier transforms in the same negative-`2π` convention. -/
theorem fourier_fourierKernelConvolution {f g : ℝ → ℂ}
    (hf : Integrable f) (hg : Integrable g) (ω : ℝ) :
    FourierTransform.fourier (fourierKernelConvolution f g) ω =
      FourierTransform.fourier f ω * FourierTransform.fourier g ω :=
  Real.fourier_mul_convolution_eq hf hg ω

/-- Iterated genuine convolution of a nonempty finite family of kernels.
The singleton case is its input kernel, with no fictitious integrable
convolution identity introduced for an empty family. -/
def finiteFourierKernelConvolution : (m : ℕ) → (Fin (m + 1) → ℝ → ℂ) → ℝ → ℂ
  | 0, f => f 0
  | m + 1, f => fourierKernelConvolution (f 0) (finiteFourierKernelConvolution m (fun i => f i.succ))

/-- Finite convolution preserves global integrability. -/
theorem integrable_finiteFourierKernelConvolution (m : ℕ) (f : Fin (m + 1) → ℝ → ℂ)
    (hf : ∀ i, Integrable (f i)) : Integrable (finiteFourierKernelConvolution m f) := by
  induction m with
  | zero => exact hf 0
  | succ m ih => exact integrable_fourierKernelConvolution (hf 0) (ih _ (fun i => hf i.succ))

/-- The finite convolution support obeys the exact additive interval budget. -/
theorem support_finiteFourierKernelConvolution_subset
    (m : ℕ) (f : Fin (m + 1) → ℝ → ℂ) (b : Fin (m + 1) → ℝ)
    (hf : ∀ i, Function.support (f i) ⊆ Set.Icc (-(b i)) (b i)) :
    Function.support (finiteFourierKernelConvolution m f) ⊆
      Set.Icc (-(∑ i, b i)) (∑ i, b i) := by
  induction m with
  | zero => simpa [finiteFourierKernelConvolution] using hf 0
  | succ m ih =>
    simpa only [finiteFourierKernelConvolution, Fin.sum_univ_succ] using
      support_fourierKernelConvolution_subset (hf 0) (ih _ _ (fun i => hf i.succ))

/-- The Fourier transform of a finite convolution is the exact finite
product, so the individual interpolation zeros are all preserved. -/
theorem fourier_finiteFourierKernelConvolution
    (m : ℕ) (f : Fin (m + 1) → ℝ → ℂ) (hf : ∀ i, Integrable (f i)) (ω : ℝ) :
    FourierTransform.fourier (finiteFourierKernelConvolution m f) ω =
      ∏ i, FourierTransform.fourier (f i) ω := by
  induction m with
  | zero => simp [finiteFourierKernelConvolution]
  | succ m ih =>
    rw [Fin.prod_univ_succ (fun i : Fin (m + 1 + 1) => FourierTransform.fourier (f i) ω),
      finiteFourierKernelConvolution,
      fourier_fourierKernelConvolution (hf 0)
        (integrable_finiteFourierKernelConvolution _ _ (fun i => hf i.succ)),
      ih _ (fun i => hf i.succ)]

/-- The `L¹` mass of a finite convolution is bounded by the product of the
individual masses, with no cardinality-dependent loss. -/
theorem integral_norm_finiteFourierKernelConvolution_le
    (m : ℕ) (f : Fin (m + 1) → ℝ → ℂ) (hf : ∀ i, Integrable (f i)) :
    (∫ x : ℝ, ‖finiteFourierKernelConvolution m f x‖) ≤
      ∏ i, ∫ x : ℝ, ‖f i x‖ := by
  induction m with
  | zero => simp [finiteFourierKernelConvolution]
  | succ m ih =>
    rw [finiteFourierKernelConvolution, Fin.prod_univ_succ]
    exact (integral_norm_fourierKernelConvolution_le (hf 0)
      (integrable_finiteFourierKernelConvolution _ _ (fun i => hf i.succ))).trans
      (mul_le_mul_of_nonneg_left (ih _ (fun i => hf i.succ))
        (integral_nonneg (fun x => norm_nonneg _)))

end

end MeyerGeneralProblem
