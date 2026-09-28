module

public import MeyerGeneralProblem.Gram.RationalDensity
public import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import all Mathlib.Analysis.Fourier.RiemannLebesgueLemma
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import all Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

@[expose] public section

/-!
# Universal Gram kernel

The kernel is the Fourier transform of the normalized positive rational
density.  This construction makes normalization, Hermitian symmetry, and
positive definiteness consequences of the integral rather than assumptions.
-/

namespace MeyerGeneralProblem

open MeasureTheory ComplexConjugate

noncomputable section

/-- The unit-modulus Fourier phase in the repository's `2π` convention. -/
def gramPhase (t η : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * t * η : ℝ) : ℂ) * Complex.I)

@[simp]
theorem gramPhase_zero_left (η : ℝ) : gramPhase 0 η = 1 := by
  simp [gramPhase]

@[simp]
theorem gramPhase_zero_right (t : ℝ) : gramPhase t 0 = 1 := by
  simp [gramPhase]

@[simp]
theorem norm_gramPhase (t η : ℝ) : ‖gramPhase t η‖ = 1 := by
  simpa [gramPhase] using Complex.norm_exp_ofReal_mul_I (2 * Real.pi * t * η)

@[simp]
theorem gramPhase_neg_left (t η : ℝ) :
    gramPhase (-t) η = conj (gramPhase t η) := by
  rw [gramPhase, gramPhase, ← Complex.exp_conj]
  apply congrArg Complex.exp
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring_nf

@[simp]
theorem gramPhase_add (s t η : ℝ) :
    gramPhase (s + t) η = gramPhase s η * gramPhase t η := by
  simp only [gramPhase, ← Complex.exp_add]
  apply congrArg Complex.exp
  push_cast
  ring

@[simp]
theorem gramPhase_sub (s t η : ℝ) :
    gramPhase (s - t) η = conj (gramPhase t η) * gramPhase s η := by
  rw [sub_eq_add_neg, gramPhase_add, gramPhase_neg_left, mul_comm]

/-- The universal same-side kernel at Hermite order `m`. -/
def universalGramKernel (m : ℕ) (t : ℝ) : ℂ :=
  ∫ η : ℝ, (gramDensity m η : ℂ) * gramPhase t η

theorem integrable_universalGramKernel_integrand {m : ℕ} (hm : 1 ≤ m) (t : ℝ) :
    Integrable (fun η : ℝ ↦ (gramDensity m η : ℂ) * gramPhase t η) := by
  apply (integrable_gramDensity hm).ofReal.mul_bdd (c := 1)
  · apply Continuous.aestronglyMeasurable
    unfold gramPhase
    fun_prop
  · exact ae_of_all _ fun η ↦ le_of_eq (norm_gramPhase t η)

/-- Normalization of the universal kernel. -/
@[simp]
theorem universalGramKernel_zero {m : ℕ} (hm : 1 ≤ m) :
    universalGramKernel m 0 = 1 := by
  simp only [universalGramKernel, gramPhase_zero_left, mul_one, integral_complex_ofReal,
    integral_gramDensity hm, Complex.ofReal_one]

/-- The universal kernel is bounded by its mass one. -/
theorem norm_universalGramKernel_le_one {m : ℕ} (hm : 1 ≤ m) (t : ℝ) :
    ‖universalGramKernel m t‖ ≤ 1 := by
  calc
    ‖universalGramKernel m t‖ ≤
        ∫ η : ℝ, ‖(gramDensity m η : ℂ) * gramPhase t η‖ := by
      exact norm_integral_le_integral_norm _
    _ = ∫ η : ℝ, gramDensity m η := by
      apply integral_congr_ae
      filter_upwards with η
      rw [Complex.norm_mul, norm_gramPhase, mul_one, Complex.norm_real,
        Real.norm_of_nonneg (gramDensity_nonneg hm η)]
    _ = 1 := integral_gramDensity hm

/-- Identification with mathlib's Fourier transform, evaluated at the
opposite frequency because `gramPhase` uses the positive sign convention. -/
theorem universalGramKernel_eq_fourier {m : ℕ} (t : ℝ) :
    universalGramKernel m t =
      FourierTransform.fourier (fun η : ℝ ↦ (gramDensity m η : ℂ)) (-t) := by
  rw [universalGramKernel, Real.fourier_eq']
  apply integral_congr_ae
  filter_upwards with η
  unfold gramPhase
  rw [smul_eq_mul, mul_comm]
  apply congrArg (fun z : ℂ ↦ z * (gramDensity m η : ℂ))
  apply congrArg Complex.exp
  simp only [RCLike.inner_apply, conj_trivial]
  push_cast
  ring

/-- The universal kernel is continuous. -/
theorem continuous_universalGramKernel {m : ℕ} (hm : 1 ≤ m) :
    Continuous (universalGramKernel m) := by
  have hfourier : Continuous
      (FourierTransform.fourier (fun η : ℝ ↦ (gramDensity m η : ℂ))) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ (integrable_gramDensity hm).ofReal
  have hfun : universalGramKernel m = fun t : ℝ ↦
      FourierTransform.fourier (fun η : ℝ ↦ (gramDensity m η : ℂ)) (-t) :=
    funext universalGramKernel_eq_fourier
  rw [hfun]
  exact hfourier.comp continuous_neg

/-- Riemann--Lebesgue decay of the universal kernel at spatial infinity. -/
theorem universalGramKernel_tendsto_zero_cocompact (m : ℕ) :
    Filter.Tendsto (universalGramKernel m) (Filter.cocompact ℝ) (nhds 0) := by
  have hfourier := Real.zero_at_infty_fourier
    (fun η : ℝ ↦ (gramDensity m η : ℂ))
  have hneg := hfourier.comp
    (Homeomorph.neg ℝ).toCocompactMap.cocompact_tendsto'
  have hfun : universalGramKernel m = fun t : ℝ ↦
      FourierTransform.fourier (fun η : ℝ ↦ (gramDensity m η : ℂ)) (-t) :=
    funext universalGramKernel_eq_fourier
  rw [hfun]
  change Filter.Tendsto
    ((FourierTransform.fourier (fun η : ℝ ↦ (gramDensity m η : ℂ))) ∘
      fun t : ℝ ↦ -t) (Filter.cocompact ℝ) (nhds 0)
  exact hneg

/-- Hermitian symmetry of the universal kernel. -/
theorem universalGramKernel_neg (m : ℕ) (t : ℝ) :
    universalGramKernel m (-t) = conj (universalGramKernel m t) := by
  rw [universalGramKernel, universalGramKernel, ← integral_conj]
  apply integral_congr_ae
  filter_upwards with η
  rw [map_mul, Complex.conj_ofReal, gramPhase_neg_left]

/-- A finite Fourier polynomial used to expose the Gram quadratic form. -/
def gramFourierPolynomial {n : ℕ} (x : Fin n → ℝ) (c : Fin n → ℂ) (η : ℝ) : ℂ :=
  ∑ i, c i * gramPhase (x i) η

theorem continuous_gramFourierPolynomial {n : ℕ} (x : Fin n → ℝ) (c : Fin n → ℂ) :
    Continuous (gramFourierPolynomial x c) := by
  unfold gramFourierPolynomial
  apply continuous_finsetSum
  intro i _hi
  apply continuous_const.mul
  unfold gramPhase
  fun_prop

theorem norm_gramFourierPolynomial_le {n : ℕ} (x : Fin n → ℝ) (c : Fin n → ℂ)
    (η : ℝ) :
    ‖gramFourierPolynomial x c η‖ ≤ ∑ i, ‖c i‖ := by
  calc
    ‖gramFourierPolynomial x c η‖ ≤ ∑ i, ‖c i * gramPhase (x i) η‖ :=
      norm_sum_le _ _
    _ = ∑ i, ‖c i‖ := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [norm_mul, norm_gramPhase, mul_one]

theorem integrable_gramDensity_mul_fourierPolynomial_sq {m n : ℕ} (hm : 1 ≤ m)
    (x : Fin n → ℝ) (c : Fin n → ℂ) :
    Integrable (fun η : ℝ ↦ (gramDensity m η : ℂ) *
      (conj (gramFourierPolynomial x c η) * gramFourierPolynomial x c η)) := by
  let C : ℝ := ∑ i, ‖c i‖
  have hzcont := continuous_gramFourierPolynomial x c
  have hzbound : ∀ η, ‖gramFourierPolynomial x c η‖ ≤ C :=
    fun η ↦ norm_gramFourierPolynomial_le x c η
  have hfirst : Integrable (fun η : ℝ ↦
      (gramDensity m η : ℂ) * conj (gramFourierPolynomial x c η)) := by
    apply (integrable_gramDensity hm).ofReal.mul_bdd (c := C)
    · exact (by fun_prop : Continuous
        (fun η : ℝ ↦ conj (gramFourierPolynomial x c η))).aestronglyMeasurable
    · exact ae_of_all _ fun η ↦ by simpa using hzbound η
  have hsecond := hfirst.mul_bdd
    (continuous_gramFourierPolynomial x c).aestronglyMeasurable
    (ae_of_all _ hzbound)
  simpa only [mul_assoc] using hsecond

/-- Positive definiteness in the concrete finite-matrix sense needed for Gram
operators.  The index order is chosen so the quadratic form is `conj cᵢ cⱼ`.
-/
def KernelPositiveDefinite (K : ℝ → ℂ) : Prop :=
  ∀ (n : ℕ) (x : Fin n → ℝ) (c : Fin n → ℂ),
    0 ≤ (∑ i, ∑ j, conj (c i) * c j * K (x j - x i)).re

theorem universalGramKernel_quadratic_eq_integral {m n : ℕ} (hm : 1 ≤ m)
    (x : Fin n → ℝ) (c : Fin n → ℂ) :
    (∑ i, ∑ j, conj (c i) * c j * universalGramKernel m (x j - x i)) =
      ∫ η : ℝ, (gramDensity m η : ℂ) *
        (conj (gramFourierPolynomial x c η) * gramFourierPolynomial x c η) := by
  calc
    (∑ i, ∑ j, conj (c i) * c j * universalGramKernel m (x j - x i)) =
        ∑ i, ∑ j, ∫ η : ℝ,
          (conj (c i) * c j) *
            ((gramDensity m η : ℂ) * gramPhase (x j - x i) η) := by
      apply Finset.sum_congr rfl
      intro i _hi
      apply Finset.sum_congr rfl
      intro j _hj
      rw [universalGramKernel, integral_const_mul]
    _ = ∑ i, ∫ η : ℝ, ∑ j,
          (conj (c i) * c j) *
            ((gramDensity m η : ℂ) * gramPhase (x j - x i) η) := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact (integral_finsetSum Finset.univ (fun j _hj ↦
        (integrable_universalGramKernel_integrand hm _).const_mul _)).symm
    _ = ∫ η : ℝ, ∑ i, ∑ j,
          (conj (c i) * c j) *
            ((gramDensity m η : ℂ) * gramPhase (x j - x i) η) := by
      exact (integral_finsetSum Finset.univ (fun i _hi ↦
        integrable_finsetSum Finset.univ (fun j _hj ↦
          (integrable_universalGramKernel_integrand hm _).const_mul _))).symm
    _ = ∫ η : ℝ, (gramDensity m η : ℂ) *
        (conj (gramFourierPolynomial x c η) * gramFourierPolynomial x c η) := by
      apply integral_congr_ae
      filter_upwards with η
      unfold gramFourierPolynomial
      calc
        (∑ i, ∑ j, (conj (c i) * c j) *
            ((gramDensity m η : ℂ) * gramPhase (x j - x i) η)) =
            ∑ i, ∑ j, (gramDensity m η : ℂ) *
              (conj (c i * gramPhase (x i) η) *
                (c j * gramPhase (x j) η)) := by
          apply Finset.sum_congr rfl
          intro i _hi
          apply Finset.sum_congr rfl
          intro j _hj
          rw [gramPhase_sub, map_mul]
          ring
        _ = (gramDensity m η : ℂ) *
            ((∑ i, conj (c i * gramPhase (x i) η)) *
              ∑ j, c j * gramPhase (x j) η) := by
          rw [Fintype.sum_mul_sum]
          simp only [Finset.mul_sum]
        _ = (gramDensity m η : ℂ) *
            (conj (∑ i, c i * gramPhase (x i) η) *
              ∑ j, c j * gramPhase (x j) η) := by
          rw [map_sum]

/-- Real-valued energy form of the universal Gram quadratic identity. -/
theorem universalGramKernel_quadratic_re_eq_integral {m n : ℕ} (hm : 1 ≤ m)
    (x : Fin n → ℝ) (c : Fin n → ℂ) :
    (∑ i, ∑ j, conj (c i) * c j *
        universalGramKernel m (x j - x i)).re =
      ∫ η : ℝ, gramDensity m η * ‖gramFourierPolynomial x c η‖ ^ 2 := by
  rw [universalGramKernel_quadratic_eq_integral hm x c]
  have hf := integrable_gramDensity_mul_fourierPolynomial_sq hm x c
  calc
    (∫ η : ℝ, (gramDensity m η : ℂ) *
        (conj (gramFourierPolynomial x c η) *
          gramFourierPolynomial x c η)).re =
        ∫ η : ℝ, ((gramDensity m η : ℂ) *
          (conj (gramFourierPolynomial x c η) *
            gramFourierPolynomial x c η)).re := (integral_re hf).symm
    _ = ∫ η : ℝ, gramDensity m η *
        ‖gramFourierPolynomial x c η‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards with η
      rw [← Complex.normSq_eq_conj_mul_self]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
        sub_zero, Complex.normSq_eq_norm_sq]

/-- Restricting the universal Gram energy to `[-a,a]` and using the exact
rational-density floor gives the analytic half of the Ingham lower bound. -/
theorem universalGramKernel_quadratic_re_ge_window
    {m n : ℕ} (hm : 1 ≤ m) (x : Fin n → ℝ) (c : Fin n → ℂ)
    (a : ℝ) :
    2 * gramNormalization m * (1 + 4 * a ^ 2)⁻¹ ^ (2 * m) *
        (∫ η : ℝ in Set.Icc (-a) a,
          ‖gramFourierPolynomial x c η‖ ^ 2) ≤
      (∑ i, ∑ j, conj (c i) * c j *
        universalGramKernel m (x j - x i)).re := by
  let w : ℝ :=
    2 * gramNormalization m * (1 + 4 * a ^ 2)⁻¹ ^ (2 * m)
  let energy : ℝ → ℝ := fun η ↦ ‖gramFourierPolynomial x c η‖ ^ 2
  let weighted : ℝ → ℝ := fun η ↦ gramDensity m η * energy η
  have henergy_cont : Continuous energy := by
    dsimp [energy]
    exact (continuous_gramFourierPolynomial x c).norm.pow 2
  have henergy_int : IntegrableOn energy (Set.Icc (-a) a) := by
    have hcompact : IsCompact (Set.Icc (-a) a) := isCompact_Icc
    exact ContinuousOn.integrableOn_compact hcompact henergy_cont.continuousOn
  have hw₀ : 0 ≤ w := by
    dsimp [w]
    exact mul_nonneg
      (mul_nonneg (by norm_num) (gramNormalization_pos hm).le)
      (pow_nonneg (inv_nonneg.mpr (by positivity)) _)
  have hweighted_int : Integrable weighted := by
    have hf := (integrable_gramDensity_mul_fourierPolynomial_sq hm x c).re
    convert hf using 1
    funext η
    dsimp [weighted, energy]
    rw [← Complex.normSq_eq_conj_mul_self]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      sub_zero, Complex.normSq_eq_norm_sq]
  have hwindow :
      ∫ η : ℝ in Set.Icc (-a) a, w * energy η ≤
        ∫ η : ℝ in Set.Icc (-a) a, weighted η := by
    apply integral_mono_ae
      (MeasureTheory.Integrable.const_mul henergy_int w)
      hweighted_int.integrableOn
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with η hη
    dsimp [weighted]
    exact mul_le_mul_of_nonneg_right
      (show w ≤ gramDensity m η by
        exact gramDensity_lower_bound_on_Icc hm hη)
      (sq_nonneg _)
  have hrestrict :
      ∫ η : ℝ in Set.Icc (-a) a, weighted η ≤ ∫ η : ℝ, weighted η := by
    apply integral_mono_measure Measure.restrict_le_self
      (ae_of_all _ fun η ↦ ?_) hweighted_int
    dsimp [weighted, energy]
    exact mul_nonneg (gramDensity_nonneg hm η) (sq_nonneg _)
  rw [universalGramKernel_quadratic_re_eq_integral hm x c]
  change w * (∫ η : ℝ in Set.Icc (-a) a, energy η) ≤ _
  calc
    w * (∫ η : ℝ in Set.Icc (-a) a, energy η) =
        ∫ η : ℝ in Set.Icc (-a) a, w * energy η := by
      rw [integral_const_mul]
    _ ≤ ∫ η : ℝ in Set.Icc (-a) a, weighted η := hwindow
    _ ≤ ∫ η : ℝ, weighted η := hrestrict

/-- Any finite window-energy floor transfers to the universal Gram form with
the exact rational-density multiplier. -/
theorem universalGramKernel_lowerBound_of_windowFloor
    {m n : ℕ} (hm : 1 ≤ m) (x : Fin n → ℝ) (c : Fin n → ℂ)
    (a L : ℝ)
    (hwindow :
      L * ∑ i, ‖c i‖ ^ 2 ≤
        ∫ η : ℝ in Set.Icc (-a) a,
          ‖gramFourierPolynomial x c η‖ ^ 2) :
    2 * gramNormalization m * L *
        (1 + 4 * a ^ 2)⁻¹ ^ (2 * m) * ∑ i, ‖c i‖ ^ 2 ≤
      (∑ i, ∑ j, conj (c i) * c j *
        universalGramKernel m (x j - x i)).re := by
  have hw₀ :
      0 ≤ 2 * gramNormalization m * (1 + 4 * a ^ 2)⁻¹ ^ (2 * m) := by
    exact mul_nonneg
      (mul_nonneg (by norm_num) (gramNormalization_pos hm).le)
      (pow_nonneg (inv_nonneg.mpr (by positivity)) _)
  calc
    2 * gramNormalization m * L *
          (1 + 4 * a ^ 2)⁻¹ ^ (2 * m) * ∑ i, ‖c i‖ ^ 2 =
        (2 * gramNormalization m * (1 + 4 * a ^ 2)⁻¹ ^ (2 * m)) *
          (L * ∑ i, ‖c i‖ ^ 2) := by ring
    _ ≤ (2 * gramNormalization m * (1 + 4 * a ^ 2)⁻¹ ^ (2 * m)) *
        (∫ η : ℝ in Set.Icc (-a) a,
          ‖gramFourierPolynomial x c η‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hwindow hw₀
    _ ≤ (∑ i, ∑ j, conj (c i) * c j *
        universalGramKernel m (x j - x i)).re :=
      universalGramKernel_quadratic_re_ge_window hm x c a

/-- Compatibility specialization of the generic window-floor transfer to
the classical sharp Ingham constant. -/
theorem universalGramKernel_lowerBound_of_ingham
    {m n : ℕ} (hm : 1 ≤ m) (x : Fin n → ℝ) (c : Fin n → ℂ)
    (a d : ℝ)
    (hIngham :
      (2 * a - d⁻¹) * ∑ i, ‖c i‖ ^ 2 ≤
        ∫ η : ℝ in Set.Icc (-a) a,
          ‖gramFourierPolynomial x c η‖ ^ 2) :
    2 * gramNormalization m * (2 * a - d⁻¹) *
        (1 + 4 * a ^ 2)⁻¹ ^ (2 * m) * ∑ i, ‖c i‖ ^ 2 ≤
      (∑ i, ∑ j, conj (c i) * c j *
        universalGramKernel m (x j - x i)).re :=
  universalGramKernel_lowerBound_of_windowFloor hm x c a (2 * a - d⁻¹)
    hIngham

/-- The Fourier integral of the positive rational density is positive definite. -/
theorem universalGramKernel_positiveDefinite {m : ℕ} (hm : 1 ≤ m) :
    KernelPositiveDefinite (universalGramKernel m) := by
  intro n x c
  rw [universalGramKernel_quadratic_eq_integral hm x c]
  let f : ℝ → ℂ := fun η ↦ (gramDensity m η : ℂ) *
    (conj (gramFourierPolynomial x c η) * gramFourierPolynomial x c η)
  have hf : Integrable f := integrable_gramDensity_mul_fourierPolynomial_sq hm x c
  calc
    0 ≤ ∫ η : ℝ, (f η).re := by
      apply integral_nonneg
      intro η
      dsimp [f]
      rw [← Complex.normSq_eq_conj_mul_self]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      exact mul_nonneg (gramDensity_nonneg hm η)
        (Complex.normSq_nonneg (gramFourierPolynomial x c η))
    _ = (∫ η : ℝ, f η).re := integral_re hf

end

end MeyerGeneralProblem
