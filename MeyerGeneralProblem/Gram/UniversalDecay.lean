module

public import MeyerGeneralProblem.Gram.UniversalKernel
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
import all Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.Analysis.Calculus.Deriv.Inv
import all Mathlib.Analysis.Calculus.Deriv.Inv

@[expose] public section

/-!
# Quantitative decay of the universal Gram kernel

The normalized rational density has an integrable second derivative.  Applying
the Fourier derivative identity twice gives a global quadratic envelope for
the universal Gram kernel.  Unlike qualitative Riemann--Lebesgue decay, this
envelope is summable on separated one-dimensional frequency sets and can feed
the carrier compactness Schur estimate.
-/

namespace MeyerGeneralProblem

open MeasureTheory

noncomputable section

/-- First derivative of the unnormalized rational Gram density. -/
def rawGramDensityDeriv (m : ℕ) (η : ℝ) : ℝ :=
  -16 * (m : ℝ) * η * (1 + 4 * η ^ 2)⁻¹ ^ (2 * m + 1)

theorem hasDerivAt_rawGramDensity {m : ℕ} (hm : 1 ≤ m) (η : ℝ) :
    HasDerivAt (rawGramDensity m) (rawGramDensityDeriv m η) η := by
  rw [show rawGramDensity m = fun x : ℝ =>
      (1 + 4 * x ^ 2)⁻¹ ^ (2 * m) from
    funext (rawGramDensity_eq_inv_pow m)]
  have hb : HasDerivAt (fun x : ℝ => 1 + 4 * x ^ 2) (8 * η) η := by
    convert! (hasDerivAt_const η (1 : ℝ)).add
      ((hasDerivAt_pow 2 η).const_mul (4 : ℝ)) using 1
    all_goals ring
  have hbinv := hb.inv (by positivity)
  have hcoef : ((2 * m : ℕ) : ℝ) *
      (1 + 4 * η ^ 2)⁻¹ ^ (2 * m - 1) *
        (-(8 * η) / (1 + 4 * η ^ 2) ^ 2) =
      rawGramDensityDeriv m η := by
    unfold rawGramDensityDeriv
    rw [div_eq_mul_inv, ← inv_pow]
    have hsum : 2 * m - 1 + 2 = 2 * m + 1 := by omega
    have hp : (1 + 4 * η ^ 2)⁻¹ ^ (2 * m - 1) *
        (1 + 4 * η ^ 2)⁻¹ ^ 2 =
        (1 + 4 * η ^ 2)⁻¹ ^ (2 * m + 1) := by
      rw [← pow_add, hsum]
    calc
      _ = -16 * (m : ℝ) * η *
          ((1 + 4 * η ^ 2)⁻¹ ^ (2 * m - 1) *
            (1 + 4 * η ^ 2)⁻¹ ^ 2) := by
        push_cast
        ring
      _ = _ := by rw [hp]
  have hpow := hbinv.pow (2 * m)
  change HasDerivAt (fun x : ℝ => (1 + 4 * x ^ 2)⁻¹ ^ (2 * m))
    (((2 * m : ℕ) : ℝ) * (1 + 4 * η ^ 2)⁻¹ ^ (2 * m - 1) *
      (-(8 * η) / (1 + 4 * η ^ 2) ^ 2)) η at hpow
  rw [hcoef] at hpow
  exact hpow

/-- Second derivative of the unnormalized rational Gram density. -/
def rawGramDensitySecondDeriv (m : ℕ) (η : ℝ) : ℝ :=
  -16 * (m : ℝ) * (1 + 4 * η ^ 2)⁻¹ ^ (2 * m + 1) +
    128 * (m : ℝ) * ((2 * m + 1 : ℕ) : ℝ) * η ^ 2 *
      (1 + 4 * η ^ 2)⁻¹ ^ (2 * m + 2)

theorem hasDerivAt_rawGramDensityDeriv {m : ℕ} (hm : 1 ≤ m) (η : ℝ) :
    HasDerivAt (rawGramDensityDeriv m) (rawGramDensitySecondDeriv m η) η := by
  have hb : HasDerivAt (fun x : ℝ => 1 + 4 * x ^ 2) (8 * η) η := by
    convert! (hasDerivAt_const η (1 : ℝ)).add
      ((hasDerivAt_pow 2 η).const_mul (4 : ℝ)) using 1
    all_goals ring
  have hbinv := hb.inv (by positivity)
  have hpow0 := hbinv.pow (2 * m + 1)
  have hcoef : (((2 * m + 1 : ℕ) : ℝ) *
      (1 + 4 * η ^ 2)⁻¹ ^ (2 * m + 1 - 1) *
        (-(8 * η) / (1 + 4 * η ^ 2) ^ 2)) =
      -8 * ((2 * m + 1 : ℕ) : ℝ) * η *
        (1 + 4 * η ^ 2)⁻¹ ^ (2 * m + 2) := by
    rw [show 2 * m + 1 - 1 = 2 * m by omega]
    rw [div_eq_mul_inv, ← inv_pow]
    have hp : (1 + 4 * η ^ 2)⁻¹ ^ (2 * m) *
        (1 + 4 * η ^ 2)⁻¹ ^ 2 =
        (1 + 4 * η ^ 2)⁻¹ ^ (2 * m + 2) := by
      rw [← pow_add]
    calc
      _ = -8 * ((2 * m + 1 : ℕ) : ℝ) * η *
          ((1 + 4 * η ^ 2)⁻¹ ^ (2 * m) *
            (1 + 4 * η ^ 2)⁻¹ ^ 2) := by ring
      _ = _ := by rw [hp]
  have hpow : HasDerivAt
      (fun x : ℝ => (1 + 4 * x ^ 2)⁻¹ ^ (2 * m + 1))
      (-8 * ((2 * m + 1 : ℕ) : ℝ) * η *
        (1 + 4 * η ^ 2)⁻¹ ^ (2 * m + 2)) η := by
    change HasDerivAt
      (fun x : ℝ => (1 + 4 * x ^ 2)⁻¹ ^ (2 * m + 1))
      (((2 * m + 1 : ℕ) : ℝ) *
        (1 + 4 * η ^ 2)⁻¹ ^ (2 * m + 1 - 1) *
          (-(8 * η) / (1 + 4 * η ^ 2) ^ 2)) η at hpow0
    rw [hcoef] at hpow0
    exact hpow0
  have hprod := (hasDerivAt_id η).mul hpow
  convert! hprod.const_mul (-16 * (m : ℝ)) using 1
  · funext x
    simp only [rawGramDensityDeriv, Pi.mul_apply, id_eq]
    ring
  · simp only [rawGramDensitySecondDeriv, id_eq, one_mul]
    ring

theorem continuous_rawGramDensityDeriv (m : ℕ) :
    Continuous (rawGramDensityDeriv m) := by
  have hinv : Continuous (fun η : ℝ => (1 + 4 * η ^ 2)⁻¹) :=
    (by fun_prop : Continuous (fun η : ℝ => 1 + 4 * η ^ 2)).inv₀
      (fun η => by positivity)
  unfold rawGramDensityDeriv
  exact (continuous_const.mul continuous_id).mul (hinv.pow _)

theorem continuous_rawGramDensitySecondDeriv (m : ℕ) :
    Continuous (rawGramDensitySecondDeriv m) := by
  have hinv : Continuous (fun η : ℝ => (1 + 4 * η ^ 2)⁻¹) :=
    (by fun_prop : Continuous (fun η : ℝ => 1 + 4 * η ^ 2)).inv₀
      (fun η => by positivity)
  unfold rawGramDensitySecondDeriv
  exact (continuous_const.mul (hinv.pow _)).add
    (((continuous_const.mul continuous_const).mul (continuous_id.pow _)).mul
      (hinv.pow _))

theorem norm_mul_inverseQuadratic_le_one (η : ℝ) :
    ‖η * (1 + 4 * η ^ 2)⁻¹‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_mul, abs_inv,
    abs_of_pos (show 0 < 1 + 4 * η ^ 2 by positivity)]
  rw [← div_eq_mul_inv, div_le_one (by positivity)]
  nlinarith [sq_abs η, sq_nonneg (|η| - 1)]

theorem norm_sq_mul_inverseQuadratic_sq_le_one (η : ℝ) :
    ‖η ^ 2 * (1 + 4 * η ^ 2)⁻¹ ^ 2‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_mul, abs_sq, abs_pow, abs_inv,
    abs_of_pos (show 0 < 1 + 4 * η ^ 2 by positivity)]
  rw [inv_pow, ← div_eq_mul_inv, div_le_one (by positivity)]
  nlinarith [sq_nonneg η, sq_nonneg (1 + 4 * η ^ 2)]

theorem integrable_rawGramDensityDeriv {m : ℕ} (hm : 1 ≤ m) :
    Integrable (rawGramDensityDeriv m) := by
  have hmul : Integrable (fun η : ℝ =>
      rawGramDensity m η * (η * (1 + 4 * η ^ 2)⁻¹)) :=
    (integrable_rawGramDensity hm).mul_bdd
      ((continuous_id.mul
        ((by fun_prop : Continuous (fun η : ℝ => 1 + 4 * η ^ 2)).inv₀
          (fun η => by positivity))).aestronglyMeasurable)
      (ae_of_all _ norm_mul_inverseQuadratic_le_one)
  have hconst := hmul.const_mul (-16 * (m : ℝ))
  convert hconst using 1
  funext η
  rw [rawGramDensity_eq_inv_pow]
  unfold rawGramDensityDeriv
  rw [show 2 * m + 1 = 2 * m + 1 by rfl, pow_succ]
  ring

theorem integrable_rawGramDensitySecondDeriv {m : ℕ} (hm : 1 ≤ m) :
    Integrable (rawGramDensitySecondDeriv m) := by
  have hfirstMul : Integrable (fun η : ℝ =>
      rawGramDensity m η * (1 + 4 * η ^ 2)⁻¹) :=
    (integrable_rawGramDensity hm).mul_bdd
      (((by fun_prop : Continuous (fun η : ℝ => 1 + 4 * η ^ 2)).inv₀
        (fun η => by positivity)).aestronglyMeasurable)
      (ae_of_all _ fun η => by
        rw [Real.norm_eq_abs, abs_inv,
          abs_of_pos (show 0 < 1 + 4 * η ^ 2 by positivity)]
        exact (inv_le_one₀ (by positivity)).2 (by nlinarith [sq_nonneg η]))
  have hsecondMul : Integrable (fun η : ℝ =>
      rawGramDensity m η *
        (η ^ 2 * (1 + 4 * η ^ 2)⁻¹ ^ 2)) :=
    (integrable_rawGramDensity hm).mul_bdd
      (((continuous_id.pow 2).mul
        (((by fun_prop : Continuous (fun η : ℝ => 1 + 4 * η ^ 2)).inv₀
          (fun η => by positivity)).pow 2)).aestronglyMeasurable)
      (ae_of_all _ norm_sq_mul_inverseQuadratic_sq_le_one)
  have hfirst := hfirstMul.const_mul (-16 * (m : ℝ))
  have hsecond := hsecondMul.const_mul
    (128 * (m : ℝ) * ((2 * m + 1 : ℕ) : ℝ))
  convert! hfirst.add hsecond using 1
  funext η
  simp only [Pi.add_apply]
  rw [rawGramDensity_eq_inv_pow]
  unfold rawGramDensitySecondDeriv
  rw [show 2 * m + 1 = 2 * m + 1 by rfl,
    show 2 * m + 2 = 2 * m + 2 by rfl]
  rw [pow_succ, show 2 * m + 2 = (2 * m) + 2 by omega, pow_add]
  ring

theorem deriv_complex_rawGramDensity {m : ℕ} (hm : 1 ≤ m) :
    deriv (fun η : ℝ => (rawGramDensity m η : ℂ)) =
      fun η : ℝ => (rawGramDensityDeriv m η : ℂ) := by
  funext η
  exact (hasDerivAt_rawGramDensity hm η).ofReal_comp.deriv

theorem deriv_complex_rawGramDensityDeriv {m : ℕ} (hm : 1 ≤ m) :
    deriv (fun η : ℝ => (rawGramDensityDeriv m η : ℂ)) =
      fun η : ℝ => (rawGramDensitySecondDeriv m η : ℂ) := by
  funext η
  exact (hasDerivAt_rawGramDensityDeriv hm η).ofReal_comp.deriv

theorem fourier_complex_rawGramDensity_secondDeriv {m : ℕ} (hm : 1 ≤ m)
    (t : ℝ) :
    FourierTransform.fourier
        (fun η : ℝ => (rawGramDensitySecondDeriv m η : ℂ)) t =
      (2 * Real.pi * Complex.I * t) ^ 2 *
        FourierTransform.fourier
          (fun η : ℝ => (rawGramDensity m η : ℂ)) t := by
  have hdiff0 : Differentiable ℝ
      (fun η : ℝ => (rawGramDensity m η : ℂ)) :=
    fun η => (hasDerivAt_rawGramDensity hm η).ofReal_comp.differentiableAt
  have hdiff1 : Differentiable ℝ
      (fun η : ℝ => (rawGramDensityDeriv m η : ℂ)) :=
    fun η => (hasDerivAt_rawGramDensityDeriv hm η).ofReal_comp.differentiableAt
  have hfour1 := Real.fourier_deriv
    (integrable_rawGramDensity hm).ofReal hdiff0
    (by rw [deriv_complex_rawGramDensity hm]
        exact (integrable_rawGramDensityDeriv hm).ofReal)
  have hfour2 := Real.fourier_deriv
    (integrable_rawGramDensityDeriv hm).ofReal hdiff1
    (by rw [deriv_complex_rawGramDensityDeriv hm]
        exact (integrable_rawGramDensitySecondDeriv hm).ofReal)
  rw [deriv_complex_rawGramDensity hm] at hfour1
  rw [deriv_complex_rawGramDensityDeriv hm] at hfour2
  have h1 := congrFun hfour1 t
  have h2 := congrFun hfour2 t
  rw [h2, h1]
  simp only [smul_eq_mul]
  ring

theorem universalGramKernel_eq_normalized_raw_fourier (m : ℕ) (t : ℝ) :
    universalGramKernel m t =
      (2 * gramNormalization m : ℂ) *
        FourierTransform.fourier
          (fun η : ℝ => (rawGramDensity m η : ℂ)) (-t) := by
  rw [universalGramKernel_eq_fourier]
  have hfun : (fun η : ℝ => (gramDensity m η : ℂ)) =
      (2 * gramNormalization m : ℂ) •
        (fun η : ℝ => (rawGramDensity m η : ℂ)) := by
    funext η
    simp only [gramDensity, Pi.smul_apply, smul_eq_mul]
    push_cast
    ring
  rw [hfun, Real.fourier_eq', Real.fourier_eq']
  simp only [Pi.smul_apply, smul_eq_mul]
  calc
    _ = ∫ η : ℝ, (2 * gramNormalization m : ℂ) *
        (Complex.exp
          (((-2 * Real.pi * inner ℝ η (-t) : ℝ) : ℂ) * Complex.I) *
            (rawGramDensity m η : ℂ)) := by
      apply integral_congr_ae
      filter_upwards with η
      ring
    _ = _ := by rw [integral_const_mul]

/-- The `L¹` size of the second derivative controlling Fourier decay. -/
def rawGramDensitySecondDerivL1 (m : ℕ) : ℝ :=
  ∫ η : ℝ, ‖rawGramDensitySecondDeriv m η‖

theorem rawGramDensitySecondDerivL1_nonneg (m : ℕ) :
    0 ≤ rawGramDensitySecondDerivL1 m := by
  exact integral_nonneg fun η => norm_nonneg _

theorem norm_fourier_complex_rawGramDensitySecondDeriv_le
    (m : ℕ) (t : ℝ) :
    ‖FourierTransform.fourier
        (fun η : ℝ => (rawGramDensitySecondDeriv m η : ℂ)) t‖ ≤
      rawGramDensitySecondDerivL1 m := by
  rw [Real.fourier_eq']
  calc
    ‖∫ η : ℝ, Complex.exp
          (((-2 * Real.pi * inner ℝ η t : ℝ) : ℂ) * Complex.I) •
        (rawGramDensitySecondDeriv m η : ℂ)‖ ≤
        ∫ η : ℝ, ‖Complex.exp
            (((-2 * Real.pi * inner ℝ η t : ℝ) : ℂ) * Complex.I) •
          (rawGramDensitySecondDeriv m η : ℂ)‖ :=
      norm_integral_le_integral_norm _
    _ = rawGramDensitySecondDerivL1 m := by
      unfold rawGramDensitySecondDerivL1
      apply integral_congr_ae
      filter_upwards with η
      rw [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul,
        Complex.norm_real]

theorem norm_universalGramKernel_le_secondDeriv_div_sq
    {m : ℕ} (hm : 1 ≤ m) {t : ℝ} (ht : t ≠ 0) :
    ‖universalGramKernel m t‖ ≤
      (2 * gramNormalization m * rawGramDensitySecondDerivL1 m) /
        ((2 * Real.pi) ^ 2 * t ^ 2) := by
  let z : ℂ := FourierTransform.fourier
    (fun η : ℝ => (rawGramDensity m η : ℂ)) (-t)
  let D : ℝ := (2 * Real.pi) ^ 2 * t ^ 2
  have hD : 0 < D := by
    dsimp [D]
    positivity
  have hfour := fourier_complex_rawGramDensity_secondDeriv hm (-t)
  have hnorm := congrArg norm hfour
  have hfactor :
      ‖(2 * Real.pi * Complex.I * ((-t : ℝ) : ℂ)) ^ 2‖ = D := by
    dsimp [D]
    simp only [norm_pow, norm_mul, Complex.norm_I, Complex.norm_real,
      Real.norm_eq_abs, abs_neg]
    norm_num
    rw [mul_pow, sq_abs]
  have hzmul : D * ‖z‖ ≤ rawGramDensitySecondDerivL1 m := by
    have hupper := norm_fourier_complex_rawGramDensitySecondDeriv_le m (-t)
    rw [hnorm, norm_mul, hfactor] at hupper
    change D * ‖z‖ ≤ rawGramDensitySecondDerivL1 m at hupper
    exact hupper
  have hz : ‖z‖ ≤ rawGramDensitySecondDerivL1 m / D :=
    (le_div_iff₀ hD).2 (by simpa [mul_comm] using hzmul)
  rw [universalGramKernel_eq_normalized_raw_fourier]
  change ‖(2 * gramNormalization m : ℂ) * z‖ ≤ _
  rw [norm_mul]
  have hcNorm : ‖(2 * gramNormalization m : ℂ)‖ =
      2 * gramNormalization m := by
    rw [show (2 * gramNormalization m : ℂ) =
      ((2 * gramNormalization m : ℝ) : ℂ) by
        push_cast
        norm_num]
    rw [Complex.norm_real, Real.norm_of_nonneg
      (mul_nonneg (by norm_num) (gramNormalization_pos hm).le)]
  rw [hcNorm]
  calc
    2 * gramNormalization m * ‖z‖ ≤
        2 * gramNormalization m *
          (rawGramDensitySecondDerivL1 m / D) := by
      exact mul_le_mul_of_nonneg_left hz
        (mul_nonneg (by norm_num) (gramNormalization_pos hm).le)
    _ = (2 * gramNormalization m * rawGramDensitySecondDerivL1 m) /
        ((2 * Real.pi) ^ 2 * t ^ 2) := by
      dsimp [D]
      ring

/-- Explicit constant for a globally summable quadratic envelope of the
universal Gram kernel. -/
def universalGramDecayConstant (m : ℕ) : ℝ :=
  4 * (1 +
    (2 * gramNormalization m * rawGramDensitySecondDerivL1 m) /
      (2 * Real.pi) ^ 2)

theorem universalGramDecayConstant_nonneg {m : ℕ} (hm : 1 ≤ m) :
    0 ≤ universalGramDecayConstant m := by
  unfold universalGramDecayConstant
  have hA : 0 ≤
      (2 * gramNormalization m * rawGramDensitySecondDerivL1 m) /
        (2 * Real.pi) ^ 2 := by
    exact div_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) (gramNormalization_pos hm).le)
        (rawGramDensitySecondDerivL1_nonneg m))
      (sq_nonneg _)
  positivity

/-- A summable global quadratic envelope for the universal Gram kernel. -/
theorem norm_universalGramKernel_le_inv_sq
    {m : ℕ} (hm : 1 ≤ m) (t : ℝ) :
    ‖universalGramKernel m t‖ ≤
      universalGramDecayConstant m / (1 + |t|) ^ 2 := by
  let A : ℝ :=
    (2 * gramNormalization m * rawGramDensitySecondDerivL1 m) /
      (2 * Real.pi) ^ 2
  have hA : 0 ≤ A := by
    dsimp [A]
    exact div_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) (gramNormalization_pos hm).le)
        (rawGramDensitySecondDerivL1_nonneg m))
      (sq_nonneg _)
  have hC : universalGramDecayConstant m = 4 * (1 + A) := by
    rfl
  have hden : 0 < (1 + |t|) ^ 2 := by positivity
  by_cases hsmall : |t| ≤ 1
  · have hden_le : (1 + |t|) ^ 2 ≤ 4 := by
      nlinarith [abs_nonneg t]
    have hfour_le : 4 ≤ universalGramDecayConstant m := by
      rw [hC]
      nlinarith
    have hone : 1 ≤
        universalGramDecayConstant m / (1 + |t|) ^ 2 := by
      rw [le_div_iff₀ hden]
      simpa using hden_le.trans hfour_le
    exact (norm_universalGramKernel_le_one hm t).trans hone
  · have hlarge : 1 ≤ |t| := le_of_lt (lt_of_not_ge hsmall)
    have ht : t ≠ 0 := by
      exact abs_pos.mp (lt_of_lt_of_le zero_lt_one hlarge)
    have htsq : 0 < t ^ 2 := sq_pos_of_ne_zero ht
    have hband : (1 + |t|) ^ 2 ≤ 4 * t ^ 2 := by
      have hprod : 0 ≤ (|t| - 1) * (3 * |t| + 1) :=
        mul_nonneg (sub_nonneg.mpr hlarge) (by positivity)
      nlinarith [sq_abs t]
    have hfourA :
        (2 * gramNormalization m * rawGramDensitySecondDerivL1 m) /
            ((2 * Real.pi) ^ 2 * t ^ 2) = A / t ^ 2 := by
      dsimp [A]
      field_simp [Real.pi_ne_zero, ht]
    have hCA : 4 * A ≤ universalGramDecayConstant m := by
      rw [hC]
      nlinarith
    calc
      ‖universalGramKernel m t‖ ≤
          (2 * gramNormalization m * rawGramDensitySecondDerivL1 m) /
            ((2 * Real.pi) ^ 2 * t ^ 2) :=
        norm_universalGramKernel_le_secondDeriv_div_sq hm ht
      _ = A / t ^ 2 := hfourA
      _ ≤ universalGramDecayConstant m / (1 + |t|) ^ 2 := by
        rw [div_le_div_iff₀ htsq hden]
        calc
          A * (1 + |t|) ^ 2 ≤ A * (4 * t ^ 2) :=
            mul_le_mul_of_nonneg_left hband hA
          _ = (4 * A) * t ^ 2 := by ring
          _ ≤ universalGramDecayConstant m * t ^ 2 :=
            mul_le_mul_of_nonneg_right hCA (sq_nonneg t)

/-- Existential form of the quadratic envelope, convenient for downstream
Schur-tail arguments. -/
theorem exists_norm_universalGramKernel_le_inv_sq
    {m : ℕ} (hm : 1 ≤ m) :
    ∃ C ≥ 0, ∀ t : ℝ,
      ‖universalGramKernel m t‖ ≤ C / (1 + |t|) ^ 2 :=
  ⟨universalGramDecayConstant m, universalGramDecayConstant_nonneg hm,
    norm_universalGramKernel_le_inv_sq hm⟩

end

end MeyerGeneralProblem
