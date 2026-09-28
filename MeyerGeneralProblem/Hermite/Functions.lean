module

public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import all Mathlib.Analysis.Asymptotics.SpecificAsymptotics

public import MeyerGeneralProblem.Atomic.PointMass
public import MeyerGeneralProblem.FourierNormalization
public import MeyerGeneralProblem.Hermite.Scale
public import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import all Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
public import Mathlib.RingTheory.Polynomial.Hermite.Gaussian
import all Mathlib.RingTheory.Polynomial.Hermite.Gaussian

@[expose] public section

/-!
# Concrete Hermite functions

This file starts the genuine analytic bridge between the abstract normalized
coefficient model in `Hermite.Scale` and tempered distributions.  It bundles
polynomially weighted complex Gaussians as Schwartz functions and then defines
the standard Fourier-compatible Hermite functions

`2^(1/4) / sqrt(n!) * He_n(2 * sqrt(pi) * x) * exp(-pi * x^2)`.

Here `He_n` is mathlib's probabilists' Hermite polynomial.  The scaling is the
one for which the real Fourier transform with kernel `exp(-2*pi*i*x*xi)` has
eigenvalue `(-i)^n`; the Fourier theorem and the coefficient summability needed
for Dirac masses are deliberately proved in later bridge modules.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter Function Set
open scoped ContDiff Topology

/-- The polynomial multiplying a Gaussian after `n` real derivatives.

If `g x = exp (-b * x^2)`, differentiation sends `P * g` to
`(P' - 2 * b * X * P) * g`.
-/
def gaussianDerivativePolynomial (b : ℂ) : ℕ → Polynomial ℂ → Polynomial ℂ
  | 0, P => P
  | n + 1, P =>
      (gaussianDerivativePolynomial b n P).derivative -
        Polynomial.C (2 * b) * Polynomial.X * gaussianDerivativePolynomial b n P

private theorem hasDerivAt_polynomial_eval_real (P : Polynomial ℂ) (x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ P.eval (y : ℂ)) (P.derivative.eval (x : ℂ)) x := by
  simpa [Function.comp_def] using
    (P.hasDerivAt (x : ℂ)).comp x Complex.ofRealCLM.hasDerivAt

private theorem hasDerivAt_cexp_neg_mul_sq (b : ℂ) (x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ Complex.exp (-b * (y : ℂ) ^ 2))
      (Complex.exp (-b * (x : ℂ) ^ 2) * (-b * (2 * (x : ℂ)))) x := by
  have h : HasDerivAt (fun y : ℂ ↦ Complex.exp (-b * y ^ 2))
      (Complex.exp (-b * (x : ℂ) ^ 2) * (-b * (2 * (x : ℂ)))) (x : ℂ) := by
    simpa [Pi.pow_apply] using
      (((hasDerivAt_id (x : ℂ)).pow 2).const_mul (-b)).cexp
  simpa [Function.comp_def] using h.comp x Complex.ofRealCLM.hasDerivAt

/-- Exact formula for every real derivative of a polynomial times a complex
Gaussian. -/
theorem iteratedDeriv_polynomial_mul_cexp_neg_quadratic
    (P : Polynomial ℂ) (b : ℂ) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (fun y : ℝ ↦ P.eval (y : ℂ) * Complex.exp (-b * (y : ℂ) ^ 2)) x =
      (gaussianDerivativePolynomial b n P).eval (x : ℂ) *
        Complex.exp (-b * (x : ℂ) ^ 2) := by
  induction n generalizing x with
  | zero => simp [gaussianDerivativePolynomial]
  | succ n ih =>
      rw [iteratedDeriv_succ]
      have hfun : iteratedDeriv n
          (fun y : ℝ ↦ P.eval (y : ℂ) * Complex.exp (-b * (y : ℂ) ^ 2)) =
          fun y : ℝ ↦
            (gaussianDerivativePolynomial b n P).eval (y : ℂ) *
              Complex.exp (-b * (y : ℂ) ^ 2) := by
        funext y
        exact ih y
      rw [hfun]
      change deriv
          ((fun y : ℝ ↦ (gaussianDerivativePolynomial b n P).eval (y : ℂ)) *
            fun y : ℝ ↦ Complex.exp (-b * (y : ℂ) ^ 2)) x = _
      convert
        ((hasDerivAt_polynomial_eval_real (gaussianDerivativePolynomial b n P) x).mul
          (hasDerivAt_cexp_neg_mul_sq b x)).deriv using 1
      all_goals
        simp [gaussianDerivativePolynomial, Polynomial.eval_sub, Polynomial.eval_mul]
        ring

/-- A complex polynomial restricted to the real line has temperate growth. -/
theorem polynomial_eval_real_hasTemperateGrowth (P : Polynomial ℂ) :
    Function.HasTemperateGrowth (fun x : ℝ ↦ P.eval (x : ℂ)) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      convert hP.add hQ using 1
      ext x
      simp
  | monomial n a =>
      have hpow : Function.HasTemperateGrowth (fun x : ℝ ↦ (x : ℂ) ^ n) := by
        fun_prop
      have h := (Function.HasTemperateGrowth.const a).smul hpow
      have hfun : ((fun _ : ℝ ↦ a) • fun x : ℝ ↦ (x : ℂ) ^ n) =
          fun x : ℝ ↦ a * (x : ℂ) ^ n := by
        funext x
        simp [smul_eq_mul]
      rw [hfun] at h
      simpa only [Polynomial.eval_monomial] using h

/-- Polynomially weighted complex Gaussians, together with any additional
power of `|x|`, are bounded when the quadratic coefficient has positive real
part. -/
theorem exists_polynomial_mul_cexp_neg_quadratic_bound
    (P : Polynomial ℂ) {b : ℂ} (hb : 0 < b.re) (k : ℕ) :
    ∃ C : ℝ, ∀ x : ℝ,
      |x| ^ k * ‖P.eval (x : ℂ) * Complex.exp (-b * (x : ℂ) ^ 2)‖ ≤ C := by
  obtain ⟨d, C, _hC, hP⟩ :=
    (polynomial_eval_real_hasTemperateGrowth P).norm_iteratedFDeriv_le_uniform 0
  have hP0 (x : ℝ) : ‖P.eval (x : ℂ)‖ ≤ C * (1 + |x|) ^ d := by
    simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hP 0 le_rfl x
  let H : ℝ → ℝ := fun x ↦
    |x| ^ k * ‖P.eval (x : ℂ) * Complex.exp (-b * (x : ℂ) ^ 2)‖
  let B : ℝ → ℝ := fun x ↦ |x| ^ (k + d) * Real.exp (-b.re * x ^ 2)
  have hB : Tendsto B (cocompact ℝ) (nhds 0) := by
    simpa only [B, ← Real.rpow_natCast, Nat.cast_add] using
      tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact hb (k + d : ℝ)
  have hO : H =O[cocompact ℝ] B := by
    apply Asymptotics.IsBigO.of_bound (C * 2 ^ d)
    filter_upwards
      [tendsto_norm_cocompact_atTop.eventually (eventually_ge_atTop (1 : ℝ))] with x hx
    have hx' : 1 + |x| ≤ 2 * |x| := by
      rw [Real.norm_eq_abs] at hx
      linarith
    have hraw : H x ≤ (C * 2 ^ d) * B x := by
      calc
        H x = |x| ^ k * ‖P.eval (x : ℂ)‖ * Real.exp (-b.re * x ^ 2) := by
          simp only [H, norm_mul, norm_cexp_neg_mul_sq]
          ring
        _ ≤ |x| ^ k * (C * (1 + |x|) ^ d) * Real.exp (-b.re * x ^ 2) := by
          gcongr
          exact hP0 x
        _ ≤ |x| ^ k * (C * (2 * |x|) ^ d) * Real.exp (-b.re * x ^ 2) := by
          gcongr
        _ = (C * 2 ^ d) * B x := by
          simp only [B, mul_pow, pow_add]
          ring
    simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ H x),
      abs_of_nonneg (by positivity : 0 ≤ B x)] using hraw
  have hH : Tendsto H (cocompact ℝ) (nhds 0) := hO.trans_tendsto hB
  have hHcont : Continuous H := by
    fun_prop
  have hHbounded : Bornology.IsBounded (Set.range H) :=
    hHcont.isBounded_range_iff_isBigO.mpr (hH.isBigO_one ℝ)
  obtain ⟨M, hM⟩ := hHbounded.exists_norm_le
  refine ⟨M, fun x ↦ ?_⟩
  have hxM := hM (H x) ⟨x, rfl⟩
  simpa only [H, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ H x)] using hxM

/-- A polynomial times `exp (-b*x^2)`, for `re b > 0`, as a bundled
Schwartz function. -/
def polynomialGaussian (P : Polynomial ℂ) (b : ℂ) (hb : 0 < b.re) : SchwartzMap ℝ ℂ where
  toFun x := P.eval (x : ℂ) * Complex.exp (-b * (x : ℂ) ^ 2)
  smooth' := by
    have hG : ContDiff ℝ ∞ (fun x : ℝ ↦ Complex.exp (-b * (x : ℂ) ^ 2)) := by
      have hOfReal : ContDiff ℝ ∞ (fun x : ℝ ↦ (x : ℂ)) := Complex.ofRealCLM.contDiff
      fun_prop
    exact (polynomial_eval_real_hasTemperateGrowth P).1.mul hG
  decay' k n := by
    obtain ⟨C, hC⟩ :=
      exists_polynomial_mul_cexp_neg_quadratic_bound
        (gaussianDerivativePolynomial b n P) hb k
    refine ⟨C, fun x ↦ ?_⟩
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,
      iteratedDeriv_polynomial_mul_cexp_neg_quadratic]
    simpa only [Real.norm_eq_abs] using hC x

@[simp]
theorem polynomialGaussian_apply (P : Polynomial ℂ) (b : ℂ)
    (hb : 0 < b.re) (x : ℝ) :
    polynomialGaussian P b hb x =
      P.eval (x : ℂ) * Complex.exp (-b * (x : ℂ) ^ 2) :=
  rfl

/-- Exact derivative formula for a bundled polynomial Gaussian. -/
theorem iteratedDeriv_polynomialGaussian (P : Polynomial ℂ) (b : ℂ)
    (hb : 0 < b.re) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (polynomialGaussian P b hb) x =
      (gaussianDerivativePolynomial b n P).eval (x : ℂ) *
        Complex.exp (-b * (x : ℂ) ^ 2) :=
  iteratedDeriv_polynomial_mul_cexp_neg_quadratic P b n x

/-- The probabilists' Hermite polynomial with coefficients promoted to `ℂ`. -/
def complexHermitePolynomial (n : ℕ) : Polynomial ℂ :=
  (Polynomial.hermite n).map (Int.castRingHom ℂ)

theorem complexHermitePolynomial_succ (n : ℕ) :
    complexHermitePolynomial (n + 1) =
      Polynomial.X * complexHermitePolynomial n -
        (complexHermitePolynomial n).derivative := by
  unfold complexHermitePolynomial
  rw [Polynomial.hermite_succ]
  simp

/-- The polynomial `He_n(2 * sqrt(pi) * x)` in the Fourier-compatible
Hermite function. -/
def scaledHermitePolynomial (n : ℕ) : Polynomial ℂ :=
  (complexHermitePolynomial n).comp
    (Polynomial.C (2 * Real.sqrt Real.pi : ℂ) * Polynomial.X)

/-- The scaled Hermite polynomials satisfy the creation recurrence adapted to
the `exp(-pi*x^2)` Gaussian. -/
theorem scaledHermitePolynomial_succ (n : ℕ) :
    scaledHermitePolynomial (n + 1) =
      Polynomial.C (2 * Real.sqrt Real.pi : ℂ) * Polynomial.X *
          scaledHermitePolynomial n -
        Polynomial.C (2 * Real.sqrt Real.pi : ℂ)⁻¹ *
          (scaledHermitePolynomial n).derivative := by
  apply Polynomial.funext
  intro x
  rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X,
    scaledHermitePolynomial, Polynomial.eval_comp,
    complexHermitePolynomial_succ, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_X]
  simp only [scaledHermitePolynomial, Polynomial.derivative_comp,
    Polynomial.derivative_mul, Polynomial.derivative_C,
    Polynomial.derivative_X, zero_mul, zero_add,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_one, Polynomial.eval_comp]
  have hsqrt : (Real.sqrt Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 Real.pi_pos).ne'
  field_simp

/-- The unnormalised Schwartz Hermite function
`He_n(2*sqrt(pi)*x) * exp(-pi*x^2)`. -/
def hermiteFunctionCore (n : ℕ) : SchwartzMap ℝ ℂ :=
  polynomialGaussian (scaledHermitePolynomial n) (Real.pi : ℂ)
    (by simpa using Real.pi_pos)

@[simp]
theorem hermiteFunctionCore_apply (n : ℕ) (x : ℝ) :
    hermiteFunctionCore n x =
      (complexHermitePolynomial n).eval
          ((2 * Real.sqrt Real.pi * x : ℝ) : ℂ) *
        Complex.exp (-(Real.pi : ℂ) * (x : ℂ) ^ 2) := by
  simp only [hermiteFunctionCore, polynomialGaussian_apply,
    scaledHermitePolynomial, Polynomial.eval_comp, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X]
  push_cast
  ring

/-- Multiplication by the real coordinate on complex Schwartz space. -/
def coordinateMultiplicationCLM : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
  SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ))

@[simp]
theorem coordinateMultiplicationCLM_apply (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    coordinateMultiplicationCLM f x = (x : ℂ) * f x := by
  have hx : Function.HasTemperateGrowth (fun y : ℝ ↦ (y : ℂ)) := by
    fun_prop
  simp [coordinateMultiplicationCLM, hx, smul_eq_mul]

/-- The creation operator `2*pi*x - d/dx` on complex Schwartz space. -/
def hermiteCreationOperator : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
  (2 * (Real.pi : ℂ)) • coordinateMultiplicationCLM -
    SchwartzMap.derivCLM ℂ ℂ

@[simp]
theorem hermiteCreationOperator_apply (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    hermiteCreationOperator f x =
      2 * (Real.pi : ℂ) * (x : ℂ) * f x - deriv f x := by
  simp [hermiteCreationOperator, mul_assoc]

/-- Fourier transformation converts coordinate multiplication into a
derivative with the exact `2*pi` normalization. -/
theorem fourier_coordinateMultiplicationCLM (f : SchwartzMap ℝ ℂ) :
    FourierTransform.fourier (coordinateMultiplicationCLM f) =
      (Complex.I / (2 * (Real.pi : ℂ))) •
        SchwartzMap.derivCLM ℂ ℂ (FourierTransform.fourier f) := by
  have hline := SchwartzMap.lineDerivOp_fourier_eq f (1 : ℝ)
  have hreal : Function.HasTemperateGrowth (fun x : ℝ ↦ x) := by
    fun_prop
  ext x
  have hx := congrArg (fun g : SchwartzMap ℝ ℂ ↦ g x) hline
  have hx' :
      deriv (FourierTransform.fourier f : ℝ → ℂ) x =
        -(2 * (Real.pi : ℂ) * Complex.I) *
          FourierTransform.fourier (coordinateMultiplicationCLM f) x := by
    simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv,
      fderiv_apply_one_eq_deriv, smul_apply, FourierTransform.fourier_smul,
      RCLike.inner_apply, conj_trivial, one_mul, smul_eq_mul] at hx
    rw [← SchwartzMap.smulLeftCLM_ofReal ℂ hreal f] at hx
    exact hx
  change FourierTransform.fourier (coordinateMultiplicationCLM f) x =
    Complex.I / (2 * (Real.pi : ℂ)) *
      deriv (FourierTransform.fourier f : ℝ → ℂ) x
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  rw [hx']
  field_simp
  rw [Complex.I_sq]
  ring

/-- Fourier transformation converts differentiation into multiplication by
`2*pi*i*x`. -/
theorem fourier_derivCLM (f : SchwartzMap ℝ ℂ) :
    FourierTransform.fourier (SchwartzMap.derivCLM ℂ ℂ f) =
      (2 * (Real.pi : ℂ) * Complex.I) •
        coordinateMultiplicationCLM (FourierTransform.fourier f) := by
  have hline := SchwartzMap.fourier_lineDerivOp_eq f (1 : ℝ)
  have hreal : Function.HasTemperateGrowth (fun x : ℝ ↦ x) := by
    fun_prop
  have hderiv : LineDeriv.lineDerivOp (1 : ℝ) f =
      SchwartzMap.derivCLM ℂ ℂ f := by
    ext x
    simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv,
      fderiv_apply_one_eq_deriv, SchwartzMap.derivCLM_apply]
  rw [hderiv] at hline
  simp only [RCLike.inner_apply, conj_trivial, one_mul] at hline
  ext x
  have hx := congrArg (fun g : SchwartzMap ℝ ℂ ↦ g x) hline
  simp only [smul_apply,
    SchwartzMap.smulLeftCLM_apply_apply hreal,
    RCLike.real_smul_eq_coe_mul, smul_eq_mul] at hx
  rw [smul_apply, coordinateMultiplicationCLM_apply]
  simp only [smul_eq_mul]
  exact hx

/-- The Fourier transform intertwines the Hermite creation operator with the
phase `-i`. -/
theorem fourier_hermiteCreationOperator (f : SchwartzMap ℝ ℂ) :
    FourierTransform.fourier (hermiteCreationOperator f) =
      (-Complex.I) •
        hermiteCreationOperator (FourierTransform.fourier f) := by
  change FourierTransform.fourier
      ((2 * (Real.pi : ℂ)) • coordinateMultiplicationCLM f -
        SchwartzMap.derivCLM ℂ ℂ f) =
    (-Complex.I) •
      ((2 * (Real.pi : ℂ)) •
          coordinateMultiplicationCLM (FourierTransform.fourier f) -
        SchwartzMap.derivCLM ℂ ℂ (FourierTransform.fourier f))
  change FourierTransform.fourierCLM ℂ (SchwartzMap ℝ ℂ)
      ((2 * (Real.pi : ℂ)) • coordinateMultiplicationCLM f -
        SchwartzMap.derivCLM ℂ ℂ f) = _
  rw [map_sub, map_smul]
  simp only [FourierTransform.fourierCLM_apply]
  rw [fourier_coordinateMultiplicationCLM,
    fourier_derivCLM]
  ext x
  simp only [sub_apply, smul_apply, coordinateMultiplicationCLM_apply,
    smul_eq_mul]
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  field_simp
  ring

/-- The creation operator advances the concrete Hermite family. -/
theorem hermiteCreationOperator_core (n : ℕ) :
    hermiteCreationOperator (hermiteFunctionCore n) =
      (2 * Real.sqrt Real.pi : ℂ) • hermiteFunctionCore (n + 1) := by
  ext x
  rw [hermiteCreationOperator_apply]
  have hderiv :
      deriv (hermiteFunctionCore n) x =
        ((scaledHermitePolynomial n).derivative.eval (x : ℂ) -
            2 * (Real.pi : ℂ) * (x : ℂ) *
              (scaledHermitePolynomial n).eval (x : ℂ)) *
          Complex.exp (-(Real.pi : ℂ) * (x : ℂ) ^ 2) := by
    rw [← iteratedDeriv_one]
    rw [hermiteFunctionCore, iteratedDeriv_polynomialGaussian]
    simp only [gaussianDerivativePolynomial, Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  rw [hderiv]
  simp only [hermiteFunctionCore, polynomialGaussian_apply, smul_apply,
    smul_eq_mul, scaledHermitePolynomial_succ, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  have hsqrt : (Real.sqrt Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 Real.pi_pos).ne'
  have hsqrt_sq : (Real.sqrt Real.pi : ℂ) ^ 2 = (Real.pi : ℂ) := by
    exact_mod_cast Real.sq_sqrt Real.pi_pos.le
  field_simp
  rw [hsqrt_sq]
  ring

@[simp]
theorem hermiteFunctionCore_zero_apply (x : ℝ) :
    hermiteFunctionCore 0 x =
      Complex.exp (-(Real.pi : ℂ) * (x : ℂ) ^ 2) := by
  simp [hermiteFunctionCore_apply, complexHermitePolynomial,
    Polynomial.hermite_zero]

/-- The ground-state Hermite Gaussian is fixed by the Fourier transform. -/
theorem fourier_hermiteFunctionCore_zero :
    FourierTransform.fourier (hermiteFunctionCore 0) =
      hermiteFunctionCore 0 := by
  ext x
  rw [SchwartzMap.fourier_coe]
  rw [show (hermiteFunctionCore 0 : ℝ → ℂ) =
      fun y : ℝ ↦ Complex.exp (-(Real.pi : ℂ) * (y : ℂ) ^ 2) from
    funext hermiteFunctionCore_zero_apply]
  have h := congrFun
    (fourier_gaussian_pi (b := (1 : ℂ)) (by norm_num)) x
  simpa using h

/-- Every concrete Hermite core is a Fourier eigenfunction with phase
`(-i)^n`. -/
theorem fourier_hermiteFunctionCore (n : ℕ) :
    FourierTransform.fourier (hermiteFunctionCore n) =
      hermiteFourierPhase n • hermiteFunctionCore n := by
  induction n with
  | zero =>
      simpa [hermiteFourierPhase] using fourier_hermiteFunctionCore_zero
  | succ n ih =>
      let a : ℂ := 2 * Real.sqrt Real.pi
      have ha : a ≠ 0 := by
        dsimp [a]
        exact mul_ne_zero (by norm_num)
          (by exact_mod_cast (Real.sqrt_pos.2 Real.pi_pos).ne')
      have hscaled :
          a • FourierTransform.fourier (hermiteFunctionCore (n + 1)) =
            a • (hermiteFourierPhase (n + 1) •
              hermiteFunctionCore (n + 1)) := by
        calc
          a • FourierTransform.fourier (hermiteFunctionCore (n + 1)) =
              FourierTransform.fourier
                (a • hermiteFunctionCore (n + 1)) := by
            rw [FourierTransform.fourier_smul]
          _ = FourierTransform.fourier
                (hermiteCreationOperator (hermiteFunctionCore n)) := by
            rw [hermiteCreationOperator_core]
          _ = (-Complex.I) •
                hermiteCreationOperator
                  (FourierTransform.fourier (hermiteFunctionCore n)) :=
            fourier_hermiteCreationOperator _
          _ = (-Complex.I) •
                hermiteCreationOperator
                  (hermiteFourierPhase n • hermiteFunctionCore n) := by
            rw [ih]
          _ = a • (hermiteFourierPhase (n + 1) •
                hermiteFunctionCore (n + 1)) := by
            rw [map_smul, hermiteCreationOperator_core]
            simp only [a, hermiteFourierPhase, pow_succ, smul_smul]
            congr 1
            ring
      calc
        FourierTransform.fourier (hermiteFunctionCore (n + 1)) =
            a⁻¹ • (a • FourierTransform.fourier
              (hermiteFunctionCore (n + 1))) := by
          rw [smul_smul, inv_mul_cancel₀ ha, one_smul]
        _ = a⁻¹ • (a • (hermiteFourierPhase (n + 1) •
              hermiteFunctionCore (n + 1))) := by
          rw [hscaled]
        _ = hermiteFourierPhase (n + 1) •
              hermiteFunctionCore (n + 1) := by
          rw [smul_smul, inv_mul_cancel₀ ha, one_smul]

/-- The positive real normalization `2^(1/4) / sqrt(n!)`, written using
nested square roots to avoid branch choices. -/
def hermiteFunctionNormalization (n : ℕ) : ℝ :=
  Real.sqrt (Real.sqrt 2) / Real.sqrt n.factorial

theorem hermiteFunctionNormalization_pos (n : ℕ) :
    0 < hermiteFunctionNormalization n := by
  unfold hermiteFunctionNormalization
  positivity

/-- The standard `L²`-normalized Hermite function for mathlib's Fourier
convention:

`2^(1/4) / sqrt(n!) * He_n(2 * sqrt(pi) * x) * exp(-pi*x^2)`.

This is a genuine Schwartz function, not an abstract coefficient atom.
-/
def normalizedHermiteSchwartz (n : ℕ) : SchwartzMap ℝ ℂ :=
  (hermiteFunctionNormalization n : ℂ) •
    hermiteFunctionCore n

@[simp]
theorem normalizedHermiteSchwartz_apply (n : ℕ) (x : ℝ) :
    normalizedHermiteSchwartz n x =
      (hermiteFunctionNormalization n : ℂ) *
        (complexHermitePolynomial n).eval
          ((2 * Real.sqrt Real.pi * x : ℝ) : ℂ) *
        Complex.exp (-(Real.pi : ℂ) * (x : ℂ) ^ 2) := by
  rw [normalizedHermiteSchwartz, smul_apply, smul_eq_mul,
    hermiteFunctionCore_apply]
  ring

/-- The normalized concrete Hermite function is a Fourier eigenfunction with
the same phase used by the abstract coefficient-space Fourier operator. -/
@[simp]
theorem fourier_normalizedHermiteSchwartz (n : ℕ) :
    FourierTransform.fourier (normalizedHermiteSchwartz n) =
      hermiteFourierPhase n • normalizedHermiteSchwartz n := by
  rw [normalizedHermiteSchwartz, FourierTransform.fourier_smul,
    fourier_hermiteFunctionCore]
  simp only [smul_smul]
  congr 1
  ring

/-- Dirac evaluation on a concrete Hermite function is its explicit Hermite
coefficient value. -/
theorem pointMass_normalizedHermiteSchwartz (x : ℝ) (n : ℕ) :
    pointMass x (normalizedHermiteSchwartz n) =
      normalizedHermiteSchwartz n x := by
  exact pointMass_apply x (normalizedHermiteSchwartz n)

end

end MeyerGeneralProblem
