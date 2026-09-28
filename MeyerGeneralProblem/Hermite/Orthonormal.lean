module

public import MeyerGeneralProblem.Hermite.Functions
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import all Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import TauCeti.Analysis.SpecialFunctions.Hermite.Function.Fourier.HilbertBasis
import all TauCeti.Analysis.SpecialFunctions.Hermite.Function.Fourier.HilbertBasis

@[expose] public section

/-!
# Orthonormal realization and pointwise Hermite bounds

This file identifies `normalizedHermiteSchwartz` with the independently
constructed Fourier-normalized Hermite Hilbert basis in the pinned TauCeti
dependency.  It then combines exact orthonormality with the derivative ladder
and the one-dimensional fundamental theorem of calculus to prove the
pointwise estimate

`‖h_n x‖² ≤ 2 * sqrt (2*pi) * sqrt (n+1)`.

That polynomial bound is the analytic input needed to place Dirac evaluation
in every negative Hermite scale of integer order at least one.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter MeasureTheory

private lemma complexHermitePolynomial_eval_real (n : ℕ) (x : ℝ) :
    (complexHermitePolynomial n).eval (x : ℂ) =
      ((Polynomial.aeval x (Polynomial.hermite n) : ℝ) : ℂ) := by
  rw [complexHermitePolynomial, Polynomial.eval_map, Polynomial.aeval_def]
  have h := Polynomial.hom_eval₂ (Polynomial.hermite n) (Int.castRingHom ℝ)
    Complex.ofRealHom x
  have hcomp : Complex.ofRealHom.comp (Int.castRingHom ℝ) = Int.castRingHom ℂ := by
    ext z
    simp
  rw [hcomp] at h
  exact h.symm

private lemma complexHermitePolynomial_eval_eq_twoPiHermiteDilated
    (n : ℕ) (x : ℝ) :
    (complexHermitePolynomial n).eval
        ((2 * Real.sqrt Real.pi * x : ℝ) : ℂ) =
      (((TauCeti.twoPiHermiteDilated n).eval x : ℝ) : ℂ) := by
  rw [complexHermitePolynomial_eval_real, TauCeti.eval_twoPiHermiteDilated,
    TauCeti.eval_hermiteDilated]
  congr 2
  rw [mul_assoc]
  have h : Real.sqrt 2 * Real.sqrt (2 * Real.pi) = 2 * Real.sqrt Real.pi := by
    calc
      Real.sqrt 2 * Real.sqrt (2 * Real.pi) = Real.sqrt (2 * (2 * Real.pi)) := by
        symm
        exact Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2) _
      _ = Real.sqrt (4 * Real.pi) := by ring
      _ = Real.sqrt 4 * Real.sqrt Real.pi := by
        exact Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 4) _
      _ = 2 * Real.sqrt Real.pi := by
        rw [show Real.sqrt 4 = 2 from
          (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2 (by norm_num)]
  congr 1
  calc
    2 * (Real.sqrt Real.pi * x) = (2 * Real.sqrt Real.pi) * x := by ring
    _ = (Real.sqrt 2 * Real.sqrt (2 * Real.pi)) * x := by rw [h]
    _ = Real.sqrt (2 * Real.pi) * x * Real.sqrt 2 := by ring

private lemma hermiteFunctionNormalization_eq_tau (n : ℕ) :
    hermiteFunctionNormalization n =
      Real.sqrt (Real.sqrt (2 * Real.pi)) /
        Real.sqrt ((n.factorial : ℝ) * Real.sqrt Real.pi) := by
  have h2p : Real.sqrt (2 * Real.pi) = Real.sqrt 2 * Real.sqrt Real.pi := by
    exact Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2) _
  apply (sq_eq_sq₀ (hermiteFunctionNormalization_pos n).le
    (div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp
  rw [hermiteFunctionNormalization, div_pow, div_pow,
    Real.sq_sqrt (Real.sqrt_nonneg 2),
    Real.sq_sqrt (by positivity : (0 : ℝ) ≤ n.factorial),
    Real.sq_sqrt (Real.sqrt_nonneg (2 * Real.pi)),
    Real.sq_sqrt (by positivity :
      (0 : ℝ) ≤ (n.factorial : ℝ) * Real.sqrt Real.pi),
    h2p]
  field_simp

private lemma hermiteFunctionNormalization_eq_inv_sqrt_twoPi (n : ℕ) :
    hermiteFunctionNormalization n =
      (Real.sqrt (TauCeti.twoPiHermiteNormalization n))⁻¹ := by
  rw [hermiteFunctionNormalization_eq_tau, TauCeti.twoPiHermiteNormalization]
  apply (sq_eq_sq₀ (by positivity)
    (inv_nonneg.2 (Real.sqrt_nonneg _))).mp
  rw [div_pow, inv_pow, Real.sq_sqrt (Real.sqrt_nonneg (2 * Real.pi)),
    Real.sq_sqrt (by positivity :
      (0 : ℝ) ≤ (n.factorial : ℝ) * Real.sqrt Real.pi),
    Real.sq_sqrt (div_nonneg (by positivity)
      (Real.sqrt_nonneg (2 * Real.pi)))]
  field_simp

/-- The concrete family constructed in this project is exactly the
Fourier-normalized orthonormal Hermite family in the pinned TauCeti library.
This discharges the `L²`-normalization claim rather than merely documenting it.
-/
theorem normalizedHermiteSchwartz_eq_twoPi (n : ℕ) :
    normalizedHermiteSchwartz n = TauCeti.twoPiHermiteSchwartzMap n := by
  ext x
  rw [normalizedHermiteSchwartz_apply, TauCeti.twoPiHermiteSchwartzMap_apply,
    TauCeti.twoPiHermiteFunction_eq_eval_mul_exp,
    hermiteFunctionNormalization_eq_inv_sqrt_twoPi,
    complexHermitePolynomial_eval_eq_twoPiHermiteDilated]
  push_cast
  simp only [div_eq_mul_inv]
  ring

private lemma normalizedHermiteDerivative_memLp (n : ℕ) :
    MemLp (deriv (TauCeti.twoPiHermiteFunction n)) 2 volume := by
  have h₁ := (TauCeti.memLp_two_twoPiHermiteFunction (n - 1)).const_mul
    (Real.sqrt (2 * Real.pi) * Real.sqrt ((n : ℝ) / 2))
  have h₂ := (TauCeti.memLp_two_twoPiHermiteFunction (n + 1)).const_mul
    (Real.sqrt (2 * Real.pi) * Real.sqrt (((n : ℝ) + 1) / 2))
  have h := h₁.sub h₂
  apply (memLp_congr_ae ?_).mpr h
  filter_upwards with x
  rw [TauCeti.deriv_twoPiHermiteFunction]
  simp only [Pi.sub_apply]
  ring

private lemma integral_normalizedHermiteDerivative_sq (n : ℕ) :
    (∫ x : ℝ, deriv (TauCeti.twoPiHermiteFunction n) x ^ 2) =
      2 * Real.pi * ((n : ℝ) + 1 / 2) := by
  let a : ℝ := Real.sqrt (2 * Real.pi) * Real.sqrt ((n : ℝ) / 2)
  let b : ℝ := Real.sqrt (2 * Real.pi) * Real.sqrt (((n : ℝ) + 1) / 2)
  let f₁ : ℝ → ℝ := TauCeti.twoPiHermiteFunction (n - 1)
  let f₂ : ℝ → ℝ := TauCeti.twoPiHermiteFunction (n + 1)
  have h₁ : MemLp f₁ 2 volume := TauCeti.memLp_two_twoPiHermiteFunction (n - 1)
  have h₂ : MemLp f₂ 2 volume := TauCeti.memLp_two_twoPiHermiteFunction (n + 1)
  have h₁₁ : Integrable (f₁ * f₁) volume := h₁.integrable_mul h₁
  have h₂₂ : Integrable (f₂ * f₂) volume := h₂.integrable_mul h₂
  have h₁₂ : Integrable (f₁ * f₂) volume := h₁.integrable_mul h₂
  have hi₁₁ : ∫ x : ℝ, f₁ x * f₁ x = 1 := by
    simpa [f₁] using
      TauCeti.integral_twoPiHermiteFunction_mul_twoPiHermiteFunction (n - 1) (n - 1)
  have hi₂₂ : ∫ x : ℝ, f₂ x * f₂ x = 1 := by
    simpa [f₂] using
      TauCeti.integral_twoPiHermiteFunction_mul_twoPiHermiteFunction (n + 1) (n + 1)
  have hn : n - 1 ≠ n + 1 := by omega
  have hi₁₂ : ∫ x : ℝ, f₁ x * f₂ x = 0 := by
    simpa [f₁, f₂, hn] using
      TauCeti.integral_twoPiHermiteFunction_mul_twoPiHermiteFunction (n - 1) (n + 1)
  have hderiv (x : ℝ) :
      deriv (TauCeti.twoPiHermiteFunction n) x = a * f₁ x - b * f₂ x := by
    rw [TauCeti.deriv_twoPiHermiteFunction]
    simp only [a, b, f₁, f₂]
    ring
  have hA : Integrable (fun x : ℝ => a ^ 2 * (f₁ x * f₁ x)) volume := by
    simpa only [Pi.mul_apply] using h₁₁.const_mul (a ^ 2)
  have hB : Integrable (fun x : ℝ => b ^ 2 * (f₂ x * f₂ x)) volume := by
    simpa only [Pi.mul_apply] using h₂₂.const_mul (b ^ 2)
  have hC : Integrable (fun x : ℝ => (2 * a * b) * (f₁ x * f₂ x)) volume := by
    simpa only [Pi.mul_apply] using h₁₂.const_mul (2 * a * b)
  calc
    (∫ x : ℝ, deriv (TauCeti.twoPiHermiteFunction n) x ^ 2) =
        ∫ x : ℝ, a ^ 2 * (f₁ x * f₁ x) + b ^ 2 * (f₂ x * f₂ x) -
          (2 * a * b) * (f₁ x * f₂ x) := by
      apply integral_congr_ae
      filter_upwards with x
      rw [hderiv]
      ring
    _ = (∫ x : ℝ, a ^ 2 * (f₁ x * f₁ x) + b ^ 2 * (f₂ x * f₂ x)) -
          ∫ x : ℝ, (2 * a * b) * (f₁ x * f₂ x) := by
      convert integral_sub (hA.add hB) hC using 1 <;>
        simp only [Pi.add_apply]
    _ = ((∫ x : ℝ, a ^ 2 * (f₁ x * f₁ x)) +
          ∫ x : ℝ, b ^ 2 * (f₂ x * f₂ x)) -
          ∫ x : ℝ, (2 * a * b) * (f₁ x * f₂ x) := by
      rw [integral_add hA hB]
    _ = a ^ 2 * 1 + b ^ 2 * 1 - (2 * a * b) * 0 := by
      rw [integral_const_mul, integral_const_mul, integral_const_mul,
        hi₁₁, hi₂₂, hi₁₂]
    _ = 2 * Real.pi * ((n : ℝ) + 1 / 2) := by
      simp only [a, b]
      rw [mul_pow, mul_pow,
        Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * Real.pi),
        Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (n : ℝ) / 2),
        Real.sq_sqrt (by positivity : (0 : ℝ) ≤ ((n : ℝ) + 1) / 2)]
      ring

private lemma twoPiHermiteFunction_tendsto_atBot (n : ℕ) :
    Tendsto (TauCeti.twoPiHermiteFunction n) atBot (nhds 0) := by
  have hc : Tendsto (normalizedHermiteSchwartz n : ℝ → ℂ) atBot (nhds 0) :=
    (SchwartzMap.tendsto_cocompact (normalizedHermiteSchwartz n)).mono_left
      atBot_le_cocompact
  have hr := Complex.continuous_re.continuousAt.tendsto.comp hc
  apply hr.congr'
  filter_upwards with x
  simp [Function.comp_apply, normalizedHermiteSchwartz_eq_twoPi]

private lemma twoPiHermiteFunction_sq_le (n : ℕ) (x : ℝ) :
    TauCeti.twoPiHermiteFunction n x ^ 2 ≤
      2 * Real.sqrt (2 * Real.pi * ((n : ℝ) + 1 / 2)) := by
  let f : ℝ → ℝ := TauCeti.twoPiHermiteFunction n
  let d : ℝ → ℝ := deriv f
  have hf : MemLp f 2 volume := TauCeti.memLp_two_twoPiHermiteFunction n
  have hd : MemLp d 2 volume := by
    simpa only [f, d] using normalizedHermiteDerivative_memLp n
  have hfd : Integrable (f * d) volume := hf.integrable_mul hd
  have hg : Integrable (fun y : ℝ => 2 * f y * d y) volume := by
    simpa only [Pi.mul_apply, mul_assoc] using hfd.const_mul 2
  have hderiv (y : ℝ) : HasDerivAt (fun z => f z ^ 2) (2 * f y * d y) y := by
    have h₀ : HasDerivAt f (d y) y := by
      simpa only [f, d, TauCeti.deriv_twoPiHermiteFunction] using
        TauCeti.hasDerivAt_twoPiHermiteFunction n y
    have hfun : (fun z => f z ^ 2) = f * f := by
      funext z
      simp only [pow_two, Pi.mul_apply]
    rw [hfun]
    exact (h₀.mul h₀).congr_deriv (by ring)
  have hzero : Tendsto (fun y => f y ^ 2) atBot (nhds 0) := by
    simpa [f] using (twoPiHermiteFunction_tendsto_atBot n).pow 2
  have hFTC : (∫ y in Set.Iic x, 2 * f y * d y) = f x ^ 2 := by
    simpa using MeasureTheory.integral_Iic_of_hasDerivAt_of_tendsto'
      (a := x) (m := 0) (fun y _ => hderiv y) hg.integrableOn hzero
  have hf_sq : (∫ y : ℝ, ‖f y‖ ^ (2 : ℝ)) = 1 := by
    have h := TauCeti.integral_twoPiHermiteFunction_mul_twoPiHermiteFunction n n
    rw [ite_eq_left rfl] at h
    convert h using 1
    apply integral_congr_ae
    filter_upwards with y
    simp only [f, Real.norm_eq_abs, Real.rpow_two, sq_abs]
    rw [pow_two]
  have hd_sq : (∫ y : ℝ, ‖d y‖ ^ (2 : ℝ)) =
      2 * Real.pi * ((n : ℝ) + 1 / 2) := by
    simpa only [d, f, Real.norm_eq_abs, Real.rpow_two, sq_abs] using
      integral_normalizedHermiteDerivative_sq n
  have hf' : MemLp f (ENNReal.ofReal (2 : ℝ)) volume := by simpa using hf
  have hd' : MemLp d (ENNReal.ofReal (2 : ℝ)) volume := by simpa using hd
  have hholder := MeasureTheory.integral_mul_norm_le_Lp_mul_Lq
    (μ := volume) (p := (2 : ℝ)) (q := (2 : ℝ))
    (by rw [Real.holderConjugate_iff]; norm_num) hf' hd'
  calc
    f x ^ 2 = ‖∫ y in Set.Iic x, 2 * f y * d y‖ := by
      rw [hFTC]
      exact (Real.norm_of_nonneg (sq_nonneg _)).symm
    _ ≤ ∫ y in Set.Iic x, ‖2 * f y * d y‖ :=
      MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ y : ℝ, ‖2 * f y * d y‖ :=
      MeasureTheory.integral_mono_measure Measure.restrict_le_self
        (Filter.Eventually.of_forall fun _ => norm_nonneg _)
        hg.norm
    _ = 2 * ∫ y : ℝ, ‖f y‖ * ‖d y‖ := by
      have hnorm : (fun y : ℝ => ‖2 * f y * d y‖) =
          fun y : ℝ => 2 * (‖f y‖ * ‖d y‖) := by
        funext y
        simp only [norm_mul, Real.norm_eq_abs]
        rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        ring
      rw [hnorm, MeasureTheory.integral_const_mul]
    _ ≤ 2 * ((∫ y : ℝ, ‖f y‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
          (∫ y : ℝ, ‖d y‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ))) := by
      gcongr
    _ = 2 * Real.sqrt (2 * Real.pi * ((n : ℝ) + 1 / 2)) := by
      rw [hf_sq, hd_sq]
      norm_num [← Real.sqrt_eq_rpow]

/-- Uniform-in-`x` polynomial pointwise bound for the normalized Hermite
family.  The exponent `1/2` on the right is sufficient for the order-`-1`
Dirac coefficient sequence to be square-summable. -/
theorem normalizedHermiteSchwartz_norm_sq_le (n : ℕ) (x : ℝ) :
    ‖normalizedHermiteSchwartz n x‖ ^ 2 ≤
      2 * Real.sqrt (2 * Real.pi) * Real.sqrt ((n : ℝ) + 1) := by
  rw [normalizedHermiteSchwartz_eq_twoPi,
    TauCeti.twoPiHermiteSchwartzMap_apply, Complex.norm_real]
  calc
    |TauCeti.twoPiHermiteFunction n x| ^ 2 =
        TauCeti.twoPiHermiteFunction n x ^ 2 := sq_abs _
    _ ≤ 2 * Real.sqrt (2 * Real.pi * ((n : ℝ) + 1 / 2)) :=
      twoPiHermiteFunction_sq_le n x
    _ ≤ 2 * Real.sqrt (2 * Real.pi * ((n : ℝ) + 1)) := by
      gcongr
      linarith
    _ = 2 * Real.sqrt (2 * Real.pi) * Real.sqrt ((n : ℝ) + 1) := by
      rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
      ring

end

end MeyerGeneralProblem
