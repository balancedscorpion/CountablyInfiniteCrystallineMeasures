module

public import MeyerGeneralProblem.Hermite.MehlerKernel
public import Mathlib.Analysis.Calculus.MeanValue
import all Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.SmoothSeries
import all Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.RingTheory.PowerSeries.Derivative
import all Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Evaluation
import all Mathlib.RingTheory.PowerSeries.Evaluation

@[expose] public section

/-!
# The closed Hermite Mehler formula

This module proves the closed Gaussian formula for the Mehler series used by
the concrete negative Hermite-scale Gram kernel.  The proof is developed from
the pinned probabilists' Hermite recurrence and convergent power-series
calculus; no kernel formula is postulated.
-/

namespace MeyerGeneralProblem

noncomputable section

open Polynomial

/-- Evaluation of the probabilists' Hermite polynomial over `ℝ`. -/
def probabilistsHermiteValue (n : ℕ) (x : ℝ) : ℝ :=
  aeval x (hermite n)

@[simp]
theorem probabilistsHermiteValue_zero (x : ℝ) :
    probabilistsHermiteValue 0 x = 1 := by
  simp [probabilistsHermiteValue]

@[simp]
theorem probabilistsHermiteValue_one (x : ℝ) :
    probabilistsHermiteValue 1 x = x := by
  simp [probabilistsHermiteValue]

/-- The evaluated three-term Hermite recurrence. -/
theorem probabilistsHermiteValue_add_two (n : ℕ) (x : ℝ) :
    probabilistsHermiteValue (n + 2) x =
      x * probabilistsHermiteValue (n + 1) x -
        (n + 1 : ℝ) * probabilistsHermiteValue n x := by
  rw [probabilistsHermiteValue, probabilistsHermiteValue,
    probabilistsHermiteValue, hermite_add_two]
  simp

/-- The coefficient in the bilinear probabilists' Hermite generating
series. -/
def hermiteBilinearCoeff (x y : ℝ) (n : ℕ) : ℝ :=
  probabilistsHermiteValue n x * probabilistsHermiteValue n y /
    (n.factorial : ℝ)

@[simp]
theorem hermiteBilinearCoeff_zero (x y : ℝ) :
    hermiteBilinearCoeff x y 0 = 1 := by
  simp [hermiteBilinearCoeff]

@[simp]
theorem hermiteBilinearCoeff_one (x y : ℝ) :
    hermiteBilinearCoeff x y 1 = x * y := by
  simp [hermiteBilinearCoeff]

private theorem probabilistsHermiteValue_bilinear_raw_recurrence
    (x y : ℝ) (k : ℕ) :
    probabilistsHermiteValue (k + 5) x *
          probabilistsHermiteValue (k + 5) y -
        2 * (k + 4 : ℝ) * (k + 3 : ℝ) *
          (probabilistsHermiteValue (k + 3) x *
            probabilistsHermiteValue (k + 3) y) +
        (k + 1 : ℝ) * (k + 4 : ℝ) * (k + 3 : ℝ) * (k + 2 : ℝ) *
          (probabilistsHermiteValue (k + 1) x *
            probabilistsHermiteValue (k + 1) y) =
      (x * y) *
          (probabilistsHermiteValue (k + 4) x *
            probabilistsHermiteValue (k + 4) y) +
        (k + 4 : ℝ) * (1 - x ^ 2 - y ^ 2) *
          (probabilistsHermiteValue (k + 3) x *
            probabilistsHermiteValue (k + 3) y) +
        (k + 4 : ℝ) * (k + 3 : ℝ) * (x * y) *
          (probabilistsHermiteValue (k + 2) x *
            probabilistsHermiteValue (k + 2) y) -
        (k + 4 : ℝ) * (k + 3 : ℝ) * (k + 2 : ℝ) *
          (probabilistsHermiteValue (k + 1) x *
            probabilistsHermiteValue (k + 1) y) := by
  rw [probabilistsHermiteValue_add_two (k + 3) x,
    probabilistsHermiteValue_add_two (k + 3) y,
    probabilistsHermiteValue_add_two (k + 2) x,
    probabilistsHermiteValue_add_two (k + 2) y,
    probabilistsHermiteValue_add_two (k + 1) x,
    probabilistsHermiteValue_add_two (k + 1) y]
  push_cast
  ring

/-- Coefficient recurrence for the first-order differential equation obeyed
by the bilinear Hermite generating series.  The conditional terms are the
zero-extension of the recurrence below degree zero. -/
theorem hermiteBilinearCoeff_ode_recurrence
    (x y : ℝ) (k : ℕ) :
    (k + 1 : ℝ) * hermiteBilinearCoeff x y (k + 1) -
        (if 2 ≤ k then
          2 * (k - 1 : ℝ) * hermiteBilinearCoeff x y (k - 1)
        else 0) +
        (if 4 ≤ k then
          (k - 3 : ℝ) * hermiteBilinearCoeff x y (k - 3)
        else 0) =
      (x * y) * hermiteBilinearCoeff x y k +
        (if 1 ≤ k then
          (1 - x ^ 2 - y ^ 2) * hermiteBilinearCoeff x y (k - 1)
        else 0) +
        (if 2 ≤ k then
          (x * y) * hermiteBilinearCoeff x y (k - 2)
        else 0) -
        (if 3 ≤ k then hermiteBilinearCoeff x y (k - 3) else 0) := by
  rcases k with (_ | _ | _ | _ | k)
  · norm_num [hermiteBilinearCoeff]
  · norm_num [hermiteBilinearCoeff,
      probabilistsHermiteValue_add_two]
    ring
  · norm_num [hermiteBilinearCoeff,
      probabilistsHermiteValue_add_two]
    ring
  · norm_num [hermiteBilinearCoeff,
      probabilistsHermiteValue_add_two]
    ring
  · simp only [ite_eq_left (show 2 ≤ k + 1 + 1 + 1 + 1 by omega),
      ite_eq_left (show 4 ≤ k + 1 + 1 + 1 + 1 by omega),
      ite_eq_left (show 1 ≤ k + 1 + 1 + 1 + 1 by omega),
      ite_eq_left (show 3 ≤ k + 1 + 1 + 1 + 1 by omega)]
    simp only [
      show k + 1 + 1 + 1 + 1 + 1 = k + 5 by omega,
      show k + 1 + 1 + 1 + 1 = k + 4 by omega,
      show k + 1 + 1 + 1 = k + 3 by omega,
      show k + 1 + 1 = k + 2 by omega,
      show k + 4 - 1 = k + 3 by omega,
      show k + 4 - 2 = k + 2 by omega,
      show k + 4 - 3 = k + 1 by omega]
    norm_num only [Nat.cast_add, Nat.cast_one]
    have hraw := probabilistsHermiteValue_bilinear_raw_recurrence x y k
    have hfac5 : ((k + 5).factorial : ℝ) =
        (k + 5 : ℝ) * ((k + 4).factorial : ℝ) := by
      exact_mod_cast (Nat.factorial_succ (k + 4))
    have hfac4 : ((k + 4).factorial : ℝ) =
        (k + 4 : ℝ) * ((k + 3).factorial : ℝ) := by
      exact_mod_cast (Nat.factorial_succ (k + 3))
    have hfac3 : ((k + 3).factorial : ℝ) =
        (k + 3 : ℝ) * ((k + 2).factorial : ℝ) := by
      exact_mod_cast (Nat.factorial_succ (k + 2))
    have hfac2 : ((k + 2).factorial : ℝ) =
        (k + 2 : ℝ) * ((k + 1).factorial : ℝ) := by
      exact_mod_cast (Nat.factorial_succ (k + 1))
    unfold hermiteBilinearCoeff
    rw [hfac5, hfac4, hfac3, hfac2]
    field_simp
    linear_combination (k + 5 : ℝ) * hraw

/-- The bilinear Hermite coefficients as a formal power series. -/
def hermiteBilinearPowerSeries (x y : ℝ) : PowerSeries ℝ :=
  PowerSeries.mk (hermiteBilinearCoeff x y)

@[simp]
theorem coeff_hermiteBilinearPowerSeries (x y : ℝ) (n : ℕ) :
    PowerSeries.coeff n (hermiteBilinearPowerSeries x y) =
      hermiteBilinearCoeff x y n := by
  simp [hermiteBilinearPowerSeries]

private theorem coeff_X_two_mul_hermiteBilinearPowerSeries_derivative
    (x y : ℝ) (k : ℕ) :
    PowerSeries.coeff k
        (PowerSeries.X ^ 2 *
          PowerSeries.derivative (hermiteBilinearPowerSeries x y)) =
      if 2 ≤ k then
        (k - 1 : ℝ) * hermiteBilinearCoeff x y (k - 1)
      else 0 := by
  rw [PowerSeries.coeff_X_pow_mul']
  split_ifs with hk
  · rw [PowerSeries.coeff_derivative,
      coeff_hermiteBilinearPowerSeries]
    have hidx : k - 2 + 1 = k - 1 := by omega
    rw [hidx]
    have hcast : ((k - 2 : ℕ) : ℝ) + 1 = (k : ℝ) - 1 := by
      rw [Nat.cast_sub hk]
      norm_num
      ring
    rw [hcast]
    ring
  · rfl

private theorem coeff_X_four_mul_hermiteBilinearPowerSeries_derivative
    (x y : ℝ) (k : ℕ) :
    PowerSeries.coeff k
        (PowerSeries.X ^ 4 *
          PowerSeries.derivative (hermiteBilinearPowerSeries x y)) =
      if 4 ≤ k then
        (k - 3 : ℝ) * hermiteBilinearCoeff x y (k - 3)
      else 0 := by
  rw [PowerSeries.coeff_X_pow_mul']
  split_ifs with hk
  · rw [PowerSeries.coeff_derivative,
      coeff_hermiteBilinearPowerSeries]
    have hidx : k - 4 + 1 = k - 3 := by omega
    rw [hidx]
    have hcast : ((k - 4 : ℕ) : ℝ) + 1 = (k : ℝ) - 3 := by
      rw [Nat.cast_sub hk]
      norm_num
      ring
    rw [hcast]
    ring
  · rfl

private theorem coeff_X_pow_mul_hermiteBilinearPowerSeries
    (x y : ℝ) (d k : ℕ) :
    PowerSeries.coeff k
        (PowerSeries.X ^ d * hermiteBilinearPowerSeries x y) =
      if d ≤ k then hermiteBilinearCoeff x y (k - d) else 0 := by
  rw [PowerSeries.coeff_X_pow_mul']
  simp only [coeff_hermiteBilinearPowerSeries]

/-- The factorial-normalized bilinear Hermite series satisfies its formal
first-order Mehler equation.  Its coefficient identity is exactly
`hermiteBilinearCoeff_ode_recurrence`; no analytic uniqueness is used at this
stage. -/
theorem hermiteBilinearPowerSeries_ode (x y : ℝ) :
    PowerSeries.derivative (hermiteBilinearPowerSeries x y) -
          PowerSeries.C 2 *
            (PowerSeries.X ^ 2 *
              PowerSeries.derivative (hermiteBilinearPowerSeries x y)) +
          PowerSeries.X ^ 4 *
            PowerSeries.derivative (hermiteBilinearPowerSeries x y) =
      PowerSeries.C (x * y) * hermiteBilinearPowerSeries x y +
          PowerSeries.C 1 *
            (PowerSeries.X ^ 1 * hermiteBilinearPowerSeries x y) -
          PowerSeries.C (x ^ 2) *
            (PowerSeries.X ^ 1 * hermiteBilinearPowerSeries x y) -
          PowerSeries.C (y ^ 2) *
            (PowerSeries.X ^ 1 * hermiteBilinearPowerSeries x y) +
          PowerSeries.C (x * y) *
            (PowerSeries.X ^ 2 * hermiteBilinearPowerSeries x y) -
          PowerSeries.X ^ 3 * hermiteBilinearPowerSeries x y := by
  ext k
  simp only [map_sub, map_add, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_derivative, coeff_hermiteBilinearPowerSeries,
    coeff_X_two_mul_hermiteBilinearPowerSeries_derivative,
    coeff_X_four_mul_hermiteBilinearPowerSeries_derivative,
    coeff_X_pow_mul_hermiteBilinearPowerSeries, one_mul, mul_ite,
    mul_zero]
  have hrec := hermiteBilinearCoeff_ode_recurrence x y k
  split_ifs at hrec ⊢
  all_goals try omega
  all_goals nlinarith [hrec]

/-- Evaluation of the coefficient-promoted Hermite polynomial at a real
point agrees with real evaluation of the original integer polynomial. -/
theorem complexHermitePolynomial_eval_real_eq_probabilistsHermiteValue
    (n : ℕ) (x : ℝ) :
    (complexHermitePolynomial n).eval (x : ℂ) =
      (probabilistsHermiteValue n x : ℂ) := by
  unfold complexHermitePolynomial probabilistsHermiteValue
  change
    Polynomial.eval (x : ℂ)
        (Polynomial.map (Int.castRingHom ℂ) (Polynomial.hermite n)) =
      ((Polynomial.eval₂ (Int.castRingHom ℝ) x
        (Polynomial.hermite n) : ℝ) : ℂ)
  rw [Polynomial.eval_map]
  have hcomp :
      (algebraMap ℝ ℂ).comp (Int.castRingHom ℝ) =
        Int.castRingHom ℂ := by
    ext z
    simp
  calc
    Polynomial.eval₂ (Int.castRingHom ℂ) (x : ℂ)
        (Polynomial.hermite n) =
      Polynomial.eval₂ (algebraMap ℝ ℂ) (x : ℂ)
        ((Polynomial.hermite n).map (Int.castRingHom ℝ)) := by
          rw [Polynomial.eval₂_map, hcomp]
    _ = (algebraMap ℝ ℂ)
        (Polynomial.eval x
          ((Polynomial.hermite n).map (Int.castRingHom ℝ))) := by
          exact Polynomial.eval₂_at_apply (algebraMap ℝ ℂ) x
    _ = ((Polynomial.eval₂ (Int.castRingHom ℝ) x
        (Polynomial.hermite n) : ℝ) : ℂ) := by
          rw [Polynomial.eval_map]
          rfl

/-- Rescaling a repository-normalized Hermite function recovers the
probabilists' Hermite polynomial with its exact factorial and Gaussian
factors. -/
theorem normalizedHermiteSchwartz_rescaled_apply (n : ℕ) (x : ℝ) :
    normalizedHermiteSchwartz n
        (x / (2 * Real.sqrt Real.pi)) =
      (hermiteFunctionNormalization n : ℂ) *
        (probabilistsHermiteValue n x : ℂ) *
          Complex.exp ((-(x ^ 2 / 4) : ℝ) : ℂ) := by
  have hsqrt : Real.sqrt Real.pi ≠ 0 :=
    (Real.sqrt_pos.2 Real.pi_pos).ne'
  have hxarg :
      2 * Real.sqrt Real.pi * (x / (2 * Real.sqrt Real.pi)) = x := by
    field_simp
  rw [normalizedHermiteSchwartz_apply, hxarg,
    complexHermitePolynomial_eval_real_eq_probabilistsHermiteValue]
  congr 1
  apply congrArg Complex.exp
  norm_cast
  field_simp [hsqrt]
  rw [Real.sq_sqrt Real.pi_pos.le]
  ring

/-- Square of the exact repository Hermite normalization. -/
theorem hermiteFunctionNormalization_sq (n : ℕ) :
    hermiteFunctionNormalization n ^ 2 =
      Real.sqrt 2 / (n.factorial : ℝ) := by
  rw [hermiteFunctionNormalization, div_pow,
    Real.sq_sqrt (Real.sqrt_nonneg 2),
    Real.sq_sqrt (Nat.cast_nonneg n.factorial)]

/-- Exact conversion of a rescaled normalized-Hermite product norm into
the corresponding bilinear-series coefficient. -/
theorem norm_star_rescaledHermite_mul_eq_bilinearCoeff
    (x y : ℝ) (n : ℕ) :
    ‖starRingEnd ℂ
          (normalizedHermiteSchwartz n
            (x / (2 * Real.sqrt Real.pi))) *
        normalizedHermiteSchwartz n
          (y / (2 * Real.sqrt Real.pi))‖ =
      Real.sqrt 2 * |hermiteBilinearCoeff x y n| *
        Real.exp (-(x ^ 2 + y ^ 2) / 4) := by
  rw [normalizedHermiteSchwartz_rescaled_apply,
    normalizedHermiteSchwartz_rescaled_apply]
  simp only [norm_mul, RCLike.norm_conj, Complex.norm_real,
    Real.norm_eq_abs, Complex.norm_exp, Complex.ofReal_re]
  rw [abs_of_pos (hermiteFunctionNormalization_pos n),
    hermiteBilinearCoeff, abs_div,
    abs_of_pos (by positivity : (0 : ℝ) < (n.factorial : ℝ)),
    abs_mul]
  have hexp :
      Real.exp (-(x ^ 2 / 4)) * Real.exp (-(y ^ 2 / 4)) =
        Real.exp (-(x ^ 2 + y ^ 2) / 4) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    hermiteFunctionNormalization n * |probabilistsHermiteValue n x| *
          Real.exp (-(x ^ 2 / 4)) *
        (hermiteFunctionNormalization n *
          |probabilistsHermiteValue n y| * Real.exp (-(y ^ 2 / 4))) =
      hermiteFunctionNormalization n ^ 2 *
        (|probabilistsHermiteValue n x| *
          |probabilistsHermiteValue n y|) *
        (Real.exp (-(x ^ 2 / 4)) * Real.exp (-(y ^ 2 / 4))) := by ring
    _ = (Real.sqrt 2 / (n.factorial : ℝ)) *
        (|probabilistsHermiteValue n x| *
          |probabilistsHermiteValue n y|) *
        (Real.exp (-(x ^ 2 / 4)) * Real.exp (-(y ^ 2 / 4))) := by
          rw [hermiteFunctionNormalization_sq]
    _ = Real.sqrt 2 *
        (|probabilistsHermiteValue n x| *
          |probabilistsHermiteValue n y| / (n.factorial : ℝ)) *
        Real.exp (-(x ^ 2 + y ^ 2) / 4) := by
          rw [hexp]
          ring

/-- A fixed polynomial-growth majorant for the bilinear Hermite
coefficients.  The constant depends on the two evaluation points, while the
spectral growth is only `sqrt (n + 1)`. -/
def hermiteBilinearCoeffBound (x y : ℝ) : ℝ :=
  (2 * Real.sqrt (2 * Real.pi)) /
    (Real.sqrt 2 * Real.exp (-(x ^ 2 + y ^ 2) / 4))

theorem hermiteBilinearCoeffBound_pos (x y : ℝ) :
    0 < hermiteBilinearCoeffBound x y := by
  unfold hermiteBilinearCoeffBound
  positivity

theorem abs_hermiteBilinearCoeff_le (x y : ℝ) (n : ℕ) :
    |hermiteBilinearCoeff x y n| ≤
      hermiteBilinearCoeffBound x y * Real.sqrt ((n : ℝ) + 1) := by
  have hprod := norm_star_normalizedHermiteSchwartz_mul_le
    (x / (2 * Real.sqrt Real.pi))
    (y / (2 * Real.sqrt Real.pi)) n
  rw [norm_star_rescaledHermite_mul_eq_bilinearCoeff] at hprod
  have hden :
      0 < Real.sqrt 2 * Real.exp (-(x ^ 2 + y ^ 2) / 4) := by
    positivity
  have hdiv :
      |hermiteBilinearCoeff x y n| ≤
        ((2 * Real.sqrt (2 * Real.pi)) *
          Real.sqrt ((n : ℝ) + 1)) /
          (Real.sqrt 2 * Real.exp (-(x ^ 2 + y ^ 2) / 4)) := by
    apply (le_div_iff₀ hden).2
    calc
      |hermiteBilinearCoeff x y n| *
          (Real.sqrt 2 * Real.exp (-(x ^ 2 + y ^ 2) / 4)) =
        Real.sqrt 2 * |hermiteBilinearCoeff x y n| *
          Real.exp (-(x ^ 2 + y ^ 2) / 4) := by ring
      _ ≤ (2 * Real.sqrt (2 * Real.pi)) *
          Real.sqrt ((n : ℝ) + 1) := hprod
  calc
    |hermiteBilinearCoeff x y n| ≤
        ((2 * Real.sqrt (2 * Real.pi)) *
          Real.sqrt ((n : ℝ) + 1)) /
          (Real.sqrt 2 * Real.exp (-(x ^ 2 + y ^ 2) / 4)) := hdiv
    _ = hermiteBilinearCoeffBound x y *
        Real.sqrt ((n : ℝ) + 1) := by
          unfold hermiteBilinearCoeffBound
          field_simp [hden.ne']

/-- Absolute convergence of the bilinear probabilists' Hermite series on
the open unit disk. -/
theorem summable_hermiteBilinearCoeff_mul_pow
    {r : ℝ} (hr : |r| < 1) (x y : ℝ) :
    Summable (fun n : ℕ ↦ hermiteBilinearCoeff x y n * r ^ n) := by
  let B := hermiteBilinearCoeffBound x y
  have hB : 0 ≤ B := by
    exact (hermiteBilinearCoeffBound_pos x y).le
  have hgeom : Summable (fun n : ℕ ↦ ((n : ℝ) + 1) * |r| ^ n) := by
    have hn : Summable (fun n : ℕ ↦ (n : ℝ) * |r| ^ n) := by
      simpa only [pow_one] using
        (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1
          (show ‖|r|‖ < 1 by simpa [Real.norm_eq_abs, abs_abs] using hr))
    have h₁ : Summable (fun n : ℕ ↦ |r| ^ n) :=
      summable_geometric_of_lt_one (abs_nonneg r) hr
    convert hn.add h₁ using 1
    ext n
    ring
  apply (hgeom.mul_left B).of_norm_bounded
  intro n
  have hc := abs_hermiteBilinearCoeff_le x y n
  have hsqrt : Real.sqrt ((n : ℝ) + 1) ≤ (n : ℝ) + 1 := by
    have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith [Real.sq_sqrt (by positivity : 0 ≤ (n : ℝ) + 1),
      Real.sqrt_nonneg ((n : ℝ) + 1)]
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_pow]
  calc
    |hermiteBilinearCoeff x y n| * |r| ^ n ≤
        B * Real.sqrt ((n : ℝ) + 1) * |r| ^ n := by
          gcongr
    _ ≤ B * ((n : ℝ) + 1) * |r| ^ n := by
          gcongr
    _ = B * (((n : ℝ) + 1) * |r| ^ n) := by ring

/-- The convergent bilinear Hermite generating series. -/
def hermiteBilinearSeries (x y r : ℝ) : ℝ :=
  ∑' n : ℕ, hermiteBilinearCoeff x y n * r ^ n

/-- The termwise derivative series. -/
def hermiteBilinearDerivativeSeries (x y r : ℝ) : ℝ :=
  ∑' n : ℕ,
    hermiteBilinearCoeff x y n * (n : ℝ) * r ^ (n - 1)

@[simp]
theorem hermiteBilinearSeries_zero (x y : ℝ) :
    hermiteBilinearSeries x y 0 = 1 := by
  rw [hermiteBilinearSeries, tsum_eq_single 0]
  · simp
  · intro n hn
    simp [hn]

/-- The bilinear series is differentiable throughout `(-1,1)`, and its
derivative is the genuine termwise derivative series. -/
theorem hasDerivAt_hermiteBilinearSeries
    {r : ℝ} (hr : |r| < 1) (x y : ℝ) :
    HasDerivAt (hermiteBilinearSeries x y)
      (hermiteBilinearDerivativeSeries x y r) r := by
  let B := hermiteBilinearCoeffBound x y
  let R : ℝ := (|r| + 1) / 2
  let u : ℕ → ℝ := fun n ↦
    (B / R) * ((n : ℝ) + 1) ^ 2 * R ^ n
  have hB : 0 ≤ B := by
    exact (hermiteBilinearCoeffBound_pos x y).le
  have hR0 : 0 < R := by
    dsimp [R]
    positivity
  have hR1 : R < 1 := by
    dsimp [R]
    linarith
  have hrR : |r| < R := by
    dsimp [R]
    linarith
  have hu : Summable u := by
    have hRnorm : ‖R‖ < 1 := by
      rw [Real.norm_eq_abs, abs_of_pos hR0]
      exact hR1
    have h₂ : Summable (fun n : ℕ ↦ (n : ℝ) ^ 2 * R ^ n) :=
      summable_pow_mul_geometric_of_norm_lt_one 2 hRnorm
    have h₁ : Summable (fun n : ℕ ↦ (n : ℝ) * R ^ n) := by
      simpa only [pow_one] using
        (summable_pow_mul_geometric_of_norm_lt_one 1 hRnorm)
    have h₀ : Summable (fun n : ℕ ↦ R ^ n) :=
      summable_geometric_of_lt_one hR0.le hR1
    have hpoly :
        Summable (fun n : ℕ ↦ ((n : ℝ) + 1) ^ 2 * R ^ n) := by
      convert (h₂.add (h₁.mul_left 2)).add h₀ using 1
      ext n
      ring
    simpa only [u, mul_assoc] using hpoly.mul_left (B / R)
  have hterm : ∀ n : ℕ, ∀ z : ℝ, z ∈ Set.Ioo (-R) R →
      HasDerivAt
        (fun w : ℝ ↦ hermiteBilinearCoeff x y n * w ^ n)
        (hermiteBilinearCoeff x y n * (n : ℝ) * z ^ (n - 1)) z := by
    intro n z _
    simpa only [mul_assoc] using
      (hasDerivAt_pow n z).const_mul (hermiteBilinearCoeff x y n)
  have htermBound : ∀ n : ℕ, ∀ z : ℝ, z ∈ Set.Ioo (-R) R →
      ‖hermiteBilinearCoeff x y n * (n : ℝ) * z ^ (n - 1)‖ ≤ u n := by
    intro n z hz
    rcases n with _ | n
    · have hBR : 0 ≤ B / R := div_nonneg hB hR0.le
      simp [u, hBR]
    · have hzabs : |z| ≤ R :=
        le_of_lt (abs_lt.mpr hz)
      have hpow : |z| ^ n ≤ R ^ n :=
        pow_le_pow_left₀ (abs_nonneg z) hzabs n
      have hc := abs_hermiteBilinearCoeff_le x y (n + 1)
      have hc' : |hermiteBilinearCoeff x y (n + 1)| ≤
          B * Real.sqrt ((n : ℝ) + 2) := by
        simpa only [B, Nat.cast_add, Nat.cast_one, add_assoc,
          one_add_one_eq_two] using hc
      have hsqrt : Real.sqrt ((n : ℝ) + 2) ≤ (n : ℝ) + 2 := by
        have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
        nlinarith [Real.sq_sqrt (by positivity : 0 ≤ (n : ℝ) + 2),
          Real.sqrt_nonneg ((n : ℝ) + 2)]
      have hRpow : 0 ≤ R ^ n := by positivity
      rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
        Nat.succ_sub_one, norm_pow, Real.norm_eq_abs, Nat.cast_add,
        Nat.cast_one]
      calc
        |hermiteBilinearCoeff x y (n + 1)| * |(n : ℝ) + 1| *
              |z| ^ n ≤
            (B * Real.sqrt ((n : ℝ) + 2)) * ((n : ℝ) + 1) * R ^ n := by
          rw [abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) + 1)]
          gcongr
        _ ≤ B * ((n : ℝ) + 2) * ((n : ℝ) + 1) * R ^ n := by
          gcongr
        _ ≤ B * ((n : ℝ) + 2) ^ 2 * R ^ n := by
          have hcommon :
              0 ≤ B * ((n : ℝ) + 2) * R ^ n := by positivity
          calc
            B * ((n : ℝ) + 2) * ((n : ℝ) + 1) * R ^ n =
                (B * ((n : ℝ) + 2) * R ^ n) * ((n : ℝ) + 1) := by ring
            _ ≤ (B * ((n : ℝ) + 2) * R ^ n) * ((n : ℝ) + 2) :=
              mul_le_mul_of_nonneg_left (by linarith) hcommon
            _ = B * ((n : ℝ) + 2) ^ 2 * R ^ n := by ring
        _ = u (n + 1) := by
          dsimp [u]
          norm_num [Nat.cast_add, Nat.cast_one, pow_succ]
          field_simp [hR0.ne']
          ring
  have hzero : (0 : ℝ) ∈ Set.Ioo (-R) R := by
    constructor <;> linarith
  have hrmem : r ∈ Set.Ioo (-R) R := abs_lt.mp hrR
  have hsum0 : Summable
      (fun n : ℕ ↦ hermiteBilinearCoeff x y n * (0 : ℝ) ^ n) :=
    summable_hermiteBilinearCoeff_mul_pow (by norm_num) x y
  have hderiv := hasDerivAt_tsum_of_isPreconnected
    (g := fun n : ℕ ↦ fun z : ℝ ↦ hermiteBilinearCoeff x y n * z ^ n)
    (g' := fun n : ℕ ↦ fun z : ℝ ↦
      hermiteBilinearCoeff x y n * (n : ℝ) * z ^ (n - 1))
    (u := u) (t := Set.Ioo (-R) R) (y₀ := 0) (y := r)
    hu isOpen_Ioo isPreconnected_Ioo hterm htermBound hzero hsum0 hrmem
  change HasDerivAt
    (fun z : ℝ ↦ ∑' n : ℕ, hermiteBilinearCoeff x y n * z ^ n)
    (∑' n : ℕ,
      hermiteBilinearCoeff x y n * (n : ℝ) * r ^ (n - 1)) r
  exact hderiv

/-- Summability of the shifted derivative coefficients on the open unit
disk. -/
theorem summable_hermiteBilinearDerivativeShiftTerm
    {r : ℝ} (hr : |r| < 1) (x y : ℝ) :
    Summable (fun n : ℕ ↦
      ((n : ℝ) + 1) * hermiteBilinearCoeff x y (n + 1) * r ^ n) := by
  let B := hermiteBilinearCoeffBound x y
  have hB : 0 ≤ B := (hermiteBilinearCoeffBound_pos x y).le
  have hnorm : ‖|r|‖ < 1 := by
    simpa [Real.norm_eq_abs, abs_abs] using hr
  have h₂ : Summable (fun n : ℕ ↦ (n : ℝ) ^ 2 * |r| ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one 2 hnorm
  have h₁ : Summable (fun n : ℕ ↦ (n : ℝ) * |r| ^ n) := by
    simpa only [pow_one] using
      (summable_pow_mul_geometric_of_norm_lt_one 1 hnorm)
  have h₀ : Summable (fun n : ℕ ↦ |r| ^ n) :=
    summable_geometric_of_lt_one (abs_nonneg r) hr
  have hmajorant :
      Summable (fun n : ℕ ↦ B * ((n : ℝ) + 2) ^ 2 * |r| ^ n) := by
    have hpoly :
        Summable (fun n : ℕ ↦ ((n : ℝ) + 2) ^ 2 * |r| ^ n) := by
      convert (h₂.add (h₁.mul_left 4)).add (h₀.mul_left 4) using 1
      ext n
      ring
    simpa only [mul_assoc] using hpoly.mul_left B
  apply hmajorant.of_norm_bounded
  intro n
  have hc := abs_hermiteBilinearCoeff_le x y (n + 1)
  have hc' : |hermiteBilinearCoeff x y (n + 1)| ≤
      B * Real.sqrt ((n : ℝ) + 2) := by
    simpa only [B, Nat.cast_add, Nat.cast_one, add_assoc,
      one_add_one_eq_two] using hc
  have hsqrt : Real.sqrt ((n : ℝ) + 2) ≤ (n : ℝ) + 2 := by
    nlinarith [Real.sq_sqrt (by positivity : 0 ≤ (n : ℝ) + 2),
      Real.sqrt_nonneg ((n : ℝ) + 2)]
  rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_pow, abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) + 1)]
  calc
    ((n : ℝ) + 1) * |hermiteBilinearCoeff x y (n + 1)| * |r| ^ n ≤
        ((n : ℝ) + 1) * (B * Real.sqrt ((n : ℝ) + 2)) * |r| ^ n := by
      gcongr
    _ ≤ B * ((n : ℝ) + 2) ^ 2 * |r| ^ n := by
      have hrpow : 0 ≤ |r| ^ n := by positivity
      have hcommon : 0 ≤ B * |r| ^ n := mul_nonneg hB hrpow
      calc
        ((n : ℝ) + 1) * (B * Real.sqrt ((n : ℝ) + 2)) * |r| ^ n =
            (B * |r| ^ n) *
              (((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 2)) := by ring
        _ ≤ (B * |r| ^ n) * (((n : ℝ) + 2) ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ hcommon
          nlinarith
        _ = B * ((n : ℝ) + 2) ^ 2 * |r| ^ n := by ring

/-- The derivative series can equivalently be indexed from its first
nonzero term. -/
theorem hermiteBilinearDerivativeSeries_eq_shift
    {r : ℝ} (hr : |r| < 1) (x y : ℝ) :
    hermiteBilinearDerivativeSeries x y r =
      ∑' n : ℕ,
        ((n : ℝ) + 1) * hermiteBilinearCoeff x y (n + 1) * r ^ n := by
  let f : ℕ → ℝ := fun n ↦
    hermiteBilinearCoeff x y n * (n : ℝ) * r ^ (n - 1)
  have htail : Summable (fun n : ℕ ↦ f (n + 1)) := by
    convert summable_hermiteBilinearDerivativeShiftTerm hr x y using 1
    ext n
    dsimp [f]
    rw [Nat.cast_add, Nat.cast_one]
    ring
  have hf : Summable f := (summable_nat_add_iff 1).mp htail
  have hsum := hf.sum_add_tsum_nat_add 1
  have hf0 : f 0 = 0 := by simp [f]
  have heq : (∑' n : ℕ, f n) = ∑' n : ℕ, f (n + 1) := by
    simpa only [Finset.sum_range_one, hf0, zero_add] using hsum.symm
  change (∑' n : ℕ, f n) =
    ∑' n : ℕ,
      ((n : ℝ) + 1) * hermiteBilinearCoeff x y (n + 1) * r ^ n
  calc
    (∑' n : ℕ, f n) = ∑' n : ℕ, f (n + 1) := heq
    _ = ∑' n : ℕ,
        ((n : ℝ) + 1) * hermiteBilinearCoeff x y (n + 1) * r ^ n := by
      apply tsum_congr
      intro n
      dsimp [f]
      rw [Nat.cast_add, Nat.cast_one]
      ring

private theorem summable_shiftedCoeff_mul_pow
    (a : ℕ → ℝ) (r : ℝ) (d : ℕ)
    (ha : Summable (fun n : ℕ ↦ a n * r ^ n)) :
    Summable (fun k : ℕ ↦
      (if d ≤ k then a (k - d) else 0) * r ^ k) := by
  let f : ℕ → ℝ := fun k ↦
    (if d ≤ k then a (k - d) else 0) * r ^ k
  have htail : Summable (fun n : ℕ ↦ f (n + d)) := by
    have hscaled := ha.mul_left (r ^ d)
    apply hscaled.congr
    intro n
    simp only [f, ite_eq_left (Nat.le_add_left d n), Nat.add_sub_cancel,
      pow_add]
    ring
  exact (summable_nat_add_iff d).mp htail

private theorem tsum_shiftedCoeff_mul_pow
    (a : ℕ → ℝ) (r : ℝ) (d : ℕ)
    (ha : Summable (fun n : ℕ ↦ a n * r ^ n)) :
    (∑' k : ℕ, (if d ≤ k then a (k - d) else 0) * r ^ k) =
      r ^ d * ∑' n : ℕ, a n * r ^ n := by
  let f : ℕ → ℝ := fun k ↦
    (if d ≤ k then a (k - d) else 0) * r ^ k
  have hf : Summable f := summable_shiftedCoeff_mul_pow a r d ha
  have hsum := hf.sum_add_tsum_nat_add d
  have hprefix : ∑ i ∈ Finset.range d, f i = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hid : ¬ d ≤ i := Nat.not_le.mpr (Finset.mem_range.mp hi)
    simp [f, hid]
  have htail : (fun n : ℕ ↦ f (n + d)) =
      fun n : ℕ ↦ r ^ d * (a n * r ^ n) := by
    funext n
    simp only [f, ite_eq_left (Nat.le_add_left d n), Nat.add_sub_cancel,
      pow_add]
    ring
  change (∑' k : ℕ, f k) = r ^ d * ∑' n : ℕ, a n * r ^ n
  calc
    (∑' k : ℕ, f k) = ∑' n : ℕ, f (n + d) := by
      rw [hprefix, zero_add] at hsum
      exact hsum.symm
    _ = ∑' n : ℕ, r ^ d * (a n * r ^ n) := by rw [htail]
    _ = r ^ d * ∑' n : ℕ, a n * r ^ n := tsum_mul_left

/-- The convergent bilinear Hermite series satisfies the numerical Mehler
ODE throughout the open unit interval. -/
theorem hermiteBilinearSeries_ode
    {r : ℝ} (hr : |r| < 1) (x y : ℝ) :
    (1 - r ^ 2) ^ 2 * hermiteBilinearDerivativeSeries x y r =
      (x * y + (1 - x ^ 2 - y ^ 2) * r +
          (x * y) * r ^ 2 - r ^ 3) *
        hermiteBilinearSeries x y r := by
  let c : ℕ → ℝ := hermiteBilinearCoeff x y
  let D0 : ℕ → ℝ := fun k ↦
    ((k : ℝ) + 1) * c (k + 1) * r ^ k
  let D2 : ℕ → ℝ := fun k ↦
    (if 2 ≤ k then 2 * (k - 1 : ℝ) * c (k - 1) else 0) * r ^ k
  let D4 : ℕ → ℝ := fun k ↦
    (if 4 ≤ k then (k - 3 : ℝ) * c (k - 3) else 0) * r ^ k
  let P0 : ℕ → ℝ := fun k ↦ c k * r ^ k
  let Q0 : ℕ → ℝ := fun k ↦ (x * y) * c k * r ^ k
  let P1 : ℕ → ℝ := fun k ↦
    (if 1 ≤ k then (1 - x ^ 2 - y ^ 2) * c (k - 1) else 0) * r ^ k
  let P2 : ℕ → ℝ := fun k ↦
    (if 2 ≤ k then (x * y) * c (k - 2) else 0) * r ^ k
  let P3 : ℕ → ℝ := fun k ↦
    (if 3 ≤ k then c (k - 3) else 0) * r ^ k
  have hP0 : Summable P0 := by
    simpa only [P0, c] using summable_hermiteBilinearCoeff_mul_pow hr x y
  have hD0 : Summable D0 := by
    simpa only [D0, c] using
      summable_hermiteBilinearDerivativeShiftTerm hr x y
  have hQ0 : Summable Q0 := by
    apply (hP0.mul_left (x * y)).congr
    intro k
    dsimp [P0, Q0]
    ring
  have hsumP0 : (∑' k : ℕ, P0 k) = hermiteBilinearSeries x y r := by
    rfl
  have hsumD0 : (∑' k : ℕ, D0 k) =
      hermiteBilinearDerivativeSeries x y r := by
    simpa only [D0, c] using
      (hermiteBilinearDerivativeSeries_eq_shift hr x y).symm
  have haD2 : Summable (fun n : ℕ ↦
      (2 * (((n : ℝ) + 1) * c (n + 1))) * r ^ n) := by
    apply (hD0.mul_left 2).congr
    intro n
    dsimp [D0]
    ring
  have hD2generic := summable_shiftedCoeff_mul_pow
    (fun n : ℕ ↦ 2 * (((n : ℝ) + 1) * c (n + 1))) r 2 haD2
  have hD2 : Summable D2 := by
    apply hD2generic.congr
    intro k
    dsimp [D2]
    split_ifs with hk
    · have hidx : k - 2 + 1 = k - 1 := by omega
      have hcast : (((k - 2 : ℕ) : ℝ) + 1) = (k : ℝ) - 1 := by
        rw [Nat.cast_sub hk]
        ring
      rw [hidx, hcast]
      ring
    · rfl
  have hsumAD2 :
      (∑' n : ℕ, (2 * (((n : ℝ) + 1) * c (n + 1))) * r ^ n) =
        2 * ∑' n : ℕ, D0 n := by
    calc
      (∑' n : ℕ, (2 * (((n : ℝ) + 1) * c (n + 1))) * r ^ n) =
          ∑' n : ℕ, 2 * D0 n := by
            apply tsum_congr
            intro n
            dsimp [D0]
            ring
      _ = 2 * ∑' n : ℕ, D0 n := tsum_mul_left
  have hsumD2 : (∑' k : ℕ, D2 k) =
      2 * r ^ 2 * hermiteBilinearDerivativeSeries x y r := by
    calc
      (∑' k : ℕ, D2 k) =
          ∑' k : ℕ,
            (if 2 ≤ k then
              2 * ((((k - 2 : ℕ) : ℝ) + 1) * c (k - 2 + 1))
            else 0) * r ^ k := by
              apply tsum_congr
              intro k
              dsimp [D2]
              split_ifs with hk
              · have hidx : k - 2 + 1 = k - 1 := by omega
                have hcast : (((k - 2 : ℕ) : ℝ) + 1) = (k : ℝ) - 1 := by
                  rw [Nat.cast_sub hk]
                  ring
                rw [hidx, hcast]
                ring
              · rfl
      _ = r ^ 2 *
          ∑' n : ℕ, (2 * (((n : ℝ) + 1) * c (n + 1))) * r ^ n :=
            tsum_shiftedCoeff_mul_pow
              (fun n : ℕ ↦ 2 * (((n : ℝ) + 1) * c (n + 1))) r 2 haD2
      _ = 2 * r ^ 2 * hermiteBilinearDerivativeSeries x y r := by
            rw [hsumAD2, hsumD0]
            ring
  have hD4generic := summable_shiftedCoeff_mul_pow
    (fun n : ℕ ↦ ((n : ℝ) + 1) * c (n + 1)) r 4 hD0
  have hD4 : Summable D4 := by
    apply hD4generic.congr
    intro k
    dsimp [D4]
    split_ifs with hk
    · have hidx : k - 4 + 1 = k - 3 := by omega
      have hcast : (((k - 4 : ℕ) : ℝ) + 1) = (k : ℝ) - 3 := by
        rw [Nat.cast_sub hk]
        ring
      rw [hidx, hcast]
    · rfl
  have hsumD4 : (∑' k : ℕ, D4 k) =
      r ^ 4 * hermiteBilinearDerivativeSeries x y r := by
    calc
      (∑' k : ℕ, D4 k) =
          ∑' k : ℕ,
            (if 4 ≤ k then
              (((k - 4 : ℕ) : ℝ) + 1) * c (k - 4 + 1)
            else 0) * r ^ k := by
              apply tsum_congr
              intro k
              dsimp [D4]
              split_ifs with hk
              · have hidx : k - 4 + 1 = k - 3 := by omega
                have hcast : (((k - 4 : ℕ) : ℝ) + 1) = (k : ℝ) - 3 := by
                  rw [Nat.cast_sub hk]
                  ring
                rw [hidx, hcast]
              · rfl
      _ = r ^ 4 * ∑' n : ℕ, (((n : ℝ) + 1) * c (n + 1)) * r ^ n :=
            tsum_shiftedCoeff_mul_pow
              (fun n : ℕ ↦ ((n : ℝ) + 1) * c (n + 1)) r 4 hD0
      _ = r ^ 4 * hermiteBilinearDerivativeSeries x y r := by
            rw [hsumD0]
  let A : ℝ := 1 - x ^ 2 - y ^ 2
  have haP1 : Summable (fun n : ℕ ↦ (A * c n) * r ^ n) := by
    apply (hP0.mul_left A).congr
    intro n
    dsimp [P0]
    ring
  have hP1generic := summable_shiftedCoeff_mul_pow
    (fun n : ℕ ↦ A * c n) r 1 haP1
  have hP1 : Summable P1 := by
    apply hP1generic.congr
    intro k
    simp only [P1, A]
  have hsumAP1 : (∑' n : ℕ, (A * c n) * r ^ n) =
      A * ∑' n : ℕ, P0 n := by
    calc
      (∑' n : ℕ, (A * c n) * r ^ n) = ∑' n : ℕ, A * P0 n := by
        apply tsum_congr
        intro n
        dsimp [P0]
        ring
      _ = A * ∑' n : ℕ, P0 n := tsum_mul_left
  have hsumP1 : (∑' k : ℕ, P1 k) =
      A * r * hermiteBilinearSeries x y r := by
    calc
      (∑' k : ℕ, P1 k) =
          r ^ 1 * ∑' n : ℕ, (A * c n) * r ^ n :=
            tsum_shiftedCoeff_mul_pow (fun n : ℕ ↦ A * c n) r 1 haP1
      _ = A * r * hermiteBilinearSeries x y r := by
            rw [hsumAP1, hsumP0]
            ring
  have haP2 : Summable (fun n : ℕ ↦ ((x * y) * c n) * r ^ n) := by
    apply (hP0.mul_left (x * y)).congr
    intro n
    dsimp [P0]
    ring
  have hP2generic := summable_shiftedCoeff_mul_pow
    (fun n : ℕ ↦ (x * y) * c n) r 2 haP2
  have hP2 : Summable P2 := by
    apply hP2generic.congr
    intro k
    rfl
  have hsumP2 : (∑' k : ℕ, P2 k) =
      (x * y) * r ^ 2 * hermiteBilinearSeries x y r := by
    calc
      (∑' k : ℕ, P2 k) =
          r ^ 2 * ∑' n : ℕ, ((x * y) * c n) * r ^ n :=
            tsum_shiftedCoeff_mul_pow (fun n : ℕ ↦ (x * y) * c n) r 2 haP2
      _ = (x * y) * r ^ 2 * hermiteBilinearSeries x y r := by
        rw [show (∑' n : ℕ, ((x * y) * c n) * r ^ n) =
            (x * y) * ∑' n : ℕ, P0 n by
          calc
            (∑' n : ℕ, ((x * y) * c n) * r ^ n) =
                ∑' n : ℕ, (x * y) * P0 n := by
                  apply tsum_congr
                  intro n
                  dsimp [P0]
                  ring
            _ = (x * y) * ∑' n : ℕ, P0 n := tsum_mul_left,
          hsumP0]
        ring
  have hP3generic := summable_shiftedCoeff_mul_pow c r 3 hP0
  have hP3 : Summable P3 := by
    apply hP3generic.congr
    intro k
    rfl
  have hsumP3 : (∑' k : ℕ, P3 k) =
      r ^ 3 * hermiteBilinearSeries x y r := by
    calc
      (∑' k : ℕ, P3 k) = r ^ 3 * ∑' n : ℕ, c n * r ^ n :=
        tsum_shiftedCoeff_mul_pow c r 3 hP0
      _ = r ^ 3 * hermiteBilinearSeries x y r := by
        rw [← hsumP0]
  have hpoint : ∀ k : ℕ,
      (D0 k - D2 k) + D4 k = ((Q0 k + P1 k) + P2 k) - P3 k := by
    intro k
    have hrec := hermiteBilinearCoeff_ode_recurrence x y k
    dsimp only [D0, D2, D4, Q0, P1, P2, P3, c]
    have hmul := congrArg (fun q : ℝ ↦ q * r ^ k) hrec
    convert hmul using 1 <;> ring
  have hsumEq :
      (∑' k : ℕ, ((D0 k - D2 k) + D4 k)) =
        (∑' k : ℕ, (((Q0 k + P1 k) + P2 k) - P3 k)) :=
    tsum_congr hpoint
  have hsumL :
      (∑' k : ℕ, ((D0 k - D2 k) + D4 k)) =
        hermiteBilinearDerivativeSeries x y r -
          2 * r ^ 2 * hermiteBilinearDerivativeSeries x y r +
          r ^ 4 * hermiteBilinearDerivativeSeries x y r := by
    rw [(hD0.sub hD2).tsum_add hD4, hD0.tsum_sub hD2,
      hsumD0, hsumD2, hsumD4]
  have hsumR :
      (∑' k : ℕ, (((Q0 k + P1 k) + P2 k) - P3 k)) =
        (x * y) * hermiteBilinearSeries x y r +
            A * r * hermiteBilinearSeries x y r +
            (x * y) * r ^ 2 * hermiteBilinearSeries x y r -
          r ^ 3 * hermiteBilinearSeries x y r := by
    rw [((hQ0.add hP1).add hP2).tsum_sub hP3,
      (hQ0.add hP1).tsum_add hP2, hQ0.tsum_add hP1,
      hsumP1, hsumP2, hsumP3]
    rw [show (∑' k : ℕ, Q0 k) =
        (x * y) * hermiteBilinearSeries x y r by
      calc
        (∑' k : ℕ, Q0 k) = (x * y) * ∑' k : ℕ, P0 k := by
          calc
            (∑' k : ℕ, Q0 k) = ∑' k : ℕ, (x * y) * P0 k := by
              apply tsum_congr
              intro k
              dsimp [Q0, P0]
              ring
            _ = (x * y) * ∑' k : ℕ, P0 k := tsum_mul_left
        _ = (x * y) * hermiteBilinearSeries x y r := by rw [hsumP0]]
  rw [hsumL, hsumR] at hsumEq
  dsimp only [A] at hsumEq
  calc
    (1 - r ^ 2) ^ 2 * hermiteBilinearDerivativeSeries x y r =
        hermiteBilinearDerivativeSeries x y r -
          2 * r ^ 2 * hermiteBilinearDerivativeSeries x y r +
          r ^ 4 * hermiteBilinearDerivativeSeries x y r := by ring
    _ = (x * y) * hermiteBilinearSeries x y r +
            (1 - x ^ 2 - y ^ 2) * r * hermiteBilinearSeries x y r +
            (x * y) * r ^ 2 * hermiteBilinearSeries x y r -
          r ^ 3 * hermiteBilinearSeries x y r := hsumEq
    _ = (x * y + (1 - x ^ 2 - y ^ 2) * r +
          (x * y) * r ^ 2 - r ^ 3) *
        hermiteBilinearSeries x y r := by ring

/-- The closed Gaussian candidate for the bilinear probabilists' Hermite
series. -/
def hermiteBilinearClosed (x y r : ℝ) : ℝ :=
  (Real.sqrt (1 - r ^ 2))⁻¹ *
    Real.exp
      ((2 * r * x * y - r ^ 2 * (x ^ 2 + y ^ 2)) /
        (2 * (1 - r ^ 2)))

@[simp]
theorem hermiteBilinearClosed_zero (x y : ℝ) :
    hermiteBilinearClosed x y 0 = 1 := by
  simp [hermiteBilinearClosed]

theorem hermiteBilinearClosed_ne_zero
    {r : ℝ} (hr : |r| < 1) (x y : ℝ) :
    hermiteBilinearClosed x y r ≠ 0 := by
  have hr2 : r ^ 2 < 1 := by
    rw [← sq_abs]
    simpa only [pow_two, one_mul] using
      mul_self_lt_mul_self (abs_nonneg r) hr
  have hq : 0 < 1 - r ^ 2 := by
    linarith
  unfold hermiteBilinearClosed
  positivity

/-- The closed Gaussian satisfies the same numerical Mehler ODE as the
convergent bilinear series. -/
theorem hasDerivAt_hermiteBilinearClosed
    {r : ℝ} (hr : |r| < 1) (x y : ℝ) :
    HasDerivAt (hermiteBilinearClosed x y)
      (((x * y + (1 - x ^ 2 - y ^ 2) * r +
          (x * y) * r ^ 2 - r ^ 3) / (1 - r ^ 2) ^ 2) *
        hermiteBilinearClosed x y r) r := by
  let q : ℝ → ℝ := fun s ↦ 1 - s ^ 2
  let N : ℝ → ℝ := fun s ↦
    2 * s * x * y - s ^ 2 * (x ^ 2 + y ^ 2)
  let E : ℝ → ℝ := fun s ↦ N s / (2 * q s)
  have hr2 : r ^ 2 < 1 := by
    rw [← sq_abs]
    simpa only [pow_two, one_mul] using
      mul_self_lt_mul_self (abs_nonneg r) hr
  have hqpos : 0 < q r := by
    dsimp [q]
    linarith
  have hq : HasDerivAt q (-2 * r) r := by
    have hraw := (hasDerivAt_const r 1).sub (hasDerivAt_pow 2 r)
    apply hraw.congr_deriv
    simp only [Nat.cast_ofNat, pow_succ, pow_zero, zero_sub]
    ring
  have hsqrt : HasDerivAt (fun s ↦ Real.sqrt (q s))
      ((-2 * r) / (2 * Real.sqrt (q r))) r :=
    hq.sqrt hqpos.ne'
  have hinv : HasDerivAt (fun s ↦ (Real.sqrt (q s))⁻¹)
      (-((-2 * r) / (2 * Real.sqrt (q r))) /
        (Real.sqrt (q r)) ^ 2) r :=
    hsqrt.inv (Real.sqrt_pos.2 hqpos).ne'
  have hN : HasDerivAt N
      (2 * x * y - 2 * r * (x ^ 2 + y ^ 2)) r := by
    have hraw :=
      ((((hasDerivAt_id r).const_mul 2).mul_const x).mul_const y).sub
        ((hasDerivAt_pow 2 r).mul_const (x ^ 2 + y ^ 2))
    apply hraw.congr_deriv
    simp only [Nat.cast_ofNat, pow_succ, pow_zero, mul_one]
    ring
  have hden : HasDerivAt (fun s ↦ 2 * q s) (-4 * r) r := by
    apply (hq.const_mul 2).congr_deriv
    ring
  have hE : HasDerivAt E
      (((2 * x * y - 2 * r * (x ^ 2 + y ^ 2)) * (2 * q r) -
          N r * (-4 * r)) / (2 * q r) ^ 2) r := by
    dsimp only [E]
    exact hN.div hden (by positivity)
  have hexp := hE.exp
  have hmul := hinv.mul hexp
  change HasDerivAt
    ((fun s : ℝ ↦ (Real.sqrt (q s))⁻¹) *
      fun s : ℝ ↦ Real.exp (E s))
    (((x * y + (1 - x ^ 2 - y ^ 2) * r +
        (x * y) * r ^ 2 - r ^ 3) / (1 - r ^ 2) ^ 2) *
      ((Real.sqrt (q r))⁻¹ * Real.exp (E r))) r
  apply hmul.congr_deriv
  have hsqrtne : Real.sqrt (q r) ≠ 0 := (Real.sqrt_pos.2 hqpos).ne'
  have hsqrtSq : Real.sqrt (q r) ^ 2 = q r :=
    Real.sq_sqrt hqpos.le
  dsimp [q, N, E] at *
  field_simp [hqpos.ne', hsqrtne]
  rw [hsqrtSq]
  ring

/-- The bilinear probabilists' Hermite generating series is exactly the
closed Mehler Gaussian on `(-1,1)`. -/
theorem hermiteBilinearSeries_eq_closed
    {r : ℝ} (hr : |r| < 1) (x y : ℝ) :
    hermiteBilinearSeries x y r = hermiteBilinearClosed x y r := by
  let Q : ℝ → ℝ := fun s ↦
    hermiteBilinearSeries x y s / hermiteBilinearClosed x y s
  have hQderiv : ∀ z : ℝ, z ∈ Set.Ioo (-1) 1 → HasDerivAt Q 0 z := by
    intro z hz
    have hzabs : |z| < 1 := abs_lt.mpr hz
    have hqne : 1 - z ^ 2 ≠ 0 := by
      have hz2 : z ^ 2 < 1 := by
        rw [← sq_abs]
        simpa only [pow_two, one_mul] using
          mul_self_lt_mul_self (abs_nonneg z) hzabs
      linarith
    let A : ℝ :=
      (x * y + (1 - x ^ 2 - y ^ 2) * z +
        (x * y) * z ^ 2 - z ^ 3) / (1 - z ^ 2) ^ 2
    have hP := hasDerivAt_hermiteBilinearSeries hzabs x y
    have hPode := hermiteBilinearSeries_ode hzabs x y
    have hDP : hermiteBilinearDerivativeSeries x y z =
        A * hermiteBilinearSeries x y z := by
      dsimp only [A]
      rw [div_mul_eq_mul_div]
      apply (eq_div_iff (pow_ne_zero 2 hqne)).2
      rw [mul_comm]
      exact hPode
    have hP' := hP.congr_deriv hDP
    have hF := hasDerivAt_hermiteBilinearClosed hzabs x y
    have hFne := hermiteBilinearClosed_ne_zero hzabs x y
    change HasDerivAt
      (fun s : ℝ ↦
        hermiteBilinearSeries x y s / hermiteBilinearClosed x y s) 0 z
    apply (hP'.div hF hFne).congr_deriv
    dsimp only [A]
    ring
  have hQdiff : DifferentiableOn ℝ Q (Set.Ioo (-1) 1) := by
    intro z hz
    exact (hQderiv z hz).differentiableAt.differentiableWithinAt
  have hQderivZero : Set.EqOn (deriv Q) 0 (Set.Ioo (-1) 1) := by
    intro z hz
    simpa using (hQderiv z hz).deriv
  have hzero : (0 : ℝ) ∈ Set.Ioo (-1) 1 := by norm_num
  have hrmem : r ∈ Set.Ioo (-1) 1 := abs_lt.mp hr
  have hconst : Q 0 = Q r :=
    isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
      hQdiff hQderivZero hzero hrmem
  have hQr : Q r = 1 := by
    calc
      Q r = Q 0 := hconst.symm
      _ = 1 := by simp [Q]
  exact (div_eq_one_iff_eq (hermiteBilinearClosed_ne_zero hr x y)).mp hQr

/-- Exact conversion of a normalized Hermite product into a bilinear
probabilists' coefficient at the Fourier-compatible spatial scale. -/
theorem star_normalizedHermiteSchwartz_mul_eq_bilinearCoeff
    (X Y : ℝ) (n : ℕ) :
    starRingEnd ℂ (normalizedHermiteSchwartz n X) *
        normalizedHermiteSchwartz n Y =
      ((Real.sqrt 2 *
          hermiteBilinearCoeff
            (2 * Real.sqrt Real.pi * X)
            (2 * Real.sqrt Real.pi * Y) n *
          Real.exp (-Real.pi * (X ^ 2 + Y ^ 2)) : ℝ) : ℂ) := by
  have hsqrt : Real.sqrt Real.pi ≠ 0 :=
    (Real.sqrt_pos.2 Real.pi_pos).ne'
  have hxcoord :
      (2 * Real.sqrt Real.pi * X) / (2 * Real.sqrt Real.pi) = X := by
    field_simp
  have hycoord :
      (2 * Real.sqrt Real.pi * Y) / (2 * Real.sqrt Real.pi) = Y := by
    field_simp
  have hx := normalizedHermiteSchwartz_rescaled_apply n
    (2 * Real.sqrt Real.pi * X)
  have hy := normalizedHermiteSchwartz_rescaled_apply n
    (2 * Real.sqrt Real.pi * Y)
  rw [hxcoord] at hx
  rw [hycoord] at hy
  have hx' : normalizedHermiteSchwartz n X =
      ((hermiteFunctionNormalization n *
        probabilistsHermiteValue n (2 * Real.sqrt Real.pi * X) *
        Real.exp (-((2 * Real.sqrt Real.pi * X) ^ 2 / 4)) : ℝ) : ℂ) := by
    rw [hx, ← Complex.ofReal_exp]
    push_cast
    rfl
  have hy' : normalizedHermiteSchwartz n Y =
      ((hermiteFunctionNormalization n *
        probabilistsHermiteValue n (2 * Real.sqrt Real.pi * Y) *
        Real.exp (-((2 * Real.sqrt Real.pi * Y) ^ 2 / 4)) : ℝ) : ℂ) := by
    rw [hy, ← Complex.ofReal_exp]
    push_cast
    rfl
  rw [hx', hy', Complex.conj_ofReal]
  norm_cast
  rw [hermiteBilinearCoeff]
  have hexp :
      Real.exp (-((2 * Real.sqrt Real.pi * X) ^ 2 / 4)) *
          Real.exp (-((2 * Real.sqrt Real.pi * Y) ^ 2 / 4)) =
        Real.exp (-Real.pi * (X ^ 2 + Y ^ 2)) := by
    rw [← Real.exp_add]
    congr 1
    rw [show (2 * Real.sqrt Real.pi * X) ^ 2 =
        4 * (Real.sqrt Real.pi) ^ 2 * X ^ 2 by ring,
      show (2 * Real.sqrt Real.pi * Y) ^ 2 =
        4 * (Real.sqrt Real.pi) ^ 2 * Y ^ 2 by ring]
    rw [Real.sq_sqrt Real.pi_pos.le]
    ring
  calc
    hermiteFunctionNormalization n *
          probabilistsHermiteValue n (2 * Real.sqrt Real.pi * X) *
          Real.exp (-((2 * Real.sqrt Real.pi * X) ^ 2 / 4)) *
        (hermiteFunctionNormalization n *
          probabilistsHermiteValue n (2 * Real.sqrt Real.pi * Y) *
          Real.exp (-((2 * Real.sqrt Real.pi * Y) ^ 2 / 4))) =
      hermiteFunctionNormalization n ^ 2 *
        (probabilistsHermiteValue n (2 * Real.sqrt Real.pi * X) *
          probabilistsHermiteValue n (2 * Real.sqrt Real.pi * Y)) *
        (Real.exp (-((2 * Real.sqrt Real.pi * X) ^ 2 / 4)) *
          Real.exp (-((2 * Real.sqrt Real.pi * Y) ^ 2 / 4))) := by ring
    _ = (Real.sqrt 2 / (n.factorial : ℝ)) *
        (probabilistsHermiteValue n (2 * Real.sqrt Real.pi * X) *
          probabilistsHermiteValue n (2 * Real.sqrt Real.pi * Y)) *
        (Real.exp (-((2 * Real.sqrt Real.pi * X) ^ 2 / 4)) *
          Real.exp (-((2 * Real.sqrt Real.pi * Y) ^ 2 / 4))) := by
            rw [hermiteFunctionNormalization_sq]
    _ = Real.sqrt 2 *
        (probabilistsHermiteValue n (2 * Real.sqrt Real.pi * X) *
          probabilistsHermiteValue n (2 * Real.sqrt Real.pi * Y) /
            (n.factorial : ℝ)) *
        Real.exp (-Real.pi * (X ^ 2 + Y ^ 2)) := by
          rw [hexp]
          ring

/-- The repository-normalized Mehler series is the rescaled bilinear
probabilists' series times the common Gaussian factor. -/
theorem hermiteMehlerSeries_eq_bilinearSeries
    (r X Y : ℝ) :
    hermiteMehlerSeries r X Y =
      ((Real.sqrt 2 * Real.exp (-Real.pi * (X ^ 2 + Y ^ 2)) : ℝ) : ℂ) *
        (hermiteBilinearSeries
          (2 * Real.sqrt Real.pi * X)
          (2 * Real.sqrt Real.pi * Y) r : ℂ) := by
  rw [hermiteMehlerSeries]
  calc
    (∑' n : ℕ, hermiteMehlerTerm r X Y n) =
        ∑' n : ℕ,
          ((Real.sqrt 2 * Real.exp (-Real.pi * (X ^ 2 + Y ^ 2)) : ℝ) : ℂ) *
            ((hermiteBilinearCoeff
              (2 * Real.sqrt Real.pi * X)
              (2 * Real.sqrt Real.pi * Y) n * r ^ n : ℝ) : ℂ) := by
      apply tsum_congr
      intro n
      rw [hermiteMehlerTerm,
        show ((r ^ n : ℝ) : ℂ) *
              starRingEnd ℂ (normalizedHermiteSchwartz n X) *
              normalizedHermiteSchwartz n Y =
            ((r ^ n : ℝ) : ℂ) *
              (starRingEnd ℂ (normalizedHermiteSchwartz n X) *
                normalizedHermiteSchwartz n Y) by ring,
        star_normalizedHermiteSchwartz_mul_eq_bilinearCoeff]
      push_cast
      ring
    _ = ((Real.sqrt 2 * Real.exp (-Real.pi * (X ^ 2 + Y ^ 2)) : ℝ) : ℂ) *
        ∑' n : ℕ,
          ((hermiteBilinearCoeff
            (2 * Real.sqrt Real.pi * X)
            (2 * Real.sqrt Real.pi * Y) n * r ^ n : ℝ) : ℂ) :=
      tsum_mul_left
    _ = ((Real.sqrt 2 * Real.exp (-Real.pi * (X ^ 2 + Y ^ 2)) : ℝ) : ℂ) *
        (hermiteBilinearSeries
          (2 * Real.sqrt Real.pi * X)
          (2 * Real.sqrt Real.pi * Y) r : ℂ) := by
      rw [hermiteBilinearSeries, Complex.ofReal_tsum]

/-- Closed real Gaussian for the repository-normalized Mehler kernel. -/
def normalizedHermiteMehlerClosed (r X Y : ℝ) : ℝ :=
  Real.sqrt 2 / Real.sqrt (1 - r ^ 2) *
    Real.exp
      (-Real.pi *
        (((1 + r ^ 2) * (X ^ 2 + Y ^ 2) - 4 * r * X * Y) /
          (1 - r ^ 2)))

/-- Closed Mehler formula in the exact Fourier normalization used by this
repository. -/
theorem hermiteMehlerSeries_eq_closed
    {r : ℝ} (hr : |r| < 1) (X Y : ℝ) :
    hermiteMehlerSeries r X Y =
      (normalizedHermiteMehlerClosed r X Y : ℂ) := by
  rw [hermiteMehlerSeries_eq_bilinearSeries,
    hermiteBilinearSeries_eq_closed hr,
    hermiteBilinearClosed]
  have hr2 : r ^ 2 < 1 := by
    rw [← sq_abs]
    simpa only [pow_two, one_mul] using
      mul_self_lt_mul_self (abs_nonneg r) hr
  have hqpos : 0 < 1 - r ^ 2 := by linarith
  have hsqrtne : Real.sqrt (1 - r ^ 2) ≠ 0 :=
    (Real.sqrt_pos.2 hqpos).ne'
  norm_cast
  unfold normalizedHermiteMehlerClosed
  have hexp :
      Real.exp (-Real.pi * (X ^ 2 + Y ^ 2)) *
          Real.exp
            ((2 * r * (2 * Real.sqrt Real.pi * X) *
                  (2 * Real.sqrt Real.pi * Y) -
                r ^ 2 *
                  ((2 * Real.sqrt Real.pi * X) ^ 2 +
                    (2 * Real.sqrt Real.pi * Y) ^ 2)) /
              (2 * (1 - r ^ 2))) =
        Real.exp
          (-Real.pi *
            (((1 + r ^ 2) * (X ^ 2 + Y ^ 2) - 4 * r * X * Y) /
              (1 - r ^ 2))) := by
    rw [← Real.exp_add]
    congr 1
    rw [show (2 * Real.sqrt Real.pi * X) ^ 2 =
        4 * (Real.sqrt Real.pi) ^ 2 * X ^ 2 by ring,
      show (2 * Real.sqrt Real.pi * Y) ^ 2 =
        4 * (Real.sqrt Real.pi) ^ 2 * Y ^ 2 by ring,
      show 2 * r * (2 * Real.sqrt Real.pi * X) *
          (2 * Real.sqrt Real.pi * Y) =
        8 * (Real.sqrt Real.pi) ^ 2 * r * X * Y by ring,
      Real.sq_sqrt Real.pi_pos.le]
    field_simp [hqpos.ne']
    ring
  calc
    Real.sqrt 2 * Real.exp (-Real.pi * (X ^ 2 + Y ^ 2)) *
          ((Real.sqrt (1 - r ^ 2))⁻¹ *
            Real.exp
              ((2 * r * (2 * Real.sqrt Real.pi * X) *
                    (2 * Real.sqrt Real.pi * Y) -
                  r ^ 2 *
                    ((2 * Real.sqrt Real.pi * X) ^ 2 +
                      (2 * Real.sqrt Real.pi * Y) ^ 2)) /
                (2 * (1 - r ^ 2)))) =
        Real.sqrt 2 * (Real.sqrt (1 - r ^ 2))⁻¹ *
          (Real.exp (-Real.pi * (X ^ 2 + Y ^ 2)) *
            Real.exp
              ((2 * r * (2 * Real.sqrt Real.pi * X) *
                    (2 * Real.sqrt Real.pi * Y) -
                  r ^ 2 *
                    ((2 * Real.sqrt Real.pi * X) ^ 2 +
                      (2 * Real.sqrt Real.pi * Y) ^ 2)) /
                (2 * (1 - r ^ 2)))) := by ring
    _ = Real.sqrt 2 * (Real.sqrt (1 - r ^ 2))⁻¹ *
        Real.exp
          (-Real.pi *
            (((1 + r ^ 2) * (X ^ 2 + Y ^ 2) - 4 * r * X * Y) /
              (1 - r ^ 2))) := by rw [hexp]
    _ = Real.sqrt 2 / Real.sqrt (1 - r ^ 2) *
        Real.exp
          (-Real.pi *
            (((1 + r ^ 2) * (X ^ 2 + Y ^ 2) - 4 * r * X * Y) /
              (1 - r ^ 2))) := by
      rw [div_eq_mul_inv]
      ring

/-- Heat-time specialization of the exact normalized Mehler formula. -/
theorem hermiteHeatKernel_eq_closed
    {t : ℝ} (ht : 0 < t) (X Y : ℝ) :
    hermiteHeatKernel t X Y =
      (normalizedHermiteMehlerClosed (Real.exp (-t)) X Y : ℂ) := by
  unfold hermiteHeatKernel
  apply hermiteMehlerSeries_eq_closed
  rw [abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]
  linarith

/-- Exact sum/difference decomposition of the Mehler quadratic form. -/
theorem mehlerQuadratic_eq_sumDiff
    {r : ℝ} (hr : |r| < 1) (X Y : ℝ) :
    ((1 + r ^ 2) * (X ^ 2 + Y ^ 2) - 4 * r * X * Y) /
        (1 - r ^ 2) =
      (1 - r) / (2 * (1 + r)) * (X + Y) ^ 2 +
        (1 + r) / (2 * (1 - r)) * (X - Y) ^ 2 := by
  have hrange := abs_lt.mp hr
  have hplus : 1 + r ≠ 0 := by linarith
  have hminus : 1 - r ≠ 0 := by linarith
  have hsq : 1 - r ^ 2 ≠ 0 := by
    have hr2 : r ^ 2 < 1 := by
      rw [← sq_abs]
      simpa only [pow_two, one_mul] using
        mul_self_lt_mul_self (abs_nonneg r) hr
    linarith
  field_simp [hplus, hminus, hsq]
  ring

/-- The closed normalized kernel in its two-coordinate Gaussian form. -/
theorem normalizedHermiteMehlerClosed_eq_sumDiff
    {r : ℝ} (hr : |r| < 1) (X Y : ℝ) :
    normalizedHermiteMehlerClosed r X Y =
      Real.sqrt 2 / Real.sqrt (1 - r ^ 2) *
        Real.exp
          (-Real.pi *
            ((1 - r) / (2 * (1 + r)) * (X + Y) ^ 2 +
              (1 + r) / (2 * (1 - r)) * (X - Y) ^ 2)) := by
  unfold normalizedHermiteMehlerClosed
  rw [mehlerQuadratic_eq_sumDiff hr]

/-- Weighted arithmetic-geometric-mean estimate intrinsic to the Mehler
sum/difference coordinates. -/
theorem abs_sum_mul_diff_le_mehlerSumDiff
    {r : ℝ} (hr : |r| < 1) (u v : ℝ) :
    |u * v| ≤
      (1 - r) / (2 * (1 + r)) * u ^ 2 +
        (1 + r) / (2 * (1 - r)) * v ^ 2 := by
  have hrange := abs_lt.mp hr
  have hplus : 0 < 1 + r := by linarith
  have hminus : 0 < 1 - r := by linarith
  have hsqpos : 0 < 1 - r ^ 2 := by nlinarith
  let W : ℝ :=
    (1 - r) / (2 * (1 + r)) * u ^ 2 +
      (1 + r) / (2 * (1 - r)) * v ^ 2
  have hminusSquare :
      (2 * (1 - r ^ 2)) * (W - u * v) =
        ((1 - r) * u - (1 + r) * v) ^ 2 := by
    dsimp [W]
    field_simp [hplus.ne', hminus.ne']
    ring
  have hplusSquare :
      (2 * (1 - r ^ 2)) * (W + u * v) =
        ((1 - r) * u + (1 + r) * v) ^ 2 := by
    dsimp [W]
    field_simp [hplus.ne', hminus.ne']
    ring
  by_cases huv : 0 ≤ u * v
  · rw [abs_of_nonneg huv]
    have hprod : 0 ≤ (2 * (1 - r ^ 2)) * (W - u * v) := by
      rw [hminusSquare]
      positivity
    have : 0 ≤ W - u * v :=
      nonneg_of_mul_nonneg_right hprod (by positivity)
    exact sub_nonneg.mp this
  · rw [abs_of_nonpos (le_of_not_ge huv)]
    have hprod : 0 ≤ (2 * (1 - r ^ 2)) * (W + u * v) := by
      rw [hplusSquare]
      positivity
    have : 0 ≤ W + u * v :=
      nonneg_of_mul_nonneg_right hprod (by positivity)
    linarith

/-- The Mehler quadratic controls the distance in signed-square
coordinates.  This is the genuine off-diagonal quantity used by the carrier
shell decomposition. -/
theorem abs_mul_abs_sub_mul_abs_le_mehlerQuadratic
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (X Y : ℝ) :
    |X * abs X - Y * abs Y| ≤
      ((1 + r ^ 2) * (X ^ 2 + Y ^ 2) - 4 * r * X * Y) /
        (1 - r ^ 2) := by
  have hr : |r| < 1 := by
    rw [abs_of_nonneg hr0]
    exact hr1
  have hqpos : 0 < 1 - r ^ 2 := by nlinarith
  by_cases hxy : 0 ≤ X * Y
  · have hsigned :
        |X * abs X - Y * abs Y| = |(X + Y) * (X - Y)| := by
      rcases mul_nonneg_iff.mp hxy with hsame | hsame
      · rw [abs_of_nonneg hsame.1, abs_of_nonneg hsame.2]
        congr 1
        ring
      · rw [abs_of_nonpos hsame.1, abs_of_nonpos hsame.2]
        rw [show X * -X - Y * -Y = -(X ^ 2 - Y ^ 2) by ring,
          show (X + Y) * (X - Y) = X ^ 2 - Y ^ 2 by ring,
          abs_neg]
    rw [mehlerQuadratic_eq_sumDiff hr, hsigned]
    exact abs_sum_mul_diff_le_mehlerSumDiff hr (X + Y) (X - Y)
  · have hxy' : X * Y < 0 := lt_of_not_ge hxy
    have hsigned : |X * abs X - Y * abs Y| = X ^ 2 + Y ^ 2 := by
      rcases mul_neg_iff.mp hxy' with hsign | hsign
      · rw [abs_of_pos hsign.1, abs_of_neg hsign.2]
        rw [abs_of_pos]
        · ring
        · nlinarith [sq_nonneg X, sq_nonneg Y]
      · rw [abs_of_neg hsign.1, abs_of_pos hsign.2]
        rw [abs_of_neg]
        · ring
        · nlinarith [sq_nonneg X, sq_nonneg Y]
    rw [hsigned]
    have hdiff :
        (((1 + r ^ 2) * (X ^ 2 + Y ^ 2) - 4 * r * X * Y) /
            (1 - r ^ 2)) - (X ^ 2 + Y ^ 2) =
          (2 * r * (r * (X ^ 2 + Y ^ 2) - 2 * X * Y)) /
            (1 - r ^ 2) := by
      field_simp [hqpos.ne']
      ring
    rw [← sub_nonneg]
    rw [hdiff]
    have hinner : 0 ≤ r * (X ^ 2 + Y ^ 2) - 2 * X * Y := by
      nlinarith [sq_nonneg X, sq_nonneg Y]
    exact div_nonneg (mul_nonneg (mul_nonneg (by positivity) hr0) hinner) hqpos.le

/-- The exact Mehler kernel has Gaussian decay in the signed-square
coordinate `X * |X|`.  Unlike a one-variable remainder, this estimate is a
genuine off-diagonal bound in both kernel variables. -/
theorem norm_normalizedHermiteMehlerClosed_le_signedSquare
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (X Y : ℝ) :
    ‖(normalizedHermiteMehlerClosed r X Y : ℂ)‖ ≤
      Real.sqrt 2 / Real.sqrt (1 - r ^ 2) *
        Real.exp (-Real.pi * |X * abs X - Y * abs Y|) := by
  have hqpos : 0 < 1 - r ^ 2 := by nlinarith
  have hpref : 0 ≤ Real.sqrt 2 / Real.sqrt (1 - r ^ 2) :=
    div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  rw [Complex.norm_real, Real.norm_eq_abs]
  unfold normalizedHermiteMehlerClosed
  rw [abs_of_nonneg (mul_nonneg hpref (Real.exp_pos _).le)]
  apply mul_le_mul_of_nonneg_left _ hpref
  apply Real.exp_le_exp.mpr
  have hquad :=
    abs_mul_abs_sub_mul_abs_le_mehlerQuadratic hr0 hr1 X Y
  nlinarith [Real.pi_pos]

/-- Heat-time form of signed-square Gaussian decay for the Hermite Mehler
kernel. -/
theorem norm_hermiteHeatKernel_le_signedSquare
    {t : ℝ} (ht : 0 < t) (X Y : ℝ) :
    ‖hermiteHeatKernel t X Y‖ ≤
      Real.sqrt 2 / Real.sqrt (1 - Real.exp (-t) ^ 2) *
        Real.exp (-Real.pi * |X * abs X - Y * abs Y|) := by
  rw [hermiteHeatKernel_eq_closed ht]
  apply norm_normalizedHermiteMehlerClosed_le_signedSquare
  · exact (Real.exp_pos _).le
  · rw [Real.exp_lt_one_iff]
    linarith

end

end MeyerGeneralProblem
