module

public import MeyerGeneralProblem.Atomic.HermitePointMass
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import all Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import all Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
import all Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

/-!
# Hermite Mehler and resolvent kernels

This module builds the analytic bridge between the concrete Hermite
point-mass Gram series and a Mehler integral.  It packages the genuine
pointwise Mehler series, proves its absolute convergence throughout the open
unit disk, records the exact Gamma/Laplace representation of the negative
Hermite-scale coefficient weight, and justifies exchanging the spectral
`tsum` with the Laplace integral at every repository order `m ≥ 1`.

The companion `MehlerFormula` module proves the closed Gaussian formula and
its signed-square off-diagonal decay.  The later carrier shell summation is
kept separate from this spectral/Laplace bridge.
-/

namespace MeyerGeneralProblem

noncomputable section

open scoped ComplexConjugate

/-- The `n`th term in the pointwise Mehler series for the repository's
Fourier-normalized Hermite functions. -/
def hermiteMehlerTerm (r x y : ℝ) (n : ℕ) : ℂ :=
  ((r ^ n : ℝ) : ℂ) *
    starRingEnd ℂ (normalizedHermiteSchwartz n x) *
      normalizedHermiteSchwartz n y

/-- The product of two normalized Hermite values has only square-root
spectral growth, uniformly in both spatial variables.  Retaining this sharper
bound (rather than weakening it to linear growth) is what makes the later
Laplace-integral norms summable already at `m = 1`. -/
theorem norm_star_normalizedHermiteSchwartz_mul_le
    (x y : ℝ) (n : ℕ) :
    ‖starRingEnd ℂ (normalizedHermiteSchwartz n x) *
        normalizedHermiteSchwartz n y‖ ≤
      (2 * Real.sqrt (2 * Real.pi)) * Real.sqrt ((n : ℝ) + 1) := by
  let A : ℝ := 2 * Real.sqrt (2 * Real.pi)
  let u : ℝ := ‖normalizedHermiteSchwartz n x‖
  let v : ℝ := ‖normalizedHermiteSchwartz n y‖
  have hu : u ^ 2 ≤ A * Real.sqrt ((n : ℝ) + 1) := by
    simpa only [u, A] using normalizedHermiteSchwartz_norm_sq_le n x
  have hv : v ^ 2 ≤ A * Real.sqrt ((n : ℝ) + 1) := by
    simpa only [v, A] using normalizedHermiteSchwartz_norm_sq_le n y
  have huv : u * v ≤ A * Real.sqrt ((n : ℝ) + 1) := by
    have hamgm : 2 * (u * v) ≤ u ^ 2 + v ^ 2 := by
      nlinarith [sq_nonneg (u - v)]
    nlinarith
  simpa only [norm_mul, RCLike.norm_conj, u, v, A] using huv

/-- A uniform polynomial-geometric majorant for the pointwise Mehler terms.
The deliberately coarse linear power is enough to prove absolute convergence
for every `|r| < 1`. -/
theorem norm_hermiteMehlerTerm_le (r x y : ℝ) (n : ℕ) :
    ‖hermiteMehlerTerm r x y n‖ ≤
      (2 * Real.sqrt (2 * Real.pi)) * ((n : ℝ) + 1) * |r| ^ n := by
  let A : ℝ := 2 * Real.sqrt (2 * Real.pi)
  have huv := norm_star_normalizedHermiteSchwartz_mul_le x y n
  have hsqrt : Real.sqrt ((n : ℝ) + 1) ≤ (n : ℝ) + 1 := by
    have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hone : 1 ≤ (n : ℝ) + 1 := by linarith
    nlinarith [Real.sq_sqrt (by positivity : 0 ≤ (n : ℝ) + 1),
      Real.sqrt_nonneg ((n : ℝ) + 1)]
  calc
    ‖hermiteMehlerTerm r x y n‖ = |r| ^ n *
        ‖starRingEnd ℂ (normalizedHermiteSchwartz n x) *
          normalizedHermiteSchwartz n y‖ := by
      simp only [hermiteMehlerTerm, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, norm_pow]
      ring
    _ ≤ |r| ^ n * (A * Real.sqrt ((n : ℝ) + 1)) := by
      exact mul_le_mul_of_nonneg_left huv (by positivity)
    _ ≤ |r| ^ n * (A * ((n : ℝ) + 1)) := by
      gcongr
    _ = A * ((n : ℝ) + 1) * |r| ^ n := by ring

/-- Absolute convergence of the pointwise Mehler series on the real open
unit disk. -/
theorem summable_hermiteMehlerTerm {r : ℝ} (hr : |r| < 1) (x y : ℝ) :
    Summable (hermiteMehlerTerm r x y) := by
  let A : ℝ := 2 * Real.sqrt (2 * Real.pi)
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
  apply (hgeom.mul_left A).of_norm_bounded
  intro n
  simpa only [A, mul_assoc] using norm_hermiteMehlerTerm_le r x y n

/-- The genuine pointwise Mehler series. -/
def hermiteMehlerSeries (r x y : ℝ) : ℂ :=
  ∑' n : ℕ, hermiteMehlerTerm r x y n

/-- At `r = 0`, only the zeroth Hermite mode remains. -/
theorem hermiteMehlerSeries_zero (x y : ℝ) :
    hermiteMehlerSeries 0 x y =
      starRingEnd ℂ (normalizedHermiteSchwartz 0 x) *
        normalizedHermiteSchwartz 0 y := by
  rw [hermiteMehlerSeries, tsum_eq_single 0]
  · simp [hermiteMehlerTerm]
  · intro n hn
    simp [hermiteMehlerTerm, hn]

/-- The heat-parameter form of the Mehler series.  Positivity of `t` places
the geometric parameter strictly inside the unit disk. -/
def hermiteHeatKernel (t x y : ℝ) : ℂ :=
  hermiteMehlerSeries (Real.exp (-t)) x y

theorem summable_hermiteHeatKernel_term {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    Summable (hermiteMehlerTerm (Real.exp (-t)) x y) := by
  apply summable_hermiteMehlerTerm
  rw [abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]
  linarith

/-- The exact `n`th spectral term of the order-`-m` Hermite point-mass
kernel, written with the positive integer power that the Laplace formula
below consumes. -/
def hermiteResolventTerm (m : ℕ) (x y : ℝ) (n : ℕ) : ℂ :=
  (((((n : ℝ) + 1)⁻¹) ^ (2 * m) : ℝ) : ℂ) *
    starRingEnd ℂ (normalizedHermiteSchwartz n x) *
      normalizedHermiteSchwartz n y

/-- The normalized negative-scale Dirac coefficients have exactly the
resolvent spectral product, with no hidden conjugation or phase. -/
theorem star_hermiteDiracCoefficients_mul_eq_resolventTerm
    (m : ℕ) (x y : ℝ) (n : ℕ) :
    starRingEnd ℂ (hermiteDiracCoefficients m x n) *
        hermiteDiracCoefficients m y n =
      hermiteResolventTerm m x y n := by
  let a : ℝ := (n : ℝ) + 1
  have hb : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hw : a ^ (-(m : ℤ)) * a ^ (-(m : ℤ)) = (a⁻¹) ^ (2 * m) := by
    have ha : a ≠ 0 := by
      dsimp [a]
      exact hb.ne'
    have hexp : (-(m : ℤ)) + (-(m : ℤ)) = -((2 * m : ℕ) : ℤ) := by
      omega
    rw [← zpow_add₀ ha, hexp, zpow_neg, zpow_natCast, inv_pow]
  change
    starRingEnd ℂ
        ((((a ^ (-(m : ℤ)) : ℝ) : ℂ) * normalizedHermiteSchwartz n x)) *
          (((a ^ (-(m : ℤ)) : ℝ) : ℂ) * normalizedHermiteSchwartz n y) =
      ((((a⁻¹) ^ (2 * m) : ℝ) : ℂ) *
        starRingEnd ℂ (normalizedHermiteSchwartz n x) *
          normalizedHermiteSchwartz n y)
  rw [map_mul, Complex.conj_ofReal]
  push_cast
  have hwc :
      (a : ℂ) ^ (-(m : ℤ)) * (a : ℂ) ^ (-(m : ℤ)) =
        ((a : ℂ)⁻¹) ^ (2 * m) := by
    exact_mod_cast hw
  ring_nf
  rw [pow_two, hwc, show m * 2 = 2 * m by omega]
  ring

/-- The unnormalized same-side resolvent kernel of the negative Hermite
scale. -/
def hermiteResolventKernel (m : ℕ) (x y : ℝ) : ℂ :=
  ∑' n : ℕ, hermiteResolventTerm m x y n

/-- The inner product of the genuine negative-scale point masses is exactly
the resolvent kernel. -/
theorem inner_hermitePointMass_eq_resolventKernel
    (m : ℕ) (hm : 1 ≤ m) (x y : ℝ) :
    inner ℂ (hermitePointMass m hm x) (hermitePointMass m hm y) =
      hermiteResolventKernel m x y := by
  rw [lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  simp only [RCLike.inner_apply, hermitePointMass_apply]
  simpa only [mul_comm] using
    star_hermiteDiracCoefficients_mul_eq_resolventTerm m x y n

/-- Exact Laplace representation of the negative-scale spectral weight.
This is the coefficient identity needed to turn the Hermite Gram `tsum` into
an integral of the Mehler heat kernel. -/
theorem hermiteScaleWeight_laplace
    (m : ℕ) (hm : 1 ≤ m) (n : ℕ) :
    ∫ t : ℝ in Set.Ioi 0,
        t ^ ((2 * m : ℕ) - 1) * Real.exp (-(((n : ℝ) + 1) * t)) =
      ((2 * m - 1).factorial : ℝ) * (((n : ℝ) + 1)⁻¹) ^ (2 * m) := by
  have hmpos : 0 < (2 * m : ℝ) := by positivity
  have hnpos : 0 < (n : ℝ) + 1 := by positivity
  have hgamma := Real.integral_rpow_mul_exp_neg_mul_Ioi hmpos hnpos
  have hGamma : Real.Gamma (2 * m : ℝ) = ((2 * m - 1).factorial : ℝ) := by
    rw [show (2 * m : ℝ) = ((2 * m - 1 : ℕ) : ℝ) + 1 by
      norm_cast
      omega]
    exact Real.Gamma_nat_eq_factorial (2 * m - 1)
  have hweight : (1 / ((n : ℝ) + 1)) ^ (2 * m : ℝ) =
      (((n : ℝ) + 1)⁻¹) ^ (2 * m : ℕ) := by
    rw [show (2 * m : ℝ) = ((2 * m : ℕ) : ℝ) by norm_cast,
      Real.rpow_natCast, one_div]
  have hcast : ((2 * m - 1 : ℕ) : ℝ) = (2 * m : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 2 * m)]
    norm_num
  have hrpow : ∀ t : ℝ, t ∈ Set.Ioi 0 →
      t ^ ((2 * m : ℕ) - 1) = t ^ ((2 * m : ℝ) - 1) := by
    intro t ht
    rw [← hcast, Real.rpow_natCast]
  calc
    (∫ t : ℝ in Set.Ioi 0,
        t ^ ((2 * m : ℕ) - 1) * Real.exp (-(((n : ℝ) + 1) * t))) =
        ∫ t : ℝ in Set.Ioi 0,
          t ^ ((2 * m : ℝ) - 1) * Real.exp (-(((n : ℝ) + 1) * t)) := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      change t ^ ((2 * m : ℕ) - 1) * Real.exp (-(((n : ℝ) + 1) * t)) =
        t ^ ((2 * m : ℝ) - 1) * Real.exp (-(((n : ℝ) + 1) * t))
      rw [hrpow t ht]
    _ = (1 / ((n : ℝ) + 1)) ^ (2 * m : ℝ) * Real.Gamma (2 * m : ℝ) := hgamma
    _ = ((2 * m - 1).factorial : ℝ) *
        (((n : ℝ) + 1)⁻¹) ^ (2 * m) := by
      rw [hGamma, hweight]
      ring

/-- The real Gamma density whose integral is the order-`-m` spectral
weight.  Naming it separately keeps the later Bochner-integral argument tied
to the exact coefficient identity rather than to an informal heat-kernel
heuristic. -/
def hermiteLaplaceDensity (m n : ℕ) (t : ℝ) : ℝ :=
  t ^ ((2 * m : ℕ) - 1) * Real.exp (-(((n : ℝ) + 1) * t))

/-- The Gamma density is integrable on the positive half-line. -/
theorem integrableOn_hermiteLaplaceDensity
    (m n : ℕ) :
    MeasureTheory.IntegrableOn (hermiteLaplaceDensity m n) (Set.Ioi 0) := by
  have hs : (-1 : ℝ) < ((2 * m - 1 : ℕ) : ℝ) := by
    exact lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg _)
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow
    (p := (1 : ℝ)) (s := ((2 * m - 1 : ℕ) : ℝ))
    (b := (n : ℝ) + 1) hs zero_lt_one hn
  refine h.congr_fun ?_ measurableSet_Ioi
  intro t ht
  dsimp only
  rw [Real.rpow_natCast, Real.rpow_one, hermiteLaplaceDensity]
  congr 2
  ring

/-- The Gamma density is nonnegative on the positive half-line. -/
theorem hermiteLaplaceDensity_nonneg
    (m n : ℕ) {t : ℝ} (ht : t ∈ Set.Ioi 0) :
    0 ≤ hermiteLaplaceDensity m n t := by
  rw [hermiteLaplaceDensity]
  have ht0 : 0 ≤ t := le_of_lt ht
  positivity

/-- The exact integral of the named Gamma density. -/
theorem integral_hermiteLaplaceDensity
    (m : ℕ) (hm : 1 ≤ m) (n : ℕ) :
    ∫ t : ℝ in Set.Ioi 0, hermiteLaplaceDensity m n t =
      ((2 * m - 1).factorial : ℝ) * (((n : ℝ) + 1)⁻¹) ^ (2 * m) := by
  simpa only [hermiteLaplaceDensity] using hermiteScaleWeight_laplace m hm n

/-- The complex-valued termwise Laplace integrand for the Hermite resolvent
kernel. -/
def hermiteResolventLaplaceTerm
    (m : ℕ) (x y : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  ((hermiteLaplaceDensity m n t : ℝ) : ℂ) *
    starRingEnd ℂ (normalizedHermiteSchwartz n x) *
      normalizedHermiteSchwartz n y

/-- Each termwise resolvent integrand is Bochner-integrable on the positive
half-line. -/
theorem integrableOn_hermiteResolventLaplaceTerm
    (m : ℕ) (x y : ℝ) (n : ℕ) :
    MeasureTheory.IntegrableOn
      (hermiteResolventLaplaceTerm m x y n) (Set.Ioi 0) := by
  let c : ℂ := starRingEnd ℂ (normalizedHermiteSchwartz n x) *
    normalizedHermiteSchwartz n y
  have hreal := integrableOn_hermiteLaplaceDensity m n
  have hcomplex : MeasureTheory.IntegrableOn
      (fun t : ℝ ↦ ((hermiteLaplaceDensity m n t : ℝ) : ℂ)) (Set.Ioi 0) :=
    hreal.ofReal
  change MeasureTheory.Integrable
    (hermiteResolventLaplaceTerm m x y n)
      (MeasureTheory.volume.restrict (Set.Ioi 0))
  convert hcomplex.mul_const c using 1
  ext t
  simp only [hermiteResolventLaplaceTerm, c]
  ring

/-- Termwise Laplace representation of the concrete negative-scale Hermite
resolvent coefficient. -/
theorem integral_hermiteResolventLaplaceTerm
    (m : ℕ) (hm : 1 ≤ m) (x y : ℝ) (n : ℕ) :
    ∫ t : ℝ in Set.Ioi 0, hermiteResolventLaplaceTerm m x y n t =
      (((2 * m - 1).factorial : ℝ) : ℂ) *
        hermiteResolventTerm m x y n := by
  let c : ℂ := starRingEnd ℂ (normalizedHermiteSchwartz n x) *
    normalizedHermiteSchwartz n y
  calc
    (∫ t : ℝ in Set.Ioi 0, hermiteResolventLaplaceTerm m x y n t) =
        (∫ t : ℝ in Set.Ioi 0,
          ((hermiteLaplaceDensity m n t : ℝ) : ℂ)) * c := by
      simp only [hermiteResolventLaplaceTerm, c, mul_assoc,
        MeasureTheory.integral_mul_const]
    _ = (((2 * m - 1).factorial : ℝ) : ℂ) *
        hermiteResolventTerm m x y n := by
      have hcast :
          (∫ t : ℝ in Set.Ioi 0,
              ((hermiteLaplaceDensity m n t : ℝ) : ℂ)) =
            ((∫ t : ℝ in Set.Ioi 0,
              hermiteLaplaceDensity m n t : ℝ) : ℂ) :=
        integral_ofReal
      rw [hcast]
      rw [integral_hermiteLaplaceDensity m hm n]
      simp only [hermiteResolventTerm, c]
      push_cast
      ring

/-- The integral of the norm of a termwise Laplace integrand is its Gamma
weight times the norm of the corresponding Hermite-value product. -/
theorem integral_norm_hermiteResolventLaplaceTerm
    (m : ℕ) (hm : 1 ≤ m) (x y : ℝ) (n : ℕ) :
    ∫ t : ℝ in Set.Ioi 0,
        ‖hermiteResolventLaplaceTerm m x y n t‖ =
      ((2 * m - 1).factorial : ℝ) *
        (((n : ℝ) + 1)⁻¹) ^ (2 * m) *
          ‖starRingEnd ℂ (normalizedHermiteSchwartz n x) *
            normalizedHermiteSchwartz n y‖ := by
  let c : ℂ := starRingEnd ℂ (normalizedHermiteSchwartz n x) *
    normalizedHermiteSchwartz n y
  calc
    (∫ t : ℝ in Set.Ioi 0,
        ‖hermiteResolventLaplaceTerm m x y n t‖) =
        ∫ t : ℝ in Set.Ioi 0, hermiteLaplaceDensity m n t * ‖c‖ := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      simp only [hermiteResolventLaplaceTerm, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (hermiteLaplaceDensity_nonneg m n ht)]
      simp only [c]
      rw [norm_mul]
      ring
    _ = (∫ t : ℝ in Set.Ioi 0, hermiteLaplaceDensity m n t) * ‖c‖ := by
      exact MeasureTheory.integral_mul_const _ _
    _ = ((2 * m - 1).factorial : ℝ) *
        (((n : ℝ) + 1)⁻¹) ^ (2 * m) *
          ‖starRingEnd ℂ (normalizedHermiteSchwartz n x) *
            normalizedHermiteSchwartz n y‖ := by
      rw [integral_hermiteLaplaceDensity m hm n]

private theorem sqrt_div_sq_eq (b : ℝ) (hb : 0 < b) :
    Real.sqrt b / b ^ 2 = 1 / b ^ (3 / 2 : ℝ) := by
  rw [Real.sqrt_eq_rpow]
  field_simp
  rw [← Real.rpow_natCast b 2, ← Real.rpow_add hb]
  norm_num

/-- At every negative integer order `m ≥ 1`, the spectral Gamma weight times
the square-root Hermite growth is bounded by the summable `3/2`-power
majorant. -/
theorem hermiteLaplaceWeight_mul_sqrt_le
    (m : ℕ) (hm : 1 ≤ m) (n : ℕ) :
    (((n : ℝ) + 1)⁻¹) ^ (2 * m) * Real.sqrt ((n : ℝ) + 1) ≤
      1 / (((n : ℝ) + 1) ^ (3 / 2 : ℝ)) := by
  let b : ℝ := (n : ℝ) + 1
  have hb : 0 < b := by positivity
  have hb1 : 1 ≤ b := by
    dsimp [b]
    exact le_add_of_nonneg_left (Nat.cast_nonneg n)
  have hpow : b⁻¹ ^ (2 * m) ≤ b⁻¹ ^ 2 :=
    pow_le_pow_of_le_one (inv_nonneg.mpr hb.le)
      ((inv_le_one₀ hb).2 hb1) (by omega)
  calc
    b⁻¹ ^ (2 * m) * Real.sqrt b ≤ b⁻¹ ^ 2 * Real.sqrt b := by
      gcongr
    _ = Real.sqrt b / b ^ 2 := by field_simp
    _ = 1 / b ^ (3 / 2 : ℝ) := sqrt_div_sq_eq b hb

/-- A summable, spatially uniform majorant for the norms of all termwise
Laplace integrals.  This proves the `tsum`/integral exchange even in the
borderline repository order `m = 1`; no false pointwise-in-`t` domination is
used. -/
theorem integral_norm_hermiteResolventLaplaceTerm_le
    (m : ℕ) (hm : 1 ≤ m) (x y : ℝ) (n : ℕ) :
    ∫ t : ℝ in Set.Ioi 0,
        ‖hermiteResolventLaplaceTerm m x y n t‖ ≤
      (((2 * m - 1).factorial : ℝ) *
          (2 * Real.sqrt (2 * Real.pi))) /
        (((n : ℝ) + 1) ^ (3 / 2 : ℝ)) := by
  rw [integral_norm_hermiteResolventLaplaceTerm m hm x y n]
  let F : ℝ := ((2 * m - 1).factorial : ℝ)
  let A : ℝ := 2 * Real.sqrt (2 * Real.pi)
  have hprod := norm_star_normalizedHermiteSchwartz_mul_le x y n
  have hweight := hermiteLaplaceWeight_mul_sqrt_le m hm n
  have hF : 0 ≤ F := by positivity
  have hw : 0 ≤ (((n : ℝ) + 1)⁻¹) ^ (2 * m) := by positivity
  calc
    F * (((n : ℝ) + 1)⁻¹) ^ (2 * m) *
        ‖starRingEnd ℂ (normalizedHermiteSchwartz n x) *
          normalizedHermiteSchwartz n y‖ ≤
      F * (((n : ℝ) + 1)⁻¹) ^ (2 * m) *
        (A * Real.sqrt ((n : ℝ) + 1)) := by
          gcongr
    _ = (F * A) *
        ((((n : ℝ) + 1)⁻¹) ^ (2 * m) *
          Real.sqrt ((n : ℝ) + 1)) := by ring
    _ ≤ (F * A) * (1 / (((n : ℝ) + 1) ^ (3 / 2 : ℝ))) := by
      gcongr
    _ = (F * A) / (((n : ℝ) + 1) ^ (3 / 2 : ℝ)) := by ring

/-- The sequence of integrals of termwise norms is summable. -/
theorem summable_integral_norm_hermiteResolventLaplaceTerm
    (m : ℕ) (hm : 1 ≤ m) (x y : ℝ) :
    Summable (fun n : ℕ ↦
      ∫ t : ℝ in Set.Ioi 0,
        ‖hermiteResolventLaplaceTerm m x y n t‖) := by
  let C : ℝ := ((2 * m - 1).factorial : ℝ) *
    (2 * Real.sqrt (2 * Real.pi))
  have hs₀ : Summable (fun n : ℕ ↦
      1 / |(n : ℝ) + 1| ^ (3 / 2 : ℝ)) :=
    (Real.summable_one_div_nat_add_rpow 1 (3 / 2)).2 (by norm_num)
  have hs : Summable (fun n : ℕ ↦
      C / (((n : ℝ) + 1) ^ (3 / 2 : ℝ))) := by
    apply (hs₀.mul_left C).congr
    intro n
    rw [abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
    ring
  exact hs.of_nonneg_of_le
    (fun n ↦ MeasureTheory.integral_nonneg
      (fun t ↦ norm_nonneg (hermiteResolventLaplaceTerm m x y n t)))
    (fun n ↦ by
      simpa only [C] using
        integral_norm_hermiteResolventLaplaceTerm_le m hm x y n)

/-- The named Gamma-density integrand is exactly the heat-kernel Mehler term
times the common Laplace factor. -/
theorem hermiteResolventLaplaceTerm_eq_mehlerTerm
    (m : ℕ) (x y : ℝ) (n : ℕ) (t : ℝ) :
    hermiteResolventLaplaceTerm m x y n t =
      (((t ^ ((2 * m : ℕ) - 1) * Real.exp (-t) : ℝ) : ℂ)) *
        hermiteMehlerTerm (Real.exp (-t)) x y n := by
  have hexp :
      Real.exp (-(((n : ℝ) + 1) * t)) =
        Real.exp (-t) * Real.exp (-t) ^ n := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  rw [hermiteResolventLaplaceTerm, hermiteLaplaceDensity,
    hermiteMehlerTerm, hexp]
  push_cast
  ring

/-- After summing in the spectral index, the termwise Laplace integrand is
the genuine Mehler heat kernel multiplied by the common Gamma factor. -/
theorem tsum_hermiteResolventLaplaceTerm_eq_heatKernel
    (m : ℕ) (x y t : ℝ) :
    ∑' n : ℕ, hermiteResolventLaplaceTerm m x y n t =
      (((t ^ ((2 * m : ℕ) - 1) * Real.exp (-t) : ℝ) : ℂ)) *
        hermiteHeatKernel t x y := by
  simp_rw [hermiteResolventLaplaceTerm_eq_mehlerTerm]
  rw [tsum_mul_left]
  rfl

/-- The concrete resolvent kernel has a fully justified Laplace/Mehler
integral representation.  The equality is proved by summability of the
integrals of the termwise norms, so it remains valid at `m = 1`. -/
theorem factorial_mul_hermiteResolventKernel_eq_laplaceIntegral
    (m : ℕ) (hm : 1 ≤ m) (x y : ℝ) :
    (((2 * m - 1).factorial : ℝ) : ℂ) *
        hermiteResolventKernel m x y =
      ∫ t : ℝ in Set.Ioi 0,
        (((t ^ ((2 * m : ℕ) - 1) * Real.exp (-t) : ℝ) : ℂ)) *
          hermiteHeatKernel t x y := by
  have hexchange :=
    MeasureTheory.integral_tsum_of_summable_integral_norm
      (μ := MeasureTheory.volume.restrict (Set.Ioi 0))
      (fun n ↦ integrableOn_hermiteResolventLaplaceTerm m x y n)
      (summable_integral_norm_hermiteResolventLaplaceTerm m hm x y)
  calc
    (((2 * m - 1).factorial : ℝ) : ℂ) *
        hermiteResolventKernel m x y =
      ∑' n : ℕ, (((2 * m - 1).factorial : ℝ) : ℂ) *
        hermiteResolventTerm m x y n := by
          rw [hermiteResolventKernel, tsum_mul_left]
    _ = ∑' n : ℕ,
        ∫ t : ℝ in Set.Ioi 0,
          hermiteResolventLaplaceTerm m x y n t := by
      apply tsum_congr
      intro n
      exact (integral_hermiteResolventLaplaceTerm m hm x y n).symm
    _ = ∫ t : ℝ in Set.Ioi 0,
        ∑' n : ℕ, hermiteResolventLaplaceTerm m x y n t := hexchange
    _ = ∫ t : ℝ in Set.Ioi 0,
        (((t ^ ((2 * m : ℕ) - 1) * Real.exp (-t) : ℝ) : ℂ)) *
          hermiteHeatKernel t x y := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro t _
      exact tsum_hermiteResolventLaplaceTerm_eq_heatKernel m x y t

/-- Division by the positive factorial gives the conventional resolvent
kernel form of the Laplace/Mehler representation. -/
theorem hermiteResolventKernel_eq_laplaceIntegral
    (m : ℕ) (hm : 1 ≤ m) (x y : ℝ) :
    hermiteResolventKernel m x y =
      ((((2 * m - 1).factorial : ℝ)⁻¹ : ℝ) : ℂ) *
        ∫ t : ℝ in Set.Ioi 0,
          (((t ^ ((2 * m : ℕ) - 1) * Real.exp (-t) : ℝ) : ℂ)) *
            hermiteHeatKernel t x y := by
  have hfact : (((2 * m - 1).factorial : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (2 * m - 1)
  have hfact' : (((2 * m - 1).factorial : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (2 * m - 1)
  have h := factorial_mul_hermiteResolventKernel_eq_laplaceIntegral m hm x y
  rw [← h]
  push_cast
  field_simp [hfact']

end

end MeyerGeneralProblem
