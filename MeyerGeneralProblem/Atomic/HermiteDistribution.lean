module

public import MeyerGeneralProblem.Hermite.Orthonormal
public import MeyerGeneralProblem.Atomic.HermitePointMass
public import TauCeti.Analysis.SpecialFunctions.Hermite.Function.Operator
import all TauCeti.Analysis.SpecialFunctions.Hermite.Function.Operator
public import TauCeti.Analysis.SpecialFunctions.Hermite.Function.Oscillator
import all TauCeti.Analysis.SpecialFunctions.Hermite.Function.Oscillator
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import all Mathlib.MeasureTheory.Function.ConvergenceInMeasure

@[expose] public section

/-!
# Hermite reconstruction and distributional realization

This module constructs the continuous Hermite coefficient map from Schwartz
space into every positive integer Hermite scale. It proves pointwise Hermite
reconstruction for arbitrary Schwartz functions, realizes negative-scale
vectors as genuine tempered distributions, and verifies that the diagonal
Hermite Fourier transform agrees with distributional Fourier transform.
-/

open MeasureTheory
open Filter
open scoped ComplexConjugate
open scoped FourierTransform

namespace MeyerGeneralProblem

noncomputable section

/-- Continuous `ℓ²` Hermite coefficient map on complex Schwartz space. -/
def schwartzHermiteCoefficients : SchwartzMap ℝ ℂ →L[ℂ] CoefficientSpace ℕ :=
  (TauCeti.twoPiHermiteHilbertBasis ℂ).repr.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (SchwartzMap.toLpCLM ℂ ℂ 2 volume)


def hermiteOscillator : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
  ((4 * (Real.pi : ℂ))⁻¹) •
    (-(SchwartzMap.derivCLM ℂ ℂ).comp (SchwartzMap.derivCLM ℂ ℂ) +
      (4 * (Real.pi : ℂ) ^ 2) •
        coordinateMultiplicationCLM.comp coordinateMultiplicationCLM)

private theorem hermiteOscillator_apply (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    hermiteOscillator f x =
      (-deriv (deriv f) x + 4 * (Real.pi : ℂ) ^ 2 * (x : ℂ) ^ 2 * f x) /
        (4 * (Real.pi : ℂ)) := by
  have hD : ⇑(SchwartzMap.derivCLM ℂ ℂ f) = deriv f :=
    funext (SchwartzMap.derivCLM_apply ℂ f)
  simp [hermiteOscillator, coordinateMultiplicationCLM_apply, div_eq_inv_mul, hD]
  ring

private theorem hermite_hasDerivAt_twoPi_direct (n : ℕ) (x : ℝ) :
    HasDerivAt (TauCeti.twoPiHermiteFunction n)
      (Real.sqrt (Real.sqrt (2 * Real.pi)) * Real.sqrt (2 * Real.pi) *
        deriv (TauCeti.hermiteFunction n) (Real.sqrt (2 * Real.pi) * x)) x := by
  let a := Real.sqrt (Real.sqrt (2 * Real.pi))
  let s := Real.sqrt (2 * Real.pi)
  have hinner : HasDerivAt (fun y : ℝ => s * y) s x := by
    simpa [id_eq] using (hasDerivAt_id x).const_mul s
  have hcomp := (TauCeti.hasDerivAt_hermiteFunction n (s * x)).comp x hinner
  have h := hcomp.const_mul a
  have heq : (fun y => a * (TauCeti.hermiteFunction n ∘ fun z => s * z) y) =
      TauCeti.twoPiHermiteFunction n := by
    funext y
    exact (TauCeti.twoPiHermiteFunction_def n y).symm
  rw [heq] at h
  refine h.congr_deriv ?_
  rw [TauCeti.deriv_hermiteFunction]
  simp only [a, s]
  ring

private theorem hermite_hasDerivAt_deriv_twoPi (n : ℕ) (x : ℝ) :
    HasDerivAt (deriv (TauCeti.twoPiHermiteFunction n))
      (Real.sqrt (Real.sqrt (2 * Real.pi)) * (2 * Real.pi) *
        deriv (deriv (TauCeti.hermiteFunction n))
          (Real.sqrt (2 * Real.pi) * x)) x := by
  let a := Real.sqrt (Real.sqrt (2 * Real.pi))
  let s := Real.sqrt (2 * Real.pi)
  have hinner : HasDerivAt (fun y : ℝ => s * y) s x := by
    simpa [id_eq] using (hasDerivAt_id x).const_mul s
  have hcomp := (TauCeti.hasDerivAt_deriv_hermiteFunction n (s * x)).comp x hinner
  have h := hcomp.const_mul (a * s)
  have hfun : ∀ y : ℝ,
      deriv (TauCeti.twoPiHermiteFunction n) y =
        a * s * deriv (TauCeti.hermiteFunction n) (s * y) := by
    intro y
    exact (hermite_hasDerivAt_twoPi_direct n y).deriv
  have h' := h.congr_of_eventuallyEq (Filter.Eventually.of_forall hfun)
  refine h'.congr_deriv ?_
  rw [TauCeti.deriv_deriv_hermiteFunction]
  have hs : s ^ 2 = 2 * Real.pi := by
    simp only [s]
    exact Real.sq_sqrt (by positivity)
  calc
    a * s * (((s * x) ^ 2 - (2 * (n : ℝ) + 1)) *
        TauCeti.hermiteFunction n (s * x) * s) =
      a * s ^ 2 * (((s * x) ^ 2 - (2 * (n : ℝ) + 1)) *
        TauCeti.hermiteFunction n (s * x)) := by ring
    _ = a * (2 * Real.pi) * (((s * x) ^ 2 - (2 * (n : ℝ) + 1)) *
        TauCeti.hermiteFunction n (s * x)) := by rw [hs]
    _ = _ := by rfl

private theorem hermite_deriv_ofReal
    (g g' : ℝ → ℝ) (hg : ∀ x, HasDerivAt g (g' x) x) (x : ℝ) :
    deriv (fun y : ℝ => (g y : ℂ)) x = (g' x : ℂ) := by
  have h := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x (hg x)
  change deriv (Complex.ofRealCLM ∘ g) x = (g' x : ℂ)
  simpa only [Complex.ofRealCLM_apply] using h.deriv

private theorem hermite_deriv_deriv_ofReal (g : ℝ → ℝ)
    (hg : ∀ x, HasDerivAt g ((deriv g : ℝ → ℝ) x) x)
    (h2g : ∀ x, HasDerivAt (deriv g : ℝ → ℝ)
      ((deriv (deriv g) : ℝ → ℝ) x) x) (x : ℝ) :
    deriv (deriv (fun y : ℝ => (g y : ℂ))) x =
      ((deriv (deriv g) : ℝ → ℝ) x : ℂ) := by
  have hfun : deriv (fun y : ℝ => (g y : ℂ)) =
      fun y => ((deriv g : ℝ → ℝ) y : ℂ) := by
    funext y
    exact hermite_deriv_ofReal g (deriv g) hg y
  rw [hfun]
  exact hermite_deriv_ofReal (deriv g : ℝ → ℝ)
    (deriv (deriv g) : ℝ → ℝ) h2g x

private theorem hermite_twoPi_oscillator (n : ℕ) (x : ℝ) :
    -deriv (deriv (TauCeti.twoPiHermiteFunction n)) x +
        4 * Real.pi ^ 2 * x ^ 2 * TauCeti.twoPiHermiteFunction n x =
      4 * Real.pi * ((n : ℝ) + 1 / 2) *
        TauCeti.twoPiHermiteFunction n x := by
  rw [(hermite_hasDerivAt_deriv_twoPi n x).deriv,
    TauCeti.deriv_deriv_hermiteFunction,
    TauCeti.twoPiHermiteFunction_def]
  have hs : Real.sqrt (2 * Real.pi) ^ 2 = 2 * Real.pi :=
    Real.sq_sqrt (by positivity)
  rw [mul_pow, hs]
  ring

private theorem hermiteOscillator_eigen (n : ℕ) :
    hermiteOscillator (normalizedHermiteSchwartz n) =
      (((n : ℝ) + 1 / 2 : ℝ) : ℂ) • normalizedHermiteSchwartz n := by
  rw [normalizedHermiteSchwartz_eq_twoPi]
  ext x
  rw [hermiteOscillator_apply]
  have hd := hermite_deriv_deriv_ofReal
    (TauCeti.twoPiHermiteFunction n)
    (fun y => (TauCeti.hasDerivAt_twoPiHermiteFunction n y).differentiableAt.hasDerivAt)
    (fun y => (hermite_hasDerivAt_deriv_twoPi n y).differentiableAt.hasDerivAt) x
  have hcoe := TauCeti.coe_twoPiHermiteSchwartzMap n
  rw [hcoe, hd, smul_apply,
    TauCeti.twoPiHermiteSchwartzMap_apply]
  simp only [Complex.ofReal_add, Complex.ofReal_natCast,
    Complex.ofReal_ofNat, Complex.ofReal_div, Complex.ofReal_one]
  have h := congrArg Complex.ofReal (hermite_twoPi_oscillator n x)
  push_cast at h
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  linear_combination h

set_option maxHeartbeats 800000 in
/-- The `n`th Hermite coefficient is the integral against the real-valued
normalized Hermite function. -/
theorem schwartzHermiteCoefficients_apply_integral (f : SchwartzMap ℝ ℂ) (n : ℕ) :
    schwartzHermiteCoefficients f n =
      ∫ x : ℝ, normalizedHermiteSchwartz n x * f x := by
  change (TauCeti.twoPiHermiteHilbertBasis ℂ).repr (f.toLp 2) n = _
  rw [HilbertBasis.repr_apply_apply, TauCeti.coe_twoPiHermiteHilbertBasis,
    ← TauCeti.toLp_twoPiHermiteSchwartzMap, MeasureTheory.L2.inner_def]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [(TauCeti.twoPiHermiteSchwartzMap n).coeFn_toLp 2 volume,
    f.coeFn_toLp 2 volume] with x hx hf
  rw [hx, hf]
  simp only [RCLike.inner_apply]
  rw [normalizedHermiteSchwartz_eq_twoPi,
    TauCeti.twoPiHermiteSchwartzMap_apply]
  change f x * conj (TauCeti.twoPiHermiteFunction n x : ℂ) = _
  rw [Complex.conj_ofReal]
  ring

private theorem hermite_integrable_mul (f g : SchwartzMap ℝ ℂ) :
    Integrable (fun x : ℝ => f x * g x) volume := by
  change Integrable ⇑(SchwartzMap.pairing
    (ContinuousLinearMap.mul ℝ ℂ) f g) volume
  exact (SchwartzMap.pairing (ContinuousLinearMap.mul ℝ ℂ) f g).integrable

private theorem hermite_integral_second_deriv_symm
    (f g : SchwartzMap ℝ ℂ) :
    (∫ x : ℝ, g x * deriv (deriv f) x) =
      ∫ x : ℝ, deriv (deriv g) x * f x := by
  let Df := SchwartzMap.derivCLM ℂ ℂ f
  let Dg := SchwartzMap.derivCLM ℂ ℂ g
  have hDf : ⇑Df = deriv f := funext (SchwartzMap.derivCLM_apply ℂ f)
  have hDg : ⇑Dg = deriv g := funext (SchwartzMap.derivCLM_apply ℂ g)
  have h1 := SchwartzMap.integral_mul_deriv_eq_neg_deriv_mul g Df
  have h2 := SchwartzMap.integral_mul_deriv_eq_neg_deriv_mul Dg f
  rw [hDf] at h1
  have hDerivDg : deriv (⇑Dg) = deriv (deriv g) := congrArg deriv hDg
  calc
    (∫ x : ℝ, g x * deriv (deriv f) x) =
        -(∫ x : ℝ, deriv g x * deriv f x) := h1
    _ = ∫ x : ℝ, deriv (deriv g) x * f x := by
      rw [← hDg, h2, neg_neg, hDerivDg]

private theorem hermiteOscillator_integral_symm (f g : SchwartzMap ℝ ℂ) :
    (∫ x : ℝ, g x * hermiteOscillator f x) =
      ∫ x : ℝ, hermiteOscillator g x * f x := by
  have hdd := hermite_integral_second_deriv_symm f g
  have hpi : (4 * (Real.pi : ℂ)) ≠ 0 := by
    exact mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)
  have hgfdd : Integrable (fun x : ℝ => g x * deriv (deriv f) x) volume := by
    let DDf := (SchwartzMap.derivCLM ℂ ℂ) ((SchwartzMap.derivCLM ℂ ℂ) f)
    have hDDf : ⇑DDf = deriv (deriv f) := by
      funext x
      simp only [DDf, SchwartzMap.derivCLM_apply]
      have hDf : ⇑(SchwartzMap.derivCLM ℂ ℂ f) = deriv f :=
        funext (SchwartzMap.derivCLM_apply ℂ f)
      rw [hDf]
    simpa only [hDDf] using hermite_integrable_mul g DDf
  have hddgf : Integrable (fun x : ℝ => deriv (deriv g) x * f x) volume := by
    let DDg := (SchwartzMap.derivCLM ℂ ℂ) ((SchwartzMap.derivCLM ℂ ℂ) g)
    have hDDg : ⇑DDg = deriv (deriv g) := by
      funext x
      simp only [DDg, SchwartzMap.derivCLM_apply]
      have hDg : ⇑(SchwartzMap.derivCLM ℂ ℂ g) = deriv g :=
        funext (SchwartzMap.derivCLM_apply ℂ g)
      rw [hDg]
    simpa only [hDDg] using hermite_integrable_mul DDg f
  let X2f := coordinateMultiplicationCLM (coordinateMultiplicationCLM f)
  let X2g := coordinateMultiplicationCLM (coordinateMultiplicationCLM g)
  have hX2f : ∀ x, X2f x = (x : ℂ) ^ 2 * f x := by
    intro x
    simp only [X2f, coordinateMultiplicationCLM_apply]
    ring
  have hX2g : ∀ x, X2g x = (x : ℂ) ^ 2 * g x := by
    intro x
    simp only [X2g, coordinateMultiplicationCLM_apply]
    ring
  have hgX2f : Integrable (fun x : ℝ => g x * ((x : ℂ) ^ 2 * f x)) volume := by
    simpa only [hX2f] using hermite_integrable_mul g X2f
  have hX2gf : Integrable (fun x : ℝ => ((x : ℂ) ^ 2 * g x) * f x) volume := by
    simpa only [hX2g] using hermite_integrable_mul X2g f
  simp_rw [hermiteOscillator_apply]
  have hleft : (fun x : ℝ => g x *
      ((-deriv (deriv f) x + 4 * (Real.pi : ℂ) ^ 2 * (x : ℂ) ^ 2 * f x) /
        (4 * (Real.pi : ℂ)))) =
      fun x : ℝ => (g x *
        (-deriv (deriv f) x + 4 * (Real.pi : ℂ) ^ 2 * (x : ℂ) ^ 2 * f x)) /
          (4 * (Real.pi : ℂ)) := by
    funext x
    ring
  have hright : (fun x : ℝ =>
      ((-deriv (deriv g) x + 4 * (Real.pi : ℂ) ^ 2 * (x : ℂ) ^ 2 * g x) /
        (4 * (Real.pi : ℂ))) * f x) =
      fun x : ℝ =>
        ((-deriv (deriv g) x + 4 * (Real.pi : ℂ) ^ 2 * (x : ℂ) ^ 2 * g x) *
          f x) / (4 * (Real.pi : ℂ)) := by
    funext x
    ring
  rw [hleft, hright, MeasureTheory.integral_div, MeasureTheory.integral_div]
  congr 1
  have hnumLeft : (fun x : ℝ => g x *
      (-deriv (deriv f) x + 4 * (Real.pi : ℂ) ^ 2 * (x : ℂ) ^ 2 * f x)) =
      fun x : ℝ => -(g x * deriv (deriv f) x) +
        (4 * (Real.pi : ℂ) ^ 2) * (g x * ((x : ℂ) ^ 2 * f x)) := by
    funext x
    ring
  have hnumRight : (fun x : ℝ =>
      (-deriv (deriv g) x + 4 * (Real.pi : ℂ) ^ 2 * (x : ℂ) ^ 2 * g x) * f x) =
      fun x : ℝ => -(deriv (deriv g) x * f x) +
        (4 * (Real.pi : ℂ) ^ 2) * (((x : ℂ) ^ 2 * g x) * f x) := by
    funext x
    ring
  rw [hnumLeft, hnumRight]
  calc
    (∫ x : ℝ, -(g x * deriv (deriv f) x) +
        (4 * (Real.pi : ℂ) ^ 2) * (g x * ((x : ℂ) ^ 2 * f x))) =
      -(∫ x : ℝ, g x * deriv (deriv f) x) +
        (4 * (Real.pi : ℂ) ^ 2) *
          ∫ x : ℝ, g x * ((x : ℂ) ^ 2 * f x) := by
            rw [← MeasureTheory.integral_neg]
            rw [← MeasureTheory.integral_const_mul]
            exact MeasureTheory.integral_add hgfdd.neg
              (hgX2f.const_mul (4 * (Real.pi : ℂ) ^ 2))
    _ = -(∫ x : ℝ, deriv (deriv g) x * f x) +
        (4 * (Real.pi : ℂ) ^ 2) *
          ∫ x : ℝ, ((x : ℂ) ^ 2 * g x) * f x := by
            rw [hdd]
            apply congrArg₂ (· + ·) rfl
            congr 1
            apply MeasureTheory.integral_congr_ae
            filter_upwards with x
            ring
    _ = ∫ x : ℝ, -(deriv (deriv g) x * f x) +
        (4 * (Real.pi : ℂ) ^ 2) * (((x : ℂ) ^ 2 * g x) * f x) := by
            rw [← MeasureTheory.integral_neg]
            rw [← MeasureTheory.integral_const_mul]
            exact (MeasureTheory.integral_add hddgf.neg
              (hX2gf.const_mul (4 * (Real.pi : ℂ) ^ 2))).symm

private theorem schwartzHermiteCoefficients_osc (f : SchwartzMap ℝ ℂ) (n : ℕ) :
    schwartzHermiteCoefficients (hermiteOscillator f) n =
      (((n : ℝ) + 1 / 2 : ℝ) : ℂ) * schwartzHermiteCoefficients f n := by
  rw [schwartzHermiteCoefficients_apply_integral, hermiteOscillator_integral_symm,
    hermiteOscillator_eigen]
  simp only [smul_apply, smul_eq_mul]
  let c : ℂ := (((n : ℝ) + 1 / 2 : ℝ) : ℂ)
  calc
    (∫ x : ℝ, c * normalizedHermiteSchwartz n x * f x) =
        ∫ x : ℝ, c * (normalizedHermiteSchwartz n x * f x) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with x
          ring
    _ = c * ∫ x : ℝ, normalizedHermiteSchwartz n x * f x := by
      rw [MeasureTheory.integral_const_mul]
    _ = c * schwartzHermiteCoefficients f n := by rw [schwartzHermiteCoefficients_apply_integral]

def hermiteWeightOperator : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
  hermiteOscillator + (1 / 2 : ℂ) • ContinuousLinearMap.id ℂ (SchwartzMap ℝ ℂ)

private theorem schwartzHermiteCoefficients_weight (f : SchwartzMap ℝ ℂ) (n : ℕ) :
    schwartzHermiteCoefficients (hermiteWeightOperator f) n =
      (((n : ℝ) + 1 : ℝ) : ℂ) * schwartzHermiteCoefficients f n := by
  simp only [hermiteWeightOperator, add_apply, smul_apply, ContinuousLinearMap.id_apply,
    map_add, map_smul]
  change schwartzHermiteCoefficients (hermiteOscillator f) n + (1 / 2 : ℂ) * schwartzHermiteCoefficients f n = _
  rw [schwartzHermiteCoefficients_osc]
  push_cast
  ring

def hermiteWeightOperatorPower : ℕ → SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ
  | 0 => ContinuousLinearMap.id ℂ (SchwartzMap ℝ ℂ)
  | m + 1 => hermiteWeightOperator.comp (hermiteWeightOperatorPower m)

@[simp]
private theorem hermiteWeightOperatorPower_zero (f : SchwartzMap ℝ ℂ) :
    hermiteWeightOperatorPower 0 f = f := rfl

@[simp]
private theorem hermiteWeightOperatorPower_succ (m : ℕ) (f : SchwartzMap ℝ ℂ) :
    hermiteWeightOperatorPower (m + 1) f = hermiteWeightOperator (hermiteWeightOperatorPower m f) := rfl

private theorem schwartzHermiteCoefficients_weightPower
    (m : ℕ) (f : SchwartzMap ℝ ℂ) (n : ℕ) :
    schwartzHermiteCoefficients (hermiteWeightOperatorPower m f) n =
      ((((n : ℝ) + 1) ^ m : ℝ) : ℂ) * schwartzHermiteCoefficients f n := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [hermiteWeightOperatorPower_succ, schwartzHermiteCoefficients_weight, ih]
      push_cast
      rw [pow_succ]
      ring

/-- Continuous Hermite coefficient map from Schwartz space into the positive
integer scale `H_m`. -/
def schwartzToHermiteScale (m : ℕ) :
    SchwartzMap ℝ ℂ →L[ℂ] HermiteScale (m : ℤ) :=
  schwartzHermiteCoefficients.comp (hermiteWeightOperatorPower m)

/-- Normalized coordinates of `schwartzToHermiteScale m f` are
`(1+n)^m` times the raw Hermite coefficients of `f`. -/
theorem schwartzToHermiteScale_apply (m : ℕ) (f : SchwartzMap ℝ ℂ) (n : ℕ) :
    schwartzToHermiteScale m f n =
      normalizeHermiteCoefficients (m : ℤ) (fun k => schwartzHermiteCoefficients f k) n := by
  rw [schwartzToHermiteScale, ContinuousLinearMap.comp_apply, schwartzHermiteCoefficients_weightPower]
  simp only [normalizeHermiteCoefficients, hermiteScaleWeight, zpow_natCast]

/-- Decoding the positive-scale vector recovers the ordinary `L²` Hermite
coefficient. -/
@[simp]
theorem schwartzToHermiteScale_raw (m : ℕ) (f : SchwartzMap ℝ ℂ) (n : ℕ) :
    rawHermiteCoefficients (m : ℤ) (schwartzToHermiteScale m f) n = schwartzHermiteCoefficients f n := by
  rw [rawHermiteCoefficients, schwartzToHermiteScale_apply]
  simp only [normalizeHermiteCoefficients]
  rw [← mul_assoc, inv_mul_cancel₀]
  · exact one_mul _
  · exact_mod_cast hermiteScaleWeight_ne_zero (m : ℤ) n

def hermiteScalePairingCLM (m : ℕ) (T : HermiteScale (-(m : ℤ))) :
    HermiteScale (m : ℤ) →L[ℂ] ℂ :=
  (innerSL ℂ) (star T)

@[simp]
private theorem hermiteScalePairingCLM_apply
    (m : ℕ) (T : HermiteScale (-(m : ℤ)))
    (u : HermiteScale (m : ℤ)) :
    hermiteScalePairingCLM m T u = hermiteScalePairing (m : ℤ) T u := by
  change inner ℂ (star T) u = hermiteScalePairing (m : ℤ) T u
  rw [lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  simp [RCLike.inner_apply, mul_comm]

def hermiteScaleDualPairingLM (m : ℕ) (u : HermiteScale (m : ℤ)) :
    HermiteScale (-(m : ℤ)) →ₗ[ℂ] ℂ where
  toFun T := hermiteScalePairing (m : ℤ) T u
  map_add' T U := by
    rw [hermiteScalePairing, hermiteScalePairing, hermiteScalePairing]
    simp_rw [lp.coeFn_add, Pi.add_apply, add_mul]
    exact Summable.tsum_add (summable_hermiteScalePairing (m : ℤ) T u)
      (summable_hermiteScalePairing (m : ℤ) U u)
  map_smul' c T := by
    rw [hermiteScalePairing, hermiteScalePairing]
    simp_rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
    exact tsum_mul_left

def hermiteScaleDualPairingCLM (m : ℕ) (u : HermiteScale (m : ℤ)) :
    HermiteScale (-(m : ℤ)) →L[ℂ] ℂ :=
  (hermiteScaleDualPairingLM m u).mkContinuous ‖u‖ fun T => by
    change ‖hermiteScalePairing (m : ℤ) T u‖ ≤ ‖u‖ * ‖T‖
    simpa only [mul_comm] using
      norm_hermiteScalePairing_le (m : ℤ) T u

@[simp]
private theorem hermiteScaleDualPairingCLM_apply
    (m : ℕ) (u : HermiteScale (m : ℤ))
    (T : HermiteScale (-(m : ℤ))) :
    hermiteScaleDualPairingCLM m u T = hermiteScalePairing (m : ℤ) T u :=
  rfl

/-- Realize a negative Hermite-scale vector as a genuine complex tempered
distribution by duality with `schwartzToHermiteScale`. -/
def hermiteScaleDistribution (m : ℕ) (T : HermiteScale (-(m : ℤ))) :
    TemperedDistribution ℝ ℂ :=
  (hermiteScalePairingCLM m T).comp (schwartzToHermiteScale m)

/-- The distribution realization acts by the normalized Hermite-scale
pairing. -/
@[simp]
theorem hermiteScaleDistribution_apply (m : ℕ) (T : HermiteScale (-(m : ℤ)))
    (f : SchwartzMap ℝ ℂ) :
    hermiteScaleDistribution m T f = hermiteScalePairing (m : ℤ) T (schwartzToHermiteScale m f) := by
  change hermiteScalePairingCLM m T (schwartzToHermiteScale m f) = _
  rw [hermiteScalePairingCLM_apply]

/-- Continuous realization of the entire negative Hermite scale inside the
space of tempered distributions with its pointwise-convergence topology. -/
def hermiteScaleDistributionCLM (m : ℕ) :
    HermiteScale (-(m : ℤ)) →L[ℂ] TemperedDistribution ℝ ℂ where
  toFun := hermiteScaleDistribution m
  map_add' T U := by
    ext f
    rw [hermiteScaleDistribution_apply, add_apply,
      hermiteScaleDistribution_apply, hermiteScaleDistribution_apply]
    simpa only [hermiteScaleDualPairingCLM_apply] using
      (hermiteScaleDualPairingCLM m
        (schwartzToHermiteScale m f)).map_add T U
  map_smul' c T := by
    ext f
    rw [hermiteScaleDistribution_apply, smul_apply,
      hermiteScaleDistribution_apply]
    simpa only [hermiteScaleDualPairingCLM_apply, RingHom.id_apply] using
      (hermiteScaleDualPairingCLM m
        (schwartzToHermiteScale m f)).map_smul c T
  cont := PointwiseConvergenceCLM.continuous_of_continuous_eval fun f => by
    have heq : (fun T => hermiteScaleDistribution m T f) =
        fun T => hermiteScaleDualPairingCLM m (schwartzToHermiteScale m f) T := by
      funext T
      rw [hermiteScaleDistribution_apply, hermiteScaleDualPairingCLM_apply]
    rw [heq]
    exact (hermiteScaleDualPairingCLM m
      (schwartzToHermiteScale m f)).continuous

@[simp]
theorem hermiteScaleDistributionCLM_apply
    (m : ℕ) (T : HermiteScale (-(m : ℤ))) :
    hermiteScaleDistributionCLM m T = hermiteScaleDistribution m T :=
  rfl

/-- The distribution realization is the convergent raw Hermite coefficient
pairing. -/
theorem hermiteScaleDistribution_apply_raw
    (m : ℕ) (T : HermiteScale (-(m : ℤ)))
    (f : SchwartzMap ℝ ℂ) :
    hermiteScaleDistribution m T f =
      ∑' n : ℕ, rawHermiteCoefficients (-(m : ℤ)) T n * schwartzHermiteCoefficients f n := by
  rw [hermiteScaleDistribution_apply, hermiteScalePairing_eq_raw]
  apply tsum_congr
  intro n
  rw [schwartzToHermiteScale_raw]

def hermiteUniformEvalBound (n : ℕ) : ℂ :=
  (Real.sqrt ((2 * Real.sqrt (2 * Real.pi)) /
    (((n : ℝ) + 1) ^ (3 / 2 : ℝ))) : ℝ)

private theorem hermiteUniformEvalBound_norm_sq (n : ℕ) :
    ‖hermiteUniformEvalBound n‖ ^ 2 =
      (2 * Real.sqrt (2 * Real.pi)) /
        (((n : ℝ) + 1) ^ (3 / 2 : ℝ)) := by
  have hnonneg : 0 ≤ (2 * Real.sqrt (2 * Real.pi)) /
      (((n : ℝ) + 1) ^ (3 / 2 : ℝ)) := by positivity
  rw [hermiteUniformEvalBound, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt hnonneg]

theorem hermiteUniformEvalBound_memℓp : Memℓp hermiteUniformEvalBound 2 := by
  have hs₀ : Summable (fun n : ℕ =>
      1 / |(n : ℝ) + 1| ^ (3 / 2 : ℝ)) :=
    (Real.summable_one_div_nat_add_rpow 1 (3 / 2)).2 (by norm_num)
  have hs : Summable (fun n : ℕ =>
      (2 * Real.sqrt (2 * Real.pi)) /
        (((n : ℝ) + 1) ^ (3 / 2 : ℝ))) := by
    apply (hs₀.mul_left (2 * Real.sqrt (2 * Real.pi))).congr
    intro n
    rw [abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
    ring
  rw [memℓp_gen_iff (by norm_num : 0 < (2 : ENNReal).toReal)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  exact hs.congr fun n => (hermiteUniformEvalBound_norm_sq n).symm

def hermiteUniformEvalVector : CoefficientSpace ℕ :=
  ⟨hermiteUniformEvalBound, hermiteUniformEvalBound_memℓp⟩

private theorem hermiteDiracCoefficients_norm_le_uniform
    (x : ℝ) (n : ℕ) :
    ‖hermiteDiracCoefficients 1 x n‖ ≤ ‖hermiteUniformEvalVector n‖ := by
  have hsq := hermiteDiracCoefficients_norm_sq_le 1 (by norm_num) x n
  rw [← hermiteUniformEvalBound_norm_sq] at hsq
  change ‖hermiteDiracCoefficients 1 x n‖ ≤ ‖hermiteUniformEvalBound n‖
  have hleft := norm_nonneg (hermiteDiracCoefficients 1 x n)
  have hright := norm_nonneg (hermiteUniformEvalBound n)
  nlinarith

private theorem hermiteSeriesTerm_norm_le
    (f : SchwartzMap ℝ ℂ) (n : ℕ) (x : ℝ) :
    ‖schwartzHermiteCoefficients f n * normalizedHermiteSchwartz n x‖ ≤
      ‖schwartzToHermiteScale 1 f n‖ * ‖hermiteUniformEvalVector n‖ := by
  have hdual := rawHermiteCoefficients_dual_term (1 : ℤ)
    (hermitePointMass 1 (by norm_num) x) (schwartzToHermiteScale 1 f) n
  have hp : rawHermiteCoefficients (-1 : ℤ)
      (hermitePointMass 1 (by norm_num) x) n =
      normalizedHermiteSchwartz n x := by
    apply rawHermiteCoefficients_hermitePointMass
  have hu : rawHermiteCoefficients (1 : ℤ) (schwartzToHermiteScale 1 f) n =
      schwartzHermiteCoefficients f n := schwartzToHermiteScale_raw 1 f n
  have hdual' : normalizedHermiteSchwartz n x * schwartzHermiteCoefficients f n =
      hermiteDiracCoefficients 1 x n * schwartzToHermiteScale 1 f n := by
    rw [hp, hu] at hdual
    simpa only [hermitePointMass_apply] using hdual
  rw [mul_comm (schwartzHermiteCoefficients f n), hdual', norm_mul,
    mul_comm ‖hermiteDiracCoefficients 1 x n‖]
  gcongr
  exact hermiteDiracCoefficients_norm_le_uniform x n

private theorem summable_hermiteSeries (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    Summable (fun n : ℕ =>
      schwartzHermiteCoefficients f n * normalizedHermiteSchwartz n x) := by
  apply Summable.of_norm_bounded
    (lp.summable_mul (p := (2 : ENNReal)) (q := (2 : ENNReal))
      (by rw [Real.holderConjugate_iff]; norm_num)
      (schwartzToHermiteScale 1 f) hermiteUniformEvalVector)
  intro n
  exact hermiteSeriesTerm_norm_le f n x

def hermiteSeries (f : SchwartzMap ℝ ℂ) (x : ℝ) : ℂ :=
  ∑' n : ℕ, schwartzHermiteCoefficients f n * normalizedHermiteSchwartz n x

private theorem hermiteSeries_continuous (f : SchwartzMap ℝ ℂ) :
    Continuous (hermiteSeries f) := by
  apply continuous_tsum
  · intro n
    fun_prop
  · exact lp.summable_mul (p := (2 : ENNReal)) (q := (2 : ENNReal))
      (by rw [Real.holderConjugate_iff]; norm_num)
      (schwartzToHermiteScale 1 f) hermiteUniformEvalVector
  · intro n x
    exact hermiteSeriesTerm_norm_le f n x

/-- The bundled coefficient map is TauCeti's Hermite Hilbert-basis
representation of the `L²` realization. -/
@[simp]
theorem schwartzHermiteCoefficients_apply_repr (f : SchwartzMap ℝ ℂ) (n : ℕ) :
    schwartzHermiteCoefficients f n =
      (TauCeti.twoPiHermiteHilbertBasis ℂ).repr (f.toLp 2) n := rfl

def hermitePartialLp (f : SchwartzMap ℝ ℂ) (N : ℕ) :
    Lp ℂ 2 (volume : Measure ℝ) :=
  ∑ n ∈ Finset.range N,
    schwartzHermiteCoefficients f n • TauCeti.twoPiHermiteFunctionLp ℂ n

private theorem hermitePartialLp_tendsto (f : SchwartzMap ℝ ℂ) :
    Tendsto (hermitePartialLp f) atTop (nhds (f.toLp 2)) := by
  have h := (TauCeti.twoPiHermiteHilbertBasis ℂ).hasSum_repr (f.toLp 2)
  have h' : HasSum (fun n : ℕ =>
      schwartzHermiteCoefficients f n • TauCeti.twoPiHermiteFunctionLp ℂ n) (f.toLp 2) := by
    simpa only [schwartzHermiteCoefficients_apply_repr,
      TauCeti.coe_twoPiHermiteHilbertBasis] using h
  exact h'.tendsto_sum_nat

private theorem hermitePartialLp_ae (f : SchwartzMap ℝ ℂ) (N : ℕ) :
    ∀ᵐ x : ℝ,
      hermitePartialLp f N x =
        ∑ n ∈ Finset.range N,
          schwartzHermiteCoefficients f n * normalizedHermiteSchwartz n x := by
  have hb : ∀ n : ℕ, ∀ᵐ x : ℝ,
      TauCeti.twoPiHermiteFunctionLp ℂ n x =
        normalizedHermiteSchwartz n x := by
    intro n
    filter_upwards [TauCeti.coeFn_twoPiHermiteFunctionLp (𝕜 := ℂ) n] with x hx
    rw [hx, normalizedHermiteSchwartz_eq_twoPi,
      TauCeti.twoPiHermiteSchwartzMap_apply]
    simp
  have hsmul : ∀ n : ℕ, ∀ᵐ x : ℝ,
      (schwartzHermiteCoefficients f n • TauCeti.twoPiHermiteFunctionLp ℂ n) x =
        schwartzHermiteCoefficients f n * TauCeti.twoPiHermiteFunctionLp ℂ n x := by
    intro n
    filter_upwards [Lp.coeFn_smul (schwartzHermiteCoefficients f n)
      (TauCeti.twoPiHermiteFunctionLp ℂ n)] with x hx
    simpa only [Pi.smul_apply, smul_eq_mul] using hx
  filter_upwards [Lp.coeFn_fun_finsetSum (Finset.range N)
      (fun n => schwartzHermiteCoefficients f n • TauCeti.twoPiHermiteFunctionLp ℂ n),
    eventually_countable_forall.mpr hb,
    eventually_countable_forall.mpr hsmul] with x hsum hx hsmulx
  rw [hermitePartialLp, hsum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [hsmulx n, hx n]

private theorem hermiteSeries_eq (f : SchwartzMap ℝ ℂ) :
    hermiteSeries f = f := by
  have hLp := hermitePartialLp_tendsto f
  have hMeasure := MeasureTheory.tendstoInMeasure_of_tendsto_Lp hLp
  obtain ⟨ns, hns, haeSub⟩ := hMeasure.exists_seq_tendsto_ae
  have haePartial : ∀ᵐ x : ℝ, ∀ N : ℕ,
      hermitePartialLp f N x =
        ∑ n ∈ Finset.range N,
          schwartzHermiteCoefficients f n * normalizedHermiteSchwartz n x :=
    eventually_countable_forall.mpr (hermitePartialLp_ae f)
  have haeF := f.coeFn_toLp 2 volume
  have haeEq : ∀ᵐ x : ℝ, f x = hermiteSeries f x := by
    filter_upwards [haeSub, haePartial, haeF] with x hsub hpartial hf
    have hseries := (summable_hermiteSeries f x).hasSum.tendsto_sum_nat
    have hseriesSub : Tendsto (fun i =>
        ∑ n ∈ Finset.range (ns i),
          schwartzHermiteCoefficients f n * normalizedHermiteSchwartz n x)
        atTop (nhds (hermiteSeries f x)) :=
      hseries.comp hns.tendsto_atTop
    have hfSub : Tendsto (fun i =>
        ∑ n ∈ Finset.range (ns i),
          schwartzHermiteCoefficients f n * normalizedHermiteSchwartz n x)
        atTop (nhds (f x)) := by
      have hsub' := hsub.congr' (show
          (fun i => hermitePartialLp f (ns i) x) =ᶠ[atTop]
            (fun i => ∑ n ∈ Finset.range (ns i),
              schwartzHermiteCoefficients f n * normalizedHermiteSchwartz n x) by
        filter_upwards with i
        exact hpartial (ns i))
      rw [hf] at hsub'
      exact hsub'
    exact tendsto_nhds_unique hfSub hseriesSub
  exact ((Continuous.ae_eq_iff_eq volume f.continuous
    (hermiteSeries_continuous f)).mp haeEq).symm

/-- Pointwise Hermite reconstruction for every complex Schwartz function. -/
theorem hermite_reconstruction (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    (∑' n : ℕ, schwartzHermiteCoefficients f n * normalizedHermiteSchwartz n x) = f x := by
  exact congrFun (hermiteSeries_eq f) x

/-- The negative-scale Hermite vector of evaluation acts as the genuine
Dirac tempered distribution on every Schwartz test function. -/
theorem hermitePointMass_represents_delta
    (m : ℕ) (hm : 1 ≤ m) (x : ℝ) :
    hermiteScaleDistribution m (hermitePointMass m hm x) = pointMass x := by
  ext f
  rw [hermiteScaleDistribution_apply_raw, pointMass_apply]
  calc
    (∑' n : ℕ,
        rawHermiteCoefficients (-(m : ℤ)) (hermitePointMass m hm x) n *
          schwartzHermiteCoefficients f n) =
        ∑' n : ℕ,
          schwartzHermiteCoefficients f n * normalizedHermiteSchwartz n x := by
            apply tsum_congr
            intro n
            rw [rawHermiteCoefficients_hermitePointMass]
            exact mul_comm _ _
    _ = f x := hermite_reconstruction f x

/-- Fourier transform on a Hermite scale multiplies the `n`th coordinate by
`(-i)^n`. -/
theorem hermiteFourier_apply (m : ℤ) (u : HermiteScale m) (n : ℕ) :
    hermiteFourier m u n = hermiteFourierPhase n * u n := by
  change hermiteFourierHilbertBasis.repr.symm
      ((coefficientHilbertBasis ℕ).repr u) n = _
  have hrepr := hermiteFourierHilbertBasis.repr_apply_apply
    (hermiteFourierHilbertBasis.repr.symm
      ((coefficientHilbertBasis ℕ).repr u)) n
  rw [LinearIsometryEquiv.apply_symm_apply] at hrepr
  rw [hermiteFourierHilbertBasis_apply, hermiteFourierAtom,
    inner_smul_left,
    show coefficientAtom n = (coefficientHilbertBasis ℕ) n by rfl,
    ← (coefficientHilbertBasis ℕ).repr_apply_apply] at hrepr
  change u n = conj (hermiteFourierPhase n) *
    hermiteFourierHilbertBasis.repr.symm
      ((coefficientHilbertBasis ℕ).repr u) n at hrepr
  have hunit : hermiteFourierPhase n * conj (hermiteFourierPhase n) = 1 := by
    rw [mul_comm, conj_hermiteFourierPhase_mul]
  calc
    hermiteFourierHilbertBasis.repr.symm
        ((coefficientHilbertBasis ℕ).repr u) n =
      1 * hermiteFourierHilbertBasis.repr.symm
        ((coefficientHilbertBasis ℕ).repr u) n := by rw [one_mul]
    _ = (hermiteFourierPhase n * conj (hermiteFourierPhase n)) *
        hermiteFourierHilbertBasis.repr.symm
          ((coefficientHilbertBasis ℕ).repr u) n := by rw [hunit]
    _ = hermiteFourierPhase n * u n := by rw [mul_assoc, ← hrepr]

/-- Fourier transform of a Schwartz test multiplies its `n`th Hermite
coefficient by `(-i)^n`. -/
theorem schwartzHermiteCoefficients_fourier (f : SchwartzMap ℝ ℂ) (n : ℕ) :
    schwartzHermiteCoefficients (FourierTransform.fourier f) n =
      hermiteFourierPhase n * schwartzHermiteCoefficients f n := by
  rw [schwartzHermiteCoefficients_apply_repr, schwartzHermiteCoefficients_apply_repr,
    ← SchwartzMap.toLp_fourier_eq,
    TauCeti.repr_fourier_twoPiHermiteHilbertBasis]
  rfl

/-- The raw-coordinate form of the diagonal Hermite Fourier action. -/
theorem rawHermiteCoefficients_hermiteFourier
    (m : ℤ) (u : HermiteScale m) (n : ℕ) :
    rawHermiteCoefficients m (hermiteFourier m u) n =
      hermiteFourierPhase n * rawHermiteCoefficients m u n := by
  rw [rawHermiteCoefficients, hermiteFourier_apply,
    rawHermiteCoefficients]
  ring

/-- The diagonal Fourier action on negative Hermite scale represents the
genuine distributional Fourier transform on every Schwartz test function. -/
theorem hermiteFourier_represents_distributionalFourier
    (m : ℕ) (T : HermiteScale (-(m : ℤ))) :
    hermiteScaleDistribution m (hermiteFourier (-(m : ℤ)) T) =
      FourierTransform.fourier (hermiteScaleDistribution m T) := by
  ext f
  rw [hermiteScaleDistribution_apply_raw, TemperedDistribution.fourier_apply,
    hermiteScaleDistribution_apply_raw]
  apply tsum_congr
  intro n
  rw [rawHermiteCoefficients_hermiteFourier, schwartzHermiteCoefficients_fourier]
  ring

end
end MeyerGeneralProblem
