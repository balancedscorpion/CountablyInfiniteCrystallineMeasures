module

public import MeyerGeneralProblem.Endpoint.ReducedCross
public import MeyerGeneralProblem.Sampling.WindowChoice
public import Mathlib.Analysis.SpecificLimits.Normed
import all Mathlib.Analysis.SpecificLimits.Normed

@[expose] public section

/-!
# Polynomial-geometric endpoint squeeze

This is the elementary final asymptotic used after the common Gamma
normalisation cancels from the Gram floor and cross ceiling.
-/

namespace MeyerGeneralProblem

open Filter

noncomputable section

/-- A fixed polynomial loss cannot defeat a geometric gain with base below one. -/
theorem polynomial_mul_geometric_tendsto_zero (A : ℕ) (D q : ℝ)
    (hq₀ : 0 ≤ q) (hq₁ : q < 1) :
    Tendsto (fun m : ℕ ↦ D * (m : ℝ) ^ A * q ^ m) atTop (nhds 0) := by
  simpa only [mul_assoc, mul_zero] using
    (tendsto_pow_const_mul_const_pow_of_lt_one A hq₀ hq₁).const_mul D

/-- Consequently the polynomial-geometric ratio is eventually strictly below one. -/
theorem eventually_polynomial_mul_geometric_lt_one (A : ℕ) (D q : ℝ)
    (hq₀ : 0 ≤ q) (hq₁ : q < 1) :
    ∀ᶠ m : ℕ in atTop, D * (m : ℝ) ^ A * q ^ m < 1 :=
  (polynomial_mul_geometric_tendsto_zero A D q hq₀ hq₁).eventually_lt_const zero_lt_one

/-- The base arising from the Ingham/Calkin comparison is below one exactly
on the subcritical choice `a < 1/2` used by the proof. -/
theorem endpointSqueezeBase_lt_one {a : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a < 1 / 2) :
    ((1 + 4 * a ^ 2) ^ 2) / 4 < 1 := by
  have haSq : a ^ 2 < 1 / 4 := by nlinarith [sq_nonneg a]
  have hcore : 1 + 4 * a ^ 2 < 2 := by nlinarith
  have hcorePos : 0 < 1 + 4 * a ^ 2 := by positivity
  have hsum : 0 < 2 + (1 + 4 * a ^ 2) := by linarith
  have hprod : 0 < (2 - (1 + 4 * a ^ 2)) * (2 + (1 + 4 * a ^ 2)) :=
    mul_pos (sub_pos.mpr hcore) hsum
  nlinarith

/-- The same endpoint base is nonnegative. -/
theorem endpointSqueezeBase_nonneg (a : ℝ) :
    0 ≤ ((1 + 4 * a ^ 2) ^ 2) / 4 := by positivity

/-- Abstracted concrete Gram floor, with the common normalization `c` kept
visible so its cancellation can be checked by the kernel. -/
def universalGramFloor (m : ℕ) (c a d : ℝ) : ℝ :=
  2 * c * inghamFloorFactor a d * (1 + 4 * a ^ 2)⁻¹ ^ (2 * m)

/-- Reviewer-corrected full leading-cross ceiling.  The only polynomial loss
is the explicit factor `m + 1`, fixing the final exponent to `A = 1`. -/
def leadingCrossCeiling (m : ℕ) (C c : ℝ) : ℝ :=
  C * c * (m + 1) * (4 : ℝ)⁻¹ ^ m

/-- The ratio after cancellation of the common Gram normalization. -/
def endpointSqueezeRatio (m : ℕ) (C a d : ℝ) : ℝ :=
  (C / (2 * inghamFloorFactor a d)) * (m + 1) *
    (((1 + 4 * a ^ 2) ^ 2) / 4) ^ m

/-- Exact algebraic cancellation behind the endpoint squeeze. -/
theorem leadingCrossCeiling_eq_floor_mul_ratio (m : ℕ) {C c a d : ℝ}
    (hc : c ≠ 0) (hI : inghamFloorFactor a d ≠ 0) :
    leadingCrossCeiling m C c =
      universalGramFloor m c a d * endpointSqueezeRatio m C a d := by
  have hb : 1 + 4 * a ^ 2 ≠ 0 := by positivity
  unfold leadingCrossCeiling universalGramFloor endpointSqueezeRatio
  rw [div_pow, pow_mul]
  field_simp [hc, hI, hb]
  have hfour : (1 / 4 : ℝ) ^ m * 4 ^ m = 1 := by
    rw [div_eq_mul_inv, one_mul, ← mul_pow, inv_mul_cancel₀ (by norm_num), one_pow]
  have hbpow : (1 + 4 * a ^ 2) ^ 2 ≠ 0 := pow_ne_zero _ hb
  have hden : (1 / (1 + 4 * a ^ 2) ^ 2) ^ m *
      ((1 + 4 * a ^ 2) ^ 2) ^ m = 1 := by
    rw [div_eq_mul_inv, one_mul, ← mul_pow, inv_mul_cancel₀ hbpow, one_pow]
  calc
    C * (1 / 4) ^ m * 4 ^ m = C := by rw [mul_assoc, hfour, mul_one]
    _ = C * ((1 / (1 + 4 * a ^ 2) ^ 2) ^ m *
        ((1 + 4 * a ^ 2) ^ 2) ^ m) := by rw [hden, mul_one]
    _ = C * (1 / (1 + 4 * a ^ 2) ^ 2) ^ m *
        ((1 + 4 * a ^ 2) ^ 2) ^ m := by ring

/-- Division form of the same cancellation, used by the abstract squeeze. -/
theorem leadingCrossCeiling_div_floor (m : ℕ) {C c a d : ℝ}
    (hc : c ≠ 0) (hI : inghamFloorFactor a d ≠ 0) :
    leadingCrossCeiling m C c / universalGramFloor m c a d =
      endpointSqueezeRatio m C a d := by
  rw [leadingCrossCeiling_eq_floor_mul_ratio m hc hI]
  exact mul_div_cancel_left₀ _ (by
    unfold universalGramFloor
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hc) hI)
      (pow_ne_zero _ (inv_ne_zero (by positivity))))

/-- The corrected `(m+1)` loss still tends to zero against a strict geometric
gain. -/
theorem linear_mul_geometric_tendsto_zero (D q : ℝ)
    (hq₀ : 0 ≤ q) (hq₁ : q < 1) :
    Tendsto (fun m : ℕ ↦ D * (m + 1 : ℝ) * q ^ m) atTop (nhds 0) := by
  have hlinear := tendsto_pow_const_mul_const_pow_of_lt_one 1 hq₀ hq₁
  have hpure := tendsto_pow_atTop_nhds_zero_of_lt_one hq₀ hq₁
  have hadd : Tendsto (fun m : ℕ ↦ (m : ℝ) * q ^ m + q ^ m) atTop (nhds 0) := by
    simpa only [pow_one, zero_add] using hlinear.add hpure
  convert hadd.const_mul D using 1
  · funext m
    ring
  · simp

/-- Eventually the exact reviewer-corrected ratio is below one. -/
theorem eventually_endpointSqueezeRatio_lt_one {C a d : ℝ}
    (_hC : 0 ≤ C) (_hI : 0 < inghamFloorFactor a d)
    (ha₀ : 0 ≤ a) (ha₁ : a < 1 / 2) :
    ∀ᶠ m : ℕ in atTop, endpointSqueezeRatio m C a d < 1 := by
  let D := C / (2 * inghamFloorFactor a d)
  let q := ((1 + 4 * a ^ 2) ^ 2) / 4
  have hq₀ : 0 ≤ q := endpointSqueezeBase_nonneg a
  have hq₁ : q < 1 := endpointSqueezeBase_lt_one ha₀ ha₁
  have ht := linear_mul_geometric_tendsto_zero D q hq₀ hq₁
  have hevent := ht.eventually_lt_const zero_lt_one
  simpa only [endpointSqueezeRatio, D, q] using hevent

end

end MeyerGeneralProblem
