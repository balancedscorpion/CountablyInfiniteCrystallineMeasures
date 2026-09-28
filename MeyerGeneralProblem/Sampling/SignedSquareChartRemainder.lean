module

public import MeyerGeneralProblem.Sampling.SignedSquareWeightedChart
public import Mathlib.Algebra.Order.Chebyshev
import all Mathlib.Algebra.Order.Chebyshev

@[expose] public section

/-!
# Quantitative lower-order errors of the actual signed-square chart

The finite derivative recursion supplies explicit constants before the
physical tail and the input function. Its principal coefficient is kept
exact; only the strictly lower derivative terms are bounded. No cutoff,
closed Sobolev graph, spectral gap, or sampling estimate is assumed here.
-/

namespace MeyerGeneralProblem

open scoped BigOperators ContDiff Topology
open Filter

noncomputable section

/-- A finite weighted sum of actual physical derivative norms. -/
def signedSquareChartJetSum (m b : ℕ) (ε : ℝ) (h : ℝ → ℂ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range m, x ^ j * ‖iteratedDeriv (b + j) h (ε * x)‖

/-- Explicit absolute-coefficient majorant for the full chart recursion. -/
def signedSquareChartBoundConstant : ℕ → ℝ → ℝ
  | 0, _ => 1
  | n + 1, a => |a| * signedSquareChartBoundConstant n (a - 1) +
      (1 / 2 : ℝ) * signedSquareChartBoundConstant n (a - 1 / 2)

/-- Explicit majorant for the strictly lower-order branch only. -/
def signedSquareChartLowerConstant : ℕ → ℝ → ℝ
  | 0, _ => 0
  | n + 1, a => |a| * signedSquareChartBoundConstant n (a - 1) +
      (1 / 2 : ℝ) * signedSquareChartLowerConstant n (a - 1 / 2)

/-- Every full-recursion majorant is nonnegative. -/
theorem signedSquareChartBoundConstant_nonneg (n : ℕ) (a : ℝ) :
    0 ≤ signedSquareChartBoundConstant n a := by
  induction n generalizing a with
  | zero => norm_num [signedSquareChartBoundConstant]
  | succ n ih =>
    exact add_nonneg (mul_nonneg (abs_nonneg a) (ih (a - 1)))
      (mul_nonneg (by norm_num) (ih (a - 1 / 2)))

/-- Every lower-order majorant is nonnegative. -/
theorem signedSquareChartLowerConstant_nonneg (n : ℕ) (a : ℝ) :
    0 ≤ signedSquareChartLowerConstant n a := by
  induction n generalizing a with
  | zero => norm_num [signedSquareChartLowerConstant]
  | succ n ih =>
    exact add_nonneg (mul_nonneg (abs_nonneg a) (signedSquareChartBoundConstant_nonneg n _))
      (mul_nonneg (by norm_num) (ih (a - 1 / 2)))

/-- The jet sum has nonnegative summands on the positive physical ray. -/
theorem signedSquareChartJetSum_nonneg (m b : ℕ) (ε : ℝ) (h : ℝ → ℂ)
    {x : ℝ} (hx : 0 ≤ x) : 0 ≤ signedSquareChartJetSum m b ε h x :=
  Finset.sum_nonneg (fun j _ => mul_nonneg (pow_nonneg hx j) (norm_nonneg _))

/-- Adding one derivative to a positive weighted jet cannot decrease it. -/
theorem signedSquareChartJetSum_le_succ (m b : ℕ) (ε : ℝ) (h : ℝ → ℂ)
    {x : ℝ} (hx : 0 ≤ x) :
    signedSquareChartJetSum m b ε h x ≤ signedSquareChartJetSum (m + 1) b ε h x := by
  rw [signedSquareChartJetSum, signedSquareChartJetSum, Finset.sum_range_succ]
  exact le_add_of_nonneg_right (mul_nonneg (pow_nonneg hx m) (norm_nonneg _))

/-- Shifting a jet by one derivative costs exactly one factor x, and
discards only the original nonnegative zeroth term. -/
theorem signedSquareChartJetSum_shift_le (m b : ℕ) (ε : ℝ) (h : ℝ → ℂ)
    (x : ℝ) :
    x * signedSquareChartJetSum m (b + 1) ε h x ≤
      signedSquareChartJetSum (m + 1) b ε h x := by
  have heq : signedSquareChartJetSum (m + 1) b ε h x =
      x * signedSquareChartJetSum m (b + 1) ε h x + ‖iteratedDeriv b h (ε * x)‖ := by
    rw [signedSquareChartJetSum, Finset.sum_range_succ', signedSquareChartJetSum, Finset.mul_sum]
    simp only [pow_zero, one_mul, Nat.add_zero]
    congr 1
    apply Finset.sum_congr rfl
    intro j _hj
    rw [show b + (j + 1) = b + 1 + j by omega, pow_succ]
    ring
  rw [heq]
  exact le_add_of_nonneg_right (norm_nonneg _)

private theorem norm_ray_half {ε : ℝ} (hε : ε ^ 2 = 1) : ‖ε / 2‖ = (1 / 2 : ℝ) := by
  have habs : |ε| = 1 := (sq_eq_sq₀ (abs_nonneg ε) (by norm_num)).mp (by simpa using hε)
  rw [Real.norm_eq_abs, abs_div, habs]
  norm_num

/-- The full actual recursion is bounded by a finite weighted jet on
every x>0, with no tail cutoff or input function in its constant. -/
theorem norm_signedSquareChartExpansion_le (n : ℕ) (a : ℝ) {ε : ℝ}
    (hε : ε ^ 2 = 1) (b : ℕ) (h : ℝ → ℂ) {x : ℝ} (hx : 0 < x) :
    ‖signedSquareChartExpansion n a ε b h (x ^ 2)‖ ≤
      signedSquareChartBoundConstant n a * x ^ (2 * a - 2 * (n : ℝ)) *
        signedSquareChartJetSum (n + 1) b ε h x := by
  induction n generalizing a b with
  | zero =>
    simp [signedSquareChartExpansion, signedSquareChartBoundConstant,
      signedSquareChartMonomial_sq _ _ _ _ hx, signedSquareChartJetSum,
      Real.norm_of_nonneg (Real.rpow_nonneg hx.le _)]
  | succ n ih =>
    have h₁ := ih (a - 1) b
    have h₂ := ih (a - 1 / 2) (b + 1)
    have hpow₁ : 2 * (a - 1) - 2 * (n : ℝ) = 2 * a - 2 * ((n + 1 : ℕ) : ℝ) := by
      push_cast
      ring
    have hpow₂ : 2 * (a - 1 / 2) - 2 * (n : ℝ) =
        (2 * a - 2 * ((n + 1 : ℕ) : ℝ)) + 1 := by
      push_cast
      ring
    rw [hpow₁] at h₁
    rw [hpow₂, Real.rpow_add_one hx.ne'] at h₂
    have hC₁ := signedSquareChartBoundConstant_nonneg n (a - 1)
    have hC₂ := signedSquareChartBoundConstant_nonneg n (a - 1 / 2)
    have hW := Real.rpow_nonneg hx.le (2 * a - 2 * ((n + 1 : ℕ) : ℝ))
    have hS₁ := signedSquareChartJetSum_le_succ (n + 1) b ε h hx.le
    have hS₂ := signedSquareChartJetSum_shift_le (n + 1) b ε h x
    calc
      _ ≤ ‖a • signedSquareChartExpansion n (a - 1) ε b h (x ^ 2)‖ +
          ‖(ε / 2) • signedSquareChartExpansion n (a - 1 / 2) ε (b + 1) h (x ^ 2)‖ :=
        norm_add_le _ _
      _ = |a| * ‖signedSquareChartExpansion n (a - 1) ε b h (x ^ 2)‖ +
          (1 / 2) * ‖signedSquareChartExpansion n (a - 1 / 2) ε (b + 1) h (x ^ 2)‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, norm_ray_half hε]
      _ ≤ |a| * (signedSquareChartBoundConstant n (a - 1) *
          x ^ (2 * a - 2 * ((n + 1 : ℕ) : ℝ)) * signedSquareChartJetSum (n + 1) b ε h x) +
          (1 / 2) * (signedSquareChartBoundConstant n (a - 1 / 2) *
            (x ^ (2 * a - 2 * ((n + 1 : ℕ) : ℝ)) * x) *
              signedSquareChartJetSum (n + 1) (b + 1) ε h x) := by gcongr
      _ = (|a| * signedSquareChartBoundConstant n (a - 1)) *
          x ^ (2 * a - 2 * ((n + 1 : ℕ) : ℝ)) * signedSquareChartJetSum (n + 1) b ε h x +
          ((1 / 2) * signedSquareChartBoundConstant n (a - 1 / 2)) *
            x ^ (2 * a - 2 * ((n + 1 : ℕ) : ℝ)) *
              (x * signedSquareChartJetSum (n + 1) (b + 1) ε h x) := by ring
      _ ≤ (|a| * signedSquareChartBoundConstant n (a - 1)) *
          x ^ (2 * a - 2 * ((n + 1 : ℕ) : ℝ)) * signedSquareChartJetSum (n + 1 + 1) b ε h x +
          ((1 / 2) * signedSquareChartBoundConstant n (a - 1 / 2)) *
            x ^ (2 * a - 2 * ((n + 1 : ℕ) : ℝ)) *
              signedSquareChartJetSum (n + 1 + 1) b ε h x := by gcongr
      _ = _ := by simp only [signedSquareChartBoundConstant]; ring

/-- The explicit lower-order recursion is bounded by precisely the
strictly lower jet. This estimate is valid at every positive x. -/
theorem norm_signedSquareChartLowerTerms_le (n : ℕ) (a : ℝ) {ε : ℝ}
    (hε : ε ^ 2 = 1) (b : ℕ) (h : ℝ → ℂ) {x : ℝ} (hx : 0 < x) :
    ‖signedSquareChartLowerTerms n a ε b h (x ^ 2)‖ ≤
      signedSquareChartLowerConstant n a * x ^ (2 * a - 2 * (n : ℝ)) *
        signedSquareChartJetSum n b ε h x := by
  induction n generalizing a b with
  | zero => simp [signedSquareChartLowerTerms, signedSquareChartLowerConstant]
  | succ n ih =>
    have h₁ := norm_signedSquareChartExpansion_le n (a - 1) hε b h hx
    have h₂ := ih (a - 1 / 2) (b + 1)
    have hpow₁ : 2 * (a - 1) - 2 * (n : ℝ) = 2 * a - 2 * ((n + 1 : ℕ) : ℝ) := by
      push_cast
      ring
    have hpow₂ : 2 * (a - 1 / 2) - 2 * (n : ℝ) =
        (2 * a - 2 * ((n + 1 : ℕ) : ℝ)) + 1 := by
      push_cast
      ring
    rw [hpow₁] at h₁
    rw [hpow₂, Real.rpow_add_one hx.ne'] at h₂
    have hC₁ := signedSquareChartBoundConstant_nonneg n (a - 1)
    have hC₂ := signedSquareChartLowerConstant_nonneg n (a - 1 / 2)
    have hW := Real.rpow_nonneg hx.le (2 * a - 2 * ((n + 1 : ℕ) : ℝ))
    have hS₂ := signedSquareChartJetSum_shift_le n b ε h x
    calc
      _ ≤ ‖a • signedSquareChartExpansion n (a - 1) ε b h (x ^ 2)‖ +
          ‖(ε / 2) • signedSquareChartLowerTerms n (a - 1 / 2) ε (b + 1) h (x ^ 2)‖ :=
        norm_add_le _ _
      _ = |a| * ‖signedSquareChartExpansion n (a - 1) ε b h (x ^ 2)‖ +
          (1 / 2) * ‖signedSquareChartLowerTerms n (a - 1 / 2) ε (b + 1) h (x ^ 2)‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, norm_ray_half hε]
      _ ≤ |a| * (signedSquareChartBoundConstant n (a - 1) *
          x ^ (2 * a - 2 * ((n + 1 : ℕ) : ℝ)) * signedSquareChartJetSum (n + 1) b ε h x) +
          (1 / 2) * (signedSquareChartLowerConstant n (a - 1 / 2) *
            (x ^ (2 * a - 2 * ((n + 1 : ℕ) : ℝ)) * x) *
              signedSquareChartJetSum n (b + 1) ε h x) := by gcongr
      _ = (|a| * signedSquareChartBoundConstant n (a - 1)) *
          x ^ (2 * a - 2 * ((n + 1 : ℕ) : ℝ)) * signedSquareChartJetSum (n + 1) b ε h x +
          ((1 / 2) * signedSquareChartLowerConstant n (a - 1 / 2)) *
            x ^ (2 * a - 2 * ((n + 1 : ℕ) : ℝ)) *
              (x * signedSquareChartJetSum n (b + 1) ε h x) := by ring
      _ ≤ (|a| * signedSquareChartBoundConstant n (a - 1)) *
          x ^ (2 * a - 2 * ((n + 1 : ℕ) : ℝ)) * signedSquareChartJetSum (n + 1) b ε h x +
          ((1 / 2) * signedSquareChartLowerConstant n (a - 1 / 2)) *
            x ^ (2 * a - 2 * ((n + 1 : ℕ) : ℝ)) * signedSquareChartJetSum (n + 1) b ε h x := by
        gcongr
      _ = _ := by simp only [signedSquareChartLowerConstant]; ring

private theorem chart_squared_weight (k j : ℕ) {x : ℝ} (hx : 0 < x) :
    x * (x ^ (-(k : ℝ) - 1 / 2)) ^ 2 * (x ^ j) ^ 2 =
      x ^ (2 * (j : ℝ) - 2 * (k : ℝ)) := by
  rw [← Real.rpow_mul_natCast hx.le, ← pow_mul, ← Real.rpow_natCast]
  calc
    x * x ^ ((-(k : ℝ) - 1 / 2) * (2 : ℕ)) * x ^ ((j * 2 : ℕ) : ℝ) =
        x ^ (1 + (-(k : ℝ) - 1 / 2) * (2 : ℕ) + ((j * 2 : ℕ) : ℝ)) := by
      rw [Real.rpow_add hx, Real.rpow_add hx, Real.rpow_one]
    _ = _ := by congr 1; push_cast; ring

/-- Squaring the explicit lower-order bound and including the normalized
Jacobian x leaves exactly the weights x^(2j-2k), j<k. -/
theorem signedSquareChartLowerTerms_jacobian_sq_le (k : ℕ) {ε : ℝ}
    (hε : ε ^ 2 = 1) (h : ℝ → ℂ) {x : ℝ} (hx : 0 < x) :
    x * ‖signedSquareChartLowerTerms k ((2 * (k : ℝ) - 1) / 4) ε 0 h (x ^ 2)‖ ^ 2 ≤
      (k : ℝ) * (signedSquareChartLowerConstant k ((2 * (k : ℝ) - 1) / 4)) ^ 2 *
        ∑ j ∈ Finset.range k, x ^ (2 * (j : ℝ) - 2 * (k : ℝ)) *
          ‖iteratedDeriv j h (ε * x)‖ ^ 2 := by
  let L := signedSquareChartLowerConstant k ((2 * (k : ℝ) - 1) / 4)
  have hL : 0 ≤ L := signedSquareChartLowerConstant_nonneg k _
  have hJ := signedSquareChartJetSum_nonneg k 0 ε h hx.le
  have hb := norm_signedSquareChartLowerTerms_le k ((2 * (k : ℝ) - 1) / 4) hε 0 h hx
  have ha : 2 * ((2 * (k : ℝ) - 1) / 4) - 2 * (k : ℝ) = -(k : ℝ) - 1 / 2 := by ring
  rw [ha] at hb
  have hbsq := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hb
  have hCS : (signedSquareChartJetSum k 0 ε h x) ^ 2 ≤
      (k : ℝ) * ∑ j ∈ Finset.range k, (x ^ j * ‖iteratedDeriv j h (ε * x)‖) ^ 2 := by
    simpa [signedSquareChartJetSum] using
      (sq_sum_le_card_mul_sum_sq (s := Finset.range k)
        (f := fun j => x ^ j * ‖iteratedDeriv j h (ε * x)‖))
  calc
    _ ≤ x * (L * x ^ (-(k : ℝ) - 1 / 2) * signedSquareChartJetSum k 0 ε h x) ^ 2 :=
      mul_le_mul_of_nonneg_left hbsq hx.le
    _ = L ^ 2 * (x * (x ^ (-(k : ℝ) - 1 / 2)) ^ 2) *
        (signedSquareChartJetSum k 0 ε h x) ^ 2 := by ring
    _ ≤ L ^ 2 * (x * (x ^ (-(k : ℝ) - 1 / 2)) ^ 2) *
        ((k : ℝ) * ∑ j ∈ Finset.range k, (x ^ j * ‖iteratedDeriv j h (ε * x)‖) ^ 2) :=
      mul_le_mul_of_nonneg_left hCS (by positivity)
    _ = _ := by
      simp only [Finset.mul_sum, mul_pow]
      apply Finset.sum_congr rfl
      intro j _hj
      rw [← chart_squared_weight k j hx]
      dsimp [L]
      ring

private theorem norm_add_sq_young (u v : ℂ) {η : ℝ} (hη : 0 < η) :
    ‖u + v‖ ^ 2 ≤ (1 + η) * ‖u‖ ^ 2 + (1 + η⁻¹) * ‖v‖ ^ 2 := by
  have htriangle := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr (norm_add_le u v)
  have hyoung : 2 * ‖u‖ * ‖v‖ ≤ η * ‖u‖ ^ 2 + η⁻¹ * ‖v‖ ^ 2 := by
    apply (mul_le_mul_iff_right₀ hη).mp
    rw [mul_add, ← mul_assoc η η⁻¹, mul_inv_cancel₀ hη.ne', one_mul]
    nlinarith [sq_nonneg (η * ‖u‖ - ‖v‖)]
  nlinarith

/-- The principal term has exactly 4^(-k) derivative energy after the
normalized quadratic Jacobian, on either ray. -/
theorem signedSquareChart_principal_jacobian (k : ℕ) {ε : ℝ} (hε : ε ^ 2 = 1)
    (z : ℂ) {x : ℝ} (hx : 0 < x) :
    x * ‖(ε ^ k / (2 : ℝ) ^ k) • (x ^ (-(1 / 2 : ℝ)) • z)‖ ^ 2 =
      ((4 : ℝ) ^ k)⁻¹ * ‖z‖ ^ 2 := by
  have habs : |ε| = 1 := (sq_eq_sq₀ (abs_nonneg ε) (by norm_num)).mp (by simpa using hε)
  have hpow : ((2 : ℝ) ^ k) ^ 2 = (4 : ℝ) ^ k := by
    rw [← pow_mul, Nat.mul_comm k 2, pow_mul]
    norm_num
  have hxpow : x * (x ^ (-(1 / 2 : ℝ))) ^ 2 = 1 := by
    rw [← Real.rpow_mul_natCast hx.le]
    norm_num
    rw [Real.rpow_neg_one, mul_inv_cancel₀ hx.ne']
  rw [norm_smul, norm_smul, Real.norm_eq_abs, abs_div, abs_pow, habs,
    abs_of_pos (pow_pos (by norm_num : (0 : ℝ) < 2) k), one_pow,
    Real.norm_of_nonneg (Real.rpow_nonneg hx.le _)]
  simp only [mul_pow, div_pow, one_pow, hpow]
  calc
    x * (1 / (4 : ℝ) ^ k * ((x ^ (-(1 / 2 : ℝ))) ^ 2 * ‖z‖ ^ 2)) =
        ((4 : ℝ) ^ k)⁻¹ * (x * (x ^ (-(1 / 2 : ℝ))) ^ 2) * ‖z‖ ^ 2 := by ring
    _ = _ := by rw [hxpow]; ring

/-- The error constant is fixed by k and η, before the tail radius,
ray, function, or evaluation point. -/
def signedSquareChartErrorConstant (k : ℕ) (η : ℝ) : ℝ :=
  (1 + η⁻¹) * (k : ℝ) * (signedSquareChartLowerConstant k ((2 * (k : ℝ) - 1) / 4)) ^ 2

/-- The error constant is nonnegative for every positive Young parameter. -/
theorem signedSquareChartErrorConstant_nonneg (k : ℕ) {η : ℝ} (hη : 0 < η) :
    0 ≤ signedSquareChartErrorConstant k η := by
  unfold signedSquareChartErrorConstant
  positivity

private theorem chart_contDiffAt_iteratedDeriv {h : ℝ → ℂ} {y : ℝ}
    (hh : ContDiffAt ℝ ∞ h y) (b : ℕ) : ContDiffAt ℝ ∞ (iteratedDeriv b h) y := by
  induction b with
  | zero => simpa using hh
  | succ b ih =>
    rw [iteratedDeriv_succ]
    exact ih.derivWithin (by simp)

private theorem chart_monomial_contDiffAt_local (a ε : ℝ) (b : ℕ) {h : ℝ → ℂ}
    {σ : ℝ} (hσ : 0 < σ) (hh : ContDiffAt ℝ ∞ h (ε * Real.sqrt σ)) :
    ContDiffAt ℝ ∞ (signedSquareChartMonomial a ε b h) σ := by
  have hd : ContDiffAt ℝ ∞ (iteratedDeriv b h) (ε * Real.sqrt σ) :=
    chart_contDiffAt_iteratedDeriv hh b
  have hp : ContDiffAt ℝ ∞ (fun t : ℝ => ε * Real.sqrt t) σ :=
    (contDiffAt_const (c := ε)).mul (Real.contDiffAt_sqrt (n := ∞) hσ.ne')
  have hc : ContDiffAt ℝ ∞ (fun t : ℝ => iteratedDeriv b h (ε * Real.sqrt t)) σ :=
    ContDiffAt.fun_comp σ (g := iteratedDeriv b h) (f := fun t : ℝ => ε * Real.sqrt t) hd hp
  exact (Real.contDiffAt_rpow_const_of_ne hσ.ne').smul hc

/-- The actual derivative recursion is local: h need only be smooth on
an open physical set containing the point pulled back from σ>0. -/
theorem iteratedDeriv_signedSquareChartMonomial_on (n : ℕ) (a ε : ℝ) (b : ℕ)
    {h : ℝ → ℂ} {s : Set ℝ} (hs : IsOpen s) (hh : ContDiffOn ℝ ∞ h s)
    {σ : ℝ} (hσ : 0 < σ) (hmem : ε * Real.sqrt σ ∈ s) :
    iteratedDeriv n (signedSquareChartMonomial a ε b h) σ =
      signedSquareChartExpansion n a ε b h σ := by
  induction n generalizing a b σ with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ']
    have hp : ContinuousAt (fun t : ℝ => ε * Real.sqrt t) σ :=
      continuousAt_const.mul (Real.continuous_sqrt.continuousAt)
    have hm : ∀ᶠ t in 𝓝 σ, ε * Real.sqrt t ∈ s := hp.eventually (hs.mem_nhds hmem)
    have heq : deriv (signedSquareChartMonomial a ε b h) =ᶠ[𝓝 σ]
        (fun t => a • signedSquareChartMonomial (a - 1) ε b h t +
          (ε / 2) • signedSquareChartMonomial (a - 1 / 2) ε (b + 1) h t) := by
      filter_upwards [Ioi_mem_nhds hσ, hm] with t ht hmt
      exact (hasDerivAt_signedSquareChartMonomial a ε b h ht
        ((chart_contDiffAt_iteratedDeriv (hh.contDiffAt (hs.mem_nhds hmt)) b).differentiableAt
          (by simp))).deriv
    rw [heq.iteratedDeriv_eq n]
    have hc := hh.contDiffAt (hs.mem_nhds hmem)
    rw [iteratedDeriv_fun_add
      (((chart_monomial_contDiffAt_local (a - 1) ε b hσ hc).of_le (by simp)).const_smul a)
      (((chart_monomial_contDiffAt_local (a - 1 / 2) ε (b + 1) hσ hc).of_le
        (by simp)).const_smul (ε / 2))]
    simp only [iteratedDeriv_fun_const_smul_field, ih _ _ hσ hmem, signedSquareChartExpansion]

/-- The exact physical-coordinate leading term needs only local smoothness
on an open set; no regularity at the omitted physical core is required. -/
theorem iteratedDeriv_signedSquareWeightedChart_leading_sq_on (k : ℕ) (ε : ℝ)
    {h : ℝ → ℂ} {s : Set ℝ} (hs : IsOpen s) (hh : ContDiffOn ℝ ∞ h s)
    {x : ℝ} (hx : 0 < x) (hmem : ε * x ∈ s) :
    iteratedDeriv k (signedSquareWeightedChart k ε h) (x ^ 2) =
      (ε ^ k / (2 : ℝ) ^ k) • (x ^ (-(1 / 2 : ℝ)) • iteratedDeriv k h (ε * x)) +
        signedSquareChartLowerTerms k ((2 * (k : ℝ) - 1) / 4) ε 0 h (x ^ 2) := by
  have hm : ε * Real.sqrt (x ^ 2) ∈ s := by simpa [Real.sqrt_sq hx.le] using hmem
  rw [signedSquareWeightedChart,
    iteratedDeriv_signedSquareChartMonomial_on k _ ε 0 hs hh (sq_pos_of_pos hx) hm,
    signedSquareChartExpansion_leading]
  rw [show (2 * (k : ℝ) - 1) / 4 - (k : ℝ) / 2 = -(1 / 4 : ℝ) by ring]
  simp only [signedSquareChartMonomial, Nat.zero_add, Real.sqrt_sq hx.le,
    div_pow, ← Real.rpow_natCast_mul hx.le]
  norm_num

/-- Quantitative bound for the actual kth chart derivative at x². The
principal coefficient is exactly (1+η)4^(-k); every other derivative has
strictly smaller order and a negative even power of x. -/
theorem signedSquareWeightedChart_jacobian_sq_le_on (k : ℕ) {η : ℝ} (hη : 0 < η)
    {ε : ℝ} (hε : ε ^ 2 = 1) {h : ℝ → ℂ} {s : Set ℝ}
    (hs : IsOpen s) (hh : ContDiffOn ℝ ∞ h s) {x : ℝ} (hx : 0 < x) (hmem : ε * x ∈ s) :
    x * ‖iteratedDeriv k (signedSquareWeightedChart k ε h) (x ^ 2)‖ ^ 2 ≤
      ((1 + η) / (4 : ℝ) ^ k) * ‖iteratedDeriv k h (ε * x)‖ ^ 2 +
        signedSquareChartErrorConstant k η *
          ∑ j ∈ Finset.range k, x ^ (2 * (j : ℝ) - 2 * (k : ℝ)) *
            ‖iteratedDeriv j h (ε * x)‖ ^ 2 := by
  rw [iteratedDeriv_signedSquareWeightedChart_leading_sq_on k ε hs hh hx hmem]
  have hyoung := norm_add_sq_young
    ((ε ^ k / (2 : ℝ) ^ k) • (x ^ (-(1 / 2 : ℝ)) • iteratedDeriv k h (ε * x)))
    (signedSquareChartLowerTerms k ((2 * (k : ℝ) - 1) / 4) ε 0 h (x ^ 2)) hη
  have hmain := signedSquareChart_principal_jacobian k hε (iteratedDeriv k h (ε * x)) hx
  have herror := signedSquareChartLowerTerms_jacobian_sq_le k hε h hx
  calc
    _ ≤ x * ((1 + η) *
        ‖(ε ^ k / (2 : ℝ) ^ k) • (x ^ (-(1 / 2 : ℝ)) • iteratedDeriv k h (ε * x))‖ ^ 2 +
        (1 + η⁻¹) * ‖signedSquareChartLowerTerms k ((2 * (k : ℝ) - 1) / 4) ε 0 h (x ^ 2)‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hyoung hx.le
    _ = (1 + η) *
        (x * ‖(ε ^ k / (2 : ℝ) ^ k) • (x ^ (-(1 / 2 : ℝ)) • iteratedDeriv k h (ε * x))‖ ^ 2) +
        (1 + η⁻¹) * (x * ‖signedSquareChartLowerTerms k ((2 * (k : ℝ) - 1) / 4) ε 0 h (x ^ 2)‖ ^ 2) :=
      by ring
    _ ≤ (1 + η) * (((4 : ℝ) ^ k)⁻¹ * ‖iteratedDeriv k h (ε * x)‖ ^ 2) +
        (1 + η⁻¹) * ((k : ℝ) * (signedSquareChartLowerConstant k ((2 * (k : ℝ) - 1) / 4)) ^ 2 *
          ∑ j ∈ Finset.range k, x ^ (2 * (j : ℝ) - 2 * (k : ℝ)) *
            ‖iteratedDeriv j h (ε * x)‖ ^ 2) := by
      rw [hmain]
      apply add_le_add le_rfl
      exact mul_le_mul_of_nonneg_left herror (show 0 ≤ 1 + η⁻¹ by positivity)
    _ = _ := by unfold signedSquareChartErrorConstant; ring

/-- Global smoothness is a convenient specialization of the local chart
estimate, not a certificate containing the desired estimate. -/
theorem signedSquareWeightedChart_jacobian_sq_le (k : ℕ) {η : ℝ} (hη : 0 < η)
    {ε : ℝ} (hε : ε ^ 2 = 1) {h : ℝ → ℂ} (hh : ContDiff ℝ ∞ h)
    {x : ℝ} (hx : 0 < x) :
    x * ‖iteratedDeriv k (signedSquareWeightedChart k ε h) (x ^ 2)‖ ^ 2 ≤
      ((1 + η) / (4 : ℝ) ^ k) * ‖iteratedDeriv k h (ε * x)‖ ^ 2 +
        signedSquareChartErrorConstant k η *
          ∑ j ∈ Finset.range k, x ^ (2 * (j : ℝ) - 2 * (k : ℝ)) *
            ‖iteratedDeriv j h (ε * x)‖ ^ 2 :=
  signedSquareWeightedChart_jacobian_sq_le_on k hη hε isOpen_univ hh.contDiffOn hx (Set.mem_univ _)

private theorem chart_lower_exponent_le (k j : ℕ) (hj : j ∈ Finset.range k) :
    2 * (j : ℝ) - 2 * (k : ℝ) ≤ -2 := by
  have hj' : j + 1 ≤ k := Finset.mem_range.mp hj
  have hcast : (j : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hj'
  linarith

/-- On x≥R>0 every lower derivative has its own decaying tail weight
R^(2j-2k). The constant was already fixed independently of R and h. -/
theorem signedSquareWeightedChart_tail_weighted_sq_le_on (k : ℕ) {η : ℝ} (hη : 0 < η)
    {ε : ℝ} (hε : ε ^ 2 = 1) {h : ℝ → ℂ} {s : Set ℝ}
    (hs : IsOpen s) (hh : ContDiffOn ℝ ∞ h s) {R x : ℝ} (hR : 0 < R)
    (hx : R ≤ x) (hmem : ε * x ∈ s) :
    x * ‖iteratedDeriv k (signedSquareWeightedChart k ε h) (x ^ 2)‖ ^ 2 ≤
      ((1 + η) / (4 : ℝ) ^ k) * ‖iteratedDeriv k h (ε * x)‖ ^ 2 +
        signedSquareChartErrorConstant k η *
          ∑ j ∈ Finset.range k, R ^ (2 * (j : ℝ) - 2 * (k : ℝ)) *
            ‖iteratedDeriv j h (ε * x)‖ ^ 2 := by
  apply (signedSquareWeightedChart_jacobian_sq_le_on k hη hε hs hh (hR.trans_le hx) hmem).trans
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ (signedSquareChartErrorConstant_nonneg k hη)
  apply Finset.sum_le_sum
  intro j hj
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact Real.rpow_le_rpow_of_nonpos hR hx ((chart_lower_exponent_le k j hj).trans (by norm_num))

/-- For R≥1 all strictly lower derivative weights are at most R^(-2).
The leading (1+η)4^(-k) coefficient is unchanged by this simplification. -/
theorem signedSquareWeightedChart_tail_sq_le_on (k : ℕ) {η : ℝ} (hη : 0 < η)
    {ε : ℝ} (hε : ε ^ 2 = 1) {h : ℝ → ℂ} {s : Set ℝ}
    (hs : IsOpen s) (hh : ContDiffOn ℝ ∞ h s) {R x : ℝ} (hR : 1 ≤ R)
    (hx : R ≤ x) (hmem : ε * x ∈ s) :
    x * ‖iteratedDeriv k (signedSquareWeightedChart k ε h) (x ^ 2)‖ ^ 2 ≤
      ((1 + η) / (4 : ℝ) ^ k) * ‖iteratedDeriv k h (ε * x)‖ ^ 2 +
        (signedSquareChartErrorConstant k η / R ^ 2) *
          ∑ j ∈ Finset.range k, ‖iteratedDeriv j h (ε * x)‖ ^ 2 := by
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num) hR
  apply (signedSquareWeightedChart_tail_weighted_sq_le_on k hη hε hs hh hRpos hx hmem).trans
  apply add_le_add le_rfl
  calc
    _ ≤ signedSquareChartErrorConstant k η *
        ∑ j ∈ Finset.range k, (R ^ 2)⁻¹ * ‖iteratedDeriv j h (ε * x)‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (signedSquareChartErrorConstant_nonneg k hη)
      apply Finset.sum_le_sum
      intro j hj
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      calc
        R ^ (2 * (j : ℝ) - 2 * (k : ℝ)) ≤ R ^ (-2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hR (chart_lower_exponent_le k j hj)
        _ = (R ^ 2)⁻¹ := by rw [Real.rpow_neg hRpos.le]; norm_num
    _ = _ := by rw [← Finset.mul_sum]; ring

/-- The two rays retain the same leading coefficient when combined with
the normalized Jacobian x. Both local physical germs are required, but
no smoothness in the omitted core and no finite-cokernel assertion is made. -/
theorem signedSquareWeightedChart_twoRay_tail_sq_le_on (k : ℕ) {η : ℝ} (hη : 0 < η)
    {h : ℝ → ℂ} {s : Set ℝ} (hs : IsOpen s) (hh : ContDiffOn ℝ ∞ h s)
    {R x : ℝ} (hR : 1 ≤ R) (hx : R ≤ x) (hpos : x ∈ s) (hneg : -x ∈ s) :
    x * (‖iteratedDeriv k (signedSquareWeightedChart k 1 h) (x ^ 2)‖ ^ 2 +
      ‖iteratedDeriv k (signedSquareWeightedChart k (-1) h) (x ^ 2)‖ ^ 2) ≤
      ((1 + η) / (4 : ℝ) ^ k) *
        (‖iteratedDeriv k h x‖ ^ 2 + ‖iteratedDeriv k h (-x)‖ ^ 2) +
      (signedSquareChartErrorConstant k η / R ^ 2) *
        ∑ j ∈ Finset.range k, (‖iteratedDeriv j h x‖ ^ 2 + ‖iteratedDeriv j h (-x)‖ ^ 2) := by
  have hp := signedSquareWeightedChart_tail_sq_le_on k hη (by norm_num : (1 : ℝ) ^ 2 = 1)
    hs hh hR hx (by simpa using hpos)
  have hn := signedSquareWeightedChart_tail_sq_le_on k hη (by norm_num : (-1 : ℝ) ^ 2 = 1)
    hs hh hR hx (by simpa using hneg)
  simp only [one_mul, neg_one_mul] at hp hn
  rw [Finset.sum_add_distrib]
  nlinarith [add_le_add hp hn]

/-- At order two the explicit lower-branch coefficient is 11/16, so the
squared-jet error constant is (121/128)(1+η⁻¹). -/
theorem signedSquareChartErrorConstant_two (η : ℝ) :
    signedSquareChartErrorConstant 2 η = (121 / 128 : ℝ) * (1 + η⁻¹) := by
  norm_num [signedSquareChartErrorConstant, signedSquareChartLowerConstant,
    signedSquareChartBoundConstant]
  ring

/-- The order-two tail estimate is a concrete regression for the exact
1/16 principal-energy coefficient and the zeroth/first-derivative errors. -/
theorem signedSquareWeightedChart_two_tail_sq_le_on {η : ℝ} (hη : 0 < η)
    {ε : ℝ} (hε : ε ^ 2 = 1) {h : ℝ → ℂ} {s : Set ℝ}
    (hs : IsOpen s) (hh : ContDiffOn ℝ ∞ h s) {R x : ℝ} (hR : 1 ≤ R)
    (hx : R ≤ x) (hmem : ε * x ∈ s) :
    x * ‖iteratedDeriv 2 (signedSquareWeightedChart 2 ε h) (x ^ 2)‖ ^ 2 ≤
      ((1 + η) / 16) * ‖iteratedDeriv 2 h (ε * x)‖ ^ 2 +
        ((121 / 128 : ℝ) * (1 + η⁻¹) / R ^ 2) *
          (‖h (ε * x)‖ ^ 2 + ‖deriv h (ε * x)‖ ^ 2) := by
  simpa [signedSquareChartErrorConstant_two, Finset.sum_range_succ, iteratedDeriv_one,
    show (4 : ℝ) ^ 2 = 16 by norm_num] using
    signedSquareWeightedChart_tail_sq_le_on 2 hη hε hs hh hR hx hmem

end

end MeyerGeneralProblem
