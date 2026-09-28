module

public import MeyerGeneralProblem.Sampling.SignedSquareChartRemainder
public import MeyerGeneralProblem.Interpolation.QuadraticDerivativeBounds

@[expose] public section

/-!
# Actual cutoff-localized signed-square energy transfer

The fixed smooth transition removes the quadratic-chart singularity and
the uncontrolled finite prefix. This module works first with genuinely
smooth functions, not with an assumed classical derivative on a completed
Sobolev graph. The principal energy and the strictly lower-order cutoff
commutator are kept separate.

This is an integrated smooth-function edge, not the final sampling theorem.
It does not assume or assert the localized chart's Fourier-Sobolev domain,
a spectral inequality, or coercivity of the complete-domain sampling map.
-/

namespace MeyerGeneralProblem

open Set Filter MeasureTheory
open scoped BigOperators ContDiff Topology

noncomputable section

/-- The retained unit-width squared-coordinate transition at radius R. -/
def signedSquareTailCutoff (R σ : ℝ) : ℝ :=
  Real.smoothTransition (σ - R ^ 2 + 1)

/-- The actual localized chart. Since the cutoff is zero near σ≤0 when
R>1, this total definition is also its extension by zero there. -/
def signedSquareCutoffChart (k : ℕ) (R ε : ℝ) (h : ℝ → ℂ) (σ : ℝ) : ℂ :=
  signedSquareTailCutoff R σ • signedSquareWeightedChart k ε h σ

/-- The cutoff is genuinely smooth, at every order and every radius. -/
theorem contDiff_signedSquareTailCutoff (R : ℝ) :
    ContDiff ℝ ∞ (signedSquareTailCutoff R) :=
  Real.smoothTransition.contDiff.comp (by fun_prop)

/-- The cutoff lies between zero and one. -/
theorem signedSquareTailCutoff_mem_Icc (R σ : ℝ) :
    signedSquareTailCutoff R σ ∈ Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

/-- The entire finite prefix is killed, including its endpoint. -/
theorem signedSquareTailCutoff_zero (R : ℝ) {σ : ℝ} (hσ : σ ≤ R ^ 2 - 1) :
    signedSquareTailCutoff R σ = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

/-- Beyond the physical tail boundary the cutoff equals one. -/
theorem signedSquareTailCutoff_one (R : ℝ) {σ : ℝ} (hσ : R ^ 2 ≤ σ) :
    signedSquareTailCutoff R σ = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

/-- The localized chart vanishes on the actual finite prefix. -/
theorem signedSquareCutoffChart_zero (k : ℕ) (R ε : ℝ) (h : ℝ → ℂ)
    {σ : ℝ} (hσ : σ ≤ R ^ 2 - 1) : signedSquareCutoffChart k R ε h σ = 0 := by
  rw [signedSquareCutoffChart, signedSquareTailCutoff_zero R hσ, zero_smul]

/-- The localized chart is the original chart on the exterior tail. -/
theorem signedSquareCutoffChart_eq (k : ℕ) (R ε : ℝ) (h : ℝ → ℂ)
    {σ : ℝ} (hσ : R ^ 2 ≤ σ) :
    signedSquareCutoffChart k R ε h σ = signedSquareWeightedChart k ε h σ := by
  rw [signedSquareCutoffChart, signedSquareTailCutoff_one R hσ, one_smul]

/-- The localized chart is globally smooth, despite the unlocalized
square-root chart's singularity at zero. -/
theorem contDiff_signedSquareCutoffChart (k : ℕ) {R : ℝ} (hR : 1 < R)
    (ε : ℝ) {h : ℝ → ℂ} (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (signedSquareCutoffChart k R ε h) := by
  rw [contDiff_iff_contDiffAt]
  intro σ
  by_cases hσ : 0 < σ
  · exact (contDiff_signedSquareTailCutoff R).contDiffAt.smul
      (contDiffAt_signedSquareChartMonomial _ ε 0 hh hσ)
  · have hσ' : σ < R ^ 2 - 1 := by nlinarith
    apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hσ'] with t ht
    exact signedSquareCutoffChart_zero k R ε h ht.le

/-- The actual derivatives of the cutoff vanish strictly outside its
transition shell whenever their order is positive. -/
theorem iteratedDeriv_signedSquareTailCutoff_eq_zero (j : ℕ) (hj : 0 < j)
    (R : ℝ) {σ : ℝ} (hσ : σ < R ^ 2 - 1 ∨ R ^ 2 < σ) :
    iteratedDeriv j (signedSquareTailCutoff R) σ = 0 := by
  rcases hσ with hσ | hσ
  · have heq : signedSquareTailCutoff R =ᶠ[𝓝 σ] (fun _ => (0 : ℝ)) := by
      filter_upwards [Iio_mem_nhds hσ] with t ht
      exact signedSquareTailCutoff_zero R ht.le
    rw [heq.iteratedDeriv_eq j, iteratedDeriv_const]
    simp [hj.ne']
  · have heq : signedSquareTailCutoff R =ᶠ[𝓝 σ] (fun _ => (1 : ℝ)) := by
      filter_upwards [Ioi_mem_nhds hσ] with t ht
      exact signedSquareTailCutoff_one R ht.le
    rw [heq.iteratedDeriv_eq j, iteratedDeriv_const]
    simp [hj.ne']

/-- Exact finite Leibniz commutator: at least one derivative falls on the
cutoff, hence every chart derivative has order strictly less than k. -/
def signedSquareCutoffCommutator (k : ℕ) (R ε : ℝ) (h : ℝ → ℂ) (σ : ℝ) : ℂ :=
  ∑ i ∈ Finset.range k, k.choose (i + 1) •
    iteratedDeriv (i + 1) (signedSquareTailCutoff R) σ •
      signedSquareChartExpansion (k - (i + 1)) ((2 * (k : ℝ) - 1) / 4) ε 0 h σ

/-- Actual differentiation gives the cutoff times the actual chart
derivative plus the explicit strictly lower-order commutator. -/
theorem iteratedDeriv_signedSquareCutoffChart (k : ℕ) (R ε : ℝ)
    {h : ℝ → ℂ} (hh : ContDiff ℝ ∞ h) {σ : ℝ} (hσ : 0 < σ) :
    iteratedDeriv k (signedSquareCutoffChart k R ε h) σ =
      signedSquareTailCutoff R σ • iteratedDeriv k (signedSquareWeightedChart k ε h) σ +
        signedSquareCutoffCommutator k R ε h σ := by
  change iteratedDeriv k (fun t => signedSquareTailCutoff R t •
    signedSquareWeightedChart k ε h t) σ = _
  have hc : ContDiffAt ℝ k (signedSquareWeightedChart k ε h) σ :=
    (contDiffAt_signedSquareChartMonomial ((2 * (k : ℝ) - 1) / 4) ε 0 hh hσ).of_le (by simp)
  rw [iteratedDeriv_fun_real_smul (g := signedSquareWeightedChart k ε h)
    ((contDiff_signedSquareTailCutoff R).of_le (by simp)).contDiffAt
    hc]
  rw [Finset.sum_range_succ']
  simp only [Nat.choose_zero_right, iteratedDeriv_zero, Nat.sub_zero, one_smul]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _hi
  rw [signedSquareWeightedChart, iteratedDeriv_signedSquareChartMonomial _ _ ε 0 hh hσ]

/-- The commutator is genuinely localized to the closed transition shell. -/
theorem signedSquareCutoffCommutator_eq_zero (k : ℕ) (R ε : ℝ) (h : ℝ → ℂ)
    {σ : ℝ} (hσ : σ < R ^ 2 - 1 ∨ R ^ 2 < σ) :
    signedSquareCutoffCommutator k R ε h σ = 0 := by
  apply Finset.sum_eq_zero
  intro i _hi
  rw [iteratedDeriv_signedSquareTailCutoff_eq_zero (i + 1) (by omega) R hσ,
    zero_smul, smul_zero]

/-- An explicit scalar coefficient for the cutoff commutator, independent
of both the input function and the ray. It is used only for x>0. -/
def signedSquareCutoffCoefficient (k : ℕ) (R x : ℝ) : ℝ :=
  ∑ i ∈ Finset.range k, (k.choose (i + 1) : ℝ) *
    ‖iteratedDeriv (i + 1) (signedSquareTailCutoff R) (x ^ 2)‖ *
    (signedSquareChartBoundConstant (k - (i + 1)) ((2 * (k : ℝ) - 1) / 4) *
      x ^ (2 * ((2 * (k : ℝ) - 1) / 4) - 2 * ((k - (i + 1) : ℕ) : ℝ)) *
        ∑ j ∈ Finset.range (k - (i + 1) + 1), x ^ j)

/-- This coefficient is nonnegative on the positive physical ray. -/
theorem signedSquareCutoffCoefficient_nonneg (k : ℕ) (R : ℝ) {x : ℝ} (hx : 0 < x) :
    0 ≤ signedSquareCutoffCoefficient k R x := by
  apply Finset.sum_nonneg
  intro i _hi
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))
    (mul_nonneg (mul_nonneg (signedSquareChartBoundConstant_nonneg _ _)
      (Real.rpow_nonneg hx.le _)) (Finset.sum_nonneg (fun j _ => pow_nonneg hx.le j)))

/-- The exact cutoff commutator involves only the physical derivatives
strictly below k, with an explicit coefficient chosen independently of h. -/
theorem norm_signedSquareCutoffCommutator_le (k : ℕ) (R : ℝ) {ε : ℝ}
    (hε : ε ^ 2 = 1) (h : ℝ → ℂ) {x : ℝ} (hx : 0 < x) :
    ‖signedSquareCutoffCommutator k R ε h (x ^ 2)‖ ≤
      signedSquareCutoffCoefficient k R x *
        ∑ j ∈ Finset.range k, ‖iteratedDeriv j h (ε * x)‖ := by
  let J := ∑ j ∈ Finset.range k, ‖iteratedDeriv j h (ε * x)‖
  have hjet (i : ℕ) (hi : i ∈ Finset.range k) :
      signedSquareChartJetSum (k - (i + 1) + 1) 0 ε h x ≤
        (∑ j ∈ Finset.range (k - (i + 1) + 1), x ^ j) * J := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j hj
    simp only [Nat.zero_add]
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hx.le j)
    dsimp [J]
    have := Finset.mem_range.mp hi
    have := Finset.mem_range.mp hj
    exact Finset.single_le_sum (f := fun l => ‖iteratedDeriv l h (ε * x)‖)
      (fun l _ => norm_nonneg _) (Finset.mem_range.mpr (by omega))
  unfold signedSquareCutoffCommutator
  calc
    _ ≤ ∑ i ∈ Finset.range k, ‖k.choose (i + 1) •
        iteratedDeriv (i + 1) (signedSquareTailCutoff R) (x ^ 2) •
          signedSquareChartExpansion (k - (i + 1)) ((2 * (k : ℝ) - 1) / 4) ε 0 h (x ^ 2)‖ :=
      norm_sum_le _ _
    _ = ∑ i ∈ Finset.range k, (k.choose (i + 1) : ℝ) *
        ‖iteratedDeriv (i + 1) (signedSquareTailCutoff R) (x ^ 2)‖ *
          ‖signedSquareChartExpansion (k - (i + 1)) ((2 * (k : ℝ) - 1) / 4) ε 0 h (x ^ 2)‖ := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [← Nat.cast_smul_eq_nsmul ℝ, norm_smul, norm_smul,
        Real.norm_of_nonneg (Nat.cast_nonneg _), mul_assoc]
    _ ≤ _ := by
      rw [signedSquareCutoffCoefficient, Finset.sum_mul]
      apply Finset.sum_le_sum
      intro i hi
      have hb := norm_signedSquareChartExpansion_le (k - (i + 1))
        ((2 * (k : ℝ) - 1) / 4) hε 0 h hx
      have hC := signedSquareChartBoundConstant_nonneg (k - (i + 1))
        ((2 * (k : ℝ) - 1) / 4)
      calc
        _ ≤ (k.choose (i + 1) : ℝ) *
            ‖iteratedDeriv (i + 1) (signedSquareTailCutoff R) (x ^ 2)‖ *
              (signedSquareChartBoundConstant (k - (i + 1)) ((2 * (k : ℝ) - 1) / 4) *
                x ^ (2 * ((2 * (k : ℝ) - 1) / 4) - 2 * ((k - (i + 1) : ℕ) : ℝ)) *
                  ((∑ j ∈ Finset.range (k - (i + 1) + 1), x ^ j) * J)) := by
          gcongr
          exact hb.trans (mul_le_mul_of_nonneg_left (hjet i hi) (by positivity))
        _ = _ := by ring

private theorem cutoff_contDiff_iteratedDeriv (R : ℝ) (j : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv j (signedSquareTailCutoff R)) := by
  induction j with
  | zero => simpa using contDiff_signedSquareTailCutoff R
  | succ j ih =>
    rw [iteratedDeriv_succ]
    exact (show ContDiff ℝ (∞ + 1) (iteratedDeriv j (signedSquareTailCutoff R)) by simpa using ih).deriv'

/-- The coefficient is continuous away from the square-root singularity. -/
theorem continuousOn_signedSquareCutoffCoefficient (k : ℕ) (R : ℝ) :
    ContinuousOn (signedSquareCutoffCoefficient k R) (Ioi 0) := by
  apply continuousOn_finsetSum
  intro i _hi
  apply ContinuousOn.mul
  · exact continuousOn_const.mul
      (((cutoff_contDiff_iteratedDeriv R (i + 1)).continuous.comp (by fun_prop)).norm.continuousOn)
  · apply ContinuousOn.mul
    · exact continuousOn_const.mul (fun x hx =>
        (Real.continuousAt_rpow_const x _ (Or.inl (ne_of_gt hx))).continuousWithinAt)
    · exact (by fun_prop : Continuous (fun x : ℝ =>
        ∑ j ∈ Finset.range (k - (i + 1) + 1), x ^ j)).continuousOn

/-- A positive uniform commutator coefficient exists on any compact
physical shell bounded away from zero, before selecting a ray or h. -/
theorem exists_signedSquareCutoffCoefficient_bound (k : ℕ) (R : ℝ)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ C > 0, ∀ x ∈ Icc ρ R, signedSquareCutoffCoefficient k R x ≤ C := by
  have hc := (continuousOn_signedSquareCutoffCoefficient k R).mono
    (show Icc ρ R ⊆ Ioi 0 from fun x hx => hρ.trans_le hx.1)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨max C 1, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro x hx
  exact (le_abs_self _).trans ((hC x hx).trans (le_max_left _ _))

private theorem cutoff_norm_add_sq_young (u v : ℂ) {η : ℝ} (hη : 0 < η) :
    ‖u + v‖ ^ 2 ≤ (1 + η) * ‖u‖ ^ 2 + (1 + η⁻¹) * ‖v‖ ^ 2 := by
  have ht := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr (norm_add_le u v)
  have hy : 2 * ‖u‖ * ‖v‖ ≤ η * ‖u‖ ^ 2 + η⁻¹ * ‖v‖ ^ 2 := by
    apply (mul_le_mul_iff_right₀ hη).mp
    rw [mul_add, ← mul_assoc η η⁻¹, mul_inv_cancel₀ hη.ne', one_mul]
    nlinarith [sq_nonneg (η * ‖u‖ - ‖v‖)]
  nlinarith

private theorem cutoff_smul_norm_le (R σ : ℝ) (z : ℂ) :
    ‖signedSquareTailCutoff R σ • z‖ ≤ ‖z‖ := by
  rw [norm_smul, Real.norm_of_nonneg (signedSquareTailCutoff_mem_Icc R σ).1]
  exact mul_le_of_le_one_left (norm_nonneg _) (signedSquareTailCutoff_mem_Icc R σ).2

/-- Pointwise normalized-Jacobian bound for the actual cutoff chart.
Young's inequality is applied once to the exact principal term, retaining
(1+η)4^(-k). The separate commutator is a genuinely local lower jet. -/
theorem signedSquareCutoffChart_jacobian_sq_le (k : ℕ) (R : ℝ) {η : ℝ} (hη : 0 < η)
    {ε : ℝ} (hε : ε ^ 2 = 1) {h : ℝ → ℂ} (hh : ContDiff ℝ ∞ h)
    {x : ℝ} (hx : 0 < x) :
    x * ‖iteratedDeriv k (signedSquareCutoffChart k R ε h) (x ^ 2)‖ ^ 2 ≤
      ((1 + η) / (4 : ℝ) ^ k) * ‖iteratedDeriv k h (ε * x)‖ ^ 2 +
        2 * signedSquareChartErrorConstant k η *
          ∑ j ∈ Finset.range k, x ^ (2 * (j : ℝ) - 2 * (k : ℝ)) *
            ‖iteratedDeriv j h (ε * x)‖ ^ 2 +
        (2 * (1 + η⁻¹)) *
          (x * ‖signedSquareCutoffCommutator k R ε h (x ^ 2)‖ ^ 2) := by
  let P := (ε ^ k / (2 : ℝ) ^ k) •
    (x ^ (-(1 / 2 : ℝ)) • iteratedDeriv k h (ε * x))
  let L := signedSquareChartLowerTerms k ((2 * (k : ℝ) - 1) / 4) ε 0 h (x ^ 2)
  let Q := signedSquareCutoffCommutator k R ε h (x ^ 2)
  let χ := signedSquareTailCutoff R (x ^ 2)
  have heq : iteratedDeriv k (signedSquareCutoffChart k R ε h) (x ^ 2) =
      χ • P + (χ • L + Q) := by
    rw [iteratedDeriv_signedSquareCutoffChart k R ε hh (sq_pos_of_pos hx),
      iteratedDeriv_signedSquareWeightedChart_leading_sq k ε hh hx, smul_add, add_assoc]
  rw [heq]
  have hy := cutoff_norm_add_sq_young (χ • P) (χ • L + Q) hη
  have he := cutoff_norm_add_sq_young (χ • L) Q (by norm_num : (0 : ℝ) < 1)
  norm_num only [inv_one, one_add_one_eq_two] at he
  have hp := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (cutoff_smul_norm_le R (x ^ 2) P)
  have hl := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (cutoff_smul_norm_le R (x ^ 2) L)
  have hmain := signedSquareChart_principal_jacobian k hε (iteratedDeriv k h (ε * x)) hx
  have herr := signedSquareChartLowerTerms_jacobian_sq_le k hε h hx
  change x * ‖P‖ ^ 2 = _ at hmain
  change x * ‖L‖ ^ 2 ≤ _ at herr
  have hηinv : 0 ≤ 1 + η⁻¹ := by positivity
  have hp' := mul_le_mul_of_nonneg_left hp (show 0 ≤ x * (1 + η) by positivity)
  have hl' := mul_le_mul_of_nonneg_left hl (show 0 ≤ 2 * x * (1 + η⁻¹) by positivity)
  have hy' := mul_le_mul_of_nonneg_left hy hx.le
  have he' := mul_le_mul_of_nonneg_left he (show 0 ≤ x * (1 + η⁻¹) by positivity)
  have herr' := mul_le_mul_of_nonneg_left herr (show 0 ≤ 2 * (1 + η⁻¹) by positivity)
  unfold signedSquareChartErrorConstant
  dsimp [χ] at hp' hl' hy' he'
  dsimp [Q]
  rw [div_eq_mul_inv]
  nlinarith

private theorem cutoff_tail_weight (k j : ℕ) (hj : j ∈ Finset.range k)
    {R x : ℝ} (hR : 2 ≤ R) (hx : R / 2 ≤ x) :
    x ^ (2 * (j : ℝ) - 2 * (k : ℝ)) ≤ 4 / R ^ 2 := by
  have hρ : 1 ≤ R / 2 := by linarith
  have hρpos : 0 < R / 2 := by linarith
  have hj' : j + 1 ≤ k := Finset.mem_range.mp hj
  have hc : (j : ℝ) + 1 ≤ k := by exact_mod_cast hj'
  have he : 2 * (j : ℝ) - 2 * (k : ℝ) ≤ -2 := by linarith
  calc
    _ ≤ (R / 2) ^ (2 * (j : ℝ) - 2 * (k : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hρpos hx (he.trans (by norm_num))
    _ ≤ (R / 2) ^ (-2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hρ he
    _ = 4 / R ^ 2 := by rw [Real.rpow_neg hρpos.le]; norm_num; ring

/-- A positive local-shell constant is fixed before the ray and smooth
input. The exterior error has R^(-2) gain; the remaining lower jet is
restricted to [R/2,R], while the principal coefficient stays exact. -/
theorem exists_signedSquareCutoffChart_tail_bound (k : ℕ) {η : ℝ} (hη : 0 < η)
    {R : ℝ} (hR : 2 ≤ R) :
    ∃ C > 0, ∀ (ε : ℝ), ε ^ 2 = 1 → ∀ (h : ℝ → ℂ), ContDiff ℝ ∞ h →
      ∀ x : ℝ, R / 2 ≤ x →
      x * ‖iteratedDeriv k (signedSquareCutoffChart k R ε h) (x ^ 2)‖ ^ 2 ≤
        ((1 + η) / (4 : ℝ) ^ k) * ‖iteratedDeriv k h (ε * x)‖ ^ 2 +
          (8 * signedSquareChartErrorConstant k η / R ^ 2) *
            (∑ j ∈ Finset.range k, ‖iteratedDeriv j h (ε * x)‖ ^ 2) +
          C * (Icc (R / 2) R).indicator
            (fun y => ∑ j ∈ Finset.range k, ‖iteratedDeriv j h (ε * y)‖ ^ 2) x := by
  have hRpos : 0 < R := by linarith
  obtain ⟨B, hB, hb⟩ := exists_signedSquareCutoffCoefficient_bound k R
    (show 0 < R / 2 by linarith)
  let C : ℝ := 2 * (1 + η⁻¹) * R * B ^ 2 * (k : ℝ) + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro ε hε h hh x hx
  have hxpos : 0 < x := by linarith
  have hweight :
      (∑ j ∈ Finset.range k, x ^ (2 * (j : ℝ) - 2 * (k : ℝ)) *
        ‖iteratedDeriv j h (ε * x)‖ ^ 2) ≤
        (4 / R ^ 2) * ∑ j ∈ Finset.range k, ‖iteratedDeriv j h (ε * x)‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun j hj =>
      mul_le_mul_of_nonneg_right (cutoff_tail_weight k j hj hR hx) (sq_nonneg _))
  have herror := mul_le_mul_of_nonneg_left hweight
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (signedSquareChartErrorConstant_nonneg k hη))
  have hcomm : (2 * (1 + η⁻¹)) *
      (x * ‖signedSquareCutoffCommutator k R ε h (x ^ 2)‖ ^ 2) ≤
      C * (Icc (R / 2) R).indicator
        (fun y => ∑ j ∈ Finset.range k, ‖iteratedDeriv j h (ε * y)‖ ^ 2) x := by
    by_cases hxR : x ≤ R
    · rw [indicator_of_mem (show x ∈ Icc (R / 2) R from ⟨hx, hxR⟩)]
      have hn := norm_signedSquareCutoffCommutator_le k R hε h hxpos
      have hJ : 0 ≤ ∑ j ∈ Finset.range k, ‖iteratedDeriv j h (ε * x)‖ :=
        Finset.sum_nonneg (fun _ _ => norm_nonneg _)
      have hn' : ‖signedSquareCutoffCommutator k R ε h (x ^ 2)‖ ≤
          B * ∑ j ∈ Finset.range k, ‖iteratedDeriv j h (ε * x)‖ :=
        hn.trans (mul_le_mul_of_nonneg_right (hb x ⟨hx, hxR⟩) hJ)
      have hn2 := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hB.le hJ)).mpr hn'
      have hCS := sq_sum_le_card_mul_sum_sq (s := Finset.range k)
        (f := fun j => ‖iteratedDeriv j h (ε * x)‖)
      simp only [Finset.card_range] at hCS
      have hlocal : x * ‖signedSquareCutoffCommutator k R ε h (x ^ 2)‖ ^ 2 ≤
          R * B ^ 2 * (k : ℝ) * ∑ j ∈ Finset.range k, ‖iteratedDeriv j h (ε * x)‖ ^ 2 := by
        calc
          _ ≤ R * (B * ∑ j ∈ Finset.range k, ‖iteratedDeriv j h (ε * x)‖) ^ 2 := by gcongr
          _ = R * B ^ 2 * (∑ j ∈ Finset.range k, ‖iteratedDeriv j h (ε * x)‖) ^ 2 := by ring
          _ ≤ R * B ^ 2 * ((k : ℝ) * ∑ j ∈ Finset.range k, ‖iteratedDeriv j h (ε * x)‖ ^ 2) := by
            gcongr
          _ = _ := by ring
      have hlocal' := mul_le_mul_of_nonneg_left hlocal
        (show 0 ≤ 2 * (1 + η⁻¹) by positivity)
      have hJsq : 0 ≤ ∑ j ∈ Finset.range k, ‖iteratedDeriv j h (ε * x)‖ ^ 2 :=
        Finset.sum_nonneg (fun _ _ => sq_nonneg _)
      dsimp [C]
      nlinarith
    · have hxR' : R < x := lt_of_not_ge hxR
      rw [signedSquareCutoffCommutator_eq_zero k R ε h (Or.inr (by nlinarith)),
        norm_zero, zero_pow (by omega : 2 ≠ 0), mul_zero, mul_zero,
        indicator_of_notMem (show x ∉ Icc (R / 2) R from fun hx' => hxR hx'.2), mul_zero]
  have hmain := signedSquareCutoffChart_jacobian_sq_le k R hη hε hh hxpos
  have heq : 2 * signedSquareChartErrorConstant k η *
      (4 / R ^ 2 * ∑ j ∈ Finset.range k, ‖iteratedDeriv j h (ε * x)‖ ^ 2) =
      (8 * signedSquareChartErrorConstant k η / R ^ 2) *
        ∑ j ∈ Finset.range k, ‖iteratedDeriv j h (ε * x)‖ ^ 2 := by ring
  rw [heq] at herror
  exact hmain.trans (add_le_add (add_le_add le_rfl herror) hcomm)

/-- Every actual derivative vanishes below the auxiliary half-radius
threshold, which lies strictly inside the zero region of the cutoff. -/
theorem iteratedDeriv_signedSquareCutoffChart_zero (k j : ℕ) {R : ℝ} (hR : 2 ≤ R)
    (ε : ℝ) (h : ℝ → ℂ) {σ : ℝ} (hσ : σ ≤ (R / 2) ^ 2) :
    iteratedDeriv j (signedSquareCutoffChart k R ε h) σ = 0 := by
  have hσ' : σ < R ^ 2 - 1 := by nlinarith
  have heq : signedSquareCutoffChart k R ε h =ᶠ[𝓝 σ] (fun _ => (0 : ℂ)) := by
    filter_upwards [Iio_mem_nhds hσ'] with t ht
    exact signedSquareCutoffChart_zero k R ε h ht.le
  rw [heq.iteratedDeriv_eq j]
  simp

/-- The actual whole-line localized derivative energy has normalized
Jacobian x on the positive physical ray. No second factor two appears. -/
theorem integral_signedSquareCutoffChart_deriv_jacobian (k j : ℕ) {R : ℝ} (hR : 2 ≤ R)
    (ε : ℝ) (h : ℝ → ℂ) :
    (1 / 2 : ℝ) * (∫ σ : ℝ, ‖iteratedDeriv j (signedSquareCutoffChart k R ε h) σ‖ ^ 2) =
      ∫ x in Ioi (R / 2), x * ‖iteratedDeriv j (signedSquareCutoffChart k R ε h) (x ^ 2)‖ ^ 2 := by
  have heq : (∫ σ in Ioi ((R / 2) ^ 2),
      ‖iteratedDeriv j (signedSquareCutoffChart k R ε h) σ‖ ^ 2) =
      ∫ σ : ℝ, ‖iteratedDeriv j (signedSquareCutoffChart k R ε h) σ‖ ^ 2 := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro σ hσ
    rw [iteratedDeriv_signedSquareCutoffChart_zero k j hR ε h (le_of_not_gt hσ),
      norm_zero, zero_pow (by omega : 2 ≠ 0)]
  rw [← heq, integral_signedSquare_jacobian _ (by linarith : 0 ≤ R / 2), ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x _hx
  ring

private theorem integrableOn_signedSquare_jacobian_iff (f : ℝ → ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    IntegrableOn f (Ioi (ρ ^ 2)) ↔ IntegrableOn (fun x => (2 * x) * f (x ^ 2)) (Ioi ρ) := by
  have hd (x : ℝ) (_hx : x ∈ Ioi ρ) :
      HasDerivWithinAt (fun x : ℝ => x ^ 2) (2 * x) (Ioi ρ) x := by
    simpa using (hasDerivAt_pow 2 x).hasDerivWithinAt
  have hinj : InjOn (fun x : ℝ => x ^ 2) (Ioi ρ) := by
    intro x hx y hy heq
    change ρ < x at hx
    change ρ < y at hy
    nlinarith
  have heq := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hd hinj f
  rw [image_sq_Ioi_of_nonneg hρ] at heq
  refine heq.trans (integrableOn_congr_fun ?_ measurableSet_Ioi)
  intro x hx
  change |2 * x| * f (x ^ 2) = (2 * x) * f (x ^ 2)
  rw [abs_of_nonneg (by have := hρ.trans hx.le; positivity)]

/-- Genuine integrated smooth-function transfer: the cutoff derivative
energy is finite, and its principal coefficient is (1+η)4^(-k). The local
term contains only lower derivatives on the compact physical shell.
The positive constant is selected before the ray and input function. -/
theorem exists_integral_signedSquareCutoffChart_deriv_le (k : ℕ) {η : ℝ} (hη : 0 < η)
    {R : ℝ} (hR : 2 ≤ R) :
    ∃ C > 0, ∀ (ε : ℝ), ε ^ 2 = 1 → ∀ (h : ℝ → ℂ), ContDiff ℝ ∞ h →
      (∀ j ≤ k, Integrable (fun x : ℝ => ‖iteratedDeriv j h (ε * x)‖ ^ 2)) →
      Integrable (fun σ : ℝ => ‖iteratedDeriv k (signedSquareCutoffChart k R ε h) σ‖ ^ 2) ∧
      (1 / 2 : ℝ) * (∫ σ : ℝ, ‖iteratedDeriv k (signedSquareCutoffChart k R ε h) σ‖ ^ 2) ≤
        ((1 + η) / (4 : ℝ) ^ k) * (∫ x in Ioi (R / 2), ‖iteratedDeriv k h (ε * x)‖ ^ 2) +
          (8 * signedSquareChartErrorConstant k η / R ^ 2) *
            (∫ x in Ioi (R / 2), ∑ j ∈ Finset.range k, ‖iteratedDeriv j h (ε * x)‖ ^ 2) +
          C * (∫ x in Icc (R / 2) R, ∑ j ∈ Finset.range k, ‖iteratedDeriv j h (ε * x)‖ ^ 2) := by
  obtain ⟨C, hC, hb⟩ := exists_signedSquareCutoffChart_tail_bound k hη hR
  refine ⟨C, hC, ?_⟩
  intro ε hε h hh hD
  let J := fun x : ℝ => ∑ j ∈ Finset.range k, ‖iteratedDeriv j h (ε * x)‖ ^ 2
  let f := fun x : ℝ => x * ‖iteratedDeriv k (signedSquareCutoffChart k R ε h) (x ^ 2)‖ ^ 2
  let g := fun x : ℝ => ((1 + η) / (4 : ℝ) ^ k) * ‖iteratedDeriv k h (ε * x)‖ ^ 2 +
    (8 * signedSquareChartErrorConstant k η / R ^ 2) * J x +
    C * (Icc (R / 2) R).indicator J x
  have hJ : Integrable J := by
    apply integrable_finsetSum
    intro j hj
    exact hD j (by have := Finset.mem_range.mp hj; omega)
  have hJ0 (x : ℝ) : 0 ≤ J x := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hg : Integrable g :=
    (((hD k le_rfl).const_mul _).add (hJ.const_mul _)).add
      ((hJ.indicator measurableSet_Icc).const_mul _)
  have hloc : ContDiff ℝ ∞ (signedSquareCutoffChart k R ε h) :=
    contDiff_signedSquareCutoffChart k (by linarith) ε hh
  have hfcont : Continuous f :=
    continuous_id.mul (((hloc.continuous_iteratedDeriv k (by simp)).comp (by fun_prop)).norm.pow 2)
  have hf0 : 0 ≤ᵐ[volume.restrict (Ioi (R / 2))] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact mul_nonneg (by have : R / 2 < x := hx; linarith) (sq_nonneg _)
  have hfg : f ≤ᵐ[volume.restrict (Ioi (R / 2))] g := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact hb ε hε h hh x hx.le
  have hf : IntegrableOn f (Ioi (R / 2)) :=
    hg.integrableOn.mono_nonneg hfcont.aestronglyMeasurable.restrict hf0 hfg
  have hFi : IntegrableOn
      (fun σ : ℝ => ‖iteratedDeriv k (signedSquareCutoffChart k R ε h) σ‖ ^ 2)
      (Ioi ((R / 2) ^ 2)) := by
    apply (integrableOn_signedSquare_jacobian_iff _ (by linarith : 0 ≤ R / 2)).mpr
    change Integrable (fun x => (2 * x) *
      ‖iteratedDeriv k (signedSquareCutoffChart k R ε h) (x ^ 2)‖ ^ 2)
      (volume.restrict (Ioi (R / 2)))
    simpa only [f, mul_assoc] using hf.const_mul 2
  have hF : Integrable (fun σ : ℝ => ‖iteratedDeriv k (signedSquareCutoffChart k R ε h) σ‖ ^ 2) := by
    apply (integrable_indicator_iff measurableSet_Ioi).mpr hFi |>.congr
    filter_upwards [] with σ
    by_cases hσ : σ ∈ Ioi ((R / 2) ^ 2)
    · rw [indicator_of_mem hσ]
    · rw [indicator_of_notMem hσ,
        iteratedDeriv_signedSquareCutoffChart_zero k k hR ε h (le_of_not_gt hσ),
        norm_zero, zero_pow (by omega : 2 ≠ 0)]
  refine ⟨hF, ?_⟩
  rw [integral_signedSquareCutoffChart_deriv_jacobian k k hR ε h]
  calc
    _ ≤ ∫ x in Ioi (R / 2), g x := integral_mono_ae hf hg.integrableOn hfg
    _ = ((1 + η) / (4 : ℝ) ^ k) * (∫ x in Ioi (R / 2), ‖iteratedDeriv k h (ε * x)‖ ^ 2) +
        (8 * signedSquareChartErrorConstant k η / R ^ 2) * (∫ x in Ioi (R / 2), J x) +
        C * (∫ x in Ioi (R / 2), (Icc (R / 2) R).indicator J x) := by
      dsimp [g]
      have hA : Integrable (fun x : ℝ => ((1 + η) / (4 : ℝ) ^ k) *
          ‖iteratedDeriv k h (ε * x)‖ ^ 2) (volume.restrict (Ioi (R / 2))) :=
        ((hD k le_rfl).const_mul _).integrableOn
      have hB : Integrable (fun x : ℝ =>
          (8 * signedSquareChartErrorConstant k η / R ^ 2) * J x)
          (volume.restrict (Ioi (R / 2))) := (hJ.const_mul _).integrableOn
      have hI : Integrable (fun x : ℝ => C * (Icc (R / 2) R).indicator J x)
          (volume.restrict (Ioi (R / 2))) :=
        ((hJ.indicator measurableSet_Icc).const_mul _).integrableOn
      have hAB : Integrable (fun x : ℝ => ((1 + η) / (4 : ℝ) ^ k) *
          ‖iteratedDeriv k h (ε * x)‖ ^ 2 +
          (8 * signedSquareChartErrorConstant k η / R ^ 2) * J x)
          (volume.restrict (Ioi (R / 2))) := hA.add hB
      rw [integral_add hAB hI, integral_add hA hB]
      simp only [integral_const_mul]
    _ ≤ _ := by
      apply add_le_add le_rfl
      apply mul_le_mul_of_nonneg_left _ hC.le
      rw [← integral_indicator measurableSet_Icc]
      apply setIntegral_le_integral (hJ.indicator measurableSet_Icc)
      exact ae_of_all _ (fun x => indicator_nonneg (fun y _ => hJ0 y) x)

private theorem cutoff_twoRay_integral_le (f : ℝ → ℝ) (hf : Integrable f)
    (hf0 : ∀ x, 0 ≤ f x) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    (∫ x in Ioi ρ, f x) + (∫ x in Ioi ρ, f (-x)) ≤ ∫ x : ℝ, f x := by
  rw [integral_reflected_positive_tail f ρ]
  have hd : Disjoint (Ioi ρ) (Iio (-ρ)) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    change ρ < x at hx
    change x < -ρ at hy
    linarith
  rw [← setIntegral_union hd measurableSet_Iio hf.integrableOn hf.integrableOn]
  exact setIntegral_le_integral hf (ae_of_all _ hf0)

/-- Integrated two-ray transfer without a factor-two loss. The main
energy is counted once on the whole physical line; only lower derivatives
enter the local shell integral. Constants precede the smooth input. -/
theorem exists_integral_signedSquareCutoffChart_twoRay_le (k : ℕ) {η : ℝ} (hη : 0 < η)
    {R : ℝ} (hR : 2 ≤ R) :
    ∃ C > 0, ∀ (h : ℝ → ℂ), ContDiff ℝ ∞ h →
      (∀ j ≤ k, Integrable (fun x : ℝ => ‖iteratedDeriv j h x‖ ^ 2)) →
      (1 / 2 : ℝ) *
        ((∫ σ : ℝ, ‖iteratedDeriv k (signedSquareCutoffChart k R 1 h) σ‖ ^ 2) +
          (∫ σ : ℝ, ‖iteratedDeriv k (signedSquareCutoffChart k R (-1) h) σ‖ ^ 2)) ≤
        ((1 + η) / (4 : ℝ) ^ k) * (∫ x : ℝ, ‖iteratedDeriv k h x‖ ^ 2) +
          (8 * signedSquareChartErrorConstant k η / R ^ 2) *
            (∫ x : ℝ, ∑ j ∈ Finset.range k, ‖iteratedDeriv j h x‖ ^ 2) +
          C * (∫ x in Icc (R / 2) R, ∑ j ∈ Finset.range k,
            (‖iteratedDeriv j h x‖ ^ 2 + ‖iteratedDeriv j h (-x)‖ ^ 2)) := by
  obtain ⟨C, hC, hb⟩ := exists_integral_signedSquareCutoffChart_deriv_le k hη hR
  refine ⟨C, hC, ?_⟩
  intro h hh hD
  have hp := (hb 1 (by norm_num) h hh (by simpa using hD)).2
  have hn := (hb (-1) (by norm_num) h hh (fun j hj => by
    simpa using (hD j hj).comp_neg)).2
  simp only [one_mul, neg_one_mul] at hp hn
  let J := fun x : ℝ => ∑ j ∈ Finset.range k, ‖iteratedDeriv j h x‖ ^ 2
  have hJ : Integrable J := by
    apply integrable_finsetSum
    intro j hj
    exact hD j (by have := Finset.mem_range.mp hj; omega)
  have ht := cutoff_twoRay_integral_le (fun x => ‖iteratedDeriv k h x‖ ^ 2)
    (hD k le_rfl) (fun x => sq_nonneg _) (by linarith : 0 ≤ R / 2)
  have hl := cutoff_twoRay_integral_le J hJ
    (fun x => Finset.sum_nonneg (fun j _ => sq_nonneg _)) (by linarith : 0 ≤ R / 2)
  have ht' := mul_le_mul_of_nonneg_left ht (show 0 ≤ (1 + η) / (4 : ℝ) ^ k by positivity)
  have hl' := mul_le_mul_of_nonneg_left hl
    (show 0 ≤ 8 * signedSquareChartErrorConstant k η / R ^ 2 from
      div_nonneg (mul_nonneg (by norm_num) (signedSquareChartErrorConstant_nonneg k hη)) (sq_nonneg R))
  have hlocal :
      (∫ x in Icc (R / 2) R, J x) + (∫ x in Icc (R / 2) R, J (-x)) =
        ∫ x in Icc (R / 2) R, ∑ j ∈ Finset.range k,
          (‖iteratedDeriv j h x‖ ^ 2 + ‖iteratedDeriv j h (-x)‖ ^ 2) := by
    rw [← integral_add hJ.integrableOn hJ.comp_neg.integrableOn]
    simp only [J, Finset.sum_add_distrib]
  dsimp [J] at hl' hlocal
  nlinarith

/-- Actual carrier zeros survive the cutoff. Above the killed prefix the
signed-square carrier must pull back into the physical zero set. -/
theorem signedSquareCutoffChart_zero_on_carrier (k : ℕ) (R ε : ℝ)
    (h : ℝ → ℂ) (Λ Γ : Set ℝ)
    (hzero : ∀ x ∈ Λ, h x = 0)
    (hcarrier : ∀ σ ∈ Γ, R ^ 2 - 1 < σ → ε * Real.sqrt σ ∈ Λ) :
    ∀ σ ∈ Γ, signedSquareCutoffChart k R ε h σ = 0 := by
  intro σ hσ
  by_cases hc : σ ≤ R ^ 2 - 1
  · exact signedSquareCutoffChart_zero k R ε h hc
  · have hz := hzero _ (hcarrier σ hσ (lt_of_not_ge hc))
    simp [signedSquareCutoffChart, signedSquareWeightedChart, signedSquareChartMonomial, hz]

/-- The actual localized mass has the same quadratic Jacobian factor as
the derivative energy, at every order k. -/
theorem signedSquareCutoffChart_mass_jacobian (k : ℕ) (R ε : ℝ) (h : ℝ → ℂ)
    {x : ℝ} (hx : 0 < x) :
    x * ‖signedSquareCutoffChart k R ε h (x ^ 2)‖ ^ 2 =
      (signedSquareTailCutoff R (x ^ 2)) ^ 2 * (x ^ (2 * k) * ‖h (ε * x)‖ ^ 2) := by
  have hw : x * (x ^ (2 * ((2 * (k : ℝ) - 1) / 4))) ^ 2 = x ^ (2 * k) := by
    rw [← Real.rpow_mul_natCast hx.le, ← Real.rpow_natCast]
    calc
      _ = x ^ (1 + 2 * ((2 * (k : ℝ) - 1) / 4) * (2 : ℕ)) := by
        rw [Real.rpow_add hx, Real.rpow_one]
      _ = _ := by congr 1; push_cast; ring
  rw [signedSquareCutoffChart, signedSquareWeightedChart,
    signedSquareChartMonomial_sq _ _ _ _ hx]
  simp only [iteratedDeriv_zero, norm_smul,
    Real.norm_of_nonneg (signedSquareTailCutoff_mem_Icc R (x ^ 2)).1,
    Real.norm_of_nonneg (Real.rpow_nonneg hx.le _), mul_pow]
  calc
    _ = (signedSquareTailCutoff R (x ^ 2)) ^ 2 *
        (x * (x ^ (2 * ((2 * (k : ℝ) - 1) / 4))) ^ 2) * ‖h (ε * x)‖ ^ 2 := by ring
    _ = _ := by rw [hw]; ring

/-- Exact mass transfer for the actual whole-line cutoff chart. The
factor 1/2 is exactly the same normalization as for its derivative energy. -/
theorem integral_signedSquareCutoffChart_mass (k : ℕ) {R : ℝ} (hR : 2 ≤ R)
    (ε : ℝ) (h : ℝ → ℂ) :
    (1 / 2 : ℝ) * (∫ σ : ℝ, ‖signedSquareCutoffChart k R ε h σ‖ ^ 2) =
      ∫ x in Ioi (R / 2), (signedSquareTailCutoff R (x ^ 2)) ^ 2 *
        (x ^ (2 * k) * ‖h (ε * x)‖ ^ 2) := by
  rw [show (fun σ => ‖signedSquareCutoffChart k R ε h σ‖ ^ 2) =
      (fun σ => ‖iteratedDeriv 0 (signedSquareCutoffChart k R ε h) σ‖ ^ 2) from rfl,
    integral_signedSquareCutoffChart_deriv_jacobian k 0 hR ε h]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  exact signedSquareCutoffChart_mass_jacobian k R ε h (by have : R / 2 < x := hx; linarith)

/-- Weighted square-integrability of the actual physical input produces
finite mass of the actual localized chart; its normalized mass dominates
the physical weighted tail. No spectral inequality is assumed. -/
theorem integrable_signedSquareCutoffChart_mass_and_tail_le (k : ℕ) {R : ℝ} (hR : 2 ≤ R)
    (ε : ℝ) {h : ℝ → ℂ} (hh : ContDiff ℝ ∞ h)
    (hW : Integrable (fun x : ℝ => x ^ (2 * k) * ‖h (ε * x)‖ ^ 2)) :
    Integrable (fun σ : ℝ => ‖signedSquareCutoffChart k R ε h σ‖ ^ 2) ∧
      (∫ x in Ioi R, x ^ (2 * k) * ‖h (ε * x)‖ ^ 2) ≤
        (1 / 2 : ℝ) * (∫ σ : ℝ, ‖signedSquareCutoffChart k R ε h σ‖ ^ 2) := by
  let f := fun x : ℝ => (signedSquareTailCutoff R (x ^ 2)) ^ 2 *
    (x ^ (2 * k) * ‖h (ε * x)‖ ^ 2)
  have hw0 (x : ℝ) : 0 ≤ x ^ (2 * k) * ‖h (ε * x)‖ ^ 2 := by
    rw [pow_mul]
    positivity
  have hf0 (x : ℝ) : 0 ≤ f x := mul_nonneg (sq_nonneg _) (hw0 x)
  have hfc : Continuous f := by
    exact (((contDiff_signedSquareTailCutoff R).continuous.comp (by fun_prop)).pow 2).mul
      ((by fun_prop : Continuous (fun x : ℝ => x ^ (2 * k))).mul
        ((hh.continuous.comp (by fun_prop)).norm.pow 2))
  have hf : Integrable f := by
    apply hW.mono_nonneg hfc.aestronglyMeasurable (ae_of_all _ hf0)
    apply ae_of_all
    intro x
    have hχ := signedSquareTailCutoff_mem_Icc R (x ^ 2)
    exact mul_le_of_le_one_left (hw0 x) (pow_le_one₀ hχ.1 hχ.2)
  have hFi : IntegrableOn (fun σ : ℝ => ‖signedSquareCutoffChart k R ε h σ‖ ^ 2)
      (Ioi ((R / 2) ^ 2)) := by
    apply (integrableOn_signedSquare_jacobian_iff _ (by linarith : 0 ≤ R / 2)).mpr
    apply (hf.const_mul 2).integrableOn.congr_fun
    · intro x hx
      change 2 * f x = (2 * x) * ‖signedSquareCutoffChart k R ε h (x ^ 2)‖ ^ 2
      have heq := signedSquareCutoffChart_mass_jacobian k R ε h (show 0 < x by
        have : R / 2 < x := hx
        linarith)
      dsimp [f]
      nlinarith [heq]
    · exact measurableSet_Ioi
  have hF : Integrable (fun σ : ℝ => ‖signedSquareCutoffChart k R ε h σ‖ ^ 2) := by
    apply (integrable_indicator_iff measurableSet_Ioi).mpr hFi |>.congr
    filter_upwards [] with σ
    by_cases hσ : σ ∈ Ioi ((R / 2) ^ 2)
    · rw [indicator_of_mem hσ]
    · rw [indicator_of_notMem hσ, signedSquareCutoffChart_zero k R ε h (by
        have : σ ≤ (R / 2) ^ 2 := le_of_not_gt hσ
        nlinarith), norm_zero, zero_pow (by omega : 2 ≠ 0)]
  refine ⟨hF, ?_⟩
  rw [integral_signedSquareCutoffChart_mass k hR ε h]
  have htail : (∫ x in Ioi R, x ^ (2 * k) * ‖h (ε * x)‖ ^ 2) = ∫ x in Ioi R, f x := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    have hxx : R ^ 2 ≤ x ^ 2 := by have : R < x := hx; nlinarith
    simp only [f, signedSquareTailCutoff_one R hxx, one_pow, one_mul]
  rw [htail]
  exact setIntegral_mono_set hf.integrableOn (ae_of_all _ hf0)
    (ae_of_all _ (by intro x hx; have : R < x := hx; change R / 2 < x; linarith))

end

end MeyerGeneralProblem
