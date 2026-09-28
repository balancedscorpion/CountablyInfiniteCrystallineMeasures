module

public import MeyerGeneralProblem.Sampling.BernsteinGrowth
public import Mathlib.Analysis.Complex.JensenFormula
import all Mathlib.Analysis.Complex.JensenFormula
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import all Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

/-!
# Sharp Jensen bounds for entire functions of exponential type

The angular average of the absolute imaginary part retains the coefficient
`2 / π`. Jensen's formula then bounds the actual multiplicity-weighted logarithmic
zero divisor, including zeros on the integration circle. Radial exponential type
and real-axis boundedness are the inputs; the sharp vertical bound is derived.
-/

noncomputable section

open Set Filter Complex MeasureTheory Metric Real MeromorphicOn
open scoped Topology

namespace MeyerGeneralProblem

/-- The absolute sine has integral four over one full period. -/
theorem integral_abs_sin_zero_two_pi :
    (∫ θ : ℝ in 0..2 * π, |Real.sin θ|) = 4 := by
  have hhalf : (∫ θ : ℝ in 0..π, |Real.sin θ|) = 2 := by
    calc
      _ = ∫ θ : ℝ in 0..π, Real.sin θ := by
        apply intervalIntegral.integral_congr
        intro θ hθ
        rw [uIcc_of_le pi_pos.le] at hθ
        exact abs_of_nonneg (Real.sin_nonneg_of_mem_Icc hθ)
      _ = 2 := by rw [integral_sin]; norm_num
  have hother : (∫ θ : ℝ in π..2 * π, |Real.sin θ|) = 2 := by
    have hshift := intervalIntegral.integral_comp_add_right
      (fun θ : ℝ => |Real.sin θ|) π (a := 0) (b := π)
    simp only [Real.sin_add_pi, abs_neg, zero_add, ← two_mul] at hshift
    exact hshift.symm.trans hhalf
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (Real.continuous_sin.abs.intervalIntegrable 0 π)
    (Real.continuous_sin.abs.intervalIntegrable π (2 * π)), hhalf, hother]
  norm_num

/-- The mean absolute imaginary part on a circle of radius `R` is `2 |R| / π`. -/
theorem circleAverage_abs_im_zero (R : ℝ) :
    Real.circleAverage (fun z : ℂ => |z.im|) 0 R = 2 * |R| / π := by
  simp only [Real.circleAverage, circleMap_zero_im, abs_mul, smul_eq_mul,
    intervalIntegral.integral_const_mul, integral_abs_sin_zero_two_pi]
  field_simp
  ring

/-- Sharp logarithmic circle-average bound. Zeros on the circle are removed only
on a codiscrete exceptional set, which does not change the genuine integral. -/
theorem circleAverage_log_norm_le_of_exponentialType
    {G : ℂ → ℂ} {τ M R : ℝ}
    (hG : Differentiable ℂ G) (hτ : 0 ≤ τ) (hM : 0 < M) (hR : 0 < R)
    (htype : ∀ ε > 0, ∃ C > 0, ∀ z,
      ‖G z‖ ≤ C * Real.exp ((τ + ε) * ‖z‖))
    (hreal : ∀ x : ℝ, ‖G x‖ ≤ M) (hzero : G 0 ≠ 0) :
    Real.circleAverage (fun z => Real.log ‖G z‖) 0 R ≤
      Real.log M + 2 * τ * R / π := by
  have hA : AnalyticOnNhd ℂ G univ := fun z _ => hG.analyticAt z
  have hne : ∀ᶠ z in codiscreteWithin univ, G z ≠ 0 :=
    (hA.eqOn_zero_or_eventually_ne_zero_of_preconnected isPreconnected_univ).resolve_left
      (fun h => hzero (h (mem_univ 0)))
  let J : ℂ → ℝ := fun z => if G z = 0 then Real.log M + τ * |z.im| else Real.log ‖G z‖
  have heq : (fun z => Real.log ‖G z‖) =ᶠ[codiscreteWithin (sphere 0 |R|)] J := by
    filter_upwards [codiscreteWithin_mono (subset_univ _) hne] with z hz
    simp [J, hz]
  have hlog : CircleIntegrable (fun z => Real.log ‖G z‖) 0 R :=
    (hA.mono (subset_univ _)).meromorphicOn.circleIntegrable_log_norm
  have hbcontinuous : Continuous (fun z : ℂ => Real.log M + τ * |z.im|) := by fun_prop
  have hbound : ∀ z, J z ≤ Real.log M + τ * |z.im| := by
    intro z
    by_cases hz : G z = 0
    · simp [J, hz]
    · simp only [J, hz, ↓reduceIte]
      calc
        Real.log ‖G z‖ ≤ Real.log (M * Real.exp (τ * |z.im|)) :=
          Real.log_le_log (norm_pos_iff.mpr hz)
            (norm_entire_le_exp_abs_im hG hτ hM.le htype hreal z)
        _ = Real.log M + τ * |z.im| := by
          rw [Real.log_mul hM.ne' (Real.exp_ne_zero _), Real.log_exp]
  calc
    _ = Real.circleAverage J 0 R := Real.circleAverage_congr_codiscreteWithin heq hR.ne'
    _ ≤ Real.circleAverage (fun z : ℂ => Real.log M + τ * |z.im|) 0 R :=
      Real.circleAverage_mono (CircleIntegrable.congr_codiscreteWithin heq hlog)
        hbcontinuous.continuousOn.circleIntegrable' (fun z _ => hbound z)
    _ = Real.log M + 2 * τ * R / π := by
      rw [Real.circleAverage_fun_add (by fun_prop) (by fun_prop), Real.circleAverage_const]
      change Real.log M + Real.circleAverage (fun z : ℂ => τ • |z.im|) 0 R = _
      rw [Real.circleAverage_fun_smul, circleAverage_abs_im_zero, abs_of_pos hR]
      simp only [smul_eq_mul]
      ring

/-- The actual Jensen logarithmic divisor of a nonzero entire function of type
at most `τ` has the sharp linear bound `2 τ R / π`, with the exact normalization
correction. Divisor values count zero multiplicities. -/
theorem log_divisor_le_of_exponentialType
    {G : ℂ → ℂ} {τ M R : ℝ}
    (hG : Differentiable ℂ G) (hτ : 0 ≤ τ) (hM : 0 < M) (hR : 0 < R)
    (htype : ∀ ε > 0, ∃ C > 0, ∀ z,
      ‖G z‖ ≤ C * Real.exp ((τ + ε) * ‖z‖))
    (hreal : ∀ x : ℝ, ‖G x‖ ≤ M) (hzero : G 0 ≠ 0) :
    (∑ᶠ u : ℂ, (divisor G (closedBall 0 R) u : ℝ) * Real.log (R * ‖u‖⁻¹)) ≤
      2 * τ * R / π + Real.log M - Real.log ‖G 0‖ := by
  have hA : AnalyticOnNhd ℂ G (closedBall 0 |R|) := fun z _ => hG.analyticAt z
  have hjensen := hA.circleAverage_log_norm hR.ne' hzero
  have hbound := circleAverage_log_norm_le_of_exponentialType hG hτ hM hR htype hreal hzero
  simp only [zero_sub, norm_neg] at hjensen
  rw [abs_of_pos hR] at hjensen
  linarith

private theorem nat_le_divisor_of_jet_zeros {G : ℂ → ℂ} {U : Set ℂ} {z : ℂ} {m : ℕ}
    (hG : Differentiable ℂ G) (hzero : G 0 ≠ 0) (hz : z ∈ U)
    (hjet : ∀ j < m, iteratedDeriv j G z = 0) :
    (m : ℤ) ≤ divisor G U z := by
  have hA : AnalyticOnNhd ℂ G univ := fun w _ => hG.analyticAt w
  have hfinite : analyticOrderAt G z ≠ ⊤ := by
    intro htop
    have heq : G =ᶠ[𝓝 z] 0 := analyticOrderAt_eq_top.mp htop
    exact hzero ((hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (mem_univ z) heq) (mem_univ 0))
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hfinite
  have hm := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hG.analyticAt z)).mpr hjet
  rw [← hk] at hm
  have hAU : AnalyticOnNhd ℂ G U := fun w _ => hG.analyticAt w
  rw [hAU.divisor_apply hz, ← hk]
  simpa using (by exact_mod_cast hm : (m : ℤ) ≤ k)

private theorem divisor_log_weight_nonneg {G : ℂ → ℂ} {R : ℝ}
    (hG : Differentiable ℂ G) (_hR : 0 < R) (u : ℂ) :
    0 ≤ (divisor G (closedBall 0 R) u : ℝ) * Real.log (R * ‖u‖⁻¹) := by
  by_cases hu : u ∈ closedBall 0 R
  · have hA : AnalyticOnNhd ℂ G (closedBall 0 R) := fun w _ => hG.analyticAt w
    apply mul_nonneg (by exact_mod_cast hA.divisor_nonneg u)
    by_cases hu0 : u = 0
    · simp [hu0]
    · apply Real.log_nonneg
      rw [← div_eq_mul_inv]
      apply (one_le_div (norm_pos_iff.mpr hu0)).mpr
      simpa only [mem_closedBall, dist_zero_right] using hu
  · simp [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hu]

/-- Any finite collection of genuine jet zeros satisfies the sharp Jensen bound,
with each node counted by the number of its vanishing derivatives. Nodes may
coincide in a limiting cluster through the integer multiplicity at that node. -/
theorem finite_jet_zero_log_sum_le_of_exponentialType
    {G : ℂ → ℂ} {τ M R : ℝ} (s : Finset ℂ) (m : ℂ → ℕ)
    (hG : Differentiable ℂ G) (hτ : 0 ≤ τ) (hM : 0 < M) (hR : 0 < R)
    (htype : ∀ ε > 0, ∃ C > 0, ∀ z,
      ‖G z‖ ≤ C * Real.exp ((τ + ε) * ‖z‖))
    (hreal : ∀ x : ℝ, ‖G x‖ ≤ M) (hzero : G 0 ≠ 0)
    (hnodes : ∀ z ∈ s, ‖z‖ ≤ R)
    (hjets : ∀ z ∈ s, ∀ j < m z, iteratedDeriv j G z = 0) :
    (∑ z ∈ s, (m z : ℝ) * Real.log (R * ‖z‖⁻¹)) ≤
      2 * τ * R / π + Real.log M - Real.log ‖G 0‖ := by
  classical
  let g : ℂ → ℝ := fun u => (divisor G (closedBall 0 R) u : ℝ) * Real.log (R * ‖u‖⁻¹)
  have hfin : (Function.support g).Finite :=
    ((divisor G (closedBall 0 R)).finiteSupport (isCompact_closedBall 0 R)).subset
      (fun u hu => by
        contrapose! hu
        have hu' : divisor G (closedBall 0 R) u = 0 := by simpa using hu
        simp [g, Function.mem_support, hu'])
  have hnonneg : ∀ u, 0 ≤ g u := divisor_log_weight_nonneg hG hR
  have hsum : (∑ z ∈ s, (m z : ℝ) * Real.log (R * ‖z‖⁻¹)) ≤ ∑ᶠ u, g u := by
    rw [finsum_eq_sum_of_support_subset g
      (s := s ∪ hfin.toFinset) (by simp only [Finset.coe_union, Set.Finite.coe_toFinset]; tauto_set)]
    apply le_trans (Finset.sum_le_sum (s := s) (g := g) ?_)
      (Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
        (fun u _ _ => hnonneg u))
    intro z hz
    change (m z : ℝ) * _ ≤ (divisor G (closedBall 0 R) z : ℝ) * _
    by_cases hz0 : z = 0
    · simp [hz0]
    · apply mul_le_mul_of_nonneg_right
      · exact_mod_cast nat_le_divisor_of_jet_zeros hG hzero
          (by simpa only [mem_closedBall, dist_zero_right] using hnodes z hz) (hjets z hz)
      · apply Real.log_nonneg
        rw [← div_eq_mul_inv]
        exact (one_le_div (norm_pos_iff.mpr hz0)).mpr (hnodes z hz)
  exact hsum.trans (log_divisor_le_of_exponentialType hG hτ hM hR htype hreal hzero)

end MeyerGeneralProblem
