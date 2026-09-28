module

public import MeyerGeneralProblem.Cardinal.Adaptive.AntiperiodicConjugation
public import MeyerGeneralProblem.Cardinal.Adaptive.NativeDiscreteJets

@[expose] public section

/-! Local cancellation of smooth multipliers off their full zero set. -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open Set Filter
open scoped ContDiff Topology

/-- Division is smooth for a compact numerator when the denominator is nonzero
on its support. Outside that support the quotient is locally identically zero. -/
theorem contDiff_compact_offZero_quotient (f : SchwartzMap ℝ ℂ) (χ : ℝ → ℂ)
    (hχ : ContDiff ℝ ∞ χ) (hzero : ∀ x ∈ tsupport f, χ x ≠ 0) :
    ContDiff ℝ ∞ (fun x => f x/χ x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport f
  · simpa only [div_eq_mul_inv,Pi.inv_apply] using!
      (f.smooth ⊤).contDiffAt.mul (hχ.contDiffAt.inv (hzero x hx))
  · have he : (fun x => f x/χ x) =ᶠ[𝓝 x] (fun _ => (0:ℂ)) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
      simp only [hy,Pi.zero_apply,zero_div]
    exact contDiffAt_const.congr_of_eventuallyEq he

/-- An actual compact Schwartz quotient, with no inverse growth condition. -/
def compactOffZeroQuotient (f : SchwartzMap ℝ ℂ) (hf : HasCompactSupport f)
    (χ : ℝ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hzero : ∀ x ∈ tsupport f, χ x ≠ 0) :
    SchwartzMap ℝ ℂ :=
  (HasCompactSupport.intro hf (fun x hx => by
    rw [image_eq_zero_of_notMem_tsupport hx,zero_div])).toSchwartzMap
      (contDiff_compact_offZero_quotient f χ hχ hzero)

/-- Exact pointwise cancellation for the constructed compact quotient. -/
theorem compactOffZeroQuotient_mul (f : SchwartzMap ℝ ℂ) (hf : HasCompactSupport f)
    (χ : ℝ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hzero : ∀ x ∈ tsupport f, χ x ≠ 0) (x : ℝ) :
    χ x*compactOffZeroQuotient f hf χ hχ hzero x = f x := by
  change χ x*(f x/χ x)=f x
  by_cases hx : χ x=0
  · have hf0 : f x=0 := by
      by_contra hn
      exact hzero x (subset_tsupport f hn) hx
    rw [hf0,zero_div,mul_zero]
  · exact mul_div_cancel₀ (f x) hx

/-- A whole product that vanishes can be cancelled on every open region where
the multiplier is nonzero, including for flat multipliers. -/
theorem distributionVanishesOn_of_multiplier_zero (O : Set ℝ) (χ : ℝ → ℂ)
    (hχ : ContDiff ℝ ∞ χ) (hg : χ.HasTemperateGrowth)
    (hzero : ∀ x ∈ O, χ x ≠ 0) (U : TemperedDistribution ℝ ℂ)
    (hU : TemperedDistribution.smulLeftCLM ℂ χ U = 0) : DistributionVanishesOn O U := by
  intro f hf hfO
  have hn : ∀ x ∈ tsupport f, χ x ≠ 0 := fun x hx => hzero x (hfO hx)
  let q := compactOffZeroQuotient f hf χ hχ hn
  have he : SchwartzMap.smulLeftCLM ℂ χ q = f := by
    ext x
    rw [SchwartzMap.smulLeftCLM_apply_apply hg,smul_eq_mul]
    exact compactOffZeroQuotient_mul f hf χ hχ hn x
  have hz := congrArg (fun V : TemperedDistribution ℝ ℂ => V q) hU
  rw [TemperedDistribution.smulLeftCLM_apply_apply,he] at hz
  exact hz

/-- Periodic multipliers commute with the genuine distributional translation. -/
theorem periodicMultiplier_translation (χ : ℝ → ℂ) (hg : χ.HasTemperateGrowth)
    (P : ℝ) (hP : Function.Periodic χ P) (U : TemperedDistribution ℝ ℂ) :
    combDistributionTranslation P (TemperedDistribution.smulLeftCLM ℂ χ U) =
      TemperedDistribution.smulLeftCLM ℂ χ (combDistributionTranslation P U) := by
  ext f
  rw [combDistributionTranslation_apply,TemperedDistribution.smulLeftCLM_apply_apply,
    TemperedDistribution.smulLeftCLM_apply_apply,combDistributionTranslation_apply]
  congr 1
  ext x
  simp only [SchwartzMap.smulLeftCLM_apply_apply hg,combSchwartzTranslation_apply]
  rw [add_comm P x,hP x]

/-- Every finite antiperiodic difference commutes with the same periodic multiplier. -/
theorem periodicMultiplier_antidifference_iter (χ : ℝ → ℂ) (hg : χ.HasTemperateGrowth)
    (P : ℝ) (hP : Function.Periodic χ P) (n : ℕ) (U : TemperedDistribution ℝ ℂ) :
    (distributionAntidifference P : TemperedDistribution ℝ ℂ → TemperedDistribution ℝ ℂ)^[n]
      (TemperedDistribution.smulLeftCLM ℂ χ U) =
    TemperedDistribution.smulLeftCLM ℂ χ
      ((distributionAntidifference P : TemperedDistribution ℝ ℂ → TemperedDistribution ℝ ℂ)^[n] U) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply',Function.iterate_succ_apply',ih]
      simp only [distributionAntidifference,_root_.add_apply,ContinuousLinearMap.id_apply,
        periodicMultiplier_translation χ hg P hP,map_add]

end
end MeyerGeneralProblem.Adaptive
