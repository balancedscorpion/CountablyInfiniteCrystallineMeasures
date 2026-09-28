module

public import MeyerGeneralProblem.Cardinal.Adaptive.ActualFutureTailBounds
public import MeyerGeneralProblem.Cardinal.Adaptive.PeriodicDescent

@[expose] public section

/-! # Local jets on isolated points of a whole periodic closure -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open Filter
open scoped Topology

/-- Ordinary support and vanishing on the complementary open testing region
agree for the actual compact-test definitions used by the lift and jet modules. -/
theorem supportedOn_iff_vanishesOn_compl (C : Set ℝ) (U : TemperedDistribution ℝ ℂ) :
    DistributionSupportedOn C U ↔ DistributionVanishesOn Cᶜ U := by
  constructor
  · intro h f hf hs
    apply h f hf
    intro a ha
    apply notMem_tsupport_iff_eventuallyEq.mp
    exact fun hmem => hs hmem ha
  · intro h f hf hz
    apply h f hf
    intro a ha hc
    exact (notMem_tsupport_iff_eventuallyEq.mpr (hz a hc)) ha

/-- The chosen template is exactly one on a neighbourhood of zero. -/
theorem fixedProbeTemplate_eventually_one :
    ∀ᶠ x : ℝ in 𝓝 0, fixedProbeTemplate x = 1 := by
  have he : ∀ᶠ x : ℝ in 𝓝 0, |x| < 1/4 :=
    (isOpen_lt continuous_abs continuous_const).mem_nhds (by norm_num)
  exact he.mono (fun x hx => fixedProbeTemplate_eq_one x hx.le)

/-- The fixed probe's actual support radius scales by one half. -/
theorem fixedShrinkingBump_zero (a δ : ℝ) (hδ : 0 < δ) (x : ℝ)
    (hx : δ/2 ≤ |x-a|) : shrinkingBump fixedProbeTemplate a δ hδ x = 0 := by
  rw [shrinkingBump_apply]
  apply fixedProbeTemplate_eq_zero
  rw [abs_div,abs_of_pos hδ]
  apply (le_div_iff₀ hδ).mpr
  linarith

/-- The fixed probe is one on its quarter-radius central interval. -/
theorem fixedShrinkingBump_one (a δ : ℝ) (hδ : 0 < δ) (x : ℝ)
    (hx : |x-a| ≤ δ/4) : shrinkingBump fixedProbeTemplate a δ hδ x = 1 := by
  rw [shrinkingBump_apply]
  apply fixedProbeTemplate_eq_one
  rw [abs_div,abs_of_pos hδ]
  apply (div_le_iff₀ hδ).mpr
  linarith

/-- A strict separation margin makes the whole fixed cutoff identically zero
near a point, which is stronger than vanishing at the point. -/
theorem fixedShrinkingBump_eventually_zero (a δ : ℝ) (hδ : 0 < δ) (b : ℝ)
    (hb : δ/2 < |b-a|) :
    (shrinkingBump fixedProbeTemplate a δ hδ : ℝ → ℂ) =ᶠ[𝓝 b] 0 := by
  have he : ∀ᶠ x in 𝓝 b, δ/2 < |x-a| :=
    (isOpen_lt continuous_const ((continuous_id.sub continuous_const).abs)).mem_nhds hb
  exact he.mono (fun x hx => fixedShrinkingBump_zero a δ hδ x hx.le)

/-- Localization at a genuinely isolated point of any whole support set produces
an actual point-supported source. The set need not be locally finite at seams. -/
theorem isolated_native_localization_supportedAt (q : ℕ) (T : HermiteScale (-(q:ℤ)))
    (C : Set ℝ) (hT : DistributionSupportedOn C (hermiteScaleDistribution q T))
    (a δ : ℝ) (hδ : 0 < δ) (hiso : ∀ x ∈ C, |x-a| < δ → x=a) :
    DistributionSupportedAt a (hermiteScaleDistribution q
      (nativeMultiplier q q (shrinkingBump fixedProbeTemplate a δ hδ) T)) := by
  rw [nativeMultiplier_schwartz_realizes]
  intro f hf hfa
  rw [TemperedDistribution.smulLeftCLM_apply_apply]
  apply hT
  · convert! hf.mul_left (f := fun x => shrinkingBump fixedProbeTemplate a δ hδ x) using 1
    ext x
    simp only [SchwartzMap.smulLeftCLM_apply_apply
      (shrinkingBump fixedProbeTemplate a δ hδ).hasTemperateGrowth,smul_eq_mul,Pi.mul_apply]
  · intro b hb
    by_cases he : b=a
    · subst b
      filter_upwards [hfa] with x hx
      simp only [SchwartzMap.smulLeftCLM_apply_apply
        (shrinkingBump fixedProbeTemplate a δ hδ).hasTemperateGrowth,hx,smul_zero,Pi.zero_apply]
    · have hab : δ ≤ |b-a| := le_of_not_gt (fun h => he (hiso b hb h))
      have hz := fixedShrinkingBump_eventually_zero a δ hδ b (by linarith)
      filter_upwards [hz] with x hx
      simp only [SchwartzMap.smulLeftCLM_apply_apply
        (shrinkingBump fixedProbeTemplate a δ hδ).hasTemperateGrowth,hx,Pi.zero_apply,zero_smul]

/-- Actual same-order local jet coefficients, fixed before choosing smaller probes. -/
def isolatedNativeJetCoefficient (q : ℕ) (T : HermiteScale (-(q:ℤ)))
    (a δ : ℝ) (hδ : 0 < δ) (r : ℕ) : ℂ :=
  hermiteScaleDistribution q (nativeMultiplier q q (shrinkingBump fixedProbeTemplate a δ hδ) T)
    (pointJetBasis r a)

/-- Every test inside the isolation neighborhood has the finite jet formula with
degree2q. This follows from native point classification, not supplied jet data. -/
theorem isolated_native_jet_formula (q : ℕ) (T : HermiteScale (-(q:ℤ)))
    (C : Set ℝ) (hT : DistributionSupportedOn C (hermiteScaleDistribution q T))
    (a δ : ℝ) (hδ : 0 < δ) (hiso : ∀ x ∈ C, |x-a| < δ → x=a)
    (f : SchwartzMap ℝ ℂ) (hf : HasCompactSupport (f : ℝ → ℂ))
    (hs : ∀ x ∈ tsupport f, |x-a| ≤ δ/4) :
    hermiteScaleDistribution q T f = ∑ r ∈ Finset.range (2*q+1),
      isolatedNativeJetCoefficient q T a δ hδ r * iteratedDeriv r (f : ℝ → ℂ) a := by
  have he : hermiteScaleDistribution q T f =
      hermiteScaleDistribution q (nativeMultiplier q q (shrinkingBump fixedProbeTemplate a δ hδ) T) f := by
    rw [nativeMultiplier_schwartz_realizes,TemperedDistribution.smulLeftCLM_apply_apply]
    congr 1
    ext x
    rw [SchwartzMap.smulLeftCLM_apply_apply (shrinkingBump fixedProbeTemplate a δ hδ).hasTemperateGrowth]
    by_cases hx : f x=0
    · simp [hx]
    · rw [fixedShrinkingBump_one a δ hδ x (hs x (subset_tsupport f hx)),one_smul]
  rw [he]
  exact supportedAt_compact_jet_formula q _ a
    (isolated_native_localization_supportedAt q T C hT a δ hδ hiso) f hf

/-- Normalized probes with the fixed template have the same half-width support,
regardless of jet order. -/
theorem fixedJetProbe_support (a δ : ℝ) (hδ : 0 < δ) (r : ℕ) :
    tsupport (localJetProbe fixedProbeTemplate δ hδ r a) ⊆ Metric.closedBall a (δ/2) := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  rw [Metric.mem_closedBall,Real.dist_eq]
  apply le_of_not_gt
  intro h
  apply hx
  rw [localJetProbe_apply]
  have hz : fixedProbeTemplate ((x-a)/δ) = 0 := by
    apply fixedProbeTemplate_eq_zero
    rw [abs_div,abs_of_pos hδ]
    apply (le_div_iff₀ hδ).mpr
    linarith
  rw [hz,mul_zero]

/-- Each actual normalized probe is compactly supported. -/
theorem fixedJetProbe_hasCompactSupport (a δ : ℝ) (hδ : 0 < δ) (r : ℕ) :
    HasCompactSupport (localJetProbe fixedProbeTemplate δ hδ r a : ℝ → ℂ) :=
  (isCompact_closedBall a (δ/2)).of_isClosed_subset (isClosed_tsupport _)
    (fixedJetProbe_support a δ hδ r)

/-- Every sufficiently narrow normalized probe reads one fixed local jet
coefficient exactly, independently of its changing width. -/
theorem isolatedNativeJetCoefficient_eq_probe (q : ℕ) (T : HermiteScale (-(q:ℤ)))
    (C : Set ℝ) (hT : DistributionSupportedOn C (hermiteScaleDistribution q T))
    (a δ : ℝ) (hδ : 0 < δ) (hiso : ∀ x ∈ C, |x-a| < δ → x=a)
    (ε : ℝ) (hε : 0 < ε) (hεδ : ε ≤ δ/2) (r : ℕ) (hr : r ≤ 2*q) :
    hermiteScaleDistribution q T (localJetProbe fixedProbeTemplate ε hε r a) =
      isolatedNativeJetCoefficient q T a δ hδ r := by
  rw [isolated_native_jet_formula q T C hT a δ hδ hiso _
    (fixedJetProbe_hasCompactSupport a ε hε r) (by
      intro x hx
      have h := fixedJetProbe_support a ε hε r hx
      rw [Metric.mem_closedBall,Real.dist_eq] at h
      linarith)]
  simp only [localJetProbe_derivative_center fixedProbeTemplate fixedProbeTemplate_eventually_one,
    mul_ite,mul_one,mul_zero]
  simp only [Finset.sum_ite_eq',Finset.mem_range,show r<2*q+1 by omega,ite_true]

/-- The actual jet width eventually fits any fixed isolation neighborhood. No
new gap or source-dependent stage parameters are selected in this limit. -/
theorem actualStage_jetRadius_eventually_le (ψ : SchwartzMap ℝ ℂ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (actualStage ψ n).jetRadius ≤ ε := by
  obtain ⟨N,hN⟩ := exists_nat_gt (1/ε)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hnat : (N:ℝ) ≤ n := by exact_mod_cast hn
  have hpos : (0:ℝ)<(n+1:ℕ) := by positivity
  have hbound : 1/(n+1:ℝ) ≤ ε := by
    apply (div_le_iff₀ (by positivity : (0:ℝ)<(n+1:ℝ))).mpr
    have hh := (div_lt_iff₀ hε).mp hN
    nlinarith
  exact (min_le_right _ _).trans (by simpa only [PNat.mk_coe,Nat.cast_add,Nat.cast_one] using hbound)

/-- The exact stage error tends to zero through all stages. -/
theorem stageError_tendsto_zero :
    Tendsto (fun n : ℕ => (2:ℝ)^(-((n+1:ℕ):ℤ))) atTop (𝓝 0) := by
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/2)
    (by norm_num : (1/2:ℝ)<1)
  have h := hp.mul_const (1/2:ℝ)
  have he (n : ℕ) : (2:ℝ)^(-((n+1:ℕ):ℤ)) = (1/2:ℝ)^n*(1/2) := by
    rw [zpow_neg,zpow_natCast,← inv_pow,pow_succ]
    norm_num
  simpa only [he,zero_mul] using h

/-- An eventual sequence of the actual geometric error bounds forces exact
coefficient equality. The threshold may depend on the fixed point and order. -/
theorem eq_of_eventual_stage_errors (x y : ℂ) (B : ℝ)
    (h : ∀ᶠ n : ℕ in atTop, ‖x-y‖ ≤ (2:ℝ)^(-((n+1:ℕ):ℤ))*B) : x=y := by
  have ht := stageError_tendsto_zero.mul_const B
  have hn : ‖x-y‖ ≤ 0 := by
    apply ge_of_tendsto (by simpa only [zero_mul] using ht)
    exact h
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hn (norm_nonneg _)))

end
end MeyerGeneralProblem.Adaptive
