module

public import MeyerGeneralProblem.Cardinal.Adaptive.AtomicProbeRecovery

@[expose] public section

/-! # Canonical native jet readings and atomic recovery on the actual carrier -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open Filter
open scoped Topology

/-- The predetermined probes eventually read each canonical discrete native jet. -/
theorem carrierJetReading_eq_actualProbe_eventually (S : LocallyFiniteCarrier) (q : ℕ)
    (T : HermiteScale (-(q:ℤ))) (hT : DistributionSupportedOn S.carrier (hermiteScaleDistribution q T))
    (a : S.subtype) (r : ℕ) (hr : r ≤ 2*q) :
    ∀ᶠ n : ℕ in atTop,
      carrierJetReading S (hermiteScaleDistribution q T) a r =
        hermiteScaleDistribution q T (localJetProbe fixedProbeTemplate
          (actualStage fixedProbeTemplate n).jetRadius (actualStage fixedProbeTemplate n).jetRadius_pos r a) := by
  filter_upwards [actualStage_jetRadius_eventually_le fixedProbeTemplate (S.isolationRadius a)
    (S.isolationRadius_pos a)] with n hn
  apply carrierJetReading_eq_of_probe S q T hT a r hr _ (fixedJetProbe_hasCompactSupport _ _ _ _)
  · intro k _
    exact localJetProbe_derivative_center fixedProbeTemplate fixedProbeTemplate_eventually_one _ _ r k a
  · intro b hba
    apply notMem_tsupport_iff_eventuallyEq.mp
    intro hmem
    have hd := fixedJetProbe_support (a:ℝ) _ _ r hmem
    rw [Metric.mem_closedBall,Real.dist_eq] at hd
    have hsep := S.isolationRadius_le_dist a b.property (fun he => hba (Subtype.ext he))
    rw [Real.dist_eq] at hsep
    have hpos := (actualStage fixedProbeTemplate n).jetRadius_pos
    linarith

/-- Canonical and directly localized coefficients are the same actual local jet. -/
theorem carrierJetReading_eq_isolatedNative (S : LocallyFiniteCarrier) (q : ℕ)
    (T : HermiteScale (-(q:ℤ))) (hT : DistributionSupportedOn S.carrier (hermiteScaleDistribution q T))
    (a : S.subtype) (r : ℕ) (hr : r ≤ 2*q) :
    carrierJetReading S (hermiteScaleDistribution q T) a r =
      isolatedNativeJetCoefficient q T a (S.isolationRadius a) (S.isolationRadius_pos a) r := by
  have hsmall := actualStage_jetRadius_eventually_le fixedProbeTemplate (S.isolationRadius a/2)
    (by have := S.isolationRadius_pos a; positivity)
  obtain ⟨n,hn,hread⟩ := (hsmall.and (carrierJetReading_eq_actualProbe_eventually S q T hT a r hr)).exists
  rw [hread]
  apply isolatedNativeJetCoefficient_eq_probe q T S.carrier hT a _ _ _ _ _ hn r hr
  intro x hx hdist
  by_contra hne
  have h := S.isolationRadius_le_dist a hx hne
  rw [Real.dist_eq] at h
  linarith

/-- Ordinary closed support forces every canonical discrete jet outside that
support to vanish, even if the larger discrete carrier contains the point. -/
theorem carrierJetReading_zero_outside_closed_support (S : LocallyFiniteCarrier) (q : ℕ)
    (T : HermiteScale (-(q:ℤ))) (hS : DistributionSupportedOn S.carrier (hermiteScaleDistribution q T))
    (C : Set ℝ) (hC : IsClosed C) (hT : DistributionSupportedOn C (hermiteScaleDistribution q T))
    (a : S.subtype) (ha : (a:ℝ) ∉ C) (r : ℕ) (hr : r ≤ 2*q) :
    carrierJetReading S (hermiteScaleDistribution q T) a r = 0 := by
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (hC.isOpen_compl.mem_nhds ha)
  obtain ⟨n,hn,hread⟩ := ((actualStage_jetRadius_eventually_le fixedProbeTemplate ε hε).and
    (carrierJetReading_eq_actualProbe_eventually S q T hS a r hr)).exists
  rw [hread]
  apply (supportedOn_iff_vanishesOn_compl C _).mp hT _ (fixedJetProbe_hasCompactSupport _ _ _ _)
  intro x hx
  apply hball
  rw [Metric.mem_ball,Real.dist_eq]
  have hd := fixedJetProbe_support (a:ℝ) _ _ r hx
  rw [Metric.mem_closedBall,Real.dist_eq] at hd
  have hpos := (actualStage fixedProbeTemplate n).jetRadius_pos
  linarith

/-- Compact-test annihilation extends to the whole Schwartz ideal by the actual
compact approximation, with no change to the distribution. -/
theorem atomicOnCarrier_of_compact_annihilation (L : LocallyFiniteCarrier) (U : TemperedDistribution ℝ ℂ)
    (hU : ∀ f : SchwartzMap ℝ ℂ, HasCompactSupport (f : ℝ → ℂ) → SchwartzVanishesOn L f → U f=0) :
    AtomicOnCarrier L U := by
  intro f hf
  have hz : ∀ N : ℕ, U (compactSchwartzApproximation N f)=0 := fun N =>
    hU _ (compactSchwartzApproximation_hasCompactSupport N f)
      (compactSchwartzApproximation_preserves_vanishing L N f hf)
  have hlim := (U.continuous.tendsto f).comp (compactSchwartzApproximation_tendsto f)
  have hzero : Tendsto (fun N : ℕ => U (compactSchwartzApproximation N f)) atTop (𝓝 0) := by
    simpa only [hz] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℂ)) atTop (𝓝 0))
  exact tendsto_nhds_unique hlim hzero

/-- No positive-order jets and no value coefficient off the actual carrier
imply whole value-only atomicity there. All sums are finite on compact tests. -/
theorem native_atomic_of_jet_conditions (S L : LocallyFiniteCarrier) (q : ℕ)
    (T : HermiteScale (-(q:ℤ))) (hT : DistributionSupportedOn S.carrier (hermiteScaleDistribution q T))
    (hpositive : ∀ a : S.subtype, ∀ r, 0 < r → r ≤ 2*q → carrierJetReading S (hermiteScaleDistribution q T) a r=0)
    (hoff : ∀ a : S.subtype, (a:ℝ) ∉ L.carrier → carrierJetReading S (hermiteScaleDistribution q T) a 0=0) :
    AtomicOnCarrier L (hermiteScaleDistribution q T) := by
  apply atomicOnCarrier_of_compact_annihilation
  intro f hf hfL
  obtain ⟨E,_,he⟩ := supportedOn_compact_jet_formula S q T hT f hf
  rw [he]
  apply Finset.sum_eq_zero
  intro a _
  apply Finset.sum_eq_zero
  intro r hr
  by_cases hr0 : r=0
  · subst r
    rw [iteratedDeriv_zero]
    by_cases ha : (a:ℝ) ∈ L.carrier
    · rw [hfL a ha,mul_zero]
    · rw [hoff a ha,zero_mul]
  · rw [hpositive a r (by omega) (by have := Finset.mem_range.mp hr; omega),zero_mul]

end
end MeyerGeneralProblem.Adaptive
