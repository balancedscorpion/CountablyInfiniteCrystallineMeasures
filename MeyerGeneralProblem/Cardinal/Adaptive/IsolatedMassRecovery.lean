module

public import MeyerGeneralProblem.Cardinal.Adaptive.AtomicProbeRecovery

@[expose] public section

/-! # Exact isolated mass recovery from the same deterministic stage probes -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open Filter
open scoped Topology FourierTransform

/-- Once physical closure support is proved, every fixed isolated local jet of
an actual selected piece equals the original value-only source mass. The support
set used for local isolation may be smaller than the periodic closure; this also
allows the later finite-cell seam reduction. -/
theorem actualSourcePiece_isolated_jet_eq_mass (s : ℕ+ → ℝ)
    (hs : ActualGoodScale fixedProbeTemplate s) (σ : ℝ) (hσ : 0 < σ) (p : ℕ)
    (hsep : ∀ b d : Label, b ≠ d → ∀ x ∈ sectorSet constructedGaps s b,
      ∀ y ∈ sectorSet constructedGaps s d, σ/(1+|x|+|y|)^6 ≤ |x-y|)
    (L : LocallyFiniteCarrier) (hL : L.carrier ⊆ carrierSet constructedGaps s)
    (T : HermiteScale (-(p:ℤ))) (hTphys : AtomicOnCarrier L (hermiteScaleDistribution p T))
    (hTspec : AtomicOnCarrier L (𝓕 (hermiteScaleDistribution p T)))
    (hphysical : ∀ d, DistributionSupportedOn (physicalPeriodicSet constructedGaps s d)
      (hermiteScaleDistribution (6*p) (nativeSourcePiece σ hσ p constructedGaps s {d} T)))
    (b : Label) (y δ : ℝ) (hδ : 0 < δ) (hy : y ∈ physicalPeriodicSet constructedGaps s b)
    (D : Set ℝ) (hD : DistributionSupportedOn D
      (hermiteScaleDistribution (6*p) (nativeSourcePiece σ hσ p constructedGaps s {b} T)))
    (hiso : ∀ x ∈ D, |x-y| < δ → x=y) (r : ℕ) (hr : r ≤ 12*p) :
    isolatedNativeJetCoefficient (6*p) (nativeSourcePiece σ hσ p constructedGaps s {b} T) y δ hδ r =
      if r=0 then originalPointMass L (hermiteScaleDistribution p T) y else 0 := by
  obtain ⟨B,hB,hbound⟩ := exists_nativeSourcePiece_norm_bound σ hσ p
  apply eq_of_eventual_stage_errors _ _ (B*‖T‖)
  filter_upwards [eventually_ge_atTop p,eventually_ge_atTop b.1.val,
    eventually_ge_atTop (⌈|y|⌉₊),
    actualStage_jetRadius_eventually_le fixedProbeTemplate (δ/2) (by positivity),
    atomic_actualStage_probe_eventually L (hermiteScaleDistribution p T) hTphys y r]
    with n hnp hnb hny hsmall hatomic
  have hp : p ≤ n+1 := by omega
  have hb : b ∈ finitePrefixLabels (n+1) := (mem_finitePrefixLabels_iff _ _).mpr (by omega)
  have hywin : |y| ≤ (n+1:ℝ) := by
    have hn : (⌈|y|⌉₊:ℝ) ≤ n := by exact_mod_cast hny
    have hyceil := Nat.le_ceil |y|
    linarith
  have he := isolatedNativeJetCoefficient_eq_probe (6*p)
    (nativeSourcePiece σ hσ p constructedGaps s {b} T) D hD y δ hδ hiso
    (actualStage fixedProbeTemplate n).jetRadius (actualStage fixedProbeTemplate n).jetRadius_pos
    hsmall r (by omega)
  rw [← he,← hatomic]
  have herror := actualSourcePiece_stage_probe_error s hs σ hσ p n hp hsep L hL T hTspec
    (fun d _ => hphysical d) b hb y hy hywin r hr
  exact herror.trans (by
    have hnorm := hbound constructedGaps s (↑(finitePrefixLabels (n+1)) : Set Label)ᶜ T
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hnorm
      (by positivity : (0:ℝ) ≤ 2^(-((n+1:ℕ):ℤ))))

/-- Fixed local jet coefficients give an actual value-only formula on the whole
isolation neighborhood after every positive-order coefficient vanishes. -/
theorem isolated_native_value_action (q : ℕ) (T : HermiteScale (-(q:ℤ)))
    (C : Set ℝ) (hT : DistributionSupportedOn C (hermiteScaleDistribution q T))
    (a δ : ℝ) (hδ : 0 < δ) (hiso : ∀ x ∈ C, |x-a| < δ → x=a)
    (m : ℂ) (hc : ∀ r ≤ 2*q, isolatedNativeJetCoefficient q T a δ hδ r = if r=0 then m else 0)
    (f : SchwartzMap ℝ ℂ) (hf : HasCompactSupport (f : ℝ → ℂ))
    (hs : ∀ x ∈ tsupport f, |x-a| ≤ δ/4) :
    hermiteScaleDistribution q T f = m*f a := by
  rw [isolated_native_jet_formula q T C hT a δ hδ hiso f hf hs]
  have he : (∑ r ∈ Finset.range (2*q+1),
      isolatedNativeJetCoefficient q T a δ hδ r * iteratedDeriv r (f : ℝ → ℂ) a) =
      ∑ r ∈ Finset.range (2*q+1), (if r=0 then m else 0) * iteratedDeriv r (f : ℝ → ℂ) a := by
    apply Finset.sum_congr rfl
    intro r hr
    rw [hc r (by have := Finset.mem_range.mp hr; omega)]
  rw [he]
  simp

/-- Zero local jet data yields whole-distribution vanishing on an actual open
neighborhood, suitable for compact-test locality and support removal. -/
theorem isolated_native_vanishesOn (q : ℕ) (T : HermiteScale (-(q:ℤ)))
    (C : Set ℝ) (hT : DistributionSupportedOn C (hermiteScaleDistribution q T))
    (a δ : ℝ) (hδ : 0 < δ) (hiso : ∀ x ∈ C, |x-a| < δ → x=a)
    (hc : ∀ r ≤ 2*q, isolatedNativeJetCoefficient q T a δ hδ r = 0) :
    DistributionVanishesOn (Metric.ball a (δ/4)) (hermiteScaleDistribution q T) := by
  intro f hf hs
  rw [isolated_native_value_action q T C hT a δ hδ hiso 0
    (fun r hr => by rw [hc r hr]; simp) f hf (by
      intro x hx
      exact (show |x-a| < δ/4 by simpa only [Metric.mem_ball,Real.dist_eq] using hs hx).le)]
  exact zero_mul _

end
end MeyerGeneralProblem.Adaptive
