module

public import MeyerGeneralProblem.Cardinal.Adaptive.ActualPolynomialSupport

@[expose] public section

/-! # Exact finite exhaustion once the excluded whole singleton pieces vanish -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open Set Filter
open scoped FourierTransform Topology

private theorem nativeDistribution_zero (q : ℕ) : hermiteScaleDistribution q 0 = 0 :=
  map_zero (hermiteScaleDistributionCLM q)

/-- Original isolated masses determine an entire atomic tempered distribution. -/
theorem atomic_eq_zero_of_isolation_eq_zero (L : LocallyFiniteCarrier)
    (U : TemperedDistribution ℝ ℂ) (hU : AtomicOnCarrier L U)
    (hzero : ∀ a : L.subtype, U (L.isolationSchwartz a)=0) : U=0 := by
  have hcompact (f : SchwartzMap ℝ ℂ) (hf : HasCompactSupport f) : U f=0 := by
    obtain ⟨E,_,he⟩ := atomicOnCarrier_isLocallyAtomicCoefficientFamily L U hU f hf
    rw [he]
    simp only [hzero,zero_mul,Finset.sum_const_zero]
  ext f
  have hlim := (U.continuous.tendsto f).comp (compactSchwartzApproximation_tendsto f)
  have hz : Tendsto (fun N : ℕ => U (compactSchwartzApproximation N f)) atTop (𝓝 0) := by
    simpa only [hcompact _ (compactSchwartzApproximation_hasCompactSupport _ _)] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℂ)) atTop (𝓝 0))
  exact tendsto_nhds_unique hlim hz

/-- Every temperate multiplier acts on the canonical isolation reading by its
literal value at the isolated point, without any compact support assumption on it. -/
theorem atomic_multiplier_isolation_reading (L : LocallyFiniteCarrier)
    (U : TemperedDistribution ℝ ℂ) (hU : AtomicOnCarrier L U)
    (g : ℝ → ℂ) (hg : g.HasTemperateGrowth) (a : L.subtype) :
    TemperedDistribution.smulLeftCLM ℂ g U (L.isolationSchwartz a) =
      g a * U (L.isolationSchwartz a) := by
  have hz := hU (SchwartzMap.smulLeftCLM ℂ g (L.isolationSchwartz a) -
    g a • L.isolationSchwartz a) (by
      intro x hx
      simp only [sub_apply,SchwartzMap.smulLeftCLM_apply_apply hg,smul_apply,smul_eq_mul]
      by_cases he : x=a
      · subst x
        simp only [sub_self]
      · rw [L.isolationSchwartz_of_mem_of_ne _ hx he]
        ring)
  simpa only [map_sub,map_smul,smul_eq_mul,sub_eq_zero,
    TemperedDistribution.smulLeftCLM_apply_apply] using hz

/-- If every singleton selected from E vanishes as a whole native source, the
actual E restriction itself vanishes. No infinite sum of source pieces is formed. -/
theorem nativeSourcePiece_eq_zero_of_singletons (σ : ℝ) (hσ : 0 < σ) (p : ℕ)
    (R : ℕ+ → ℕ) (s : ℕ+ → ℝ)
    (hsep : ∀ b d : Label, b ≠ d → ∀ x ∈ sectorSet R s b,
      ∀ y ∈ sectorSet R s d, σ/(1+|x|+|y|)^6 ≤ |x-y|)
    (L : LocallyFiniteCarrier) (hL : L.carrier ⊆ carrierSet R s)
    (T : HermiteScale (-(p:ℤ))) (hT : AtomicOnCarrier L (𝓕 (hermiteScaleDistribution p T)))
    (E : Set Label) (hzero : ∀ b ∈ E, nativeSourcePiece σ hσ p R s {b} T=0) :
    nativeSourcePiece σ hσ p R s E T=0 := by
  let U := 𝓕 (hermiteScaleDistribution p T)
  let g := actualSectorSelector σ hσ R s E
  have hselected : AtomicOnCarrier L (TemperedDistribution.smulLeftCLM ℂ g U) := by
    intro f hf
    apply hT
    intro x hx
    change SchwartzMap.smulLeftCLM ℂ g f x=0
    rw [SchwartzMap.smulLeftCLM_apply_apply (actualSectorSelector_hasTemperateGrowth σ hσ R s E)]
    rw [hf x hx,smul_zero]
  have hwhole : TemperedDistribution.smulLeftCLM ℂ g U=0 := by
    apply atomic_eq_zero_of_isolation_eq_zero L _ hselected
    intro a
    rw [atomic_multiplier_isolation_reading L U hT g
      (actualSectorSelector_hasTemperateGrowth σ hσ R s E)]
    obtain ⟨b,hb⟩ := mem_iUnion.mp (hL a.property)
    change actualSectorSelector σ hσ R s E a * U (L.isolationSchwartz a)=0
    rw [actualSectorSelector_on_sector σ hσ R s hsep E b a hb]
    by_cases he : b ∈ E
    · rw [ite_eq_left he,one_mul]
      have hh := fourier_nativeSourcePiece σ hσ p R s {b} T
      rw [hzero b he,nativeDistribution_zero,FourierTransform.fourier_zero] at hh
      have hv := congrArg (fun W : TemperedDistribution ℝ ℂ => W (L.isolationSchwartz a)) hh
      rw [atomic_multiplier_isolation_reading L U hT _
        (actualSectorSelector_hasTemperateGrowth σ hσ R s {b}),
        actualSectorSelector_on_sector σ hσ R s hsep {b} b a hb] at hv
      simpa using hv.symm
    · rw [ite_eq_right he,zero_mul]
  apply hermiteScaleDistribution_injective (6*p)
  rw [nativeSourcePiece_realizes]
  change 𝓕⁻ (TemperedDistribution.smulLeftCLM ℂ g U) = hermiteScaleDistribution (6*p) 0
  rw [hwhole]
  simp only [FourierTransform.fourierInv_zero,nativeDistribution_zero]

/-- Vanishing of every omitted singleton closes the exact finite algebraic
source identity. The future remainder is proved zero by its isolated masses. -/
theorem nativeSourcePiece_finite_exhaustion (σ : ℝ) (hσ : 0 < σ) (p : ℕ)
    (R : ℕ+ → ℕ) (s : ℕ+ → ℝ)
    (hsep : ∀ b d : Label, b ≠ d → ∀ x ∈ sectorSet R s b,
      ∀ y ∈ sectorSet R s d, σ/(1+|x|+|y|)^6 ≤ |x-y|)
    (L : LocallyFiniteCarrier) (hL : L.carrier ⊆ carrierSet R s)
    (T : HermiteScale (-(p:ℤ))) (hT : AtomicOnCarrier L (𝓕 (hermiteScaleDistribution p T)))
    (F : Finset Label) (hzero : ∀ b ∉ F, nativeSourcePiece σ hσ p R s {b} T=0) :
    (∑ b ∈ F, hermiteScaleDistribution (6*p) (nativeSourcePiece σ hσ p R s {b} T)) =
      hermiteScaleDistribution p T := by
  have h := nativeSourcePiece_finite_split σ hσ p R s hsep L hL T hT F
  have hz := nativeSourcePiece_eq_zero_of_singletons σ hσ p R s hsep L hL T hT
    (↑F : Set Label)ᶜ hzero
  rw [hz] at h
  simpa only [nativeDistribution_zero,add_zero] using h

end
end MeyerGeneralProblem.Adaptive
