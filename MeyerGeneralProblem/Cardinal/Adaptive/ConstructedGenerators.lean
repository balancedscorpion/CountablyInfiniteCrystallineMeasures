module

public import MeyerGeneralProblem.Cardinal.Adaptive.HighOrderGapLines
public import MeyerGeneralProblem.Cardinal.Adaptive.SectorIndependentFamily

@[expose] public section

/-! # Actual reciprocal generators of the constructed carrier -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open Set
open scoped FourierTransform

/-- A fixed nonzero whole block source, chosen from the proved native construction. -/
def constructedBlockGenerator (i : ℕ+) : TemperedDistribution ℝ ℂ :=
  Classical.choose (exists_actualHighGapGenerator i (constructedGaps i) i.pos
    (actualPositiveGaps_pos fixedProbeTemplate i))

/-- The chosen block source retains all proved native and complete-line properties. -/
theorem constructedBlockGenerator_spec (i : ℕ+) :
    constructedBlockGenerator i ≠ 0 ∧
    constructedBlockGenerator i ∈ actualBlockCompleteSource i (constructedGaps i) i.pos
      (actualPositiveGaps_pos fixedProbeTemplate i) ∧
    constructedBlockGenerator i ∈ originalNativeDistributionSpace (18*i.val+4) ∧
    ∀ T ∈ actualBlockCompleteSource i (constructedGaps i) i.pos
      (actualPositiveGaps_pos fixedProbeTemplate i), ∃ c : ℂ, T=c • constructedBlockGenerator i :=
  Classical.choose_spec (exists_actualHighGapGenerator i (constructedGaps i) i.pos
    (actualPositiveGaps_pos fixedProbeTemplate i))

/-- The actual inverse dilation places each block in its paired reciprocal sectors. -/
def constructedGenerator (b : Label) : TemperedDistribution ℝ ℂ :=
  combDistributionDilation (labelScale constructedScales b)⁻¹
    (inv_ne_zero (labelScale_pos constructedScales constructedScales_good.1.1 b).ne')
    (constructedBlockGenerator b.1)

/-- Every actual reciprocal generator is nonzero. -/
theorem constructedGenerator_ne_zero (b : Label) : constructedGenerator b ≠ 0 := by
  intro hz
  apply (constructedBlockGenerator_spec b.1).1
  apply combDistributionDilation_injective (labelScale constructedScales b)⁻¹
    (inv_ne_zero (labelScale_pos constructedScales constructedScales_good.1.1 b).ne')
  simpa only [constructedGenerator, map_zero] using hz

/-- Each generator has its complete value-only physical record on the flipped sector. -/
theorem constructedGenerator_physical (b : Label) :
    AtomicOnCarrier (sectorCarrier constructedGaps constructedScales
      (actualPositiveGaps_pos fixedProbeTemplate) constructedScales_good.1.1 (b.1,b.2.flip))
      (constructedGenerator b) := by
  apply atomicOnCarrier_combDilation
    (blockCarrier b.1 (constructedGaps b.1) b.1.pos (actualPositiveGaps_pos fixedProbeTemplate b.1))
    _ _ _ _ _ (constructedBlockGenerator_spec b.1).2.1.1
  intro x hx
  change (labelScale constructedScales b)⁻¹*x ∈ sectorSet constructedGaps constructedScales (b.1,b.2.flip)
  rw [←physicalSectorSet_eq_flipped]
  exact ⟨x,hx,rfl⟩

/-- Fourier covariance carries the entire spectral record, including its Jacobian. -/
theorem constructedGenerator_spectral (b : Label) :
    AtomicOnCarrier (sectorCarrier constructedGaps constructedScales
      (actualPositiveGaps_pos fixedProbeTemplate) constructedScales_good.1.1 b)
      (𝓕 (constructedGenerator b)) := by
  unfold constructedGenerator
  rw [fourier_combDistributionDilation]
  have h := atomicOnCarrier_combDilation
    (blockCarrier b.1 (constructedGaps b.1) b.1.pos (actualPositiveGaps_pos fixedProbeTemplate b.1))
    (sectorCarrier constructedGaps constructedScales (actualPositiveGaps_pos fixedProbeTemplate)
      constructedScales_good.1.1 b)
    ((labelScale constructedScales b)⁻¹)⁻¹
    (inv_ne_zero (inv_ne_zero (labelScale_pos constructedScales constructedScales_good.1.1 b).ne'))
    (by intro x hx; exact ⟨x,hx,by simp⟩)
    (𝓕 (constructedBlockGenerator b.1)) (constructedBlockGenerator_spec b.1).2.1.2
  intro f hf
  simp only [smul_apply,h f hf,smul_zero]

/-- Both actual records lie on the single constructed carrier. -/
theorem constructedGenerator_mem_paired (b : Label) :
    constructedGenerator b ∈ pairedAtomicSource constructedCarrier constructedCarrier := by
  constructor
  · intro f hf
    apply constructedGenerator_physical b f
    intro x hx
    apply hf x
    rw [constructedCarrier_carrier]
    exact Set.mem_iUnion.mpr ⟨(b.1,b.2.flip),hx⟩
  · intro f hf
    apply constructedGenerator_spectral b f
    intro x hx
    apply hf x
    rw [constructedCarrier_carrier]
    exact Set.mem_iUnion.mpr ⟨b,hx⟩

/-- The reciprocal dilation preserves precisely the original admission order. -/
theorem constructedGenerator_native (b : Label) :
    constructedGenerator b ∈ originalNativeDistributionSpace (18*b.1.val+4) := by
  obtain ⟨U,hU⟩ := (constructedBlockGenerator_spec b.1).2.2.1
  have ha : (labelScale constructedScales b)⁻¹ ∈ Set.Icc (1/2:ℝ) 2 := by
    rw [←labelScale_flip]
    exact labelScale_mem_Icc constructedScales constructedScales_good.1.1 _
  refine ⟨nativeDilation (18*b.1.val+4) (labelScale constructedScales b)⁻¹ ha U,?_⟩
  change hermiteScaleDistribution _ _ = _
  rw [nativeDilation_realizes]
  exact congrArg (combDistributionDilation (labelScale constructedScales b)⁻¹
    (inv_ne_zero (labelScale_pos constructedScales constructedScales_good.1.1 b).ne')) hU

/-- All reciprocal generators are linearly independent as whole actual distributions. -/
theorem constructedGenerator_linearIndependent : LinearIndependent ℂ constructedGenerator :=
  actual_spectral_family_linearIndependent constructedSeparation constructedSeparation_pos
    constructedGaps constructedScales (actualPositiveGaps_pos fixedProbeTemplate)
    constructedScales_good.1.1 constructedSeparation_spec constructedGenerator
    constructedGenerator_spectral constructedGenerator_ne_zero

end
end MeyerGeneralProblem.Adaptive
