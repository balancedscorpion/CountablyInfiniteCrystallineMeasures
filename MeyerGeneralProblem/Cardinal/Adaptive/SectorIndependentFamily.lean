module

public import MeyerGeneralProblem.Cardinal.Adaptive.ConstructedSourceRecovery
public import MeyerGeneralProblem.Cardinal.Adaptive.SingletonExhaustion
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
import all Mathlib.LinearAlgebra.LinearIndependent.Defs

@[expose] public section

/-! # Actual whole-source independence across distinct reciprocal sectors -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped FourierTransform

/-- The actual smooth selector acts as its literal membership scalar on a whole sector source. -/
theorem actualSelector_on_whole_sector (σ : ℝ) (hσ : 0 < σ)
    (R : ℕ+ → ℕ) (s : ℕ+ → ℝ) (hR : ∀ i, 1 ≤ R i) (hs : ∀ i, s i ∈ Set.Icc (1 : ℝ) 2)
    (hsep : ∀ b d : Label, b ≠ d → ∀ x ∈ sectorSet R s b,
      ∀ y ∈ sectorSet R s d, σ/(1+|x|+|y|)^6 ≤ |x-y|)
    (E : Set Label) (b : Label) (U : TemperedDistribution ℝ ℂ)
    (hU : AtomicOnCarrier (sectorCarrier R s hR hs b) U) :
    TemperedDistribution.smulLeftCLM ℂ (actualSectorSelector σ hσ R s E) U=
      (if b ∈ E then (1 : ℂ) else 0) •U := by
  classical
  rw [←TemperedDistribution.smulLeftCLM_const]
  exact atomic_multiplier_eq_of_eqOn _ U hU _ _
    (actualSectorSelector_hasTemperateGrowth σ hσ R s E) (Function.HasTemperateGrowth.const _)
    (fun x hx => actualSectorSelector_on_sector σ hσ R s hsep E b x hx)

/-- Any nonzero family of whole original sources on the distinct actual sectors is independent. -/
theorem actual_sector_family_linearIndependent (σ : ℝ) (hσ : 0 < σ)
    (R : ℕ+ → ℕ) (s : ℕ+ → ℝ) (hR : ∀ i, 1 ≤ R i) (hs : ∀ i, s i ∈ Set.Icc (1 : ℝ) 2)
    (hsep : ∀ b d : Label, b ≠ d → ∀ x ∈ sectorSet R s b,
      ∀ y ∈ sectorSet R s d, σ/(1+|x|+|y|)^6 ≤ |x-y|)
    (U : Label → TemperedDistribution ℝ ℂ)
    (hU : ∀ b, AtomicOnCarrier (sectorCarrier R s hR hs b) (U b))
    (hUne : ∀ b, U b ≠ 0) : LinearIndependent ℂ U := by
  classical
  rw [linearIndependent_iff']
  intro F c hzero b hb
  have he := congrArg (TemperedDistribution.smulLeftCLM ℂ (actualSectorSelector σ hσ R s {b})) hzero
  simp only [map_sum,map_smul,map_zero,actualSelector_on_whole_sector σ hσ R s hR hs hsep {b} _ _ (hU _),
    Set.mem_singleton_iff] at he
  have hp : ∑ i ∈ F, c i •((if i=b then (1 : ℂ) else 0) •U i)=c b •U b := by
    rw [Finset.sum_eq_single_of_mem b hb]
    · simp
    · intro i hi hib
      rw [if_neg hib]
      change c i • ((0 : ℂ) • U i) = 0
      rw [zero_smul ℂ (U i)]
      ext f
      change c i * (0 : ℂ) = 0
      exact mul_zero _
  rw [hp] at he
  exact (smul_eq_zero.mp he).resolve_right (hUne b)

/-- The same whole-source independence is visible in the actual spectral sectors. -/
theorem actual_spectral_family_linearIndependent (σ : ℝ) (hσ : 0 < σ)
    (R : ℕ+ → ℕ) (s : ℕ+ → ℝ) (hR : ∀ i, 1 ≤ R i) (hs : ∀ i, s i ∈ Set.Icc (1 : ℝ) 2)
    (hsep : ∀ b d : Label, b ≠ d → ∀ x ∈ sectorSet R s b,
      ∀ y ∈ sectorSet R s d, σ/(1+|x|+|y|)^6 ≤ |x-y|)
    (U : Label → TemperedDistribution ℝ ℂ)
    (hU : ∀ b, AtomicOnCarrier (sectorCarrier R s hR hs b) (𝓕 (U b)))
    (hUne : ∀ b, U b ≠ 0) : LinearIndependent ℂ U := by
  have hn (b : Label) : 𝓕 (U b) ≠ 0 := by
    intro hz
    apply hUne b
    have hv := congrArg (fun V : TemperedDistribution ℝ ℂ => 𝓕⁻ V) hz
    simpa using hv
  have hi := actual_sector_family_linearIndependent σ hσ R s hR hs hsep (fun b => 𝓕 (U b)) hU hn
  exact hi.of_comp (FourierTransform.fourierCLM ℂ (TemperedDistribution ℝ ℂ)).toLinearMap

end
end MeyerGeneralProblem.Adaptive
