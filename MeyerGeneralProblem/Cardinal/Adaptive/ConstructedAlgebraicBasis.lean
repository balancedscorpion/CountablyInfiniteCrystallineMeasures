module

public import MeyerGeneralProblem.Cardinal.Adaptive.ConstructedNativeUpperBound
public import MeyerGeneralProblem.Cardinal.Adaptive.ConstructedGenerators
public import MeyerGeneralProblem.Cardinal.Adaptive.IntrinsicNativeRank
public import Mathlib.LinearAlgebra.Dimension.Constructions
import all Mathlib.LinearAlgebra.Dimension.Constructions

@[expose] public section

/-! The actual constructed reciprocal family is a Hamel basis of the complete Meyer space. -/
noncomputable section
namespace MeyerGeneralProblem.Adaptive

/-- Every actual recovered singleton lies on its actual reciprocal generator line. -/
theorem constructedPiece_eq_smul_generator (p : ℕ) (T : constructedNativeSource p) (b : Label) :
    ∃ c : ℂ, hermiteScaleDistribution (6*p) (constructedPiece p b T)=c •constructedGenerator b := by
  obtain ⟨c,hc⟩ := (constructedBlockGenerator_spec b.1).2.2.2
    (constructedReducedPiece p b T) (constructedReducedPiece_mem p T b)
  have he : constructedReducedPiece p b T=
      combDistributionDilation (labelScale constructedScales b)
        (labelScale_pos constructedScales constructedScales_good.1.1 b).ne'
        (hermiteScaleDistribution (6*p) (constructedPiece p b T)) := by
    simp only [constructedReducedPiece,ContinuousLinearMap.comp_apply,nativeBlockPiece,
      hermiteScaleDistributionCLM_apply,nativeDilation_realizes,constructedPiece]
  rw [he] at hc
  have hh := congrArg (combDistributionDilation (labelScale constructedScales b)⁻¹
    (inv_ne_zero (labelScale_pos constructedScales constructedScales_good.1.1 b).ne')) hc
  rw [combDistributionDilation_inv_cancel,map_smul] at hh
  exact ⟨c,hh⟩

/-- Complete original-native exhaustion is a finite algebraic span statement. -/
theorem constructedNativeSource_mem_generator_span (p : ℕ) (hp : 1 ≤ p) (T : constructedNativeSource p) :
    hermiteScaleDistribution p T ∈ Submodule.span ℂ (Set.range constructedGenerator) := by
  rw [←constructedSource_finite_exhaustion p hp T T.property]
  apply Submodule.sum_mem
  intro b hb
  obtain ⟨c,hc⟩ := constructedPiece_eq_smul_generator p T b
  rw [hc]
  exact Submodule.smul_mem _ c (Submodule.subset_span ⟨b,rfl⟩)

/-- Every whole paired source is a finite combination of the actual generators.
Native representation is obtained from the complete intrinsic exhaustion theorem. -/
theorem constructedPaired_mem_generator_span (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ pairedAtomicSource constructedCarrier constructedCarrier) :
    T ∈ Submodule.span ℂ (Set.range constructedGenerator) := by
  have hM : T ∈ DistributionalMeyerSpace constructedCarrier := by
    rwa [←pairedAtomicSource_eq_distributionalMeyerSpace]
  obtain ⟨p,hp,U,hU,he⟩ := exists_fixedOrderMeyerLayer_representation constructedCarrier T hM
  have hn : U ∈ constructedNativeSource p := by
    change hermiteScaleDistribution p U ∈ pairedAtomicSource constructedCarrier constructedCarrier
    rwa [he]
  rw [←he]
  exact constructedNativeSource_mem_generator_span p hp ⟨U,hn⟩

/-- Exact whole-space equality with the finite algebraic span of actual reciprocal sources. -/
theorem constructedGenerator_span_eq_paired :
    Submodule.span ℂ (Set.range constructedGenerator)=pairedAtomicSource constructedCarrier constructedCarrier := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨b,rfl⟩
    exact constructedGenerator_mem_paired b
  · exact constructedPaired_mem_generator_span

/-- The independent locally atomic definition gives the same complete algebraic span. -/
theorem constructedGenerator_span_eq_meyer :
    Submodule.span ℂ (Set.range constructedGenerator)=DistributionalMeyerSpace constructedCarrier := by
  rw [constructedGenerator_span_eq_paired,pairedAtomicSource_eq_distributionalMeyerSpace]

/-- Genuine finite generator synthesis is a linear equivalence onto the COMPLETE
Meyer space. Its domain is finitely supported reciprocal-label coefficients. -/
def constructedGeneratorSynthesisEquiv :
    (Label →₀ ℂ) ≃ₗ[ℂ] DistributionalMeyerSpace constructedCarrier :=
  constructedGenerator_linearIndependent.linearCombinationEquiv.trans
    (LinearEquiv.ofEq _ _ constructedGenerator_span_eq_meyer)

/-- The synthesis equivalence has precisely the prescribed literal finite source sum. -/
theorem constructedGeneratorSynthesisEquiv_apply (c : Label →₀ ℂ) :
    (constructedGeneratorSynthesisEquiv c : TemperedDistribution ℝ ℂ)=
      Finsupp.linearCombination ℂ constructedGenerator c := rfl

/-- The actual synthesis linear map, retaining the finite coefficient interpretation. -/
def constructedGeneratorSynthesis :
    (Label →₀ ℂ) →ₗ[ℂ] DistributionalMeyerSpace constructedCarrier :=
  constructedGeneratorSynthesisEquiv.toLinearMap

/-- Actual generator synthesis loses no coefficients and reaches every whole Meyer source. -/
theorem constructedGeneratorSynthesis_bijective : Function.Bijective constructedGeneratorSynthesis :=
  constructedGeneratorSynthesisEquiv.bijective

/-- Literal finite generator synthesis has countable rank,
with its actual reciprocal-label cardinality and universe conversion explicit. -/
theorem constructedMeyerRank_eq_aleph0_via_synthesis :
    Module.rank ℂ (DistributionalMeyerSpace constructedCarrier)=Cardinal.aleph0 := by
  let : Nonempty ReciprocalSign := ⟨.forward⟩
  rw [←constructedGeneratorSynthesisEquiv.rank_eq,rank_finsupp_self']
  exact Cardinal.mk_eq_aleph0 Label

end MeyerGeneralProblem.Adaptive
