module

public import MeyerGeneralProblem.Cardinal.Adaptive.ConstructedSourceRecovery
public import MeyerGeneralProblem.Cardinal.Adaptive.SingletonExhaustion
public import MeyerGeneralProblem.Cardinal.Adaptive.HighOrderGapLines

@[expose] public section

/-! Exact finite exhaustion of every original native source on the constructed carrier. -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open scoped FourierTransform

/-- The actual paired source space pulled back to its original native order. -/
def constructedNativeSource (p : ℕ) : Submodule ℂ (HermiteScale (-(p:ℤ))) :=
  (pairedAtomicSource constructedCarrier constructedCarrier).comap
    (hermiteScaleDistributionCLM p).toLinearMap

/-- Membership retains exactly the two whole original atomic records. -/
theorem mem_constructedNativeSource (p : ℕ) (T : HermiteScale (-(p:ℤ))) :
    T ∈ constructedNativeSource p ↔
      AtomicOnCarrier constructedCarrier (hermiteScaleDistribution p T) ∧
      AtomicOnCarrier constructedCarrier (𝓕 (hermiteScaleDistribution p T)) := Iff.rfl

/-- Every excluded high-index singleton is zero as a whole original native piece. -/
theorem constructedPiece_eq_zero_of_large_index (p : ℕ) (hp : 1 ≤ p)
    (T : HermiteScale (-(p:ℤ))) (hT : T ∈ constructedNativeSource p)
    (b : Label) (hb : 6*p ≤ b.1.val) : constructedPiece p b T=0 := by
  have h := constructedPiece_reduced_block p T hT.1 hT.2 b
  rw [actualBlockNativeSource_eq_bot b.1 (constructedGaps b.1) (6*p) b.1.pos
    (actualPositiveGaps_pos fixedProbeTemplate b.1) (by omega) hb] at h
  have hn : nativeBlockPiece constructedSeparation constructedSeparation_pos p constructedGaps
      constructedScales constructedScales_good.1.1 b T=0 := by
    apply hermiteScaleDistribution_injective (6*p)
    simpa only [Submodule.mem_bot,←hermiteScaleDistributionCLM_apply,map_zero] using h
  exact (nativeBlockPiece_eq_zero_iff constructedSeparation constructedSeparation_pos p
    constructedGaps constructedScales constructedScales_good.1.1 b T).mp hn

/-- Every source is literally the finite sum of its singleton pieces with
positive block index below6p. No infinite source sum or convergence certificate is used. -/
theorem constructedSource_finite_exhaustion (p : ℕ) (hp : 1 ≤ p)
    (T : HermiteScale (-(p:ℤ))) (hT : T ∈ constructedNativeSource p) :
    (∑ b ∈ finitePrefixLabels (6*p-1), hermiteScaleDistribution (6*p) (constructedPiece p b T))=
      hermiteScaleDistribution p T := by
  apply nativeSourcePiece_finite_exhaustion constructedSeparation constructedSeparation_pos p
    constructedGaps constructedScales constructedSeparation_spec constructedCarrier constructedCarrier_carrier.le T hT.2
  intro b hb
  apply constructedPiece_eq_zero_of_large_index p hp T hT b
  have hn := not_le.mp (fun h => hb ((mem_finitePrefixLabels_iff _ _).mpr h))
  omega

/-- The exact equivalent finite index is one of the two reciprocal signs at
one of the first6p-1 positive block indices. -/
theorem constructedSource_finite_exhaustion_indexed (p : ℕ) (hp : 1 ≤ p)
    (T : HermiteScale (-(p:ℤ))) (hT : T ∈ constructedNativeSource p) :
    (∑ b : Fin (6*p-1) × ReciprocalSign,
      hermiteScaleDistribution (6*p) (constructedPiece p (prefixScaleIndex b.1,b.2) T))=
      hermiteScaleDistribution p T := by
  simpa only [sum_finitePrefixLabels] using constructedSource_finite_exhaustion p hp T hT

end
end MeyerGeneralProblem.Adaptive
