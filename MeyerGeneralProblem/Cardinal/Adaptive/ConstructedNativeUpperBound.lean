module

public import MeyerGeneralProblem.Cardinal.Adaptive.ConstructedFiniteExhaustion

@[expose] public section

/-! Actual singleton reduction used by the exhaustive generator proof. -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section

/-- The actual native singleton reduction, viewed as a full tempered distribution. -/
def constructedReducedPiece (p : ℕ) (b : Label) :
    HermiteScale (-(p:ℤ)) →L[ℂ] TemperedDistribution ℝ ℂ :=
  (hermiteScaleDistributionCLM (6*p)).comp
    (nativeBlockPiece constructedSeparation constructedSeparation_pos p constructedGaps
      constructedScales constructedScales_good.1.1 b)

/-- Every reduced actual piece lies in its complete original block line. -/
theorem constructedReducedPiece_mem (p : ℕ) (T : constructedNativeSource p) (b : Label) :
    constructedReducedPiece p b T ∈ actualBlockCompleteSource b.1 (constructedGaps b.1)
      b.1.pos (actualPositiveGaps_pos fixedProbeTemplate b.1) :=
  (constructedPiece_reduced_block p T T.property.1 T.property.2 b).1

end
end MeyerGeneralProblem.Adaptive
