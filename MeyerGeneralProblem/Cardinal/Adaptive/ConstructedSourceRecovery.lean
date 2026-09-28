module

public import MeyerGeneralProblem.Cardinal.Adaptive.SinglePhaseLift
public import MeyerGeneralProblem.Cardinal.Adaptive.ActualPolynomialSupport
public import MeyerGeneralProblem.Cardinal.Adaptive.ActualBlockReduction

@[expose] public section

/-! # Complete physical and spectral recovery for the single constructed carrier -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open Set
open scoped FourierTransform

/-- Full physical support of every actual whole native restriction, derived
from both original atomic records and the same profile-consistent stage sequence. -/
theorem actualSourcePiece_physical_support (ψ : SchwartzMap ℝ ℂ)
    (hψone : ψ 0 = 1) (hψzero : ∀ x, 2 ≤ |x| → ψ x = 0)
    (s : ℕ+ → ℝ) (hs : ActualGoodScale ψ s) (σ : ℝ) (hσ : 0 < σ) (p : ℕ)
    (hsep : ∀ b d : Label, b ≠ d → ∀ x ∈ sectorSet (actualPositiveGaps ψ) s b,
      ∀ y ∈ sectorSet (actualPositiveGaps ψ) s d, σ/(1+|x|+|y|)^6 ≤ |x-y|)
    (L : LocallyFiniteCarrier) (hL : L.carrier ⊆ carrierSet (actualPositiveGaps ψ) s)
    (T : HermiteScale (-(p:ℤ))) (hTphys : AtomicOnCarrier L (hermiteScaleDistribution p T))
    (hTspec : AtomicOnCarrier L (𝓕 (hermiteScaleDistribution p T))) :
    ∀ b, DistributionSupportedOn (physicalPeriodicSet (actualPositiveGaps ψ) s b)
      (hermiteScaleDistribution (6*p) (nativeSourcePiece σ hσ p (actualPositiveGaps ψ) s {b} T)) :=
  actualSourcePiece_supportedOn_of_antidifference ψ s hs σ hσ p hsep L hL T hTphys hTspec
    (actualSourcePiece_local_antidifference ψ hψone hψzero σ hσ p s hs hsep L L hL hL T hTphys hTspec)

/-- Whole value-only physical recovery for the final profile, with no supplied
local lift, support, derivative, or coefficient certificate. -/
theorem actualSourcePiece_complete_physical_atomic (s : ℕ+ → ℝ)
    (hs : ActualGoodScale fixedProbeTemplate s) (σ : ℝ) (hσ : 0 < σ) (p : ℕ)
    (hsep : ∀ b d : Label, b ≠ d → ∀ x ∈ sectorSet constructedGaps s b,
      ∀ y ∈ sectorSet constructedGaps s d, σ/(1+|x|+|y|)^6 ≤ |x-y|)
    (L : LocallyFiniteCarrier) (hL : L.carrier ⊆ carrierSet constructedGaps s)
    (T : HermiteScale (-(p:ℤ))) (hTphys : AtomicOnCarrier L (hermiteScaleDistribution p T))
    (hTspec : AtomicOnCarrier L (𝓕 (hermiteScaleDistribution p T))) (b : Label) :
    AtomicOnCarrier (sectorCarrier constructedGaps s (actualPositiveGaps_pos fixedProbeTemplate)
      hs.1.1 (b.1,b.2.flip))
      (hermiteScaleDistribution (6*p) (nativeSourcePiece σ hσ p constructedGaps s {b} T)) :=
  actualSourcePiece_physical_atomic s hs σ hσ p hsep L hL T hTphys hTspec
    (actualSourcePiece_physical_support fixedProbeTemplate (fixedProbeTemplate_eq_one 0 (by norm_num))
      (fun x hx => fixedProbeTemplate_eq_zero x (by linarith)) s hs σ hσ p hsep L hL T hTphys hTspec) b

/-- The constructed tuple supplies a single separation constant, fixed before
all input orders, source distributions and labels. -/
def constructedSeparation : ℝ := Classical.choose constructedScales_good.1.2.2

/-- Positivity of the fixed constructed separation constant. -/
theorem constructedSeparation_pos : 0 < constructedSeparation :=
  (Classical.choose_spec constructedScales_good.1.2.2).1

/-- The fixed constant separates all actual atoms from different reciprocal labels. -/
theorem constructedSeparation_spec : ∀ b d : Label, b ≠ d →
    ∀ x ∈ sectorSet constructedGaps constructedScales b,
    ∀ y ∈ sectorSet constructedGaps constructedScales d,
      constructedSeparation/(1+|x|+|y|)^6 ≤ |x-y| :=
  (Classical.choose_spec constructedScales_good.1.2.2).2

/-- The actual singleton native restriction for the fixed final carrier. -/
def constructedPiece (p : ℕ) (b : Label) :
    HermiteScale (-(p:ℤ)) →L[ℂ] HermiteScale (-((6*p:ℕ):ℤ)) :=
  nativeSourcePiece constructedSeparation constructedSeparation_pos p constructedGaps constructedScales {b}

/-- The fixed source's whole physical record is recovered on exactly the paired block. -/
theorem constructedPiece_physical_atomic (p : ℕ) (T : HermiteScale (-(p:ℤ)))
    (hTphys : AtomicOnCarrier constructedCarrier (hermiteScaleDistribution p T))
    (hTspec : AtomicOnCarrier constructedCarrier (𝓕 (hermiteScaleDistribution p T))) (b : Label) :
    AtomicOnCarrier (sectorCarrier constructedGaps constructedScales (actualPositiveGaps_pos fixedProbeTemplate)
      constructedScales_good.1.1 (b.1,b.2.flip)) (hermiteScaleDistribution (6*p) (constructedPiece p b T)) :=
  actualSourcePiece_complete_physical_atomic constructedScales constructedScales_good
    constructedSeparation constructedSeparation_pos p constructedSeparation_spec constructedCarrier
    constructedCarrier_carrier.le T hTphys hTspec b

/-- The corresponding spectral record is value-only on its literal selected block. -/
theorem constructedPiece_spectral_atomic (p : ℕ) (T : HermiteScale (-(p:ℤ)))
    (hTspec : AtomicOnCarrier constructedCarrier (𝓕 (hermiteScaleDistribution p T))) (b : Label) :
    AtomicOnCarrier (sectorCarrier constructedGaps constructedScales (actualPositiveGaps_pos fixedProbeTemplate)
      constructedScales_good.1.1 b) (𝓕 (hermiteScaleDistribution (6*p) (constructedPiece p b T))) :=
  actualSourcePiece_spectral_sector constructedSeparation constructedSeparation_pos p constructedGaps
    constructedScales (actualPositiveGaps_pos fixedProbeTemplate) constructedScales_good.1.1
    constructedSeparation_spec constructedCarrier constructedCarrier_carrier.le T hTspec b

/-- Every recovered singleton of every native source on the fixed carrier belongs,
after the exact dilation, to the complete original native block space at order6p. -/
theorem constructedPiece_reduced_block (p : ℕ) (T : HermiteScale (-(p:ℤ)))
    (hTphys : AtomicOnCarrier constructedCarrier (hermiteScaleDistribution p T))
    (hTspec : AtomicOnCarrier constructedCarrier (𝓕 (hermiteScaleDistribution p T))) (b : Label) :
    hermiteScaleDistribution (6*p)
      (nativeBlockPiece constructedSeparation constructedSeparation_pos p constructedGaps
        constructedScales constructedScales_good.1.1 b T) ∈
      actualBlockNativeSource b.1 (constructedGaps b.1) b.1.pos
        (actualPositiveGaps_pos fixedProbeTemplate b.1) (6*p) :=
  nativeBlockPiece_mem_actualBlock constructedScales constructedScales_good constructedSeparation
    constructedSeparation_pos p constructedSeparation_spec constructedCarrier
    constructedCarrier_carrier.le T hTphys hTspec
    (actualSourcePiece_physical_support fixedProbeTemplate (fixedProbeTemplate_eq_one 0 (by norm_num))
      (fun x hx => fixedProbeTemplate_eq_zero x (by linarith)) constructedScales constructedScales_good
      constructedSeparation constructedSeparation_pos p constructedSeparation_spec constructedCarrier
      constructedCarrier_carrier.le T hTphys hTspec) b

end
end MeyerGeneralProblem.Adaptive
