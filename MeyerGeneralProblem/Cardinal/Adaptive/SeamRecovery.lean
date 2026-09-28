module

public import MeyerGeneralProblem.Cardinal.Adaptive.PhysicalIsolation
public import MeyerGeneralProblem.Cardinal.Adaptive.DistributionLocality

@[expose] public section

/-! # Recovering a locally finite support while retaining the full seam lattice -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open scoped FourierTransform

/-- Removing the forbidden isolated phases leaves the actual locally finite
carrier and the complete seam lattice. No seam derivative has been discarded. -/
theorem actualSourcePiece_supportedOn_with_seams (s : ℕ+ → ℝ)
    (hs : ActualGoodScale fixedProbeTemplate s) (σ : ℝ) (hσ : 0 < σ) (p : ℕ)
    (hsep : ∀ b d : Label, b ≠ d → ∀ x ∈ sectorSet constructedGaps s b,
      ∀ y ∈ sectorSet constructedGaps s d, σ/(1+|x|+|y|)^6 ≤ |x-y|)
    (L : LocallyFiniteCarrier) (hL : L.carrier ⊆ carrierSet constructedGaps s)
    (T : HermiteScale (-(p:ℤ))) (hTphys : AtomicOnCarrier L (hermiteScaleDistribution p T))
    (hTspec : AtomicOnCarrier L (𝓕 (hermiteScaleDistribution p T)))
    (hphysical : ∀ d, DistributionSupportedOn (physicalPeriodicSet constructedGaps s d)
      (hermiteScaleDistribution (6*p) (nativeSourcePiece σ hσ p constructedGaps s {d} T)))
    (b : Label) :
    DistributionSupportedOn (carrierWithSeams L (labelScale s b) (labelScale_pos s hs.1.1 b)).carrier
      (hermiteScaleDistribution (6*p) (nativeSourcePiece σ hσ p constructedGaps s {b} T)) := by
  apply supportedOn_of_local_vanishing
  intro y hy
  have hyL : y ∉ L.carrier := fun h => hy (Or.inl h)
  have hyseam : ∀ n : ℤ, y ≠ ((n:ℝ)+1/2)/(labelScale s b) := by
    intro n hn
    exact hy (Or.inr ⟨n,hn.symm⟩)
  by_cases hyC : y ∈ physicalPeriodicSet constructedGaps s b
  · obtain ⟨δ,hδ,hiso⟩ := physicalPeriodicSet_isolation_radius constructedGaps s
      (actualPositiveGaps_pos fixedProbeTemplate) hs.1.1 b y hyC hyseam
    refine ⟨Metric.ball y (δ/4),Metric.isOpen_ball,Metric.mem_ball_self (by positivity),?_⟩
    apply isolated_native_vanishesOn (6*p) _ _ (hphysical b) y δ hδ hiso
    intro r hr
    rw [actualSourcePiece_isolated_jet_eq_mass s hs σ hσ p hsep L hL T hTphys hTspec
      hphysical b y δ hδ hyC _ (hphysical b) hiso r (by omega)]
    simp only [originalPointMass,dite_eq_right hyL,ite_self]
  · exact ⟨(physicalPeriodicSet constructedGaps s b)ᶜ,
      (physicalPeriodicSet_isClosed constructedGaps s (actualPositiveGaps_pos fixedProbeTemplate) hs.1.1 b).isOpen_compl,
      hyC,(supportedOn_iff_vanishesOn_compl _ _).mp (hphysical b)⟩

end
end MeyerGeneralProblem.Adaptive
