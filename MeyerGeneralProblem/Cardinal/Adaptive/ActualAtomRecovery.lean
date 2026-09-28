module

public import MeyerGeneralProblem.Cardinal.Adaptive.SeamRecovery
public import MeyerGeneralProblem.Cardinal.Adaptive.NativeJetProbeRecovery

@[expose] public section

/-! # Complete actual atom recovery, including removal of seam jets -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open scoped FourierTransform

/-- After the independently proved physical-closure support step, the actual
selected source is value-only on precisely the intersection of its closure and
the original carrier. Every seam derivative and every forbidden atom is removed
using the same preselected stage probes and original native bounds. -/
theorem actualSourcePiece_atomic_on_actual_intersection (s : ℕ+ → ℝ)
    (hs : ActualGoodScale fixedProbeTemplate s) (σ : ℝ) (hσ : 0 < σ) (p : ℕ)
    (hsep : ∀ b d : Label, b ≠ d → ∀ x ∈ sectorSet constructedGaps s b,
      ∀ y ∈ sectorSet constructedGaps s d, σ/(1+|x|+|y|)^6 ≤ |x-y|)
    (L : LocallyFiniteCarrier) (hL : L.carrier ⊆ carrierSet constructedGaps s)
    (T : HermiteScale (-(p:ℤ))) (hTphys : AtomicOnCarrier L (hermiteScaleDistribution p T))
    (hTspec : AtomicOnCarrier L (𝓕 (hermiteScaleDistribution p T)))
    (hphysical : ∀ d, DistributionSupportedOn (physicalPeriodicSet constructedGaps s d)
      (hermiteScaleDistribution (6*p) (nativeSourcePiece σ hσ p constructedGaps s {d} T)))
    (b : Label) :
    AtomicOnCarrier (L.restrict (L.carrier ∩ physicalPeriodicSet constructedGaps s b) Set.inter_subset_left)
      (hermiteScaleDistribution (6*p) (nativeSourcePiece σ hσ p constructedGaps s {b} T)) := by
  let S := carrierWithSeams L (labelScale s b) (labelScale_pos s hs.1.1 b)
  let U := nativeSourcePiece σ hσ p constructedGaps s {b} T
  have hS : DistributionSupportedOn S.carrier (hermiteScaleDistribution (6*p) U) :=
    actualSourcePiece_supportedOn_with_seams s hs σ hσ p hsep L hL T hTphys hTspec hphysical b
  have hclosed := physicalPeriodicSet_isClosed constructedGaps s
    (actualPositiveGaps_pos fixedProbeTemplate) hs.1.1 b
  have hread (a : S.subtype) (ha : (a:ℝ) ∈ physicalPeriodicSet constructedGaps s b)
      (r : ℕ) (hr : r ≤ 2*(6*p)) :
      carrierJetReading S (hermiteScaleDistribution (6*p) U) a r =
        if r=0 then originalPointMass L (hermiteScaleDistribution p T) a else 0 := by
    rw [carrierJetReading_eq_isolatedNative S (6*p) U hS a r hr]
    apply actualSourcePiece_isolated_jet_eq_mass s hs σ hσ p hsep L hL T hTphys hTspec
      hphysical b a (S.isolationRadius a) (S.isolationRadius_pos a) ha S.carrier hS _ r (by omega)
    intro x hx hdist
    by_contra hne
    have h := S.isolationRadius_le_dist a hx hne
    rw [Real.dist_eq] at h
    linarith
  apply native_atomic_of_jet_conditions S _ (6*p) U hS
  · intro a r hrpos hr
    by_cases ha : (a:ℝ) ∈ physicalPeriodicSet constructedGaps s b
    · rw [hread a ha r hr,ite_eq_right (by omega)]
    · exact carrierJetReading_zero_outside_closed_support S (6*p) U hS _ hclosed
        (hphysical b) a ha r hr
  · intro a ha
    by_cases hac : (a:ℝ) ∈ physicalPeriodicSet constructedGaps s b
    · have haL : (a:ℝ) ∉ L.carrier := fun h => ha ⟨h,hac⟩
      rw [hread a hac 0 (by omega)]
      simp only [ite_true,originalPointMass,dite_eq_right haL]
    · exact carrierJetReading_zero_outside_closed_support S (6*p) U hS _ hclosed
        (hphysical b) a hac 0 (by omega)

/-- The recovered whole piece is value-only on the literal paired physical block
A_i/t_b, not merely on the larger full periodic closure. -/
theorem actualSourcePiece_physical_atomic (s : ℕ+ → ℝ)
    (hs : ActualGoodScale fixedProbeTemplate s) (σ : ℝ) (hσ : 0 < σ) (p : ℕ)
    (hsep : ∀ b d : Label, b ≠ d → ∀ x ∈ sectorSet constructedGaps s b,
      ∀ y ∈ sectorSet constructedGaps s d, σ/(1+|x|+|y|)^6 ≤ |x-y|)
    (L : LocallyFiniteCarrier) (hL : L.carrier ⊆ carrierSet constructedGaps s)
    (T : HermiteScale (-(p:ℤ))) (hTphys : AtomicOnCarrier L (hermiteScaleDistribution p T))
    (hTspec : AtomicOnCarrier L (𝓕 (hermiteScaleDistribution p T)))
    (hphysical : ∀ d, DistributionSupportedOn (physicalPeriodicSet constructedGaps s d)
      (hermiteScaleDistribution (6*p) (nativeSourcePiece σ hσ p constructedGaps s {d} T)))
    (b : Label) :
    AtomicOnCarrier (sectorCarrier constructedGaps s (actualPositiveGaps_pos fixedProbeTemplate)
      hs.1.1 (b.1,b.2.flip))
      (hermiteScaleDistribution (6*p) (nativeSourcePiece σ hσ p constructedGaps s {b} T)) := by
  have h := actualSourcePiece_atomic_on_actual_intersection s hs σ hσ p hsep L hL T hTphys hTspec hphysical b
  intro f hf
  apply h f
  intro x hx
  apply hf x
  have hx' : x ∈ carrierSet constructedGaps s ∩ physicalPeriodicSet constructedGaps s b := ⟨hL hx.1,hx.2⟩
  rw [carrierSet_inter_physicalPeriodicSet constructedGaps s hs.1.2.1 b,
    physicalSectorSet_eq_flipped] at hx'
  exact hx'

end
end MeyerGeneralProblem.Adaptive
