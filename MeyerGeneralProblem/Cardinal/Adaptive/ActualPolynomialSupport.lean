module

public import MeyerGeneralProblem.Cardinal.Adaptive.PolynomialSupportDescent
public import MeyerGeneralProblem.Cardinal.Adaptive.AntiperiodicLift
public import MeyerGeneralProblem.Cardinal.Adaptive.ActualAtomRecovery

@[expose] public section

/-! # Physical support from the actual bounded polynomial lifts -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open Set
open scoped FourierTransform

/-- Reindex the actual finite prefix without replacing it by an infinite sum. -/
theorem sum_finitePrefixLabels {A : Type*} [AddCommMonoid A] (M : ℕ) (f : Label → A) :
    (∑ b ∈ finitePrefixLabels M, f b) =
      ∑ b : Fin M × ReciprocalSign, f (prefixScaleIndex b.1,b.2) := by
  classical
  unfold finitePrefixLabels
  rw [Finset.sum_image]
  intro b hb c hc he
  apply Prod.ext
  · apply Fin.ext
    have hi := congrArg (fun d : Label => d.1.val) he
    change b.1.val+1=c.1.val+1 at hi
    omega
  · exact congrArg (fun d : Label => d.2) he

/-- Instantiate the finite downward phase descent with the actual uniform native
source restrictions and the actual bounded antiperiodic coefficient maps. The
only remaining premise is the local lift agreement supplied by seam recovery. -/
theorem actualSourcePiece_supportedOn_of_lift_agreement (ψ : SchwartzMap ℝ ℂ)
    (s : ℕ+ → ℝ) (hs : ActualGoodScale ψ s) (σ : ℝ) (hσ : 0 < σ) (p : ℕ)
    (hsep : ∀ b d : Label, b ≠ d → ∀ x ∈ sectorSet (actualPositiveGaps ψ) s b,
      ∀ y ∈ sectorSet (actualPositiveGaps ψ) s d, σ/(1+|x|+|y|)^6 ≤ |x-y|)
    (L : LocallyFiniteCarrier) (hL : L.carrier ⊆ carrierSet (actualPositiveGaps ψ) s)
    (T : HermiteScale (-(p:ℤ))) (hTphys : AtomicOnCarrier L (hermiteScaleDistribution p T))
    (hTspec : AtomicOnCarrier L (𝓕 (hermiteScaleDistribution p T)))
    (hlocal : ∀ b : Label, DistributionVanishesOn (physicalPeriodicSet (actualPositiveGaps ψ) s b)ᶜ
      (hermiteScaleDistribution (6*p) (nativeSourcePiece σ hσ p (actualPositiveGaps ψ) s {b} T) -
        antiperiodicLiftPolynomial p (12*p) (labelScale s b)⁻¹ (physical_period_mem_Icc s hs.1.1 b)
          (nativeSourcePiece σ hσ p (actualPositiveGaps ψ) s {b} T))) :
    ∀ b, DistributionSupportedOn (physicalPeriodicSet (actualPositiveGaps ψ) s b)
      (hermiteScaleDistribution (6*p) (nativeSourcePiece σ hσ p (actualPositiveGaps ψ) s {b} T)) := by
  let U (b : Label) := nativeSourcePiece σ hσ p (actualPositiveGaps ψ) s {b} T
  let V (b : Label) (r : Fin (12*p+1)) :=
    nativeAntiperiodicCoefficient p (12*p) (labelScale s b)⁻¹
      (physical_period_mem_Icc s hs.1.1 b) r (U b)
  let future (n : ℕ) := nativeSourcePiece σ hσ p (actualPositiveGaps ψ) s
    (↑(finitePrefixLabels (n+1)) : Set Label)ᶜ T
  obtain ⟨A,hA,hAop⟩ := exists_nativeSourcePiece_norm_bound σ hσ p
  obtain ⟨B,hB,hBop⟩ := exists_nativeAntiperiodicCoefficient_norm_bound p
  have hnorm (b : Label) (r : Fin (12*p+1)) : ‖V b r‖ ≤ B*(A*‖T‖) := by
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul (hBop (12*p) le_rfl _ _ r) (hAop _ s {b} T) (norm_nonneg _) hB.le)
  have hlocal' (b : Label) : DistributionVanishesOn (physicalPeriodicSet (actualPositiveGaps ψ) s b)ᶜ
      (hermiteScaleDistribution (6*p) (U b) -
        ∑ r, monomialDistribution r.val (hermiteScaleDistribution (liftOrder p) (V b r))) := hlocal b
  have hsplit (n : ℕ) :
      (∑ b : Fin (n+1) × ReciprocalSign,
        hermiteScaleDistribution (6*p) (U (prefixScaleIndex b.1,b.2))) +
        hermiteScaleDistribution (6*p) (future n) = hermiteScaleDistribution p T := by
    simpa only [sum_finitePrefixLabels] using
      nativeSourcePiece_finite_split σ hσ p (actualPositiveGaps ψ) s hsep L hL T hTspec
        (finitePrefixLabels (n+1))
  have hcoeff := all_coefficients_vanishOffClosure ψ s hs p (12*p) le_rfl V
    (fun b r => nativeAntiperiodicCoefficient_antiperiodic p (12*p) le_rfl _ _ r (U b))
    (B*(A*‖T‖)) (by positivity) hnorm
    (fun b => hermiteScaleDistribution (6*p) (U b)) (hermiteScaleDistribution p T)
    future (A*‖T‖) (fun n => hAop _ s _ T)
    (fun n => actualSourcePiece_future_support ψ s hs σ hσ p n hsep L hL T hTspec)
    hsplit hlocal' L hL hTphys
  intro b
  exact piece_supportedOn_of_local_polynomial_agreement _ (12*p) _ _ (hlocal' b) (hcoeff b)

/-- The actual physical closure complement is periodic with its literal reciprocal period. -/
theorem physicalPeriodicSet_compl_periodic (R : ℕ+ → ℕ) (s : ℕ+ → ℝ) (b : Label) :
    Function.Periodic (fun x => x ∈ (physicalPeriodicSet R s b)ᶜ) (labelScale s b)⁻¹ := by
  intro x
  apply propext
  apply not_congr
  simpa only [Int.cast_one,one_mul] using physicalPeriodicSet_add_period_iff R s b x 1

/-- S03's exact local antidifference identity supplies the last input to the
actual fixed-order support descent; coefficient bounds and future errors are derived. -/
theorem actualSourcePiece_supportedOn_of_antidifference (ψ : SchwartzMap ℝ ℂ)
    (s : ℕ+ → ℝ) (hs : ActualGoodScale ψ s) (σ : ℝ) (hσ : 0 < σ) (p : ℕ)
    (hsep : ∀ b d : Label, b ≠ d → ∀ x ∈ sectorSet (actualPositiveGaps ψ) s b,
      ∀ y ∈ sectorSet (actualPositiveGaps ψ) s d, σ/(1+|x|+|y|)^6 ≤ |x-y|)
    (L : LocallyFiniteCarrier) (hL : L.carrier ⊆ carrierSet (actualPositiveGaps ψ) s)
    (T : HermiteScale (-(p:ℤ))) (hTphys : AtomicOnCarrier L (hermiteScaleDistribution p T))
    (hTspec : AtomicOnCarrier L (𝓕 (hermiteScaleDistribution p T)))
    (hdiff : ∀ b : Label, DistributionVanishesOn (physicalPeriodicSet (actualPositiveGaps ψ) s b)ᶜ
      ((distributionAntidifference (labelScale s b)⁻¹ : TemperedDistribution ℝ ℂ → TemperedDistribution ℝ ℂ)^[12*p+1]
        (hermiteScaleDistribution (6*p) (nativeSourcePiece σ hσ p (actualPositiveGaps ψ) s {b} T)))) :
    ∀ b, DistributionSupportedOn (physicalPeriodicSet (actualPositiveGaps ψ) s b)
      (hermiteScaleDistribution (6*p) (nativeSourcePiece σ hσ p (actualPositiveGaps ψ) s {b} T)) := by
  apply actualSourcePiece_supportedOn_of_lift_agreement ψ s hs σ hσ p hsep L hL T hTphys hTspec
  intro b
  exact antiperiodicLiftPolynomial_agrees p (12*p) le_rfl _ (physical_period_mem_Icc s hs.1.1 b)
    _ (physicalPeriodicSet_isClosed _ s (actualPositiveGaps_pos ψ) hs.1.1 b).isOpen_compl
    (physicalPeriodicSet_compl_periodic _ s b) _ (hdiff b)

end
end MeyerGeneralProblem.Adaptive
