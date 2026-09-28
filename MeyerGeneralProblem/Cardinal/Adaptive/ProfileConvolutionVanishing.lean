module

public import MeyerGeneralProblem.Cardinal.Adaptive.ActualConvolutionVanishing
public import MeyerGeneralProblem.Cardinal.Adaptive.CatalogueProfile

@[expose] public section

/-! Full convolution vanishing for the exact profile used by the final gap recursion. -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open Classical Filter Set
open scoped Topology FourierTransform

/-- The complete phase convolution vanishes for any actual normalized compact
profile, with every deterministic stage parameter chosen from that same profile. -/
theorem exists_profile_phase_convolution_zero (ψ : SchwartzMap ℝ ℂ)
    (hψone : ψ 0 = 1) (hψzero : ∀ x, 2 ≤ |x| → ψ x = 0) (σ : ℝ) (hσ : 0 < σ) (p : ℕ)
    (s : ℕ+ → ℝ) (hs : ActualGoodScale ψ s)
    (hsep : ∀ b d : Label, b ≠ d →
      ∀ x ∈ sectorSet (actualPositiveGaps ψ) s b,
      ∀ y ∈ sectorSet (actualPositiveGaps ψ) s d,
        σ/(1+|x|+|y|)^6 ≤ |x-y|)
    (b : Label) (β : ℝ)
    (hβ : β ∈ phaseSet b.1 (actualPositiveGaps ψ b.1)) :
    ∃ γ : ℝ, ∃ hγ : 0 < γ,
      (∀ m : ℤ, ∀ y ∈ sectorSet (actualPositiveGaps ψ) s b,
        y ≠ labelScale s b*((m:ℝ)+β) → 4*γ ≤ |y-labelScale s b*((m:ℝ)+β)|) ∧
      ∀ A B : LocallyFiniteCarrier,
      A.carrier ⊆ carrierSet (actualPositiveGaps ψ) s →
      B.carrier ⊆ carrierSet (actualPositiveGaps ψ) s →
      ∀ T : HermiteScale (-(p:ℤ)), AtomicOnCarrier A (hermiteScaleDistribution p T) →
      AtomicOnCarrier B (𝓕 (hermiteScaleDistribution p T)) → ∀ n : ℤ,
      (∑' l : ℤ, phaseCoefficient b.1 (actualPositiveGaps ψ b.1)
        b.1.pos (actualPositiveGaps_pos ψ b.1) l *
        isolatedSourceCoefficient σ hσ p (actualPositiveGaps ψ) s b β γ hγ T (n-l)) = 0 := by
  obtain ⟨γ,hγ,hisol,hsum⟩ := exists_isolatedSourceCoefficient_convolution σ hσ p
    (actualPositiveGaps ψ) s (actualPositiveGaps_pos ψ)
    hs.1.1 b β hβ
  refine ⟨γ,hγ,hisol,fun A B hA hB T hT hFT n => ?_⟩
  let a := phaseCoefficient b.1 (actualPositiveGaps ψ b.1)
    b.1.pos (actualPositiveGaps_pos ψ b.1)
  let c := isolatedSourceCoefficient σ hσ p (actualPositiveGaps ψ) s b β γ hγ T
  have hconv := (tendsto_phase_convolution_cutoffs a c n (hsum T n)).comp
    (actualStage_fourierCutoff_tendsto ψ)
  have hbound : ∀ᶠ N : ℕ in atTop,
      ‖∑ l ∈ Finset.Icc (-((actualStage ψ N).fourierCutoff:ℤ))
        ((actualStage ψ N).fourierCutoff:ℤ), a l*c (n-l)‖ ≤
        2*(2:ℝ)^(-((N+1:ℕ):ℤ))*‖T‖ := by
    obtain ⟨j,positive,hphase⟩ := hβ
    filter_upwards [eventually_ge_atTop (max p (max b.1.val (max j.val n.natAbs)))] with N hN
    have hp : p ≤ N+1 := by omega
    have hbN : b.1.val ≤ N+1 := by omega
    have hjN : j.val ≤ N+1 := by omega
    have hnN : |n| ≤ N+1 := by
      have hnn : n.natAbs ≤ N+1 := by omega
      have hh : (n.natAbs:ℤ) ≤ ((N+1:ℕ):ℤ) := Int.ofNat_le.mpr hnn
      simpa only [Int.natCast_natAbs,Nat.cast_add,Nat.cast_one] using hh
    let target : Fin (N+1) × ReciprocalSign :=
      (⟨b.1.val-1,by have := b.1.pos; omega⟩,b.2)
    let phaseIndex : Fin (N+1) := ⟨j.val-1,by have := j.pos; omega⟩
    have ht : prefixScaleIndex target.1 = b.1 := by
      apply Subtype.ext
      change b.1.val-1+1 = b.1.val
      exact Nat.sub_add_cancel b.1.pos
    have hbt : (prefixScaleIndex target.1,target.2) = b := Prod.ext ht rfl
    have hj : (⟨phaseIndex.val+1,Nat.succ_pos _⟩ : ℕ+) = j := by
      apply Subtype.ext
      change j.val-1+1 = j.val
      exact Nat.sub_add_cancel j.pos
    have hph : prefixCataloguePhase
        (fun i => actualPositiveGaps ψ (prefixScaleIndex i))
        (target.1,phaseIndex,positive) = β := by
      unfold prefixCataloguePhase
      change signedPhase positive (blockPhase (target.1.val+1)
        (actualPositiveGaps ψ (prefixScaleIndex target.1))
        ⟨phaseIndex.val+1,Nat.succ_pos _⟩) = β
      have htval : target.1.val+1 = b.1.val := congrArg Subtype.val ht
      rw [htval,ht,hj]
      exact hphase.symm
    have hh := actualStage_profile_phase_convolution_bound ψ hψone hψzero σ hσ p N hp s hs hsep
      target phaseIndex positive n hnN γ hγ (by simpa only [hbt,hph] using hisol)
      A B hA hB T hT hFT
    simpa only [cataloguePhaseCoefficient,ht,hbt,hph] using hh
  have hle : ‖∑' l : ℤ, a l*c (n-l)‖ ≤ 0 :=
    le_of_tendsto_of_tendsto hconv.norm (actualCatalogue_error_tendsto ‖T‖) hbound
  exact norm_eq_zero.mp (le_antisymm hle (norm_nonneg _))


/-- The full convolution vanishing theorem for the pinned final constructed
profile and therefore precisely the constructedGaps schedule. -/
theorem exists_fixedProfile_phase_convolution_zero (σ : ℝ) (hσ : 0 < σ) (p : ℕ)
    (s : ℕ+ → ℝ) (hs : ActualGoodScale fixedProbeTemplate s)
    (hsep : ∀ b d : Label, b ≠ d →
      ∀ x ∈ sectorSet (actualPositiveGaps fixedProbeTemplate) s b,
      ∀ y ∈ sectorSet (actualPositiveGaps fixedProbeTemplate) s d,
        σ/(1+|x|+|y|)^6 ≤ |x-y|)
    (b : Label) (β : ℝ)
    (hβ : β ∈ phaseSet b.1 (actualPositiveGaps fixedProbeTemplate b.1)) :
    ∃ γ : ℝ, ∃ hγ : 0 < γ,
      (∀ m : ℤ, ∀ y ∈ sectorSet (actualPositiveGaps fixedProbeTemplate) s b,
        y ≠ labelScale s b*((m:ℝ)+β) → 4*γ ≤ |y-labelScale s b*((m:ℝ)+β)|) ∧
      ∀ A B : LocallyFiniteCarrier,
      A.carrier ⊆ carrierSet (actualPositiveGaps fixedProbeTemplate) s →
      B.carrier ⊆ carrierSet (actualPositiveGaps fixedProbeTemplate) s →
      ∀ T : HermiteScale (-(p:ℤ)), AtomicOnCarrier A (hermiteScaleDistribution p T) →
      AtomicOnCarrier B (𝓕 (hermiteScaleDistribution p T)) → ∀ n : ℤ,
      (∑' l : ℤ, phaseCoefficient b.1 (actualPositiveGaps fixedProbeTemplate b.1)
        b.1.pos (actualPositiveGaps_pos fixedProbeTemplate b.1) l *
        isolatedSourceCoefficient σ hσ p (actualPositiveGaps fixedProbeTemplate) s b β γ hγ T (n-l)) = 0 :=
  exists_profile_phase_convolution_zero fixedProbeTemplate
    (fixedProbeTemplate_eq_one 0 (by norm_num))
    (fun x hx => fixedProbeTemplate_eq_zero x (by linarith)) σ hσ p s hs hsep b β hβ

end
end MeyerGeneralProblem.Adaptive
