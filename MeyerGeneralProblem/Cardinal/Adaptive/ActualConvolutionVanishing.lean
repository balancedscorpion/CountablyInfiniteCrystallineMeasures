module

public import MeyerGeneralProblem.Cardinal.Adaptive.ActualCatalogueBounds

@[expose] public section

/-! Full isolated-phase convolution vanishing from the actual stage recursion. -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open Classical Filter Set
open scoped Topology FourierTransform

/-- The actual deterministic Fourier cutoffs tend to infinity. -/
theorem actualStage_fourierCutoff_tendsto (ψ : SchwartzMap ℝ ℂ) :
    Tendsto (fun N : ℕ => (actualStage ψ N).fourierCutoff) atTop atTop :=
  tendsto_atTop_mono (fun N => (Nat.le_succ N).trans (actualStage ψ N).stage_le_cutoff) tendsto_id

/-- The two complete stage errors tend to zero at every fixed source norm. -/
theorem actualCatalogue_error_tendsto (C : ℝ) :
    Tendsto (fun N : ℕ => 2*(2:ℝ)^(-((N+1:ℕ):ℤ))*C) atTop (𝓝 0) := by
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (1:ℝ)/2 < 1)).mul_const C
  convert! h using 1
  · funext N
    rw [zpow_neg,zpow_natCast,pow_succ]
    simp only [one_div,inv_pow]
    field_simp
  · simp

/-- Every fixed actual phase orbit has one physical probe width for which the
entire original annihilator convolution vanishes. The proof uses the actual
stage recursion, both complete tails and both whole atomic source records. -/
theorem exists_actual_phase_convolution_zero (σ : ℝ) (hσ : 0 < σ) (p : ℕ)
    (s : ℕ+ → ℝ) (hs : ActualGoodScale compactSchwartzCutoff s)
    (hsep : ∀ b d : Label, b ≠ d →
      ∀ x ∈ sectorSet (actualPositiveGaps compactSchwartzCutoff) s b,
      ∀ y ∈ sectorSet (actualPositiveGaps compactSchwartzCutoff) s d,
        σ/(1+|x|+|y|)^6 ≤ |x-y|)
    (b : Label) (β : ℝ)
    (hβ : β ∈ phaseSet b.1 (actualPositiveGaps compactSchwartzCutoff b.1)) :
    ∃ γ : ℝ, ∃ hγ : 0 < γ,
      (∀ m : ℤ, ∀ y ∈ sectorSet (actualPositiveGaps compactSchwartzCutoff) s b,
        y ≠ labelScale s b*((m:ℝ)+β) → 4*γ ≤ |y-labelScale s b*((m:ℝ)+β)|) ∧
      ∀ A B : LocallyFiniteCarrier,
      A.carrier ⊆ carrierSet (actualPositiveGaps compactSchwartzCutoff) s →
      B.carrier ⊆ carrierSet (actualPositiveGaps compactSchwartzCutoff) s →
      ∀ T : HermiteScale (-(p:ℤ)), AtomicOnCarrier A (hermiteScaleDistribution p T) →
      AtomicOnCarrier B (𝓕 (hermiteScaleDistribution p T)) → ∀ n : ℤ,
      (∑' l : ℤ, phaseCoefficient b.1 (actualPositiveGaps compactSchwartzCutoff b.1)
        b.1.pos (actualPositiveGaps_pos compactSchwartzCutoff b.1) l *
        isolatedSourceCoefficient σ hσ p (actualPositiveGaps compactSchwartzCutoff) s b β γ hγ T (n-l)) = 0 := by
  obtain ⟨γ,hγ,hisol,hsum⟩ := exists_isolatedSourceCoefficient_convolution σ hσ p
    (actualPositiveGaps compactSchwartzCutoff) s (actualPositiveGaps_pos compactSchwartzCutoff)
    hs.1.1 b β hβ
  refine ⟨γ,hγ,hisol,fun A B hA hB T hT hFT n => ?_⟩
  let a := phaseCoefficient b.1 (actualPositiveGaps compactSchwartzCutoff b.1)
    b.1.pos (actualPositiveGaps_pos compactSchwartzCutoff b.1)
  let c := isolatedSourceCoefficient σ hσ p (actualPositiveGaps compactSchwartzCutoff) s b β γ hγ T
  have hconv := (tendsto_phase_convolution_cutoffs a c n (hsum T n)).comp
    (actualStage_fourierCutoff_tendsto compactSchwartzCutoff)
  have hbound : ∀ᶠ N : ℕ in atTop,
      ‖∑ l ∈ Finset.Icc (-((actualStage compactSchwartzCutoff N).fourierCutoff:ℤ))
        ((actualStage compactSchwartzCutoff N).fourierCutoff:ℤ), a l*c (n-l)‖ ≤
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
        (fun i => actualPositiveGaps compactSchwartzCutoff (prefixScaleIndex i))
        (target.1,phaseIndex,positive) = β := by
      unfold prefixCataloguePhase
      change signedPhase positive (blockPhase (target.1.val+1)
        (actualPositiveGaps compactSchwartzCutoff (prefixScaleIndex target.1))
        ⟨phaseIndex.val+1,Nat.succ_pos _⟩) = β
      have htval : target.1.val+1 = b.1.val := congrArg Subtype.val ht
      rw [htval,ht,hj]
      exact hphase.symm
    have hh := actualStage_phase_convolution_bound σ hσ p N hp s hs hsep
      target phaseIndex positive n hnN γ hγ (by simpa only [hbt,hph] using hisol)
      A B hA hB T hT hFT
    simpa only [cataloguePhaseCoefficient,ht,hbt,hph] using hh
  have hle : ‖∑' l : ℤ, a l*c (n-l)‖ ≤ 0 :=
    le_of_tendsto_of_tendsto hconv.norm (actualCatalogue_error_tendsto ‖T‖) hbound
  exact norm_eq_zero.mp (le_antisymm hle (norm_nonneg _))

end
end MeyerGeneralProblem.Adaptive
