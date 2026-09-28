module

public import MeyerGeneralProblem.Cardinal.Adaptive.ActualCatalogueBounds

@[expose] public section

/-! Catalogue extraction for the same fixed probe profile as the actual gap recursion. -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open Classical Set
open scoped FourierTransform

/-- Every normalized compact profile selects exactly the same actual catalogue atoms. -/
theorem catalogueTemplate_shifted_atom_value (ψ : SchwartzMap ℝ ℂ)
    (hψone : ψ 0 = 1) (hψzero : ∀ x, 2 ≤ |x| → ψ x = 0) (R : ℕ+ → ℕ) (M : ℕ)
    (c : ℝ) (hc : 0 ≤ c) (s : ℕ+ → ℝ) (hgood : ActualPrefixNonresonance R M c s)
    (L : ℕ) (target : Fin M × ReciprocalSign) (j : Fin M) (positive : Bool)
    (n : ℤ) (hn : |n| ≤ M) (origin : Label) (j' : ℕ+) (positive' : Bool) (n' : ℤ)
    (hcell : cellThreshold (R origin.1) j' ≤ n'.natAbs)
    (k : Fin M × ReciprocalSign → ℤ) (hk : k ∈ prefixShiftCatalogue M L)
    (δ : ℝ) (hδ : 0 < δ)
    (hδsmall : 2*δ ≤ c/(3+2*(L:ℝ))^(catalogueDistanceExponent M)) :
    shrinkingBump ψ (catalogueTargetPoint R s target j positive n) δ hδ
      (labelScale s origin*((n':ℝ)+signedPhase positive' (blockPhase origin.1 (R origin.1) j'))+
        catalogueShift k s) =
      if ExpectedPrefixComparison target origin n n'
        (prefixCataloguePhase (fun i => R (prefixScaleIndex i)) (target.1,j,positive))
        (signedPhase positive' (blockPhase origin.1 (R origin.1) j')) k then 1 else 0 := by
  let β := prefixCataloguePhase (fun i => R (prefixScaleIndex i)) (target.1,j,positive)
  let β' := signedPhase positive' (blockPhase origin.1 (R origin.1) j')
  let x := labelScale s origin*((n':ℝ)+β')
  let z := catalogueTargetPoint R s target j positive n
  have he : prefixComparisonValue target origin n n' β β' k s = z-x-catalogueShift k s := by
    simp only [prefixComparisonValue,z,catalogueTargetPoint,x,catalogueShift,β,β',catalogueTarget_scale]
  by_cases hex : ExpectedPrefixComparison target origin n n' β β' k
  · rw [ite_eq_left hex]
    have hz := expectedPrefixComparison_value_zero target origin n n' β β' k s hex
    rw [he] at hz
    have hxz : x+catalogueShift k s = z := by linarith
    change shrinkingBump ψ z δ hδ (x+catalogueShift k s) = 1
    rw [hxz,shrinkingBump_apply,sub_self,zero_div,hψone]
  · rw [ite_eq_right hex]
    rw [shrinkingBump_apply]
    apply hψzero
    rw [abs_div,abs_of_pos hδ,le_div_iff₀ hδ]
    have hdist := actualPrefixNonresonance_arbitrary_cutoff R M c hc s hgood L
      target j positive n hn origin j' positive' n' hcell k hk hex
    change c/(3+2*(L:ℝ))^(catalogueDistanceExponent M) ≤
      |prefixComparisonValue target origin n n' β β' k s| at hdist
    rw [he] at hdist
    have hh : |x+catalogueShift k s-z| = |z-x-catalogueShift k s| := by
      rw [show x+catalogueShift k s-z = -(z-x-catalogueShift k s) by ring,abs_neg]
    change 2*δ ≤ |x+catalogueShift k s-z|
    rw [hh]
    exact hδsmall.trans hdist


/-- Actual whole atomic sources give identical translated pairings for any admissible profile. -/
theorem catalogueTemplate_shift_pairing (ψ : SchwartzMap ℝ ℂ)
    (hψone : ψ 0 = 1) (hψzero : ∀ x, 2 ≤ |x| → ψ x = 0) (R : ℕ+ → ℕ) (M : ℕ)
    (c : ℝ) (hc : 0 ≤ c) (s : ℕ+ → ℝ) (hgood : ActualPrefixNonresonance R M c s)
    (L : ℕ) (target : Fin M × ReciprocalSign) (j : Fin M) (positive : Bool)
    (n : ℤ) (hn : |n| ≤ M)
    (k : Fin M × ReciprocalSign → ℤ) (hk : k ∈ prefixShiftCatalogue M L)
    (δ : ℝ) (hδ : 0 < δ)
    (hδsmall : 2*δ ≤ c/(3+2*(L:ℝ))^(catalogueDistanceExponent M))
    (A : LocallyFiniteCarrier) (hA : A.carrier ⊆ carrierSet R s)
    (U : TemperedDistribution ℝ ℂ) (hU : AtomicOnCarrier A U) :
    combDistributionTranslation (catalogueShift k s) U
      (shrinkingBump ψ (catalogueTargetPoint R s target j positive n) δ hδ) =
    combDistributionTranslation (catalogueShift k s) U
      (catalogueProbe R s target j positive n δ hδ) := by
  rw [combDistributionTranslation_apply,combDistributionTranslation_apply]
  apply atomic_test_eq_of_eqOn A U hU
  intro x hx
  obtain ⟨origin,horigin⟩ := mem_iUnion.mp (hA hx)
  rcases horigin with ⟨y,⟨j',positive',n',hcell,rfl⟩,rfl⟩
  rw [combSchwartzTranslation_apply,combSchwartzTranslation_apply,
    add_comm (catalogueShift k s)]
  rw [catalogueTemplate_shifted_atom_value ψ hψone hψzero R M c hc s hgood L target j positive n hn
    origin j' positive' n' hcell k hk δ hδ hδsmall,
    catalogueProbe_shifted_atom_value R M c hc s hgood L target j positive n hn
    origin j' positive' n' hcell k hk δ hδ hδsmall]

/-- The literal finite catalogue pairing is independent of the normalized probe profile. -/
theorem catalogueTemplate_l1_pairing (ψ : SchwartzMap ℝ ℂ)
    (hψone : ψ 0 = 1) (hψzero : ∀ x, 2 ≤ |x| → ψ x = 0) (R : ℕ+ → ℕ) (M : ℕ)
    (c : ℝ) (hc : 0 ≤ c) (s : ℕ+ → ℝ) (hgood : ActualPrefixNonresonance R M c s)
    (L : ℕ) (target : Fin M × ReciprocalSign) (j : Fin M) (positive : Bool)
    (n : ℤ) (hn : |n| ≤ M)
    (a : Fin M × ReciprocalSign → ℤ → ℂ)
    (δ : ℝ) (hδ : 0 < δ)
    (hδsmall : 2*δ ≤ c/(3+2*(L:ℝ))^(catalogueDistanceExponent M))
    (A : LocallyFiniteCarrier) (hA : A.carrier ⊆ carrierSet R s)
    (U : TemperedDistribution ℝ ℂ) (hU : AtomicOnCarrier A U) :
    (∑ k ∈ catalogueL1Cutoff M L, (∏ d, a d (k d)) •
      combDistributionTranslation (catalogueShift k s) U)
      (shrinkingBump ψ (catalogueTargetPoint R s target j positive n) δ hδ) =
    (∑ k ∈ catalogueL1Cutoff M L, (∏ d, a d (k d)) •
      combDistributionTranslation (catalogueShift k s) U)
      (catalogueProbe R s target j positive n δ hδ) := by
  simp only [_root_.sum_apply,_root_.smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  exact catalogueTemplate_shift_pairing ψ hψone hψzero R M c hc s hgood L target j positive n hn
    k (Finset.mem_filter.mp hk).1 δ hδ hδsmall A hA U hU

/-- Both complete stage errors pay the actual phase convolution for the very
same normalized profile that generated the deterministic gap recursion. -/
theorem actualStage_profile_phase_convolution_bound (ψ : SchwartzMap ℝ ℂ)
    (hψone : ψ 0 = 1) (hψzero : ∀ x, 2 ≤ |x| → ψ x = 0) (σ : ℝ) (hσ : 0 < σ) (p N : ℕ)
    (hp : p ≤ N+1) (s : ℕ+ → ℝ) (hs : ActualGoodScale ψ s)
    (hsep : ∀ b d : Label, b ≠ d →
      ∀ x ∈ sectorSet (actualPositiveGaps ψ) s b,
      ∀ y ∈ sectorSet (actualPositiveGaps ψ) s d,
        σ/(1+|x|+|y|)^6 ≤ |x-y|)
    (target : Fin (N+1) × ReciprocalSign) (j : Fin (N+1)) (positive : Bool)
    (n : ℤ) (hn : |n| ≤ N+1) (γ : ℝ) (hγ : 0 < γ)
    (hisol : ∀ m : ℤ, ∀ y ∈ sectorSet (actualPositiveGaps ψ) s
      (prefixScaleIndex target.1,target.2),
      y ≠ labelScale s (prefixScaleIndex target.1,target.2)*((m:ℝ)+
        prefixCataloguePhase (fun i => actualPositiveGaps ψ (prefixScaleIndex i))
          (target.1,j,positive)) →
      4*γ ≤ |y-labelScale s (prefixScaleIndex target.1,target.2)*((m:ℝ)+
        prefixCataloguePhase (fun i => actualPositiveGaps ψ (prefixScaleIndex i))
          (target.1,j,positive))|)
    (A B : LocallyFiniteCarrier)
    (hA : A.carrier ⊆ carrierSet (actualPositiveGaps ψ) s)
    (hB : B.carrier ⊆ carrierSet (actualPositiveGaps ψ) s)
    (T : HermiteScale (-(p:ℤ))) (hT : AtomicOnCarrier A (hermiteScaleDistribution p T))
    (hFT : AtomicOnCarrier B (𝓕 (hermiteScaleDistribution p T))) :
    ‖∑ l ∈ Finset.Icc (-((actualStage ψ N).fourierCutoff:ℤ))
      ((actualStage ψ N).fourierCutoff:ℤ),
      cataloguePhaseCoefficient (actualPositiveGaps ψ)
        (actualPositiveGaps_pos ψ) target l *
      isolatedSourceCoefficient σ hσ p (actualPositiveGaps ψ) s
        (prefixScaleIndex target.1,target.2)
        (prefixCataloguePhase (fun i => actualPositiveGaps ψ (prefixScaleIndex i))
          (target.1,j,positive)) γ hγ T (n-l)‖ ≤ 2*(2:ℝ)^(-((N+1:ℕ):ℤ))*‖T‖ := by
  let C := actualStage ψ N
  have he := catalogue_actual_truncated_pairing σ hσ p (actualPositiveGaps ψ)
    (actualPositiveGaps_pos ψ) (N+1) C.catalogueConstant C.catalogueConstant_pos.le
    s (hs.nonresonance _ s N) hsep C.fourierCutoff target j positive n hn
    C.catalogueRadius C.catalogueRadius_pos (actualStage_catalogueRadius_small ψ N)
    γ hγ hisol B hB T hFT
  rw [← he]
  rw [← catalogueTemplate_l1_pairing ψ hψone hψzero (actualPositiveGaps ψ) (N+1)
    C.catalogueConstant C.catalogueConstant_pos.le s (hs.nonresonance _ s N)
    C.fourierCutoff target j positive n hn
    (cataloguePhaseCoefficient (actualPositiveGaps ψ) (actualPositiveGaps_pos ψ))
    C.catalogueRadius C.catalogueRadius_pos (actualStage_catalogueRadius_small ψ N)
    B hB (𝓕 (hermiteScaleDistribution p T)) hFT]
  exact actualCatalogue_truncated_pairing_bound ψ N p hp s hs.1.1 A hA T hT _
    (by simpa only [Nat.cast_add,Nat.cast_one] using
      catalogueTargetPoint_bound _ (actualPositiveGaps_pos ψ) s hs.1.1 target j positive n hn)


end
end MeyerGeneralProblem.Adaptive
