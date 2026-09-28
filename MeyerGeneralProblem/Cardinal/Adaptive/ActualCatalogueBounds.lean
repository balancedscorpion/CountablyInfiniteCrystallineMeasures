module

public import MeyerGeneralProblem.Cardinal.Adaptive.ActualFutureTailBounds
public import MeyerGeneralProblem.Cardinal.Adaptive.CatalogueProduct

@[expose] public section

/-! Actual catalogue spatial and complete Fourier-tail estimates. -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open Classical
open scoped FourierTransform

private theorem reciprocal_coefficients_congr (M : ℕ) (P R R' : Fin M → ℕ)
    (hP : ∀ i, 1 ≤ P i) (hR : ∀ i, 1 ≤ R i) (hR' : ∀ i, 1 ≤ R' i) (h : R = R') :
    (fun j l => periodicCoefficient (reciprocalProductFunctions M P R hP hR j)
      (reciprocalProductFunctions_smooth M P R hP hR j) l) =
    (fun j l => periodicCoefficient (reciprocalProductFunctions M P R' hP hR' j)
      (reciprocalProductFunctions_smooth M P R' hP hR' j) l) := by
  subst R'
  rfl

private theorem reciprocal_product_congr (M : ℕ) (P R R' : Fin M → ℕ)
    (hP : ∀ i, 1 ≤ P i) (hR : ∀ i, 1 ≤ R i) (hR' : ∀ i, 1 ≤ R' i) (h : R = R')
    (s : Fin M → ℝ) :
    reciprocalAnnihilatorProduct M P R hP hR s =
      reciprocalAnnihilatorProduct M P R' hP hR' s := by
  subst R'
  rfl

/-- The complete actual annihilator at stage n+1, with both reciprocal arms. -/
def actualStageProduct (ψ : SchwartzMap ℝ ℂ) (n : ℕ) (s : ℕ+ → ℝ) : ℝ → ℂ :=
  reciprocalAnnihilatorProduct (n+1) (fun i => i.val+1) (fun i => actualGaps ψ i.val)
    (fun _ => Nat.succ_pos _) (fun i => actualGaps_pos ψ i.val) (fun i => s (prefixScaleIndex i))

/-- The actual stage product is a valid whole Schwartz multiplier. -/
theorem actualStageProduct_hasTemperateGrowth (ψ : SchwartzMap ℝ ℂ) (n : ℕ) (s : ℕ+ → ℝ) :
    (actualStageProduct ψ n s).HasTemperateGrowth :=
  reciprocalAnnihilatorProduct_hasTemperateGrowth _ _ _ _ _ _

/-- Every physical point in a covered signed sector is killed by the actual stage product. -/
theorem actualStageProduct_zero_on_prefix (ψ : SchwartzMap ℝ ℂ) (n : ℕ)
    (s : ℕ+ → ℝ) (hs : ∀ i, s i ∈ Set.Icc 1 2) (b : Label)
    (hb : b ∈ finitePrefixLabels (n+1)) (x : ℝ)
    (hx : x ∈ sectorSet (actualPositiveGaps ψ) s b) : actualStageProduct ψ n s x = 0 := by
  obtain ⟨⟨i,sign⟩,_,rfl⟩ := Finset.mem_image.mp hb
  rcases hx with ⟨y,hy,rfl⟩
  have hy' : y ∈ blockSet (i.val+1) (actualGaps ψ i.val) := by
    simpa only [actualPositiveGaps,prefixScaleIndex,PNat.mk_coe,Prod.fst,
      Nat.add_sub_cancel] using hy
  apply reciprocalAnnihilatorProduct_zero_on_blocks (n+1) _ _ _ _ _ i
    (ne_of_gt (lt_of_lt_of_le zero_lt_one (hs _).1))
  cases sign with
  | forward => exact Or.inr ⟨y,hy',rfl⟩
  | reciprocal => exact Or.inl ⟨y,hy',rfl⟩

/-- Every omitted physical sector lies beyond the preselected compact cutoff. -/
theorem actual_future_atom_outside_cutoff (ψ : SchwartzMap ℝ ℂ) (n : ℕ)
    (s : ℕ+ → ℝ) (hs : ∀ i, s i ∈ Set.Icc 1 2) (b : Label)
    (hb : b ∉ finitePrefixLabels (n+1)) (x : ℝ)
    (hx : x ∈ sectorSet (actualPositiveGaps ψ) s b) :
    2*(((actualStage ψ n).spatialCutoff:ℝ)+1) ≤ |x| := by
  have hg := sectorSet_central_gap _ s (actualPositiveGaps_pos ψ) hs b hx
  have hr : (actualGaps ψ (n+1):ℝ) ≤ actualPositiveGaps ψ b.1 := by
    exact_mod_cast actual_future_gap ψ n b hb
  have hcut := actualStage_cutoff_inside_next_gap ψ n
  have ht := (actualGaps_step ψ n).2.2.2
  have hlarge : (6:ℝ) ≤ actualGaps ψ (n+1) := by
    have h : 6 ≤ actualGaps ψ (n+1) := by omega
    exact_mod_cast h
  linarith

/-- The original whole atomic source sees only the paid cutoff error after
multiplication by the complete actual annihilator. -/
theorem actualStageProduct_pairing_eq_cutoff_error (ψ : SchwartzMap ℝ ℂ) (n : ℕ)
    (s : ℕ+ → ℝ) (hs : ∀ i, s i ∈ Set.Icc 1 2)
    (A : LocallyFiniteCarrier) (hA : A.carrier ⊆ carrierSet (actualPositiveGaps ψ) s)
    (U : TemperedDistribution ℝ ℂ) (hU : AtomicOnCarrier A U) (f : SchwartzMap ℝ ℂ) :
    U (SchwartzMap.smulLeftCLM ℂ (actualStageProduct ψ n s) f) =
      U (SchwartzMap.smulLeftCLM ℂ (actualStageProduct ψ n s)
        (f-compactSchwartzApproximation (actualStage ψ n).spatialCutoff f)) := by
  apply atomic_test_eq_of_eqOn A U hU
  intro x hx
  obtain ⟨b,hb⟩ := Set.mem_iUnion.mp (hA hx)
  rw [SchwartzMap.smulLeftCLM_apply_apply (actualStageProduct_hasTemperateGrowth ψ n s),
    SchwartzMap.smulLeftCLM_apply_apply (actualStageProduct_hasTemperateGrowth ψ n s)]
  by_cases hprefix : b ∈ finitePrefixLabels (n+1)
  · rw [actualStageProduct_zero_on_prefix ψ n s hs b hprefix x hb,zero_smul,zero_smul]
  · have he := schwartzCutoffError_eq_self (actualStage ψ n).spatialCutoff f x
      (actual_future_atom_outside_cutoff ψ n s hs b hprefix x hb)
    exact congrArg (fun z : ℂ => actualStageProduct ψ n s x • z) he.symm


/-- Exact identification with the product used in the preselected analytic budget. -/
theorem actualStageProduct_eq (ψ : SchwartzMap ℝ ℂ) (n : ℕ) (s : ℕ+ → ℝ) :
    actualStageProduct ψ n s = fun x => ∏ j,
      stageAnnihilatorFunctions ⟨n+1,Nat.succ_pos _⟩ (fun i => actualGaps ψ i.val)
        (fun i => actualGaps_pos ψ i.val) j
        (reciprocalProductScales (n+1) (fun i => s (prefixScaleIndex i)) j*x) := by
  funext x
  exact reciprocalAnnihilatorProduct_eq _ _ _ _ _ _ x

/-- Budget A controls the entire actual multiplied source at the original
native order. The covered atoms vanish and every future atom sees only the
preselected cutoff error; no physical support of a spectral piece is assumed. -/
theorem actualStage_catalogue_spatial_pairing_bound (ψ : SchwartzMap ℝ ℂ) (n p : ℕ)
    (hp : p ≤ n+1) (s : ℕ+ → ℝ) (hs : ∀ i, s i ∈ Set.Icc 1 2)
    (A : LocallyFiniteCarrier) (hA : A.carrier ⊆ carrierSet (actualPositiveGaps ψ) s)
    (T : HermiteScale (-(p:ℤ))) (hT : AtomicOnCarrier A (hermiteScaleDistribution p T))
    (y : ℝ) (hy : |y| ≤ 2*(n+1:ℝ)+1) :
    ‖(𝓕 (TemperedDistribution.smulLeftCLM ℂ (actualStageProduct ψ n s)
      (hermiteScaleDistribution p T)))
      (shrinkingBump ψ y (actualStage ψ n).catalogueRadius (actualStage ψ n).catalogueRadius_pos)‖ ≤
      (2:ℝ)^(-((n+1:ℕ):ℤ))*‖T‖ := by
  rw [TemperedDistribution.fourier_apply,TemperedDistribution.smulLeftCLM_apply_apply,
    actualStageProduct_pairing_eq_cutoff_error ψ n s hs A hA _ hT,
    hermiteScaleDistribution_apply]
  apply (norm_hermiteScalePairing_le (p:ℤ) T _).trans
  rw [mul_comm ((2:ℝ)^(-((n+1:ℕ):ℤ)))]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg T)
  have h := (actualStage_laws ψ n).catalogue_spatial p hp false y
    (by simpa only [PNat.mk_coe,Nat.cast_add,Nat.cast_one] using hy)
    (reciprocalProductScales (n+1) (fun i => s (prefixScaleIndex i)))
    (reciprocalProductScales_bound _ _ (fun i => hs _))
  rw [actualStageProduct_eq]
  exact h.le


/-- The unchanged-order complete omitted operator at the actual chosen Fourier cutoff. -/
def actualCatalogueTail (ψ : SchwartzMap ℝ ℂ) (n p : ℕ) (s : ℕ+ → ℝ) :
    HermiteScale (-(p:ℤ)) →L[ℂ] HermiteScale (-(p:ℤ)) :=
  fourierTranslationTail ((n+1)+(n+1)) p
    (fun j => periodicCoefficient
      (stageAnnihilatorFunctions ⟨n+1,Nat.succ_pos _⟩ (fun i => actualGaps ψ i.val)
        (fun i => actualGaps_pos ψ i.val) j)
      (stageAnnihilatorFunctions_smooth ⟨n+1,Nat.succ_pos _⟩
        (fun i => actualGaps ψ i.val) (fun i => actualGaps_pos ψ i.val) j))
    (reciprocalProductScales (n+1) (fun i => s (prefixScaleIndex i)))
    (actualStage ψ n).fourierCutoff

/-- The actual preselected full-tail budget applies to the Fourier image of
the original source, retaining precisely its original norm. -/
theorem actualCatalogueTail_pairing_bound (ψ : SchwartzMap ℝ ℂ) (n p : ℕ)
    (hp : p ≤ n+1) (s : ℕ+ → ℝ) (hs : ∀ i, s i ∈ Set.Icc 1 2)
    (T : HermiteScale (-(p:ℤ))) (y : ℝ) (hy : |y| ≤ 2*(n+1:ℝ)+1) :
    ‖hermiteScaleDistribution p (actualCatalogueTail ψ n p s (hermiteFourier (-(p:ℤ)) T))
      (shrinkingBump ψ y (actualStage ψ n).catalogueRadius (actualStage ψ n).catalogueRadius_pos)‖ ≤
      (2:ℝ)^(-((n+1:ℕ):ℤ))*‖T‖ := by
  have h := (actualStage_laws ψ n).fourier_tail p hp
    (reciprocalProductScales (n+1) (fun i => s (prefixScaleIndex i)))
    (reciprocalProductScales_bound _ _ (fun i => hs _)) y
    (by simpa only [PNat.mk_coe,Nat.cast_add,Nat.cast_one] using hy)
    (hermiteFourier (-(p:ℤ)) T)
  rw [LinearIsometryEquiv.norm_map] at h
  exact h

/-- The actual omitted native source represents every omitted signed tuple. -/
theorem actualCatalogueTail_realizes (ψ : SchwartzMap ℝ ℂ) (n p : ℕ)
    (s : ℕ+ → ℝ) (hs : ∀ i, s i ∈ Set.Icc 1 2) (T : HermiteScale (-(p:ℤ))) :
    hermiteScaleDistribution p (actualCatalogueTail ψ n p s (hermiteFourier (-(p:ℤ)) T)) =
    ∑' k : {k : Fin (n+1) × ReciprocalSign → ℤ //
      ((actualStage ψ n).fourierCutoff:ℝ) < ∑ d, |(k d:ℝ)|},
      (∏ d, cataloguePhaseCoefficient (actualPositiveGaps ψ) (actualPositiveGaps_pos ψ) d (k.val d)) •
        combDistributionTranslation (catalogueShift k.val s) (𝓕 (hermiteScaleDistribution p T)) := by
  have h := catalogueProduct_tail_realizes (actualPositiveGaps ψ) (actualPositiveGaps_pos ψ)
    s hs (n+1) p (actualStage ψ n).fourierCutoff T
  have hr : (fun i : Fin (n+1) => actualPositiveGaps ψ (prefixScaleIndex i)) =
      (fun i => actualGaps ψ i.val) := funext (actualPositiveGaps_prefix ψ)
  have hc := reciprocal_coefficients_congr (n+1) (fun i => i.val+1) _ _
    (fun _ => Nat.succ_pos _) (fun i => actualPositiveGaps_pos ψ (prefixScaleIndex i))
    (fun i => actualGaps_pos ψ i.val) hr
  rw [hc] at h
  exact h

/-- The actual product is exactly the product used by the signed catalogue series. -/
theorem actualStageProduct_eq_catalogue (ψ : SchwartzMap ℝ ℂ) (n : ℕ) (s : ℕ+ → ℝ) :
    actualStageProduct ψ n s =
    reciprocalAnnihilatorProduct (n+1) (fun i => i.val+1)
      (fun i => actualPositiveGaps ψ (prefixScaleIndex i))
      (fun _ => Nat.succ_pos _) (fun i => actualPositiveGaps_pos ψ (prefixScaleIndex i))
      (fun i => s (prefixScaleIndex i)) := by
  have hr : (fun i : Fin (n+1) => actualPositiveGaps ψ (prefixScaleIndex i)) =
      (fun i => actualGaps ψ i.val) := funext (actualPositiveGaps_prefix ψ)
  exact (reciprocal_product_congr (n+1) (fun i => i.val+1) _ _
    (fun _ => Nat.succ_pos _) (fun i => actualPositiveGaps_pos ψ (prefixScaleIndex i))
    (fun i => actualGaps_pos ψ i.val) hr (fun i => s (prefixScaleIndex i))).symm


/-- The two paid errors control the actual finite catalogue pairing uniformly
at each eligible original native order. Both full tails are retained. -/
theorem actualCatalogue_truncated_pairing_bound (ψ : SchwartzMap ℝ ℂ) (n p : ℕ)
    (hp : p ≤ n+1) (s : ℕ+ → ℝ) (hs : ∀ i, s i ∈ Set.Icc 1 2)
    (A : LocallyFiniteCarrier) (hA : A.carrier ⊆ carrierSet (actualPositiveGaps ψ) s)
    (T : HermiteScale (-(p:ℤ))) (hT : AtomicOnCarrier A (hermiteScaleDistribution p T))
    (y : ℝ) (hy : |y| ≤ 2*(n+1:ℝ)+1) :
    ‖(∑ k ∈ catalogueL1Cutoff (n+1) (actualStage ψ n).fourierCutoff,
      (∏ d, cataloguePhaseCoefficient (actualPositiveGaps ψ) (actualPositiveGaps_pos ψ) d (k d)) •
        combDistributionTranslation (catalogueShift k s) (𝓕 (hermiteScaleDistribution p T)))
      (shrinkingBump ψ y (actualStage ψ n).catalogueRadius (actualStage ψ n).catalogueRadius_pos)‖ ≤
      2*(2:ℝ)^(-((n+1:ℕ):ℤ))*‖T‖ := by
  have he := catalogueProduct_full_split (actualPositiveGaps ψ) (actualPositiveGaps_pos ψ)
    s hs (n+1) p (actualStage ψ n).fourierCutoff T
  rw [← actualCatalogueTail_realizes ψ n p s hs T,← actualStageProduct_eq_catalogue] at he
  have he' := congrArg (fun U : TemperedDistribution ℝ ℂ => U
    (shrinkingBump ψ y (actualStage ψ n).catalogueRadius (actualStage ψ n).catalogueRadius_pos)) he
  simp only [_root_.add_apply] at he'
  rw [eq_sub_of_add_eq he']
  apply (norm_sub_le _ _).trans
  apply (add_le_add (actualStage_catalogue_spatial_pairing_bound ψ n p hp s hs A hA T hT y hy)
    (actualCatalogueTail_pairing_bound ψ n p hp s hs T y hy)).trans_eq
  ring


/-- The actual radius meets the literal nonresonance isolation requirement. -/
theorem actualStage_catalogueRadius_small (ψ : SchwartzMap ℝ ℂ) (n : ℕ) :
    2*(actualStage ψ n).catalogueRadius ≤ (actualStage ψ n).catalogueConstant /
      (3+2*((actualStage ψ n).fourierCutoff:ℝ))^(catalogueDistanceExponent (n+1)) := by
  let C := actualStage ψ n
  have h := polynomialIsolationRadius_le_source C.catalogueConstant C.catalogueConstant_pos.le
    C.catalogueExponent C.fourierCutoff
  change C.catalogueRadius ≤ C.catalogueConstant /
    (10*(3+2*(C.fourierCutoff:ℝ))^C.catalogueExponent) at h
  have he : C.catalogueConstant/(10*(3+2*(C.fourierCutoff:ℝ))^C.catalogueExponent) =
      (C.catalogueConstant/(3+2*(C.fourierCutoff:ℝ))^C.catalogueExponent)/10 := by ring
  rw [he] at h
  have hn : 0 ≤ C.catalogueConstant/(3+2*(C.fourierCutoff:ℝ))^C.catalogueExponent := by
    have := C.catalogueConstant_pos; positivity
  change 2*C.catalogueRadius ≤ C.catalogueConstant/(3+2*(C.fourierCutoff:ℝ))^C.catalogueExponent
  linarith

/-- Every literal target catalogue point lies in the prescribed stage window. -/
theorem catalogueTargetPoint_bound (R : ℕ+ → ℕ) (hR : ∀ i, 1 ≤ R i)
    (s : ℕ+ → ℝ) (hs : ∀ i, s i ∈ Set.Icc 1 2) {M : ℕ}
    (target : Fin M × ReciprocalSign) (j : Fin M) (positive : Bool)
    (n : ℤ) (hn : |n| ≤ M) : |catalogueTargetPoint R s target j positive n| ≤ 2*(M:ℝ)+1 := by
  have hb : |prefixCataloguePhase (fun i => R (prefixScaleIndex i)) (target.1,j,positive)| < 1/2 :=
    abs_signedPhase_lt_half (Nat.succ_pos _) (hR _) ⟨j.val+1,Nat.succ_pos _⟩ positive
  have hn' : |(n:ℝ)| ≤ M := by exact_mod_cast hn
  have hsum := abs_add_le (n:ℝ)
    (prefixCataloguePhase (fun i => R (prefixScaleIndex i)) (target.1,j,positive))
  have hscale := (labelScale_mem_Icc s hs (prefixScaleIndex target.1,target.2)).2
  have hscale0 := labelScale_pos s hs (prefixScaleIndex target.1,target.2)
  unfold catalogueTargetPoint
  rw [abs_mul,abs_of_pos hscale0]
  have hmul := mul_le_mul_of_nonneg_right hscale
    (abs_nonneg ((n:ℝ)+prefixCataloguePhase (fun i => R (prefixScaleIndex i)) (target.1,j,positive)))
  nlinarith

/-- The actual fixed-phase truncated convolution is bounded by the two complete
stage errors. This is equation 13 with both analytic error estimates attached. -/
theorem actualStage_phase_convolution_bound (σ : ℝ) (hσ : 0 < σ) (p N : ℕ)
    (hp : p ≤ N+1) (s : ℕ+ → ℝ) (hs : ActualGoodScale compactSchwartzCutoff s)
    (hsep : ∀ b d : Label, b ≠ d →
      ∀ x ∈ sectorSet (actualPositiveGaps compactSchwartzCutoff) s b,
      ∀ y ∈ sectorSet (actualPositiveGaps compactSchwartzCutoff) s d,
        σ/(1+|x|+|y|)^6 ≤ |x-y|)
    (target : Fin (N+1) × ReciprocalSign) (j : Fin (N+1)) (positive : Bool)
    (n : ℤ) (hn : |n| ≤ N+1) (γ : ℝ) (hγ : 0 < γ)
    (hisol : ∀ m : ℤ, ∀ y ∈ sectorSet (actualPositiveGaps compactSchwartzCutoff) s
      (prefixScaleIndex target.1,target.2),
      y ≠ labelScale s (prefixScaleIndex target.1,target.2)*((m:ℝ)+
        prefixCataloguePhase (fun i => actualPositiveGaps compactSchwartzCutoff (prefixScaleIndex i))
          (target.1,j,positive)) →
      4*γ ≤ |y-labelScale s (prefixScaleIndex target.1,target.2)*((m:ℝ)+
        prefixCataloguePhase (fun i => actualPositiveGaps compactSchwartzCutoff (prefixScaleIndex i))
          (target.1,j,positive))|)
    (A B : LocallyFiniteCarrier)
    (hA : A.carrier ⊆ carrierSet (actualPositiveGaps compactSchwartzCutoff) s)
    (hB : B.carrier ⊆ carrierSet (actualPositiveGaps compactSchwartzCutoff) s)
    (T : HermiteScale (-(p:ℤ))) (hT : AtomicOnCarrier A (hermiteScaleDistribution p T))
    (hFT : AtomicOnCarrier B (𝓕 (hermiteScaleDistribution p T))) :
    ‖∑ l ∈ Finset.Icc (-((actualStage compactSchwartzCutoff N).fourierCutoff:ℤ))
      ((actualStage compactSchwartzCutoff N).fourierCutoff:ℤ),
      cataloguePhaseCoefficient (actualPositiveGaps compactSchwartzCutoff)
        (actualPositiveGaps_pos compactSchwartzCutoff) target l *
      isolatedSourceCoefficient σ hσ p (actualPositiveGaps compactSchwartzCutoff) s
        (prefixScaleIndex target.1,target.2)
        (prefixCataloguePhase (fun i => actualPositiveGaps compactSchwartzCutoff (prefixScaleIndex i))
          (target.1,j,positive)) γ hγ T (n-l)‖ ≤ 2*(2:ℝ)^(-((N+1:ℕ):ℤ))*‖T‖ := by
  let C := actualStage compactSchwartzCutoff N
  have he := catalogue_actual_truncated_pairing σ hσ p (actualPositiveGaps compactSchwartzCutoff)
    (actualPositiveGaps_pos compactSchwartzCutoff) (N+1) C.catalogueConstant C.catalogueConstant_pos.le
    s (hs.nonresonance _ s N) hsep C.fourierCutoff target j positive n hn
    C.catalogueRadius C.catalogueRadius_pos (actualStage_catalogueRadius_small compactSchwartzCutoff N)
    γ hγ hisol B hB T hFT
  rw [← he,catalogueProbe_eq_shrinkingBump]
  exact actualCatalogue_truncated_pairing_bound compactSchwartzCutoff N p hp s hs.1.1 A hA T hT _
    (by simpa only [Nat.cast_add,Nat.cast_one] using
      catalogueTargetPoint_bound _ (actualPositiveGaps_pos compactSchwartzCutoff) s hs.1.1 target j positive n hn)

end
end MeyerGeneralProblem.Adaptive
