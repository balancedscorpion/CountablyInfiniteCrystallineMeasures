module

public import MeyerGeneralProblem.Cardinal.Adaptive.IsolatedPhaseCoefficients
public import MeyerGeneralProblem.Cardinal.Adaptive.CatalogueNonresonance

@[expose] public section

/-! Exact finite catalogue extraction from actual whole atomic spectral sources. -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open MeasureTheory Set Filter Classical
open scoped Topology ContDiff FourierTransform

/-- The actual finite-prefix Fourier translation at a shift tuple. -/
def catalogueShift {M : ℕ} (k : Fin M × ReciprocalSign → ℤ) (s : ℕ+ → ℝ) : ℝ :=
  reciprocalLaurentValue (fun i => (k (i,.forward):ℝ))
    (fun i => (k (i,.reciprocal):ℝ)) (fun i => s (prefixScaleIndex i))

/-- An arbitrary translation cutoff sits below a dyadic cutoff at most twice its successor. -/
theorem exists_catalogue_dyadic_cover (L : ℕ) : ∃ ℓ : ℕ, L ≤ 2^ℓ ∧ 2^ℓ ≤ 2*(L+1) := by
  refine ⟨Nat.log 2 (L+1)+1,?_,?_⟩
  · have h := Nat.lt_pow_succ_log_self (by norm_num : 1<2) (L+1)
    exact (Nat.le_succ L).trans h.le
  · rw [pow_succ]
    have h := Nat.pow_log_le_self 2 (x := L+1) (by omega)
    omega

/-- The proven dyadic good event yields the accepted radius at every actual cutoff L. -/
theorem actualPrefixNonresonance_arbitrary_cutoff (R : ℕ+ → ℕ) (M : ℕ)
    (c : ℝ) (hc : 0 ≤ c) (s : ℕ+ → ℝ) (hgood : ActualPrefixNonresonance R M c s)
    (L : ℕ) (target : Fin M × ReciprocalSign) (j : Fin M) (positive : Bool)
    (n : ℤ) (hn : |n| ≤ M) (origin : Label) (j' : ℕ+) (positive' : Bool) (n' : ℤ)
    (hcell : cellThreshold (R origin.1) j' ≤ n'.natAbs)
    (k : Fin M × ReciprocalSign → ℤ) (hk : k ∈ prefixShiftCatalogue M L)
    (hbad : ¬ ExpectedPrefixComparison target origin n n'
      (prefixCataloguePhase (fun i => R (prefixScaleIndex i)) (target.1,j,positive))
      (signedPhase positive' (blockPhase origin.1 (R origin.1) j')) k) :
    c / (3+2*(L:ℝ))^(catalogueDistanceExponent M) ≤
      |prefixComparisonValue target origin n n'
        (prefixCataloguePhase (fun i => R (prefixScaleIndex i)) (target.1,j,positive))
        (signedPhase positive' (blockPhase origin.1 (R origin.1) j')) k s| := by
  obtain ⟨ℓ,hL,hpow⟩ := exists_catalogue_dyadic_cover L
  have hk' : k ∈ prefixShiftCatalogue M (2^ℓ) := by
    apply Fintype.mem_piFinset.mpr
    intro d
    have hh := Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hk d)
    apply Finset.mem_Icc.mpr
    have hcast : (L:ℤ) ≤ ((2^ℓ:ℕ):ℤ) := by exact_mod_cast hL
    constructor <;> omega
  have hb := hgood ℓ target j positive n hn origin j' positive' n' hcell k hk' hbad
  apply le_trans _ hb
  apply div_le_div_of_nonneg_left hc (by positivity)
  apply pow_le_pow_left₀ (by positivity)
  have hh : ((2^ℓ:ℕ):ℝ) ≤ 2*((L:ℝ)+1) := by exact_mod_cast hpow
  push_cast at hh ⊢
  linarith

/-- Every prefix reciprocal scale is exactly its actual label scale. -/
theorem catalogueTarget_scale {M : ℕ} (s : ℕ+ → ℝ) (target : Fin M × ReciprocalSign) :
    scaleFactor target.2 (s (prefixScaleIndex target.1)) =
      labelScale s (prefixScaleIndex target.1,target.2) :=
  (labelScale_eq_scaleFactor s (prefixScaleIndex target.1,target.2)).symm

/-- A shift tuple supported at one generating coordinate is one actual physical translation. -/
theorem catalogueShift_single_coordinate {M : ℕ} (target : Fin M × ReciprocalSign)
    (k : Fin M × ReciprocalSign → ℤ) (s : ℕ+ → ℝ)
    (hk : ∀ d, d ≠ target → k d = 0) :
    catalogueShift k s = (k target:ℝ)*labelScale s (prefixScaleIndex target.1,target.2) := by
  unfold catalogueShift reciprocalLaurentValue
  rw [Finset.sum_eq_single target.1]
  · rcases target with ⟨i,sign⟩
    cases sign with
    | forward =>
        have hz := hk (i,.reciprocal) (by simp)
        simp only [hz,Int.cast_zero,zero_mul,add_zero,labelScale]
    | reciprocal =>
        have hz := hk (i,.forward) (by simp)
        simp only [hz,Int.cast_zero,zero_mul,zero_add,labelScale]
  · intro i hi hne
    have hf := hk (i,.forward) (fun he => hne (congrArg Prod.fst he))
    have hr := hk (i,.reciprocal) (fun he => hne (congrArg Prod.fst he))
    simp only [hf,hr,Int.cast_zero,zero_mul,add_zero]
  · simp

/-- Every expected comparison is an exact physical equality, with all scale signs retained. -/
theorem expectedPrefixComparison_value_zero {M : ℕ} (target : Fin M × ReciprocalSign)
    (origin : Label) (n n' : ℤ) (β β' : ℝ) (k : Fin M × ReciprocalSign → ℤ)
    (s : ℕ+ → ℝ) (h : ExpectedPrefixComparison target origin n n' β β' k) :
    prefixComparisonValue target origin n n' β β' k s = 0 := by
  rcases h with ⟨ho,hβ,hk,hsparse⟩
  unfold prefixComparisonValue
  rw [catalogueTarget_scale,ho,hβ]
  change _ - _ - catalogueShift k s = 0
  rw [catalogueShift_single_coordinate target k s hsparse,hk]
  push_cast
  ring


/-- The literal target point of the stage catalogue. -/
def catalogueTargetPoint {M : ℕ} (R : ℕ+ → ℕ) (s : ℕ+ → ℝ)
    (target : Fin M × ReciprocalSign) (j : Fin M) (positive : Bool) (n : ℤ) : ℝ :=
  labelScale s (prefixScaleIndex target.1,target.2)*((n:ℝ)+
    prefixCataloguePhase (fun i => R (prefixScaleIndex i)) (target.1,j,positive))

/-- The actual compact catalogue test with value one at its target. -/
def catalogueProbe {M : ℕ} (R : ℕ+ → ℕ) (s : ℕ+ → ℝ)
    (target : Fin M × ReciprocalSign) (j : Fin M) (positive : Bool) (n : ℤ)
    (δ : ℝ) (hδ : 0 < δ) : SchwartzMap ℝ ℂ :=
  localJetProbe compactSchwartzCutoff δ hδ 0 (catalogueTargetPoint R s target j positive n)

/-- The catalogue test is the same actual physical shrinking bump used by the original tail budget. -/
theorem catalogueProbe_eq_shrinkingBump {M : ℕ} (R : ℕ+ → ℕ) (s : ℕ+ → ℝ)
    (target : Fin M × ReciprocalSign) (j : Fin M) (positive : Bool) (n : ℤ)
    (δ : ℝ) (hδ : 0 < δ) :
    catalogueProbe R s target j positive n δ hδ =
      shrinkingBump compactSchwartzCutoff (catalogueTargetPoint R s target j positive n) δ hδ := by
  ext x
  simp only [catalogueProbe,localJetProbe_apply,shrinkingBump_apply,pow_zero,
    Nat.factorial_zero,Nat.cast_one,div_one,one_mul]

/-- The actual shifted compact catalogue test selects exactly the expected physical comparisons. -/
theorem catalogueProbe_shifted_atom_value (R : ℕ+ → ℕ) (M : ℕ)
    (c : ℝ) (hc : 0 ≤ c) (s : ℕ+ → ℝ) (hgood : ActualPrefixNonresonance R M c s)
    (L : ℕ) (target : Fin M × ReciprocalSign) (j : Fin M) (positive : Bool)
    (n : ℤ) (hn : |n| ≤ M) (origin : Label) (j' : ℕ+) (positive' : Bool) (n' : ℤ)
    (hcell : cellThreshold (R origin.1) j' ≤ n'.natAbs)
    (k : Fin M × ReciprocalSign → ℤ) (hk : k ∈ prefixShiftCatalogue M L)
    (δ : ℝ) (hδ : 0 < δ)
    (hδsmall : 2*δ ≤ c/(3+2*(L:ℝ))^(catalogueDistanceExponent M)) :
    catalogueProbe R s target j positive n δ hδ
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
    change localJetProbe compactSchwartzCutoff δ hδ 0 z (x+catalogueShift k s) = 1
    rw [hxz,localJetProbe_apply,sub_self,zero_div]
    simp only [pow_zero,Nat.factorial_zero,Nat.cast_one,div_one,one_mul]
    exact compactSchwartzCutoff_eq_one (by norm_num)
  · rw [ite_eq_right hex]
    apply localJetProbe_cutoff_zero
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


/-- A shift with a nonzero nongenerating coordinate contributes exactly zero to the catalogue test. -/
theorem catalogue_nongenerating_shift_action_zero (R : ℕ+ → ℕ) (M : ℕ)
    (c : ℝ) (hc : 0 ≤ c) (s : ℕ+ → ℝ) (hgood : ActualPrefixNonresonance R M c s)
    (L : ℕ) (target : Fin M × ReciprocalSign) (j : Fin M) (positive : Bool)
    (n : ℤ) (hn : |n| ≤ M)
    (k : Fin M × ReciprocalSign → ℤ) (hk : k ∈ prefixShiftCatalogue M L)
    (hnot : ¬ ∀ d, d ≠ target → k d = 0) (δ : ℝ) (hδ : 0 < δ)
    (hδsmall : 2*δ ≤ c/(3+2*(L:ℝ))^(catalogueDistanceExponent M))
    (A : LocallyFiniteCarrier) (hA : A.carrier ⊆ carrierSet R s)
    (U : TemperedDistribution ℝ ℂ) (hU : AtomicOnCarrier A U) :
    combDistributionTranslation (catalogueShift k s) U
      (catalogueProbe R s target j positive n δ hδ) = 0 := by
  rw [combDistributionTranslation_apply]
  apply hU
  intro x hx
  obtain ⟨origin,horigin⟩ := mem_iUnion.mp (hA hx)
  rcases horigin with ⟨y,⟨j',positive',n',hcell,rfl⟩,rfl⟩
  rw [combSchwartzTranslation_apply,add_comm (catalogueShift k s)]
  rw [catalogueProbe_shifted_atom_value R M c hc s hgood L target j positive n hn
    origin j' positive' n' hcell k hk δ hδ hδsmall]
  rw [ite_eq_right]
  exact fun h => hnot h.2.2.2


/-- A generating-coordinate shift reads exactly the actual fixed-phase mass, including absent cells. -/
theorem catalogue_generating_shift_action (σ : ℝ) (hσ : 0 < σ) (p : ℕ)
    (R : ℕ+ → ℕ) (M : ℕ) (c : ℝ) (hc : 0 ≤ c) (s : ℕ+ → ℝ)
    (hgood : ActualPrefixNonresonance R M c s)
    (hsep : ∀ b d : Label, b ≠ d → ∀ x ∈ sectorSet R s b,
      ∀ y ∈ sectorSet R s d, σ/(1+|x|+|y|)^6 ≤ |x-y|)
    (L : ℕ) (target : Fin M × ReciprocalSign) (j : Fin M) (positive : Bool)
    (n : ℤ) (hn : |n| ≤ M)
    (k : Fin M × ReciprocalSign → ℤ) (hk : k ∈ prefixShiftCatalogue M L)
    (hsparse : ∀ d, d ≠ target → k d = 0) (δ : ℝ) (hδ : 0 < δ)
    (hδsmall : 2*δ ≤ c/(3+2*(L:ℝ))^(catalogueDistanceExponent M))
    (γ : ℝ) (hγ : 0 < γ)
    (hisol : ∀ m : ℤ, ∀ y ∈ sectorSet R s (prefixScaleIndex target.1,target.2),
      y ≠ labelScale s (prefixScaleIndex target.1,target.2)*((m:ℝ)+
        prefixCataloguePhase (fun i => R (prefixScaleIndex i)) (target.1,j,positive)) →
      4*γ ≤ |y-labelScale s (prefixScaleIndex target.1,target.2)*((m:ℝ)+
        prefixCataloguePhase (fun i => R (prefixScaleIndex i)) (target.1,j,positive))|)
    (A : LocallyFiniteCarrier) (hA : A.carrier ⊆ carrierSet R s)
    (T : HermiteScale (-(p:ℤ))) (hT : AtomicOnCarrier A (𝓕 (hermiteScaleDistribution p T))) :
    combDistributionTranslation (catalogueShift k s) (𝓕 (hermiteScaleDistribution p T))
      (catalogueProbe R s target j positive n δ hδ) =
    isolatedSourceCoefficient σ hσ p R s (prefixScaleIndex target.1,target.2)
      (prefixCataloguePhase (fun i => R (prefixScaleIndex i)) (target.1,j,positive)) γ hγ T (n-k target) := by
  rw [combDistributionTranslation_apply,isolatedSourceCoefficient,isolatedOrbitCoefficient,
    fourier_nativeSourcePiece,TemperedDistribution.smulLeftCLM_apply_apply]
  apply atomic_test_eq_of_eqOn A _ hT
  intro x hx
  obtain ⟨origin,horigin⟩ := mem_iUnion.mp (hA hx)
  rcases horigin with ⟨y,⟨j',positive',n',hcell,rfl⟩,rfl⟩
  let b : Label := (prefixScaleIndex target.1,target.2)
  let β := prefixCataloguePhase (fun i => R (prefixScaleIndex i)) (target.1,j,positive)
  let β' := signedPhase positive' (blockPhase origin.1 (R origin.1) j')
  let x : ℝ := labelScale s origin*((n':ℝ)+β')
  let z := catalogueTargetPoint R s target j positive n
  have hxsec : x ∈ sectorSet R s origin := ⟨_,⟨j',positive',n',hcell,rfl⟩,rfl⟩
  have hsel := actualSectorSelector_on_sector σ hσ R s hsep {b} origin x hxsec
  rw [combSchwartzTranslation_apply,add_comm (catalogueShift k s),
    catalogueProbe_shifted_atom_value R M c hc s hgood L target j positive n hn
      origin j' positive' n' hcell k hk δ hδ hδsmall,
    SchwartzMap.smulLeftCLM_apply_apply (actualSectorSelector_hasTemperateGrowth σ hσ R s _),smul_eq_mul]
  by_cases hex : ExpectedPrefixComparison target origin n n' β β' k
  · rw [ite_eq_left hex]
    have ho : origin=b := hex.1
    have hphase : β'=β := hex.2.1
    have hcellid : n' = n-k target := by have hh := hex.2.2.1; omega
    have hxx : x = labelScale s b*((((n-k target):ℤ):ℝ)+β) := by
      dsimp only [x]
      rw [ho,hphase,hcellid]
    have hselone : actualSectorSelector σ hσ R s {b} x = 1 := by
      simpa only [ho,mem_singleton_iff,ite_true] using hsel
    change 1 = actualSectorSelector σ hσ R s {b} x *
      localJetProbe compactSchwartzCutoff γ hγ 0 (labelScale s b*((((n-k target):ℤ):ℝ)+β)) x
    rw [hselone,one_mul,hxx,localJetProbe_apply,sub_self,zero_div]
    simp only [pow_zero,Nat.factorial_zero,Nat.cast_one,div_one,one_mul]
    exact (compactSchwartzCutoff_eq_one (by norm_num)).symm
  · rw [ite_eq_right hex]
    change 0 = actualSectorSelector σ hσ R s {b} x *
      localJetProbe compactSchwartzCutoff γ hγ 0 (labelScale s b*((((n-k target):ℤ):ℝ)+β)) x
    by_cases ho : origin=b
    · have hselone : actualSectorSelector σ hσ R s {b} x = 1 := by
        simpa only [ho,mem_singleton_iff,ite_true] using hsel
      rw [hselone,one_mul]
      symm
      apply localJetProbe_cutoff_zero
      have hne : x ≠ labelScale s b*((((n-k target):ℤ):ℝ)+β) := by
        intro heq
        have hcentre : labelScale s b*((((n-k target):ℤ):ℝ)+β)+catalogueShift k s = z := by
          rw [catalogueShift_single_coordinate target k s hsparse]
          dsimp only [z,catalogueTargetPoint,b,β]
          push_cast
          ring
        have heval : prefixComparisonValue target origin n n' β β' k s = 0 := by
          unfold prefixComparisonValue
          rw [catalogueTarget_scale]
          change z-x-catalogueShift k s = 0
          linarith
        have hdist := actualPrefixNonresonance_arbitrary_cutoff R M c hc s hgood L
          target j positive n hn origin j' positive' n' hcell k hk hex
        change c/(3+2*(L:ℝ))^(catalogueDistanceExponent M) ≤
          |prefixComparisonValue target origin n n' β β' k s| at hdist
        rw [heval,abs_zero] at hdist
        linarith
      have hh := hisol (n-k target) x (by simpa only [ho] using hxsec) hne
      linarith
    · have hselzero : actualSectorSelector σ hσ R s {b} x = 0 := by
        simpa only [mem_singleton_iff,ho,ite_false] using hsel
      rw [hselzero,zero_mul]


/-- One integer Fourier shift in the target generating coordinate, zero in every other coordinate. -/
def catalogueSingleShift {M : ℕ} (target : Fin M × ReciprocalSign) (l : ℤ)
    (d : Fin M × ReciprocalSign) : ℤ := if d=target then l else 0

/-- Single-coordinate shifts are injectively parametrized by their actual integer value. -/
theorem catalogueSingleShift_injective {M : ℕ} (target : Fin M × ReciprocalSign) :
    Function.Injective (catalogueSingleShift target) := by
  intro l m h
  have he := congrFun h target
  simpa only [catalogueSingleShift,ite_true] using he

/-- The one-coordinate shift is in the full finite box precisely at the usual symmetric integer cutoff. -/
theorem catalogueSingleShift_mem {M L : ℕ} (target : Fin M × ReciprocalSign) (l : ℤ) :
    catalogueSingleShift target l ∈ prefixShiftCatalogue M L ↔ l ∈ Finset.Icc (-(L:ℤ)) (L:ℤ) := by
  constructor
  · intro h
    have hh := Fintype.mem_piFinset.mp h target
    simpa only [catalogueSingleShift,ite_true] using hh
  · intro h
    apply Fintype.mem_piFinset.mpr
    intro d
    by_cases hd : d=target
    · simpa only [catalogueSingleShift,hd,ite_true] using h
    · simp only [catalogueSingleShift,hd,ite_false,Finset.mem_Icc]
      constructor <;> omega

/-- A sparse shift is exactly its single-coordinate representative. -/
theorem catalogueShift_eq_single {M : ℕ} (target : Fin M × ReciprocalSign)
    (k : Fin M × ReciprocalSign → ℤ) (hk : ∀ d, d ≠ target → k d = 0) :
    k = catalogueSingleShift target (k target) := by
  funext d
  by_cases hd : d=target
  · subst d
    simp only [catalogueSingleShift,ite_true]
  · simp only [catalogueSingleShift,hd,ite_false,hk d hd]

/-- Removing all zero nongenerating terms leaves exactly one symmetric integer sum. -/
theorem catalogue_sparse_sum {M L : ℕ} (target : Fin M × ReciprocalSign)
    (f : (Fin M × ReciprocalSign → ℤ) → ℂ)
    (hf : ∀ k ∈ prefixShiftCatalogue M L, (¬ ∀ d, d ≠ target → k d = 0) → f k = 0) :
    (∑ k ∈ prefixShiftCatalogue M L, f k) =
      ∑ l ∈ Finset.Icc (-(L:ℤ)) (L:ℤ), f (catalogueSingleShift target l) := by
  let G := (prefixShiftCatalogue M L).filter (fun k => ∀ d, d ≠ target → k d = 0)
  have he : G = (Finset.Icc (-(L:ℤ)) (L:ℤ)).image (catalogueSingleShift target) := by
    ext k
    constructor
    · intro hk
      obtain ⟨hkbox,hksparse⟩ := Finset.mem_filter.mp hk
      apply Finset.mem_image.mpr
      refine ⟨k target,Fintype.mem_piFinset.mp hkbox target,?_⟩
      exact (catalogueShift_eq_single target k hksparse).symm
    · intro hk
      obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hk
      apply Finset.mem_filter.mpr
      refine ⟨(catalogueSingleShift_mem target l).mpr hl,?_⟩
      intro d hd
      simp only [catalogueSingleShift,hd,ite_false]
  have hsum : (∑ k ∈ G, f k) = ∑ k ∈ prefixShiftCatalogue M L, f k := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro k hk hnot
    apply hf k hk
    intro hsparse
    exact hnot (Finset.mem_filter.mpr ⟨hk,hsparse⟩)
  rw [← hsum,he,Finset.sum_image]
  intro l hl m hm heq
  exact catalogueSingleShift_injective target heq

/-- Mean-one factors on all unused coordinates leave exactly the target Fourier coefficient. -/
theorem catalogue_coefficient_single {M : ℕ} (a : Fin M × ReciprocalSign → ℤ → ℂ)
    (ha : ∀ d, a d 0 = 1) (target : Fin M × ReciprocalSign) (l : ℤ) :
    (∏ d : Fin M × ReciprocalSign, a d (catalogueSingleShift target l d)) = a target l := by
  rw [Finset.prod_eq_single target]
  · simp only [catalogueSingleShift,ite_true]
  · intro d hd hne
    simp only [catalogueSingleShift,hne,ite_false,ha d]
  · simp


/-- The actual finite whole-distribution pairing is exactly the target truncated phase convolution. -/
theorem catalogue_truncated_pairing (σ : ℝ) (hσ : 0 < σ) (p : ℕ)
    (R : ℕ+ → ℕ) (M : ℕ) (c : ℝ) (hc : 0 ≤ c) (s : ℕ+ → ℝ)
    (hgood : ActualPrefixNonresonance R M c s)
    (hsep : ∀ b d : Label, b ≠ d → ∀ x ∈ sectorSet R s b,
      ∀ y ∈ sectorSet R s d, σ/(1+|x|+|y|)^6 ≤ |x-y|)
    (L : ℕ) (target : Fin M × ReciprocalSign) (j : Fin M) (positive : Bool)
    (n : ℤ) (hn : |n| ≤ M)
    (a : Fin M × ReciprocalSign → ℤ → ℂ) (ha : ∀ d, a d 0 = 1)
    (δ : ℝ) (hδ : 0 < δ)
    (hδsmall : 2*δ ≤ c/(3+2*(L:ℝ))^(catalogueDistanceExponent M))
    (γ : ℝ) (hγ : 0 < γ)
    (hisol : ∀ m : ℤ, ∀ y ∈ sectorSet R s (prefixScaleIndex target.1,target.2),
      y ≠ labelScale s (prefixScaleIndex target.1,target.2)*((m:ℝ)+
        prefixCataloguePhase (fun i => R (prefixScaleIndex i)) (target.1,j,positive)) →
      4*γ ≤ |y-labelScale s (prefixScaleIndex target.1,target.2)*((m:ℝ)+
        prefixCataloguePhase (fun i => R (prefixScaleIndex i)) (target.1,j,positive))|)
    (A : LocallyFiniteCarrier) (hA : A.carrier ⊆ carrierSet R s)
    (T : HermiteScale (-(p:ℤ))) (hT : AtomicOnCarrier A (𝓕 (hermiteScaleDistribution p T))) :
    (∑ k ∈ prefixShiftCatalogue M L,
      (∏ d, a d (k d)) • combDistributionTranslation (catalogueShift k s)
        (𝓕 (hermiteScaleDistribution p T))) (catalogueProbe R s target j positive n δ hδ) =
    ∑ l ∈ Finset.Icc (-(L:ℤ)) (L:ℤ), a target l *
      isolatedSourceCoefficient σ hσ p R s (prefixScaleIndex target.1,target.2)
        (prefixCataloguePhase (fun i => R (prefixScaleIndex i)) (target.1,j,positive))
        γ hγ T (n-l) := by
  simp only [_root_.sum_apply, _root_.smul_apply, smul_eq_mul]
  rw [catalogue_sparse_sum target]
  · apply Finset.sum_congr rfl
    intro l hl
    rw [catalogue_coefficient_single a ha target l]
    congr 1
    have hk := (catalogueSingleShift_mem target l).mpr hl
    have hsparse : ∀ d, d ≠ target → catalogueSingleShift target l d = 0 := by
      intro d hd
      simp only [catalogueSingleShift,hd,ite_false]
    simpa only [catalogueSingleShift,ite_true] using
      catalogue_generating_shift_action σ hσ p R M c hc s hgood hsep L target j
        positive n hn (catalogueSingleShift target l) hk hsparse δ hδ hδsmall
        γ hγ hisol A hA T hT
  · intro k hk hnot
    rw [catalogue_nongenerating_shift_action_zero R M c hc s hgood L target j
      positive n hn k hk hnot δ hδ hδsmall A hA _ hT, mul_zero]

/-- Actual Fourier coefficient in a signed coordinate of the finite prefix. -/
def cataloguePhaseCoefficient (R : ℕ+ → ℕ) (hR : ∀ i, 1 ≤ R i) {M : ℕ}
    (d : Fin M × ReciprocalSign) (l : ℤ) : ℂ :=
  phaseCoefficient (prefixScaleIndex d.1) (R (prefixScaleIndex d.1))
    (prefixScaleIndex d.1).property (hR _) l

/-- Every unused actual annihilator factor contributes its exact mean one. -/
theorem cataloguePhaseCoefficient_zero (R : ℕ+ → ℕ) (hR : ∀ i, 1 ≤ R i)
    {M : ℕ} (d : Fin M × ReciprocalSign) : cataloguePhaseCoefficient R hR d 0 = 1 :=
  phaseCoefficient_zero _ _ _ _


/-- The literal total-frequency cutoff used in the complete Fourier-tail bound. -/
def catalogueL1Cutoff (M L : ℕ) : Finset (Fin M × ReciprocalSign → ℤ) :=
  (prefixShiftCatalogue M L).filter (fun k => ∑ d, |(k d:ℝ)| ≤ L)

/-- Membership is exactly the literal total-frequency inequality; the
ambient coordinate box adds no extra restriction. -/
theorem mem_catalogueL1Cutoff {M L : ℕ} (k : Fin M × ReciprocalSign → ℤ) :
    k ∈ catalogueL1Cutoff M L ↔ ∑ d, |(k d:ℝ)| ≤ L := by
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro h
    apply Finset.mem_filter.mpr
    refine ⟨?_,h⟩
    apply Fintype.mem_piFinset.mpr
    intro d
    have hd : |(k d:ℝ)| ≤ L := (Finset.single_le_sum
      (fun e _ => abs_nonneg (k e:ℝ)) (Finset.mem_univ d)).trans h
    have hh := abs_le.mp hd
    apply Finset.mem_Icc.mpr
    constructor
    · exact_mod_cast hh.1
    · exact_mod_cast hh.2

/-- The total frequency of a generating shift is precisely its absolute integer value. -/
theorem catalogueSingleShift_l1 {M : ℕ} (target : Fin M × ReciprocalSign) (l : ℤ) :
    (∑ d, |(catalogueSingleShift target l d:ℝ)|) = |(l:ℝ)| := by
  rw [Finset.sum_eq_single target]
  · simp only [catalogueSingleShift,ite_true]
  · intro d hd hne
    simp only [catalogueSingleShift,hne,ite_false,Int.cast_zero,abs_zero]
  · simp

/-- Restricting from the coordinate box to the actual total-frequency cutoff
removes only terms already excluded by catalogue separation. -/
theorem catalogue_l1_sum_eq_box {M L : ℕ} (target : Fin M × ReciprocalSign)
    (f : (Fin M × ReciprocalSign → ℤ) → ℂ)
    (hf : ∀ k ∈ prefixShiftCatalogue M L, (¬ ∀ d, d ≠ target → k d = 0) → f k = 0) :
    (∑ k ∈ catalogueL1Cutoff M L, f k) = ∑ k ∈ prefixShiftCatalogue M L, f k := by
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro k hk hnot
  apply hf k hk
  intro hsparse
  apply hnot
  apply Finset.mem_filter.mpr
  refine ⟨hk,?_⟩
  rw [catalogueShift_eq_single target k hsparse,catalogueSingleShift_l1]
  have hh := Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hk target)
  rw [abs_le]
  constructor
  · exact_mod_cast hh.1
  · exact_mod_cast hh.2


/-- Exact accepted catalogue extraction for the actual mean-one annihilator
coefficients and the literal total-frequency truncation of the full product. -/
theorem catalogue_actual_truncated_pairing (σ : ℝ) (hσ : 0 < σ) (p : ℕ)
    (R : ℕ+ → ℕ) (hR : ∀ i, 1 ≤ R i) (M : ℕ) (c : ℝ) (hc : 0 ≤ c) (s : ℕ+ → ℝ)
    (hgood : ActualPrefixNonresonance R M c s)
    (hsep : ∀ b d : Label, b ≠ d → ∀ x ∈ sectorSet R s b,
      ∀ y ∈ sectorSet R s d, σ/(1+|x|+|y|)^6 ≤ |x-y|)
    (L : ℕ) (target : Fin M × ReciprocalSign) (j : Fin M) (positive : Bool)
    (n : ℤ) (hn : |n| ≤ M)
    (δ : ℝ) (hδ : 0 < δ)
    (hδsmall : 2*δ ≤ c/(3+2*(L:ℝ))^(catalogueDistanceExponent M))
    (γ : ℝ) (hγ : 0 < γ)
    (hisol : ∀ m : ℤ, ∀ y ∈ sectorSet R s (prefixScaleIndex target.1,target.2),
      y ≠ labelScale s (prefixScaleIndex target.1,target.2)*((m:ℝ)+
        prefixCataloguePhase (fun i => R (prefixScaleIndex i)) (target.1,j,positive)) →
      4*γ ≤ |y-labelScale s (prefixScaleIndex target.1,target.2)*((m:ℝ)+
        prefixCataloguePhase (fun i => R (prefixScaleIndex i)) (target.1,j,positive))|)
    (A : LocallyFiniteCarrier) (hA : A.carrier ⊆ carrierSet R s)
    (T : HermiteScale (-(p:ℤ))) (hT : AtomicOnCarrier A (𝓕 (hermiteScaleDistribution p T))) :
    (∑ k ∈ catalogueL1Cutoff M L,
      (∏ d, cataloguePhaseCoefficient R hR d (k d)) • combDistributionTranslation (catalogueShift k s)
        (𝓕 (hermiteScaleDistribution p T))) (catalogueProbe R s target j positive n δ hδ) =
    ∑ l ∈ Finset.Icc (-(L:ℤ)) (L:ℤ), cataloguePhaseCoefficient R hR target l *
      isolatedSourceCoefficient σ hσ p R s (prefixScaleIndex target.1,target.2)
        (prefixCataloguePhase (fun i => R (prefixScaleIndex i)) (target.1,j,positive))
        γ hγ T (n-l) := by
  have he := catalogue_truncated_pairing σ hσ p R M c hc s hgood hsep L target j
    positive n hn (cataloguePhaseCoefficient R hR) (cataloguePhaseCoefficient_zero R hR)
    δ hδ hδsmall γ hγ hisol A hA T hT
  simp only [_root_.sum_apply, _root_.smul_apply, smul_eq_mul] at he ⊢
  rw [catalogue_l1_sum_eq_box target]
  · exact he
  · intro k hk hnot
    rw [catalogue_nongenerating_shift_action_zero R M c hc s hgood L target j
      positive n hn k hk hnot δ hδ hδsmall A hA _ hT, mul_zero]

end
end MeyerGeneralProblem.Adaptive
