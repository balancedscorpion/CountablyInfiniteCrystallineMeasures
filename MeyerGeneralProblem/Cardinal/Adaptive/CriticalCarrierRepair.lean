module

public import MeyerGeneralProblem.Cardinal.Adaptive.CriticalNativeRepair

@[expose] public section

/-! # Exact deletion and whole critical-source repair -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open scoped FourierTransform

/-- Fixed head-only Schwartz test for one original triangular hole. -/
def criticalHoleTest {k : ℕ} (α : Fin k → ℝ) (h : TriangularHoleIndex k) : SchwartzMap ℝ ℂ :=
  (criticalHeadCosetCarrier α).isolationSchwartz
    ⟨criticalHeadPoint α h.1 h.2.1 (triangularHoleCell h),criticalHeadPoint_mem α h.1 h.2.1 _⟩

/-- The chosen head-only isolation radius is at most one because the next
integer translate of the same coset is another actual carrier point. -/
theorem criticalHeadIsolationRadius_le_one {k : ℕ} (α : Fin k → ℝ)
    (i : Fin k) (u : Bool) (n : ℤ) :
    (criticalHeadCosetCarrier α).isolationRadius
      ⟨criticalHeadPoint α i u n,criticalHeadPoint_mem α i u n⟩ ≤ 1 := by
  have he : criticalHeadPoint α i u (n+1) = criticalHeadPoint α i u n+1 := by
    simp only [criticalHeadPoint,Int.cast_add,Int.cast_one]
    ring
  have h := (criticalHeadCosetCarrier α).isolationRadius_le_dist
    ⟨criticalHeadPoint α i u n,criticalHeadPoint_mem α i u n⟩
    (criticalHeadPoint_mem α i u (n+1)) (by rw [he]; linarith)
  simpa only [he,Real.dist_eq,add_sub_cancel_left,abs_one] using h

/-- Every original forbidden head point is strictly inside the universal head window. -/
theorem criticalHolePoint_abs_lt {k : ℕ} (α : Fin k → ℝ)
    (hi : ∀ i, 0 < α i ∧ α i < 1/2) (h : TriangularHoleIndex k) :
    |criticalHeadPoint α h.1 h.2.1 (triangularHoleCell h)| < (k : ℝ)-1/2 := by
  have hn : |((triangularHoleCell h : ℤ) : ℝ)| ≤ (h.1.val : ℝ) := by
    exact_mod_cast triangularHoleCell_bound h
  have hp : |criticalSignedPhase h.2.1 (α h.1)| < 1/2 := by
    cases h.2.1 <;> simpa [criticalSignedPhase,abs_of_pos (hi h.1).1] using (hi h.1).2
  have hik : (h.1.val : ℝ)+1 ≤ k := by exact_mod_cast h.1.isLt
  have ht := abs_add_le ((triangularHoleCell h : ℤ) : ℝ) (criticalSignedPhase h.2.1 (α h.1))
  change |((triangularHoleCell h : ℤ) : ℝ)+criticalSignedPhase h.2.1 (α h.1)| < _
  linarith

/-- The head-only extraction test is zero outside the fixed head window,
independently of every phase in the infinite tail. -/
theorem criticalHoleTest_zero_of_abs_ge {k : ℕ} (α : Fin k → ℝ)
    (hi : ∀ i, 0 < α i ∧ α i < 1/2) (h : TriangularHoleIndex k)
    (x : ℝ) (hx : (k : ℝ) ≤ |x|) : criticalHoleTest α h x = 0 := by
  let z : (criticalHeadCosetCarrier α).subtype :=
    ⟨criticalHeadPoint α h.1 h.2.1 (triangularHoleCell h),criticalHeadPoint_mem α _ _ _⟩
  have hr := criticalHeadIsolationRadius_le_one α h.1 h.2.1 (triangularHoleCell h)
  have hz := criticalHolePoint_abs_lt α hi h
  have hd : 1/2 ≤ dist x (z : ℝ) := by
    have ht := abs_sub_le x (z : ℝ) 0
    simp only [sub_zero] at ht
    have ht' : |x| ≤ |x-(z : ℝ)|+|(z : ℝ)| := by
      have h := abs_add_le (x-(z : ℝ)) (z : ℝ)
      simpa using h
    rw [Real.dist_eq]
    change |criticalHeadPoint α h.1 h.2.1 (triangularHoleCell h)| < _ at hz
    change |x| ≤ |x-criticalHeadPoint α h.1 h.2.1 (triangularHoleCell h)|+
      |criticalHeadPoint α h.1 h.2.1 (triangularHoleCell h)| at ht'
    dsimp [z]
    linarith
  change (((criticalHeadCosetCarrier α).isolationBump z x : ℝ) : ℂ)=0
  rw [((criticalHeadCosetCarrier α).isolationBump z).zero_of_le_dist]
  · norm_num
  · change (criticalHeadCosetCarrier α).isolationRadius z/2 ≤ dist x (z : ℝ)
    exact (show (criticalHeadCosetCarrier α).isolationRadius z/2 ≤ 1/2 by dsimp [z]; linarith).trans hd

/-- Every restored infinite tail lies beyond the universal finite head window. -/
theorem criticalPhaseTail_abs_lower (α : ℕ+ → ℝ)
    (hi : ∀ j, 0 < α j ∧ α j < 1/2) (k : ℕ) {x : ℝ}
    (hx : x ∈ criticalPhaseTailSet α k k) : (k : ℝ)+1/2 < |x| := by
  obtain ⟨j,u,n,hn,rfl⟩ := hx
  have hp := criticalTailPhase_abs_lt_half α hi k j u
  have hnj : ((j : ℕ) : ℝ)+(k : ℝ) ≤ |(n : ℝ)| := by
    have hc : (((j : ℕ)+k : ℕ) : ℝ) ≤ (n.natAbs : ℝ) := by exact_mod_cast hn
    simpa using hc
  have hj : (1 : ℝ) ≤ (j : ℕ) := by exact_mod_cast j.pos
  have ht := abs_add_le ((n : ℝ)+signedPhase u (criticalTailPhases α k j))
    (-signedPhase u (criticalTailPhases α k j))
  simp only [add_neg_cancel_right,abs_neg] at ht
  linarith

/-- The head-only extraction tests vanish on the entire original restored tail. -/
theorem criticalHoleTest_zero_on_tail (α : ℕ+ → ℝ)
    (hi : ∀ j, 0 < α j ∧ α j < 1/2) (k : ℕ)
    (h : TriangularHoleIndex k) (x : ℝ) (hx : x ∈ criticalPhaseTailSet α k k) :
    criticalHoleTest (criticalPrefixPhases α k) h x = 0 :=
  criticalHoleTest_zero_of_abs_ge _ (criticalPrefixPhases_inside α hi k) h x
    (by have := criticalPhaseTail_abs_lower α hi k hx; linarith)

/-- The finite original triangular hole set, with both signs and equality endpoints. -/
def criticalHoleSet {k : ℕ} (α : Fin k → ℝ) : Set ℝ :=
  Set.range (fun h : TriangularHoleIndex k => criticalHeadPoint α h.1 h.2.1 (triangularHoleCell h))

/-- The fixed head-only test extracts the actual coefficient even in the
complete restored carrier. This equality removes all tail dependence from repair norms. -/
theorem criticalHoleTest_extracts_restored (α : ℕ+ → ℝ)
    (hi : ∀ j, 0 < α j ∧ α j < 1/2) (k : ℕ) (h : TriangularHoleIndex k)
    (T : TemperedDistribution ℝ ℂ) (hT : AtomicOnCarrier (criticalRestoredPhaseCarrier α hi k) T) :
    T ((criticalRestoredPhaseCarrier α hi k).isolationSchwartz
      ⟨criticalHeadPoint (criticalPrefixPhases α k) h.1 h.2.1 (triangularHoleCell h),
        Or.inl (criticalHeadPoint_mem _ _ _ _)⟩) = T (criticalHoleTest (criticalPrefixPhases α k) h) := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply hT
  intro y hy
  simp only [_root_.sub_apply]
  by_cases he : y=criticalHeadPoint (criticalPrefixPhases α k) h.1 h.2.1 (triangularHoleCell h)
  · subst y
    rw [LocallyFiniteCarrier.isolationSchwartz_self]
    change 1-(criticalHeadCosetCarrier (criticalPrefixPhases α k)).isolationSchwartz _ _=0
    rw [LocallyFiniteCarrier.isolationSchwartz_self,sub_self]
  · rw [LocallyFiniteCarrier.isolationSchwartz_of_mem_of_ne _ _ hy he]
    have hz : criticalHoleTest (criticalPrefixPhases α k) h y = 0 := by
      rcases hy with hy|hy
      · exact (criticalHeadCosetCarrier (criticalPrefixPhases α k)).isolationSchwartz_of_mem_of_ne _ hy he
      · exact criticalHoleTest_zero_on_tail α hi k h y hy
    rw [hz,sub_self]

/-- Removing the original finite holes from the restored carrier leaves only
points of the actual original critical schedule. -/
theorem criticalRestored_delete_subset_original (α : ℕ+ → ℝ)
    (hi : ∀ j, 0 < α j ∧ α j < 1/2) (k : ℕ) :
    (deleteCarrier (criticalRestoredPhaseCarrier α hi k)
      (criticalHoleSet (criticalPrefixPhases α k))).carrier ⊆
      (criticalPhaseTailCarrier α hi 0 0).carrier := by
  rintro x ⟨hx,hnot⟩
  rcases hx with hx|hx
  · obtain ⟨i,u,n,rfl⟩ := hx
    have hn : (i.val+1 : ℕ) ≤ n.natAbs := by
      by_contra hn
      have hn' : |n| ≤ (i : ℤ) := by
        have habs : (n.natAbs : ℤ)=|n| := Int.natCast_natAbs n
        omega
      obtain ⟨h,hi',hu,he⟩ := triangularHoleCell_surjective i (!u) n hn'
      apply hnot
      refine ⟨h,?_⟩
      simp only [criticalHeadPoint,hi',hu,he,signedPhase_eq_criticalSignedPhase]
    refine ⟨⟨i.val+1,by omega⟩,u,n,by simpa using hn,?_⟩
    simp only [criticalTailPhases_zero,criticalPrefixPhases]
  · exact criticalPhaseTailSet_restored_subset α k hx

/-- Vanishing of the actual finite head-only observations gives the complete
original critical source, by exact coefficient deletion on the restored carrier. -/
theorem criticalRestored_atomic_of_holes_zero (α : ℕ+ → ℝ)
    (hi : ∀ j, 0 < α j ∧ α j < 1/2) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ) (hT : AtomicOnCarrier (criticalRestoredPhaseCarrier α hi k) T)
    (hz : ∀ h : TriangularHoleIndex k, T (criticalHoleTest (criticalPrefixPhases α k) h)=0) :
    AtomicOnCarrier (criticalPhaseTailCarrier α hi 0 0) T := by
  have hd : AtomicOnCarrier (deleteCarrier (criticalRestoredPhaseCarrier α hi k)
      (criticalHoleSet (criticalPrefixPhases α k))) T := by
    apply (atomicOn_deleteCarrier_iff _ _ _).mpr
    refine ⟨hT,?_⟩
    rintro x ⟨h,he⟩
    have hh := criticalHoleTest_extracts_restored α hi k h T hT
    have heq : x = ⟨criticalHeadPoint (criticalPrefixPhases α k) h.1 h.2.1 (triangularHoleCell h),
        Or.inl (criticalHeadPoint_mem _ _ _ _)⟩ := Subtype.ext he.symm
    rw [heq,hh,hz h]
  intro f hf
  exact hd f (fun x hx => hf x (criticalRestored_delete_subset_original α hi k hx))


/-- The actual whole repaired inverse maps complete infinite scheduled tails
into the original critical carriers on both the physical and Fourier sides. -/
theorem criticalRepairedDistribution_atomic_records (α β : ℕ+ → ℝ)
    (ha : Function.Injective α) (hia : ∀ j, 0 < α j ∧ α j < 1/2)
    (hb : Function.Injective β) (hib : ∀ j, 0 < β j ∧ β j < 1/2) (k : ℕ) (hk : 1 ≤ k)
    (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier (criticalPhaseTailCarrier α hia k 0) T)
    (hFT : AtomicOnCarrier (criticalPhaseTailCarrier β hib k 0) (𝓕 T)) :
    let Q := criticalRepairedDistributionLM (criticalPrefixPhases α k) (criticalPrefixPhases β k)
      (criticalPrefixPhases_injective α ha k) (criticalPrefixPhases_inside α hia k)
      (criticalPrefixPhases_injective β hb k) (criticalPrefixPhases_inside β hib k)
    AtomicOnCarrier (criticalPhaseTailCarrier α hia 0 0) (Q T) ∧
    AtomicOnCarrier (criticalPhaseTailCarrier β hib 0 0) (𝓕 (Q T)) := by
  let a := criticalPrefixPhases α k
  let b := criticalPrefixPhases β k
  let ia := criticalPrefixPhases_injective α ha k
  let ib := criticalPrefixPhases_injective β hb k
  let pa := criticalPrefixPhases_inside α hia k
  let pb := criticalPrefixPhases_inside β hib k
  let V := criticalFullPreinverseCLM α β ha hia hb hib k T
  let C := criticalPoissonCorrection a b ia pa ib pb (criticalHeadCosetCarrier a)
    (criticalHeadCosetCarrier b) (criticalHeadCosetCarrier_contains a) (criticalHeadCosetCarrier_contains b) V
  have hv := criticalFullPreinverse_atomic_records α β ha hia hb hib k hk T hT hFT
  have hc : AtomicOnCarrier (criticalHeadCosetCarrier a) C ∧
      AtomicOnCarrier (criticalHeadCosetCarrier b) (𝓕 C) :=
    criticalPoissonSynthesis_atomic_records a b _
  have hz := criticalPoissonCorrection_holes_zero a b ia pa ib pb
    (criticalHeadCosetCarrier a) (criticalHeadCosetCarrier b)
    (criticalHeadCosetCarrier_contains a) (criticalHeadCosetCarrier_contains b) V
  change AtomicOnCarrier (criticalPhaseTailCarrier α hia 0 0) (V-C) ∧
    AtomicOnCarrier (criticalPhaseTailCarrier β hib 0 0) (𝓕 (V-C))
  constructor
  · apply criticalRestored_atomic_of_holes_zero α hia k (V-C)
    · intro f hf
      change V f-C f=0
      rw [hv.1 f hf,hc.1 f (fun x hx => hf x (Or.inl hx)),sub_self]
    · intro h
      exact congrFun hz (Sum.inl h)
  · apply criticalRestored_atomic_of_holes_zero β hib k (𝓕 (V-C))
    · intro f hf
      change temperedFourierLinearMap (V-C) f=0
      rw [map_sub]
      change (𝓕 V) f-(𝓕 C) f=0
      rw [hv.2 f hf,hc.2 f (fun x hx => hf x (Or.inl hx)),sub_self]
    · intro h
      exact congrFun hz (Sum.inr h)

/-- Complete native critical-source right inverse with exactly two orders of
loss. The actual operator and its bound depend only on the finite prefixes. -/
theorem criticalRepairedNative_source_bound (α β : ℕ+ → ℝ)
    (ha : Function.Injective α) (hia : ∀ j, 0 < α j ∧ α j < 1/2)
    (hb : Function.Injective β) (hib : ∀ j, 0 < β j ∧ β j < 1/2) (k p : ℕ) (hk : 1 ≤ k) :
    ∃ C > 0, ∀ T : HermiteScale (-(p : ℤ)),
      AtomicOnCarrier (criticalPhaseTailCarrier α hia k 0) (hermiteScaleDistribution p T) →
      AtomicOnCarrier (criticalPhaseTailCarrier β hib k 0) (𝓕 (hermiteScaleDistribution p T)) →
      ∃ U : HermiteScale (-((p+2 : ℕ) : ℤ)), ‖U‖ ≤ C*‖T‖ ∧
        AtomicOnCarrier (criticalPhaseTailCarrier α hia 0 0) (hermiteScaleDistribution (p+2) U) ∧
        AtomicOnCarrier (criticalPhaseTailCarrier β hib 0 0) (𝓕 (hermiteScaleDistribution (p+2) U)) ∧
        criticalHeadMultiplierDistributionCLM (criticalPrefixPhases α k)
          (criticalHeadDifferenceDistributionCLM (criticalPrefixPhases β k)
            (hermiteScaleDistribution (p+2) U))=hermiteScaleDistribution p T := by
  let a := criticalPrefixPhases α k
  let b := criticalPrefixPhases β k
  let ia := criticalPrefixPhases_injective α ha k
  let ib := criticalPrefixPhases_injective β hb k
  let pa := criticalPrefixPhases_inside α hia k
  let pb := criticalPrefixPhases_inside β hib k
  obtain ⟨C,hC,hbound⟩ := criticalRepairedNativeCLM_bound a b ia pa ib pb p
  refine ⟨C,hC,fun T hT hFT => ⟨criticalRepairedNativeCLM a b ia pa ib pb p T,hbound T,?_⟩⟩
  rw [criticalRepairedNativeCLM_realizes]
  have h := criticalRepairedDistribution_atomic_records α β ha hia hb hib k hk
    (hermiteScaleDistribution p T) hT hFT
  exact ⟨h.1,h.2,criticalRepairedDistribution_rightInverse hk a b ia pa ib pb _⟩


/-- The complete actual critical tail source in the original native order,
without a finite-cap or phasewise representation restriction. -/
def criticalOriginalNativeSource (α β : ℕ+ → ℝ)
    (hia : ∀ j, 0 < α j ∧ α j < 1/2) (hib : ∀ j, 0 < β j ∧ β j < 1/2) (k p : ℕ) :
    Submodule ℂ (TemperedDistribution ℝ ℂ) :=
  pairedAtomicSource (criticalPhaseTailCarrier α hia k 0) (criticalPhaseTailCarrier β hib k 0) ⊓
    originalNativeDistributionSpace p

/-- The actual repaired operator preserves both complete source conditions
and lands in precisely the original native layer two orders higher. -/
theorem criticalRepairedDistribution_maps_native_source (α β : ℕ+ → ℝ)
    (ha : Function.Injective α) (hia : ∀ j, 0 < α j ∧ α j < 1/2)
    (hb : Function.Injective β) (hib : ∀ j, 0 < β j ∧ β j < 1/2) (k p : ℕ) (hk : 1 ≤ k)
    (T : TemperedDistribution ℝ ℂ) (hT : T ∈ criticalOriginalNativeSource α β hia hib k p) :
    criticalRepairedDistributionLM (criticalPrefixPhases α k) (criticalPrefixPhases β k)
      (criticalPrefixPhases_injective α ha k) (criticalPrefixPhases_inside α hia k)
      (criticalPrefixPhases_injective β hb k) (criticalPrefixPhases_inside β hib k) T ∈
      criticalOriginalNativeSource α β hia hib 0 (p+2) := by
  refine ⟨criticalRepairedDistribution_atomic_records α β ha hia hb hib k hk T hT.1.1 hT.1.2,?_⟩
  obtain ⟨u,hu⟩ := hT.2
  refine ⟨criticalRepairedNativeCLM (criticalPrefixPhases α k) (criticalPrefixPhases β k)
    (criticalPrefixPhases_injective α ha k) (criticalPrefixPhases_inside α hia k)
    (criticalPrefixPhases_injective β hb k) (criticalPrefixPhases_inside β hib k) p u,?_⟩
  change hermiteScaleDistribution (p+2) _ = _
  rw [criticalRepairedNativeCLM_realizes]
  exact congrArg _ hu

/-- Linear injection from the complete infinite tail into the complete original
critical source, with an order loss independent of the head length. -/
def criticalNativeSourceInjection (α β : ℕ+ → ℝ)
    (ha : Function.Injective α) (hia : ∀ j, 0 < α j ∧ α j < 1/2)
    (hb : Function.Injective β) (hib : ∀ j, 0 < β j ∧ β j < 1/2) (k p : ℕ) (hk : 1 ≤ k) :
    criticalOriginalNativeSource α β hia hib k p →ₗ[ℂ]
      criticalOriginalNativeSource α β hia hib 0 (p+2) :=
  ((criticalRepairedDistributionLM (criticalPrefixPhases α k) (criticalPrefixPhases β k)
    (criticalPrefixPhases_injective α ha k) (criticalPrefixPhases_inside α hia k)
    (criticalPrefixPhases_injective β hb k) (criticalPrefixPhases_inside β hib k)).comp
      (criticalOriginalNativeSource α β hia hib k p).subtype).codRestrict _
        (fun T => criticalRepairedDistribution_maps_native_source α β ha hia hb hib k p hk T T.property)

/-- Injectivity is obtained from the actual whole product identity. -/
theorem criticalNativeSourceInjection_injective (α β : ℕ+ → ℝ)
    (ha : Function.Injective α) (hia : ∀ j, 0 < α j ∧ α j < 1/2)
    (hb : Function.Injective β) (hib : ∀ j, 0 < β j ∧ β j < 1/2) (k p : ℕ) (hk : 1 ≤ k) :
    Function.Injective (criticalNativeSourceInjection α β ha hia hb hib k p hk) := by
  intro T U h
  apply Subtype.ext
  exact criticalRepairedDistribution_injective hk _ _ _ _ _ _ (congrArg Subtype.val h)

/-- Actual critical tail rank comparison with exactly two original orders of
loss, valid for every infinite injective strictly interior phase schedule. -/
theorem criticalNativeSource_rank_le (α β : ℕ+ → ℝ)
    (ha : Function.Injective α) (hia : ∀ j, 0 < α j ∧ α j < 1/2)
    (hb : Function.Injective β) (hib : ∀ j, 0 < β j ∧ β j < 1/2) (k p : ℕ) (hk : 1 ≤ k) :
    Module.rank ℂ (criticalOriginalNativeSource α β hia hib k p) ≤
      Module.rank ℂ (criticalOriginalNativeSource α β hia hib 0 (p+2)) :=
  (criticalNativeSourceInjection α β ha hia hb hib k p hk).rank_le_of_injective
    (criticalNativeSourceInjection_injective α β ha hia hb hib k p hk)


/-- The rank comparison also includes the empty head, where original native
layer inclusion gives the result directly. -/
theorem criticalNativeSource_rank_le_all (α β : ℕ+ → ℝ)
    (ha : Function.Injective α) (hia : ∀ j, 0 < α j ∧ α j < 1/2)
    (hb : Function.Injective β) (hib : ∀ j, 0 < β j ∧ β j < 1/2) (k p : ℕ) :
    Module.rank ℂ (criticalOriginalNativeSource α β hia hib k p) ≤
      Module.rank ℂ (criticalOriginalNativeSource α β hia hib 0 (p+2)) := by
  by_cases hk : 1 ≤ k
  · exact criticalNativeSource_rank_le α β ha hia hb hib k p hk
  · have hk0 : k=0 := by omega
    subst k
    apply Submodule.rank_mono
    exact inf_le_inf_left _ (originalNativeDistributionSpace_mono (by omega))

end
end MeyerGeneralProblem.Adaptive
