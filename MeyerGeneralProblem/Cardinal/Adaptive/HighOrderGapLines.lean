module

public import MeyerGeneralProblem.Cardinal.Adaptive.RapidCompleteLine

@[expose] public section

/-! # Complete high-gap block lines in the original native scale -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section

/-- The full original gapped block is finite dimensional by the constructed
whole-source bijection to its rapid tail. -/
theorem actualBlockCompleteSource_finite (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) :
    Module.Finite ℂ (actualBlockCompleteSource P R hP hR) := by
  let := actualRapidCompleteSource_finite P R hP hR
  exact Module.Finite.of_injective (actualBlockRapidEquiv P R hP hR).toLinearMap
    (actualBlockRapidEquiv P R hP hR).injective

/-- The complete actual high-gap block has complex dimension at most one. -/
theorem actualBlockCompleteSource_finrank_le_one (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) :
    Module.finrank ℂ (actualBlockCompleteSource P R hP hR) ≤ 1 := by
  rw [(actualBlockRapidEquiv P R hP hR).finrank_eq]
  exact actualRapidCompleteSource_finrank_le_one P R hP hR

/-- Each original native layer is a genuine finite-dimensional subspace of
the complete block, including order zero. -/
theorem actualBlockNativeSource_finite (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) (p : ℕ) :
    Module.Finite ℂ (actualBlockNativeSource P R hP hR p) := by
  let := actualBlockCompleteSource_finite P R hP hR
  let f : actualBlockNativeSource P R hP hR p →ₗ[ℂ] actualBlockCompleteSource P R hP hR :=
    Submodule.inclusion (show actualBlockNativeSource P R hP hR p ≤ actualBlockCompleteSource P R hP hR from inf_le_left)
  exact Module.Finite.of_injective f (Submodule.inclusion_injective _)

/-- Every actual original native layer has dimension at most one. -/
theorem actualBlockNativeSource_finrank_le_one (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) (p : ℕ) :
    Module.finrank ℂ (actualBlockNativeSource P R hP hR p) ≤ 1 := by
  let := actualBlockCompleteSource_finite P R hP hR
  let f : actualBlockNativeSource P R hP hR p →ₗ[ℂ] actualBlockCompleteSource P R hP hR :=
    Submodule.inclusion (show actualBlockNativeSource P R hP hR p ≤ actualBlockCompleteSource P R hP hR from inf_le_left)
  exact (LinearMap.finrank_le_finrank_of_injective (f := f) (Submodule.inclusion_injective _)).trans
    (actualBlockCompleteSource_finrank_le_one P R hP hR)

/-- Every actual block source is a scalar multiple of any nonzero actual block
source, through the constructed whole-source rapid equivalence. -/
theorem actualBlockCompleteSource_eq_scalar (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R)
    (T U : actualBlockCompleteSource P R hP hR) (hU : U ≠ 0) : ∃ c : ℂ, T=c • U := by
  let E := actualBlockRapidEquiv P R hP hR
  have hn : E U ≠ 0 := by
    intro hz
    apply hU
    apply E.injective
    simpa only [map_zero] using hz
  have hh := actualSmallTail_eq_scalar (rapidTailPhase P R) (rapidTailPhase P R)
    (rapidTailPhase_inside P R hP hR) (rapidTailPhase_inside P R hP hR)
    (rapidTailPhase_small P R hP hR) (rapidTailPhase_small P R hP hR) (E T) (E U) hn
  refine ⟨actualSmallTailZeroth (rapidTailPhase P R) (rapidTailPhase P R)
    (rapidTailPhase_inside P R hP hR) (rapidTailPhase_inside P R hP hR) (E T) /
    actualSmallTailZeroth (rapidTailPhase P R) (rapidTailPhase P R)
    (rapidTailPhase_inside P R hP hR) (rapidTailPhase_inside P R hP hR) (E U), ?_⟩
  apply E.injective
  rw [map_smul]
  apply Subtype.ext
  exact congrArg (fun V : criticalCompleteSource (rapidTailPhase P R) (rapidTailPhase P R)
    (rapidTailPhase_inside P R hP hR) (rapidTailPhase_inside P R hP hR) 0 =>
      (V : TemperedDistribution ℝ ℂ)) hh

/-- An actual nonzero native rapid vector produces an actual nonzero block
vector with precisely two additional original orders. -/
theorem actualBlockNative_nonzero_of_rapid (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) (p : ℕ)
    (h : ∃ T ∈ actualRapidNativeSource P R hP hR p, T ≠ 0) :
    ∃ T ∈ actualBlockNativeSource P R hP hR (p+2), T ≠ 0 := by
  obtain ⟨T,hT,hne⟩ := h
  have hp : 0 < Module.rank ℂ (actualRapidNativeSource P R hP hR p) := by
    apply rank_pos_iff_exists_ne_zero.mpr
    refine ⟨⟨T,hT⟩,?_⟩
    intro he
    exact hne (congrArg Subtype.val he)
  exact exists_mem_ne_zero_of_rank_pos
    (hp.trans_le (actualRapidNative_rank_le_block P R hP hR p))

/-- A proved zero native rapid layer forces the actual same-order block layer
to vanish, by the complete original-order forward map. -/
theorem actualBlockNative_zero_of_rapid (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R)
    (p : ℕ) (hp : 1 ≤ p) (hz : actualRapidNativeSource P R hP hR p=⊥) :
    actualBlockNativeSource P R hP hR p=⊥ := by
  have h := actualBlockNative_rank_le_rapid P R hP hR p hp
  rw [hz,rank_bot] at h
  have hr : Module.rank ℂ (actualBlockNativeSource P R hP hR p)=0 := le_antisymm h (by simp)
  have hh := rank_zero_iff_forall_zero.mp hr
  apply (Submodule.eq_bot_iff _).mpr
  intro T hT
  exact congrArg Subtype.val (hh ⟨T,hT⟩)

/-- The complete original gapped block is exactly one complex line, by its
constructed equivalence to the actual nonzero rapid source. -/
theorem actualBlockCompleteSource_finrank_eq_one (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) :
    Module.finrank ℂ (actualBlockCompleteSource P R hP hR)=1 := by
  rw [(actualBlockRapidEquiv P R hP hR).finrank_eq]
  exact actualRapidCompleteSource_finrank_eq_one P R hP hR

/-- Every positive original native block layer through P vanishes. -/
theorem actualBlockNativeSource_eq_bot (P R p : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R)
    (hp : 1 ≤ p) (hpP : p ≤ P) : actualBlockNativeSource P R hP hR p=⊥ :=
  actualBlockNative_zero_of_rapid P R hP hR p hp (actualRapidNativeSource_eq_bot P R p hP hR hpP)

/-- Order zero also vanishes by its literal inclusion in the first original layer. -/
theorem actualBlockNativeSource_zero_eq_bot (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) :
    actualBlockNativeSource P R hP hR 0=⊥ := by
  apply le_antisymm _ bot_le
  calc
    actualBlockNativeSource P R hP hR 0 ≤ actualBlockNativeSource P R hP hR 1 :=
      inf_le_inf_left _ (originalNativeDistributionSpace_mono (by omega))
    _ = ⊥ := actualBlockNativeSource_eq_bot P R 1 hP hR le_rfl hP

/-- A genuine high-gap generator exists in original order18P+4 and spans the
entire actual block source. Its construction uses the actual native weak limit
and exact finite-head transport with precisely two additional orders. -/
theorem exists_actualHighGapGenerator (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) :
    ∃ μ : TemperedDistribution ℝ ℂ, μ ≠ 0 ∧
      μ ∈ actualBlockCompleteSource P R hP hR ∧
      μ ∈ originalNativeDistributionSpace (18*P+4) ∧
      ∀ T ∈ actualBlockCompleteSource P R hP hR, ∃ c : ℂ, T=c • μ := by
  have hh := actualBlockNative_nonzero_of_rapid P R hP hR (18*P+2)
    (actualRapidNativeSource_nonzero P R hP hR)
  have he : 18*P+2+2=18*P+4 := by omega
  rw [he] at hh
  obtain ⟨μ,hμ,hne⟩ := hh
  refine ⟨μ,hne,hμ.1,hμ.2,?_⟩
  intro T hT
  have hu : (⟨μ,hμ.1⟩ : actualBlockCompleteSource P R hP hR) ≠ 0 := by
    intro he
    exact hne (congrArg Subtype.val he)
  obtain ⟨c,hc⟩ := actualBlockCompleteSource_eq_scalar P R hP hR ⟨T,hT⟩ ⟨μ,hμ.1⟩ hu
  exact ⟨c,congrArg Subtype.val hc⟩

/-- No nonzero member of the whole block line occurs at an excluded original
order; the assertion concerns the original distributional native range. -/
theorem actualHighGap_not_native (P R p : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) (hpP : p ≤ P)
    (T : TemperedDistribution ℝ ℂ) (hT : T ∈ actualBlockCompleteSource P R hP hR) (hne : T ≠ 0) :
    T ∉ originalNativeDistributionSpace p := by
  intro hn
  have hz : actualBlockNativeSource P R hP hR p=⊥ := by
    by_cases hp : p=0
    · subst p; exact actualBlockNativeSource_zero_eq_bot P R hP hR
    · exact actualBlockNativeSource_eq_bot P R p hP hR (by omega) hpP
  have hm : T ∈ actualBlockNativeSource P R hP hR p := ⟨hT,hn⟩
  rw [hz,Submodule.mem_bot] at hm
  exact hne hm

end
end MeyerGeneralProblem.Adaptive
