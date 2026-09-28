module

public import MeyerGeneralProblem.Cardinal.Adaptive.ActualSmallTailUniqueness
public import MeyerGeneralProblem.Cardinal.Adaptive.BlockTailEquivalence
public import MeyerGeneralProblem.Cardinal.Adaptive.RapidNativeAdmission
public import MeyerGeneralProblem.Cardinal.Adaptive.RapidNativeExclusion

@[expose] public section

/-! # The complete literal rapid critical source is a line -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section

/-- Every literal rapid phase lies inside the proved full-source uniqueness window. -/
theorem rapidTailPhase_small (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) (j : ℕ+) :
    |1/2-rapidTailPhase P R j| ≤ 1/549755813888 := by
  have hp := (rapidDistance_bounds hP hR (j:ℕ)).1.le
  have hs := rapidDistance_le_small_constant hP hR (j:ℕ)
  simpa only [rapidTailPhase,sub_sub_cancel,abs_of_nonneg hp] using hs.trans (by norm_num)

/-- The literal original rapid source has its actual injective compact zeroth reading. -/
theorem actualRapid_zeroth_injective (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) :
    Function.Injective (actualSmallTailZeroth (rapidTailPhase P R) (rapidTailPhase P R)
      (rapidTailPhase_inside P R hP hR) (rapidTailPhase_inside P R hP hR)) :=
  actualSmallTailZeroth_injective _ _ _ _ (rapidTailPhase_small P R hP hR) (rapidTailPhase_small P R hP hR)

/-- The entire original rapid source is finite dimensional, without a native-order premise. -/
theorem actualRapidCompleteSource_finite (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) :
    Module.Finite ℂ (actualRapidCompleteSource P R hP hR) :=
  actualSmallTail_finite _ _ _ _ (rapidTailPhase_small P R hP hR) (rapidTailPhase_small P R hP hR)

/-- Complete rapid-source upper dimension, including both infinite arms and all original jets. -/
theorem actualRapidCompleteSource_finrank_le_one (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) :
    Module.finrank ℂ (actualRapidCompleteSource P R hP hR) ≤ 1 :=
  actualSmallTail_finrank_le_one _ _ _ _ (rapidTailPhase_small P R hP hR) (rapidTailPhase_small P R hP hR)

/-- The constructed actual weak-limit source closes the complete rapid line,
with no nonzero-source hypothesis or native certificate. -/
theorem actualRapidCompleteSource_finrank_eq_one (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) :
    Module.finrank ℂ (actualRapidCompleteSource P R hP hR)=1 := by
  obtain ⟨T,hT,hne⟩ := actualRapidNativeSource_nonzero P R hP hR
  apply actualSmallTail_finrank_eq_one (rapidTailPhase P R) (rapidTailPhase P R)
    (rapidTailPhase_inside P R hP hR) (rapidTailPhase_inside P R hP hR)
    (rapidTailPhase_small P R hP hR) (rapidTailPhase_small P R hP hR) ⟨T,hT.1⟩
  intro he
  exact hne (congrArg Subtype.val he)

/-- The actual low original-native rapid layers vanish by the full
variable-weight source exclusion theorem, including order zero. -/
theorem actualRapidNativeSource_eq_bot (P R p : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) (hp : p ≤ P) :
    actualRapidNativeSource P R hP hR p=⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro T hT
  obtain ⟨v,hv⟩ := hT.2
  have hrecords := hT.1
  have hd : hermiteScaleDistribution p v=T := hv
  have hzero := rapidNativeSource_eq_zero P R p hP hR hp v
    (by rw [hd]; exact hrecords.1) (by rw [hd]; exact hrecords.2)
  rw [←hd,hzero]
  exact map_zero (hermiteScaleDistributionCLM p)

end
end MeyerGeneralProblem.Adaptive
