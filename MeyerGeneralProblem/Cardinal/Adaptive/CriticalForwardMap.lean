module

public import MeyerGeneralProblem.Cardinal.Adaptive.FiniteHeadExhaustion

@[expose] public section

/-! # Complete critical forward transport and original native realization -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open scoped BigOperators FourierTransform

/-- The literal finite critical difference transports the restored scheduled
tail into the reindexed original schedule. -/
theorem criticalHeadDifference_restored_to_tail {k : ℕ} (β : Fin k → ℝ)
    (α : ℕ+ → ℝ) (hia : ∀ j, 0 < α j ∧ α j < 1/2)
    (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier (criticalPhaseTailCarrier α hia k k) T) :
    AtomicOnCarrier (criticalPhaseTailCarrier α hia k 0)
      (criticalHeadDifferenceDistributionCLM β T) := by
  intro f hf
  change T (criticalHeadDifferenceTestCLM β f)=0
  apply hT
  rintro x ⟨j,u,n,hn,rfl⟩
  rw [criticalHeadDifferenceTestCLM_apply]
  apply Finset.sum_eq_zero
  intro i _
  have hi : i.val ≤ 2*k := by
    have hh := i.isLt
    simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool] at hh
    omega
  let l : ℤ := (i.val : ℤ)-(k : ℤ)
  have hl : |l| ≤ (k : ℤ) := by
    apply abs_le.mpr
    dsimp [l]
    constructor <;> omega
  have hnj : (j : ℤ)+(k : ℤ) ≤ |n| := by
    rw [← Int.natCast_natAbs n]
    exact_mod_cast hn
  have htri := abs_add_le (n+l) (-l)
  simp only [add_neg_cancel_right,abs_neg] at htri
  have hnew : (j : ℕ)+0 ≤ (n+l).natAbs := by
    have hnat := Int.natCast_natAbs (n+l)
    have h : (j : ℤ) ≤ |n+l| := by omega
    rw [← hnat] at h
    simpa only [add_zero] using (show (j : ℕ) ≤ (n+l).natAbs by exact_mod_cast h)
  have hz := hf ((n+l : ℤ)+signedPhase u (criticalTailPhases α k j)) ⟨j,u,n+l,hnew,rfl⟩
  have he : (n : ℝ)+signedPhase u (criticalTailPhases α k j)+
      (((i.val : ℤ)-(k : ℤ) : ℤ) : ℝ)=((n+l : ℤ) : ℝ)+signedPhase u (criticalTailPhases α k j) := by
    simp only [l,Int.cast_add,Int.cast_sub]
    ring
  rw [he,hz,mul_zero]

/-- The actual full critical product maps complete original paired sources
into the complete reindexed pair, before any native-layer restriction. -/
theorem criticalProduct_maps_source (α β : ℕ+ → ℝ)
    (hia : ∀ j, 0 < α j ∧ α j < 1/2) (hib : ∀ j, 0 < β j ∧ β j < 1/2)
    (k : ℕ) (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier (criticalPhaseTailCarrier α hia 0 0) T)
    (hFT : AtomicOnCarrier (criticalPhaseTailCarrier β hib 0 0) (𝓕 T)) :
    let U := criticalHeadMultiplierDistributionCLM (criticalPrefixPhases α k)
      (criticalHeadDifferenceDistributionCLM (criticalPrefixPhases β k) T)
    AtomicOnCarrier (criticalPhaseTailCarrier α hia k 0) U ∧
    AtomicOnCarrier (criticalPhaseTailCarrier β hib k 0) (𝓕 U) := by
  constructor
  · rw [criticalHeadMultiplier_difference_commute]
    exact criticalHeadDifference_restored_to_tail _ α hia _
      (criticalPrefixMultiplier_original_tail α hia k T hT)
  · rw [fourier_criticalHeadMultiplierDistribution,fourier_criticalHeadDifferenceDistribution]
    exact criticalHeadDifference_restored_to_tail _ β hib _
      (criticalPrefixMultiplier_original_tail β hib k (𝓕 T) hFT)

/-- Actual same-order native realization of the finite critical difference. -/
def criticalHeadDifferenceNativeCLM {k : ℕ} (α : Fin k → ℝ) (p : ℕ) :
    HermiteScale (-(p : ℤ)) →L[ℂ] HermiteScale (-(p : ℤ)) :=
  ∑ i : Fin (Fintype.card (Fin k × Bool)+1), criticalHeadDifferenceCoeff α i •
    nativeTranslation p (((i.val : ℤ)-(k : ℤ) : ℤ) : ℝ)

/-- Equality with the complete difference distribution on every Schwartz test. -/
theorem criticalHeadDifferenceNativeCLM_realizes {k : ℕ} (α : Fin k → ℝ) (p : ℕ)
    (T : HermiteScale (-(p : ℤ))) :
    hermiteScaleDistribution p (criticalHeadDifferenceNativeCLM α p T)=
      criticalHeadDifferenceDistributionCLM α (hermiteScaleDistribution p T) := by
  change hermiteScaleDistributionCLM p (criticalHeadDifferenceNativeCLM α p T)=_
  simp only [criticalHeadDifferenceNativeCLM,_root_.sum_apply,_root_.smul_apply,map_sum,map_smul,
    hermiteScaleDistributionCLM_apply,nativeTranslation_realizes]
  ext f
  change (∑ i : Fin (Fintype.card (Fin k × Bool)+1), criticalHeadDifferenceCoeff α i •
      combDistributionTranslation _ (hermiteScaleDistribution p T)) f=
    hermiteScaleDistribution p T (criticalHeadDifferenceTestCLM α f)
  simp only [_root_.sum_apply,_root_.smul_apply,smul_eq_mul,criticalHeadDifferenceTestCLM,
    map_sum,map_smul]
  simp only [combDistributionTranslation_apply,Int.cast_sub,Int.cast_natCast]

/-- Actual same-order native head multiplication by exact Fourier conjugacy. -/
def criticalHeadMultiplierNativeCLM {k : ℕ} (α : Fin k → ℝ) (p : ℕ) :
    HermiteScale (-(p : ℤ)) →L[ℂ] HermiteScale (-(p : ℤ)) :=
  (hermiteFourier (-(p : ℤ))).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((criticalHeadDifferenceNativeCLM α p).comp
      (hermiteFourier (-(p : ℤ))).toContinuousLinearEquiv.toContinuousLinearMap)

/-- The native head multiplier is the literal whole multiplier, with no loss. -/
theorem criticalHeadMultiplierNativeCLM_realizes {k : ℕ} (α : Fin k → ℝ) (p : ℕ)
    (T : HermiteScale (-(p : ℤ))) :
    hermiteScaleDistribution p (criticalHeadMultiplierNativeCLM α p T)=
      criticalHeadMultiplierDistributionCLM α (hermiteScaleDistribution p T) := by
  change hermiteScaleDistribution p ((hermiteFourier (-(p : ℤ))).symm
    (criticalHeadDifferenceNativeCLM α p (hermiteFourier (-(p : ℤ)) T)))=_
  rw [hermiteFourier_symm_represents,criticalHeadDifferenceNativeCLM_realizes,
    hermiteFourier_represents_distributionalFourier]
  rw [← fourier_criticalHeadMultiplierDistribution,FourierTransform.fourierInv_fourier_eq]

/-- Original-native bounded forward product at the same order. -/
def criticalProductNativeCLM {k : ℕ} (α β : Fin k → ℝ) (p : ℕ) :
    HermiteScale (-(p : ℤ)) →L[ℂ] HermiteScale (-(p : ℤ)) :=
  (criticalHeadMultiplierNativeCLM α p).comp (criticalHeadDifferenceNativeCLM β p)

/-- The bounded native forward product realizes the actual complete product. -/
theorem criticalProductNativeCLM_realizes {k : ℕ} (α β : Fin k → ℝ) (p : ℕ)
    (T : HermiteScale (-(p : ℤ))) :
    hermiteScaleDistribution p (criticalProductNativeCLM α β p T)=
      criticalHeadMultiplierDistributionCLM α
        (criticalHeadDifferenceDistributionCLM β (hermiteScaleDistribution p T)) := by
  change hermiteScaleDistribution p (criticalHeadMultiplierNativeCLM α p
    (criticalHeadDifferenceNativeCLM β p T))=_
  rw [criticalHeadMultiplierNativeCLM_realizes,criticalHeadDifferenceNativeCLM_realizes]

/-- The original same-order forward norm constant is fixed by the heads and p. -/
theorem criticalProductNativeCLM_bound {k : ℕ} (α β : Fin k → ℝ) (p : ℕ) :
    ∃ C > 0, ∀ T : HermiteScale (-(p : ℤ)), ‖criticalProductNativeCLM α β p T‖ ≤ C*‖T‖ := by
  let U := criticalProductNativeCLM α β p
  refine ⟨‖U‖+1,by positivity,fun T => ?_⟩
  exact (U.le_opNorm T).trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))


/-- The complete whole critical source after reindexing k phases on each side. -/
def criticalCompleteSource (α β : ℕ+ → ℝ)
    (hia : ∀ j, 0 < α j ∧ α j < 1/2) (hib : ∀ j, 0 < β j ∧ β j < 1/2) (k : ℕ) :
    Submodule ℂ (TemperedDistribution ℝ ℂ) :=
  pairedAtomicSource (criticalPhaseTailCarrier α hia k 0) (criticalPhaseTailCarrier β hib k 0)

/-- The literal whole critical forward map on complete source spaces. -/
def criticalCompleteForward (α β : ℕ+ → ℝ)
    (hia : ∀ j, 0 < α j ∧ α j < 1/2) (hib : ∀ j, 0 < β j ∧ β j < 1/2) (k : ℕ) :
    criticalCompleteSource α β hia hib 0 →ₗ[ℂ] criticalCompleteSource α β hia hib k :=
  (((criticalHeadMultiplierDistributionCLM (criticalPrefixPhases α k)).comp
    (criticalHeadDifferenceDistributionCLM (criticalPrefixPhases β k))).toLinearMap.comp
      (criticalCompleteSource α β hia hib 0).subtype).codRestrict _
        (fun T => criticalProduct_maps_source α β hia hib k T T.property.1 T.property.2)

/-- The forward map is injective on the complete original source, by the
proved whole finite-cap exhaustion and original triangular holes. -/
theorem criticalCompleteForward_injective (α β : ℕ+ → ℝ)
    (ha : Function.Injective α) (hia : ∀ j, 0 < α j ∧ α j < 1/2)
    (hb : Function.Injective β) (hib : ∀ j, 0 < β j ∧ β j < 1/2) (k : ℕ) (hk : 1 ≤ k) :
    Function.Injective (criticalCompleteForward α β hia hib k) := by
  intro T U h
  apply sub_eq_zero.mp
  apply Subtype.ext
  apply criticalProduct_original_kernel hk α β ha hia hb hib _ (T-U).property.1 (T-U).property.2
  change criticalHeadMultiplierDistributionCLM _ (criticalHeadDifferenceDistributionCLM _
    ((T : TemperedDistribution ℝ ℂ)-U))=0
  rw [map_sub,map_sub]
  exact sub_eq_zero.mpr (congrArg Subtype.val h)

/-- The repaired whole inverse takes values in the complete original source. -/
def criticalCompleteInverse (α β : ℕ+ → ℝ)
    (ha : Function.Injective α) (hia : ∀ j, 0 < α j ∧ α j < 1/2)
    (hb : Function.Injective β) (hib : ∀ j, 0 < β j ∧ β j < 1/2) (k : ℕ) (hk : 1 ≤ k) :
    criticalCompleteSource α β hia hib k →ₗ[ℂ] criticalCompleteSource α β hia hib 0 :=
  ((criticalRepairedDistributionLM (criticalPrefixPhases α k) (criticalPrefixPhases β k)
    (criticalPrefixPhases_injective α ha k) (criticalPrefixPhases_inside α hia k)
    (criticalPrefixPhases_injective β hb k) (criticalPrefixPhases_inside β hib k)).comp
      (criticalCompleteSource α β hia hib k).subtype).codRestrict _
        (fun T => criticalRepairedDistribution_atomic_records α β ha hia hb hib k hk T T.property.1 T.property.2)

/-- The complete inverse is a right inverse of the literal forward map. -/
theorem criticalCompleteForward_inverse (α β : ℕ+ → ℝ)
    (ha : Function.Injective α) (hia : ∀ j, 0 < α j ∧ α j < 1/2)
    (hb : Function.Injective β) (hib : ∀ j, 0 < β j ∧ β j < 1/2) (k : ℕ) (hk : 1 ≤ k)
    (T : criticalCompleteSource α β hia hib k) :
    criticalCompleteForward α β hia hib k (criticalCompleteInverse α β ha hia hb hib k hk T)=T := by
  apply Subtype.ext
  exact criticalRepairedDistribution_rightInverse hk _ _ _ _ _ _ T

/-- The exact complete critical head theorem: the actual forward map is a
bijection of entire original source spaces, with the constructed whole inverse. -/
def criticalCompleteHeadEquiv (α β : ℕ+ → ℝ)
    (ha : Function.Injective α) (hia : ∀ j, 0 < α j ∧ α j < 1/2)
    (hb : Function.Injective β) (hib : ∀ j, 0 < β j ∧ β j < 1/2) (k : ℕ) (hk : 1 ≤ k) :
    criticalCompleteSource α β hia hib 0 ≃ₗ[ℂ] criticalCompleteSource α β hia hib k :=
  LinearEquiv.ofBijective (criticalCompleteForward α β hia hib k)
    ⟨criticalCompleteForward_injective α β ha hia hb hib k hk,
      fun T => ⟨criticalCompleteInverse α β ha hia hb hib k hk T,
        criticalCompleteForward_inverse α β ha hia hb hib k hk T⟩⟩

/-- The forward product preserves original native order on complete sources. -/
theorem criticalProduct_maps_native_source (α β : ℕ+ → ℝ)
    (hia : ∀ j, 0 < α j ∧ α j < 1/2) (hib : ∀ j, 0 < β j ∧ β j < 1/2)
    (k p : ℕ) (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ criticalOriginalNativeSource α β hia hib 0 p) :
    criticalHeadMultiplierDistributionCLM (criticalPrefixPhases α k)
      (criticalHeadDifferenceDistributionCLM (criticalPrefixPhases β k) T) ∈
      criticalOriginalNativeSource α β hia hib k p := by
  refine ⟨criticalProduct_maps_source α β hia hib k T hT.1.1 hT.1.2,?_⟩
  obtain ⟨u,hu⟩ := hT.2
  refine ⟨criticalProductNativeCLM (criticalPrefixPhases α k) (criticalPrefixPhases β k) p u,?_⟩
  change hermiteScaleDistribution p _=_
  rw [criticalProductNativeCLM_realizes]
  exact congrArg _ (congrArg _ hu)

/-- Actual same-order linear forward injection between the original native sources. -/
def criticalNativeForward (α β : ℕ+ → ℝ)
    (hia : ∀ j, 0 < α j ∧ α j < 1/2) (hib : ∀ j, 0 < β j ∧ β j < 1/2) (k p : ℕ) :
    criticalOriginalNativeSource α β hia hib 0 p →ₗ[ℂ]
      criticalOriginalNativeSource α β hia hib k p :=
  (((criticalHeadMultiplierDistributionCLM (criticalPrefixPhases α k)).comp
    (criticalHeadDifferenceDistributionCLM (criticalPrefixPhases β k))).toLinearMap.comp
      (criticalOriginalNativeSource α β hia hib 0 p).subtype).codRestrict _
        (fun T => criticalProduct_maps_native_source α β hia hib k p T T.property)

/-- Same-order injectivity retains the exact original native layer. -/
theorem criticalNativeForward_injective (α β : ℕ+ → ℝ)
    (ha : Function.Injective α) (hia : ∀ j, 0 < α j ∧ α j < 1/2)
    (hb : Function.Injective β) (hib : ∀ j, 0 < β j ∧ β j < 1/2) (k p : ℕ) (hk : 1 ≤ k) :
    Function.Injective (criticalNativeForward α β hia hib k p) := by
  intro T U h
  apply sub_eq_zero.mp
  apply Subtype.ext
  apply criticalProduct_original_kernel hk α β ha hia hb hib _ (T-U).property.1.1 (T-U).property.1.2
  change criticalHeadMultiplierDistributionCLM _ (criticalHeadDifferenceDistributionCLM _
    ((T : TemperedDistribution ℝ ℂ)-U))=0
  rw [map_sub,map_sub]
  exact sub_eq_zero.mpr (congrArg Subtype.val h)

/-- Complete original critical native ranks obey both proved directions of
head transport, with same-order forward and exactly two-order inverse loss. -/
theorem criticalNativeSource_rank_sandwich (α β : ℕ+ → ℝ)
    (ha : Function.Injective α) (hia : ∀ j, 0 < α j ∧ α j < 1/2)
    (hb : Function.Injective β) (hib : ∀ j, 0 < β j ∧ β j < 1/2) (k p : ℕ) (hk : 1 ≤ k) :
    Module.rank ℂ (criticalOriginalNativeSource α β hia hib 0 p) ≤
      Module.rank ℂ (criticalOriginalNativeSource α β hia hib k p) ∧
    Module.rank ℂ (criticalOriginalNativeSource α β hia hib k p) ≤
      Module.rank ℂ (criticalOriginalNativeSource α β hia hib 0 (p+2)) :=
  ⟨(criticalNativeForward α β hia hib k p).rank_le_of_injective
      (criticalNativeForward_injective α β ha hia hb hib k p hk),
    criticalNativeSource_rank_le α β ha hia hb hib k p hk⟩


/-- The equivalence inverse is exactly the already constructed repaired whole
Green inverse, rather than a separately chosen algebraic preimage. -/
theorem criticalCompleteHeadEquiv_symm_eq (α β : ℕ+ → ℝ)
    (ha : Function.Injective α) (hia : ∀ j, 0 < α j ∧ α j < 1/2)
    (hb : Function.Injective β) (hib : ∀ j, 0 < β j ∧ β j < 1/2) (k : ℕ) (hk : 1 ≤ k)
    (T : criticalCompleteSource α β hia hib k) :
    (criticalCompleteHeadEquiv α β ha hia hb hib k hk).symm T=
      criticalCompleteInverse α β ha hia hb hib k hk T := by
  apply (criticalCompleteHeadEquiv α β ha hia hb hib k hk).injective
  rw [LinearEquiv.apply_symm_apply]
  exact (criticalCompleteForward_inverse α β ha hia hb hib k hk T).symm

/-- The unique complete critical inverse satisfies the original two-order
native norm estimate. The bound is the actual finite-head-only operator bound. -/
theorem criticalCompleteHeadEquiv_native_inverse_bound (α β : ℕ+ → ℝ)
    (ha : Function.Injective α) (hia : ∀ j, 0 < α j ∧ α j < 1/2)
    (hb : Function.Injective β) (hib : ∀ j, 0 < β j ∧ β j < 1/2) (k p : ℕ) (hk : 1 ≤ k) :
    ∃ C > 0, ∀ (T : HermiteScale (-(p : ℤ)))
      (hT : AtomicOnCarrier (criticalPhaseTailCarrier α hia k 0) (hermiteScaleDistribution p T))
      (hFT : AtomicOnCarrier (criticalPhaseTailCarrier β hib k 0) (𝓕 (hermiteScaleDistribution p T))),
      ∃ U : HermiteScale (-((p+2 : ℕ) : ℤ)), ‖U‖ ≤ C*‖T‖ ∧
        hermiteScaleDistribution (p+2) U=
          ((criticalCompleteHeadEquiv α β ha hia hb hib k hk).symm
            ⟨hermiteScaleDistribution p T,hT,hFT⟩ : TemperedDistribution ℝ ℂ) := by
  let a := criticalPrefixPhases α k
  let b := criticalPrefixPhases β k
  let ia := criticalPrefixPhases_injective α ha k
  let ib := criticalPrefixPhases_injective β hb k
  let pa := criticalPrefixPhases_inside α hia k
  let pb := criticalPrefixPhases_inside β hib k
  obtain ⟨C,hC,hbound⟩ := criticalRepairedNativeCLM_bound a b ia pa ib pb p
  refine ⟨C,hC,fun T hT hFT => ⟨criticalRepairedNativeCLM a b ia pa ib pb p T,hbound T,?_⟩⟩
  rw [criticalCompleteHeadEquiv_symm_eq]
  exact criticalRepairedNativeCLM_realizes a b ia pa ib pb p T

/-- Both original-native rank directions include the empty-head identity case. -/
theorem criticalNativeSource_rank_sandwich_all (α β : ℕ+ → ℝ)
    (ha : Function.Injective α) (hia : ∀ j, 0 < α j ∧ α j < 1/2)
    (hb : Function.Injective β) (hib : ∀ j, 0 < β j ∧ β j < 1/2) (k p : ℕ) :
    Module.rank ℂ (criticalOriginalNativeSource α β hia hib 0 p) ≤
      Module.rank ℂ (criticalOriginalNativeSource α β hia hib k p) ∧
    Module.rank ℂ (criticalOriginalNativeSource α β hia hib k p) ≤
      Module.rank ℂ (criticalOriginalNativeSource α β hia hib 0 (p+2)) := by
  by_cases hk : 1 ≤ k
  · exact criticalNativeSource_rank_sandwich α β ha hia hb hib k p hk
  · have hk0 : k=0 := by omega
    subst k
    exact ⟨le_rfl,criticalNativeSource_rank_le_all α β ha hia hb hib 0 p⟩

end
end MeyerGeneralProblem.Adaptive
