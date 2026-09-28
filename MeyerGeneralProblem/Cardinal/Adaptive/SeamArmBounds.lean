module

public import MeyerGeneralProblem.Cardinal.Adaptive.SeamArmInvariance
public import MeyerGeneralProblem.Cardinal.Adaptive.SeamTailIntertwining

@[expose] public section

/-! # Full complementary feedback controls both infinite moment arms -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The actual shifted index range is exactly the simultaneous tail quadrant. -/
theorem seamTailIndex_range (h : ℕ) : Set.range (seamTailIndex h)=seamQuadrantIndices h := by
  ext p
  rcases p with ⟨⟨i,e⟩,j,f⟩
  constructor
  · rintro ⟨⟨⟨m,b⟩,n,c⟩,hh⟩
    simp only [seamTailIndex,Prod.mk.injEq] at hh
    change h ≤ i ∧ h ≤ j
    omega
  · rintro ⟨hi,hj⟩
    refine ⟨((i-h,e),(j-h,f)),?_⟩
    simp [seamTailIndex,Nat.sub_add_cancel hi,Nat.sub_add_cancel hj]

/-- Complete quadrant extraction preserves precisely the norm of its zero extension. -/
theorem seamQuadrantProjection_norm (h : ℕ) (u : SeamMomentArray) :
    ‖seamQuadrantProjection h u‖=‖seamTailShift h u‖ := by
  have hh := momentEmbedding_pullback (seamTailIndex h) (seamTailIndex_injective h) u
  rw [seamTailIndex_range] at hh
  change ‖momentProjection (seamQuadrantIndices h) u‖=_
  rw [←hh,momentEmbedding_norm]
  rfl

/-- On the whole leading diagonal the maximum-index arm is exactly the shifted quadrant. -/
theorem seamArm_D_eq_quadrant (h : ℕ) (u : SeamMomentArray) :
    seamArmProjection h (seamDProjection u)=seamQuadrantProjection h (seamDProjection u) := by
  ext p
  simp only [seamArmProjection,seamQuadrantProjection,seamDProjection,momentProjection_apply,
    seamArmIndices,seamQuadrantIndices,seamDIndices,Set.mem_setOf_eq]
  split_ifs <;> simp_all

theorem seamTailShift_D (h : ℕ) (u : SeamMomentArray) :
    seamTailShift h (seamDProjection u)=seamDProjection (seamTailShift h u) := by
  ext p
  simp only [seamTailShift_apply,seamDProjection,momentProjection_apply,seamDIndices,
    Set.mem_setOf_eq,seamTailIndex]
  simp

/-- The complete diagonal arm norm equals the literal diagonal reading of the shifted array. -/
theorem seamArm_D_norm (h : ℕ) (u : SeamMomentArray) :
    ‖seamArmProjection h (seamDProjection u)‖=‖seamDiagonalReading false false (seamTailShift h u)‖ := by
  rw [seamArm_D_eq_quadrant,seamQuadrantProjection_norm,seamTailShift_D,
    seamDProjection_eq_diagonal,seamDiagonalEmbedding_norm]

/-- Entire complementary-arm feedback is controlled by the corresponding full diagonal arm. -/
theorem seamSchur_complement_arm_bound (h : ℕ) (F : SeamMomentArray →L[ℂ] SeamMomentArray)
    (hF : ‖F-seamQProjection‖ ≤ 10*(1/4096 : ℝ))
    (htri : OperatorCornerInvariant (seamArmProjection h) F)
    (u : SeamMomentArray) (hu : seamPProjection u=u) (hFu : F u=0) :
    ‖seamArmProjection h (seamCProjection u)‖ ≤
      20*(1/4096 : ℝ)*‖seamArmProjection h (seamDProjection u)‖ := by
  have he := (seamSchur_block_equations F u hu hFu).1
  have hb := seamSchurB_arm_invariant h F htri
  have hbe : ∀ x, seamArmProjection h (seamSchurB F x)=
      seamArmProjection h (seamSchurB F (seamArmProjection h x)) := by
    intro x
    exact congrArg (fun A : SeamMomentArray →L[ℂ] SeamMomentArray => A x) hb
  have hn := seamArm_full_complement_bound h (seamSchurB F) hbe
    (10*(1/4096 : ℝ)) (by norm_num) ((seamSchurB_close F).trans hF)
    (seamSchurA F (seamDiagonalReading false false u)) (seamCProjection u) he
  have ht : OperatorCornerInvariant (seamArmProjection h) (seamCProjection*(F-seamQProjection)) :=
    (momentProjection_corner _ _).mul (htri.sub (momentProjection_corner _ _))
  have hs : seamArmProjection h (seamSchurA F (seamDiagonalReading false false u))=
      seamArmProjection h ((seamCProjection*(F-seamQProjection)) (seamArmProjection h (seamDProjection u))) := by
    rw [seamDProjection_eq_diagonal]
    exact congrArg (fun A : SeamMomentArray →L[ℂ] SeamMomentArray =>
      A (seamDiagonalEmbedding false false (seamDiagonalReading false false u))) ht
  have hnA : ‖seamArmProjection h (seamSchurA F (seamDiagonalReading false false u))‖ ≤
      10*(1/4096 : ℝ)*‖seamArmProjection h (seamDProjection u)‖ := by
    rw [hs]
    have hm : ‖seamArmProjection h*(seamCProjection*(F-seamQProjection))‖ ≤ 10*(1/4096 : ℝ) := by
      calc
        _ ≤ ‖seamArmProjection h‖*(‖seamCProjection‖*‖F-seamQProjection‖) :=
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg _))
        _ ≤ 1*(1*(10*(1/4096 : ℝ))) := by gcongr <;> first | exact seamArmProjection_norm_le_one h | exact seamCProjection_norm_le_one
        _ = _ := by ring
    exact (ContinuousLinearMap.le_opNorm (seamArmProjection h*(seamCProjection*(F-seamQProjection))) _).trans
      (mul_le_mul_of_nonneg_right hm (norm_nonneg _))
  apply hn.trans
  calc
    _ ≤ (1-10*(1/4096 : ℝ))⁻¹*(10*(1/4096 : ℝ)*‖seamArmProjection h (seamDProjection u)‖) :=
      mul_le_mul_of_nonneg_left hnA (by norm_num)
    _ ≤ _ := by nlinarith [norm_nonneg (seamArmProjection h (seamDProjection u))]

/-- Both complete arms of a full flag vector are controlled by its shifted diagonal. -/
theorem seamSchur_arm_bound (h : ℕ) (F : SeamMomentArray →L[ℂ] SeamMomentArray)
    (hF : ‖F-seamQProjection‖ ≤ 10*(1/4096 : ℝ))
    (htri : OperatorCornerInvariant (seamArmProjection h) F)
    (u : SeamMomentArray) (hu : seamPProjection u=u) (hFu : F u=0) :
    ‖seamArmProjection h u‖ ≤ (1+20*(1/4096 : ℝ))*
      ‖seamDiagonalReading false false (seamTailShift h u)‖ := by
  have he := seamPProjection_decomposition u
  rw [hu,←seamDProjection_eq_diagonal] at he
  have hc := seamSchur_complement_arm_bound h F hF htri u hu hFu
  have hn : ‖seamArmProjection h u‖ ≤
      ‖seamArmProjection h (seamDProjection u)‖+‖seamArmProjection h (seamCProjection u)‖ := by
    conv_lhs => rw [he,map_add]
    exact norm_add_le _ _
  rw [seamArm_D_norm] at hc hn
  nlinarith

end
end MeyerGeneralProblem.Adaptive
