module

public import MeyerGeneralProblem.Cardinal.Adaptive.SeamGraphCorrections
public import MeyerGeneralProblem.Cardinal.Adaptive.SeamKernelBounds

@[expose] public section

/-! # Complete Schur reduction on the literal moment Hilbert space -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
attribute [local instance] Classical.propDecidable

theorem seamPProjection_decomposition (u : SeamMomentArray) :
    seamPProjection u=seamDiagonalEmbedding false false (seamDiagonalReading false false u)+seamCProjection u := by
  rw [←seamDProjection_eq_diagonal]
  ext p
  rcases p with ⟨⟨i,e⟩,j,f⟩
  change seamPProjection u ((i,e),(j,f))=seamDProjection u ((i,e),(j,f))+seamCProjection u ((i,e),(j,f))
  simp only [seamPProjection,seamDProjection,seamCProjection,momentProjection_apply,
    seamDIndices,seamCIndices,Set.mem_union,Set.mem_setOf_eq]
  cases e <;> cases f <;> by_cases h : i=j <;> simp_all

theorem seamQProjection_C (u : SeamMomentArray) : seamQProjection (seamCProjection u)=seamCProjection u := by
  ext p
  simp only [seamQProjection,seamCProjection,momentProjection_apply,Set.mem_union]
  by_cases h : p ∈ seamCIndices <;> simp [h]

theorem seamQProjection_D (u : SeamSequence) : seamQProjection (seamDiagonalEmbedding false false u)=0 := by
  ext p
  rcases p with ⟨⟨i,e⟩,j,f⟩
  simp only [seamQProjection,momentProjection_apply,seamDiagonalEmbedding_apply,
    seamCIndices,seamGIndices,Set.mem_union,Set.mem_setOf_eq]
  cases e <;> cases f <;> by_cases h : i=j <;> simp_all

theorem seamGReading_C (u : SeamMomentArray) : seamDiagonalReading true true (seamCProjection u)=0 := by
  ext i
  simp [seamDiagonalReading_apply,seamCProjection,momentProjection_apply,seamCIndices]

/-- Complete complementary right-hand side, mapping the entire leading diagonal. -/
def seamSchurA (F : SeamMomentArray →L[ℂ] SeamMomentArray) : SeamSequence →L[ℂ] SeamMomentArray :=
  seamCProjection.comp ((F-seamQProjection).comp (seamDiagonalEmbedding false false))

/-- The full complementary block, extended by identity on the unused orthogonal coordinates.
Its inverse is the genuine whole Neumann inverse and retains all feedback. -/
def seamSchurB (F : SeamMomentArray →L[ℂ] SeamMomentArray) : SeamMomentArray →L[ℂ] SeamMomentArray :=
  1+seamCProjection*(F-seamQProjection)*seamCProjection

/-- Exact full target-diagonal compression. -/
def seamSchurH (F : SeamMomentArray →L[ℂ] SeamMomentArray) : SeamSequence →L[ℂ] SeamSequence :=
  (seamDiagonalReading true true).comp (F.comp (seamDiagonalEmbedding false false))

/-- Exact full complementary-to-target block. -/
def seamSchurJ (F : SeamMomentArray →L[ℂ] SeamMomentArray) : SeamMomentArray →L[ℂ] SeamSequence :=
  (seamDiagonalReading true true).comp ((F-seamQProjection).comp seamCProjection)

theorem seamSchurA_norm (F : SeamMomentArray →L[ℂ] SeamMomentArray) :
    ‖seamSchurA F‖ ≤ ‖F-seamQProjection‖ := by
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  calc
    _ ≤ 1*(‖F-seamQProjection‖*1) := by
      apply mul_le_mul seamCProjection_norm_le_one _ (norm_nonneg _) zero_le_one
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (seamDiagonalEmbedding_norm_le_one false false) (norm_nonneg _))
    _ = _ := by ring

theorem seamSchurB_close (F : SeamMomentArray →L[ℂ] SeamMomentArray) :
    ‖seamSchurB F-ContinuousLinearMap.id ℂ SeamMomentArray‖ ≤ ‖F-seamQProjection‖ := by
  change ‖(1+seamCProjection*(F-seamQProjection)*seamCProjection)-1‖ ≤ _
  rw [add_sub_cancel_left]
  calc
    _ ≤ (‖seamCProjection‖*‖F-seamQProjection‖)*‖seamCProjection‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (1*‖F-seamQProjection‖)*1 := by gcongr <;> exact seamCProjection_norm_le_one
    _ = _ := by ring

theorem seamSchurJ_norm (F : SeamMomentArray →L[ℂ] SeamMomentArray) :
    ‖seamSchurJ F‖ ≤ ‖F-seamQProjection‖ := by
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  calc
    _ ≤ 1*(‖F-seamQProjection‖*1) := by
      apply mul_le_mul (seamDiagonalReading_norm_le_one true true) _ (norm_nonneg _) zero_le_one
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left seamCProjection_norm_le_one (norm_nonneg _))
    _ = _ := by ring

/-- The exact full reduced operator with the actual complete complementary inverse. -/
def seamSchur (F : SeamMomentArray →L[ℂ] SeamMomentArray) (hF : ‖F-seamQProjection‖ < 1) :
    SeamSequence →L[ℂ] SeamSequence :=
  fullSchurOperator (seamSchurA F) (seamSchurB F) (seamSchurH F) (seamSchurJ F)
    ((seamSchurB_close F).trans_lt hF)

/-- Every full flag-kernel vector satisfies both actual Schur block equations. -/
theorem seamSchur_block_equations (F : SeamMomentArray →L[ℂ] SeamMomentArray)
    (a : SeamMomentArray) (ha : seamPProjection a=a) (hFa : F a=0) :
    let u := seamDiagonalReading false false a
    let c := seamCProjection a
    seamSchurA F u+seamSchurB F c=0 ∧ seamSchurH F u+seamSchurJ F c=0 := by
  dsimp only
  have hd := seamPProjection_decomposition a
  rw [ha] at hd
  have he : F (seamDiagonalEmbedding false false (seamDiagonalReading false false a))+F (seamCProjection a)=0 := by
    rw [←map_add,←hd,hFa]
  have hC := congrArg seamCProjection he
  have hG := congrArg (seamDiagonalReading true true) he
  constructor
  · change seamCProjection (F (seamDiagonalEmbedding false false (seamDiagonalReading false false a))-
      seamQProjection (seamDiagonalEmbedding false false (seamDiagonalReading false false a)))+
      (seamCProjection a+seamCProjection ((F-seamQProjection) (seamCProjection (seamCProjection a))))=0
    simp only [seamQProjection_D,sub_zero,seamCProjection_idempotent,sub_apply,seamQProjection_C,map_sub]
    simp only [map_add,map_zero] at hC
    convert hC using 1 <;> abel
  · change seamDiagonalReading true true (F (seamDiagonalEmbedding false false (seamDiagonalReading false false a)))+
      seamDiagonalReading true true ((F-seamQProjection) (seamCProjection (seamCProjection a)))=0
    simp only [seamCProjection_idempotent,sub_apply,seamQProjection_C,map_sub,seamGReading_C,sub_zero]
    simpa only [map_add,map_zero] using hG

/-- Complete graph solutions retain the exact Neumann-eliminated complementary coordinate. -/
theorem seamSchur_kernel_coordinate (F : SeamMomentArray →L[ℂ] SeamMomentArray)
    (hF : ‖F-seamQProjection‖ < 1) (a : SeamMomentArray)
    (ha : seamPProjection a=a) (hFa : F a=0) :
    seamSchur F hF (seamDiagonalReading false false a)=0 ∧
    seamCProjection a=fullSchurComplementCoordinate (seamSchurA F) (seamSchurB F)
      ((seamSchurB_close F).trans_lt hF) (seamDiagonalReading false false a) :=
  (fullSchur_kernel_iff _ _ _ _ _ _ _).mp (seamSchur_block_equations F a ha hFa)

/-- The actual assembled blocks preserve the complete quantitative Schur error. -/
theorem seamSchur_error (F : SeamMomentArray →L[ℂ] SeamMomentArray)
    (hF : ‖F-seamQProjection‖ ≤ 10*(1/4096 : ℝ))
    (hH : ‖seamSchurH F-seamLeadingCoefficient •seamBackwardShift‖ ≤ 100*(1/4096 : ℝ)^2) :
    ‖seamSchur F (hF.trans_lt (by norm_num))-seamLeadingCoefficient •seamBackwardShift‖ ≤
      300*(1/4096 : ℝ)^2 :=
  fullSchurOperator_seam_error _ _ _ _ _ ((seamSchurB_close F).trans hF)
    ((seamSchurA_norm F).trans hF) ((seamSchurJ_norm F).trans hF) hH

/-- Every actual flag-kernel diagonal is determined by its single zeroth reading. -/
theorem seamSchur_diagonal_eq_smul (F : SeamMomentArray →L[ℂ] SeamMomentArray)
    (hF : ‖F-seamQProjection‖ ≤ 10*(1/4096 : ℝ))
    (hH : ‖seamSchurH F-seamLeadingCoefficient •seamBackwardShift‖ ≤ 100*(1/4096 : ℝ)^2)
    (a : SeamMomentArray) (ha : seamPProjection a=a) (hFa : F a=0) :
    seamDiagonalReading false false a=a ((0,false),(0,false)) •
      seamCanonicalKernelVector
        (seamSchur F (hF.trans_lt (by norm_num))-seamLeadingCoefficient •seamBackwardShift)
        (seamSchur_error F hF hH) := by
  have hK := (seamSchur_kernel_coordinate F (hF.trans_lt (by norm_num)) a ha hFa).1
  apply seam_kernel_eq_smul _ (seamSchur_error F hF hH)
  simpa only [perturbedBackwardShift,add_sub_cancel] using hK

/-- Quantitative norm of the complete flag vector, not just its diagonal. -/
theorem seamSchur_flag_norm (F : SeamMomentArray →L[ℂ] SeamMomentArray)
    (hF : ‖F-seamQProjection‖ ≤ 10*(1/4096 : ℝ))
    (hH : ‖seamSchurH F-seamLeadingCoefficient •seamBackwardShift‖ ≤ 100*(1/4096 : ℝ)^2)
    (a : SeamMomentArray) (ha : seamPProjection a=a) (hFa : F a=0) :
    ‖a‖ ≤ 4*‖a ((0,false),(0,false))‖ := by
  let u := seamDiagonalReading false false a
  have hu : ‖u‖ ≤ 3*‖a ((0,false),(0,false))‖ := by
    dsimp only [u]
    rw [seamSchur_diagonal_eq_smul F hF hH a ha hFa,norm_smul]
    calc
      _ ≤ ‖a ((0,false),(0,false))‖*3 := mul_le_mul_of_nonneg_left
        (seamCanonicalKernelVector_norm _ _) (norm_nonneg _)
      _ = _ := mul_comm _ _
  have hc := (seamSchur_kernel_coordinate F (hF.trans_lt (by norm_num)) a ha hFa).2
  have hcn : ‖seamCProjection a‖ ≤ (1-10*(1/4096 : ℝ))⁻¹*(10*(1/4096 : ℝ))*‖u‖ := by
    rw [hc]
    apply (fullSchurComplementCoordinate_bound _ _ (10*(1/4096 : ℝ)) (by norm_num)
      ((seamSchurB_close F).trans hF) u).trans
    gcongr
    exact (seamSchurA_norm F).trans hF
  have hd := seamPProjection_decomposition a
  rw [ha] at hd
  have han : ‖a‖ ≤ ‖u‖+‖seamCProjection a‖ := by
    conv_lhs => rw [hd]
    exact (norm_add_le _ _).trans (by rw [seamDiagonalEmbedding_norm])
  have hb : ‖a‖ ≤ (1+(1-10*(1/4096 : ℝ))⁻¹*(10*(1/4096 : ℝ)))*‖u‖ := by nlinarith
  apply hb.trans
  calc
    _ ≤ (1+(1-10*(1/4096 : ℝ))⁻¹*(10*(1/4096 : ℝ)))*(3*‖a ((0,false),(0,false))‖) :=
      mul_le_mul_of_nonneg_left hu (by norm_num)
    _ ≤ _ := by nlinarith [norm_nonneg (a ((0,false),(0,false)))]

/-- A zero zeroth reading kills the entire full graph-kernel vector. -/
theorem seamSchur_flag_zero (F : SeamMomentArray →L[ℂ] SeamMomentArray)
    (hF : ‖F-seamQProjection‖ ≤ 10*(1/4096 : ℝ))
    (hH : ‖seamSchurH F-seamLeadingCoefficient •seamBackwardShift‖ ≤ 100*(1/4096 : ℝ)^2)
    (a : SeamMomentArray) (ha : seamPProjection a=a) (hFa : F a=0)
    (hz : a ((0,false),(0,false))=0) : a=0 := by
  have hn := seamSchur_flag_norm F hF hH a ha hFa
  rw [hz,norm_zero,mul_zero] at hn
  exact norm_eq_zero.mp (le_antisymm hn (norm_nonneg _))

end
end MeyerGeneralProblem.Adaptive
