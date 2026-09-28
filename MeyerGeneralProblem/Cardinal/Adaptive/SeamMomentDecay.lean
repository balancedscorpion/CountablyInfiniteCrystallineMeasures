module

public import MeyerGeneralProblem.Cardinal.Adaptive.SeamArmBounds
public import MeyerGeneralProblem.Cardinal.Adaptive.SeamFirstReadingBounds

@[expose] public section

/-! # Whole maximum-index decay from exact full shifted equations -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open scoped ENNReal

section Decay
variable (a b ta tb : ℕ → ℂ)
variable (ha : ∀ i, ‖a i‖ ≤ (1/4096 : ℝ)^2) (hb : ∀ i, ‖b i‖ ≤ (1/4096 : ℝ)^2)
variable (hta : ∀ i, ‖ta i‖ ≤ (1/4096 : ℝ)^3) (htb : ∀ i, ‖tb i‖ ≤ (1/4096 : ℝ)^3)

/-- The actual full operator formed with each simultaneously shifted node and tangent sequence. -/
def seamShiftedFullOperator (h : ℕ) : SeamMomentArray →L[ℂ] SeamMomentArray :=
  seamFullOperator (fun i => a (i+h)) (fun i => b (i+h)) (fun i => ta (i+h)) (fun i => tb (i+h))
    (fun i => ha (i+h)) (fun i => hb (i+h)) (fun i => hta (i+h)) (fun i => htb (i+h))

variable (hH : ∀ h, ‖seamSchurH (seamShiftedFullOperator a b ta tb ha hb hta htb h)-
  seamLeadingCoefficient •seamBackwardShift‖ ≤ 100*(1/4096 : ℝ)^2)
variable (u : SeamMomentArray) (hu : seamPProjection u=u)
variable (hFu : seamFullOperator a b ta tb ha hb hta htb u=0)
include a b ta tb ha hb hta htb hH u hu hFu

/-- Each genuine shifted diagonal step retains the next actual phases. -/
theorem seamFull_diagonal_step (h : ℕ) :
    ‖u ((h+1,false),(h+1,false))‖ ≤
      (8589934592*(‖ta h‖+‖tb h‖+‖b h‖))*‖u ((h,false),(h,false))‖ := by
  have hp : seamPProjection (seamTailShift h u)=seamTailShift h u := by rw [←seamTailShift_P,hu]
  have hk := seamTailShift_kernel h a b ta tb ha hb hta htb u hFu
  have hn := seamFullOperator_next_reading_bound _ _ _ _ _ _ _ _ (hH h) (seamTailShift h u) hp hk
  simpa only [seamTailShift_apply,seamTailIndex,Nat.zero_add,Nat.add_comm,Nat.add_zero] using hn

/-- Complete diagonal decay is the product of the actual successive phase residuals. -/
theorem seamFull_diagonal_product (h : ℕ) :
    ‖u ((h,false),(h,false))‖ ≤
      (∏ n ∈ Finset.range h, (8589934592*(‖ta n‖+‖tb n‖+‖b n‖)))*‖u ((0,false),(0,false))‖ := by
  induction h with
  | zero => simp
  | succ h ih =>
    apply (seamFull_diagonal_step a b ta tb ha hb hta htb hH u hu hFu h).trans
    calc
      _ ≤ (8589934592*(‖ta h‖+‖tb h‖+‖b h‖))*
          ((∏ n ∈ Finset.range h, (8589934592*(‖ta n‖+‖tb n‖+‖b n‖)))*‖u ((0,false),(0,false))‖) :=
        mul_le_mul_of_nonneg_left ih (by positivity)
      _ = _ := by rw [Finset.prod_range_succ]; ring

/-- Both full flag arms are bounded by the actual diagonal corner of the shifted equation. -/
theorem seamFull_flag_arm (h : ℕ) :
    ‖seamArmProjection h u‖ ≤ (9/2 : ℝ)*‖u ((h,false),(h,false))‖ := by
  have hp : seamPProjection (seamTailShift h u)=seamTailShift h u := by rw [←seamTailShift_P,hu]
  have hk := seamTailShift_kernel h a b ta tb ha hb hta htb u hFu
  have hq := seamSchur_flag_norm _ (seamFullOperator_close _ _ _ _ _ _ _ _) (hH h) (seamTailShift h u) hp hk
  have hd : ‖seamDiagonalReading false false (seamTailShift h u)‖ ≤ 4*‖u ((h,false),(h,false))‖ := by
    apply ((seamDiagonalReading false false).le_opNorm _).trans
    have hr := seamDiagonalReading_norm_le_one false false
    have hqn : ‖seamTailShift h u‖ ≤ 4*‖u ((h,false),(h,false))‖ := by
      simpa only [seamTailShift_apply,seamTailIndex,Nat.zero_add] using hq
    nlinarith [norm_nonneg (seamTailShift h u)]
  apply (seamSchur_arm_bound h _ (seamFullOperator_close a b ta tb ha hb hta htb)
    (seamFullOperator_arm_invariant h a b ta tb ha hb hta htb) u hu hFu).trans
  calc
    _ ≤ (1+20*(1/4096 : ℝ))*(4*‖u ((h,false),(h,false))‖) := mul_le_mul_of_nonneg_left hd (by norm_num)
    _ ≤ _ := by nlinarith [norm_nonneg (u ((h,false),(h,false)))]

/-- The full reconstructed source array has uniform control on both infinite arms. -/
theorem seamFull_physical_arm (h : ℕ) :
    ‖seamArmProjection h (u+seamPhysicalGraph ta hta u)‖ ≤ 5*‖u ((h,false),(h,false))‖ := by
  have ht := seamPhysicalGraph_arm_invariant h ta hta
  have he : seamArmProjection h (seamPhysicalGraph ta hta u)=
      seamArmProjection h (seamPhysicalGraph ta hta (seamArmProjection h u)) :=
    congrArg (fun A : SeamMomentArray →L[ℂ] SeamMomentArray => A u) ht
  have hc : ‖seamArmProjection h (seamPhysicalGraph ta hta u)‖ ≤
      (1/4096 : ℝ)^2*‖seamArmProjection h u‖ := by
    rw [he]
    apply (ContinuousLinearMap.le_opNorm (seamArmProjection h*seamPhysicalGraph ta hta) _).trans
    have hn : ‖seamArmProjection h*seamPhysicalGraph ta hta‖ ≤ (1/4096 : ℝ)^2 := by
      calc
        _ ≤ ‖seamArmProjection h‖*‖seamPhysicalGraph ta hta‖ := norm_mul_le _ _
        _ ≤ 1*(1/4096 : ℝ)^2 := mul_le_mul (seamArmProjection_norm_le_one h)
          (seamPhysicalGraph_norm ta hta) (norm_nonneg _) zero_le_one
        _ = _ := one_mul _
    exact mul_le_mul_of_nonneg_right hn (norm_nonneg _)
  rw [map_add]
  apply (norm_add_le _ _).trans
  have hn := seamFull_flag_arm a b ta tb ha hb hta htb hH u hu hFu h
  nlinarith [norm_nonneg (seamArmProjection h u),norm_nonneg (u ((h,false),(h,false)))]

/-- Every coordinate in either arm obeys the full maximum-index product estimate. -/
theorem seamFull_moment_product (i j : ℕ) (e f : Bool) :
    ‖(u+seamPhysicalGraph ta hta u) ((i,e),(j,f))‖ ≤
      5*(∏ n ∈ Finset.range (max i j), (8589934592*(‖ta n‖+‖tb n‖+‖b n‖)))*‖u ((0,false),(0,false))‖ := by
  have he := lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (seamArmProjection (max i j) (u+seamPhysicalGraph ta hta u)) ((i,e),(j,f))
  have hp : seamArmProjection (max i j) (u+seamPhysicalGraph ta hta u) ((i,e),(j,f))=
      (u+seamPhysicalGraph ta hta u) ((i,e),(j,f)) := by
    simp only [seamArmProjection,momentProjection_apply,seamArmIndices,Set.mem_setOf_eq,le_refl,ite_true]
  rw [hp] at he
  apply (he.trans (seamFull_physical_arm a b ta tb ha hb hta htb hH u hu hFu (max i j))).trans
  have hd := seamFull_diagonal_product a b ta tb ha hb hta htb hH u hu hFu (max i j)
  nlinarith

end Decay
end
end MeyerGeneralProblem.Adaptive
