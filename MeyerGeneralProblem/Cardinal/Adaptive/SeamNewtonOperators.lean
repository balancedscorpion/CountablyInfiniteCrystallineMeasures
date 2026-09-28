module

public import MeyerGeneralProblem.Cardinal.Adaptive.SeamMomentProjections

@[expose] public section

/-! # Genuine whole-array Newton shifts and their exact diagonal compression -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section

/-- Increment the physical Newton level, preserving both parity bits. -/
def seamRowSuccessor (p : SeamMomentIndex) : SeamMomentIndex := ((p.1.1+1,p.1.2),p.2)
/-- Increment the spectral Newton level, preserving both parity bits. -/
def seamColumnSuccessor (p : SeamMomentIndex) : SeamMomentIndex := (p.1,(p.2.1+1,p.2.2))

theorem seamRowSuccessor_injective : Function.Injective seamRowSuccessor := by
  rintro ⟨⟨i,e⟩,j,f⟩ ⟨⟨k,g⟩,l,h⟩ heq
  simpa [seamRowSuccessor] using heq

theorem seamColumnSuccessor_injective : Function.Injective seamColumnSuccessor := by
  rintro ⟨⟨i,e⟩,j,f⟩ ⟨⟨k,g⟩,l,h⟩ heq
  simpa [seamColumnSuccessor] using heq

/-- The actual row backward shift on all four parity sectors. -/
def seamRowShift : SeamMomentArray →L[ℂ] SeamMomentArray := momentPullback seamRowSuccessor seamRowSuccessor_injective
/-- The actual column backward shift on all four parity sectors. -/
def seamColumnShift : SeamMomentArray →L[ℂ] SeamMomentArray := momentPullback seamColumnSuccessor seamColumnSuccessor_injective

@[simp] theorem seamRowShift_apply (u : SeamMomentArray) (p : SeamMomentIndex) :
    seamRowShift u p=u ((p.1.1+1,p.1.2),p.2) := rfl
@[simp] theorem seamColumnShift_apply (u : SeamMomentArray) (p : SeamMomentIndex) :
    seamColumnShift u p=u (p.1,(p.2.1+1,p.2.2)) := rfl

theorem seamRowShift_norm_le_one : ‖seamRowShift‖ ≤ 1 := momentPullback_norm_le_one _ _
theorem seamColumnShift_norm_le_one : ‖seamColumnShift‖ ≤ 1 := momentPullback_norm_le_one _ _

/-- Multiplication by the physical Newton coordinate on the actual whole array. -/
def seamNewtonRow (R : ℂ) (a : ℕ → ℂ) (K : ℝ) (hK : 0 ≤ K) (ha : ∀ i, ‖a i‖ ≤ K) :
    SeamMomentArray →L[ℂ] SeamMomentArray :=
  R •seamRowShift+momentDiagonal (fun p => a p.1.1) K hK (fun p => ha p.1.1)
/-- Multiplication by the spectral Newton coordinate on the actual whole array. -/
def seamNewtonColumn (R : ℂ) (b : ℕ → ℂ) (K : ℝ) (hK : 0 ≤ K) (hb : ∀ i, ‖b i‖ ≤ K) :
    SeamMomentArray →L[ℂ] SeamMomentArray :=
  R •seamColumnShift+momentDiagonal (fun p => b p.2.1) K hK (fun p => hb p.2.1)

@[simp] theorem seamNewtonRow_apply (R : ℂ) (a : ℕ → ℂ) (K : ℝ) (hK : 0 ≤ K)
    (ha : ∀ i, ‖a i‖ ≤ K) (u : SeamMomentArray) (p : SeamMomentIndex) :
    seamNewtonRow R a K hK ha u p=R*u ((p.1.1+1,p.1.2),p.2)+a p.1.1*u p := rfl
@[simp] theorem seamNewtonColumn_apply (R : ℂ) (b : ℕ → ℂ) (K : ℝ) (hK : 0 ≤ K)
    (hb : ∀ i, ‖b i‖ ≤ K) (u : SeamMomentArray) (p : SeamMomentIndex) :
    seamNewtonColumn R b K hK hb u p=R*u (p.1,(p.2.1+1,p.2.2))+b p.2.1*u p := rfl

theorem seamNewtonRow_norm_le (R : ℂ) (a : ℕ → ℂ) (K : ℝ) (hK : 0 ≤ K) (ha : ∀ i, ‖a i‖ ≤ K) :
    ‖seamNewtonRow R a K hK ha‖ ≤ ‖R‖+K := by
  calc
    _ ≤ ‖R •seamRowShift‖+‖momentDiagonal (fun p : SeamMomentIndex => a p.1.1) K hK (fun p => ha p.1.1)‖ := norm_add_le _ _
    _ ≤ ‖R‖+K := by
      rw [norm_smul]
      exact add_le_add (by nlinarith [seamRowShift_norm_le_one,norm_nonneg R]) (momentDiagonal_norm_le _ _ _ _)

theorem seamNewtonColumn_norm_le (R : ℂ) (b : ℕ → ℂ) (K : ℝ) (hK : 0 ≤ K) (hb : ∀ i, ‖b i‖ ≤ K) :
    ‖seamNewtonColumn R b K hK hb‖ ≤ ‖R‖+K := by
  calc
    _ ≤ ‖R •seamColumnShift‖+‖momentDiagonal (fun p : SeamMomentIndex => b p.2.1) K hK (fun p => hb p.2.1)‖ := norm_add_le _ _
    _ ≤ ‖R‖+K := by
      rw [norm_smul]
      exact add_le_add (by nlinarith [seamColumnShift_norm_le_one,norm_nonneg R]) (momentDiagonal_norm_le _ _ _ _)

/-- The whole tensor operation has an exact backward shift after diagonal
compression; both mixed single-shift terms vanish on the actual diagonal. -/
theorem seamNewton_diagonal_compression (R : ℂ) (a b : ℕ → ℂ) (Ka Kb : ℝ)
    (hKa : 0 ≤ Ka) (hKb : 0 ≤ Kb) (ha : ∀ i, ‖a i‖ ≤ Ka) (hb : ∀ i, ‖b i‖ ≤ Kb)
    (e f : Bool) (u : SeamSequence) (n : ℕ) :
    seamDiagonalReading e f
      (seamNewtonRow R a Ka hKa ha (seamNewtonColumn R b Kb hKb hb (seamDiagonalEmbedding e f u))) n=
      R^2*u (n+1)+a n*b n*u n := by
  simp only [seamDiagonalReading_apply,seamNewtonRow_apply,seamNewtonColumn_apply,seamDiagonalEmbedding_apply]
  simp only [and_self,ite_true,Nat.add_eq_left,one_ne_zero,false_and,ite_false,mul_zero,add_zero]
  have hn : ¬n=n+1 := by omega
  simp only [hn,false_and,ite_false,mul_zero,zero_add]
  ring

end
end MeyerGeneralProblem.Adaptive
