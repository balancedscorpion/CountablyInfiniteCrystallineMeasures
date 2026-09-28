module

public import MeyerGeneralProblem.Cardinal.Adaptive.PerturbedBackwardShift
public import Mathlib.Analysis.InnerProductSpace.l2Space
import all Mathlib.Analysis.InnerProductSpace.l2Space

@[expose] public section

/-! # Genuine backward and forward shifts on the diagonal moment Hilbert space -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section

/-- The actual square-summable diagonal Newton coordinates. -/
abbrev SeamSequence := lp (fun _ : ℕ => ℂ) 2

/-- Delete the first coordinate of an actual square-summable sequence. -/
def seamBackwardVector (u : SeamSequence) : SeamSequence :=
  ⟨fun n => u (n+1),memℓp_gen (((lp.memℓp u).summable (by norm_num)).comp_injective Nat.succ_injective)⟩

/-- Insert a zero coordinate before an actual square-summable sequence. -/
def seamForwardVector (u : SeamSequence) : SeamSequence :=
  ⟨fun n => Nat.casesOn n 0 (fun m => u m),memℓp_gen (by
    apply (summable_nat_add_iff 1).mp
    simpa using (lp.memℓp u).summable (by norm_num))⟩

theorem seamBackwardVector_norm_le (u : SeamSequence) : ‖seamBackwardVector u‖ ≤ ‖u‖ := by
  apply lp.norm_le_of_tsum_le (by norm_num) (norm_nonneg _)
  rw [lp.norm_rpow_eq_tsum (by norm_num)]
  have h := ((lp.memℓp u).summable (by norm_num)).tsum_eq_zero_add
  change (∑' n : ℕ, ‖u (n+1)‖^(2 : ℝ)) ≤ ∑' n : ℕ, ‖u n‖^(2 : ℝ)
  have hh : (∑' n : ℕ, ‖u n‖^(2 : ℝ)) = ‖u 0‖^(2 : ℝ)+(∑' n : ℕ, ‖u (n+1)‖^(2 : ℝ)) := by
    simpa using h
  rw [hh]
  exact le_add_of_nonneg_left (by positivity)

theorem seamForwardVector_norm (u : SeamSequence) : ‖seamForwardVector u‖ = ‖u‖ := by
  rw [lp.norm_eq_tsum_rpow (by norm_num),lp.norm_eq_tsum_rpow (by norm_num)]
  congr 1
  rw [((lp.memℓp (seamForwardVector u)).summable (by norm_num)).tsum_eq_zero_add]
  simp [seamForwardVector]

/-- The bounded backward shift on the actual Hilbert space. -/
def seamBackwardShift : SeamSequence →L[ℂ] SeamSequence :=
  LinearMap.mkContinuous
    { toFun := seamBackwardVector
      map_add' u v := by ext n; rfl
      map_smul' a u := by ext n; rfl } 1
    (fun u => by simpa using seamBackwardVector_norm_le u)

/-- The actual forward isometry, viewed as a bounded operator. -/
def seamForwardShift : SeamSequence →L[ℂ] SeamSequence :=
  LinearMap.mkContinuous
    { toFun := seamForwardVector
      map_add' u v := by
        ext n
        cases n with
        | zero => change (0 : ℂ)=0+0; simp
        | succ n => change u n+v n=u n+v n; rfl
      map_smul' a u := by
        ext n
        cases n with
        | zero => change (0 : ℂ)=a*0; simp
        | succ n => rfl } 1
    (fun u => by simp [seamForwardVector_norm])

@[simp] theorem seamBackwardShift_apply (u : SeamSequence) (n : ℕ) : seamBackwardShift u n=u (n+1) := rfl
@[simp] theorem seamForwardShift_zero (u : SeamSequence) : seamForwardShift u 0=0 := rfl
@[simp] theorem seamForwardShift_succ (u : SeamSequence) (n : ℕ) : seamForwardShift u (n+1)=u n := rfl

theorem seamForwardShift_norm_le_one : ‖seamForwardShift‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  change ‖seamForwardVector u‖ ≤ 1*‖u‖
  simpa only [one_mul] using (le_of_eq (seamForwardVector_norm u))

theorem seamBackwardShift_norm_le_one : ‖seamBackwardShift‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  change ‖seamBackwardVector u‖ ≤ 1*‖u‖
  simpa only [one_mul] using seamBackwardVector_norm_le u

/-- The genuine first-coordinate vector, which represents the limiting corner. -/
def seamFirstVector : SeamSequence := lp.single 2 0 1

/-- Evaluation of the genuine first coordinate as a bounded scalar observation. -/
def seamFirstReading : SeamSequence →L[ℂ] ℂ := lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 0

@[simp] theorem seamFirstReading_apply (u : SeamSequence) : seamFirstReading u=u 0 := rfl

@[simp] theorem seamFirstReading_first : seamFirstReading seamFirstVector=1 := by
  rw [seamFirstReading_apply]
  exact lp.single_apply_self _ _ _

@[simp] theorem seamFirstReading_forward (u : SeamSequence) : seamFirstReading (seamForwardShift u)=0 := rfl

theorem seamFirstVector_norm : ‖seamFirstVector‖=1 := by
  rw [seamFirstVector,lp.norm_single (by norm_num)]
  norm_num

@[simp] theorem seamBackward_forward (u : SeamSequence) : seamBackwardShift (seamForwardShift u)=u := by
  ext n
  rfl

@[simp] theorem seamBackward_first : seamBackwardShift seamFirstVector=0 := by
  ext n
  simp [seamFirstVector]

/-- The exact whole-sequence decomposition, with no finite-support restriction. -/
theorem seamSequence_decomposition (u : SeamSequence) :
    u=seamFirstReading u • seamFirstVector+seamForwardShift (seamBackwardShift u) := by
  ext n
  change u n=u 0*seamFirstVector n+seamForwardShift (seamBackwardShift u) n
  cases n with
  | zero => simp [seamFirstVector]
  | succ n => simp [seamFirstVector]

/-- The generic full-kernel theorem now applies to genuine square-summable
sequences with no supplied shift or coordinate-decomposition certificate. -/
theorem seamPerturbedShift_kernel_finrank (c : ℂ) (hc : c ≠ 0)
    (T : SeamSequence →L[ℂ] SeamSequence) (hT : ‖T‖ < ‖c‖) :
    Module.finrank ℂ (perturbedBackwardShift c seamBackwardShift T).ker=1 :=
  perturbedShift_kernel_finrank c hc seamBackwardShift T seamForwardShift seamBackward_forward
    seamForwardShift_norm_le_one hT seamFirstVector seamFirstReading seamSequence_decomposition
    seamFirstReading_first seamFirstReading_forward

end
end MeyerGeneralProblem.Adaptive
