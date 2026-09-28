module

public import MeyerGeneralProblem.Cardinal.Adaptive.SeamShiftOperators
public import MeyerGeneralProblem.Cardinal.Adaptive.FullGraphBounds
public import Mathlib.Analysis.Real.Pi.Bounds
import all Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section

/-! # Quantitative full seam kernel at the accepted constants -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section

/-- The signed leading backward-shift coefficient in the actual gauge convention. -/
def seamLeadingCoefficient : ℂ := -Complex.I*(1/4096)/(2*(Real.pi : ℂ))

theorem seamLeadingCoefficient_norm : ‖seamLeadingCoefficient‖=(1/4096 : ℝ)/(2*Real.pi) := by
  simp [seamLeadingCoefficient,norm_div,norm_mul,Complex.norm_real,abs_of_pos Real.pi_pos]

theorem seamLeadingCoefficient_ne_zero : seamLeadingCoefficient ≠ 0 := by
  apply norm_ne_zero_iff.mp
  rw [seamLeadingCoefficient_norm]
  positivity

/-- The source's 300R² perturbation is genuinely smaller than 75/128 of
 the leading coefficient, using the actual value of π. -/
theorem seam_error_ratio (T : SeamSequence →L[ℂ] SeamSequence)
    (hT : ‖T‖ ≤ 300*(1/4096 : ℝ)^2) :
    ‖T‖ ≤ (75/128 : ℝ)*‖seamLeadingCoefficient‖ := by
  apply hT.trans
  rw [seamLeadingCoefficient_norm,← mul_div_assoc]
  apply (le_div_iff₀ (by positivity : 0 < 2*Real.pi)).mpr
  nlinarith [Real.pi_lt_four]

theorem seam_error_lt_leading (T : SeamSequence →L[ℂ] SeamSequence)
    (hT : ‖T‖ ≤ 300*(1/4096 : ℝ)^2) : ‖T‖ < ‖seamLeadingCoefficient‖ := by
  have hp := norm_pos_iff.mpr seamLeadingCoefficient_ne_zero
  have hb := seam_error_ratio T hT
  nlinarith

/-- The actual normalized full kernel, obtained from the complete right-block inverse. -/
def seamCanonicalKernelVector (T : SeamSequence →L[ℂ] SeamSequence)
    (hT : ‖T‖ ≤ 300*(1/4096 : ℝ)^2) : SeamSequence :=
  perturbedShiftKernelVector seamLeadingCoefficient seamLeadingCoefficient_ne_zero
    seamBackwardShift T seamForwardShift seamForwardShift_norm_le_one
      (seam_error_lt_leading T hT) seamFirstVector

@[simp] theorem seamCanonicalKernelVector_reading (T : SeamSequence →L[ℂ] SeamSequence)
    (hT : ‖T‖ ≤ 300*(1/4096 : ℝ)^2) : seamFirstReading (seamCanonicalKernelVector T hT)=1 :=
  perturbedShiftKernelVector_reading _ _ _ _ _ _ _ _ _ seamFirstReading_first seamFirstReading_forward

theorem seamCanonicalKernelVector_mem (T : SeamSequence →L[ℂ] SeamSequence)
    (hT : ‖T‖ ≤ 300*(1/4096 : ℝ)^2) :
    perturbedBackwardShift seamLeadingCoefficient seamBackwardShift T (seamCanonicalKernelVector T hT)=0 :=
  perturbedShiftKernelVector_mem _ _ _ _ _ seamBackward_forward _ _ _

theorem seamCanonicalKernelVector_stability (T : SeamSequence →L[ℂ] SeamSequence)
    (hT : ‖T‖ ≤ 300*(1/4096 : ℝ)^2) :
    ‖seamCanonicalKernelVector T hT-seamFirstVector‖ ≤
      (‖seamLeadingCoefficient‖-‖T‖)⁻¹*‖T seamFirstVector‖ := by
  have h := perturbedShiftKernelVector_stability seamLeadingCoefficient seamLeadingCoefficient_ne_zero
    seamBackwardShift T seamForwardShift seamForwardShift_norm_le_one
      (seam_error_lt_leading T hT) seamFirstVector
  simpa only [perturbedBackwardShift,ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
    seamBackward_first,smul_zero,zero_add,seamCanonicalKernelVector] using h

/-- The normalized whole diagonal kernel has a uniform norm below three. -/
theorem seamCanonicalKernelVector_norm (T : SeamSequence →L[ℂ] SeamSequence)
    (hT : ‖T‖ ≤ 300*(1/4096 : ℝ)^2) : ‖seamCanonicalKernelVector T hT‖ ≤ 3 := by
  have hp : 0 < ‖seamLeadingCoefficient‖-‖T‖ := sub_pos.mpr (seam_error_lt_leading T hT)
  have hres : ‖T seamFirstVector‖ ≤ ‖T‖ := by
    simpa only [seamFirstVector_norm,mul_one] using T.le_opNorm seamFirstVector
  have hrat : (‖seamLeadingCoefficient‖-‖T‖)⁻¹*‖T‖ ≤ (75/53 : ℝ) := by
    rw [inv_mul_eq_div]
    apply (div_le_iff₀ hp).mpr
    nlinarith [seam_error_ratio T hT]
  have hdist := (seamCanonicalKernelVector_stability T hT).trans
    (mul_le_mul_of_nonneg_left hres (by positivity))
  have hnorm := norm_le_norm_sub_add (seamCanonicalKernelVector T hT) seamFirstVector
  rw [seamFirstVector_norm] at hnorm
  linarith

/-- Every full kernel vector is exactly its genuine zeroth coordinate times
 the constructed normalized vector. -/
theorem seam_kernel_eq_smul (T : SeamSequence →L[ℂ] SeamSequence)
    (hT : ‖T‖ ≤ 300*(1/4096 : ℝ)^2) (u : SeamSequence)
    (hu : perturbedBackwardShift seamLeadingCoefficient seamBackwardShift T u=0) :
    u=u 0 •seamCanonicalKernelVector T hT :=
  perturbedShift_kernel_eq_smul _ _ _ _ _ seamBackward_forward _ _ _ _ seamSequence_decomposition u hu

end
end MeyerGeneralProblem.Adaptive
