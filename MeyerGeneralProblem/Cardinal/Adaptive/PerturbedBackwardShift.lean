module

public import MeyerGeneralProblem.Cardinal.Adaptive.FullSchurComplement
public import Mathlib.LinearAlgebra.Dimension.Constructions
import all Mathlib.LinearAlgebra.Dimension.Constructions

@[expose] public section

/-! # The full kernel of a bounded perturbation of a backward shift

The right-block inverse is constructed by a geometric series. The scalar
coordinate faithfully determines the whole kernel, and an actual normalized
kernel vector is produced with quantitative bounds.
-/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- A scalar multiple of the identity as a genuine continuous equivalence. -/
def nonzeroScalarEquiv (c : ℂ) (hc : c ≠ 0) : E ≃L[ℂ] E :=
  ContinuousLinearEquiv.equivOfInverse (c • ContinuousLinearMap.id ℂ E)
    (c⁻¹ • ContinuousLinearMap.id ℂ E)
    (fun x => by simp [smul_smul,hc]) (fun x => by simp [smul_smul,hc])

/-- The actual normalized perturbation of identity. -/
def normalizedScalarPerturbation (c : ℂ) (T : E →L[ℂ] E) : E →L[ℂ] E :=
  ContinuousLinearMap.id ℂ E+c⁻¹ • T

theorem normalizedScalarPerturbation_close (c : ℂ) (hc : c ≠ 0) (T : E →L[ℂ] E)
    (hT : ‖T‖ < ‖c‖) : ‖normalizedScalarPerturbation c T-ContinuousLinearMap.id ℂ E‖ < 1 := by
  rw [normalizedScalarPerturbation,add_sub_cancel_left,norm_smul,norm_inv]
  have hp : 0 < ‖c‖ := norm_pos_iff.mpr hc
  rw [inv_mul_eq_div,div_lt_one hp]
  exact hT

/-- A scalar identity plus a small actual operator has a constructed full inverse. -/
def scalarPerturbationEquiv (c : ℂ) (hc : c ≠ 0) (T : E →L[ℂ] E) (hT : ‖T‖ < ‖c‖) : E ≃L[ℂ] E :=
  (fullNearIdentityEquiv (normalizedScalarPerturbation c T)
    (normalizedScalarPerturbation_close c hc T hT)).trans (nonzeroScalarEquiv c hc)

@[simp] theorem scalarPerturbationEquiv_apply (c : ℂ) (hc : c ≠ 0)
    (T : E →L[ℂ] E) (hT : ‖T‖ < ‖c‖) (x : E) :
    scalarPerturbationEquiv c hc T hT x=c • x+T x := by
  simp [scalarPerturbationEquiv,nonzeroScalarEquiv,ContinuousLinearEquiv.equivOfInverse_apply,
    normalizedScalarPerturbation,smul_add,smul_smul,hc]

/-- The inverse bound is in the original operator norm. -/
theorem scalarPerturbationEquiv_symm_bound (c : ℂ) (hc : c ≠ 0)
    (T : E →L[ℂ] E) (hT : ‖T‖ < ‖c‖) (y : E) :
    ‖(scalarPerturbationEquiv c hc T hT).symm y‖ ≤ (‖c‖-‖T‖)⁻¹*‖y‖ := by
  let x := (scalarPerturbationEquiv c hc T hT).symm y
  have he : c • x+T x=y := by
    simpa only [scalarPerturbationEquiv_apply] using (scalarPerturbationEquiv c hc T hT).apply_symm_apply y
  have ht : ‖c‖*‖x‖ ≤ ‖y‖+‖T‖*‖x‖ := by
    calc
      ‖c‖*‖x‖ = ‖c • x‖ := (norm_smul _ _).symm
      _ = ‖y-T x‖ := by congr 1; rw [← he]; abel
      _ ≤ ‖y‖+‖T x‖ := norm_sub_le _ _
      _ ≤ ‖y‖+‖T‖*‖x‖ := add_le_add le_rfl (T.le_opNorm x)
  change ‖x‖ ≤ _
  rw [inv_mul_eq_div,le_div_iff₀ (sub_pos.mpr hT)]
  nlinarith

/-- The complete perturbed shift operator. -/
def perturbedBackwardShift (c : ℂ) (S T : E →L[ℂ] E) : E →L[ℂ] E := c • S+T

/-- The full forward-shift block is a small perturbation of scalar identity. -/
def perturbedShiftRightEquiv (c : ℂ) (hc : c ≠ 0) (T V : E →L[ℂ] E)
    (hV : ‖V‖ ≤ 1) (hT : ‖T‖ < ‖c‖) : E ≃L[ℂ] E :=
  scalarPerturbationEquiv c hc (T.comp V)
    (((T.opNorm_comp_le V).trans (by nlinarith [norm_nonneg T])).trans_lt hT)

theorem perturbedShiftRightEquiv_apply (c : ℂ) (hc : c ≠ 0) (S T V : E →L[ℂ] E)
    (hSV : ∀ x, S (V x)=x) (hV : ‖V‖ ≤ 1) (hT : ‖T‖ < ‖c‖) (x : E) :
    perturbedShiftRightEquiv c hc T V hV hT x=perturbedBackwardShift c S T (V x) := by
  simp [perturbedShiftRightEquiv,scalarPerturbationEquiv_apply,perturbedBackwardShift,hSV]

/-- The actual normalized kernel vector constructed through the full right-block inverse. -/
def perturbedShiftKernelVector (c : ℂ) (hc : c ≠ 0) (S T V : E →L[ℂ] E)
    (hV : ‖V‖ ≤ 1) (hT : ‖T‖ < ‖c‖) (e₀ : E) : E :=
  e₀-V ((perturbedShiftRightEquiv c hc T V hV hT).symm (perturbedBackwardShift c S T e₀))

theorem perturbedShiftKernelVector_mem (c : ℂ) (hc : c ≠ 0) (S T V : E →L[ℂ] E)
    (hSV : ∀ x, S (V x)=x) (hV : ‖V‖ ≤ 1) (hT : ‖T‖ < ‖c‖) (e₀ : E) :
    perturbedBackwardShift c S T (perturbedShiftKernelVector c hc S T V hV hT e₀)=0 := by
  rw [perturbedShiftKernelVector,map_sub,← perturbedShiftRightEquiv_apply c hc S T V hSV hV hT,
    ContinuousLinearEquiv.apply_symm_apply,sub_self]

theorem perturbedShiftKernelVector_reading (c : ℂ) (hc : c ≠ 0) (S T V : E →L[ℂ] E)
    (hV : ‖V‖ ≤ 1) (hT : ‖T‖ < ‖c‖) (e₀ : E) (q : E →L[ℂ] ℂ)
    (he₀ : q e₀=1) (hqV : ∀ x, q (V x)=0) :
    q (perturbedShiftKernelVector c hc S T V hV hT e₀)=1 := by
  simp only [perturbedShiftKernelVector,map_sub,he₀,hqV,sub_zero]

/-- No complementary coordinate is discarded: every full kernel vector is
the scalar reading times the constructed normalized vector. -/
theorem perturbedShift_kernel_eq_smul (c : ℂ) (hc : c ≠ 0) (S T V : E →L[ℂ] E)
    (hSV : ∀ x, S (V x)=x) (hV : ‖V‖ ≤ 1) (hT : ‖T‖ < ‖c‖)
    (e₀ : E) (q : E →L[ℂ] ℂ) (hdecomp : ∀ u, u=q u • e₀+V (S u))
    (u : E) (hu : perturbedBackwardShift c S T u=0) :
    u=q u • perturbedShiftKernelVector c hc S T V hV hT e₀ := by
  let K := perturbedBackwardShift c S T
  let B := perturbedShiftRightEquiv c hc T V hV hT
  have he : q u • K e₀+B (S u)=0 := by
    rw [perturbedShiftRightEquiv_apply c hc S T V hSV hV hT]
    rw [← map_smul,← map_add,← hdecomp]
    exact hu
  have hSu : S u= -(q u • B.symm (K e₀)) := by
    have hh := congrArg B.symm he
    simp only [map_add,map_smul,map_zero,ContinuousLinearEquiv.symm_apply_apply] at hh
    exact eq_neg_of_add_eq_zero_right hh
  calc
    u=q u • e₀+V (S u) := hdecomp u
    _ = q u • e₀+V (-(q u • B.symm (K e₀))) := by rw [hSu]
    _ = _ := by simp [perturbedShiftKernelVector,K,B,map_neg,map_smul,smul_sub,sub_eq_add_neg]

/-- The normalized vector is nonzero, detected by its actual scalar coordinate. -/
theorem perturbedShiftKernelVector_ne_zero (c : ℂ) (hc : c ≠ 0) (S T V : E →L[ℂ] E)
    (hV : ‖V‖ ≤ 1) (hT : ‖T‖ < ‖c‖) (e₀ : E) (q : E →L[ℂ] ℂ)
    (he₀ : q e₀=1) (hqV : ∀ x, q (V x)=0) :
    perturbedShiftKernelVector c hc S T V hV hT e₀ ≠ 0 := by
  intro he
  have h := perturbedShiftKernelVector_reading c hc S T V hV hT e₀ q he₀ hqV
  rw [he,map_zero] at h
  exact zero_ne_one h

/-- The complete perturbed-shift kernel is exactly the constructed nonzero line. -/
theorem perturbedShift_kernel_eq_span (c : ℂ) (hc : c ≠ 0) (S T V : E →L[ℂ] E)
    (hSV : ∀ x, S (V x)=x) (hV : ‖V‖ ≤ 1) (hT : ‖T‖ < ‖c‖)
    (e₀ : E) (q : E →L[ℂ] ℂ) (hdecomp : ∀ u, u=q u • e₀+V (S u)) :
    (perturbedBackwardShift c S T).ker =
      Submodule.span ℂ {perturbedShiftKernelVector c hc S T V hV hT e₀} := by
  apply le_antisymm
  · intro u hu
    rw [perturbedShift_kernel_eq_smul c hc S T V hSV hV hT e₀ q hdecomp u hu]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  · apply Submodule.span_le.mpr
    intro u hu
    rcases Set.mem_singleton_iff.mp hu with rfl
    exact perturbedShiftKernelVector_mem c hc S T V hSV hV hT e₀

/-- Finite dimensionality and dimension one follow from an actual full-kernel
span, rather than from `finrank` alone. -/
theorem perturbedShift_kernel_finrank (c : ℂ) (hc : c ≠ 0) (S T V : E →L[ℂ] E)
    (hSV : ∀ x, S (V x)=x) (hV : ‖V‖ ≤ 1) (hT : ‖T‖ < ‖c‖)
    (e₀ : E) (q : E →L[ℂ] ℂ) (hdecomp : ∀ u, u=q u • e₀+V (S u))
    (he₀ : q e₀=1) (hqV : ∀ x, q (V x)=0) :
    Module.finrank ℂ (perturbedBackwardShift c S T).ker=1 := by
  rw [perturbedShift_kernel_eq_span c hc S T V hSV hV hT e₀ q hdecomp]
  exact finrank_span_singleton (perturbedShiftKernelVector_ne_zero c hc S T V hV hT e₀ q he₀ hqV)

/-- Uniform control of the actual complete right-block inverse. -/
theorem perturbedShiftRightEquiv_symm_bound (c : ℂ) (hc : c ≠ 0) (T V : E →L[ℂ] E)
    (hV : ‖V‖ ≤ 1) (hT : ‖T‖ < ‖c‖) (y : E) :
    ‖(perturbedShiftRightEquiv c hc T V hV hT).symm y‖ ≤ (‖c‖-‖T‖)⁻¹*‖y‖ := by
  have hTV : ‖T.comp V‖ ≤ ‖T‖ := (T.opNorm_comp_le V).trans (by nlinarith [norm_nonneg T])
  have hb := scalarPerturbationEquiv_symm_bound c hc (T.comp V) (hTV.trans_lt hT) y
  apply hb.trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact inv_anti₀ (sub_pos.mpr hT) (by linarith)

/-- Quantitative stability of the normalized kernel against its first vector.
A smaller bound for the actual residual `K e₀` transfers directly to the full kernel. -/
theorem perturbedShiftKernelVector_stability (c : ℂ) (hc : c ≠ 0) (S T V : E →L[ℂ] E)
    (hV : ‖V‖ ≤ 1) (hT : ‖T‖ < ‖c‖) (e₀ : E) :
    ‖perturbedShiftKernelVector c hc S T V hV hT e₀-e₀‖ ≤
      (‖c‖-‖T‖)⁻¹*‖perturbedBackwardShift c S T e₀‖ := by
  rw [perturbedShiftKernelVector,sub_sub_cancel_left,norm_neg]
  calc
    _ ≤ ‖V‖*‖(perturbedShiftRightEquiv c hc T V hV hT).symm (perturbedBackwardShift c S T e₀)‖ := V.le_opNorm _
    _ ≤ ‖(perturbedShiftRightEquiv c hc T V hV hT).symm (perturbedBackwardShift c S T e₀)‖ := by
      nlinarith [norm_nonneg ((perturbedShiftRightEquiv c hc T V hV hT).symm (perturbedBackwardShift c S T e₀))]
    _ ≤ _ := perturbedShiftRightEquiv_symm_bound c hc T V hV hT _

end
end MeyerGeneralProblem.Adaptive
