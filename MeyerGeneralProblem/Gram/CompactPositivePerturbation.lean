module

public import MeyerGeneralProblem.Gram.Whitening
public import Mathlib.Analysis.InnerProductSpace.Spectrum
import all Mathlib.Analysis.InnerProductSpace.Spectrum

@[expose] public section

/-!
# Injective positive compact perturbations of a positive isomorphism

The Fredholm alternative eliminates the only remaining obstruction in a
positive compact perturbation of a strictly positive model: a nonzero kernel.
This file packages that argument independently of the carrier construction.
-/

namespace MeyerGeneralProblem

noncomputable section

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- A positive scalar Loewner floor makes an operator strictly positive. -/
theorem strictlyPositive_of_positive_scalar_floor [Nontrivial E]
    (G : E →L[ℂ] E) {A : ℝ} (hA : 0 < A)
    (hfloor : A • (1 : E →L[ℂ] E) ≤ G) :
    IsStrictlyPositive G := by
  have hscalar : IsStrictlyPositive (A • (1 : E →L[ℂ] E)) :=
    IsStrictlyPositive.smul hA isStrictlyPositive_one
  exact hscalar.of_le hfloor

/-- If a nonnegative operator is an injective compact perturbation of a
strictly positive operator, then it is strictly positive. -/
theorem strictlyPositive_of_compact_perturbation_of_injective
    (G H : E →L[ℂ] E) (hG : 0 ≤ G) (hH : IsStrictlyPositive H)
    (hcompact : IsCompactOperator (G - H)) (hinj : Function.Injective G) :
    IsStrictlyPositive G := by
  let R : E →L[ℂ] E := ↑hH.isUnit.unit⁻¹
  let B : E →L[ℂ] E := R * (H - G)
  have hreverse : IsCompactOperator (H - G) := by
    have heq : H - G = -(G - H) := by abel
    rw [heq]
    exact hcompact.neg
  have hBcompact : IsCompactOperator B := by
    dsimp [B]
    change IsCompactOperator (R ∘ (H - G))
    exact hreverse.clm_comp R
  have hHR : H * R = 1 := by
    simp [R]
  have hfactor : H * (1 - B) = G := by
    dsimp [B]
    rw [mul_sub, mul_one, ← mul_assoc, hHR, one_mul]
    abel
  have hnoEigen :
      ¬ Module.End.HasEigenvalue (B : Module.End ℂ E) (1 : ℂ) := by
    intro heigen
    obtain ⟨x, hxEigen, hxne⟩ := heigen.exists_hasEigenvector
    simp only [Module.End.mem_genEigenspace_one, one_smul] at hxEigen
    change B x = x at hxEigen
    have honeSub : (1 - B) x = 0 := by simp [hxEigen]
    have hGx : G x = 0 := by
      calc
        G x = (H * (1 - B)) x :=
          congrArg (fun T : E →L[ℂ] E => T x) hfactor.symm
        _ = H ((1 - B) x) := rfl
        _ = 0 := by rw [honeSub, map_zero]
    exact hxne (hinj (by simpa using hGx))
  have hres : (1 : ℂ) ∈ resolventSet ℂ B :=
    (hBcompact.hasEigenvalue_or_mem_resolventSet one_ne_zero).resolve_left
      hnoEigen
  have honeSubUnit : IsUnit (1 - B) := by
    rw [spectrum.mem_resolventSet_iff] at hres
    simpa using hres
  rw [IsStrictlyPositive.iff_of_unital]
  refine ⟨hG, ?_⟩
  rw [← hfactor]
  exact hH.isUnit.mul honeSubUnit

/-- An injective synthesis with closed range has a strictly positive Gram.
This is the closed-range form of the lower Riesz bound. -/
theorem adjoint_comp_self_strictlyPositive_of_injective_of_isClosed_range
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial E]
    (S : E →L[ℂ] H) (hinj : Function.Injective S)
    (hclosed : IsClosed (Set.range S)) :
    IsStrictlyPositive (S.adjoint.comp S) := by
  obtain ⟨K, hK⟩ :=
    S.antilipschitz_of_injective_of_isClosed_range hinj hclosed
  have hKne : K ≠ 0 := by
    intro hKzero
    obtain ⟨x, hx⟩ := exists_ne (0 : E)
    have hbound := hK.le_mul_dist x 0
    rw [hKzero, NNReal.coe_zero, zero_mul] at hbound
    have hdist : dist x 0 ≠ 0 := dist_ne_zero.mpr hx
    exact hdist (le_antisymm hbound dist_nonneg)
  have hKposNN : 0 < K := pos_iff_ne_zero.mpr hKne
  have hKpos : 0 < (K : ℝ) := by exact_mod_cast hKposNN
  let A : ℝ := ((K : ℝ) ^ 2)⁻¹
  have hA : 0 < A := inv_pos.mpr (sq_pos_of_pos hKpos)
  have hlower (x : E) : A * ‖x‖ ^ 2 ≤ ‖S x‖ ^ 2 := by
    have hbound := hK.le_mul_dist x 0
    simp only [dist_zero_right, map_zero] at hbound
    have hsquare : ‖x‖ ^ 2 ≤ ((K : ℝ) * ‖S x‖) ^ 2 := by
      nlinarith [norm_nonneg x, norm_nonneg (S x)]
    calc
      A * ‖x‖ ^ 2 ≤ A * (((K : ℝ) * ‖S x‖) ^ 2) :=
        mul_le_mul_of_nonneg_left hsquare hA.le
      _ = ‖S x‖ ^ 2 := by
        dsimp only [A]
        field_simp
  have hfloor : A • (1 : E →L[ℂ] E) ≤ S.adjoint.comp S := by
    rw [ContinuousLinearMap.le_def]
    apply ContinuousLinearMap.isPositive_def'.mpr
    constructor
    · apply IsSelfAdjoint.sub
      · exact (ContinuousLinearMap.isPositive_adjoint_comp_self S).isSelfAdjoint
      · rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
        apply IsSelfAdjoint.smul
        · rw [isSelfAdjoint_iff]
          simp
        · exact ContinuousLinearMap.isPositive_one.isSelfAdjoint
    · intro x
      change 0 ≤ RCLike.re
        (inner ℂ ((S.adjoint.comp S - A • 1) x) x)
      rw [sub_apply, inner_sub_left, map_sub]
      simp only [ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.adjoint_inner_left, one_apply_eq_self,
        smul_apply]
      rw [← norm_sq_eq_re_inner]
      rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
      rw [inner_smul_real_left, RCLike.smul_re]
      rw [← norm_sq_eq_re_inner]
      linarith [hlower x]
  exact strictlyPositive_of_positive_scalar_floor
    (S.adjoint.comp S) hA hfloor

end

end MeyerGeneralProblem
