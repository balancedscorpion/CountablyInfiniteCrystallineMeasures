module

public import MeyerGeneralProblem.Hilbert.FriedrichsAngle
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import all Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.InnerProductSpace.Spectrum
import all Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.InnerProductSpace.StarOrder
import all Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
import all Mathlib.Analysis.Normed.Operator.Compact.Basic

@[expose] public section

set_option maxHeartbeats 400000

/-!
# Compact operators and norm attainment

The compact-perturbation endpoint argument ultimately needs a maximizing
vector.  This file obtains one for a compact operator by applying the compact
self-adjoint spectral theorem to its Gram operator `T⋆T`.
-/

namespace MeyerGeneralProblem

open ComplexConjugate

noncomputable section

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [Nontrivial E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- A compact operator on a nontrivial complex Hilbert space attains its
operator norm on the unit sphere. -/
theorem compactOperator_norm_attained (T : E →L[ℂ] F)
    (hT : IsCompactOperator T) :
    ∃ x : E, ‖x‖ = 1 ∧ ‖T x‖ = ‖T‖ := by
  by_cases hTzero : T = 0
  · obtain ⟨x, hx⟩ := exists_norm_eq E zero_le_one
    refine ⟨x, hx, ?_⟩
    simp [hTzero]
  let A : E →L[ℂ] E := T.adjoint.comp T
  have hAcompact : IsCompactOperator A := by
    dsimp [A]
    change IsCompactOperator (T.adjoint ∘ T)
    exact hT.clm_comp T.adjoint
  have hApos : 0 ≤ A := by
    exact ContinuousLinearMap.nonneg_iff_isPositive.mpr
      (ContinuousLinearMap.isPositive_adjoint_comp_self T)
  have hAnorm : ‖A‖ ≠ 0 := by
    dsimp [A]
    rw [ContinuousLinearMap.norm_adjoint_comp_self]
    exact mul_ne_zero (norm_ne_zero_iff.mpr hTzero) (norm_ne_zero_iff.mpr hTzero)
  have hspecReal : ‖A‖ ∈ spectrum ℝ A :=
    CStarAlgebra.norm_mem_spectrum_of_nonneg A hApos
  have hspec : (‖A‖ : ℂ) ∈ spectrum ℂ A := by
    simpa using spectrum.algebraMap_mem ℂ hspecReal
  have heigen : Module.End.HasEigenvalue (A : Module.End ℂ E) (‖A‖ : ℂ) :=
    (hAcompact.hasEigenvalue_iff_mem_spectrum (by exact_mod_cast hAnorm)).mpr hspec
  obtain ⟨x, hxEigen, hxne⟩ := heigen.exists_hasEigenvector
  simp only [Module.End.mem_genEigenspace_one] at hxEigen
  change A x = (‖A‖ : ℂ) • x at hxEigen
  have hxnorm : 0 < ‖x‖ := (norm_pos_iff.mpr hxne)
  have hnormSquare : ‖T x‖ ^ 2 = (‖T‖ * ‖x‖) ^ 2 := by
    rw [T.apply_norm_sq_eq_inner_adjoint_right]
    change RCLike.re (inner ℂ x (A x)) = (‖T‖ * ‖x‖) ^ 2
    rw [hxEigen, inner_smul_right, inner_self_eq_norm_sq_to_K]
    dsimp [A]
    rw [ContinuousLinearMap.norm_adjoint_comp_self]
    norm_cast
    ring
  have hnorm : ‖T x‖ = ‖T‖ * ‖x‖ := by
    exact (sq_eq_sq₀ (norm_nonneg (T x))
      (mul_nonneg (norm_nonneg T) (norm_nonneg x))).mp hnormSquare
  let y : E := (‖x‖⁻¹ : ℂ) • x
  have hynorm : ‖y‖ = 1 := by
    dsimp [y]
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hxnorm.le,
      inv_mul_cancel₀ hxnorm.ne']
  refine ⟨y, hynorm, ?_⟩
  dsimp [y]
  rw [map_smul, norm_smul, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg hxnorm.le, hnorm]
  field_simp

/-- A strict gap between the norm of a Gram operator and a bounded model,
together with compactness of their difference, forces norm attainment.  This
is the compact-perturbation form needed by the endpoint argument: the operator
`T` itself need not be compact. -/
theorem norm_attained_of_compact_gram_perturbation (T : E →L[ℂ] F)
    (S : E →L[ℂ] E)
    (hcompact : IsCompactOperator (T.adjoint.comp T - S))
    (hgap : ‖S‖ < ‖T‖ ^ 2) :
    ∃ x : E, ‖x‖ = 1 ∧ ‖T x‖ = ‖T‖ := by
  let A : E →L[ℂ] E := T.adjoint.comp T
  have hAnorm : ‖A‖ = ‖T‖ ^ 2 := by
    dsimp [A]
    rw [ContinuousLinearMap.norm_adjoint_comp_self]
    ring
  have hTne : T ≠ 0 := by
    intro hTzero
    subst T
    exact (not_lt_of_ge (norm_nonneg S)) (by simpa using hgap)
  have hApos : 0 ≤ A := by
    exact ContinuousLinearMap.nonneg_iff_isPositive.mpr
      (ContinuousLinearMap.isPositive_adjoint_comp_self T)
  have hlambdaSpectrum : (‖A‖ : ℂ) ∈ spectrum ℂ A := by
    have hreal : ‖A‖ ∈ spectrum ℝ A :=
      CStarAlgebra.norm_mem_spectrum_of_nonneg A hApos
    simpa using spectrum.algebraMap_mem ℂ hreal
  have hSnorm : ‖S‖ < ‖A‖ := by simpa [hAnorm] using hgap
  have hDunit : IsUnit ((algebraMap ℂ (E →L[ℂ] E)) (‖A‖ : ℂ) - S) := by
    rw [← spectrum.mem_resolventSet_iff]
    apply spectrum.mem_resolventSet_of_norm_lt
    simpa using hSnorm
  let D : E →L[ℂ] E := (algebraMap ℂ (E →L[ℂ] E)) (‖A‖ : ℂ) - S
  have hDunit' : IsUnit D := by simpa [D] using hDunit
  let K : E →L[ℂ] E := A - S
  let R : E →L[ℂ] E := ↑hDunit'.unit⁻¹
  let B : E →L[ℂ] E := R * K
  have hKcompact : IsCompactOperator K := by simpa [K, A] using hcompact
  have hBcompact : IsCompactOperator B := by
    dsimp [B]
    change IsCompactOperator (R ∘ K)
    exact hKcompact.clm_comp R
  have hfactor : D * (1 - B) =
      (algebraMap ℂ (E →L[ℂ] E)) (‖A‖ : ℂ) - A := by
    have hDR : D * R = 1 := by
      simp [R]
    dsimp [B, K]
    rw [mul_sub, mul_one, ← mul_assoc, hDR, one_mul]
    dsimp [D]
    abel
  have hnotUnit : ¬ IsUnit (1 - B) := by
    intro hunit
    have : IsUnit (D * (1 - B)) := hDunit'.mul hunit
    rw [hfactor] at this
    exact (spectrum.mem_iff.mp hlambdaSpectrum) this
  have honeSpectrum : (1 : ℂ) ∈ spectrum ℂ B := by
    rw [spectrum.mem_iff]
    simpa using hnotUnit
  have honeEigen : Module.End.HasEigenvalue (B : Module.End ℂ E) (1 : ℂ) :=
    (hBcompact.hasEigenvalue_iff_mem_spectrum one_ne_zero).mpr honeSpectrum
  obtain ⟨x, hxEigen, hxne⟩ := honeEigen.exists_hasEigenvector
  simp only [Module.End.mem_genEigenspace_one, one_smul] at hxEigen
  change B x = x at hxEigen
  have hKx : K x = D x := by
    have hDR : D * R = 1 := by
      simp [R]
    calc
      K x = (1 : E →L[ℂ] E) (K x) := by simp
      _ = (D * R) (K x) := by rw [hDR]
      _ = D (B x) := by rfl
      _ = D x := congrArg D hxEigen
  have hxA : A x = (‖A‖ : ℂ) • x := by
    have := hKx
    change A x - S x = (‖A‖ : ℂ) • x - S x at this
    exact sub_left_inj.mp this
  have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hxne
  have hnormSquare : ‖T x‖ ^ 2 = (‖T‖ * ‖x‖) ^ 2 := by
    rw [T.apply_norm_sq_eq_inner_adjoint_right]
    change RCLike.re (inner ℂ x (A x)) = (‖T‖ * ‖x‖) ^ 2
    rw [hxA, inner_smul_right, inner_self_eq_norm_sq_to_K]
    dsimp [A]
    rw [ContinuousLinearMap.norm_adjoint_comp_self]
    norm_cast
    ring
  have hnorm : ‖T x‖ = ‖T‖ * ‖x‖ := by
    exact (sq_eq_sq₀ (norm_nonneg (T x))
      (mul_nonneg (norm_nonneg T) (norm_nonneg x))).mp hnormSquare
  let y : E := (‖x‖⁻¹ : ℂ) • x
  have hynorm : ‖y‖ = 1 := by
    dsimp [y]
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hxnorm.le,
      inv_mul_cancel₀ hxnorm.ne']
  refine ⟨y, hynorm, ?_⟩
  dsimp [y]
  rw [map_smul, norm_smul, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg hxnorm.le, hnorm]
  field_simp

/-- An abstract compact-Gram-model criterion for upgrading a pointwise strict
contraction to a strict operator-norm contraction. -/
theorem operator_norm_lt_one_of_compact_gram_model (T : E →L[ℂ] F)
    (S : E →L[ℂ] E)
    (hle : ‖T‖ ≤ 1)
    (hpoint : ∀ x : E, ‖x‖ = 1 → ‖T x‖ < 1)
    (hcompact : IsCompactOperator (T.adjoint.comp T - S))
    (hmodel : ‖S‖ < 1) :
    ‖T‖ < 1 := by
  by_contra hnot
  have hnorm : ‖T‖ = 1 := le_antisymm hle (not_lt.mp hnot)
  have hgap : ‖S‖ < ‖T‖ ^ 2 := by simpa [hnorm] using hmodel
  obtain ⟨x, hxnorm, hxattain⟩ :=
    norm_attained_of_compact_gram_perturbation T S hcompact hgap
  have := hpoint x hxnorm
  rw [hxattain, hnorm] at this
  exact (lt_irrefl 1 this)

/-- Compactness of the reduced cross map supplies the missing maximizing
vector and therefore forces a strict Friedrichs-angle gap. -/
theorem reducedCross_norm_lt_one_of_compact
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M N : Submodule ℂ H) [CompleteSpace M] [N.HasOrthogonalProjection]
    (hcompact : IsCompactOperator (reducedCross M N)) :
    ‖reducedCross M N‖ < 1 := by
  have hNclosed : IsClosed (N : Set H) := by
    rw [← N.orthogonal_orthogonal]
    exact Nᗮ.isClosed_orthogonal
  let hNclosedInst : IsClosed (N : Set H) := hNclosed
  have hNcomplete : CompleteSpace N := inferInstance
  rcases subsingleton_or_nontrivial ((intersectionIn M N).orthogonal) with hX | hX
  · have hzero : reducedCross M N = 0 := by
      ext x
      have hx : x = 0 := Subsingleton.elim _ _
      subst x
      simp
    simp [hzero]
  · let hXInst : Nontrivial ((intersectionIn M N).orthogonal) := hX
    apply reducedCross_norm_lt_one_of_attained
    exact compactOperator_norm_attained (reducedCross M N) hcompact

/-- A compact perturbation of a strict Gram model forces a strict reduced
endpoint gap.  Unlike `reducedCross_norm_lt_one_of_compact`, the reduced cross
operator itself need not be compact. -/
theorem reducedCross_norm_lt_one_of_compact_gram_model
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M N : Submodule ℂ H) [CompleteSpace M] [CompleteSpace N]
    [N.HasOrthogonalProjection]
    (S : (intersectionIn M N).orthogonal →L[ℂ] (intersectionIn M N).orthogonal)
    (hcompact : IsCompactOperator
      ((reducedCross M N).adjoint.comp (reducedCross M N) - S))
    (hmodel : ‖S‖ < 1) :
    ‖reducedCross M N‖ < 1 := by
  rcases subsingleton_or_nontrivial ((intersectionIn M N).orthogonal) with hX | hX
  · have hzero : reducedCross M N = 0 := by
      ext x
      have hx : x = 0 := Subsingleton.elim _ _
      subst x
      simp
    simp [hzero]
  · let hXInst : Nontrivial ((intersectionIn M N).orthogonal) := hX
    apply operator_norm_lt_one_of_compact_gram_model (reducedCross M N) S
      (reducedCross_norm_le_one M N) ?_ hcompact hmodel
    intro x hxnorm
    have hxne : x ≠ 0 := by
      intro hxzero
      subst x
      simp at hxnorm
    simpa [hxnorm] using reducedCross_apply_norm_lt M N x hxne

end

end MeyerGeneralProblem
