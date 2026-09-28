module

public import MeyerGeneralProblem.Hilbert.CompactPerturbation
public import Mathlib.Analysis.Normed.Group.Quotient
import all Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import all Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section

/-!
# Compact propagation through operator models

The analytic proof constructs a whitened cross operator by multiplying a raw
cross matrix on both sides by whitening maps.  This file proves the operator
algebra needed to pass compact errors through those products and then feed a
strict model norm into the Fredholm endpoint criterion.
-/

namespace MeyerGeneralProblem

open MeasureTheory

noncomputable section

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

set_option linter.style.haveILetI false in
/-- A Bochner integral of compact-operator-valued maps is compact when the
integrand is compact almost everywhere.  The proof passes to the Banach-space
quotient by the norm-closed subspace of compact operators. -/
theorem isCompactOperator_integral
    {X : Type*} [MeasurableSpace X] [CompleteSpace F]
    {f : X → (E →L[ℂ] F)} {mu : Measure X}
    (hf : Integrable f mu)
    (hcompact : ∀ᵐ x ∂mu, IsCompactOperator (f x)) :
    IsCompactOperator ((∫ x, f x ∂mu) : E →L[ℂ] F) := by
  letI : NormedAddCommGroup (E →L[ℂ] F) :=
    ContinuousLinearMap.toNormedAddCommGroup
  letI : NormedSpace ℂ (E →L[ℂ] F) := ContinuousLinearMap.toNormedSpace
  let K : Submodule ℂ (E →L[ℂ] F) := compactOperator (RingHom.id ℂ) E F
  have hK : IsClosed (K : Set (E →L[ℂ] F)) :=
    isClosed_setOfPred_isCompactOperator
  letI hKinst : IsClosed (K : Set (E →L[ℂ] F)) := hK
  letI : NormedAddCommGroup ((E →L[ℂ] F) ⧸ K) :=
    Submodule.Quotient.normedAddCommGroup K
  have hqbound : ∀ T : E →L[ℂ] F, ‖K.mkQ T‖ ≤ 1 * ‖T‖ := by
    intro T
    rw [one_mul, Submodule.mkQ_apply]
    exact Submodule.Quotient.norm_mk_le K T
  let q := K.mkQ.mkContinuous 1 hqbound
  have hqf : ∀ᵐ x ∂mu, q (f x) = 0 := by
    filter_upwards [hcompact] with x hx
    change K.mkQ (f x) = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hx
  have hqint : q (∫ x, f x ∂mu) = 0 := by
    let qr := q.restrictScalars ℝ
    change qr (∫ x, f x ∂mu) = 0
    rw [← ContinuousLinearMap.integral_comp_comm (𝕜 := ℝ) qr hf]
    exact integral_eq_zero_of_ae hqf
  have hmem : (∫ x, f x ∂mu) ∈ K := by
    rw [← Submodule.Quotient.mk_eq_zero K]
    simpa only [q, LinearMap.mkContinuous_apply, Submodule.mkQ_apply] using hqint
  exact hmem

/-- Compact errors in all three factors remain compact after forming a
three-factor operator product. -/
theorem compact_triple_product_sub_model
    (U U₀ X X₀ V V₀ : E →L[ℂ] E)
    (hU : IsCompactOperator (U - U₀))
    (hX : IsCompactOperator (X - X₀))
    (hV : IsCompactOperator (V - V₀)) :
    IsCompactOperator (U * X * V - U₀ * X₀ * V₀) := by
  have h₁ : IsCompactOperator ((U - U₀) * X * V) := by
    change IsCompactOperator ((U - U₀) ∘ (X * V))
    exact hU.comp_clm (X * V)
  have h₂ : IsCompactOperator (U₀ * (X - X₀) * V) := by
    have hright : IsCompactOperator ((X - X₀) * V) := by
      change IsCompactOperator ((X - X₀) ∘ V)
      exact hX.comp_clm V
    change IsCompactOperator (U₀ ∘ ((X - X₀) * V))
    exact hright.clm_comp U₀
  have h₃ : IsCompactOperator (U₀ * X₀ * (V - V₀)) := by
    change IsCompactOperator ((U₀ * X₀) ∘ (V - V₀))
    exact hV.clm_comp (U₀ * X₀)
  have hop : U * X * V - U₀ * X₀ * V₀ =
      (U - U₀) * X * V + U₀ * (X - X₀) * V + U₀ * X₀ * (V - V₀) := by
    noncomm_ring
  rw [hop]
  exact (h₁.add h₂).add h₃

/-- The symmetric specialization used for whitening on the left and right. -/
theorem compact_whitenedCross_sub_model
    (W W₀ Ξ B : E →L[ℂ] E)
    (hW : IsCompactOperator (W - W₀))
    (hΞ : IsCompactOperator (Ξ - B)) :
    IsCompactOperator (W * Ξ * W - W₀ * B * W₀) :=
  compact_triple_product_sub_model W W₀ Ξ B W W₀ hW hΞ hW

/-- Inversion preserves compact differences between invertible bounded
operators.  This resolvent identity is the algebraic input for transferring
continuous functional calculus through compact perturbations. -/
theorem compact_ringInverse_sub_ringInverse
    (G H : E →L[ℂ] E) (hG : IsUnit G) (hH : IsUnit H)
    (hcompact : IsCompactOperator (G - H)) :
    IsCompactOperator (Ring.inverse G - Ring.inverse H) := by
  have hreverse : IsCompactOperator (H - G) := by
    have heq : H - G = -(G - H) := by abel
    rw [heq]
    exact hcompact.neg
  have hright : IsCompactOperator ((H - G) * Ring.inverse H) := by
    change IsCompactOperator ((H - G) ∘ (Ring.inverse H : E →L[ℂ] E))
    exact hreverse.comp_clm (Ring.inverse H : E →L[ℂ] E)
  have hproduct : IsCompactOperator
      (Ring.inverse G * (H - G) * Ring.inverse H) := by
    change IsCompactOperator
      ((Ring.inverse G : E →L[ℂ] E) ∘ ((H - G) * Ring.inverse H))
    exact hright.clm_comp (Ring.inverse G : E →L[ℂ] E)
  rw [Ring.inverse_sub_inverse (show IsUnit G ↔ IsUnit H from iff_of_true hG hH)]
  exact hproduct

/-- Adjoint-side version of `compact_whitenedCross_sub_model`.  It is stated
with explicit compactness of the adjoint factor errors so concrete kernel
estimates can discharge it without requiring a general Schauder theorem. -/
theorem compact_adjoint_whitenedCross_sub_model [CompleteSpace E]
    (W W₀ Ξ B : E →L[ℂ] E)
    (hWAdjoint : IsCompactOperator (W.adjoint - W₀.adjoint))
    (hΞAdjoint : IsCompactOperator (Ξ.adjoint - B.adjoint)) :
    IsCompactOperator ((W * Ξ * W).adjoint - (W₀ * B * W₀).adjoint) := by
  have h := compact_triple_product_sub_model
    W.adjoint W₀.adjoint Ξ.adjoint B.adjoint W.adjoint W₀.adjoint
    hWAdjoint hΞAdjoint hWAdjoint
  have hleft : (W * Ξ * W).adjoint = W.adjoint * Ξ.adjoint * W.adjoint := by
    change ((W.comp Ξ).comp W).adjoint = _
    simp [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.mul_def]
    rw [ContinuousLinearMap.comp_assoc]
  have hright : (W₀ * B * W₀).adjoint = W₀.adjoint * B.adjoint * W₀.adjoint := by
    change ((W₀.comp B).comp W₀).adjoint = _
    simp [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.mul_def]
    rw [ContinuousLinearMap.comp_assoc]
  rw [hleft, hright]
  exact h

/-- An operator upper bound on the Gram operator gives the corresponding
square bound on the operator norm. -/
theorem norm_sq_le_of_gram_le [CompleteSpace E] [Nontrivial E]
    (W : E →L[ℂ] E) {a : ℝ} (ha : 0 ≤ a)
    (hW : W.adjoint.comp W ≤ a • (1 : E →L[ℂ] E)) :
    ‖W‖ ^ 2 ≤ a := by
  rw [pow_two, ← ContinuousLinearMap.norm_adjoint_comp_self]
  calc
    ‖W.adjoint.comp W‖ ≤ ‖a • (1 : E →L[ℂ] E)‖ :=
      CStarAlgebra.norm_le_norm_of_le_of_nonneg hW
        (ContinuousLinearMap.nonneg_iff_isPositive.mpr
          (ContinuousLinearMap.isPositive_adjoint_comp_self W))
    _ = a := by simp [Real.norm_of_nonneg ha]

/-- The norm of a model whitened on both sides is controlled by the square of
the whitener norm times the raw model norm. -/
theorem norm_whitenedModel_le (W B : E →L[ℂ] E) :
    ‖W * B * W‖ ≤ ‖W‖ ^ 2 * ‖B‖ := by
  calc
    ‖W * B * W‖ ≤ ‖W * B‖ * ‖W‖ := norm_mul_le _ _
    _ ≤ (‖W‖ * ‖B‖) * ‖W‖ :=
      mul_le_mul_of_nonneg_right (norm_mul_le W B) (norm_nonneg W)
    _ = ‖W‖ ^ 2 * ‖B‖ := by ring

/-- Quantitative whitening bound in the `β / A` form used by the endpoint
squeeze.  The hypothesis on `W` is the operator-norm consequence of the Gram
floor `A • 1 ≤ H`. -/
theorem norm_whitenedModel_le_div
    (W B : E →L[ℂ] E) {A β : ℝ}
    (hA : 0 < A)
    (hW : ‖W‖ ^ 2 ≤ A⁻¹) (hB : ‖B‖ ≤ β) :
    ‖W * B * W‖ ≤ β / A := by
  calc
    ‖W * B * W‖ ≤ ‖W‖ ^ 2 * ‖B‖ := norm_whitenedModel_le W B
    _ ≤ A⁻¹ * β := mul_le_mul hW hB (norm_nonneg B) (inv_nonneg.mpr hA.le)
    _ = β / A := by rw [div_eq_mul_inv, mul_comm]

/-- A strict ratio `β / A < 1` makes the two-sided whitened model a strict
contraction. -/
theorem norm_whitenedModel_lt_one
    (W B : E →L[ℂ] E) {A β : ℝ}
    (hA : 0 < A)
    (hW : ‖W‖ ^ 2 ≤ A⁻¹) (hB : ‖B‖ ≤ β)
    (hgap : β / A < 1) :
    ‖W * B * W‖ < 1 :=
  (norm_whitenedModel_le_div W B hA hW hB).trans_lt hgap

/-- Operator-order version of the quantitative whitening bound. -/
theorem norm_whitenedModel_lt_one_of_gram_le [CompleteSpace E] [Nontrivial E]
    (W B : E →L[ℂ] E) {A β : ℝ}
    (hA : 0 < A)
    (hW : W.adjoint.comp W ≤ A⁻¹ • (1 : E →L[ℂ] E))
    (hB : ‖B‖ ≤ β) (hgap : β / A < 1) :
    ‖W * B * W‖ < 1 := by
  apply norm_whitenedModel_lt_one W B hA
    (norm_sq_le_of_gram_le W (inv_nonneg.mpr hA.le) hW) hB hgap

variable [CompleteSpace E] [CompleteSpace F]

/-- If both a rectangular operator difference and its adjoint difference are
compact, then the corresponding Gram operators differ compactly. -/
theorem compact_gram_sub_model
    (T B : E →L[ℂ] F)
    (h : IsCompactOperator (T - B))
    (hAdjoint : IsCompactOperator (T.adjoint - B.adjoint)) :
    IsCompactOperator (T.adjoint.comp T - B.adjoint.comp B) := by
  have h₁ : IsCompactOperator ((T.adjoint - B.adjoint).comp T) :=
    hAdjoint.comp_clm T
  have h₂ : IsCompactOperator (B.adjoint.comp (T - B)) :=
    h.clm_comp B.adjoint
  have hop : T.adjoint.comp T - B.adjoint.comp B =
      (T.adjoint - B.adjoint).comp T + B.adjoint.comp (T - B) := by
    ext x
    simp only [sub_apply, add_apply, ContinuousLinearMap.comp_apply, map_sub]
    module
  rw [hop]
  exact h₁.add h₂

/-- A pointwise strict contraction that is a two-sided compact perturbation
of a model of norm below one has operator norm below one. -/
theorem operator_norm_lt_one_of_compact_model
    [Nontrivial E] (T B : E →L[ℂ] F)
    (hle : ‖T‖ ≤ 1)
    (hpoint : ∀ x : E, ‖x‖ = 1 → ‖T x‖ < 1)
    (h : IsCompactOperator (T - B))
    (hAdjoint : IsCompactOperator (T.adjoint - B.adjoint))
    (hmodel : ‖B‖ < 1) :
    ‖T‖ < 1 := by
  apply operator_norm_lt_one_of_compact_gram_model T (B.adjoint.comp B)
    hle hpoint (compact_gram_sub_model T B h hAdjoint)
  rw [ContinuousLinearMap.norm_adjoint_comp_self]
  nlinarith [norm_nonneg B]

/-- Abstract reduced-cross squeeze against a strict operator model.  This is
the endpoint consumer for a concrete whitened model and its compact error. -/
theorem reducedCross_norm_lt_one_of_models
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M N : Submodule ℂ H) [CompleteSpace M] [CompleteSpace N]
    [N.HasOrthogonalProjection]
    (B : (intersectionIn M N).orthogonal →L[ℂ] N)
    (h : IsCompactOperator (reducedCross M N - B))
    (hAdjoint : IsCompactOperator ((reducedCross M N).adjoint - B.adjoint))
    (hmodel : ‖B‖ < 1) :
    ‖reducedCross M N‖ < 1 := by
  rcases subsingleton_or_nontrivial ((intersectionIn M N).orthogonal) with hX | hX
  · have hzero : reducedCross M N = 0 := by
      ext x
      have hx : x = 0 := Subsingleton.elim _ _
      subst x
      simp
    simp [hzero]
  · let hXInst : Nontrivial ((intersectionIn M N).orthogonal) := hX
    apply operator_norm_lt_one_of_compact_model (reducedCross M N) B
      (reducedCross_norm_le_one M N) ?_ h hAdjoint hmodel
    intro x hxnorm
    have hxne : x ≠ 0 := by
      intro hxzero
      subst x
      simp at hxnorm
    simpa [hxnorm] using reducedCross_apply_norm_lt M N x hxne

end

end MeyerGeneralProblem
