module

public import MeyerGeneralProblem.Hilbert.CompactModels
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import all Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.IntegralRepresentation
import all Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.IntegralRepresentation

@[expose] public section

/-!
# Gram whitening by inverse square root

For a strictly positive Gram operator `G`, its continuous-functional-calculus
power `G⁻¹ᐟ²` is the canonical whitener.  The main result converts a lower
operator floor `A I ≤ G` into the quantitative norm bound required by the
abstract endpoint squeeze.
-/

namespace MeyerGeneralProblem

open CFC MeasureTheory Set

noncomputable section

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The inverse-square-root whitener of a Gram operator. -/
def gramWhitener (G : E →L[ℂ] E) : E →L[ℂ] E :=
  G ^ (-(1 / 2) : ℝ)

theorem gramWhitener_nonneg (G : E →L[ℂ] E) :
    0 ≤ gramWhitener G :=
  CFC.rpow_nonneg

theorem gramWhitener_isSelfAdjoint (G : E →L[ℂ] E) :
    IsSelfAdjoint (gramWhitener G) :=
  (gramWhitener_nonneg G).isSelfAdjoint

@[simp]
theorem gramWhitener_adjoint (G : E →L[ℂ] E) :
    (gramWhitener G).adjoint = gramWhitener G := by
  rw [← ContinuousLinearMap.star_eq_adjoint]
  exact (gramWhitener_isSelfAdjoint G).star_eq

/-- Whitening conjugates a strictly positive Gram operator to the identity. -/
theorem gramWhitener_conjugate (G : E →L[ℂ] E)
    (hG : IsStrictlyPositive G) :
    gramWhitener G * G * gramWhitener G = 1 := by
  simpa only [gramWhitener] using CFC.conjugate_rpow_neg_one_half G hG

/-- The Gram operator of the whitener is the inverse first power of `G`. -/
theorem gramWhitener_adjoint_comp_self (G : E →L[ℂ] E)
    (hG : IsStrictlyPositive G) :
    (gramWhitener G).adjoint.comp (gramWhitener G) = G ^ (-1 : ℝ) := by
  rw [gramWhitener_adjoint]
  change gramWhitener G * gramWhitener G = G ^ (-1 : ℝ)
  rw [gramWhitener, ← CFC.rpow_add hG.isUnit]
  congr 1
  norm_num

/-- A positive scalar multiple of the identity has the expected negative
first real power. -/
theorem scalarId_rpow_neg_one {A : ℝ} (hA : 0 < A) :
    (A • (1 : E →L[ℂ] E)) ^ (-1 : ℝ) =
      A⁻¹ • (1 : E →L[ℂ] E) := by
  simp only [← Algebra.algebraMap_eq_smul_one]
  rw [CFC.rpow_eq_cfc_real (isStrictlyPositive_algebraMap hA).nonneg,
    cfc_algebraMap]
  rw [Real.rpow_neg_one]

/-- A lower Gram floor reverses under the negative first power. -/
theorem gramWhitener_gram_le_inv_floor [Nontrivial E]
    (G : E →L[ℂ] E) {A : ℝ} (hA : 0 < A)
    (hfloor : A • (1 : E →L[ℂ] E) ≤ G) :
    (gramWhitener G).adjoint.comp (gramWhitener G) ≤
      A⁻¹ • (1 : E →L[ℂ] E) := by
  have hscalar : IsStrictlyPositive (A • (1 : E →L[ℂ] E)) :=
    IsStrictlyPositive.smul hA isStrictlyPositive_one
  have hG : IsStrictlyPositive G := hscalar.of_le hfloor
  rw [gramWhitener_adjoint_comp_self G hG, ← scalarId_rpow_neg_one hA]
  exact CStarAlgebra.rpow_neg_one_le_rpow_neg_one hfloor hscalar

/-- Norm form of the inverse-square-root estimate. -/
theorem gramWhitener_norm_sq_le_inv [Nontrivial E]
    (G : E →L[ℂ] E) {A : ℝ} (hA : 0 < A)
    (hfloor : A • (1 : E →L[ℂ] E) ≤ G) :
    ‖gramWhitener G‖ ^ 2 ≤ A⁻¹ :=
  norm_sq_le_of_gram_le (gramWhitener G) (inv_nonneg.mpr hA.le)
    (gramWhitener_gram_le_inv_floor G hA hfloor)

/-- Compact Gram perturbations have compact differences of all positive
resolvents.  This is the pointwise resolvent input for the integral formula
for the inverse square root. -/
theorem compact_shiftedInverse_sub_shiftedInverse
    (G H : E →L[ℂ] E) (hG : IsStrictlyPositive G)
    (hH : IsStrictlyPositive H) (hcompact : IsCompactOperator (G - H))
    (t : ℝ) (ht : 0 ≤ t) :
    IsCompactOperator
      (Ring.inverse (G + t • (1 : E →L[ℂ] E)) -
        Ring.inverse (H + t • (1 : E →L[ℂ] E))) := by
  have htId : 0 ≤ t • (1 : E →L[ℂ] E) := smul_nonneg ht zero_le_one
  have hGunit : IsUnit (G + t • (1 : E →L[ℂ] E)) :=
    (hG.add_nonneg htId).isUnit
  have hHunit : IsUnit (H + t • (1 : E →L[ℂ] E)) :=
    (hH.add_nonneg htId).isUnit
  have hdiff : IsCompactOperator
      ((G + t • (1 : E →L[ℂ] E)) -
        (H + t • (1 : E →L[ℂ] E))) := by
    have heq : (G + t • (1 : E →L[ℂ] E)) -
        (H + t • (1 : E →L[ℂ] E)) = G - H := by abel
    rw [heq]
    exact hcompact
  exact compact_ringInverse_sub_ringInverse _ _ hGunit hHunit hdiff

/-- On a positive operator, the non-unital CFC integrand for powers in
`(0, 1)` is a scalar term minus a positive resolvent. -/
theorem cfcₙ_rpowIntegrand₀₁_formula
    (G : E →L[ℂ] E) (hG : 0 ≤ G) {p t : ℝ}
    (hp : p ∈ Ioo 0 1) (ht : 0 < t) :
    cfcₙ (Real.rpowIntegrand₀₁ p t) G =
      algebraMap ℝ (E →L[ℂ] E) (t ^ (p - 1)) -
        t ^ p • Ring.inverse (algebraMap ℝ (E →L[ℂ] E) t + G) := by
  have hqspec : quasispectrum ℝ G ⊆ Ici 0 := by grind
  have hcfc : ContinuousOn (Real.rpowIntegrand₀₁ p t) (quasispectrum ℝ G) :=
    (Real.continuousOn_rpowIntegrand₀₁_Ici hp ht).mono hqspec
  rw [cfcₙ_eq_cfc (hf := hcfc) (hf0 := by simp),
    Real.rpowIntegrand₀₁_eq_sub (by grind) ht]
  have hresolvent : ContinuousOn (fun z : ℝ => (t + z)⁻¹) (spectrum ℝ G) := by
    fun_prop (disch := grind -abstractProof)
  have hshift : ContinuousOn (fun z : ℝ => t + z) (spectrum ℝ G) := by fun_prop
  have hspectrum : ∀ r ∈ spectrum ℝ G, t + r ≠ 0 := by grind
  have hself : IsSelfAdjoint G := hG.isSelfAdjoint
  rw [cfc_sub (fun _ : ℝ => t ^ (p - 1))
      (fun z : ℝ => t ^ p * (t + z)⁻¹) G
      continuousOn_const (continuousOn_const.mul hresolvent),
    cfc_const _ _ (ha := hself),
    cfc_const_mul _ _ _ (hf := hresolvent),
    cfc_inv (f := fun z : ℝ => t + z) (a := G) hspectrum
      (hf := hshift) (ha := hself),
    cfc_const_add t (fun z : ℝ => z) G
      (hf := continuousOn_id) (ha := hself),
    cfc_id' ℝ (ha := hself)]

/-- Compact perturbations give compact differences of the CFC power
integrands.  The common scalar term cancels, leaving the compact resolvent
difference. -/
theorem compact_cfcₙ_rpowIntegrand₀₁_sub
    (G H : E →L[ℂ] E) (hG : IsStrictlyPositive G)
    (hH : IsStrictlyPositive H) (hcompact : IsCompactOperator (G - H))
    {p t : ℝ} (hp : p ∈ Ioo 0 1) (ht : 0 < t) :
    IsCompactOperator
      (cfcₙ (Real.rpowIntegrand₀₁ p t) G -
        cfcₙ (Real.rpowIntegrand₀₁ p t) H) := by
  have hres := compact_shiftedInverse_sub_shiftedInverse
    G H hG hH hcompact t ht.le
  have hres' : IsCompactOperator
      (Ring.inverse (algebraMap ℝ (E →L[ℂ] E) t + G) -
        Ring.inverse (algebraMap ℝ (E →L[ℂ] E) t + H)) := by
    simpa only [← Algebra.algebraMap_eq_smul_one, add_comm] using hres
  have hscaled := hres'.smul (-(t ^ p) : ℝ)
  rw [cfcₙ_rpowIntegrand₀₁_formula G hG.nonneg hp ht,
    cfcₙ_rpowIntegrand₀₁_formula H hH.nonneg hp ht]
  have heq :
      ((algebraMap ℝ (E →L[ℂ] E) (t ^ (p - 1)) -
          t ^ p • Ring.inverse (algebraMap ℝ (E →L[ℂ] E) t + G)) -
        (algebraMap ℝ (E →L[ℂ] E) (t ^ (p - 1)) -
          t ^ p • Ring.inverse (algebraMap ℝ (E →L[ℂ] E) t + H))) =
        (-(t ^ p) : ℝ) •
          (Ring.inverse (algebraMap ℝ (E →L[ℂ] E) t + G) -
            Ring.inverse (algebraMap ℝ (E →L[ℂ] E) t + H)) := by
    module
  rw [heq]
  exact hscaled

/-- The positive square-root functional calculus preserves compact
differences between strictly positive operators. -/
theorem compact_nnrpow_half_sub
    (G H : E →L[ℂ] E) (hG : IsStrictlyPositive G)
    (hH : IsStrictlyPositive H) (hcompact : IsCompactOperator (G - H)) :
    IsCompactOperator
      ((G ^ (1 / 2 : NNReal) - H ^ (1 / 2 : NNReal)) : E →L[ℂ] E) := by
  have hp : (1 / 2 : NNReal) ∈ Ioo 0 1 := by norm_num
  obtain ⟨mu, hmu⟩ :=
    CFC.exists_measure_nnrpow_eq_integral_cfcₙ_rpowIntegrand₀₁
      (E →L[ℂ] E) hp
  obtain ⟨hGint, hGeq⟩ := hmu G hG.nonneg
  obtain ⟨hHint, hHeq⟩ := hmu H hH.nonneg
  rw [hGeq, hHeq, ← integral_sub hGint hHint]
  apply isCompactOperator_integral (hGint.sub hHint)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact compact_cfcₙ_rpowIntegrand₀₁_sub G H hG hH hcompact (by norm_num) ht

/-- The inverse-square-root whitener is the positive square root of the ring
inverse. -/
theorem gramWhitener_eq_sqrt_inverse
    (G : E →L[ℂ] E) (hG : IsStrictlyPositive G) :
    gramWhitener G = CFC.sqrt (Ring.inverse G) := by
  rw [gramWhitener, CFC.sqrt_eq_rpow,
    CFC.inverse_eq_rpow_neg_one (ha := hG),
    CFC.rpow_rpow G (-1 : ℝ) (1 / 2 : ℝ) (by norm_num) (ha := hG)]
  congr 1
  norm_num

/-- Compact Gram perturbations remain compact after applying the canonical
inverse-square-root whitening map. -/
theorem compact_gramWhitener_sub
    (G H : E →L[ℂ] E) (hG : IsStrictlyPositive G)
    (hH : IsStrictlyPositive H) (hcompact : IsCompactOperator (G - H)) :
    IsCompactOperator ((gramWhitener G - gramWhitener H) : E →L[ℂ] E) := by
  have hinv : IsCompactOperator (Ring.inverse G - Ring.inverse H) :=
    compact_ringInverse_sub_ringInverse G H hG.isUnit hH.isUnit hcompact
  have hsqrt := compact_nnrpow_half_sub
    (Ring.inverse G) (Ring.inverse H) hG.ringInverse hH.ringInverse hinv
  rw [gramWhitener_eq_sqrt_inverse G hG,
    gramWhitener_eq_sqrt_inverse H hH,
    CFC.sqrt_eq_nnrpow, CFC.sqrt_eq_nnrpow]
  exact hsqrt

/-- Adjoint form of compact whitening transfer.  Whiteners are self-adjoint,
so it is the same compact difference. -/
theorem compact_gramWhitener_adjoint_sub
    (G H : E →L[ℂ] E) (hG : IsStrictlyPositive G)
    (hH : IsStrictlyPositive H) (hcompact : IsCompactOperator (G - H)) :
    IsCompactOperator
      (((gramWhitener G).adjoint - (gramWhitener H).adjoint) : E →L[ℂ] E) := by
  simpa only [gramWhitener_adjoint] using
    compact_gramWhitener_sub G H hG hH hcompact

end

end MeyerGeneralProblem
