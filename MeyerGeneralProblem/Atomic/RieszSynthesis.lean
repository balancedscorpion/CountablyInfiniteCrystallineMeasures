module

public import Mathlib.Analysis.InnerProductSpace.l2Space
import all Mathlib.Analysis.InnerProductSpace.l2Space

@[expose] public section

/-!
# Riesz synthesis on coefficient space

This file fixes the coefficient-space interface used by the atomic Hermite
model.  A Riesz basis is represented by a continuous linear equivalence from
`ℓ²`; this records both the synthesis map and its bounded inverse without
hiding either bound in an unbundled predicate.
-/

namespace MeyerGeneralProblem

noncomputable section

open scoped lp

/-- Square-summable complex coefficients indexed by `ι`. -/
abbrev CoefficientSpace (iota : Type*) := ℓ²(iota, ℂ)

/-- The canonical Hilbert basis of coefficient space. -/
def coefficientHilbertBasis (iota : Type*) :
    HilbertBasis iota ℂ (CoefficientSpace iota) :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)

/-- The canonical unit atom in coefficient space. -/
def coefficientAtom {iota : Type*} (i : iota) :
    CoefficientSpace iota :=
  coefficientHilbertBasis iota i

/-- Finite linear combinations of canonical coefficient atoms are dense. -/
theorem coefficientAtom_dense_span {iota : Type*} [DecidableEq iota] :
    (Submodule.span ℂ (Set.range (coefficientAtom : iota → CoefficientSpace iota))).topologicalClosure =
      ⊤ := by
  rw [show (coefficientAtom : iota → CoefficientSpace iota) =
    fun i => coefficientHilbertBasis iota i by rfl]
  exact (coefficientHilbertBasis iota).dense_span

@[simp]
theorem coefficientAtom_norm {iota : Type*} [DecidableEq iota] (i : iota) :
    ‖coefficientAtom i‖ = 1 := by
  exact (coefficientHilbertBasis iota).orthonormal.1 i

/-- A family is a Riesz basis when it is the image of the canonical `ℓ²`
basis under a bounded linear equivalence. -/
def IsRieszBasis {iota H : Type*} [DecidableEq iota]
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    (v : iota → H) : Prop :=
  ∃ S : CoefficientSpace iota ≃L[ℂ] H,
    ∀ i, S (coefficientAtom i) = v i

/-- The atoms produced by a bounded invertible synthesis map form a Riesz
basis. -/
theorem continuousLinearEquiv_image_isRieszBasis
    {iota H : Type*} [DecidableEq iota]
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    (S : CoefficientSpace iota ≃L[ℂ] H) :
    IsRieszBasis (fun i => S (coefficientAtom i)) :=
  ⟨S, fun _ => rfl⟩

/-- Upper Riesz bound supplied by the synthesis operator norm. -/
theorem rieszSynthesis_norm_le
    {iota H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (S : CoefficientSpace iota ≃L[ℂ] H) (c : CoefficientSpace iota) :
    ‖S c‖ ≤ ‖S.toContinuousLinearMap‖ * ‖c‖ :=
  S.toContinuousLinearMap.le_opNorm c

/-- Lower Riesz bound in a division-free form. -/
theorem rieszSynthesis_norm_le_inverse_mul
    {iota H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (S : CoefficientSpace iota ≃L[ℂ] H) (c : CoefficientSpace iota) :
    ‖c‖ ≤ ‖S.symm.toContinuousLinearMap‖ * ‖S c‖ := by
  simpa using S.symm.toContinuousLinearMap.le_opNorm (S c)

end

end MeyerGeneralProblem
