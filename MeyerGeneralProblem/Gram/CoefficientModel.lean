module

import all Mathlib.Analysis.InnerProductSpace.Adjoint

public import MeyerGeneralProblem.Atomic.RieszSynthesis
public import MeyerGeneralProblem.Gram.Whitening
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import all Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

@[expose] public section

/-!
# Coefficient Gram and whitened cross models

The physical and Fourier atomic systems are first synthesized from the same
coefficient Hilbert space. Their raw Gram and cross operators are then
whitened globally. The results below prove that this construction is exact:
whitened synthesis is isometric and its cross operator is precisely the
two-sided whitened raw cross matrix.
-/

namespace MeyerGeneralProblem

noncomputable section

open scoped lp

variable {C H : Type*}
  [NormedAddCommGroup C] [InnerProductSpace ℂ C] [CompleteSpace C]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Coefficient Gram operator of a synthesis map. -/
def coefficientGram (S : C →L[ℂ] H) : C →L[ℂ] C :=
  S.adjoint.comp S

/-- Raw coefficient cross operator between two synthesis maps. -/
def rawCoefficientCross (S T : C →L[ℂ] H) : C →L[ℂ] C :=
  S.adjoint.comp T

/-- Globally whitened synthesis map. -/
def whitenedSynthesis (S : C →L[ℂ] H) : C →L[ℂ] H :=
  S.comp (gramWhitener (coefficientGram S))

/-- The two-sided whitened raw coefficient cross operator. -/
def whitenedCoefficientCross (S T : C →L[ℂ] H) : C →L[ℂ] C :=
  gramWhitener (coefficientGram S) * rawCoefficientCross S T *
    gramWhitener (coefficientGram T)

/-- The real scalar action is compatible with composition on coefficient operators. -/
instance coefficientOperator_isScalarTower {ι : Type*} :
    IsScalarTower ℝ (CoefficientSpace ι →L[ℂ] CoefficientSpace ι)
      (CoefficientSpace ι →L[ℂ] CoefficientSpace ι) := by
  constructor
  intro c A B
  change (c • A) * B = c • (A * B)
  exact ContinuousLinearMap.smul_comp c A B

/-- Real scalars commute with composition on coefficient operators. -/
instance coefficientOperator_smulCommClass {ι : Type*} :
    SMulCommClass ℝ (CoefficientSpace ι →L[ℂ] CoefficientSpace ι)
      (CoefficientSpace ι →L[ℂ] CoefficientSpace ι) := by
  constructor
  intro c A B
  change c • (A * B) = A * (c • B)
  exact (ContinuousLinearMap.comp_smul A c B).symm

/-- The positive square root of an operator on the canonical coefficient
space. The explicit instance removes an ambiguity between the inherited
`ℓ²` normed-space structures. -/
def coefficientSqrt {iota : Type*} [Nontrivial (CoefficientSpace iota)]
    (G : CoefficientSpace iota →L[ℂ] CoefficientSpace iota) :
    CoefficientSpace iota →L[ℂ] CoefficientSpace iota := by
  letI : ContinuousFunctionalCalculus ℝ
      (CoefficientSpace iota →L[ℂ] CoefficientSpace iota) IsSelfAdjoint :=
    IsSelfAdjoint.instContinuousFunctionalCalculus
      (A := CoefficientSpace iota →L[ℂ] CoefficientSpace iota)
  exact CFC.sqrt G

/-- The abstract coefficient-basis family obtained from a positive Gram
operator. This is deliberately not called a point-mass family: identifying
such vectors with genuine Dirac distributions requires the separate
Hermite--Dirac semantic bridge. -/
def coefficientGramAtom {iota : Type*} [DecidableEq iota]
    [Nontrivial (CoefficientSpace iota)]
    (G : CoefficientSpace iota →L[ℂ] CoefficientSpace iota) (i : iota) :
    CoefficientSpace iota :=
  coefficientSqrt G (coefficientAtom i)

set_option linter.style.haveILetI false in
theorem coefficientSqrt_isUnit
    {iota : Type*} [Nontrivial (CoefficientSpace iota)]
    (G : CoefficientSpace iota →L[ℂ] CoefficientSpace iota)
    (hG : IsStrictlyPositive G) : IsUnit (coefficientSqrt G) := by
  letI : ContinuousFunctionalCalculus ℝ
      (CoefficientSpace iota →L[ℂ] CoefficientSpace iota) IsSelfAdjoint :=
    IsSelfAdjoint.instContinuousFunctionalCalculus
      (A := CoefficientSpace iota →L[ℂ] CoefficientSpace iota)
  exact CFC.isUnit_sqrt_iff_isStrictlyPositive.mpr hG

/-- The square-root synthesis equivalence associated with a strictly positive
Gram operator. -/
def gramSynthesisEquiv {iota : Type*} [Nontrivial (CoefficientSpace iota)]
    (G : CoefficientSpace iota →L[ℂ] CoefficientSpace iota)
    (hG : IsStrictlyPositive G) :
    CoefficientSpace iota ≃L[ℂ] CoefficientSpace iota := by
  exact ContinuousLinearEquiv.unitsEquiv ℂ (CoefficientSpace iota)
    (coefficientSqrt_isUnit G hG).unit

@[simp]
theorem gramSynthesisEquiv_apply
    {iota : Type*} [Nontrivial (CoefficientSpace iota)]
    (G : CoefficientSpace iota →L[ℂ] CoefficientSpace iota)
    (hG : IsStrictlyPositive G) (c : CoefficientSpace iota) :
    gramSynthesisEquiv G hG c = coefficientSqrt G c := by
  simp only [gramSynthesisEquiv, ContinuousLinearEquiv.unitsEquiv_apply]
  rw [IsUnit.unit_spec]

/-- Strict positivity of the coefficient Gram operator makes its transformed
coefficient atoms a Riesz basis. -/
theorem coefficientGramAtom_rieszBasis
    {iota : Type*} [DecidableEq iota] [Nontrivial (CoefficientSpace iota)]
    (G : CoefficientSpace iota →L[ℂ] CoefficientSpace iota)
    (hG : IsStrictlyPositive G) :
    IsRieszBasis (coefficientGramAtom G) := by
  refine ⟨gramSynthesisEquiv G hG, ?_⟩
  intro i
  rw [gramSynthesisEquiv_apply]
  rfl

/-- Global Gram whitening turns synthesis into an isometry. -/
theorem whitenedSynthesis_adjoint_comp_self
    (S : C →L[ℂ] H) (hS : IsStrictlyPositive (coefficientGram S)) :
    (whitenedSynthesis S).adjoint.comp (whitenedSynthesis S) = 1 := by
  rw [whitenedSynthesis, ContinuousLinearMap.adjoint_comp]
  simp only [gramWhitener_adjoint]
  change gramWhitener (coefficientGram S) * coefficientGram S *
      gramWhitener (coefficientGram S) = 1
  exact gramWhitener_conjugate (coefficientGram S) hS

/-- Norm preservation of globally whitened synthesis. -/
theorem whitenedSynthesis_norm
    (S : C →L[ℂ] H) (hS : IsStrictlyPositive (coefficientGram S))
    (c : C) :
    ‖whitenedSynthesis S c‖ = ‖c‖ :=
  (whitenedSynthesis S).norm_map_iff_adjoint_comp_self.mpr
    (whitenedSynthesis_adjoint_comp_self S hS) c

/-- Exact cross identity after global whitening. -/
theorem whitenedSynthesis_cross
    (S T : C →L[ℂ] H) :
    (whitenedSynthesis S).adjoint.comp (whitenedSynthesis T) =
      whitenedCoefficientCross S T := by
  rw [whitenedSynthesis, whitenedSynthesis,
    ContinuousLinearMap.adjoint_comp]
  simp only [gramWhitener_adjoint, whitenedCoefficientCross,
    rawCoefficientCross]
  rfl

end

end MeyerGeneralProblem
