module

public import MeyerGeneralProblem.Trace.System
public import MeyerGeneralProblem.Endpoint.WhitenedRange
public import Mathlib.LinearAlgebra.Dimension.Basic
import all Mathlib.LinearAlgebra.Dimension.Basic

@[expose] public section

/-!
# Exact trace presentations of closed subspaces

A trace presentation records all three facts required for sound coordinates:
a genuine Bessel synthesis system, strict positivity of its coefficient Gram,
and exact equality of its synthesis range with the declared closed subspace.
The range equality is deliberately data, so a coordinate construction cannot
silently replace the intended space by the span of its chosen atoms.
-/

namespace MeyerGeneralProblem

noncomputable section

open scoped lp

universe uH ui

variable {H : Type uH}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A well-conditioned Bessel presentation of an exact closed subspace. -/
structure TracePresentation (X : ClosedSubmodule ℂ H) (iota : Type*) where
  /-- The underlying Bessel synthesis system. -/
  system : TraceSystem H iota
  /-- The coefficient Gram is strictly positive. -/
  gram_strictlyPositive : IsStrictlyPositive system.gram
  /-- Synthesis has exactly the declared range. -/
  synthesis_range_eq : system.synthesis.range = X.toSubmodule

namespace TracePresentation

variable {X : ClosedSubmodule ℂ H} {iota : Type ui}

/-- The synthesis operator of a trace presentation. -/
def synthesis (P : TracePresentation X iota) :
    CoefficientSpace iota →L[ℂ] H :=
  P.system.synthesis

/-- The coefficient Gram of a trace presentation. -/
def gram (P : TracePresentation X iota) :
    CoefficientSpace iota →L[ℂ] CoefficientSpace iota :=
  P.system.gram

theorem gram_strictlyPositive' (P : TracePresentation X iota) :
    IsStrictlyPositive (coefficientGram P.synthesis) :=
  P.gram_strictlyPositive

theorem synthesis_range_eq' (P : TracePresentation X iota) :
    P.synthesis.range = X.toSubmodule :=
  P.synthesis_range_eq

/-- The declared closed subspace is also exactly the closed span of the
presented atoms.  This consequence uses both the genuine Bessel synthesis
and strict coefficient-Gram positivity. -/
theorem atomicSupportSubspace_eq [DecidableEq iota]
    (P : TracePresentation X iota) :
    atomicSupportSubspace P.system.atom = X.toSubmodule := by
  calc
    atomicSupportSubspace P.system.atom =
        atomicSupportSubspace
          (fun i ↦ P.synthesis (coefficientAtom i)) := by
      congr 1
      funext i
      exact (P.system.synthesis_coefficientAtom i).symm
    _ = P.synthesis.range :=
      (synthesis_range_eq_atomicSupportSubspace P.synthesis
        P.gram_strictlyPositive').symm
    _ = X.toSubmodule := P.synthesis_range_eq'

/-- Whitening preserves the exact declared synthesis range. -/
theorem whitenedSynthesis_range_eq (P : TracePresentation X iota) :
    (whitenedSynthesis P.synthesis).range = X.toSubmodule := by
  rw [MeyerGeneralProblem.whitenedSynthesis_range_eq P.synthesis
      P.gram_strictlyPositive',
    P.synthesis_range_eq']

/-- The exact unitary coefficient parametrization of the declared closed
subspace obtained by Gram whitening. -/
def whiteningEquiv (P : TracePresentation X iota) :
    CoefficientSpace iota ≃ₗᵢ[ℂ] X.toSubmodule :=
  (whitenedSynthesisIsometry P.synthesis
      P.gram_strictlyPositive').equivRange.trans
    (LinearIsometryEquiv.ofEq _ _ P.whitenedSynthesis_range_eq)

@[simp]
theorem coe_whiteningEquiv_apply (P : TracePresentation X iota)
    (c : CoefficientSpace iota) :
    ((P.whiteningEquiv c : X.toSubmodule) : H) =
      whitenedSynthesis P.synthesis c :=
  rfl

/-- A trace presentation preserves Hamel rank exactly, with universe lifts
made explicit so the trace index and ambient Hilbert space may live in
different universes. -/
theorem coefficient_lift_rank_eq (P : TracePresentation X iota) :
    Cardinal.lift.{uH} (Module.rank ℂ (CoefficientSpace iota)) =
      Cardinal.lift.{ui} (Module.rank ℂ X.toSubmodule) :=
  P.whiteningEquiv.toLinearEquiv.lift_rank_eq

/-- The symmetric form of exact lifted-rank preservation. -/
theorem lift_rank_eq_coefficient (P : TracePresentation X iota) :
    Cardinal.lift.{ui} (Module.rank ℂ X.toSubmodule) =
      Cardinal.lift.{uH} (Module.rank ℂ (CoefficientSpace iota)) :=
  P.coefficient_lift_rank_eq.symm

end TracePresentation

end

end MeyerGeneralProblem
