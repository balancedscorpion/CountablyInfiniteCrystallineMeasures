module

public import MeyerGeneralProblem.Atomic.BesselSynthesis
public import MeyerGeneralProblem.Gram.CoefficientModel

@[expose] public section

/-!
# Abstract trace synthesis systems

A trace system is a family in a complex Hilbert space together with genuine
Bessel analysis data.  Its synthesis operator is therefore the Hilbert
adjoint of a bounded analysis map, rather than a formal infinite sum.

No lower Riesz bound or conditioning assertion is part of this structure.
Those are separate fields of `TracePresentation`.
-/

namespace MeyerGeneralProblem

noncomputable section

open scoped lp

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A Hilbert-space trace family with a genuine bounded analysis/synthesis
pair.  This is the upper Bessel half of a trace presentation. -/
structure TraceSystem (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (iota : Type*) where
  /-- The trace atoms. -/
  atom : iota → H
  /-- Bounded analysis data whose adjoint synthesizes the atoms. -/
  bessel : BesselAnalysis atom

namespace TraceSystem

variable {iota : Type*}

/-- The genuine infinite synthesis operator supplied by the Bessel data. -/
def synthesis (T : TraceSystem H iota) : CoefficientSpace iota →L[ℂ] H :=
  T.bessel.synthesis

@[simp]
theorem synthesis_coefficientAtom [DecidableEq iota]
    (T : TraceSystem H iota) (i : iota) :
    T.synthesis (coefficientAtom i) = T.atom i :=
  T.bessel.synthesis_coefficientAtom i

/-- The coefficient Gram of a trace synthesis system. -/
def gram (T : TraceSystem H iota) :
    CoefficientSpace iota →L[ℂ] CoefficientSpace iota :=
  coefficientGram T.synthesis

end TraceSystem

end

end MeyerGeneralProblem
