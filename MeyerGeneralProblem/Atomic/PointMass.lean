module

public import Mathlib.Analysis.Distribution.Support
import all Mathlib.Analysis.Distribution.Support
public import MeyerGeneralProblem.Basic

@[expose] public section

/-!
# Point masses as tempered distributions

This file fixes the concrete atomic object used by the Hermite support
spaces.  It deliberately uses mathlib's genuine Dirac tempered distribution,
so the evaluation and support statements below are not coefficient-model
proxies.
-/

namespace MeyerGeneralProblem

noncomputable section

/-- A point mass at `x`, regarded as a complex tempered distribution. -/
def pointMass (x : ℝ) : TemperedDistribution ℝ ℂ :=
  TemperedDistribution.delta x

@[simp]
theorem pointMass_apply (x : ℝ) (φ : SchwartzMap ℝ ℂ) :
    pointMass x φ = φ x :=
  rfl

/-- A point mass has exactly singleton distributional support. -/
@[simp]
theorem dsupport_pointMass (x : ℝ) :
    Distribution.dsupport (pointMass x) = {x} := by
  exact Distribution.TemperedDistribution.dsupport_delta x

/-- Distinct locations give distinct point-mass distributions. -/
theorem pointMass_injective : Function.Injective pointMass := by
  intro x y hxy
  have hs : ({x} : Set ℝ) = {y} := by
    rw [← dsupport_pointMass x, ← dsupport_pointMass y, hxy]
  exact Set.singleton_eq_singleton_iff.mp hs

@[simp]
theorem pointMass_inj {x y : ℝ} : pointMass x = pointMass y ↔ x = y :=
  pointMass_injective.eq_iff

end

end MeyerGeneralProblem
