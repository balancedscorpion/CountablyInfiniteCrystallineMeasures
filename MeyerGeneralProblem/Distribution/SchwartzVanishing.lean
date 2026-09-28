module

public import MeyerGeneralProblem.Carrier.LocallyFinite
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import all Mathlib.Analysis.Distribution.SchwartzSpace.Basic

@[expose] public section

/-!
# Schwartz functions vanishing on a locally finite carrier

The definitions in this file use only the extensional carrier set.  No
enumeration or separation hypothesis is part of the interface.
-/

namespace MeyerGeneralProblem

/-- A Schwartz function vanishes on every point of an extensional locally
finite carrier. -/
def SchwartzVanishesOn (S : LocallyFiniteCarrier) (f : SchwartzMap ℝ ℂ) : Prop :=
  ∀ x ∈ S.carrier, f x = 0

/-- The complex submodule of Schwartz functions vanishing on a locally
finite carrier. -/
def schwartzVanishingSubmodule (S : LocallyFiniteCarrier) :
    Submodule ℂ (SchwartzMap ℝ ℂ) where
  carrier := {f | SchwartzVanishesOn S f}
  zero_mem' := by
    intro x hx
    simp
  add_mem' := by
    intro f g hf hg x hx
    simp [hf x hx, hg x hx]
  smul_mem' := by
    intro c f hf x hx
    simp [hf x hx]

@[simp]
theorem mem_schwartzVanishingSubmodule_iff
    (S : LocallyFiniteCarrier) (f : SchwartzMap ℝ ℂ) :
    f ∈ schwartzVanishingSubmodule S ↔ SchwartzVanishesOn S f :=
  Iff.rfl

theorem schwartzVanishingSubmodule_antitone
    {S T : LocallyFiniteCarrier} (hST : S.carrier ⊆ T.carrier) :
    schwartzVanishingSubmodule T ≤ schwartzVanishingSubmodule S := by
  intro f hf x hx
  exact hf x (hST hx)

end MeyerGeneralProblem
