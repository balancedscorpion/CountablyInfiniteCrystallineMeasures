module

public import MeyerGeneralProblem.Carrier.TwoSided

@[expose] public section

/-!
# Strict-subcritical carrier tails

The epsilon/eventual formulation is the working form of the strict density
inequality. Its constant `1 / 2` is the critical signed-square spacing.
-/

namespace MeyerGeneralProblem

namespace TwoSidedCarrier

/-- Quantitative strict subcriticality on both index tails. -/
def StrictSubcritical (Λ : TwoSidedCarrier) : Prop :=
  ∃ ε > 0, ∃ N : ℕ, ∀ j : ℤ, N ≤ Int.natAbs j →
    |Λ j| * (Λ (j + 1) - Λ j) ≥ 1 / 2 + ε

theorem StrictSubcritical.gap_pos {Λ : TwoSidedCarrier}
    (hΛ : Λ.StrictSubcritical) :
    ∃ ε > 0, ∃ N : ℕ, ∀ j : ℤ, N ≤ Int.natAbs j →
      0 < Λ (j + 1) - Λ j ∧
      1 / 2 + ε ≤ |Λ j| * (Λ (j + 1) - Λ j) := by
  rcases hΛ with ⟨ε, hε, N, hN⟩
  refine ⟨ε, hε, N, ?_⟩
  intro j hj
  exact ⟨sub_pos.mpr (Λ.strictMono (by omega)), hN j hj⟩

end TwoSidedCarrier

end MeyerGeneralProblem
