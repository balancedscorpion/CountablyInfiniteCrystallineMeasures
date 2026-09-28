module

public import MeyerGeneralProblem.Basic
public import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import all Mathlib.Order.Filter.AtTopBot.CountablyGenerated

@[expose] public section

/-!
# Enumerated two-sided carriers

The primary carrier interface records an increasing enumeration by `ℤ` together
with escape to both ends of the real line. This avoids making a noncanonical
enumeration choice inside every analytic construction.
-/

namespace MeyerGeneralProblem

open Filter

/-- A locally finite two-sided carrier with its increasing enumeration fixed. -/
structure TwoSidedCarrier where
  /-- The increasing enumeration. -/
  point : ℤ → ℝ
  /-- Carrier nodes do not repeat and respect the index order. -/
  strictMono : StrictMono point
  /-- The positive-index tail escapes to `+∞`. -/
  tendsto_atTop : Tendsto point atTop atTop
  /-- The negative-index tail escapes to `-∞`. -/
  tendsto_atBot : Tendsto point atBot atBot

namespace TwoSidedCarrier

variable (Λ : TwoSidedCarrier)

instance : FunLike TwoSidedCarrier ℤ ℝ where
  coe := TwoSidedCarrier.point
  coe_injective := by
    intro Λ Γ h
    cases Λ
    cases Γ
    simp_all

@[simp]
theorem coe_apply (j : ℤ) : Λ j = Λ.point j := rfl

theorem point_lt_point {i j : ℤ} (hij : i < j) : Λ i < Λ j :=
  Λ.strictMono hij

theorem point_le_point {i j : ℤ} (hij : i ≤ j) : Λ i ≤ Λ j :=
  Λ.strictMono.monotone hij

theorem point_ne_point {i j : ℤ} (hij : i ≠ j) : Λ i ≠ Λ j := by
  exact Λ.strictMono.injective.ne hij

/-- Every sufficiently positive node lies to the right of a prescribed threshold. -/
theorem eventually_point_ge (R : ℝ) : ∀ᶠ j : ℤ in atTop, R ≤ Λ j :=
  Λ.tendsto_atTop.eventually (eventually_ge_atTop R)

/-- Every sufficiently negative node lies to the left of a prescribed threshold. -/
theorem eventually_point_le (R : ℝ) : ∀ᶠ j : ℤ in atBot, Λ j ≤ R :=
  Λ.tendsto_atBot.eventually (eventually_le_atBot R)

/-- Only finitely many carrier indices can lie in a bounded physical interval. -/
theorem finite_indices_in_Icc (a b : ℝ) :
    {j : ℤ | Λ j ∈ Set.Icc a b}.Finite := by
  rcases Filter.eventually_atTop.mp (Λ.eventually_point_ge (b + 1)) with ⟨hi, hhi⟩
  rcases Filter.eventually_atBot.mp (Λ.eventually_point_le (a - 1)) with ⟨lo, hlo⟩
  apply (Set.finite_Icc lo hi).subset
  intro j hj
  simp only [Set.mem_ofPred_eq, Set.mem_Icc] at hj ⊢
  constructor
  · by_contra hnot
    have hjlo : j ≤ lo := le_of_not_ge hnot
    have hleft := hlo j hjlo
    linarith
  · by_contra hnot
    have hhij : hi ≤ j := le_of_not_ge hnot
    have hright := hhi j hhij
    linarith

/-- The carrier itself is locally finite as a subset of the real line. -/
theorem finite_carrier_inter_Icc (a b : ℝ) :
    ((Set.range Λ) ∩ Set.Icc a b).Finite := by
  have hfinite := Λ.finite_indices_in_Icc a b
  apply hfinite.image Λ |>.subset
  rintro x ⟨⟨j, rfl⟩, hj⟩
  exact ⟨j, hj, rfl⟩

end TwoSidedCarrier

end MeyerGeneralProblem
