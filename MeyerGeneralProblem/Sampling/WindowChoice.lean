module

public import Mathlib.Analysis.SpecificLimits.Normed
import all Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import all Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

@[expose] public section

/-!
# Subcritical Ingham window choice

This elementary sampling module defines the cosine-window floor factor and
chooses a window between the reciprocal-spacing and endpoint thresholds.  It
is deliberately independent of the endpoint operator layer.
-/

namespace MeyerGeneralProblem

noncomputable section

/-- The proved cosine-window Ingham factor appearing in the Gram floor. -/
def inghamFloorFactor (a d : ℝ) : ℝ :=
  (4 * a / Real.pi) * (1 - (2 * a * d)⁻¹ ^ 2)

/-- Every strict signed-square gap `d > 1` admits an Ingham window strictly
between the dual-spacing threshold and the endpoint threshold. -/
theorem exists_subcritical_ingham_window {d : ℝ} (hd : 1 < d) :
    ∃ a : ℝ, 0 < a ∧ 1 / (2 * d) < a ∧ a < 1 / 2 ∧
      0 < inghamFloorFactor a d := by
  have hd₀ : 0 < d := zero_lt_one.trans hd
  have hdinv : d⁻¹ < 1 := inv_lt_one_of_one_lt₀ hd
  have hrewrite : 2 * (1 / (2 * d)) = d⁻¹ := by
    field_simp
  have hlower : 1 / (2 * d) < (1 / 2 : ℝ) := by
    nlinarith
  let a : ℝ := (1 / (2 * d) + 1 / 2) / 2
  refine ⟨a, ?_, ?_, ?_, ?_⟩
  · dsimp [a]
    positivity
  · dsimp [a]
    linarith
  · dsimp [a]
    linarith
  · have ha : 1 / (2 * d) < a := by
      dsimp [a]
      linarith
    have had : 1 < 2 * a * d := by
      have hden : 0 < 2 * d := by positivity
      have hmul := (div_lt_iff₀ hden).mp ha
      nlinarith
    unfold inghamFloorFactor
    apply mul_pos (by positivity)
    have hq : 0 < 2 * a * d := zero_lt_one.trans had
    have hinv : (2 * a * d)⁻¹ < 1 := by
      rw [inv_lt_one₀ hq]
      exact had
    have hinv0 : 0 ≤ (2 * a * d)⁻¹ := inv_nonneg.mpr hq.le
    nlinarith [sq_nonneg ((2 * a * d)⁻¹)]

end

end MeyerGeneralProblem
