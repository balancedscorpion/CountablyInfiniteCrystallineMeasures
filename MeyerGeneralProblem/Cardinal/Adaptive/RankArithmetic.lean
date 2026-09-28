module

public import Mathlib.Algebra.Order.Floor.Ring
import all Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Data.Real.Basic
import all Mathlib.Data.Real.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic

@[expose] public section

/-!
# Exact order arithmetic for adaptive cardinal ranks

This file contains only the numerical conversions used by the construction.
It neither assumes nor constructs native source vectors. The lower bound is
zero below order 22; that fact is not a statement that a native layer is zero.
-/

namespace MeyerGeneralProblem.Adaptive

/-- Number of reciprocal directions guaranteed by the native admission bound. -/
def lowerRankBound (p : ℕ) : ℕ := 2 * ((p - 4) / 18)

/-- Number of reciprocal directions allowed by the complete exhaustion bound. -/
def upperRankBound (p : ℕ) : ℕ := 12 * p - 2

/-- A common native order for every generalized antiperiodic coefficient. -/
def liftOrder (p : ℕ) : ℕ := 1000 * (p + 1) ^ 3

/-- Fixed test regularity; it depends only on native order, never stage. -/
def testOrder (p : ℕ) : ℕ := 2 * liftOrder p + 20

/-- Integer floor and natural division give exactly the same clipped count. -/
theorem lowerRankBound_eq_clipped_floor (p : ℕ) :
    (lowerRankBound p : ℤ) =
      2 * max 0 ⌊((p : ℝ) - 4) / 18⌋ := by
  have hfloor : ⌊((p : ℝ) - 4) / 18⌋ = ((p : ℤ) - 4) / 18 := by
    rw [show (18 : ℝ) = ((18 : ℕ) : ℝ) by norm_num, Int.floor_div_natCast]
    norm_num
  rw [hfloor]
  unfold lowerRankBound
  omega

/-- Every small-order lower bound vanishes, without a zero-layer conclusion. -/
theorem lowerRankBound_eq_zero_of_lt_twentyTwo {p : ℕ} (hp : p < 22) :
    lowerRankBound p = 0 := by
  unfold lowerRankBound
  omega

/-- The first guaranteed reciprocal pair occurs at order 22. -/
theorem lowerRankBound_twentyTwo : lowerRankBound 22 = 2 := by decide

/-- Exact admission orders count the first `i` positive blocks, in both directions. -/
theorem lowerRankBound_admission (i : ℕ) :
    lowerRankBound (18 * i + 4) = 2 * i := by
  unfold lowerRankBound
  omega

/-- The explicit order used to defeat any proposed finite rank bound. -/
theorem lowerRankBound_exceeds (B : ℕ) :
    B < lowerRankBound (18 * (B + 1) + 4) := by
  rw [lowerRankBound_admission]
  omega

/-- Counting the two directions of blocks `1,…,6p-1` gives the upper bound. -/
theorem upperRankBound_eq_two_times (p : ℕ) (hp : 1 ≤ p) :
    upperRankBound p = 2 * (6 * p - 1) := by
  unfold upperRankBound
  omega

/-- The numerical lower and upper bounds are compatible at every positive order. -/
theorem lowerRankBound_le_upperRankBound (p : ℕ) (hp : 1 ≤ p) :
    lowerRankBound p ≤ upperRankBound p := by
  unfold lowerRankBound upperRankBound
  omega

/-- An index admitted by the lower-bound count is admitted at the actual order.
Positivity is necessary when the clipped count is zero. -/
theorem admissionOrder_le_of_le_count {i p : ℕ} (hi : 1 ≤ i)
    (hip : i ≤ (p - 4) / 18) : 18 * i + 4 ≤ p := by
  omega

/-- The conservative polynomial lift loss fits strictly inside its fixed budget. -/
theorem lift_loss_lt_liftOrder (p : ℕ) :
    72 * p ^ 2 + 60 * p + 4 < liftOrder p := by
  unfold liftOrder
  nlinarith [sq_nonneg (p : ℤ)]

/-- The fixed test order leaves room beyond the original sixfold native loss. -/
theorem sixfold_order_margin (p : ℕ) : 12 * p + 20 < testOrder p := by
  have h := lift_loss_lt_liftOrder p
  unfold testOrder
  omega

end MeyerGeneralProblem.Adaptive
