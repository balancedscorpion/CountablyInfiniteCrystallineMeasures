module

public import MeyerGeneralProblem.Cardinal.Adaptive.FullSchurComplement
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import all Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecificLimits.Normed
import all Mathlib.Analysis.SpecificLimits.Normed

@[expose] public section

/-! # Full Banach-algebra power series with coefficientwise quantitative bounds -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section

variable {A : Type*} [NormedRing A] [NormOneClass A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- The entire operator power series, without finite compression. -/
def boundedOperatorSeries (c : ℕ → ℂ) (X : A) : A := ∑' n, c n •X^n

theorem boundedOperatorSeries_summable_norm (c : ℕ → ℂ) (hc : ∀ n, ‖c n‖ ≤ 1)
    (X : A) (hX : ‖X‖ < 1) : Summable (fun n => ‖c n •X^n‖) := by
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) _
    (summable_geometric_of_lt_one (norm_nonneg X) hX)
  intro n
  rw [norm_smul]
  exact (mul_le_mul_of_nonneg_right (hc n) (norm_nonneg _)).trans (by simpa using norm_pow_le X n)

theorem boundedOperatorSeries_hasSum (c : ℕ → ℂ) (hc : ∀ n, ‖c n‖ ≤ 1)
    (X : A) (hX : ‖X‖ < 1) : HasSum (fun n => c n •X^n) (boundedOperatorSeries c X) :=
  (boundedOperatorSeries_summable_norm c hc X hX).of_norm.hasSum

/-- Norm control for the complete series follows from an absolutely convergent
geometric majorant in the original Banach-algebra norm. -/
theorem boundedOperatorSeries_norm_le (c : ℕ → ℂ) (hc : ∀ n, ‖c n‖ ≤ 1)
    (X : A) (hX : ‖X‖ < 1) : ‖boundedOperatorSeries c X‖ ≤ (1-‖X‖)⁻¹ := by
  have hs := boundedOperatorSeries_summable_norm c hc X hX
  calc
    _ ≤ ∑' n, ‖c n •X^n‖ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' n, ‖X‖^n := hs.tsum_le_tsum (fun n => by
      rw [norm_smul]
      exact (mul_le_mul_of_nonneg_right (hc n) (norm_nonneg _)).trans (by simpa using norm_pow_le X n))
      (summable_geometric_of_lt_one (norm_nonneg X) hX)
    _ = _ := tsum_geometric_of_lt_one (norm_nonneg X) hX

/-- Exact removal of the constant term leaves the entire shifted series. -/
theorem boundedOperatorSeries_sub_constant (c : ℕ → ℂ) (hc : ∀ n, ‖c n‖ ≤ 1)
    (X : A) (hX : ‖X‖ < 1) :
    boundedOperatorSeries c X-c 0 •(1 : A)=∑' n, c (n+1) •X^(n+1) := by
  have h := ((boundedOperatorSeries_summable_norm c hc X hX).of_norm).tsum_eq_zero_add
  unfold boundedOperatorSeries
  simpa only [pow_zero,add_sub_cancel_left] using congrArg (fun a : A => a-c 0 •1) h

/-- The full nonconstant tail is small, including every feedback power. -/
theorem boundedOperatorSeries_sub_one_bound (c : ℕ → ℂ) (hc : ∀ n, ‖c n‖ ≤ 1)
    (hc0 : c 0=1) (X : A) (hX : ‖X‖ < 1) :
    ‖boundedOperatorSeries c X-1‖ ≤ ‖X‖/(1-‖X‖) := by
  have hs := (boundedOperatorSeries_summable_norm c hc X hX).comp_injective Nat.succ_injective
  have he : boundedOperatorSeries c X-1=∑' n, c (n+1) •X^(n+1) := by
    simpa only [hc0,one_smul] using boundedOperatorSeries_sub_constant c hc X hX
  rw [he]
  calc
    _ ≤ ∑' n, ‖c (n+1) •X^(n+1)‖ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' n, ‖X‖*‖X‖^n := hs.tsum_le_tsum (fun n => by
      rw [norm_smul]
      calc
        _ ≤ 1*‖X^(n+1)‖ := mul_le_mul_of_nonneg_right (hc _) (norm_nonneg _)
        _ ≤ ‖X‖^(n+1) := by simpa only [one_mul] using norm_pow_le X (n+1)
        _ = ‖X‖*‖X‖^n := by rw [pow_succ,mul_comm])
      ((summable_geometric_of_lt_one (norm_nonneg X) hX).mul_left ‖X‖)
    _ = _ := by rw [tsum_mul_left,tsum_geometric_of_lt_one (norm_nonneg X) hX,div_eq_mul_inv]

/-- Every complete shifted tail obeys its geometric majorant. -/
theorem boundedOperatorSeries_tail_bound (c : ℕ → ℂ) (hc : ∀ n, ‖c n‖ ≤ 1)
    (X : A) (hX : ‖X‖ < 1) (N : ℕ) :
    ‖∑' n, c (n+N) •X^(n+N)‖ ≤ ‖X‖^N/(1-‖X‖) := by
  have hs := (boundedOperatorSeries_summable_norm c hc X hX).comp_injective (add_left_injective N)
  calc
    _ ≤ ∑' n, ‖c (n+N) •X^(n+N)‖ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' n, ‖X‖^N*‖X‖^n := hs.tsum_le_tsum (fun n => by
      rw [norm_smul]
      calc
        _ ≤ 1*‖X^(n+N)‖ := mul_le_mul_of_nonneg_right (hc _) (norm_nonneg _)
        _ ≤ ‖X‖^(n+N) := by simpa only [one_mul] using norm_pow_le X (n+N)
        _ = ‖X‖^N*‖X‖^n := by rw [pow_add,mul_comm])
      ((summable_geometric_of_lt_one (norm_nonneg X) hX).mul_left (‖X‖^N))
    _ = _ := by rw [tsum_mul_left,tsum_geometric_of_lt_one (norm_nonneg X) hX,div_eq_mul_inv]

/-- The complete nonlinear remainder after the linear term is quadratic. -/
theorem boundedOperatorSeries_sub_linear_bound (c : ℕ → ℂ) (hc : ∀ n, ‖c n‖ ≤ 1)
    (hc0 : c 0=1) (hc1 : c 1=1) (X : A) (hX : ‖X‖ < 1) :
    ‖boundedOperatorSeries c X-1-X‖ ≤ ‖X‖^2/(1-‖X‖) := by
  have htail := ((boundedOperatorSeries_summable_norm c hc X hX).of_norm.comp_injective Nat.succ_injective).tsum_eq_zero_add
  simp only [Function.comp_def,Nat.succ_eq_add_one] at htail
  have hfirst := boundedOperatorSeries_sub_constant c hc X hX
  simp only [hc0,one_smul] at hfirst
  have he : boundedOperatorSeries c X-1-X=∑' n, c (n+2) •X^(n+2) := by
    rw [hfirst,htail]
    simp only [zero_add,hc1,pow_one,one_smul,add_sub_cancel_left]
  rw [he]
  exact boundedOperatorSeries_tail_bound c hc X hX 2

end
end MeyerGeneralProblem.Adaptive
