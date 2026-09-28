module

public import MeyerGeneralProblem.Cardinal.Adaptive.NativeTestTranspose
public import Mathlib.Algebra.Group.ForwardDiff
import all Mathlib.Algebra.Group.ForwardDiff

@[expose] public section

/-! # Actual distributional differences and polynomial periodic sources -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section

/-- The actual one-step difference of whole tempered distributions. -/
def distributionDifference (P : ℝ) :
    TemperedDistribution ℝ ℂ →L[ℂ] TemperedDistribution ℝ ℂ :=
  combDistributionTranslation P - ContinuousLinearMap.id ℂ _

/-- Difference acts by the genuine translated Schwartz test. -/
theorem distributionDifference_apply (P : ℝ) (T : TemperedDistribution ℝ ℂ)
    (f : SchwartzMap ℝ ℂ) :
    distributionDifference P T f = T (combSchwartzTranslation P f) - T f := rfl

/-- Translation addition with the project's pushforward convention. -/
theorem difference_translation_add (a b : ℝ) (f : SchwartzMap ℝ ℂ) :
    combSchwartzTranslation a (combSchwartzTranslation b f) =
      combSchwartzTranslation (a+b) f := by
  ext x
  simp only [combSchwartzTranslation_apply]
  congr 1
  ring

private theorem difference_iter_orbit (P : ℝ) (n j : ℕ)
    (T : TemperedDistribution ℝ ℂ) (f : SchwartzMap ℝ ℂ) :
    ((distributionDifference P : TemperedDistribution ℝ ℂ → TemperedDistribution ℝ ℂ)^[n] T)
      (combSchwartzTranslation ((j:ℝ)*P) f) =
    (fwdDiff (1:ℕ))^[n] (fun k : ℕ => T (combSchwartzTranslation ((k:ℝ)*P) f)) j := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', distributionDifference_apply, difference_translation_add]
      have he : P+(j:ℝ)*P = ((j+1:ℕ):ℝ)*P := by push_cast; ring
      rw [he, ih, ih, Function.iterate_succ_apply']
      rfl

/-- Exact binomial expansion of every iterated distributional difference. -/
theorem distributionDifference_iter_apply (P : ℝ) (n : ℕ)
    (T : TemperedDistribution ℝ ℂ) (f : SchwartzMap ℝ ℂ) :
    ((distributionDifference P : TemperedDistribution ℝ ℂ → TemperedDistribution ℝ ℂ)^[n] T) f =
    ∑ k ∈ Finset.range (n+1), ((-1:ℂ)^(n-k)*(n.choose k:ℂ)) *
      T (combSchwartzTranslation ((k:ℝ)*P) f) := by
  have h := difference_iter_orbit P n 0 T f
  have he : combSchwartzTranslation (((0:ℕ):ℝ)*P) f = f := by
    ext x; simp only [Nat.cast_zero, zero_mul, combSchwartzTranslation_apply, zero_add]
  rw [he, fwdDiff_iter_eq_sum_shift] at h
  simpa only [nsmul_eq_mul, mul_one, zero_add, zsmul_eq_mul, Int.cast_mul,
    Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast, Nat.cast_id] using h

/-- Multiplication of a whole distribution by an actual coordinate monomial. -/
def monomialDistribution (d : ℕ) :
    TemperedDistribution ℝ ℂ →L[ℂ] TemperedDistribution ℝ ℂ :=
  PointwiseConvergenceCLM.precomp ℂ (monomialTestCLM d)

/-- Monomial multiplication retains every Schwartz test. -/
theorem monomialDistribution_apply (d : ℕ) (T : TemperedDistribution ℝ ℂ)
    (f : SchwartzMap ℝ ℂ) :
    monomialDistribution d T f = T (monomialTestCLM d f) := rfl

/-- A whole one-step periodic source is invariant under every nonnegative
integer translate, without a support or coefficient assumption. -/
theorem distribution_periodic_nat (P : ℝ) (T : TemperedDistribution ℝ ℂ)
    (hT : combDistributionTranslation P T = T) (k : ℕ) (f : SchwartzMap ℝ ℂ) :
    T (combSchwartzTranslation ((k:ℝ)*P) f) = T f := by
  induction k with
  | zero => congr 1; ext x; simp [combSchwartzTranslation_apply]
  | succ k ih =>
      have he : ((k+1:ℕ):ℝ)*P = P+(k:ℝ)*P := by push_cast; ring
      rw [he, ← difference_translation_add]
      have h := congrArg (fun U : TemperedDistribution ℝ ℂ => U
        (combSchwartzTranslation ((k:ℝ)*P) f)) hT
      exact h.trans ih

/-- A finite difference sum of monomials is the scaled unit-step difference.
The step may be negative, as required by the distribution convention. -/
theorem monomial_difference_sum (a : ℂ) (ha : a ≠ 0) (x : ℂ) (d n : ℕ) :
    (∑ k ∈ Finset.range (n+1), ((-1:ℂ)^(n-k)*(n.choose k:ℂ)) * (x+(k:ℂ)*a)^d) =
      a^d * (fwdDiff (1:ℂ))^[n] (fun z : ℂ => z^d) (x/a) := by
  rw [fwdDiff_iter_eq_sum_shift, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [nsmul_eq_mul, mul_one, zsmul_eq_mul, Int.cast_mul, Int.cast_pow,
    Int.cast_neg, Int.cast_one, Int.cast_natCast]
  have he : x+(k:ℂ)*a = a*(x/a+k) := by field_simp
  rw [he, mul_pow]
  ring

/-- The top-degree finite difference has its exact factorial and signed period. -/
theorem monomial_difference_top (P x : ℝ) (hP : P ≠ 0) (d : ℕ) :
    (∑ k ∈ Finset.range (d+1), ((-1:ℂ)^(d-k)*(d.choose k:ℂ)) *
      ((x:ℂ)-(k:ℂ)*(P:ℂ))^d) = (d.factorial:ℂ)*(-(P:ℂ))^d := by
  have ha : -(P:ℂ) ≠ 0 := neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr hP)
  have h := monomial_difference_sum (-(P:ℂ)) ha x d d
  simp only [mul_neg, ← sub_eq_add_neg] at h
  rw [fwdDiff_iter_eq_factorial] at h
  simpa only [Pi.natCast_apply, mul_comm] using h

/-- Every higher finite difference of a degree-d monomial vanishes. -/
theorem monomial_difference_zero (P x : ℝ) (hP : P ≠ 0) (d n : ℕ) (hd : d < n) :
    (∑ k ∈ Finset.range (n+1), ((-1:ℂ)^(n-k)*(n.choose k:ℂ)) *
      ((x:ℂ)-(k:ℂ)*(P:ℂ))^d) = 0 := by
  have ha : -(P:ℂ) ≠ 0 := neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr hP)
  have h := monomial_difference_sum (-(P:ℂ)) ha x d n
  simp only [mul_neg, ← sub_eq_add_neg] at h
  rw [fwdDiff_iter_pow_eq_zero_of_lt hd] at h
  simpa using h

/-- Translated monomial test with its shift cancelled on the underlying test. -/
def shiftedMonomialTest (d : ℕ) (a : ℝ) (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  combSchwartzTranslation (-a) (monomialTestCLM d (combSchwartzTranslation a f))

/-- The shifted test is the exact ordinary shifted monomial times f. -/
theorem shiftedMonomialTest_apply (d : ℕ) (a : ℝ) (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    shiftedMonomialTest d a f x = ((x:ℂ)-(a:ℂ))^d * f x := by
  simp only [shiftedMonomialTest, combSchwartzTranslation_apply, monomialTestCLM_apply,
    add_neg_cancel_left, Complex.ofReal_add, Complex.ofReal_neg]
  congr 2
  ring

/-- Whole periodicity moves the translation from the test onto its polynomial. -/
theorem monomial_periodic_translation (P : ℝ) (T : TemperedDistribution ℝ ℂ)
    (hT : combDistributionTranslation P T = T) (d k : ℕ) (f : SchwartzMap ℝ ℂ) :
    T (monomialTestCLM d (combSchwartzTranslation ((k:ℝ)*P) f)) =
      T (shiftedMonomialTest d ((k:ℝ)*P) f) := by
  have h := distribution_periodic_nat P T hT k (shiftedMonomialTest d ((k:ℝ)*P) f)
  have he : combSchwartzTranslation ((k:ℝ)*P) (shiftedMonomialTest d ((k:ℝ)*P) f) =
      monomialTestCLM d (combSchwartzTranslation ((k:ℝ)*P) f) := by
    ext x
    simp only [shiftedMonomialTest, combSchwartzTranslation_apply, neg_add_cancel_left]
  rw [he] at h
  exact h

/-- Iterated differences of a periodic monomial source reduce to an actual
finite sum of Schwartz tests. -/
theorem difference_monomial_iter_apply (P : ℝ) (T : TemperedDistribution ℝ ℂ)
    (hT : combDistributionTranslation P T = T) (d n : ℕ) (f : SchwartzMap ℝ ℂ) :
    ((distributionDifference P : TemperedDistribution ℝ ℂ → TemperedDistribution ℝ ℂ)^[n]
      (monomialDistribution d T)) f =
    T (∑ k ∈ Finset.range (n+1), ((-1:ℂ)^(n-k)*(n.choose k:ℂ)) •
      shiftedMonomialTest d ((k:ℝ)*P) f) := by
  rw [distributionDifference_iter_apply]
  simp_rw [monomialDistribution_apply, monomial_periodic_translation P T hT]
  simp only [map_sum, map_smul, smul_eq_mul]

/-- The exact factorial identity for whole polynomial periodic sources,
including the sign imposed by pushforward translation. -/
theorem distributionDifference_monomial_top (P : ℝ) (hP : P ≠ 0)
    (T : TemperedDistribution ℝ ℂ) (hT : combDistributionTranslation P T = T) (d : ℕ) :
    (distributionDifference P : TemperedDistribution ℝ ℂ → TemperedDistribution ℝ ℂ)^[d]
      (monomialDistribution d T) = ((d.factorial:ℂ)*(-(P:ℂ))^d) • T := by
  ext f
  rw [difference_monomial_iter_apply P T hT]
  have he : (∑ k ∈ Finset.range (d+1), ((-1:ℂ)^(d-k)*(d.choose k:ℂ)) •
      shiftedMonomialTest d ((k:ℝ)*P) f) = ((d.factorial:ℂ)*(-(P:ℂ))^d) • f := by
    ext x
    simp only [sum_apply, smul_apply, smul_eq_mul, shiftedMonomialTest_apply,
      Complex.ofReal_mul, Complex.ofReal_natCast, ← mul_assoc, ← Finset.sum_mul]
    rw [monomial_difference_top P x hP d]
  rw [he, map_smul]
  rfl

/-- All strictly higher differences of a whole degree-d periodic monomial vanish. -/
theorem distributionDifference_monomial_zero (P : ℝ) (hP : P ≠ 0)
    (T : TemperedDistribution ℝ ℂ) (hT : combDistributionTranslation P T = T)
    (d n : ℕ) (hd : d < n) :
    (distributionDifference P : TemperedDistribution ℝ ℂ → TemperedDistribution ℝ ℂ)^[n]
      (monomialDistribution d T) = 0 := by
  ext f
  rw [difference_monomial_iter_apply P T hT]
  have he : (∑ k ∈ Finset.range (n+1), ((-1:ℂ)^(n-k)*(n.choose k:ℂ)) •
      shiftedMonomialTest d ((k:ℝ)*P) f) = 0 := by
    ext x
    simp only [sum_apply, smul_apply, smul_eq_mul, shiftedMonomialTest_apply,
      Complex.ofReal_mul, Complex.ofReal_natCast, ← mul_assoc, ← Finset.sum_mul, zero_apply]
    rw [monomial_difference_zero P x hP d n hd, zero_mul]
  rw [he, map_zero]
  rfl

end
end MeyerGeneralProblem.Adaptive
