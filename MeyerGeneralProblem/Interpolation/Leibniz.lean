module

public import MeyerGeneralProblem.Interpolation.NewtonPolynomial
public import Mathlib.Algebra.Polynomial.Div
import all Mathlib.Algebra.Polynomial.Div

@[expose] public section

/-!
# Leibniz law for divided differences

We use synthetic division by `X - a` to define polynomial divided differences along an ordered
node sequence.  This definition remains meaningful when nodes coalesce; analytic identification
with confluent derivative data is deliberately deferred.
-/

namespace MeyerGeneralProblem

noncomputable section

open Finset Polynomial

variable {K : Type*} [Field K]

/-- Remove the value at `a` from a polynomial and divide by `X - a`. -/
def newtonQuotient (a : K) (p : K[X]) : K[X] :=
  (p - Polynomial.C (p.eval a)) /ₘ (Polynomial.X - Polynomial.C a)

/-- Exact synthetic-division reconstruction. -/
theorem X_sub_C_mul_newtonQuotient (a : K) (p : K[X]) :
    (Polynomial.X - Polynomial.C a) * newtonQuotient a p =
      p - Polynomial.C (p.eval a) := by
  rw [newtonQuotient, Polynomial.mul_divByMonic_eq_iff_isRoot]
  simp [Polynomial.IsRoot]

/-- The Newton quotient of zero vanishes. -/
@[simp]
theorem newtonQuotient_zero (a : K) : newtonQuotient a (0 : K[X]) = 0 := by
  apply mul_left_cancel₀ (Polynomial.monic_X_sub_C a).ne_zero
  rw [X_sub_C_mul_newtonQuotient, mul_zero]
  simp

/-- Newton quotient is additive in the polynomial. -/
theorem newtonQuotient_add (a : K) (p q : K[X]) :
    newtonQuotient a (p + q) = newtonQuotient a p + newtonQuotient a q := by
  apply mul_left_cancel₀ (Polynomial.monic_X_sub_C a).ne_zero
  rw [X_sub_C_mul_newtonQuotient, mul_add, X_sub_C_mul_newtonQuotient,
    X_sub_C_mul_newtonQuotient]
  simp
  ring

/-- Constants pull through the Newton quotient. -/
theorem newtonQuotient_C_mul (a c : K) (p : K[X]) :
    newtonQuotient a (Polynomial.C c * p) = Polynomial.C c * newtonQuotient a p := by
  apply mul_left_cancel₀ (Polynomial.monic_X_sub_C a).ne_zero
  rw [X_sub_C_mul_newtonQuotient, ← mul_assoc, mul_comm (Polynomial.X - Polynomial.C a),
    mul_assoc, X_sub_C_mul_newtonQuotient]
  simp
  ring

/-- The first-order product rule for synthetic Newton quotients. -/
theorem newtonQuotient_mul (a : K) (p q : K[X]) :
    newtonQuotient a (p * q) =
      newtonQuotient a p * q + Polynomial.C (p.eval a) * newtonQuotient a q := by
  apply mul_left_cancel₀ (Polynomial.monic_X_sub_C a).ne_zero
  calc
    (Polynomial.X - Polynomial.C a) * newtonQuotient a (p * q) =
        p * q - Polynomial.C ((p * q).eval a) :=
      X_sub_C_mul_newtonQuotient a (p * q)
    _ = (p - Polynomial.C (p.eval a)) * q +
        Polynomial.C (p.eval a) * (q - Polynomial.C (q.eval a)) := by
      simp [Polynomial.eval_mul]
      ring
    _ = (Polynomial.X - Polynomial.C a) *
        (newtonQuotient a p * q + Polynomial.C (p.eval a) * newtonQuotient a q) := by
      rw [← X_sub_C_mul_newtonQuotient a p, ← X_sub_C_mul_newtonQuotient a q]
      ring

/-- Polynomial divided difference of order `order` along the initial segment of `nodes`.

At order zero this is evaluation at `nodes 0`; each successor strips the first Newton factor and
continues along the tail. -/
def polynomialDividedDifference (nodes : ℕ → K) : ℕ → K[X] → K
  | 0, p => p.eval (nodes 0)
  | order + 1, p => polynomialDividedDifference (fun i ↦ nodes (i + 1)) order
      (newtonQuotient (nodes 0) p)

/-- Zeroth-order polynomial divided difference is evaluation at the first node. -/
@[simp]
theorem polynomialDividedDifference_zero_order (nodes : ℕ → K) (p : K[X]) :
    polynomialDividedDifference nodes 0 p = p.eval (nodes 0) :=
  rfl

/-- Every divided difference of the zero polynomial is zero. -/
@[simp]
theorem polynomialDividedDifference_zero (nodes : ℕ → K) (order : ℕ) :
    polynomialDividedDifference nodes order (0 : K[X]) = 0 := by
  induction order generalizing nodes with
  | zero => simp [polynomialDividedDifference]
  | succ order ih => simp [polynomialDividedDifference, ih]

/-- Polynomial divided differences are additive. -/
theorem polynomialDividedDifference_add (nodes : ℕ → K) (order : ℕ) (p q : K[X]) :
    polynomialDividedDifference nodes order (p + q) =
      polynomialDividedDifference nodes order p + polynomialDividedDifference nodes order q := by
  induction order generalizing nodes p q with
  | zero => simp [polynomialDividedDifference]
  | succ order ih =>
      simp only [polynomialDividedDifference, newtonQuotient_add]
      exact ih _ _ _

/-- Scalar constants pull out of polynomial divided differences. -/
theorem polynomialDividedDifference_C_mul (nodes : ℕ → K) (order : ℕ) (c : K) (p : K[X]) :
    polynomialDividedDifference nodes order (Polynomial.C c * p) =
      c * polynomialDividedDifference nodes order p := by
  induction order generalizing nodes p with
  | zero => simp [polynomialDividedDifference]
  | succ order ih =>
      simp only [polynomialDividedDifference, newtonQuotient_C_mul]
      exact ih _ _

/-- Divided-difference Leibniz law.  The `k`th summand uses the first `k + 1` nodes for `p` and
the remaining `order - k + 1` nodes for `q`. -/
theorem dividedDifference_leibniz (nodes : ℕ → K) (order : ℕ) (p q : K[X]) :
    polynomialDividedDifference nodes order (p * q) =
      ∑ k ∈ Finset.range (order + 1),
        polynomialDividedDifference nodes k p *
          polynomialDividedDifference (fun i ↦ nodes (i + k)) (order - k) q := by
  induction order generalizing nodes p q with
  | zero => simp [polynomialDividedDifference]
  | succ order ih =>
      rw [polynomialDividedDifference, newtonQuotient_mul,
        polynomialDividedDifference_add, polynomialDividedDifference_C_mul,
        ih (fun i ↦ nodes (i + 1)) (newtonQuotient (nodes 0) p) q]
      conv_rhs => rw [Finset.sum_range_succ']
      apply congrArg₂ (· + ·)
      · apply Finset.sum_congr rfl
        intro k hk
        simp only [polynomialDividedDifference]
        congr 2
        omega
      · simp [polynomialDividedDifference]

/-- The order-one case is the usual difference quotient, with its exact denominator. -/
theorem polynomialDividedDifference_one (nodes : ℕ → K) (p : K[X])
    (hnodes : nodes 1 ≠ nodes 0) :
    polynomialDividedDifference nodes 1 p =
      (p.eval (nodes 1) - p.eval (nodes 0)) / (nodes 1 - nodes 0) := by
  change (newtonQuotient (nodes 0) p).eval (nodes 1) = _
  have h := congrArg (Polynomial.eval (nodes 1)) (X_sub_C_mul_newtonQuotient (nodes 0) p)
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at h
  exact (eq_div_iff (sub_ne_zero.mpr hnodes)).mpr (by simpa [mul_comm] using h)

end

end MeyerGeneralProblem
