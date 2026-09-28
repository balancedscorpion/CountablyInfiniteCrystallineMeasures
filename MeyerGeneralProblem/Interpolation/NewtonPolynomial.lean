module

public import MeyerGeneralProblem.Interpolation.DividedDifference
public import Mathlib.Data.Complex.Basic
import all Mathlib.Data.Complex.Basic

@[expose] public section

/-!
# Newton interpolation at distinct finite nodes

The Newton-coordinate change from `DividedDifference` becomes a values-to-coefficients
equivalence when the nodes are distinct.  The final interface specializes strictly increasing real
cluster nodes to complex-valued traces.
-/

namespace MeyerGeneralProblem

noncomputable section

open Finset Polynomial

variable {K : Type*} [Field K]

@[instance_reducible]
def invertibleVandermonde {n : ℕ} (nodes : Fin n → K)
    (hnodes : Function.Injective nodes) : Invertible (Matrix.vandermonde nodes) :=
  Matrix.invertibleOfIsUnitDet _ <|
    isUnit_iff_ne_zero.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr hnodes)

/-- Evaluation at distinct nodes is a linear equivalence on polynomials of degree below the node
count. -/
def polynomialValuesEquiv {n : ℕ} (nodes : Fin n → K) (hnodes : Function.Injective nodes) :
    Polynomial.degreeLT K n ≃ₗ[K] (Fin n → K) :=
  (Polynomial.degreeLTEquiv K n).trans
    (Matrix.toLinearEquiv' (Matrix.vandermonde nodes)
      (invertibleVandermonde nodes hnodes))

/-- The polynomial-to-values equivalence is pointwise evaluation at the supplied nodes. -/
@[simp]
theorem polynomialValuesEquiv_apply {n : ℕ} (nodes : Fin n → K)
    (hnodes : Function.Injective nodes) (p : Polynomial.degreeLT K n) (i : Fin n) :
    polynomialValuesEquiv nodes hnodes p i = p.1.eval (nodes i) :=
  by
    have he := LinearMap.congr_fun (Matrix.toLinearEquiv'_apply
      (Matrix.vandermonde nodes) (invertibleVandermonde nodes hnodes))
        (Polynomial.degreeLTEquiv K n p)
    change polynomialValuesEquiv nodes hnodes p i = p.1.eval (nodes i)
    rw [Polynomial.eval_eq_sum_degreeLTEquiv p.property]
    rw [show polynomialValuesEquiv nodes hnodes p =
      Matrix.mulVec (Matrix.vandermonde nodes) (Polynomial.degreeLTEquiv K n p) by
        exact he]
    simp [Matrix.mulVec, dotProduct, mul_comm]

/-- Newton coefficients and values at distinct ordered nodes are linearly equivalent. -/
def newtonCoefficientsEquivValues {n : ℕ} (nodes : Fin n → K)
    (hnodes : Function.Injective nodes) : (Fin n → K) ≃ₗ[K] (Fin n → K) :=
  (newtonCoefficientsEquivPolynomial nodes).trans (polynomialValuesEquiv nodes hnodes)

/-- Values at distinct nodes, converted to their ordered divided-difference vector. -/
def valuesEquivDividedDifferencesOfInjective {n : ℕ} (nodes : Fin n → K)
    (hnodes : Function.Injective nodes) : (Fin n → K) ≃ₗ[K] (Fin n → K) :=
  (newtonCoefficientsEquivValues nodes hnodes).symm

/-- The divided differences of a finite value vector, in increasing prefix order. -/
def dividedDifferences {n : ℕ} (nodes : Fin n → K) (hnodes : Function.Injective nodes)
    (values : Fin n → K) : Fin n → K :=
  valuesEquivDividedDifferencesOfInjective nodes hnodes values

/-- The highest-order divided difference on a nonempty finite node vector. -/
def dividedDifference {n : ℕ} (nodes : Fin (n + 1) → K)
    (hnodes : Function.Injective nodes) (values : Fin (n + 1) → K) : K :=
  dividedDifferences nodes hnodes values (Fin.last n)

/-- Strictly increasing real cluster nodes give a canonical equivalence between complex values
and complex divided differences. -/
def values_equiv_dividedDifferences_of_strictMono {n : ℕ} (nodes : Fin n → ℝ)
    (hnodes : StrictMono nodes) : (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ) :=
  valuesEquivDividedDifferencesOfInjective (fun i ↦ (nodes i : ℂ))
    (Complex.ofReal_injective.comp hnodes.injective)

/-- Complex divided differences on strictly increasing real cluster nodes. -/
def complexDividedDifferencesOfStrictMono {n : ℕ} (nodes : Fin n → ℝ)
    (hnodes : StrictMono nodes) (values : Fin n → ℂ) : Fin n → ℂ :=
  values_equiv_dividedDifferences_of_strictMono nodes hnodes values

/-- Newton interpolation reconstructed from a value vector. -/
def newtonInterpolantFromValues {n : ℕ} (nodes : Fin n → K)
    (hnodes : Function.Injective nodes) (values : Fin n → K) : K[X] :=
  newtonInterpolant nodes (dividedDifferences nodes hnodes values)

/-- Newton reconstruction is exact at every supplied node. -/
@[simp]
theorem eval_newtonInterpolantFromValues_at_node {n : ℕ} (nodes : Fin n → K)
    (hnodes : Function.Injective nodes) (values : Fin n → K) (i : Fin n) :
    (newtonInterpolantFromValues nodes hnodes values).eval (nodes i) = values i := by
  have h := LinearEquiv.apply_symm_apply
    (newtonCoefficientsEquivValues nodes hnodes) values
  change polynomialValuesEquiv nodes hnodes
    (newtonCoefficientsEquivPolynomial nodes (dividedDifferences nodes hnodes values)) =
      values at h
  have hi := congrFun h i
  rw [polynomialValuesEquiv_apply] at hi
  simpa [newtonInterpolantFromValues, newtonInterpolant] using hi

/-- The reconstructed interpolant is the Newton sum with the divided-difference vector. -/
theorem newtonInterpolantFromValues_eq_sum {n : ℕ} (nodes : Fin n → K)
    (hnodes : Function.Injective nodes) (values : Fin n → K) :
    newtonInterpolantFromValues nodes hnodes values =
      ∑ k : Fin n, Polynomial.C (dividedDifferences nodes hnodes values k) *
        newtonBasisPolynomial nodes k :=
  newtonInterpolant_eq_sum nodes (dividedDifferences nodes hnodes values)

/-- The empty values/divided-differences equivalence is the unique endomorphism of the empty
coordinate space. -/
@[simp]
theorem valuesEquivDividedDifferencesOfInjective_empty
    (nodes : Fin 0 → K) (hnodes : Function.Injective nodes) (values : Fin 0 → K) :
    valuesEquivDividedDifferencesOfInjective nodes hnodes values = values := by
  funext i
  exact Fin.elim0 i

/-- At a singleton node the sole divided difference is exactly the supplied value. -/
@[simp]
theorem dividedDifferences_singleton (nodes : Fin 1 → K) (hnodes : Function.Injective nodes)
    (values : Fin 1 → K) : dividedDifferences nodes hnodes values 0 = values 0 := by
  have h := eval_newtonInterpolantFromValues_at_node nodes hnodes values 0
  simpa [newtonInterpolantFromValues, newtonInterpolant_singleton] using h

/-- The first divided difference has the exact difference-quotient normalization. -/
theorem dividedDifference_two (nodes : Fin 2 → K) (hnodes : Function.Injective nodes)
    (values : Fin 2 → K) :
    dividedDifference nodes hnodes values =
      (values 1 - values 0) / (nodes 1 - nodes 0) := by
  have h0 := eval_newtonInterpolantFromValues_at_node nodes hnodes values 0
  have h1 := eval_newtonInterpolantFromValues_at_node nodes hnodes values 1
  rw [newtonInterpolantFromValues_eq_sum] at h0 h1
  simp only [eval_finsetSum, eval_mul, eval_C, eval_newtonBasisPolynomial] at h0 h1
  have hiio0 : Finset.Iio (0 : Fin 2) = ∅ := by decide
  have hiio1 : Finset.Iio (1 : Fin 2) = {0} := by decide
  simp [hiio0, hiio1] at h0 h1
  change dividedDifferences nodes hnodes values 1 = _
  rw [h0] at h1
  have hnode : nodes 1 ≠ nodes 0 := fun he ↦ (show (1 : Fin 2) ≠ 0 by decide) (hnodes he)
  have hne : nodes 1 - nodes 0 ≠ 0 := sub_ne_zero.mpr hnode
  apply (eq_div_iff hne).mpr
  exact eq_sub_iff_add_eq.mpr (by simpa [add_comm] using h1)

end

end MeyerGeneralProblem
