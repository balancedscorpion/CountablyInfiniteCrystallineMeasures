module

public import Mathlib.LinearAlgebra.Lagrange
import all Mathlib.LinearAlgebra.Lagrange
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import all Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

@[expose] public section

/-!
# Finite divided-difference coordinates

This module constructs Newton coordinates for a finite ordered list of nodes.  The change of basis
from Newton coefficients to polynomials is available without a distinctness hypothesis; node
distinctness enters only when coefficients are reconstructed from values.
-/

namespace MeyerGeneralProblem

noncomputable section

open Finset Polynomial

variable {K : Type*} [Field K]

/-- The `k`th Newton basis polynomial for the ordered nodes `nodes`: the product of the factors
belonging to nodes strictly before `k`. -/
def newtonBasisPolynomial {n : ℕ} (nodes : Fin n → K) (k : Fin n) : K[X] :=
  Lagrange.nodal (Finset.Iio k) nodes

/-- The zeroth Newton basis polynomial is constant one. -/
@[simp]
theorem newtonBasisPolynomial_zero {n : ℕ} (nodes : Fin (n + 1) → K) :
    newtonBasisPolynomial nodes 0 = 1 := by
  change Lagrange.nodal (Finset.Iio (⊥ : Fin (n + 1))) nodes = 1
  rw [Finset.Iio_bot, Lagrange.nodal_empty]

/-- Evaluation of a Newton basis polynomial is its defining product of node differences. -/
@[simp]
theorem eval_newtonBasisPolynomial {n : ℕ} (nodes : Fin n → K) (k : Fin n) (x : K) :
    (newtonBasisPolynomial nodes k).eval x = ∏ j ∈ Finset.Iio k, (x - nodes j) := by
  simp [newtonBasisPolynomial, Lagrange.eval_nodal]

/-- The `k`th Newton basis polynomial has degree exactly `k`. -/
@[simp]
theorem natDegree_newtonBasisPolynomial {n : ℕ} (nodes : Fin n → K) (k : Fin n) :
    (newtonBasisPolynomial nodes k).natDegree = k := by
  simp [newtonBasisPolynomial]

/-- Every Newton basis polynomial is monic. -/
theorem monic_newtonBasisPolynomial {n : ℕ} (nodes : Fin n → K) (k : Fin n) :
    (newtonBasisPolynomial nodes k).Monic :=
  Lagrange.nodal_monic

/-- Matrix taking Newton coefficients to ordinary monomial coefficients. -/
def newtonCoefficientMatrix {n : ℕ} (nodes : Fin n → K) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i k ↦ (newtonBasisPolynomial nodes k).coeff i

/-- The Newton-to-monomial transition matrix is unit triangular. -/
@[simp]
theorem det_newtonCoefficientMatrix {n : ℕ} (nodes : Fin n → K) :
    (newtonCoefficientMatrix nodes).det = 1 := by
  exact Matrix.det_matrixOfPolynomials (fun k ↦ newtonBasisPolynomial nodes k)
    (natDegree_newtonBasisPolynomial nodes) (monic_newtonBasisPolynomial nodes)

/-- Newton coefficients are linearly equivalent to polynomials of degree strictly below the
number of coefficients.  No node-distinctness assumption is needed for this change of basis. -/
def newtonCoefficientsEquivPolynomial {n : ℕ} (nodes : Fin n → K) :
    (Fin n → K) ≃ₗ[K] Polynomial.degreeLT K n := by
  let hdet : IsUnit (newtonCoefficientMatrix nodes).det := by
    rw [det_newtonCoefficientMatrix]
    exact isUnit_one
  exact (Matrix.toLinearEquiv' (newtonCoefficientMatrix nodes)
    (Matrix.invertibleOfIsUnitDet _ hdet)).trans (Polynomial.degreeLTEquiv K n).symm

/-- The Newton polynomial with the supplied coefficient vector. -/
def newtonInterpolant {n : ℕ} (nodes : Fin n → K) (coefficients : Fin n → K) : K[X] :=
  newtonCoefficientsEquivPolynomial nodes coefficients

/-- Ordinary coefficients of a Newton-coordinate polynomial are obtained by multiplying by the
Newton coefficient matrix. -/
@[simp]
theorem degreeLTEquiv_newtonCoefficientsEquivPolynomial {n : ℕ} (nodes : Fin n → K)
    (coefficients : Fin n → K) :
    Polynomial.degreeLTEquiv K n (newtonCoefficientsEquivPolynomial nodes coefficients) =
      Matrix.mulVec (newtonCoefficientMatrix nodes) coefficients :=
  by
    simp only [newtonCoefficientsEquivPolynomial, LinearEquiv.trans_apply]
    rw [LinearEquiv.apply_symm_apply]
    exact LinearMap.congr_fun (Matrix.toLinearEquiv'_apply _ _) coefficients

/-- A Newton interpolant has degree strictly below the number of supplied coefficients. -/
theorem newtonInterpolant_mem_degreeLT {n : ℕ} (nodes : Fin n → K)
    (coefficients : Fin n → K) : newtonInterpolant nodes coefficients ∈ Polynomial.degreeLT K n :=
  (newtonCoefficientsEquivPolynomial nodes coefficients).property

/-- The matrix definition is the usual Newton sum. -/
theorem newtonInterpolant_eq_sum {n : ℕ} (nodes : Fin n → K) (coefficients : Fin n → K) :
    newtonInterpolant nodes coefficients =
      ∑ k : Fin n, Polynomial.C (coefficients k) * newtonBasisPolynomial nodes k := by
  ext i
  by_cases hi : i < n
  · let ii : Fin n := ⟨i, hi⟩
    have hcoord := congrFun
      (degreeLTEquiv_newtonCoefficientsEquivPolynomial nodes coefficients) ii
    change (newtonInterpolant nodes coefficients).coeff i = _ at hcoord
    rw [hcoord, Polynomial.finsetSum_coeff]
    simp only [Matrix.mulVec, dotProduct, newtonCoefficientMatrix, Matrix.of_apply,
      Polynomial.coeff_C_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [show (ii : ℕ) = i by rfl, mul_comm]
  · have hni : n ≤ i := Nat.le_of_not_gt hi
    have hleft : (newtonInterpolant nodes coefficients).coeff i = 0 :=
      Polynomial.coeff_eq_zero_of_degree_lt <|
        (Polynomial.mem_degreeLT.mp (newtonInterpolant_mem_degreeLT nodes coefficients)).trans_le
          (WithBot.coe_le_coe.mpr hni)
    rw [hleft, Polynomial.finsetSum_coeff]
    symm
    apply Finset.sum_eq_zero
    intro k _
    rw [Polynomial.coeff_C_mul]
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
    · simp
    · rw [natDegree_newtonBasisPolynomial]
      exact k.isLt.trans_le hni

@[simp]
theorem newtonInterpolant_empty (nodes : Fin 0 → K) (coefficients : Fin 0 → K) :
    newtonInterpolant nodes coefficients = 0 := by
  rw [newtonInterpolant_eq_sum]
  simp

@[simp]
theorem newtonInterpolant_singleton (nodes : Fin 1 → K) (coefficients : Fin 1 → K) :
    newtonInterpolant nodes coefficients = Polynomial.C (coefficients 0) := by
  rw [newtonInterpolant_eq_sum]
  simp

end

end MeyerGeneralProblem
