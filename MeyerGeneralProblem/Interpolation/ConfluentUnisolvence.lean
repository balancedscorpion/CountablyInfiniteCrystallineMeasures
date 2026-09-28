module

public import MeyerGeneralProblem.Interpolation.Leibniz
public import Mathlib.Algebra.Polynomial.Taylor
import all Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import all Mathlib.LinearAlgebra.FiniteDimensional.Basic

@[expose] public section

/-!
# Confluent Newton unisolvence

Synthetic divided differences remain meaningful for repeated nodes.  Their
first `n` values determine every polynomial of degree below `n`, without a
separation or distinctness assumption.  At a fully repeated node they are
exactly Taylor (Hasse-derivative) coefficients.  Analytic continuity under
coalescence is a separate Hermite–Genocchi obligation.
-/

namespace MeyerGeneralProblem

noncomputable section

open Polynomial

variable {K : Type*} [Field K]

/-- Homogeneous confluent Newton data have only the zero polynomial in the
degree-restricted space.  The nodes may repeat in any order. -/
theorem confluentUnisolvence (nodes : ℕ → K) {n : ℕ} (p : K[X])
    (hp : p ∈ Polynomial.degreeLT K n)
    (hdata : ∀ k : ℕ, k < n → polynomialDividedDifference nodes k p = 0) :
    p = 0 := by
  induction n generalizing nodes p with
  | zero =>
      apply Polynomial.ext
      intro k
      exact (Polynomial.degree_lt_iff_coeff_zero p 0).mp
        (Polynomial.mem_degreeLT.mp hp) k (Nat.zero_le k)
  | succ n ih =>
      have hvalue : p.eval (nodes 0) = 0 := hdata 0 (Nat.zero_lt_succ n)
      let q := newtonQuotient (nodes 0) p
      have hfactor : (Polynomial.X - Polynomial.C (nodes 0)) * q = p := by
        simpa only [hvalue, Polynomial.C_0, sub_zero, q] using
          X_sub_C_mul_newtonQuotient (nodes 0) p
      by_cases hq : q = 0
      · simpa only [hq, mul_zero] using hfactor.symm
      · have hpne : p ≠ 0 := by
          rw [← hfactor]
          exact mul_ne_zero (Polynomial.monic_X_sub_C _).ne_zero hq
        have hdegree : q.natDegree < n := by
          have hpdegree := (Polynomial.natDegree_lt_iff_degree_lt hpne).mpr
            (Polynomial.mem_degreeLT.mp hp)
          rw [← hfactor, Polynomial.natDegree_mul
            (Polynomial.monic_X_sub_C _).ne_zero hq,
            Polynomial.natDegree_X_sub_C] at hpdegree
          omega
        have hqdegree : q ∈ Polynomial.degreeLT K n :=
          Polynomial.mem_degreeLT.mpr
            ((Polynomial.natDegree_lt_iff_degree_lt hq).mp hdegree)
        have hqdata : ∀ k : ℕ, k < n →
            polynomialDividedDifference (fun i => nodes (i + 1)) k q = 0 := by
          intro k hk
          exact hdata (k + 1) (Nat.succ_lt_succ hk)
        exact (hq (ih (fun i => nodes (i + 1)) q hqdegree hqdata)).elim

/-- The first `n` confluent Newton functionals as a linear map on the
degree-restricted polynomial space. -/
def confluentNewtonData (nodes : ℕ → K) (n : ℕ) :
    Polynomial.degreeLT K n →ₗ[K] (Fin n → K) where
  toFun p i := polynomialDividedDifference nodes i p
  map_add' p q := by
    funext i
    exact polynomialDividedDifference_add nodes i p q
  map_smul' c p := by
    funext i
    simpa only [Submodule.coe_smul, Polynomial.smul_eq_C_mul, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply] using polynomialDividedDifference_C_mul nodes i c p

/-- Arbitrary repeated-node Newton data are injective on degree-bounded
polynomials. -/
theorem confluentNewtonData_injective (nodes : ℕ → K) (n : ℕ) :
    Function.Injective (confluentNewtonData nodes n) := by
  intro p q hpq
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply confluentUnisolvence nodes (p.1 - q.1)
    ((Polynomial.degreeLT K n).sub_mem p.property q.property)
  intro k hk
  have hzero : confluentNewtonData nodes n (p - q) = 0 := by
    rw [map_sub, hpq, sub_self]
  exact congrFun hzero ⟨k, hk⟩

/-- Every finite confluent Newton data vector has a unique interpolating
polynomial of degree below its length. -/
def confluentNewtonDataEquiv (nodes : ℕ → K) (n : ℕ) :
    Polynomial.degreeLT K n ≃ₗ[K] (Fin n → K) :=
  LinearEquiv.ofInjectiveOfFinrankEq (confluentNewtonData nodes n)
    (confluentNewtonData_injective nodes n)
    (Polynomial.degreeLTEquiv K n).finrank_eq

@[simp]
theorem confluentNewtonDataEquiv_apply (nodes : ℕ → K) (n : ℕ)
    (p : Polynomial.degreeLT K n) (i : Fin n) :
    confluentNewtonDataEquiv nodes n p i =
      polynomialDividedDifference nodes i p :=
  rfl

/-- The polynomial interpolating finite confluent Newton data. -/
def confluentNewtonInterpolant (nodes : ℕ → K) {n : ℕ} (data : Fin n → K) :
    Polynomial.degreeLT K n :=
  (confluentNewtonDataEquiv nodes n).symm data

/-- The confluent interpolant realizes every supplied prefix functional. -/
@[simp]
theorem polynomialDividedDifference_confluentNewtonInterpolant
    (nodes : ℕ → K) {n : ℕ} (data : Fin n → K) (i : Fin n) :
    polynomialDividedDifference nodes i (confluentNewtonInterpolant nodes data) =
      data i := by
  change confluentNewtonDataEquiv nodes n
    ((confluentNewtonDataEquiv nodes n).symm data) i = data i
  rw [LinearEquiv.apply_symm_apply]

/-- Existence and uniqueness of a degree-bounded polynomial with arbitrary
confluent Newton data, including repeated-node configurations. -/
theorem existsUnique_confluentNewtonInterpolant
    (nodes : ℕ → K) {n : ℕ} (data : Fin n → K) :
    ∃! p : Polynomial.degreeLT K n,
      ∀ i : Fin n, polynomialDividedDifference nodes i p = data i := by
  refine ⟨confluentNewtonInterpolant nodes data,
    polynomialDividedDifference_confluentNewtonInterpolant nodes data, ?_⟩
  intro p hp
  apply confluentNewtonData_injective nodes n
  funext i
  exact (hp i).trans
    (polynomialDividedDifference_confluentNewtonInterpolant nodes data i).symm

/-- A fully repeated node gives the exact Taylor-coefficient normalization
of the confluent divided difference. -/
theorem polynomialDividedDifference_repeated_node
    (a : K) (order : ℕ) (p : K[X]) :
    polynomialDividedDifference (fun _ => a) order p =
      (Polynomial.taylor a p).coeff order := by
  induction order generalizing p with
  | zero => simp
  | succ order ih =>
      change polynomialDividedDifference (fun _ => a) order
        (newtonQuotient a p) = _
      rw [ih]
      have h := congrArg (fun r : K[X] => (Polynomial.taylor a r).coeff (order + 1))
        (X_sub_C_mul_newtonQuotient a p)
      simpa only [Polynomial.taylor_mul, map_sub, Polynomial.taylor_X,
        Polynomial.taylor_C, add_sub_cancel_right, Polynomial.coeff_X_mul,
        Polynomial.coeff_sub, Polynomial.coeff_C, Nat.succ_ne_zero,
        ite_false, sub_zero] using h

/-- Equivalently, fully confluent divided differences are Hasse derivatives
evaluated at the repeated node. -/
theorem polynomialDividedDifference_repeated_node_eq_hasseDeriv
    (a : K) (order : ℕ) (p : K[X]) :
    polynomialDividedDifference (fun _ => a) order p =
      (Polynomial.hasseDeriv order p).eval a := by
  rw [polynomialDividedDifference_repeated_node, Polynomial.taylor_coeff]

/-- The first fully confluent difference is the ordinary derivative, with
no residual denominator. -/
@[simp]
theorem polynomialDividedDifference_repeated_node_one (a : K) (p : K[X]) :
    polynomialDividedDifference (fun _ => a) 1 p = p.derivative.eval a := by
  rw [polynomialDividedDifference_repeated_node,
    Polynomial.taylor_coeff_one]

end

end MeyerGeneralProblem
