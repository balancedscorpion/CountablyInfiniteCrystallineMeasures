module

public import MeyerGeneralProblem.Sampling.GroupedExponential
public import Mathlib.Analysis.Calculus.Deriv.Shift
import all Mathlib.Analysis.Calculus.Deriv.Shift

@[expose] public section

/-!
# Gap-independent subgroup data for arbitrary functions

At distinct nodes an arbitrary complex-valued function has the same prefix
divided differences as its actual Newton interpolant. The polynomial subgroup
bound therefore controls every selected subgroup by the full group's data.
Translation invariance removes dependence on the group's absolute position:
the final constant depends only on the maximal group size and its diameter.

Subgroups are explicit embeddings of finite index sets. No function
regularity, minimum node gap, or global weighted interpolation estimate is
assumed.
-/

namespace MeyerGeneralProblem

noncomputable section

open Finset Polynomial

section Translation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Translation commutes with the actual divided slope, including its
derivative value when the two nodes coincide. No differentiability assumption
is needed because the derivative translation identity is unconditional. -/
theorem dslope_comp_add_const (f : ℝ → E) (c a b : ℝ) :
    dslope (fun x => f (x + c)) a b = dslope f (a + c) (b + c) := by
  by_cases hab : b = a
  · subst b
    rw [dslope_same, dslope_same, deriv_comp_add_const]
  · have habc : b + c ≠ a + c := fun h => hab (add_right_cancel h)
    rw [dslope_of_ne _ hab, dslope_of_ne _ habc, slope_def_module, slope_def_module]
    congr 2
    ring

/-- Analytic divided differences commute with translation at every order,
including repeated nodes and arbitrary Banach-valued functions. -/
theorem analyticDividedDifference_comp_add_const
    (nodes : ℕ → ℝ) (order : ℕ) (f : ℝ → E) (c : ℝ) :
    analyticDividedDifference nodes order (fun x => f (x + c)) =
      analyticDividedDifference (fun j => nodes j + c) order f := by
  induction order generalizing nodes f with
  | zero => rfl
  | succ order ih =>
      simp only [analyticDividedDifference_succ]
      have hslope : dslope (fun x => f (x + c)) (nodes 0) =
          fun x => dslope f (nodes 0 + c) (x + c) := by
        funext x
        exact dslope_comp_add_const f c (nodes 0) x
      rw [hslope]
      exact ih (fun j => nodes (j + 1)) (dslope f (nodes 0 + c))

/-- Translation invariance for a genuine finite prefix. The zero extension
outside the finite list has no influence on any declared prefix. -/
theorem analyticDividedDifference_finite_comp_add_const {n : ℕ}
    (nodes : Fin n → ℝ) (j : Fin n) (f : ℝ → E) (c : ℝ) :
    analyticDividedDifference (finiteNodeSequence nodes) j (fun x => f (x + c)) =
      analyticDividedDifference (finiteNodeSequence (fun i => nodes i + c)) j f := by
  rw [analyticDividedDifference_comp_add_const]
  apply analyticDividedDifference_congr_nodes
  intro i hi
  have hin : i < n := hi.trans_lt j.isLt
  simp only [finiteNodeSequence, dite_eq_left hin]

/-- Translating nodes by `-c` and the function by `+c` preserves each
actual finite-prefix divided difference exactly. -/
theorem analyticDividedDifference_finite_recenter {n : ℕ}
    (nodes : Fin n → ℝ) (j : Fin n) (f : ℝ → E) (c : ℝ) :
    analyticDividedDifference (finiteNodeSequence (fun i => nodes i - c)) j
      (fun x => f (x + c)) = analyticDividedDifference (finiteNodeSequence nodes) j f := by
  rw [analyticDividedDifference_finite_comp_add_const]
  simp only [sub_add_cancel]

end Translation

private theorem finiteNodeSequence_distinct_prefix {n : ℕ}
    (nodes : Fin n → ℝ) (hnodes : Function.Injective nodes) (j : Fin n) :
    ∀ i ≤ (j : ℕ), ∀ k ≤ (j : ℕ), i ≠ k →
      finiteNodeSequence nodes i ≠ finiteNodeSequence nodes k := by
  intro i hi k hk hik heq
  have hin : i < n := hi.trans_lt j.isLt
  have hkn : k < n := hk.trans_lt j.isLt
  simp only [finiteNodeSequence, dite_eq_left hin, dite_eq_left hkn] at heq
  exact hik (congrArg Fin.val (hnodes heq))

/-- Every actual subgroup prefix of an arbitrary function on distinct nodes
is controlled by the full group's prefix data. The radius constant contains
no inverse node gap, and the selection need not preserve order. -/
theorem norm_analyticDividedDifference_subgroup_le {n m q : ℕ}
    (hnq : n ≤ q) (nodes : Fin n → ℝ) (hnodes : Function.Injective nodes)
    (selection : Fin m ↪ Fin n) (f : ℝ → ℂ) (j : Fin m) {R : ℝ}
    (hR : 0 ≤ R) (hbound : ∀ i, |nodes i| ≤ R) :
    ‖analyticDividedDifference (finiteNodeSequence (fun i => nodes (selection i))) j f‖ ≤
      boundedClusterNewtonBound q R *
        ∑ i : Fin n, ‖analyticDividedDifference (finiteNodeSequence nodes) i f‖ := by
  let z : Fin n → ℂ := fun i => (nodes i : ℂ)
  let hz : Function.Injective z := Complex.ofReal_injective.comp hnodes
  let data := dividedDifferences z hz (fun i => f (nodes i))
  let p : Polynomial.degreeLT ℂ n := newtonCoefficientsEquivPolynomial z data
  have hvalues (i : Fin n) : p.1.eval (nodes i : ℂ) = f (nodes i) :=
    eval_newtonInterpolantFromValues_at_node z hz (fun i => f (nodes i)) i
  have hfull (i : Fin n) :
      polynomialDividedDifference (fun k => (finiteNodeSequence nodes k : ℂ)) i p =
        analyticDividedDifference (finiteNodeSequence nodes) i f := by
    rw [analyticDividedDifference_eq_dividedDifferences nodes hnodes f i]
    change polynomialDividedDifference (fun k => (finiteNodeSequence nodes k : ℂ)) i
      (newtonInterpolant z data) = data i
    simpa only [finiteNodeSequence_apply, z] using
      polynomialDividedDifference_newtonInterpolant
        (fun k => (finiteNodeSequence nodes k : ℂ)) data i
  have hsub := analyticDividedDifference_congr_values_of_distinct
    (finiteNodeSequence (fun i => nodes (selection i))) j f
    (fun x => p.1.eval (x : ℂ))
    (finiteNodeSequence_distinct_prefix _ (hnodes.comp selection.injective) j) (by
      intro k hk
      have hkm : k < m := hk.trans_lt j.isLt
      rw [finiteNodeSequence, dite_eq_left hkm]
      exact (hvalues _).symm)
  rw [hsub]
  have hp := norm_analyticDividedDifference_le_boundedClusterNewtonData hnq
    (fun k => (finiteNodeSequence nodes k : ℂ)) p
    (finiteNodeSequence (fun i => nodes (selection i))) j hR (by
      intro i hi
      simp only [finiteNodeSequence, dite_eq_left hi, Complex.norm_real, Real.norm_eq_abs]
      exact hbound _) (by
      intro i hi
      have him : i < m := hi.trans_lt j.isLt
      simp only [finiteNodeSequence, dite_eq_left him]
      exact abs_le.mp (hbound _))
  simpa only [hfull] using hp

/-- The subgroup bound after recentering. Its constant depends only on the
maximal number of nodes and a radius about the chosen centre, not the centre
itself; arbitrary functions and arbitrary distinct finite selections work. -/
theorem norm_analyticDividedDifference_subgroup_le_centered {n m q : ℕ}
    (hnq : n ≤ q) (nodes : Fin n → ℝ) (hnodes : Function.Injective nodes)
    (selection : Fin m ↪ Fin n) (f : ℝ → ℂ) (j : Fin m) (c : ℝ) {R : ℝ}
    (hR : 0 ≤ R) (hbound : ∀ i, |nodes i - c| ≤ R) :
    ‖analyticDividedDifference (finiteNodeSequence (fun i => nodes (selection i))) j f‖ ≤
      boundedClusterNewtonBound q R *
        ∑ i : Fin n, ‖analyticDividedDifference (finiteNodeSequence nodes) i f‖ := by
  have hdistinct : Function.Injective (fun i => nodes i - c) := by
    intro i k hik
    apply hnodes
    linarith
  have h := norm_analyticDividedDifference_subgroup_le hnq
    (fun i => nodes i - c) hdistinct selection (fun x => f (x + c)) j hR hbound
  simpa only [analyticDividedDifference_finite_recenter] using h

/-- The source subgroup estimate with a diameter bound. All constants are
independent of absolute position and every minimum intra-group gap. -/
theorem norm_analyticDividedDifference_subgroup_le_of_diameter_bound {n m q : ℕ}
    (hnq : n ≤ q) (nodes : Fin n → ℝ) (hnodes : Function.Injective nodes)
    (selection : Fin m ↪ Fin n) (f : ℝ → ℂ) (j : Fin m) {D : ℝ}
    (hD : 0 ≤ D) (hdiam : ∀ i k, dist (nodes i) (nodes k) ≤ D) :
    ‖analyticDividedDifference (finiteNodeSequence (fun i => nodes (selection i))) j f‖ ≤
      boundedClusterNewtonBound q D *
        ∑ i : Fin n, ‖analyticDividedDifference (finiteNodeSequence nodes) i f‖ := by
  apply norm_analyticDividedDifference_subgroup_le_centered hnq nodes hnodes
    selection f j (nodes (selection j)) hD
  intro i
  simpa only [Real.dist_eq] using hdiam i (selection j)

/-- Fully intrinsic diameter version of the subgroup estimate for arbitrary
functions at distinct nodes. No externally chosen centre or radius remains. -/
theorem norm_analyticDividedDifference_subgroup_le_diameter {n m q : ℕ}
    (hnq : n ≤ q) (nodes : Fin n → ℝ) (hnodes : Function.Injective nodes)
    (selection : Fin m ↪ Fin n) (f : ℝ → ℂ) (j : Fin m) :
    ‖analyticDividedDifference (finiteNodeSequence (fun i => nodes (selection i))) j f‖ ≤
      boundedClusterNewtonBound q (Metric.diam (Set.range nodes)) *
        ∑ i : Fin n, ‖analyticDividedDifference (finiteNodeSequence nodes) i f‖ := by
  apply norm_analyticDividedDifference_subgroup_le_of_diameter_bound hnq nodes hnodes
    selection f j Metric.diam_nonneg
  intro i k
  exact Metric.dist_le_diam_of_mem (Set.finite_range nodes).isBounded ⟨i, rfl⟩ ⟨k, rfl⟩

end

end MeyerGeneralProblem
