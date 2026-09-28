module

public import MeyerGeneralProblem.Interpolation.ConfluentUnisolvence
public import MeyerGeneralProblem.Interpolation.HermiteGenocchiHigher

@[expose] public section

/-!
# Gap-independent Newton bounds

Newton basis coefficients and all their derivatives on a fixed compact
interval have bounds depending only on the degree, derivative order, and
interval radius. Indexed products retain repeated nodes. No inverse node
gap, grouped-matrix inverse, or global weighted interpolation estimate is
assumed in this module.
-/

namespace MeyerGeneralProblem

noncomputable section

open Finset Polynomial

section ConfluentCoordinates

variable {K : Type*} [Field K]

def prefixNewtonPolynomial (nodes : ℕ → K) (k : ℕ) : K[X] :=
  ∏ i ∈ Finset.range k, (X - C (nodes i))

private theorem prefixNewtonPolynomial_succ (nodes : ℕ → K) (k : ℕ) :
    prefixNewtonPolynomial nodes (k + 1) =
      (X - C (nodes 0)) * prefixNewtonPolynomial (fun i => nodes (i + 1)) k := by
  simp only [prefixNewtonPolynomial, Finset.prod_range_succ', mul_comm]

private theorem newtonQuotient_C (a c : K) : newtonQuotient a (C c) = 0 := by
  apply mul_left_cancel₀ (Polynomial.monic_X_sub_C a).ne_zero
  rw [X_sub_C_mul_newtonQuotient, mul_zero]
  simp

private theorem newtonQuotient_X_sub_C_mul (a : K) (p : K[X]) :
    newtonQuotient a ((X - C a) * p) = p := by
  apply mul_left_cancel₀ (Polynomial.monic_X_sub_C a).ne_zero
  rw [X_sub_C_mul_newtonQuotient]
  simp

private theorem polynomialDividedDifference_prefixNewtonPolynomial
    (nodes : ℕ → K) (k order : ℕ) :
    polynomialDividedDifference nodes order (prefixNewtonPolynomial nodes k) =
      if order = k then 1 else 0 := by
  induction k generalizing nodes order with
  | zero =>
      cases order with
      | zero => simp [prefixNewtonPolynomial]
      | succ order =>
          change polynomialDividedDifference (fun i => nodes (i + 1)) order
            (newtonQuotient (nodes 0) (C 1)) = _
          rw [newtonQuotient_C]
          simp
  | succ k ih =>
      rw [prefixNewtonPolynomial_succ]
      cases order with
      | zero => simp
      | succ order =>
          simp only [polynomialDividedDifference, newtonQuotient_X_sub_C_mul, ih,
            Nat.succ.injEq]

private theorem newtonBasisPolynomial_eq_prefix {n : ℕ} (nodes : ℕ → K) (k : Fin n) :
    newtonBasisPolynomial (fun i : Fin n => nodes i) k = prefixNewtonPolynomial nodes k := by
  classical
  unfold newtonBasisPolynomial Lagrange.nodal prefixNewtonPolynomial
  apply Finset.prod_bij (fun (i : Fin n) (_ : i ∈ Finset.Iio k) => (i : ℕ))
  · intro i hi
    exact Finset.mem_range.mpr (Fin.lt_def.mp (Finset.mem_Iio.mp hi))
  · intro i _ j _ hij
    exact Fin.ext hij
  · intro i hi
    refine ⟨⟨i, (Finset.mem_range.mp hi).trans k.isLt⟩, ?_, rfl⟩
    exact Finset.mem_Iio.mpr (Fin.lt_def.mpr (Finset.mem_range.mp hi))
  · intro i _
    rfl

/-- Initial synthetic divided differences are exactly the coordinates dual
to the actual Newton basis, with no distinctness or order assumption. -/
theorem polynomialDividedDifference_newtonBasisPolynomial {n : ℕ}
    (nodes : ℕ → K) (k : Fin n) (order : ℕ) :
    polynomialDividedDifference nodes order
      (newtonBasisPolynomial (fun i : Fin n => nodes i) k) =
        if order = (k : ℕ) then 1 else 0 := by
  rw [newtonBasisPolynomial_eq_prefix, polynomialDividedDifference_prefixNewtonPolynomial]

private theorem polynomialDividedDifference_sum {ι : Type*} (nodes : ℕ → K)
    (order : ℕ) (s : Finset ι) (p : ι → K[X]) :
    polynomialDividedDifference nodes order (∑ i ∈ s, p i) =
      ∑ i ∈ s, polynomialDividedDifference nodes order (p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [Finset.sum_insert hi, polynomialDividedDifference_add, ih]

/-- The existing explicit Newton interpolant realizes the same confluent
prefix data as the abstract unisolvence construction. -/
theorem polynomialDividedDifference_newtonInterpolant {n : ℕ}
    (nodes : ℕ → K) (data : Fin n → K) (i : Fin n) :
    polynomialDividedDifference nodes i
      (newtonInterpolant (fun j : Fin n => nodes j) data) = data i := by
  classical
  rw [newtonInterpolant_eq_sum, polynomialDividedDifference_sum]
  simp only [polynomialDividedDifference_C_mul,
    polynomialDividedDifference_newtonBasisPolynomial]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    have hne : (i : ℕ) ≠ (j : ℕ) := fun h => hji (Fin.ext h).symm
    simp [hne]
  · simp

/-- The abstract confluent interpolant is the actual Newton polynomial sum,
including arbitrary repeated-node configurations. -/
theorem confluentNewtonInterpolant_eq_newtonInterpolant {n : ℕ}
    (nodes : ℕ → K) (data : Fin n → K) :
    (confluentNewtonInterpolant nodes data : K[X]) =
      newtonInterpolant (fun i : Fin n => nodes i) data := by
  have heq : confluentNewtonInterpolant nodes data =
      newtonCoefficientsEquivPolynomial (fun i : Fin n => nodes i) data := by
    apply confluentNewtonData_injective nodes n
    funext i
    exact (polynomialDividedDifference_confluentNewtonInterpolant nodes data i).trans
      (polynomialDividedDifference_newtonInterpolant nodes data i).symm
  exact congrArg Subtype.val heq

/-- A degree-bounded polynomial is reconstructed from its own confluent
prefix divided differences. -/
theorem confluentNewtonInterpolant_own_data (nodes : ℕ → K) {n : ℕ}
    (p : Polynomial.degreeLT K n) :
    (confluentNewtonInterpolant nodes
      (fun i : Fin n => polynomialDividedDifference nodes i p) : K[X]) = p := by
  exact congrArg Subtype.val ((confluentNewtonDataEquiv nodes n).symm_apply_apply p)

/-- Fully collapsed interpolation prescribes actual Taylor coefficients,
rather than repeatedly prescribing the same point evaluation. -/
theorem taylor_coeff_confluentNewtonInterpolant_repeated {n : ℕ}
    (a : K) (data : Fin n → K) (i : Fin n) :
    (Polynomial.taylor a (confluentNewtonInterpolant (fun _ => a) data : K[X])).coeff i =
      data i := by
  rw [← polynomialDividedDifference_repeated_node]
  exact polynomialDividedDifference_confluentNewtonInterpolant (fun _ => a) data i

end ConfluentCoordinates

set_option maxHeartbeats 800000 in
/-- Every coefficient of a product of linear factors has a gap-independent
bound. The indexing, rather than a set of node values, preserves collisions. -/
theorem norm_coeff_prod_X_sub_C_le {ι : Type*} (s : Finset ι) (nodes : ι → ℂ)
    {R : ℝ} (hR : 0 ≤ R) (hnodes : ∀ i ∈ s, ‖nodes i‖ ≤ R) (j : ℕ) :
    ‖(∏ i ∈ s, (X - C (nodes i))).coeff j‖ ≤ (1 + R) ^ s.card := by
  classical
  induction s using Finset.induction_on generalizing j with
  | empty =>
      simp only [prod_empty, card_empty, pow_zero, coeff_one]
      split_ifs <;> norm_num
  | @insert i s hi ih =>
      have hnode := hnodes i (mem_insert_self _ _)
      have hs : ∀ a ∈ s, ‖nodes a‖ ≤ R := fun a ha => hnodes a (mem_insert_of_mem ha)
      rw [prod_insert hi, card_insert_of_notMem hi, pow_succ, sub_mul, coeff_sub,
        coeff_C_mul]
      have hX : ‖(X * ∏ a ∈ s, (X - C (nodes a))).coeff j‖ ≤ (1 + R) ^ s.card := by
        cases j with
        | zero => simp only [coeff_X_mul_zero, norm_zero]; positivity
        | succ j => simpa only [coeff_X_mul] using ih hs j
      calc
        _ ≤ ‖(X * ∏ a ∈ s, (X - C (nodes a))).coeff j‖ +
            ‖nodes i * (∏ a ∈ s, (X - C (nodes a))).coeff j‖ := norm_sub_le _ _
        _ ≤ (1 + R) ^ s.card + R * (1 + R) ^ s.card := by
          rw [norm_mul]
          exact add_le_add hX (mul_le_mul hnode (ih hs j) (norm_nonneg _) hR)
        _ = (1 + R) ^ s.card * (1 + R) := by ring

/-- Explicit derivative evaluation constant for degree at most `n` and
coefficient bound one on the radius-`R` interval. -/
def polynomialDerivativeBound (n order : ℕ) (R : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1),
    ((i + order).descFactorial order : ℝ) * (1 + R) ^ i

/-- The explicit polynomial derivative bound is nonnegative at every
nonnegative interval radius. -/
theorem polynomialDerivativeBound_nonneg (n order : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    0 ≤ polynomialDerivativeBound n order R := by
  unfold polynomialDerivativeBound
  positivity

/-- Coefficient control gives actual iterated polynomial derivative control
on a fixed interval, without any reference to interpolation nodes. -/
theorem norm_eval_iterate_derivative_le_of_coeff_bound (p : ℂ[X]) (n order : ℕ)
    (hdegree : p.natDegree ≤ n) {R B : ℝ} (_hR : 0 ≤ R) (hB : 0 ≤ B)
    (hcoeff : ∀ i, ‖p.coeff i‖ ≤ B) {x : ℂ} (hx : ‖x‖ ≤ R) :
    ‖((Polynomial.derivative^[order]) p).eval x‖ ≤
      B * polynomialDerivativeBound n order R := by
  have hd : ((Polynomial.derivative^[order]) p).natDegree < n + 1 :=
    lt_of_le_of_lt ((Polynomial.natDegree_iterate_derivative p order).trans
      ((Nat.sub_le _ _).trans hdegree)) (Nat.lt_succ_self _)
  rw [Polynomial.eval_eq_sum_range' hd]
  calc
    _ ≤ ∑ i ∈ Finset.range (n + 1),
        ‖((Polynomial.derivative^[order]) p).coeff i * x ^ i‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (n + 1),
        B * (((i + order).descFactorial order : ℝ) * (1 + R) ^ i) := by
      apply Finset.sum_le_sum
      intro i _
      rw [Polynomial.coeff_iterate_derivative, nsmul_eq_mul, norm_mul, norm_mul,
        norm_natCast, norm_pow]
      have hp : ‖x‖ ^ i ≤ (1 + R) ^ i :=
        pow_le_pow_left₀ (norm_nonneg x) (hx.trans (by linarith)) i
      calc
        _ ≤ ((i + order).descFactorial order : ℝ) * B * (1 + R) ^ i := by
          gcongr
          exact hcoeff _
        _ = B * (((i + order).descFactorial order : ℝ) * (1 + R) ^ i) := by ring
    _ = B * polynomialDerivativeBound n order R := by
      rw [polynomialDerivativeBound, Finset.mul_sum]

/-- Explicit collision-safe derivative bound for a Newton basis polynomial. -/
theorem norm_eval_iterate_derivative_newtonBasisPolynomial_le {n : ℕ}
    (nodes : Fin n → ℂ) (k : Fin n) (order : ℕ) {R : ℝ}
    (hR : 0 ≤ R) (hnodes : ∀ i, ‖nodes i‖ ≤ R) {x : ℂ} (hx : ‖x‖ ≤ R) :
    ‖((Polynomial.derivative^[order]) (newtonBasisPolynomial nodes k)).eval x‖ ≤
      (1 + R) ^ (k : ℕ) * polynomialDerivativeBound k order R := by
  apply norm_eval_iterate_derivative_le_of_coeff_bound _ k order
    (by rw [natDegree_newtonBasisPolynomial]) hR (by positivity) _ hx
  intro i
  simpa only [newtonBasisPolynomial, Lagrange.nodal, Fin.card_Iio] using
    norm_coeff_prod_X_sub_C_le (Finset.Iio k) nodes hR (fun a _ => hnodes a) i

/-- A single derivative-order constant for every Newton basis vector with
index below `n`; the expression depends only on `n`, `order`, and `R`. -/
def uniformNewtonDerivativeBound (n order : ℕ) (R : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, (1 + R) ^ k * polynomialDerivativeBound k order R

/-- Every summand in the uniform Newton constant is nonnegative. -/
theorem uniformNewtonDerivativeBound_nonneg (n order : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    0 ≤ uniformNewtonDerivativeBound n order R := by
  apply Finset.sum_nonneg
  intro k _
  exact mul_nonneg (by positivity) (polynomialDerivativeBound_nonneg k order hR)

/-- Derivatives of the actual Newton interpolant are bounded by the sum of
its Newton coefficient magnitudes, uniformly under arbitrary node collision. -/
theorem norm_eval_iterate_derivative_newtonInterpolant_le {n : ℕ}
    (nodes : Fin n → ℂ) (data : Fin n → ℂ) (order : ℕ) {R : ℝ}
    (hR : 0 ≤ R) (hnodes : ∀ i, ‖nodes i‖ ≤ R) {x : ℂ} (hx : ‖x‖ ≤ R) :
    ‖((Polynomial.derivative^[order]) (newtonInterpolant nodes data)).eval x‖ ≤
      uniformNewtonDerivativeBound n order R * ∑ i : Fin n, ‖data i‖ := by
  classical
  rw [newtonInterpolant_eq_sum, Polynomial.iterate_derivative_sum,
    Polynomial.eval_finsetSum]
  calc
    _ ≤ ∑ i : Fin n,
        ‖((Polynomial.derivative^[order]) (C (data i) * newtonBasisPolynomial nodes i)).eval x‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i : Fin n, uniformNewtonDerivativeBound n order R * ‖data i‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [Polynomial.iterate_derivative_C_mul, Polynomial.eval_mul, Polynomial.eval_C, norm_mul]
      have hsingle : (1 + R) ^ (i : ℕ) * polynomialDerivativeBound i order R ≤
          uniformNewtonDerivativeBound n order R := by
        exact Finset.single_le_sum (fun k _ => mul_nonneg (by positivity)
          (polynomialDerivativeBound_nonneg k order hR)) (Finset.mem_range.mpr i.isLt)
      have hb := (norm_eval_iterate_derivative_newtonBasisPolynomial_le
        nodes i order hR hnodes hx).trans hsingle
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hb (norm_nonneg (data i))
    _ = uniformNewtonDerivativeBound n order R * ∑ i : Fin n, ‖data i‖ :=
      (Finset.mul_sum ..).symm

/-- The abstract confluent interpolant inherits the same explicit
gap-independent Newton-coefficient derivative estimate. -/
theorem norm_eval_iterate_derivative_confluentNewtonInterpolant_le {n : ℕ}
    (nodes : ℕ → ℂ) (data : Fin n → ℂ) (order : ℕ) {R : ℝ}
    (hR : 0 ≤ R) (hnodes : ∀ i < n, ‖nodes i‖ ≤ R) {x : ℂ} (hx : ‖x‖ ≤ R) :
    ‖((Polynomial.derivative^[order])
      (confluentNewtonInterpolant nodes data : ℂ[X])).eval x‖ ≤
        uniformNewtonDerivativeBound n order R * ∑ i : Fin n, ‖data i‖ := by
  rw [confluentNewtonInterpolant_eq_newtonInterpolant]
  exact norm_eval_iterate_derivative_newtonInterpolant_le _ data order hR
    (fun i => hnodes i i.isLt) hx

/-- A common constant for all derivative orders at degree below `n`.
Its only parameters are the degree bound and interval radius. -/
def uniformNewtonBound (n : ℕ) (R : ℝ) : ℝ :=
  ∑ order ∈ Finset.range (n + 1), uniformNewtonDerivativeBound n order R

/-- The common all-order Newton bound is nonnegative. -/
theorem uniformNewtonBound_nonneg (n : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    0 ≤ uniformNewtonBound n R :=
  Finset.sum_nonneg (fun order _ => uniformNewtonDerivativeBound_nonneg n order hR)

/-- A single degree/radius constant controls every derivative of the
confluent interpolant; derivatives above its degree vanish exactly. -/
theorem norm_eval_iterate_derivative_confluentNewtonInterpolant_le_uniform {n : ℕ}
    (nodes : ℕ → ℂ) (data : Fin n → ℂ) (order : ℕ) {R : ℝ}
    (hR : 0 ≤ R) (hnodes : ∀ i < n, ‖nodes i‖ ≤ R) {x : ℂ} (hx : ‖x‖ ≤ R) :
    ‖((Polynomial.derivative^[order])
      (confluentNewtonInterpolant nodes data : ℂ[X])).eval x‖ ≤
        uniformNewtonBound n R * ∑ i : Fin n, ‖data i‖ := by
  by_cases horder : order ≤ n
  · refine (norm_eval_iterate_derivative_confluentNewtonInterpolant_le
      nodes data order hR hnodes hx).trans ?_
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun i _ => norm_nonneg _)
    exact Finset.single_le_sum
      (fun r _ => uniformNewtonDerivativeBound_nonneg n r hR)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le horder))
  · have hp : (confluentNewtonInterpolant nodes data : ℂ[X]).degree < order :=
      (Polynomial.mem_degreeLT.mp (confluentNewtonInterpolant nodes data).property).trans_le
        (WithBot.coe_le_coe.mpr (Nat.le_of_not_ge horder))
    rw [Polynomial.iterate_derivative_eq_zero_of_degree_lt hp, Polynomial.eval_zero, norm_zero]
    exact mul_nonneg (uniformNewtonBound_nonneg n hR) (Finset.sum_nonneg fun i _ => norm_nonneg _)

/-- Divided differences at any real nodes in the same compact interval are
bounded by the confluent Newton data, including repeated evaluation nodes.
The exact Hermite–Genocchi factorial is retained. -/
theorem norm_polynomialDividedDifference_confluentNewtonInterpolant_le {n : ℕ}
    (nodes : ℕ → ℂ) (data : Fin n → ℂ) (testNodes : ℕ → ℝ) (order : ℕ) {R : ℝ}
    (hR : 0 ≤ R) (hnodes : ∀ i < n, ‖nodes i‖ ≤ R)
    (htest : ∀ i ≤ order, testNodes i ∈ Set.Icc (-R) R) :
    ‖polynomialDividedDifference (fun i => (testNodes i : ℂ)) order
      (confluentNewtonInterpolant nodes data : ℂ[X])‖ ≤
        (uniformNewtonBound n R * ∑ i : Fin n, ‖data i‖) / (order.factorial : ℝ) := by
  apply norm_polynomialDividedDifference_le testNodes order _ htest
  intro x hx
  apply norm_eval_iterate_derivative_confluentNewtonInterpolant_le_uniform
    nodes data order hR hnodes
  simpa only [Complex.norm_real, Real.norm_eq_abs] using abs_le.mpr hx

/-- Polynomial subgroup data are controlled by the full prefix data on the
same interval. The evaluation multiset can repeat, and need not be a subset
when the input is already a degree-bounded polynomial. -/
theorem norm_polynomialDividedDifference_le_fullNewtonData {n : ℕ}
    (nodes : ℕ → ℂ) (p : Polynomial.degreeLT ℂ n)
    (testNodes : ℕ → ℝ) (order : ℕ) {R : ℝ}
    (hR : 0 ≤ R) (hnodes : ∀ i < n, ‖nodes i‖ ≤ R)
    (htest : ∀ i ≤ order, testNodes i ∈ Set.Icc (-R) R) :
    ‖polynomialDividedDifference (fun i => (testNodes i : ℂ)) order p‖ ≤
      (uniformNewtonBound n R *
        ∑ i : Fin n, ‖polynomialDividedDifference nodes i p‖) / (order.factorial : ℝ) := by
  have h := norm_polynomialDividedDifference_confluentNewtonInterpolant_le nodes
    (fun i : Fin n => polynomialDividedDifference nodes i p) testNodes order hR hnodes htest
  simpa only [confluentNewtonInterpolant_own_data] using h

/-- Formal iterated polynomial derivatives agree with genuine real
derivatives of complex polynomial evaluation on the real line. -/
theorem iteratedDeriv_polynomial_eval_ofReal (p : ℂ[X]) (order : ℕ) :
    iteratedDeriv order (fun x : ℝ => p.eval (x : ℂ)) =
      fun x : ℝ => ((Polynomial.derivative^[order]) p).eval (x : ℂ) := by
  induction order with
  | zero => rfl
  | succ order ih =>
      rw [iteratedDeriv_succ, ih]
      funext x
      rw [Function.iterate_succ_apply']
      exact ((((Polynomial.derivative^[order]) p).hasDerivAt (x : ℂ)).comp_ofReal).deriv

/-- The degree/radius constant bounds genuine derivatives of the actual
confluent interpolant on the real compact interval. -/
theorem norm_iteratedDeriv_confluentNewtonInterpolant_le_uniform {n : ℕ}
    (nodes : ℕ → ℂ) (data : Fin n → ℂ) (order : ℕ) {R : ℝ}
    (hR : 0 ≤ R) (hnodes : ∀ i < n, ‖nodes i‖ ≤ R)
    {x : ℝ} (hx : x ∈ Set.Icc (-R) R) :
    ‖iteratedDeriv order
      (fun t : ℝ => (confluentNewtonInterpolant nodes data : ℂ[X]).eval (t : ℂ)) x‖ ≤
        uniformNewtonBound n R * ∑ i : Fin n, ‖data i‖ := by
  rw [iteratedDeriv_polynomial_eval_ofReal]
  exact norm_eval_iterate_derivative_confluentNewtonInterpolant_le_uniform
    nodes data order hR hnodes (by
      simpa only [Complex.norm_real, Real.norm_eq_abs] using abs_le.mpr hx)

/-- The same polynomial subgroup estimate in the actual analytic
divided-difference API, including every confluent node configuration. -/
theorem norm_analyticDividedDifference_le_fullNewtonData {n : ℕ}
    (nodes : ℕ → ℂ) (p : Polynomial.degreeLT ℂ n)
    (testNodes : ℕ → ℝ) (order : ℕ) {R : ℝ}
    (hR : 0 ≤ R) (hnodes : ∀ i < n, ‖nodes i‖ ≤ R)
    (htest : ∀ i ≤ order, testNodes i ∈ Set.Icc (-R) R) :
    ‖analyticDividedDifference testNodes order (fun x : ℝ => p.1.eval (x : ℂ))‖ ≤
      (uniformNewtonBound n R *
        ∑ i : Fin n, ‖polynomialDividedDifference nodes i p‖) / (order.factorial : ℝ) := by
  rw [analyticDividedDifference_polynomial_eval]
  exact norm_polynomialDividedDifference_le_fullNewtonData nodes p testNodes order hR hnodes htest

/-- One explicit constant works simultaneously for all cluster sizes at
most `q`, not only for a single fixed number of nodes. -/
def boundedClusterNewtonBound (q : ℕ) (R : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (q + 1), uniformNewtonBound n R

/-- The common bounded-cluster Newton constant is nonnegative. -/
theorem boundedClusterNewtonBound_nonneg (q : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    0 ≤ boundedClusterNewtonBound q R :=
  Finset.sum_nonneg (fun n _ => uniformNewtonBound_nonneg n hR)

/-- Uniform genuine derivative bounds for all cluster lengths at most `q`
and all derivative orders, with arbitrary node multiplicities. -/
theorem norm_iteratedDeriv_confluentNewtonInterpolant_le_of_length_le {n q : ℕ}
    (hnq : n ≤ q) (nodes : ℕ → ℂ) (data : Fin n → ℂ) (order : ℕ) {R : ℝ}
    (hR : 0 ≤ R) (hnodes : ∀ i < n, ‖nodes i‖ ≤ R)
    {x : ℝ} (hx : x ∈ Set.Icc (-R) R) :
    ‖iteratedDeriv order
      (fun t : ℝ => (confluentNewtonInterpolant nodes data : ℂ[X]).eval (t : ℂ)) x‖ ≤
        boundedClusterNewtonBound q R * ∑ i : Fin n, ‖data i‖ := by
  refine (norm_iteratedDeriv_confluentNewtonInterpolant_le_uniform
    nodes data order hR hnodes hx).trans ?_
  apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun i _ => norm_nonneg _)
  exact Finset.single_le_sum (fun r _ => uniformNewtonBound_nonneg r hR)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hnq))

/-- Polynomial subgroup control with one constant depending only on the
maximum cluster size and interval radius. No node separation enters. -/
theorem norm_analyticDividedDifference_le_boundedClusterNewtonData {n q : ℕ}
    (hnq : n ≤ q) (nodes : ℕ → ℂ) (p : Polynomial.degreeLT ℂ n)
    (testNodes : ℕ → ℝ) (order : ℕ) {R : ℝ}
    (hR : 0 ≤ R) (hnodes : ∀ i < n, ‖nodes i‖ ≤ R)
    (htest : ∀ i ≤ order, testNodes i ∈ Set.Icc (-R) R) :
    ‖analyticDividedDifference testNodes order (fun x : ℝ => p.1.eval (x : ℂ))‖ ≤
      boundedClusterNewtonBound q R *
        ∑ i : Fin n, ‖polynomialDividedDifference nodes i p‖ := by
  have hfirst := norm_analyticDividedDifference_le_fullNewtonData
    nodes p testNodes order hR hnodes htest
  have hsum : 0 ≤ ∑ i : Fin n, ‖polynomialDividedDifference nodes i p‖ :=
    Finset.sum_nonneg fun i _ => norm_nonneg _
  have hfact : (1 : ℝ) ≤ order.factorial := by exact_mod_cast Nat.factorial_pos order
  refine hfirst.trans ((div_le_self
    (mul_nonneg (uniformNewtonBound_nonneg n hR) hsum) hfact).trans ?_)
  apply mul_le_mul_of_nonneg_right _ hsum
  exact Finset.single_le_sum (fun r _ => uniformNewtonBound_nonneg r hR)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hnq))

end

end MeyerGeneralProblem
