module

public import MeyerGeneralProblem.Interpolation.HermiteGenocchi
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import all Mathlib.Analysis.Calculus.IteratedDeriv.Defs

@[expose] public section

/-!
# Arbitrary-order Hermite–Genocchi integrals

Weighted affine derivative averages provide the induction step for analytic
Newton quotients.  The recursive integral uses the genuine simplex-Jacobian
weights, and is identified with analytic divided differences by differentiation
under the integral sign.  Its total mass is `1 / n!`, independently of node
gaps, and nodes are allowed to coincide.
-/

namespace MeyerGeneralProblem

noncomputable section

open MeasureTheory Set
open scoped Topology Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A weighted affine average, the derivative integral for a Newton quotient. -/
def weightedDerivativeAverage (order : ℕ) (g : ℝ → E) (a b : ℝ) : E :=
  ∫ t in (0 : ℝ)..1, t ^ order • g (a + (b - a) * t)

/-- Continuous integrands give continuous weighted averages in the moving node. -/
theorem continuous_weightedDerivativeAverage (order : ℕ) {g : ℝ → E}
    (hg : Continuous g) (a : ℝ) : Continuous (weightedDerivativeAverage order g a) := by
  change Continuous (fun b : ℝ =>
    ∫ t in (0 : ℝ)..1, t ^ order • g (a + (b - a) * t))
  have hc : Continuous (fun b : ℝ =>
      ∫ t in Icc (0 : ℝ) 1, t ^ order • g (a + (b - a) * t)) :=
    continuous_parametric_integral_of_continuous (by fun_prop) isCompact_Icc
  simpa only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_Icc_eq_integral_Ioc] using hc

/-- The mass of the order-`j` weight is `1 / (j + 1)`. -/
theorem norm_weightedDerivativeAverage_le (order : ℕ) {g : ℝ → E} {a b M : ℝ}
    (hbound : ∀ x ∈ uIcc a b, ‖g x‖ ≤ M) :
    ‖weightedDerivativeAverage order g a b‖ ≤ M / (order + 1 : ℕ) := by
  have h := intervalIntegral.norm_integral_le_of_norm_le
    (f := fun t : ℝ => t ^ order • g (a + (b - a) * t)) (μ := volume)
    (a := (0 : ℝ)) (b := 1) (g := fun t : ℝ => t ^ order * M) (by norm_num)
    (Filter.Eventually.of_forall (by
      intro t ht
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg ht.1.le _)]
      exact mul_le_mul_of_nonneg_left
        (hbound _ (affineNode_mem_uIcc a b ⟨ht.1.le, ht.2⟩)) (pow_nonneg ht.1.le _)))
    (((continuous_id.pow order).mul continuous_const).intervalIntegrable _ _)
  rw [intervalIntegral.integral_mul_const, integral_pow] at h
  simpa only [weightedDerivativeAverage, one_pow, zero_pow (Nat.succ_ne_zero order),
    sub_zero, Nat.cast_add, Nat.cast_one, one_div, one_mul,
    div_eq_mul_inv, mul_comm M] using h

section Complete

variable [CompleteSpace E]

/-- At zero weight the average is the actual extended divided slope. -/
theorem weightedDerivativeAverage_zero_eq_dslope {f f' : ℝ → E}
    (hderiv : ∀ x, HasDerivAt f (f' x) x) (hcont : Continuous f') (a b : ℝ) :
    weightedDerivativeAverage 0 f' a b = dslope f a b := by
  simpa only [weightedDerivativeAverage, pow_zero, one_smul] using
    (dslope_eq_integral_derivative (fun x _ => hderiv x)
      (hcont.intervalIntegrable a b)).symm

/-- A collapsed weighted affine average retains its exact reciprocal weight. -/
theorem weightedDerivativeAverage_same (order : ℕ) (g : ℝ → E) (a : ℝ) :
    weightedDerivativeAverage order g a a = (1 / (order + 1 : ℕ) : ℝ) • g a := by
  simp only [weightedDerivativeAverage, sub_self, zero_mul, add_zero,
    intervalIntegral.integral_smul_const, integral_pow, one_pow,
    zero_pow (Nat.succ_ne_zero order), sub_zero, Nat.cast_add, Nat.cast_one]

omit [CompleteSpace E] in
/-- Differentiation increases the weight by one.  Compact domination is proved
from continuity, with no uniform global bound on the derivative. -/
theorem hasDerivAt_weightedDerivativeAverage (order : ℕ) {g g' : ℝ → E}
    (hderiv : ∀ x, HasDerivAt g (g' x) x) (hcont' : Continuous g') (a b : ℝ) :
    HasDerivAt (weightedDerivativeAverage order g a)
      (weightedDerivativeAverage (order + 1) g' a b) b := by
  have hcont : Continuous g := continuous_iff_continuousAt.mpr
    (fun x => (hderiv x).continuousAt)
  have hcontinuous : Continuous (fun z : ℝ × ℝ =>
      ‖z.2 ^ (order + 1) • g' (a + (z.1 - a) * z.2)‖) := by fun_prop
  obtain ⟨M, hM⟩ := ((isCompact_Icc : IsCompact (Icc (b - 1) (b + 1))).prod
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1))).bddAbove_image
      hcontinuous.continuousOn
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun x t : ℝ => t ^ order • g (a + (x - a) * t))
    (F' := fun x t : ℝ => t ^ (order + 1) • g' (a + (x - a) * t))
    (bound := fun _ => M) (μ := volume)
    (a := (0 : ℝ)) (b := 1) (s := Ioo (b - 1) (b + 1)) (x₀ := b)
    (Ioo_mem_nhds (by linarith) (by linarith))
    (Filter.Eventually.of_forall (fun x =>
      (show Continuous (fun t : ℝ => t ^ order • g (a + (x - a) * t)) by
        fun_prop).aestronglyMeasurable))
    ((show Continuous (fun t : ℝ => t ^ order • g (a + (b - a) * t)) by
      fun_prop).intervalIntegrable _ _)
    ((show Continuous (fun t : ℝ => t ^ (order + 1) • g' (a + (b - a) * t)) by
      fun_prop).aestronglyMeasurable)
    (Filter.Eventually.of_forall (by
      intro t ht x hx
      have ht' : t ∈ Ioc (0 : ℝ) 1 := by simpa using ht
      exact hM (mem_image_of_mem _ (show (x, t) ∈
        Icc (b - 1) (b + 1) ×ˢ Icc (0 : ℝ) 1 from
          ⟨⟨hx.1.le, hx.2.le⟩, ht'.1.le, ht'.2⟩))))
    (intervalIntegrable_const)
    (Filter.Eventually.of_forall (by
      intro t _ x _
      have hinner : HasDerivAt (fun y : ℝ => a + (y - a) * t) t x := by
        simpa using (((hasDerivAt_id x).sub_const a).mul_const t).const_add a
      simpa only [Function.comp_def, Pi.smul_def, smul_smul, ← pow_succ] using
        ((hderiv _).scomp x hinner).const_smul (t ^ order)))).2

end Complete

/-- Hermite–Genocchi integration in recursive cube coordinates.  The descending
power weights are the simplex Jacobian; this is not defined using differences. -/
def hermiteGenocchiIntegral (nodes : ℕ → ℝ) : ℕ → (ℝ → E) → E
  | 0, g => g (nodes 0)
  | order + 1, g => hermiteGenocchiIntegral (fun i => nodes (i + 1)) order
      (weightedDerivativeAverage order g (nodes 0))

/-- An order-zero simplex integral is evaluation at its sole node. -/
@[simp]
theorem hermiteGenocchiIntegral_zero (nodes : ℕ → ℝ) (g : ℝ → E) :
    hermiteGenocchiIntegral nodes 0 g = g (nodes 0) := rfl

/-- The genuine integral recursion and its simplex weight. -/
theorem hermiteGenocchiIntegral_succ (nodes : ℕ → ℝ) (order : ℕ) (g : ℝ → E) :
    hermiteGenocchiIntegral nodes (order + 1) g =
      hermiteGenocchiIntegral (fun i => nodes (i + 1)) order
        (weightedDerivativeAverage order g (nodes 0)) := rfl

/-- The integral has total mass `1 / n!` on any common enclosing interval,
independently of all node separations. -/
theorem norm_hermiteGenocchiIntegral_le (nodes : ℕ → ℝ) (order : ℕ)
    (g : ℝ → E) {L U M : ℝ}
    (hnodes : ∀ j ≤ order, nodes j ∈ Icc L U)
    (hbound : ∀ x ∈ Icc L U, ‖g x‖ ≤ M) :
    ‖hermiteGenocchiIntegral nodes order g‖ ≤ M / (order.factorial : ℝ) := by
  induction order generalizing nodes g M with
  | zero => simpa using hbound (nodes 0) (hnodes 0 (by omega))
  | succ order ih =>
      change ‖hermiteGenocchiIntegral (fun i => nodes (i + 1)) order
        (weightedDerivativeAverage order g (nodes 0))‖ ≤ _
      have h := ih (fun i => nodes (i + 1))
        (weightedDerivativeAverage order g (nodes 0))
        (M := M / (order + 1 : ℕ))
        (fun j hj => hnodes (j + 1) (by omega)) (by
          intro x hx
          apply norm_weightedDerivativeAverage_le
          intro y hy
          exact hbound y (uIcc_subset_Icc (hnodes 0 (by omega)) hx hy))
      simpa only [div_div, Nat.factorial_succ, Nat.cast_mul] using h

/-- Continuous finite-dimensional parameters, nodes, and integrands give a
continuous Hermite–Genocchi integral, including at every node collision. -/
theorem continuous_hermiteGenocchiIntegral_parametric
    {P : Type*} [TopologicalSpace P] [FirstCountableTopology P] [LocallyCompactSpace P]
    (nodes : P → ℕ → ℝ) (order : ℕ) (g : P → ℝ → E)
    (hnodes : ∀ j, Continuous (fun p => nodes p j))
    (hg : Continuous (Function.uncurry g)) :
    Continuous (fun p => hermiteGenocchiIntegral (nodes p) order (g p)) := by
  induction order generalizing nodes g with
  | zero =>
      exact hg.comp (continuous_id.prodMk (hnodes 0))
  | succ order ih =>
      let G : P → ℝ → E := fun p =>
        weightedDerivativeAverage order (g p) (nodes p 0)
      have hG : Continuous (Function.uncurry G) := by
        change Continuous (fun z : P × ℝ =>
          ∫ t in (0 : ℝ)..1, t ^ order • g z.1 (nodes z.1 0 + (z.2 - nodes z.1 0) * t))
        have hzero := hnodes 0
        have hint : Continuous (fun z : (P × ℝ) × ℝ =>
            z.2 ^ order • g z.1.1 (nodes z.1.1 0 + (z.1.2 - nodes z.1.1 0) * z.2)) := by
          apply (continuous_snd.pow order).smul
          exact hg.comp (show Continuous (fun z : (P × ℝ) × ℝ =>
            (z.1.1, nodes z.1.1 0 + (z.1.2 - nodes z.1.1 0) * z.2)) by fun_prop)
        have hc : Continuous (fun z : P × ℝ =>
            ∫ t in Icc (0 : ℝ) 1,
              t ^ order • g z.1 (nodes z.1 0 + (z.2 - nodes z.1 0) * t)) :=
          continuous_parametric_integral_of_continuous hint isCompact_Icc
        simpa only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
          integral_Icc_eq_integral_Ioc] using hc
      exact ih (fun p j => nodes p (j + 1)) G (fun j => hnodes (j + 1)) hG

/-- Extend a finite node presentation by zero; order-bounded differences only
inspect its finite prefix. -/
def finiteNodeSequence {n : ℕ} (nodes : Fin n → ℝ) (j : ℕ) : ℝ :=
  if hj : j < n then nodes ⟨j, hj⟩ else 0

/-- The finite extension retains every actual node exactly. -/
@[simp]
theorem finiteNodeSequence_apply {n : ℕ} (nodes : Fin n → ℝ) (i : Fin n) :
    finiteNodeSequence nodes i = nodes i := by simp [finiteNodeSequence, i.isLt]

/-- Each coordinate of the extended finite node sequence is continuous. -/
theorem continuous_finiteNodeSequence (n j : ℕ) :
    Continuous (fun nodes : Fin n → ℝ => finiteNodeSequence nodes j) := by
  unfold finiteNodeSequence
  split_ifs with hj
  · exact continuous_apply (⟨j, hj⟩ : Fin n)
  · exact continuous_const

/-- The true integral is jointly continuous in all nodes of a finite cluster,
without a minimum-gap hypothesis. -/
theorem continuous_hermiteGenocchiIntegral_nodes (order : ℕ) {g : ℝ → E}
    (hg : Continuous g) :
    Continuous (fun nodes : Fin (order + 1) → ℝ =>
      hermiteGenocchiIntegral (finiteNodeSequence nodes) order g) := by
  apply continuous_hermiteGenocchiIntegral_parametric
  · exact fun j => continuous_finiteNodeSequence _ j
  · exact hg.comp continuous_snd

section CompleteHigher

variable [CompleteSpace E]

/-- Full collapse of the genuine integral gives its exact factorial mass. -/
theorem hermiteGenocchiIntegral_repeated_node (a : ℝ) (order : ℕ) (g : ℝ → E) :
    hermiteGenocchiIntegral (fun _ => a) order g =
      (1 / (order.factorial : ℝ)) • g a := by
  induction order generalizing g with
  | zero => simp
  | succ order ih =>
      change hermiteGenocchiIntegral (fun _ => a) order
        (weightedDerivativeAverage order g a) = _
      rw [ih, weightedDerivativeAverage_same, smul_smul]
      congr 1
      simp [Nat.factorial_succ, Nat.cast_mul, div_eq_mul_inv, mul_comm]

/-- A genuine finite derivative tower identifies the analytic Newton recursion
with the Hermite–Genocchi integral of its highest derivative.  The proof uses
the weighted differentiation theorem, not an assumed representation formula. -/
theorem analyticDividedDifference_eq_hermiteGenocchi_of_derivativeTower
    (nodes : ℕ → ℝ) (order : ℕ) (F : ℕ → ℝ → E)
    (hcont : ∀ j ≤ order, Continuous (F j))
    (hderiv : ∀ j < order, ∀ x, HasDerivAt (F j) (F (j + 1) x) x) :
    analyticDividedDifference nodes order (F 0) =
      hermiteGenocchiIntegral nodes order (F order) := by
  induction order generalizing nodes F with
  | zero => rfl
  | succ order ih =>
      let G : ℕ → ℝ → E := fun j =>
        weightedDerivativeAverage j (F (j + 1)) (nodes 0)
      have hgzero : dslope (F 0) (nodes 0) = G 0 := by
        funext x
        exact (weightedDerivativeAverage_zero_eq_dslope
          (hderiv 0 (by omega)) (hcont 1 (by omega)) (nodes 0) x).symm
      change analyticDividedDifference (fun i => nodes (i + 1)) order
        (dslope (F 0) (nodes 0)) =
          hermiteGenocchiIntegral (fun i => nodes (i + 1)) order (G order)
      rw [hgzero]
      apply ih
      · intro j hj
        exact continuous_weightedDerivativeAverage j (hcont (j + 1) (by omega)) (nodes 0)
      · intro j hj x
        exact hasDerivAt_weightedDerivativeAverage j
          (hderiv (j + 1) (by omega)) (hcont (j + 1 + 1) (by omega)) (nodes 0) x

/-- Hermite–Genocchi representation for an arbitrary `C^n` Banach-valued
function on the real line, with repeated and unordered nodes permitted. -/
theorem analyticDividedDifference_eq_hermiteGenocchi (nodes : ℕ → ℝ) (order : ℕ)
    {f : ℝ → E} (hf : ContDiff ℝ order f) :
    analyticDividedDifference nodes order f =
      hermiteGenocchiIntegral nodes order (iteratedDeriv order f) := by
  have h := analyticDividedDifference_eq_hermiteGenocchi_of_derivativeTower
    nodes order (fun j => iteratedDeriv j f)
    (fun j hj => hf.continuous_iteratedDeriv j (by exact_mod_cast hj)) (by
      intro j hj x
      rw [iteratedDeriv_succ]
      exact (hf.differentiable_iteratedDeriv j (by exact_mod_cast hj) x).hasDerivAt)
  simpa only [iteratedDeriv_zero] using h

/-- The arbitrary-order `C^n` divided-difference estimate contains no inverse
node gap and has the exact factorial normalization. -/
theorem norm_analyticDividedDifference_le_of_contDiff (nodes : ℕ → ℝ) (order : ℕ)
    {f : ℝ → E} (hf : ContDiff ℝ order f) {L U M : ℝ}
    (hnodes : ∀ j ≤ order, nodes j ∈ Icc L U)
    (hbound : ∀ x ∈ Icc L U, ‖iteratedDeriv order f x‖ ≤ M) :
    ‖analyticDividedDifference nodes order f‖ ≤ M / (order.factorial : ℝ) := by
  rw [analyticDividedDifference_eq_hermiteGenocchi nodes order hf]
  exact norm_hermiteGenocchiIntegral_le nodes order _ hnodes hbound

/-- At fully collapsed nodes a `C^n` function gives its `n`-th derivative
divided by `n!`, with the same normalization as confluent polynomial data. -/
theorem analyticDividedDifference_repeated_node_of_contDiff (a : ℝ) (order : ℕ)
    {f : ℝ → E} (hf : ContDiff ℝ order f) :
    analyticDividedDifference (fun _ => a) order f =
      (1 / (order.factorial : ℝ)) • iteratedDeriv order f a := by
  rw [analyticDividedDifference_eq_hermiteGenocchi _ _ hf,
    hermiteGenocchiIntegral_repeated_node]

/-- `C^n` analytic divided differences extend jointly continuously across every
collision of the `n + 1` nodes in a finite cluster presentation. -/
theorem continuous_analyticDividedDifference_nodes (order : ℕ) {f : ℝ → E}
    (hf : ContDiff ℝ order f) :
    Continuous (fun nodes : Fin (order + 1) → ℝ =>
      analyticDividedDifference (finiteNodeSequence nodes) order f) := by
  simpa only [analyticDividedDifference_eq_hermiteGenocchi _ _ hf] using
    continuous_hermiteGenocchiIntegral_nodes order (hf.continuous_iteratedDeriv' order)

end CompleteHigher

/-- The existing synthetic polynomial divided difference equals the genuine
arbitrary-order integral of the iterated polynomial derivative. -/
theorem polynomialDividedDifference_eq_hermiteGenocchi (nodes : ℕ → ℝ) (order : ℕ)
    (p : Polynomial ℂ) :
    polynomialDividedDifference (fun j => (nodes j : ℂ)) order p =
      hermiteGenocchiIntegral nodes order
        (fun x : ℝ => ((Polynomial.derivative^[order]) p).eval (x : ℂ)) := by
  rw [← analyticDividedDifference_polynomial_eval]
  have h := analyticDividedDifference_eq_hermiteGenocchi_of_derivativeTower nodes order
    (fun (j : ℕ) (x : ℝ) => ((Polynomial.derivative^[j]) p).eval (x : ℂ))
    (by
      intro j _
      exact ((((Polynomial.derivative^[j]) p).differentiable.continuous).comp
        Complex.continuous_ofReal))
    (by
      intro j _ x
      rw [Function.iterate_succ_apply']
      exact (((Polynomial.derivative^[j]) p).hasDerivAt (x : ℂ)).comp_ofReal)
  simpa only [Function.iterate_zero, id_eq] using h

/-- Gap-independent polynomial divided-difference bounds use the same exact
factorial normalization as the analytic and confluent APIs. -/
theorem norm_polynomialDividedDifference_le (nodes : ℕ → ℝ) (order : ℕ)
    (p : Polynomial ℂ) {L U M : ℝ}
    (hnodes : ∀ j ≤ order, nodes j ∈ Icc L U)
    (hbound : ∀ x ∈ Icc L U,
      ‖((Polynomial.derivative^[order]) p).eval (x : ℂ)‖ ≤ M) :
    ‖polynomialDividedDifference (fun j => (nodes j : ℂ)) order p‖ ≤
      M / (order.factorial : ℝ) := by
  rw [polynomialDividedDifference_eq_hermiteGenocchi]
  exact norm_hermiteGenocchiIntegral_le nodes order _ hnodes hbound

end

end MeyerGeneralProblem
