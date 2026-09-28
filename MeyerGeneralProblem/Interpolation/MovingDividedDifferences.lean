module

public import MeyerGeneralProblem.Interpolation.HermiteGenocchiHigher
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import all Mathlib.Topology.UniformSpace.LocallyUniformConvergence

@[expose] public section

/-!
# Moving-function and moving-node divided-difference limits

The genuine Hermite–Genocchi integral has norm at most `1 / j!` times
the uniform norm of its integrand on a common enclosing interval. Its
subtraction law therefore controls varying functions without inverse node
gaps. Combining this estimate with continuity in the finite node list gives
convergence of actual analytic divided differences, including collisions.

For order `j`, only the highest real derivative must converge uniformly on
the enclosing interval. Every function and the limit are explicitly `C^j`.
This is a finite-cluster result, not a whole-line multiset extraction theorem.
-/

namespace MeyerGeneralProblem

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Subtraction for the actual weighted derivative integral, with its
integrability discharged from continuity. -/
theorem weightedDerivativeAverage_sub (order : ℕ) {g h : ℝ → E}
    (hg : Continuous g) (hh : Continuous h) (a b : ℝ) :
    weightedDerivativeAverage order (fun x => g x - h x) a b =
      weightedDerivativeAverage order g a b - weightedDerivativeAverage order h a b := by
  simp only [weightedDerivativeAverage, smul_sub]
  apply intervalIntegral.integral_sub
  · exact (show Continuous (fun t : ℝ => t ^ order • g (a + (b - a) * t)) by
      fun_prop).intervalIntegrable _ _
  · exact (show Continuous (fun t : ℝ => t ^ order • h (a + (b - a) * t)) by
      fun_prop).intervalIntegrable _ _

/-- Subtraction for the genuine recursive Hermite–Genocchi integral. -/
theorem hermiteGenocchiIntegral_sub (nodes : ℕ → ℝ) (order : ℕ) {g h : ℝ → E}
    (hg : Continuous g) (hh : Continuous h) :
    hermiteGenocchiIntegral nodes order (fun x => g x - h x) =
      hermiteGenocchiIntegral nodes order g - hermiteGenocchiIntegral nodes order h := by
  induction order generalizing nodes g h with
  | zero => rfl
  | succ order ih =>
      simp only [hermiteGenocchiIntegral_succ]
      have hsub : weightedDerivativeAverage order (fun x => g x - h x) (nodes 0) =
          fun x => weightedDerivativeAverage order g (nodes 0) x -
            weightedDerivativeAverage order h (nodes 0) x := by
        funext x
        exact weightedDerivativeAverage_sub order hg hh (nodes 0) x
      rw [hsub]
      exact ih (fun i => nodes (i + 1))
        (continuous_weightedDerivativeAverage order hg (nodes 0))
        (continuous_weightedDerivativeAverage order hh (nodes 0))

/-- Exact factorial error control for two actual HG integrands on a common
interval. All node collisions and orderings are permitted. -/
theorem norm_hermiteGenocchiIntegral_sub_le (nodes : ℕ → ℝ) (order : ℕ)
    {g h : ℝ → E} (hg : Continuous g) (hh : Continuous h) {L U M : ℝ}
    (hnodes : ∀ j ≤ order, nodes j ∈ Icc L U)
    (hbound : ∀ x ∈ Icc L U, ‖g x - h x‖ ≤ M) :
    ‖hermiteGenocchiIntegral nodes order g - hermiteGenocchiIntegral nodes order h‖ ≤
      M / (order.factorial : ℝ) := by
  rw [← hermiteGenocchiIntegral_sub nodes order hg hh]
  exact norm_hermiteGenocchiIntegral_le nodes order _ hnodes hbound

/-- A genuine order-`j` HG integral only inspects the first `j + 1` nodes. -/
theorem hermiteGenocchiIntegral_congr_nodes (nodes other : ℕ → ℝ) (order : ℕ)
    (g : ℝ → E) (h : ∀ j ≤ order, nodes j = other j) :
    hermiteGenocchiIntegral nodes order g = hermiteGenocchiIntegral other order g := by
  induction order generalizing nodes other g with
  | zero => simp only [hermiteGenocchiIntegral_zero, h 0 (by omega)]
  | succ order ih =>
      simp only [hermiteGenocchiIntegral_succ, h 0 (by omega)]
      exact ih (fun i => nodes (i + 1)) (fun i => other (i + 1)) _
        (fun j hj => h (j + 1) (by omega))

/-- Uniform convergence of the integrands on one enclosing interval and
convergence of the finite nodes imply convergence of the actual HG integral.
The varying and limiting integrands are continuous; no node gap is assumed. -/
theorem tendsto_hermiteGenocchiIntegral_of_tendstoUniformlyOn
    {α : Type*} {l : Filter α} (order : ℕ)
    (nodes : α → Fin (order + 1) → ℝ) (limitNodes : Fin (order + 1) → ℝ)
    (g : α → ℝ → E) (limit : ℝ → E)
    (hg : ∀ a, Continuous (g a)) (hlimit : Continuous limit)
    (hnodes : Tendsto nodes l (𝓝 limitNodes)) {L U : ℝ}
    (hbounded : ∀ᶠ a in l, ∀ i, nodes a i ∈ Icc L U)
    (huniform : TendstoUniformlyOn g limit l (Icc L U)) :
    Tendsto (fun a => hermiteGenocchiIntegral (finiteNodeSequence (nodes a)) order (g a)) l
      (𝓝 (hermiteGenocchiIntegral (finiteNodeSequence limitNodes) order limit)) := by
  have hfixed : Tendsto
      (fun a => hermiteGenocchiIntegral (finiteNodeSequence (nodes a)) order limit) l
      (𝓝 (hermiteGenocchiIntegral (finiteNodeSequence limitNodes) order limit)) :=
    (continuous_hermiteGenocchiIntegral_nodes order hlimit).continuousAt.tendsto.comp hnodes
  have herror : Tendsto (fun a =>
      hermiteGenocchiIntegral (finiteNodeSequence (nodes a)) order (g a) -
        hermiteGenocchiIntegral (finiteNodeSequence (nodes a)) order limit) l (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hfac : (0 : ℝ) < order.factorial := by positivity
    have huni := (Metric.tendstoUniformlyOn_iff.mp huniform)
      (ε / 2 * order.factorial) (mul_pos (half_pos hε) hfac)
    filter_upwards [hbounded, huni] with a hba hua
    rw [dist_zero_right]
    have hb := norm_hermiteGenocchiIntegral_sub_le
      (finiteNodeSequence (nodes a)) order (hg a) hlimit
      (M := ε / 2 * order.factorial) (by
        intro j hj
        have hj' : j < order + 1 := by omega
        simpa only [finiteNodeSequence, dite_eq_left hj'] using hba ⟨j, hj'⟩) (by
        intro x hx
        simpa only [dist_eq_norm, norm_sub_rev] using (hua x hx).le)
    have hcancel : (ε / 2 * order.factorial) / (order.factorial : ℝ) = ε / 2 :=
      mul_div_cancel_right₀ _ (ne_of_gt hfac)
    rw [hcancel] at hb
    exact hb.trans_lt (half_lt_self hε)
  have hsum := herror.add hfixed
  simpa only [sub_add_cancel, zero_add] using hsum

/-- A convergent finite node list is eventually contained in one explicit
common interval. No assumptions about ordering, distinctness, or gaps occur. -/
theorem eventually_mem_Icc_of_tendsto_finite_nodes
    {α : Type*} {l : Filter α} {n : ℕ}
    (nodes : α → Fin n → ℝ) (limitNodes : Fin n → ℝ)
    (hnodes : Tendsto nodes l (𝓝 limitNodes)) :
    ∀ᶠ a in l, ∀ i, nodes a i ∈ Icc (-(‖limitNodes‖ + 1)) (‖limitNodes‖ + 1) := by
  filter_upwards [Metric.tendsto_nhds.mp hnodes 1 zero_lt_one] with a ha
  intro i
  rw [dist_eq_norm] at ha
  apply abs_le.mp
  have hi : ‖nodes a i‖ ≤ ‖limitNodes‖ + 1 := by
    calc
      _ = ‖(nodes a i - limitNodes i) + limitNodes i‖ := by rw [sub_add_cancel]
      _ ≤ ‖nodes a i - limitNodes i‖ + ‖limitNodes i‖ := norm_add_le _ _
      _ ≤ ‖nodes a - limitNodes‖ + ‖limitNodes‖ :=
        add_le_add (norm_le_pi_norm (nodes a - limitNodes) i) (norm_le_pi_norm limitNodes i)
      _ ≤ ‖limitNodes‖ + 1 := by linarith
  simpa only [Real.norm_eq_abs] using hi

variable [CompleteSpace E]

/-- The moving-function divided-difference theorem: only the top derivative
must converge uniformly on the common interval. Genuine `C^j` regularity of
every function and the limit discharges the actual HG representation. -/
theorem tendsto_analyticDividedDifference_of_tendstoUniformlyOn_iteratedDeriv
    {α : Type*} {l : Filter α} (order : ℕ)
    (nodes : α → Fin (order + 1) → ℝ) (limitNodes : Fin (order + 1) → ℝ)
    (f : α → ℝ → E) (limit : ℝ → E)
    (hf : ∀ a, ContDiff ℝ order (f a)) (hlimit : ContDiff ℝ order limit)
    (hnodes : Tendsto nodes l (𝓝 limitNodes)) {L U : ℝ}
    (hbounded : ∀ᶠ a in l, ∀ i, nodes a i ∈ Icc L U)
    (huniform : TendstoUniformlyOn (fun a => iteratedDeriv order (f a))
      (iteratedDeriv order limit) l (Icc L U)) :
    Tendsto (fun a => analyticDividedDifference (finiteNodeSequence (nodes a)) order (f a)) l
      (𝓝 (analyticDividedDifference (finiteNodeSequence limitNodes) order limit)) := by
  simpa only [analyticDividedDifference_eq_hermiteGenocchi _ _ (hf _),
    analyticDividedDifference_eq_hermiteGenocchi _ _ hlimit] using
    tendsto_hermiteGenocchiIntegral_of_tendstoUniformlyOn order nodes limitNodes
      (fun a => iteratedDeriv order (f a)) (iteratedDeriv order limit)
      (fun a => (hf a).continuous_iteratedDeriv' order)
      (hlimit.continuous_iteratedDeriv' order) hnodes hbounded huniform

/-- Locally uniform convergence of the top derivative suffices with no
separately supplied enclosing interval: finite node convergence supplies it,
and compactness upgrades local uniform convergence on that interval. -/
theorem tendsto_analyticDividedDifference_of_tendstoLocallyUniformly_iteratedDeriv
    {α : Type*} {l : Filter α} (order : ℕ)
    (nodes : α → Fin (order + 1) → ℝ) (limitNodes : Fin (order + 1) → ℝ)
    (f : α → ℝ → E) (limit : ℝ → E)
    (hf : ∀ a, ContDiff ℝ order (f a)) (hlimit : ContDiff ℝ order limit)
    (hnodes : Tendsto nodes l (𝓝 limitNodes))
    (huniform : TendstoLocallyUniformly (fun a => iteratedDeriv order (f a))
      (iteratedDeriv order limit) l) :
    Tendsto (fun a => analyticDividedDifference (finiteNodeSequence (nodes a)) order (f a)) l
      (𝓝 (analyticDividedDifference (finiteNodeSequence limitNodes) order limit)) := by
  apply tendsto_analyticDividedDifference_of_tendstoUniformlyOn_iteratedDeriv
    order nodes limitNodes f limit hf hlimit hnodes
    (eventually_mem_Icc_of_tendsto_finite_nodes nodes limitNodes hnodes)
  exact (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact isCompact_Icc).mp
    huniform.tendstoLocallyUniformlyOn

/-- A common `C^q` derivative tower with locally uniform derivative limits
controls every moving prefix of order at most `q`. This is the finite-cluster
form consumed after analytic normal-family derivative convergence. -/
theorem tendsto_analyticDividedDifference_of_tendstoLocallyUniformly_derivatives
    {α : Type*} {l : Filter α} {order q : ℕ} (horder : order ≤ q)
    (nodes : α → Fin (order + 1) → ℝ) (limitNodes : Fin (order + 1) → ℝ)
    (f : α → ℝ → E) (limit : ℝ → E)
    (hf : ∀ a, ContDiff ℝ q (f a)) (hlimit : ContDiff ℝ q limit)
    (hnodes : Tendsto nodes l (𝓝 limitNodes))
    (huniform : ∀ j ≤ q, TendstoLocallyUniformly (fun a => iteratedDeriv j (f a))
      (iteratedDeriv j limit) l) :
    Tendsto (fun a => analyticDividedDifference (finiteNodeSequence (nodes a)) order (f a)) l
      (𝓝 (analyticDividedDifference (finiteNodeSequence limitNodes) order limit)) := by
  exact tendsto_analyticDividedDifference_of_tendstoLocallyUniformly_iteratedDeriv
    order nodes limitNodes f limit (fun a => (hf a).of_le (by exact_mod_cast horder))
    (hlimit.of_le (by exact_mod_cast horder)) hnodes (huniform order horder)

/-- A fully collapsed finite prefix has the same exact factorial jet as
the infinite constant-node presentation; the unused zero extension is irrelevant. -/
theorem analyticDividedDifference_finite_repeated_node_of_contDiff
    (centre : ℝ) (order : ℕ) {f : ℝ → E} (hf : ContDiff ℝ order f) :
    analyticDividedDifference
        (finiteNodeSequence (fun _ : Fin (order + 1) => centre)) order f =
      (1 / (order.factorial : ℝ)) • iteratedDeriv order f centre := by
  rw [analyticDividedDifference_eq_hermiteGenocchi _ _ hf]
  have hnodes : ∀ j ≤ order,
      finiteNodeSequence (fun _ : Fin (order + 1) => centre) j = centre := by
    intro j hj
    simp only [finiteNodeSequence, dite_eq_left (show j < order + 1 by omega)]
  rw [hermiteGenocchiIntegral_congr_nodes _ (fun _ => centre) order _ hnodes,
    hermiteGenocchiIntegral_repeated_node]

/-- When all finite nodes collide, the moving divided differences tend to
the actual factorially normalized derivative jet of the limiting function. -/
theorem tendsto_analyticDividedDifference_collision
    {α : Type*} {l : Filter α} (order : ℕ)
    (nodes : α → Fin (order + 1) → ℝ) (centre : ℝ)
    (f : α → ℝ → E) (limit : ℝ → E)
    (hf : ∀ a, ContDiff ℝ order (f a)) (hlimit : ContDiff ℝ order limit)
    (hnodes : Tendsto nodes l (𝓝 (fun _ => centre))) {L U : ℝ}
    (hbounded : ∀ᶠ a in l, ∀ i, nodes a i ∈ Icc L U)
    (huniform : TendstoUniformlyOn (fun a => iteratedDeriv order (f a))
      (iteratedDeriv order limit) l (Icc L U)) :
    Tendsto (fun a => analyticDividedDifference (finiteNodeSequence (nodes a)) order (f a)) l
      (𝓝 ((1 / (order.factorial : ℝ)) • iteratedDeriv order limit centre)) := by
  simpa only [analyticDividedDifference_finite_repeated_node_of_contDiff centre order hlimit]
    using tendsto_analyticDividedDifference_of_tendstoUniformlyOn_iteratedDeriv order nodes
      (fun _ => centre) f limit hf hlimit hnodes hbounded huniform

/-- Vanishing moving divided differences force the limiting normalized jet
to vanish at a full collision. The filter is nontrivial, so uniqueness of the
limit is substantive. -/
theorem normalizedJet_eq_zero_of_colliding_dividedDifferences_eq_zero
    {α : Type*} {l : Filter α} [NeBot l] (order : ℕ)
    (nodes : α → Fin (order + 1) → ℝ) (centre : ℝ)
    (f : α → ℝ → E) (limit : ℝ → E)
    (hf : ∀ a, ContDiff ℝ order (f a)) (hlimit : ContDiff ℝ order limit)
    (hnodes : Tendsto nodes l (𝓝 (fun _ => centre))) {L U : ℝ}
    (hbounded : ∀ᶠ a in l, ∀ i, nodes a i ∈ Icc L U)
    (huniform : TendstoUniformlyOn (fun a => iteratedDeriv order (f a))
      (iteratedDeriv order limit) l (Icc L U))
    (hzero : ∀ᶠ a in l,
      analyticDividedDifference (finiteNodeSequence (nodes a)) order (f a) = 0) :
    (1 / (order.factorial : ℝ)) • iteratedDeriv order limit centre = 0 := by
  exact tendsto_nhds_unique
    (tendsto_analyticDividedDifference_collision order nodes centre f limit hf hlimit
      hnodes hbounded huniform)
    (tendsto_const_nhds.congr' (Filter.EventuallyEq.symm hzero))

/-- The factorial normalization is nonzero, so the actual unnormalized
derivative jet also vanishes in the collision limit. -/
theorem iteratedDeriv_eq_zero_of_colliding_dividedDifferences_eq_zero
    {α : Type*} {l : Filter α} [NeBot l] (order : ℕ)
    (nodes : α → Fin (order + 1) → ℝ) (centre : ℝ)
    (f : α → ℝ → E) (limit : ℝ → E)
    (hf : ∀ a, ContDiff ℝ order (f a)) (hlimit : ContDiff ℝ order limit)
    (hnodes : Tendsto nodes l (𝓝 (fun _ => centre))) {L U : ℝ}
    (hbounded : ∀ᶠ a in l, ∀ i, nodes a i ∈ Icc L U)
    (huniform : TendstoUniformlyOn (fun a => iteratedDeriv order (f a))
      (iteratedDeriv order limit) l (Icc L U))
    (hzero : ∀ᶠ a in l,
      analyticDividedDifference (finiteNodeSequence (nodes a)) order (f a) = 0) :
    iteratedDeriv order limit centre = 0 := by
  have h := normalizedJet_eq_zero_of_colliding_dividedDifferences_eq_zero
    order nodes centre f limit hf hlimit hnodes hbounded huniform hzero
  exact (smul_eq_zero.mp h).resolve_left (by positivity)

/-- Locally uniform top-derivative convergence and vanishing moving data
force the actual limiting jet to vanish, without an assumed common interval. -/
theorem iteratedDeriv_eq_zero_of_colliding_locallyUniformly_dividedDifferences
    {α : Type*} {l : Filter α} [NeBot l] (order : ℕ)
    (nodes : α → Fin (order + 1) → ℝ) (centre : ℝ)
    (f : α → ℝ → E) (limit : ℝ → E)
    (hf : ∀ a, ContDiff ℝ order (f a)) (hlimit : ContDiff ℝ order limit)
    (hnodes : Tendsto nodes l (𝓝 (fun _ => centre)))
    (huniform : TendstoLocallyUniformly (fun a => iteratedDeriv order (f a))
      (iteratedDeriv order limit) l)
    (hzero : ∀ᶠ a in l,
      analyticDividedDifference (finiteNodeSequence (nodes a)) order (f a) = 0) :
    iteratedDeriv order limit centre = 0 := by
  apply iteratedDeriv_eq_zero_of_colliding_dividedDifferences_eq_zero
    order nodes centre f limit hf hlimit hnodes
    (eventually_mem_Icc_of_tendsto_finite_nodes nodes (fun _ => centre) hnodes) _ hzero
  exact (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact isCompact_Icc).mp
    huniform.tendstoLocallyUniformlyOn

end

end MeyerGeneralProblem
