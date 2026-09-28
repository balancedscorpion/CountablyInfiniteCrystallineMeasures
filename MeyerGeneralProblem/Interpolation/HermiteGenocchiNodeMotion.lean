module

public import MeyerGeneralProblem.Interpolation.MovingDividedDifferences
public import Mathlib.Analysis.Calculus.MeanValue
import all Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.FDeriv.Partial
import all Mathlib.Analysis.Calculus.FDeriv.Partial
public import Mathlib.Topology.Algebra.Module.Cardinality
import all Mathlib.Topology.Algebra.Module.Cardinality

@[expose] public section

/-!
# Motion of finite confluent divided differences

This file develops the one-parameter calculus needed for moving finite node
lists.  All formulas are stated for the analytic (confluent) divided
difference, so coincident nodes require no exceptional branch or inverse-gap
bound.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A weighted affine derivative average is `C^n` in its moving right endpoint
when its integrand is `C^n`. -/
theorem contDiff_weightedDerivativeAverage_right (weight n : ℕ) {g : ℝ → E}
    (hg : ContDiff ℝ n g) (a : ℝ) :
    ContDiff ℝ n (weightedDerivativeAverage weight g a) := by
  induction n generalizing weight g with
  | zero =>
      exact contDiff_zero.mpr
        (continuous_weightedDerivativeAverage weight hg.continuous a)
  | succ n ih =>
      change ContDiff ℝ ((n : WithTop ℕ∞) + 1)
        (weightedDerivativeAverage weight g a)
      rw [contDiff_succ_iff_deriv]
      have hdiff : Differentiable ℝ (weightedDerivativeAverage weight g a) := fun b =>
        (hasDerivAt_weightedDerivativeAverage weight
          (fun x => (hg.differentiable (by simp) x).hasDerivAt)
          (hg.continuous_deriv (by simp)) a b).differentiableAt
      refine ⟨hdiff, by simp, ?_⟩
      have hderiv : deriv (weightedDerivativeAverage weight g a) =
          weightedDerivativeAverage (weight + 1) (deriv g) a := by
        funext b
        exact (hasDerivAt_weightedDerivativeAverage weight
          (fun x => (hg.differentiable (by simp) x).hasDerivAt)
          (hg.continuous_deriv (by simp)) a b).deriv
      rw [hderiv]
      exact ih (weight + 1) ((contDiff_succ_iff_deriv.mp hg).2.2)

/-- Anchoring one confluent divided slope consumes exactly one derivative. -/
theorem ContDiff.dslope_right {n : ℕ} {f : ℝ → E}
    (hf : ContDiff ℝ (n + 1) f) (a : ℝ) :
    ContDiff ℝ n (dslope f a) := by
  have hdiff : ∀ x, HasDerivAt f (deriv f x) x := fun x =>
    (hf.differentiable (by simp) x).hasDerivAt
  have hcont : Continuous (deriv f) := hf.continuous_deriv (by simp)
  have havg : weightedDerivativeAverage 0 (deriv f) a = dslope f a := by
    funext b
    exact weightedDerivativeAverage_zero_eq_dslope hdiff hcont a b
  rw [← havg]
  exact contDiff_weightedDerivativeAverage_right 0 n
    ((contDiff_succ_iff_deriv.mp hf).2.2) a

/-- Extended divided slopes are symmetric in their two nodes, including at a
collision. -/
theorem dslope_comm (f : ℝ → E) (a b : ℝ) : dslope f a b = dslope f b a := by
  by_cases hab : a = b
  · subst b
    rfl
  · rw [dslope_of_ne f (Ne.symm hab), dslope_of_ne f hab,
      slope_def_module, slope_def_module]
    rw [show b - a = -(a - b) by ring, inv_neg, neg_smul,
      show f b - f a = -(f a - f b) by abel, smul_neg, neg_neg]

/-- Two anchored divided-slope operators commute on a `C²` function.  The
proof first uses the ordinary distinct-node quotient identity, then extends
across the two possible collisions by continuity. -/
theorem dslope_dslope_comm {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (a b x : ℝ) :
    dslope (dslope f a) b x = dslope (dslope f b) a x := by
  let F : ℝ → ℂ := fun x => dslope (dslope f a) b x
  let G : ℝ → ℂ := fun x => dslope (dslope f b) a x
  have hFa : ContDiff ℝ 1 (dslope f a) :=
    MeyerGeneralProblem.ContDiff.dslope_right hf a
  have hFb : ContDiff ℝ 1 (dslope f b) :=
    MeyerGeneralProblem.ContDiff.dslope_right hf b
  have hFc : Continuous F :=
    (MeyerGeneralProblem.ContDiff.dslope_right hFa b).continuous
  have hGc : Continuous G :=
    (MeyerGeneralProblem.ContDiff.dslope_right hFb a).continuous
  have hEq : Set.EqOn F G ({a, b} : Set ℝ)ᶜ := by
    intro y hy
    have hy' : y ≠ a ∧ y ≠ b := by
      simpa only [Set.mem_compl_iff, Set.mem_insert_iff,
        Set.mem_singleton_iff, not_or] using hy
    have hya : y ≠ a := hy'.1
    have hyb : y ≠ b := hy'.2
    by_cases hab : a = b
    · subst b
      rfl
    · simp only [F, G, dslope_of_ne _ hyb, dslope_of_ne _ hya,
        dslope_of_ne _ hab, dslope_of_ne _ (Ne.symm hab), slope_def_module]
      have hyaC : (y : ℂ) - (a : ℂ) ≠ 0 := by
        exact_mod_cast sub_ne_zero.mpr hya
      have hybC : (y : ℂ) - (b : ℂ) ≠ 0 := by
        exact_mod_cast sub_ne_zero.mpr hyb
      have habC : (a : ℂ) - (b : ℂ) ≠ 0 := by
        exact_mod_cast sub_ne_zero.mpr hab
      rw [Complex.real_smul, Complex.real_smul, Complex.real_smul,
        Complex.real_smul, Complex.real_smul, Complex.real_smul]
      push_cast
      rw [show ((b : ℂ) - (a : ℂ)) = -((a : ℂ) - (b : ℂ)) by ring,
        inv_neg]
      field_simp [hyaC, hybC, habC]
      ring
  have hdense : Dense (({a, b} : Set ℝ)ᶜ) :=
    Set.Countable.dense_compl ℝ (Set.toFinite {a, b}).countable
  have hall : Set.EqOn F G Set.univ := by
    rw [← hdense.closure_eq]
    exact hEq.closure hFc hGc
  exact hall (Set.mem_univ x)

/-- Successively anchor divided slopes at `nodes 0, ..., nodes (order - 1)`.
The remaining real variable is the final divided-difference node. -/
def iteratedAnchoredDslope (nodes : ℕ → ℝ) : ℕ → (ℝ → ℂ) → (ℝ → ℂ)
  | 0, f => f
  | order + 1, f => dslope (iteratedAnchoredDslope nodes order f) (nodes order)

@[simp]
theorem iteratedAnchoredDslope_zero (nodes : ℕ → ℝ) (f : ℝ → ℂ) :
    iteratedAnchoredDslope nodes 0 f = f := rfl

@[simp]
theorem iteratedAnchoredDslope_succ (nodes : ℕ → ℝ) (order : ℕ)
    (f : ℝ → ℂ) :
    iteratedAnchoredDslope nodes (order + 1) f =
      dslope (iteratedAnchoredDslope nodes order f) (nodes order) := rfl

/-- Each anchored divided slope consumes one derivative from a finite smoothness
budget. -/
theorem ContDiff.iteratedAnchoredDslope {anchors regularity : ℕ}
    {f : ℝ → ℂ} (hf : ContDiff ℝ (anchors + regularity) f)
    (nodes : ℕ → ℝ) :
    ContDiff ℝ regularity (iteratedAnchoredDslope nodes anchors f) := by
  induction anchors generalizing f regularity with
  | zero => simpa using hf
  | succ anchors ih =>
      rw [iteratedAnchoredDslope_succ]
      apply MeyerGeneralProblem.ContDiff.dslope_right
      apply ih (regularity := regularity + 1)
      simpa only [Nat.cast_add, Nat.cast_one, add_assoc, add_comm,
        add_left_comm] using hf

/-- Iterated anchored slopes inspect exactly their declared finite prefix. -/
theorem iteratedAnchoredDslope_congr (nodes other : ℕ → ℝ) (order : ℕ)
    (f : ℝ → ℂ) (h : ∀ i < order, nodes i = other i) :
    iteratedAnchoredDslope nodes order f = iteratedAnchoredDslope other order f := by
  induction order with
  | zero => rfl
  | succ order ih =>
      simp only [iteratedAnchoredDslope_succ, h order (by omega)]
      rw [ih (fun i hi => h i (by omega))]

/-- Removing the first analytic node agrees with applying its anchored slope
before all remaining anchors. -/
theorem iteratedAnchoredDslope_shift (nodes : ℕ → ℝ) (order : ℕ)
    (f : ℝ → ℂ) :
    iteratedAnchoredDslope (fun i => nodes (i + 1)) order (dslope f (nodes 0)) =
      iteratedAnchoredDslope nodes (order + 1) f := by
  induction order with
  | zero => rfl
  | succ order ih =>
      simp only [iteratedAnchoredDslope_succ]
      rw [ih]
      rfl

/-- The recursive analytic divided difference is evaluation of the iterated
anchored slope at its last node. -/
theorem analyticDividedDifference_eq_iteratedAnchoredDslope
    (nodes : ℕ → ℝ) (order : ℕ) (f : ℝ → ℂ) :
    analyticDividedDifference nodes order f =
      iteratedAnchoredDslope nodes order f (nodes order) := by
  induction order generalizing nodes f with
  | zero => rfl
  | succ order ih =>
      rw [analyticDividedDifference_succ, ih, iteratedAnchoredDslope_shift]

/-- An initial anchored slope can be commuted through any finite string of
subsequent anchors. -/
theorem iteratedAnchoredDslope_dslope_comm (nodes : ℕ → ℝ) (order : ℕ)
    {f : ℝ → ℂ} (hf : ContDiff ℝ (order + 1) f) (a : ℝ) :
    iteratedAnchoredDslope nodes order (dslope f a) =
      dslope (iteratedAnchoredDslope nodes order f) a := by
  induction order generalizing f with
  | zero => rfl
  | succ order ih =>
      simp only [iteratedAnchoredDslope_succ]
      rw [ih (hf.of_le (by exact_mod_cast Nat.le_succ (order + 1)))]
      funext x
      apply dslope_dslope_comm
      apply MeyerGeneralProblem.ContDiff.iteratedAnchoredDslope
        (anchors := order) (regularity := 2) (nodes := nodes)
      convert hf using 1
      rw [Nat.cast_add, Nat.cast_one]
      have htwo : ((2 : ℕ) : WithTop ℕ∞) = 1 + 1 := by norm_num
      calc
        (order : WithTop ℕ∞) + (2 : ℕ) =
            (order : WithTop ℕ∞) + (1 + 1) :=
          congrArg ((order : WithTop ℕ∞) + ·) htwo
        _ = (order : WithTop ℕ∞) + 1 + 1 := by rw [add_assoc]

/-- Cyclic rotation of a finite `C^(n+1)` confluent divided difference leaves
its value unchanged.  In particular this remains true when nodes collide. -/
theorem analyticDividedDifference_cyclic (nodes : ℕ → ℝ) (order : ℕ)
    {f : ℝ → ℂ} (hf : ContDiff ℝ (order + 1) f) :
    analyticDividedDifference nodes (order + 1) f =
      analyticDividedDifference
        (fun i => if i ≤ order then nodes (i + 1) else nodes 0) (order + 1) f := by
  rw [analyticDividedDifference_succ,
    analyticDividedDifference_eq_iteratedAnchoredDslope]
  rw [iteratedAnchoredDslope_dslope_comm
    (fun i => nodes (i + 1)) order hf (nodes 0)]
  rw [dslope_comm]
  rw [analyticDividedDifference_eq_iteratedAnchoredDslope]
  have hprefix : iteratedAnchoredDslope
      (fun i => if i ≤ order then nodes (i + 1) else nodes 0) order f =
      iteratedAnchoredDslope (fun i => nodes (i + 1)) order f := by
    apply iteratedAnchoredDslope_congr
    intro i hi
    rw [if_pos hi.le]
  simp only [iteratedAnchoredDslope_succ, if_pos (le_refl order),
    if_neg (show ¬order + 1 ≤ order by omega)]
  rw [hprefix]

/-- Replace one indexed node while leaving every other sequence entry fixed. -/
def replaceNodeSequence (nodes : ℕ → ℝ) (r : ℕ) (x : ℝ) : ℕ → ℝ :=
  fun i => if i = r then x else nodes i

/-- Duplicate the `r`-th node, retaining the order of all other indexed
nodes.  This is the collision-safe sequence generated by differentiating in
that node. -/
def duplicateAffineNodeSequence (nodes : ℕ → ℝ) (r : ℕ) : ℕ → ℝ :=
  fun i => if i ≤ r then nodes i else nodes (i - 1)

/-- Analytic divided differences inspect only their declared node prefix. -/
theorem analyticDividedDifference_congr_node_prefix
    (nodes other : ℕ → ℝ) (order : ℕ) (f : ℝ → ℂ)
    (h : ∀ i ≤ order, nodes i = other i) :
    analyticDividedDifference nodes order f =
      analyticDividedDifference other order f := by
  induction order generalizing nodes other f with
  | zero =>
      rw [analyticDividedDifference_zero, analyticDividedDifference_zero,
        h 0 (by omega)]
  | succ order ih =>
      rw [analyticDividedDifference_succ, analyticDividedDifference_succ,
        h 0 (by omega)]
      apply ih
      intro i hi
      exact h (i + 1) (by omega)

/-- Continuous finite node coordinates give a continuous confluent divided
difference, with no separation assumption. -/
theorem continuous_analyticDividedDifference_node_family
    {P : Type*} [TopologicalSpace P] (nodes : P → ℕ → ℝ) (order : ℕ)
    {f : ℝ → ℂ} (hf : ContDiff ℝ order f)
    (hnodes : ∀ i ≤ order, Continuous (fun p => nodes p i)) :
    Continuous (fun p => analyticDividedDifference (nodes p) order f) := by
  let finiteNodes : P → Fin (order + 1) → ℝ := fun p i => nodes p i
  have hfinite : Continuous finiteNodes := continuous_pi (fun i => hnodes i (by omega))
  have h := (continuous_analyticDividedDifference_nodes order hf).comp hfinite
  apply h.congr
  intro p
  apply analyticDividedDifference_congr_node_prefix
  intro i hi
  simp only [finiteNodeSequence, dite_eq_left (show i < order + 1 by omega),
    finiteNodes]

/-- Varying only the terminal node differentiates a divided difference by
duplicating that node. -/
theorem hasDerivAt_analyticDividedDifference_replace_last
    (nodes : ℕ → ℝ) (order : ℕ) {f : ℝ → ℂ}
    (hf : ContDiff ℝ (order + 1) f) (x : ℝ) :
    HasDerivAt
      (fun y => analyticDividedDifference
        (replaceNodeSequence nodes order y) order f)
      (analyticDividedDifference
        (duplicateAffineNodeSequence (replaceNodeSequence nodes order x) order)
        (order + 1) f) x := by
  let G : ℝ → ℂ := iteratedAnchoredDslope nodes order f
  have hG : ContDiff ℝ 1 G := by
    exact MeyerGeneralProblem.ContDiff.iteratedAnchoredDslope hf nodes
  have hfun : (fun y => analyticDividedDifference
        (replaceNodeSequence nodes order y) order f) = G := by
    funext y
    rw [analyticDividedDifference_eq_iteratedAnchoredDslope]
    have hpref : iteratedAnchoredDslope
        (replaceNodeSequence nodes order y) order f = G := by
      dsimp only [G]
      apply iteratedAnchoredDslope_congr
      intro i hi
      rw [replaceNodeSequence, if_neg (by omega)]
    rw [hpref, replaceNodeSequence, if_pos rfl]
  have hcand : analyticDividedDifference
        (duplicateAffineNodeSequence (replaceNodeSequence nodes order x) order)
        (order + 1) f = deriv G x := by
    rw [analyticDividedDifference_eq_iteratedAnchoredDslope,
      iteratedAnchoredDslope_succ]
    have hpref : iteratedAnchoredDslope
        (duplicateAffineNodeSequence (replaceNodeSequence nodes order x) order)
        order f = G := by
      dsimp only [G]
      apply iteratedAnchoredDslope_congr
      intro i hi
      rw [duplicateAffineNodeSequence, if_pos hi.le,
        replaceNodeSequence, if_neg (by omega)]
    rw [hpref]
    simp only [duplicateAffineNodeSequence, replaceNodeSequence,
      if_pos (le_refl order), if_pos rfl,
      if_neg (show ¬order + 1 ≤ order by omega),
      show order + 1 - 1 = order by omega, if_true, dslope_same]
  rw [hfun, hcand]
  exact (hG.differentiable (by norm_num) x).hasDerivAt

/-- Cyclically move the first node of an order-`n+1` prefix to its end. -/
def cycleNodeSequence (nodes : ℕ → ℝ) (order : ℕ) : ℕ → ℝ :=
  fun i => if i ≤ order then nodes (i + 1) else nodes 0

theorem analyticDividedDifference_cycleNodeSequence
    (nodes : ℕ → ℝ) (order : ℕ) {f : ℝ → ℂ}
    (hf : ContDiff ℝ (order + 1) f) :
    analyticDividedDifference nodes (order + 1) f =
      analyticDividedDifference (cycleNodeSequence nodes order) (order + 1) f := by
  change analyticDividedDifference nodes (order + 1) f =
    analyticDividedDifference
      (fun i => if i ≤ order then nodes (i + 1) else nodes 0) (order + 1) f
  exact analyticDividedDifference_cyclic nodes order hf

/-- Varying the first node also differentiates by duplicating that node.  The
proof cyclically places it in the terminal slot and then cyclically restores
the differentiated node list. -/
theorem hasDerivAt_analyticDividedDifference_replace_first
    (nodes : ℕ → ℝ) (order : ℕ) {f : ℝ → ℂ}
    (hf : ContDiff ℝ (order + 2) f) (x : ℝ) :
    HasDerivAt
      (fun y => analyticDividedDifference
        (replaceNodeSequence nodes 0 y) (order + 1) f)
      (analyticDividedDifference
        (duplicateAffineNodeSequence (replaceNodeSequence nodes 0 x) 0)
        (order + 2) f) x := by
  let tail : ℕ → ℝ := fun i => nodes (i + 1)
  have hfun : (fun y => analyticDividedDifference
        (replaceNodeSequence nodes 0 y) (order + 1) f) =
      fun y => analyticDividedDifference
        (replaceNodeSequence tail (order + 1) y) (order + 1) f := by
    funext y
    rw [analyticDividedDifference_cycleNodeSequence _ order
      (hf.of_le (by exact_mod_cast Nat.le_succ (order + 1)))]
    apply analyticDividedDifference_congr_node_prefix
    intro i hi
    by_cases hilast : i = order + 1
    · subst i
      simp only [cycleNodeSequence, if_neg (show ¬order + 1 ≤ order by omega),
        replaceNodeSequence, if_pos rfl, if_true]
    · have hiorder : i ≤ order := by omega
      simp only [cycleNodeSequence, if_pos hiorder, replaceNodeSequence,
        if_neg (show i + 1 ≠ 0 by omega), tail, if_neg hilast]
  have hlast := hasDerivAt_analyticDividedDifference_replace_last
    tail (order + 1) hf x
  let desired := duplicateAffineNodeSequence (replaceNodeSequence nodes 0 x) 0
  let last := duplicateAffineNodeSequence
    (replaceNodeSequence tail (order + 1) x) (order + 1)
  have hcycle1 := analyticDividedDifference_cycleNodeSequence
    desired (order + 1) hf
  have hcycle2 := analyticDividedDifference_cycleNodeSequence
    (cycleNodeSequence desired (order + 1)) (order + 1) hf
  have hdesired : analyticDividedDifference desired (order + 2) f =
      analyticDividedDifference
        (cycleNodeSequence (cycleNodeSequence desired (order + 1)) (order + 1))
        (order + 2) f := hcycle1.trans hcycle2
  have hlastCycle : analyticDividedDifference last (order + 2) f =
      analyticDividedDifference
        (cycleNodeSequence (cycleNodeSequence desired (order + 1)) (order + 1))
        (order + 2) f := by
    apply analyticDividedDifference_congr_node_prefix
    intro i hi
    have hirange : i ≤ order ∨ i = order + 1 ∨ i = order + 2 := by omega
    rcases hirange with hirange | hirange | hirange
    · simp only [last, tail, duplicateAffineNodeSequence,
        if_pos (show i ≤ order + 1 by omega), replaceNodeSequence,
        if_neg (show i ≠ order + 1 by omega), cycleNodeSequence,
        if_pos (show i ≤ order + 1 by omega),
        if_pos (show i + 1 ≤ order + 1 by omega), desired,
        if_neg (show i + 1 + 1 ≤ 0 → False by omega),
        show i + 1 + 1 - 1 = i + 1 by omega,
        if_neg (show i + 1 = 0 → False by omega)]
    · subst i
      simp only [last, tail, duplicateAffineNodeSequence, replaceNodeSequence,
        cycleNodeSequence, desired]
      simp
    · subst i
      simp only [last, tail, duplicateAffineNodeSequence, replaceNodeSequence,
        cycleNodeSequence, desired]
      simp
  have hcand : analyticDividedDifference desired (order + 2) f =
      analyticDividedDifference last (order + 2) f :=
    hdesired.trans hlastCycle.symm
  rw [hfun]
  change HasDerivAt _ (analyticDividedDifference desired (order + 2) f) x
  rw [hcand]
  exact hlast

/-- Affine motion of an infinite node sequence; an order-`n` divided
difference only inspects its first `n+1` entries. -/
def affineNodeSequence (initial velocity : ℕ → ℝ) (t : ℝ) : ℕ → ℝ :=
  fun i => initial i + t * velocity i

/-- The exact finite sum generated by simultaneous affine motion of all nodes
in an order-`n` divided difference. -/
def affineNodeDividedDifferenceDerivative
    (initial velocity : ℕ → ℝ) (t : ℝ) (order : ℕ) (f : ℝ → ℂ) : ℂ :=
  ∑ r : Fin (order + 1),
    (velocity r : ℂ) *
      analyticDividedDifference
        (duplicateAffineNodeSequence (affineNodeSequence initial velocity t) r)
        (order + 1) f

/-- Exact derivative identity for simultaneous affine motion of every node in
a finite analytic divided difference.  Repeated nodes are allowed at every
time. -/
theorem hasDerivAt_analyticDividedDifference_affine_nodes
    (initial velocity : ℕ → ℝ) (order : ℕ) {f : ℝ → ℂ}
    (hf : ContDiff ℝ (order + 1) f) (t : ℝ) :
    HasDerivAt
      (fun s => analyticDividedDifference
        (affineNodeSequence initial velocity s) order f)
      (affineNodeDividedDifferenceDerivative initial velocity t order f) t := by
  induction order generalizing f initial velocity t with
  | zero =>
      have hinner : HasDerivAt
          (fun s => affineNodeSequence initial velocity s 0) (velocity 0) t := by
        change HasDerivAt (fun s => initial 0 + s * velocity 0) (velocity 0) t
        exact (hasDerivAt_mul_const (x := t) (velocity 0)).const_add (initial 0)
      have houter : HasDerivAt f
          (deriv f (affineNodeSequence initial velocity t 0))
          (affineNodeSequence initial velocity t 0) :=
        (hf.differentiable (by norm_num)
          (affineNodeSequence initial velocity t 0)).hasDerivAt
      have hcomp := houter.scomp t hinner
      have hfun : (fun s => analyticDividedDifference
          (affineNodeSequence initial velocity s) 0 f) =
          f ∘ fun s => affineNodeSequence initial velocity s 0 := by
        funext s
        rfl
      have hderiv : affineNodeDividedDifferenceDerivative initial velocity t 0 f =
          velocity 0 • deriv f (affineNodeSequence initial velocity t 0) := by
        simp [affineNodeDividedDifferenceDerivative, Fin.sum_univ_succ,
          analyticDividedDifference_one, duplicateAffineNodeSequence,
          affineNodeSequence, dslope_same, Complex.real_smul]
      rw [hfun, hderiv]
      exact hcomp
  | succ order ih =>
      let full : ℝ → ℕ → ℝ := fun s =>
        affineNodeSequence initial velocity s
      let tailInitial : ℕ → ℝ := fun i => initial (i + 1)
      let tailVelocity : ℕ → ℝ := fun i => velocity (i + 1)
      let Ψ : ℝ → ℝ → ℂ := fun a s =>
        analyticDividedDifference (replaceNodeSequence (full s) 0 a)
          (order + 1) f
      let A : ℝ → ℝ → ℂ := fun a s =>
        analyticDividedDifference
          (duplicateAffineNodeSequence (replaceNodeSequence (full s) 0 a) 0)
          (order + 2) f
      let B : ℝ → ℝ → ℂ := fun a s =>
        ∑ r : Fin (order + 1),
          (tailVelocity r : ℂ) *
            analyticDividedDifference
              (duplicateAffineNodeSequence (replaceNodeSequence (full s) 0 a)
                (r.val + 1)) (order + 2) f
      have hpartialFirst (a s : ℝ) : HasDerivAt (Ψ · s) (A a s) a := by
        exact hasDerivAt_analyticDividedDifference_replace_first
          (full s) order hf a
      have hpartialTail (a s : ℝ) : HasDerivAt (Ψ a) (B a s) s := by
        have hds : ContDiff ℝ (order + 1) (dslope f a) :=
          MeyerGeneralProblem.ContDiff.dslope_right hf a
        have hih := ih tailInitial tailVelocity hds s
        have hfun : Ψ a = fun u => analyticDividedDifference
            (affineNodeSequence tailInitial tailVelocity u) order (dslope f a) := by
          funext u
          dsimp only [Ψ]
          rw [analyticDividedDifference_succ]
          apply analyticDividedDifference_congr_node_prefix
          intro i hi
          simp only [replaceNodeSequence, if_neg (show i + 1 ≠ 0 by omega),
            full, affineNodeSequence, tailInitial, tailVelocity]
        have hderiv : B a s = affineNodeDividedDifferenceDerivative
            tailInitial tailVelocity s order (dslope f a) := by
          dsimp only [B, affineNodeDividedDifferenceDerivative]
          apply Finset.sum_congr rfl
          intro r hr
          congr 1
          rw [analyticDividedDifference_succ]
          apply analyticDividedDifference_congr_node_prefix
          intro i hi
          simp only [duplicateAffineNodeSequence, replaceNodeSequence, full,
            affineNodeSequence, tailInitial, tailVelocity]
          by_cases hir : i ≤ r
          · rw [if_pos hir, if_pos (by omega), if_neg (by omega)]
          · rw [if_neg hir, if_neg (by omega), if_neg (by omega)]
            have hi0 : 0 < i := by omega
            rw [show i + 1 - 1 = i by omega,
              show i - 1 + 1 = i by omega]
        rw [hfun, hderiv]
        exact hih
      have hf2 : ContDiff ℝ (order + 2) f := by
        convert hf using 1
        rw [Nat.cast_add, Nat.cast_one]
        have htwo : ((2 : ℕ) : WithTop ℕ∞) = 1 + 1 := by norm_num
        calc
          (order : WithTop ℕ∞) + (2 : ℕ) =
              (order : WithTop ℕ∞) + (1 + 1) :=
            congrArg ((order : WithTop ℕ∞) + ·) htwo
          _ = (order : WithTop ℕ∞) + 1 + 1 := by rw [add_assoc]
      have hA : Continuous (Function.uncurry A) := by
        apply continuous_analyticDividedDifference_node_family
        · exact hf2
        · intro i hi
          dsimp only [Function.uncurry, A, full, duplicateAffineNodeSequence,
            replaceNodeSequence, affineNodeSequence]
          split_ifs <;> fun_prop
      have hB : Continuous (Function.uncurry B) := by
        apply continuous_finset_sum
        intro r hr
        apply continuous_const.mul
        apply continuous_analyticDividedDifference_node_family
        · exact hf2
        · intro i hi
          dsimp only [Function.uncurry, B, full, duplicateAffineNodeSequence,
            replaceNodeSequence, affineNodeSequence]
          split_ifs <;> fun_prop
      let f₁ : ℝ → ℝ → ℝ →L[ℝ] ℂ := fun a s =>
        ContinuousLinearMap.toSpanSingleton ℝ (A a s)
      let f₂ : ℝ → ℝ → ℝ →L[ℝ] ℂ := fun a s =>
        ContinuousLinearMap.toSpanSingleton ℝ (B a s)
      have hf₁ : Continuous (Function.uncurry f₁) := by
        exact (ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ)
          (E := ℂ)).continuous.comp hA
      have hf₂ : Continuous (Function.uncurry f₂) := by
        exact (ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ)
          (E := ℂ)).continuous.comp hB
      have hΨ : HasStrictFDerivAt (Function.uncurry Ψ)
          ((f₁ (full t 0) t).coprod (f₂ (full t 0) t)) (full t 0, t) := by
        apply hasStrictFDerivAt_uncurry_coprod
          (f := Ψ) (f₁ := f₁) (f₂ := f₂) (u := (full t 0, t))
        · exact Filter.Eventually.of_forall (fun z =>
            (hpartialFirst z.1 z.2).hasFDerivAt)
        · exact Filter.Eventually.of_forall (fun z =>
            (hpartialTail z.1 z.2).hasFDerivAt)
        · exact hf₁.continuousAt
        · exact hf₂.continuousAt
      have hpair : HasFDerivAt (fun s : ℝ => (full s 0, s))
          ((ContinuousLinearMap.toSpanSingleton ℝ (velocity 0)).prod
            (1 : ℝ →L[ℝ] ℝ)) t := by
        apply HasFDerivAt.prodMk
        · have hnode : HasDerivAt (fun s => full s 0) (velocity 0) t := by
            change HasDerivAt (fun s => initial 0 + s * velocity 0)
              (velocity 0) t
            exact (hasDerivAt_mul_const (x := t) (velocity 0)).const_add (initial 0)
          exact hnode.hasFDerivAt
        · exact hasFDerivAt_id t
      let pairPath : ℝ → ℝ × ℝ := fun s => (full s 0, s)
      have hpair' : HasFDerivAt pairPath
          ((ContinuousLinearMap.toSpanSingleton ℝ (velocity 0)).prod
            (1 : ℝ →L[ℝ] ℝ)) t := hpair
      have hcomp := HasFDerivAt.comp (f := pairPath) t hΨ.hasFDerivAt hpair'
      have hfun : (fun s => analyticDividedDifference
          (affineNodeSequence initial velocity s) (order + 1) f) =
          Function.uncurry Ψ ∘ pairPath := by
        funext s
        dsimp only [Function.uncurry, Function.comp_def, pairPath, Ψ, full,
          replaceNodeSequence]
        apply analyticDividedDifference_congr_node_prefix
        intro i hi
        simp only [replaceNodeSequence]
        split_ifs with hzero
        · subst i
          rfl
        · rfl
      have hderiv : affineNodeDividedDifferenceDerivative initial velocity t
          (order + 1) f =
          (((f₁ (full t 0) t).coprod (f₂ (full t 0) t)).comp
            ((ContinuousLinearMap.toSpanSingleton ℝ (velocity 0)).prod
              (1 : ℝ →L[ℝ] ℝ))) 1 := by
        dsimp only [affineNodeDividedDifferenceDerivative]
        rw [Fin.sum_univ_succ]
        have hreplace : replaceNodeSequence (full t) 0 (full t 0) = full t := by
          funext i
          by_cases hi : i = 0
          · subst i
            rfl
          · simp [replaceNodeSequence, hi]
        simp only [f₁, f₂,
          ContinuousLinearMap.comp_apply, ContinuousLinearMap.coprod_apply,
          ContinuousLinearMap.prod_apply, ContinuousLinearMap.toSpanSingleton_apply,
          one_apply_eq_self, one_smul, full, A, B, tailVelocity, hreplace]
        rw [Complex.real_smul]
        congr 1
      rw [hfun, hderiv]
      exact hcomp.hasDerivAt

end

end MeyerGeneralProblem
