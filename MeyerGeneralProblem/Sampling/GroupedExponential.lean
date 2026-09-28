module

public import MeyerGeneralProblem.Interpolation.HermiteGenocchiHigher
public import MeyerGeneralProblem.Gram.UniversalKernel
public import MeyerGeneralProblem.Trace.GroupedTrace
public import MeyerGeneralProblem.Interpolation.UniformNewtonBounds

@[expose] public section

/-!
# Actual grouped exponential divided differences

The grouped exponential functions are analytic Newton divided differences in
the frequency variable, in the repository's positive-`2π` convention.  Their
Hermite–Genocchi representation uses actual derivatives and remains valid
when nodes collide.  Initial-segment order and factorial normalization are
explicit; no lower Riesz inequality is included as an assumption.
-/

namespace MeyerGeneralProblem

open MeasureTheory Set
open scoped ContDiff Interval

noncomputable section

/-- The exact frequency-derivative multiplier of the positive Fourier phase. -/
def gramPhaseFrequencyMultiplier (t : ℝ) : ℂ :=
  ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I

/-- Rewriting the Fourier phase as a complex exponential of a linear map. -/
theorem gramPhase_eq_exp_frequencyMultiplier (s t : ℝ) :
    gramPhase s t = Complex.exp (gramPhaseFrequencyMultiplier t * (s : ℂ)) := by
  unfold gramPhase gramPhaseFrequencyMultiplier
  congr 1
  push_cast
  ring

/-- The actual real derivative of the Fourier phase in its frequency variable. -/
theorem hasDerivAt_gramPhase_frequency (s t : ℝ) :
    HasDerivAt (fun x : ℝ => gramPhase x t)
      (gramPhaseFrequencyMultiplier t * gramPhase s t) s := by
  have h := ((Complex.hasDerivAt_exp (gramPhaseFrequencyMultiplier t * (s : ℂ))).comp
    (s : ℂ) ((hasDerivAt_id (s : ℂ)).const_mul (gramPhaseFrequencyMultiplier t))).comp_ofReal
  simpa only [gramPhase_eq_exp_frequencyMultiplier, Function.comp_def,
    mul_one, mul_comm] using h

/-- Every level of the explicit frequency derivative tower has the next
level as its actual real derivative. -/
theorem hasDerivAt_gramPhase_frequency_tower (k : ℕ) (s t : ℝ) :
    HasDerivAt (fun x : ℝ => gramPhaseFrequencyMultiplier t ^ k * gramPhase x t)
      (gramPhaseFrequencyMultiplier t ^ (k + 1) * gramPhase s t) s := by
  simpa only [pow_succ, mul_assoc] using
    (hasDerivAt_gramPhase_frequency s t).const_mul (gramPhaseFrequencyMultiplier t ^ k)

/-- The explicit derivative tower agrees with iterated real derivatives. -/
theorem iteratedDeriv_gramPhase_frequency (k : ℕ) (t s : ℝ) :
    iteratedDeriv k (fun x : ℝ => gramPhase x t) s =
      gramPhaseFrequencyMultiplier t ^ k * gramPhase s t := by
  induction k generalizing s with
  | zero => simp
  | succ k ih =>
      rw [iteratedDeriv_succ, show iteratedDeriv k (fun x : ℝ => gramPhase x t) =
        (fun x => gramPhaseFrequencyMultiplier t ^ k * gramPhase x t) from funext ih]
      exact (hasDerivAt_gramPhase_frequency_tower k s t).deriv

/-- Actual analytic divided differences of the exponential over an ordered
node prefix of length `order + 1`, permitting collisions. -/
def groupedExponential (nodes : ℕ → ℝ) (order : ℕ) (t : ℝ) : ℂ :=
  analyticDividedDifference nodes order (fun s => gramPhase s t)

/-- The source grouped exponential indexed by an initial segment of a finite
group.  No value past index `j` is used. -/
def groupedExponentialInitial {n : ℕ} (nodes : Fin n → ℝ) (j : Fin n) (t : ℝ) : ℂ :=
  groupedExponential (finiteNodeSequence nodes) j t

/-- The singleton grouped exponential is the original Fourier phase. -/
@[simp]
theorem groupedExponential_zero (nodes : ℕ → ℝ) (t : ℝ) :
    groupedExponential nodes 0 t = gramPhase (nodes 0) t := rfl

/-- The grouped exponential has its genuine all-order Hermite–Genocchi
representation, including repeated and unordered frequency nodes. -/
theorem groupedExponential_eq_hermiteGenocchi
    (nodes : ℕ → ℝ) (order : ℕ) (t : ℝ) :
    groupedExponential nodes order t =
      hermiteGenocchiIntegral nodes order
        (fun s => gramPhaseFrequencyMultiplier t ^ order * gramPhase s t) := by
  have h := analyticDividedDifference_eq_hermiteGenocchi_of_derivativeTower nodes order
    (fun j s => gramPhaseFrequencyMultiplier t ^ j * gramPhase s t)
    (by
      intro j hj
      exact continuous_const.mul
        (continuous_iff_continuousAt.mpr (fun s => (hasDerivAt_gramPhase_frequency s t).continuousAt)))
    (fun j hj s => hasDerivAt_gramPhase_frequency_tower j s t)
  simpa only [pow_zero, one_mul, groupedExponential] using h

/-- At full node collapse the grouped exponential is the exact factorially
normalized frequency jet, not an unnormalized derivative. -/
theorem groupedExponential_repeated_node (s t : ℝ) (order : ℕ) :
    groupedExponential (fun _ => s) order t =
      (1 / (order.factorial : ℝ)) •
        (gramPhaseFrequencyMultiplier t ^ order * gramPhase s t) := by
  rw [groupedExponential_eq_hermiteGenocchi, hermiteGenocchiIntegral_repeated_node]

/-- Grouped exponentials depend jointly continuously on all finite nodes
and on time, including at every collision of frequency nodes. -/
theorem continuous_groupedExponential_nodes_time (order : ℕ) :
    Continuous (fun p : (Fin (order + 1) → ℝ) × ℝ =>
      groupedExponential (finiteNodeSequence p.1) order p.2) := by
  simp only [groupedExponential_eq_hermiteGenocchi]
  apply continuous_hermiteGenocchiIntegral_parametric
  · intro j
    exact (continuous_finiteNodeSequence _ j).comp continuous_fst
  · unfold Function.uncurry gramPhaseFrequencyMultiplier gramPhase
    fun_prop

/-- The derivative multiplier has exactly the expected real magnitude. -/
theorem norm_gramPhaseFrequencyMultiplier (t : ℝ) :
    ‖gramPhaseFrequencyMultiplier t‖ = 2 * Real.pi * |t| := by
  simp [gramPhaseFrequencyMultiplier, abs_of_pos Real.pi_pos]

/-- The exact factorially normalized grouped exponential bound is independent
of all node gaps, including at full collapse. -/
theorem norm_groupedExponential_le
    (nodes : ℕ → ℝ) (order : ℕ) (t : ℝ) {L U : ℝ}
    (hnodes : ∀ j ≤ order, nodes j ∈ Icc L U) :
    ‖groupedExponential nodes order t‖ ≤
      (2 * Real.pi * |t|) ^ order / (order.factorial : ℝ) := by
  rw [groupedExponential_eq_hermiteGenocchi]
  apply norm_hermiteGenocchiIntegral_le nodes order _ hnodes
  intro s hs
  simp only [norm_mul, norm_pow, norm_gramPhase, mul_one, norm_gramPhaseFrequencyMultiplier,
    le_refl]

/-- Every finite initial-segment grouped exponential is continuous in time,
also when nodes repeat. -/
theorem continuous_groupedExponentialInitial {n : ℕ} (nodes : Fin n → ℝ) (j : Fin n) :
    Continuous (groupedExponentialInitial nodes j) := by
  change Continuous (fun t => groupedExponential (finiteNodeSequence nodes) j t)
  simp only [groupedExponential_eq_hermiteGenocchi]
  apply continuous_hermiteGenocchiIntegral_parametric
  · intro k
    exact continuous_const
  · unfold Function.uncurry gramPhaseFrequencyMultiplier gramPhase
    fun_prop

/-- Analytic Newton recursion only inspects its declared node prefix. -/
theorem analyticDividedDifference_congr_nodes
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (nodes other : ℕ → ℝ) (order : ℕ) (f : ℝ → E)
    (h : ∀ j ≤ order, nodes j = other j) :
    analyticDividedDifference nodes order f = analyticDividedDifference other order f := by
  induction order generalizing nodes other f with
  | zero => simp only [analyticDividedDifference_zero, h 0 (by omega)]
  | succ order ih =>
      simp only [analyticDividedDifference_succ, h 0 (by omega)]
      exact ih _ _ _ (fun j hj => h (j + 1) (by omega))

/-- At distinct prefix nodes the analytic divided difference depends only
on the actual point values, without any global regularity assumption. -/
theorem analyticDividedDifference_congr_values_of_distinct
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (nodes : ℕ → ℝ) (order : ℕ) (f g : ℝ → E)
    (hnode : ∀ i ≤ order, ∀ j ≤ order, i ≠ j → nodes i ≠ nodes j)
    (hvalues : ∀ j ≤ order, f (nodes j) = g (nodes j)) :
    analyticDividedDifference nodes order f = analyticDividedDifference nodes order g := by
  induction order generalizing nodes f g with
  | zero => exact hvalues 0 (by omega)
  | succ order ih =>
      apply ih (fun j => nodes (j + 1)) _ _
      · intro i hi j hj hij
        exact hnode (i + 1) (by omega) (j + 1) (by omega) (by omega)
      · intro j hj
        have hne : nodes (j + 1) ≠ nodes 0 := hnode (j + 1) (by omega) 0 (by omega) (by omega)
        rw [dslope_of_ne _ hne, dslope_of_ne _ hne, slope_def_module, slope_def_module,
          hvalues (j + 1) (by omega), hvalues 0 (by omega)]

/-- The actual analytic initial-segment divided difference agrees with the
existing finite values-to-Newton coordinate on distinct real nodes. -/
theorem analyticDividedDifference_eq_dividedDifferences
    {n : ℕ} (nodes : Fin n → ℝ) (hnodes : Function.Injective nodes)
    (f : ℝ → ℂ) (j : Fin n) :
    analyticDividedDifference (finiteNodeSequence nodes) j f =
      dividedDifferences (fun i => (nodes i : ℂ)) (Complex.ofReal_injective.comp hnodes)
        (fun i => f (nodes i)) j := by
  let z : Fin n → ℂ := fun i => (nodes i : ℂ)
  let hz : Function.Injective z := Complex.ofReal_injective.comp hnodes
  let data := dividedDifferences z hz (fun i => f (nodes i))
  let p := newtonInterpolant z data
  have hprefix (k : ℕ) (hk : k ≤ j) :
      finiteNodeSequence nodes k = nodes ⟨k, lt_of_le_of_lt hk j.isLt⟩ := by
    simp only [finiteNodeSequence, dite_eq_left (lt_of_le_of_lt hk j.isLt)]
  have hvalues (i : Fin n) : p.eval (nodes i : ℂ) = f (nodes i) :=
    eval_newtonInterpolantFromValues_at_node z hz (fun i => f (nodes i)) i
  have hcongr := analyticDividedDifference_congr_values_of_distinct
    (finiteNodeSequence nodes) j f (fun x => p.eval (x : ℂ))
    (by
      intro i hi k hk hik
      rw [hprefix i hi, hprefix k hk]
      exact fun he => hik (congrArg Fin.val (hnodes he)))
    (by
      intro k hk
      rw [hprefix k hk]
      exact (hvalues _).symm)
  rw [hcongr, analyticDividedDifference_polynomial_eval]
  have hp := polynomialDividedDifference_newtonInterpolant
    (fun k => (finiteNodeSequence nodes k : ℂ)) data j
  simpa only [finiteNodeSequence_apply, p, z, data, hz] using hp

/-- On distinct nodes the grouped exponential is exactly the source's
initial-segment barycentric combination, with the established grouped weights. -/
theorem groupedExponentialInitial_eq_groupedNewtonWeights
    {n : ℕ} (nodes : Fin n → ℝ) (hnodes : Function.Injective nodes)
    (j : Fin n) (t : ℝ) :
    groupedExponentialInitial nodes j t =
      ∑ i, groupedNewtonWeight (fun k => (nodes k : ℂ)) j i * gramPhase (nodes i) t := by
  rw [groupedExponentialInitial, groupedExponential,
    analyticDividedDifference_eq_dividedDifferences nodes hnodes,
    dividedDifferences_eq_groupedNewtonWeights]

end

end MeyerGeneralProblem
