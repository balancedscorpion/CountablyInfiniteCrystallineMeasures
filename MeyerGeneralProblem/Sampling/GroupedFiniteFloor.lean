module

public import MeyerGeneralProblem.Sampling.GroupedLocalFloor
public import MeyerGeneralProblem.Interpolation.MovingDividedDifferences
public import MeyerGeneralProblem.Interpolation.GroupedSubdata

@[expose] public section

/-!
# Uniform finite-cluster confluent window floors

Actual time derivatives of Hermite–Genocchi integrals give triangular jets
for the grouped exponential basis at time zero, including every frequency
collision. Compact node configurations and actual window energies then
provide a positive finite-cluster floor without inverse internal gaps.
-/

namespace MeyerGeneralProblem

noncomputable section

open MeasureTheory Set Filter Finset Polynomial
open scoped Topology ContDiff

private theorem continuous_weightedAverage_parameter
    (order : ℕ) (g : ℝ → ℝ → ℂ) (hg : Continuous (Function.uncurry g)) (a : ℝ) :
    Continuous (fun p : ℝ × ℝ => weightedDerivativeAverage order (g p.1) a p.2) := by
  have hc : Continuous (fun p : ℝ × ℝ =>
      ∫ u in Icc (0 : ℝ) 1, u ^ order • g p.1 (a + (p.2 - a) * u)) :=
    continuous_parametric_integral_of_continuous (by
      apply (continuous_snd.pow order).smul
      exact hg.comp (show Continuous (fun p : (ℝ × ℝ) × ℝ =>
        (p.1.1, a + (p.1.2 - a) * p.2)) by fun_prop)) isCompact_Icc
  simpa only [weightedDerivativeAverage,
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_Icc_eq_integral_Ioc] using hc

private theorem hasDerivAt_weightedAverage_parameter
    (order : ℕ) (g g' : ℝ → ℝ → ℂ)
    (hg : Continuous (Function.uncurry g)) (hg' : Continuous (Function.uncurry g'))
    (hderiv : ∀ t s, HasDerivAt (fun u => g u s) (g' t s) t) (a b t : ℝ) :
    HasDerivAt (fun u => weightedDerivativeAverage order (g u) a b)
      (weightedDerivativeAverage order (g' t) a b) t := by
  have hcontinuous : Continuous (fun p : ℝ × ℝ =>
      ‖p.2 ^ order • g' p.1 (a + (b - a) * p.2)‖) := by
    apply Continuous.norm
    apply (continuous_snd.pow order).smul
    exact hg'.comp (show Continuous (fun p : ℝ × ℝ =>
      (p.1, a + (b - a) * p.2)) by fun_prop)
  obtain ⟨M, hM⟩ := ((isCompact_Icc : IsCompact (Icc (t - 1) (t + 1))).prod
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1))).bddAbove_image hcontinuous.continuousOn
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun v u : ℝ => u ^ order • g v (a + (b - a) * u))
    (F' := fun v u : ℝ => u ^ order • g' v (a + (b - a) * u))
    (bound := fun _ => M) (μ := volume) (a := (0 : ℝ)) (b := 1)
    (s := Ioo (t - 1) (t + 1)) (x₀ := t)
    (Ioo_mem_nhds (by linarith) (by linarith))
    (Eventually.of_forall (fun v => (show Continuous
      (fun u : ℝ => u ^ order • g v (a + (b - a) * u)) from
      (continuous_id.pow order).smul (hg.comp
        (show Continuous (fun u : ℝ => (v, a + (b - a) * u)) by fun_prop))).aestronglyMeasurable))
    ((show Continuous (fun u : ℝ => u ^ order • g t (a + (b - a) * u)) from
      (continuous_id.pow order).smul (hg.comp
        (show Continuous (fun u : ℝ => (t, a + (b - a) * u)) by fun_prop))).intervalIntegrable _ _)
    ((show Continuous (fun u : ℝ => u ^ order • g' t (a + (b - a) * u)) from
      (continuous_id.pow order).smul (hg'.comp
        (show Continuous (fun u : ℝ => (t, a + (b - a) * u)) by fun_prop))).aestronglyMeasurable)
    (Eventually.of_forall (by
      intro u hu v hv
      have hu' : u ∈ Ioc (0 : ℝ) 1 := by simpa using hu
      exact hM (mem_image_of_mem _ (show (v, u) ∈
        Icc (t - 1) (t + 1) ×ˢ Icc (0 : ℝ) 1 from
          ⟨⟨hv.1.le, hv.2.le⟩, hu'.1.le, hu'.2⟩))))
    intervalIntegrable_const
    (Eventually.of_forall (by
      intro u _ v _
      simpa only [Pi.smul_def] using (hderiv v (a + (b - a) * u)).const_smul (u ^ order)))).2

/-- Actual differentiation in an external real parameter commutes with the
HG integral. Compact domination is proved from joint continuity, not assumed. -/
theorem hasDerivAt_hermiteGenocchiIntegral_parameter
    (nodes : ℕ → ℝ) (order : ℕ) (g g' : ℝ → ℝ → ℂ)
    (hg : Continuous (Function.uncurry g)) (hg' : Continuous (Function.uncurry g'))
    (hderiv : ∀ t s, HasDerivAt (fun u => g u s) (g' t s) t) (t : ℝ) :
    HasDerivAt (fun u => hermiteGenocchiIntegral nodes order (g u))
      (hermiteGenocchiIntegral nodes order (g' t)) t := by
  induction order generalizing nodes g g' with
  | zero => exact hderiv t (nodes 0)
  | succ order ih =>
      exact ih (fun i => nodes (i + 1))
        (fun u => weightedDerivativeAverage order (g u) (nodes 0))
        (fun u => weightedDerivativeAverage order (g' u) (nodes 0))
        (continuous_weightedAverage_parameter order g hg (nodes 0))
        (continuous_weightedAverage_parameter order g' hg' (nodes 0))
        (fun u b => hasDerivAt_weightedAverage_parameter order g g' hg hg' hderiv (nodes 0) b u)

/-- Complex scalar multiplication commutes with the actual HG integral. -/
theorem hermiteGenocchiIntegral_const_mul (nodes : ℕ → ℝ) (order : ℕ)
    (z : ℂ) (g : ℝ → ℂ) :
    hermiteGenocchiIntegral nodes order (fun s => z * g s) =
      z * hermiteGenocchiIntegral nodes order g := by
  induction order generalizing nodes g with
  | zero => rfl
  | succ order ih =>
      have havg (a b : ℝ) : weightedDerivativeAverage order (fun s => z * g s) a b =
          z * weightedDerivativeAverage order g a b := by
        simp only [weightedDerivativeAverage, Complex.real_smul]
        simp_rw [show ∀ u : ℝ, (↑(u ^ order) : ℂ) * (z * g (a + (b - a) * u)) =
          z * ((↑(u ^ order) : ℂ) * g (a + (b - a) * u)) by intro u; ring]
        exact intervalIntegral.integral_const_mul _ _
      simp only [hermiteGenocchiIntegral_succ]
      rw [show weightedDerivativeAverage order (fun s => z * g s) (nodes 0) =
        (fun b => z * weightedDerivativeAverage order g (nodes 0) b) from funext (havg _)]
      exact ih _ _

/-- A constant HG integrand has the exact factorial mass at arbitrary nodes. -/
theorem hermiteGenocchiIntegral_const (nodes : ℕ → ℝ) (order : ℕ) (z : ℂ) :
    hermiteGenocchiIntegral nodes order (fun _ => z) =
      (1 / (order.factorial : ℝ)) • z := by
  induction order generalizing nodes z with
  | zero => simp
  | succ order ih =>
      have havg : weightedDerivativeAverage order (fun _ : ℝ => z) (nodes 0) =
          fun _ : ℝ => (1 / (order + 1 : ℕ) : ℝ) • z := by
        funext b
        exact weightedDerivativeAverage_same order (fun _ : ℝ => z) 0
      rw [hermiteGenocchiIntegral_succ, havg, ih, smul_smul]
      congr 1
      simp [Nat.factorial_succ, Nat.cast_mul, div_eq_mul_inv, mul_comm]

/-- The genuine HG average of the unweighted Fourier phase. -/
def groupedPhaseAverage (nodes : ℕ → ℝ) (order : ℕ) (t : ℝ) : ℂ :=
  hermiteGenocchiIntegral nodes order (fun s => gramPhase s t)

/-- Every derivative of the phase average is obtained by differentiating
the actual phase under the HG integral. -/
theorem iteratedDeriv_groupedPhaseAverage (nodes : ℕ → ℝ) (order k : ℕ) (t : ℝ) :
    iteratedDeriv k (groupedPhaseAverage nodes order) t =
      hermiteGenocchiIntegral nodes order
        (fun s => gramPhaseFrequencyMultiplier s ^ k * gramPhase s t) := by
  induction k generalizing t with
  | zero => simp [groupedPhaseAverage]
  | succ k ih =>
      rw [iteratedDeriv_succ, show iteratedDeriv k (groupedPhaseAverage nodes order) =
        (fun t => hermiteGenocchiIntegral nodes order
          (fun s => gramPhaseFrequencyMultiplier s ^ k * gramPhase s t)) from funext ih]
      apply HasDerivAt.deriv
      apply hasDerivAt_hermiteGenocchiIntegral_parameter nodes order
        (fun u s => gramPhaseFrequencyMultiplier s ^ k * gramPhase s u)
        (fun u s => gramPhaseFrequencyMultiplier s ^ (k + 1) * gramPhase s u)
      · unfold Function.uncurry gramPhaseFrequencyMultiplier gramPhase
        fun_prop
      · unfold Function.uncurry gramPhaseFrequencyMultiplier gramPhase
        fun_prop
      · intro u s
        simpa only [pow_succ, mul_assoc] using
          (hasDerivAt_gramPhase_time s u).const_mul (gramPhaseFrequencyMultiplier s ^ k)

/-- The phase average is genuinely smooth in time at every finite node
configuration, including all collisions. -/
theorem contDiff_groupedPhaseAverage (nodes : ℕ → ℝ) (order : ℕ) :
    ContDiff ℝ ∞ (groupedPhaseAverage nodes order) := by
  apply contDiff_of_differentiable_iteratedDeriv
  intro k _ t
  rw [show iteratedDeriv k (groupedPhaseAverage nodes order) =
    (fun t => hermiteGenocchiIntegral nodes order
      (fun s => gramPhaseFrequencyMultiplier s ^ k * gramPhase s t)) from
        funext (iteratedDeriv_groupedPhaseAverage nodes order k)]
  apply HasDerivAt.differentiableAt
  apply hasDerivAt_hermiteGenocchiIntegral_parameter nodes order
    (fun u s => gramPhaseFrequencyMultiplier s ^ k * gramPhase s u)
    (fun u s => gramPhaseFrequencyMultiplier s ^ (k + 1) * gramPhase s u)
  · unfold Function.uncurry gramPhaseFrequencyMultiplier gramPhase
    fun_prop
  · unfold Function.uncurry gramPhaseFrequencyMultiplier gramPhase
    fun_prop
  · intro u s
    simpa only [pow_succ, mul_assoc] using
      (hasDerivAt_gramPhase_time s u).const_mul (gramPhaseFrequencyMultiplier s ^ k)

/-- The phase average has the exact factorial value at time zero. -/
theorem groupedPhaseAverage_zero (nodes : ℕ → ℝ) (order : ℕ) :
    groupedPhaseAverage nodes order 0 = ((1 / (order.factorial : ℝ) : ℝ) : ℂ) := by
  simp only [groupedPhaseAverage, gramPhase_zero_right, hermiteGenocchiIntegral_const,
    Complex.real_smul, mul_one]

/-- The true grouped exponential factors by its exact vanishing power in
time and a genuinely smooth HG average with known nonzero value at zero. -/
theorem groupedExponential_eq_timePower (nodes : ℕ → ℝ) (order : ℕ) (t : ℝ) :
    groupedExponential nodes order t =
      t ^ order • (gramPhaseFrequencyMultiplier 1 ^ order * groupedPhaseAverage nodes order t) := by
  rw [groupedExponential_eq_hermiteGenocchi, hermiteGenocchiIntegral_const_mul]
  have hmult : gramPhaseFrequencyMultiplier t =
      (t : ℂ) * gramPhaseFrequencyMultiplier 1 := by
    unfold gramPhaseFrequencyMultiplier
    push_cast
    ring
  rw [hmult, mul_pow]
  simp only [Complex.real_smul, Complex.ofReal_pow, groupedPhaseAverage, mul_assoc]

/-- The actual grouped exponential is smooth in time at every finite node
configuration, not merely continuous in its confluent parameters. -/
theorem contDiff_groupedExponential (nodes : ℕ → ℝ) (order : ℕ) :
    ContDiff ℝ ∞ (groupedExponential nodes order) := by
  have hfun : groupedExponential nodes order = fun t : ℝ =>
      (t : ℂ) ^ order * (gramPhaseFrequencyMultiplier 1 ^ order *
        groupedPhaseAverage nodes order t) := by
    funext t
    simp only [groupedExponential_eq_timePower, Complex.real_smul, Complex.ofReal_pow]
  rw [hfun]
  exact (show ContDiff ℝ ∞ (fun t : ℝ => (t : ℂ) ^ order) from
    Complex.ofRealCLM.contDiff.pow order).mul
    (contDiff_const.mul (contDiff_groupedPhaseAverage nodes order))

private theorem iteratedDeriv_ofReal_pow_zero (k j : ℕ) :
    iteratedDeriv k (fun t : ℝ => (t : ℂ) ^ j) 0 =
      if k = j then (j.factorial : ℂ) else 0 := by
  have hfun : (fun t : ℝ => (Polynomial.X ^ j : ℂ[X]).eval (t : ℂ)) =
      fun t : ℝ => (t : ℂ) ^ j := by funext t; simp
  rw [← hfun]
  rw [iteratedDeriv_polynomial_eval_ofReal]
  simp only [Complex.ofReal_zero]
  rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_iterate_derivative]
  simp only [zero_add, Polynomial.coeff_X_pow]
  by_cases h : k = j
  · subst k
    simp [Nat.descFactorial_self]
  · simp [h]

/-- Every time derivative below the initial-segment order vanishes at zero.
This is actual derivative triangularity, valid at partial or full collisions. -/
theorem iteratedDeriv_groupedExponential_zero_of_lt (nodes : ℕ → ℝ) {k j : ℕ}
    (hkj : k < j) : iteratedDeriv k (groupedExponential nodes j) 0 = 0 := by
  have hfun : groupedExponential nodes j = fun t : ℝ =>
      (t : ℂ) ^ j * (gramPhaseFrequencyMultiplier 1 ^ j * groupedPhaseAverage nodes j t) := by
    funext t
    simp only [groupedExponential_eq_timePower, Complex.real_smul, Complex.ofReal_pow]
  have hp : ContDiffAt ℝ k (fun t : ℝ => (t : ℂ) ^ j) 0 :=
    (Complex.ofRealCLM.contDiff.pow j).contDiffAt
  have ha : ContDiffAt ℝ k (fun t : ℝ => gramPhaseFrequencyMultiplier 1 ^ j *
      groupedPhaseAverage nodes j t) 0 :=
    ((show ContDiff ℝ ∞ (fun t : ℝ => gramPhaseFrequencyMultiplier 1 ^ j *
      groupedPhaseAverage nodes j t) from contDiff_const.mul (contDiff_groupedPhaseAverage nodes j)).of_le
        (show (k : ℕ∞ω) ≤ ∞ by simp)).contDiffAt
  rw [hfun, iteratedDeriv_fun_mul hp ha]
  apply sum_eq_zero
  intro i hi
  have hij : i ≠ j := by have := mem_range.mp hi; omega
  simp only [iteratedDeriv_ofReal_pow_zero, ite_eq_right hij, mul_zero, zero_mul]

/-- The diagonal time jet is exactly `(2πi)^j`, with factorial cancellation
proved from the HG mass. It is independent of every frequency node. -/
theorem iteratedDeriv_groupedExponential_diagonal (nodes : ℕ → ℝ) (j : ℕ) :
    iteratedDeriv j (groupedExponential nodes j) 0 = gramPhaseFrequencyMultiplier 1 ^ j := by
  have hfun : groupedExponential nodes j = fun t : ℝ =>
      (t : ℂ) ^ j * (gramPhaseFrequencyMultiplier 1 ^ j * groupedPhaseAverage nodes j t) := by
    funext t
    simp only [groupedExponential_eq_timePower, Complex.real_smul, Complex.ofReal_pow]
  have hp : ContDiffAt ℝ j (fun t : ℝ => (t : ℂ) ^ j) 0 :=
    (Complex.ofRealCLM.contDiff.pow j).contDiffAt
  have ha : ContDiffAt ℝ j (fun t : ℝ => gramPhaseFrequencyMultiplier 1 ^ j *
      groupedPhaseAverage nodes j t) 0 :=
    ((show ContDiff ℝ ∞ (fun t : ℝ => gramPhaseFrequencyMultiplier 1 ^ j *
      groupedPhaseAverage nodes j t) from contDiff_const.mul (contDiff_groupedPhaseAverage nodes j)).of_le
        (show (j : ℕ∞ω) ≤ ∞ by simp)).contDiffAt
  rw [hfun, iteratedDeriv_fun_mul hp ha]
  rw [sum_eq_single j]
  · simp only [Nat.choose_self, Nat.cast_one, one_mul, iteratedDeriv_ofReal_pow_zero,
      ite_true, Nat.sub_self, iteratedDeriv_zero, groupedPhaseAverage_zero,
      Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_natCast]
    have hf : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
    field_simp
  · intro i hi hij
    simp only [iteratedDeriv_ofReal_pow_zero, ite_eq_right hij, mul_zero, zero_mul]
  · simp

/-- Every finite initial-segment basis is jointly continuous in its full
node list and time, including prefixes inside a longer confluent list. -/
theorem continuous_groupedExponentialInitial_nodes_time {r : ℕ} (j : Fin r) :
    Continuous (fun p : (Fin r → ℝ) × ℝ => groupedExponentialInitial p.1 j p.2) := by
  simp only [groupedExponentialInitial, groupedExponential_eq_hermiteGenocchi]
  apply continuous_hermiteGenocchiIntegral_parametric
  · intro i
    exact (continuous_finiteNodeSequence r i).comp continuous_fst
  · unfold Function.uncurry gramPhaseFrequencyMultiplier gramPhase
    fun_prop

private theorem dslope_const_mul_complex (z : ℂ) (f : ℝ → ℂ) (a b : ℝ) :
    dslope (fun s => z * f s) a b = z * dslope f a b := by
  by_cases hab : b = a
  · subst b
    rw [dslope_same, dslope_same, deriv_const_mul_field]
  · rw [dslope_of_ne _ hab, dslope_of_ne _ hab, slope_def_module, slope_def_module]
    simp only [Complex.real_smul]
    ring

/-- Constant complex multiplication commutes with actual analytic divided
differences, including their derivative branches at repeated nodes. -/
theorem analyticDividedDifference_const_mul_complex (nodes : ℕ → ℝ) (order : ℕ)
    (z : ℂ) (f : ℝ → ℂ) :
    analyticDividedDifference nodes order (fun s => z * f s) =
      z * analyticDividedDifference nodes order f := by
  induction order generalizing nodes f with
  | zero => rfl
  | succ order ih =>
      simp only [analyticDividedDifference_succ]
      rw [show dslope (fun s => z * f s) (nodes 0) =
        (fun b => z * dslope f (nodes 0) b) from
          funext (dslope_const_mul_complex z f (nodes 0))]
      exact ih _ _

/-- Translation of every frequency node multiplies every true grouped
basis vector by the same unit-modulus anchor phase. -/
theorem groupedExponentialInitial_anchor {r : ℕ} (nodes : Fin r → ℝ)
    (j : Fin r) (anchor t : ℝ) :
    groupedExponentialInitial (fun i => nodes i + anchor) j t =
      gramPhase anchor t * groupedExponentialInitial nodes j t := by
  unfold groupedExponentialInitial groupedExponential
  rw [← analyticDividedDifference_finite_comp_add_const nodes j (fun s => gramPhase s t) anchor]
  simp_rw [gramPhase_add]
  rw [show (fun s => gramPhase s t * gramPhase anchor t) =
    (fun s => gramPhase anchor t * gramPhase s t) from funext (fun _ => mul_comm _ _)]
  exact analyticDividedDifference_const_mul_complex _ _ _ _

/-- Actual finite grouped exponential synthesis in initial-segment order. -/
def finiteGroupedAmplitude {r : ℕ} (nodes : Fin r → ℝ) (c : Fin r → ℂ) (t : ℝ) : ℂ :=
  ∑ j, c j * groupedExponentialInitial nodes j t

/-- Genuine synthesis is jointly continuous in nodes, coefficients, and time. -/
theorem continuous_finiteGroupedAmplitude {r : ℕ} :
    Continuous (fun p : ((Fin r → ℝ) × (Fin r → ℂ)) × ℝ =>
      finiteGroupedAmplitude p.1.1 p.1.2 p.2) := by
  apply continuous_finsetSum
  intro j _
  exact ((continuous_apply j).comp continuous_fst.snd).mul
    ((continuous_groupedExponentialInitial_nodes_time j).comp
      (show Continuous (fun p : ((Fin r → ℝ) × (Fin r → ℂ)) × ℝ =>
        (p.1.1, p.2)) by fun_prop))

/-- Actual triangular time jets force every coefficient of a synthesis
vanishing on a positive window to vanish. No node ordering or gap is required. -/
theorem finiteGroupedAmplitude_coeff_eq_zero {r : ℕ} {W : ℝ} (hW : 0 < W)
    (nodes : Fin r → ℝ) (c : Fin r → ℂ)
    (hzero : ∀ t ∈ Icc (-W) W, finiteGroupedAmplitude nodes c t = 0) : c = 0 := by
  have heq : finiteGroupedAmplitude nodes c =ᶠ[𝓝 0] (fun _ => (0 : ℂ)) := by
    filter_upwards [Ioo_mem_nhds (show -W < 0 by linarith) hW] with t ht
    exact hzero t ⟨ht.1.le, ht.2.le⟩
  have hjets (k : ℕ) :
      ∑ j, c j * iteratedDeriv k (groupedExponentialInitial nodes j) 0 = 0 := by
    have h := heq.iteratedDeriv_eq k
    simp only [iteratedDeriv_const, ite_self] at h
    change iteratedDeriv k (fun t => ∑ j, c j * groupedExponentialInitial nodes j t) 0 = 0 at h
    have hsmooth (j : Fin r) (_ : j ∈ (univ : Finset (Fin r))) :
        ContDiffAt ℝ k (fun t => c j * groupedExponentialInitial nodes j t) 0 :=
      ((show ContDiff ℝ ∞ (fun t => c j * groupedExponentialInitial nodes j t) from
        contDiff_const.mul (contDiff_groupedExponential (finiteNodeSequence nodes) j)).of_le
          (show (k : ℕ∞ω) ≤ ∞ by simp)).contDiffAt
    rw [iteratedDeriv_fun_sum hsmooth] at h
    simpa only [iteratedDeriv_const_mul_field] using h
  have hβ : gramPhaseFrequencyMultiplier 1 ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [norm_gramPhaseFrequencyMultiplier]
    positivity
  have hcoeff (k : ℕ) : ∀ hk : k < r, c ⟨k, hk⟩ = 0 := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk
      have hsum : (∑ j, c j * iteratedDeriv k (groupedExponentialInitial nodes j) 0) =
          c ⟨k, hk⟩ * gramPhaseFrequencyMultiplier 1 ^ k := by
        rw [sum_eq_single (⟨k, hk⟩ : Fin r)]
        · change c ⟨k, hk⟩ * iteratedDeriv k (groupedExponential (finiteNodeSequence nodes) k) 0 = _
          rw [iteratedDeriv_groupedExponential_diagonal]
        · intro j _ hj
          by_cases hjk : j.val < k
          · rw [ih j.val hjk j.isLt, zero_mul]
          · have hkj : k < j.val := by
              have hne : j.val ≠ k := fun he => hj (Fin.ext he)
              omega
            change c j * iteratedDeriv k (groupedExponential (finiteNodeSequence nodes) j.val) 0 = 0
            rw [iteratedDeriv_groupedExponential_zero_of_lt _ hkj, mul_zero]
        · simp
      exact (mul_eq_zero.mp (hsum.symm.trans (hjets k))).resolve_right (pow_ne_zero _ hβ)
  funext j
  exact hcoeff j.val j.isLt

/-- Nonzero finite coefficients have nonzero actual synthesis somewhere in
every positive window, including all confluent configurations. -/
theorem exists_finiteGroupedAmplitude_ne_zero {r : ℕ} {W : ℝ} (hW : 0 < W)
    (nodes : Fin r → ℝ) (c : Fin r → ℂ) (hc : c ≠ 0) :
    ∃ t ∈ Icc (-W) W, finiteGroupedAmplitude nodes c t ≠ 0 := by
  by_contra h
  push Not at h
  exact hc (finiteGroupedAmplitude_coeff_eq_zero hW nodes c h)

/-- The actual finite-cluster Lebesgue window energy. -/
def finiteGroupedWindowEnergy {r : ℕ} (W : ℝ) (nodes : Fin r → ℝ) (c : Fin r → ℂ) : ℝ :=
  ∫ t in Icc (-W) W, ‖finiteGroupedAmplitude nodes c t‖ ^ 2

/-- Continuity of the true finite-cluster window energy. -/
theorem continuous_finiteGroupedWindowEnergy (r : ℕ) (W : ℝ) :
    Continuous (fun p : (Fin r → ℝ) × (Fin r → ℂ) => finiteGroupedWindowEnergy W p.1 p.2) := by
  exact continuous_parametric_integral_of_continuous
    (continuous_finiteGroupedAmplitude.norm.pow 2) isCompact_Icc

/-- Actual triangular independence makes the continuous energy strictly
positive for every nonzero coefficient vector. -/
theorem finiteGroupedWindowEnergy_pos {r : ℕ} {W : ℝ} (hW : 0 < W)
    (nodes : Fin r → ℝ) (c : Fin r → ℂ) (hc : c ≠ 0) :
    0 < finiteGroupedWindowEnergy W nodes c := by
  have hcontinuous : Continuous (finiteGroupedAmplitude nodes c) :=
    continuous_finiteGroupedAmplitude.comp
      (show Continuous (fun t : ℝ => ((nodes, c), t)) by fun_prop)
  obtain ⟨t, ht, hne⟩ := exists_finiteGroupedAmplitude_ne_zero hW nodes c hc
  have hpos := intervalIntegral.integral_pos (show -W < W by linarith)
    (hcontinuous.norm.pow 2).continuousOn (fun t _ => sq_nonneg _)
    ⟨t, ht, sq_pos_of_pos (norm_pos_iff.mpr hne)⟩
  simpa only [Pi.pow_apply, finiteGroupedWindowEnergy,
    intervalIntegral.integral_of_le (show -W ≤ W by linarith),
    integral_Icc_eq_integral_Ioc] using hpos

/-- Exact complex homogeneity of finite grouped synthesis. -/
theorem finiteGroupedAmplitude_smul {r : ℕ} (nodes : Fin r → ℝ) (c : Fin r → ℂ)
    (z : ℂ) (t : ℝ) :
    finiteGroupedAmplitude nodes (z • c) t = z * finiteGroupedAmplitude nodes c t := by
  simp only [finiteGroupedAmplitude, Pi.smul_apply, smul_eq_mul, mul_sum, mul_assoc]

/-- Exact quadratic homogeneity of the true finite-cluster window energy. -/
theorem finiteGroupedWindowEnergy_smul {r : ℕ} (W : ℝ) (nodes : Fin r → ℝ)
    (c : Fin r → ℂ) (z : ℂ) :
    finiteGroupedWindowEnergy W nodes (z • c) = ‖z‖ ^ 2 * finiteGroupedWindowEnergy W nodes c := by
  simp only [finiteGroupedWindowEnergy, finiteGroupedAmplitude_smul, norm_mul, mul_pow]
  exact integral_const_mul _ _

/-- Translation of the entire frequency cluster multiplies its synthesis
by one common Fourier phase, including every confluent initial segment. -/
theorem finiteGroupedAmplitude_anchor {r : ℕ} (nodes : Fin r → ℝ) (c : Fin r → ℂ)
    (anchor t : ℝ) :
    finiteGroupedAmplitude (fun i => nodes i + anchor) c t =
      gramPhase anchor t * finiteGroupedAmplitude nodes c t := by
  simp only [finiteGroupedAmplitude, groupedExponentialInitial_anchor, mul_sum]
  apply sum_congr rfl
  intro j _
  ring

/-- The exact energy is invariant under arbitrary frequency translation. -/
theorem finiteGroupedWindowEnergy_anchor {r : ℕ} (W : ℝ) (nodes : Fin r → ℝ)
    (c : Fin r → ℂ) (anchor : ℝ) :
    finiteGroupedWindowEnergy W (fun i => nodes i + anchor) c =
      finiteGroupedWindowEnergy W nodes c := by
  simp only [finiteGroupedWindowEnergy, finiteGroupedAmplitude_anchor, norm_mul,
    norm_gramPhase, one_mul]

/-- For fixed cluster size, compactness of the actual node cube and the
coefficient unit sphere gives a positive floor, including all collisions. -/
theorem exists_fixedSizeGroupedWindowEnergy_floor (r : ℕ) {W D : ℝ}
    (hW : 0 < W) (_hD : 0 ≤ D) :
    ∃ A : ℝ, 0 < A ∧ ∀ nodes : Fin r → ℝ, ‖nodes‖ ≤ D → ∀ c : Fin r → ℂ,
      A * ‖c‖ ^ 2 ≤ finiteGroupedWindowEnergy W nodes c := by
  have hcompact : IsCompact
      (Metric.closedBall (0 : Fin r → ℝ) D ×ˢ Metric.sphere (0 : Fin r → ℂ) 1) :=
    (isCompact_closedBall 0 D).prod (isCompact_sphere 0 1)
  obtain ⟨A, hA, hbound⟩ := hcompact.exists_forall_le'
    (continuous_finiteGroupedWindowEnergy r W).continuousOn (a := (0 : ℝ)) (by
      rintro ⟨nodes, c⟩ ⟨hnodes, hc⟩
      apply finiteGroupedWindowEnergy_pos hW nodes c
      intro hz
      simp [hz] at hc)
  refine ⟨A, hA, ?_⟩
  intro nodes hnodes c
  by_cases hc : c = 0
  · simp [hc, finiteGroupedWindowEnergy, finiteGroupedAmplitude]
  have hnorm : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hunit : ((‖c‖⁻¹ : ℝ) : ℂ) • c ∈ Metric.sphere (0 : Fin r → ℂ) 1 := by
    simp only [Metric.mem_sphere, dist_zero_right, norm_smul, Complex.norm_real,
      Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg c)]
    exact inv_mul_cancel₀ hnorm.ne'
  have hn : nodes ∈ Metric.closedBall (0 : Fin r → ℝ) D := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hnodes
  have h := hbound (nodes, ((‖c‖⁻¹ : ℝ) : ℂ) • c) ⟨hn, hunit⟩
  rw [finiteGroupedWindowEnergy_smul] at h
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_inv,
    abs_of_nonneg (norm_nonneg c), inv_pow] at h
  apply (le_div_iff₀ (sq_pos_of_pos hnorm)).mp
  simpa only [div_eq_mul_inv, mul_comm] using h

/-- A single positive norm floor works for every size at most `q`, by a
finite minimum of the proved actual fixed-size floors. -/
theorem exists_boundedSizeGroupedWindowEnergy_floor (q : ℕ) {W D : ℝ}
    (hW : 0 < W) (hD : 0 ≤ D) :
    ∃ A : ℝ, 0 < A ∧ ∀ r : ℕ, r ≤ q → ∀ nodes : Fin r → ℝ,
      ‖nodes‖ ≤ D → ∀ c : Fin r → ℂ,
        A * ‖c‖ ^ 2 ≤ finiteGroupedWindowEnergy W nodes c := by
  have hlocal (r : Fin (q + 1)) := exists_fixedSizeGroupedWindowEnergy_floor r.val hW hD
  choose C hC hbound using hlocal
  obtain ⟨A, hA, hsmall⟩ := (isCompact_univ : IsCompact (univ : Set (Fin (q + 1)))).exists_forall_le'
    (show ContinuousOn C univ from continuous_of_discreteTopology.continuousOn)
    (a := (0 : ℝ)) (fun r _ => hC r)
  refine ⟨A, hA, ?_⟩
  intro r hr nodes hnodes c
  let ri : Fin (q + 1) := ⟨r, by omega⟩
  exact (mul_le_mul_of_nonneg_right (hsmall ri (mem_univ ri)) (sq_nonneg ‖c‖)).trans
    (hbound ri nodes hnodes c)

/-- The exact sum of coefficient squares is bounded by the cluster size
times the squared supremum norm; no coefficient is discarded. -/
theorem finiteGrouped_coefficientEnergy_le {r : ℕ} (c : Fin r → ℂ) :
    ∑ j, ‖c j‖ ^ 2 ≤ (r : ℝ) * ‖c‖ ^ 2 := by
  calc
    ∑ j, ‖c j‖ ^ 2 ≤ ∑ _ : Fin r, ‖c‖ ^ 2 := by
      apply sum_le_sum
      intro j _
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm c j) 2
    _ = (r : ℝ) * ‖c‖ ^ 2 := by simp

/-- One positive actual `L²` floor works for every cluster size at most `q`,
every anchor, and every radius-`D` node list, including unordered and repeated
nodes. The coefficient norm is the full sum of squared magnitudes. -/
theorem exists_groupedFiniteExponential_localFloor (q : ℕ) {W D : ℝ}
    (hW : 0 < W) (hD : 0 ≤ D) :
    ∃ A : ℝ, 0 < A ∧ ∀ r : ℕ, r ≤ q → ∀ anchor : ℝ,
      ∀ nodes : Fin r → ℝ, (∀ j, |nodes j - anchor| ≤ D) → ∀ c : Fin r → ℂ,
        A * (∑ j, ‖c j‖ ^ 2) ≤
          ∫ t in Icc (-W) W, ‖∑ j, c j * groupedExponentialInitial nodes j t‖ ^ 2 := by
  obtain ⟨A, hA, hbound⟩ := exists_boundedSizeGroupedWindowEnergy_floor q hW hD
  have hq : (0 : ℝ) < (q : ℝ) + 1 := by positivity
  refine ⟨A / ((q : ℝ) + 1), div_pos hA hq, ?_⟩
  intro r hr anchor nodes hnodes c
  let centred : Fin r → ℝ := fun j => nodes j - anchor
  have hcentred : ‖centred‖ ≤ D := (pi_norm_le_iff_of_nonneg hD).mpr (by
    intro j
    simpa only [centred, Real.norm_eq_abs] using hnodes j)
  have heq : finiteGroupedWindowEnergy W centred c = finiteGroupedWindowEnergy W nodes c := by
    have h := finiteGroupedWindowEnergy_anchor W centred c anchor
    simpa only [centred, sub_add_cancel] using h.symm
  have henergy := (finiteGrouped_coefficientEnergy_le c).trans
    (mul_le_mul_of_nonneg_right (show (r : ℝ) ≤ (q : ℝ) + 1 by exact_mod_cast (by omega : r ≤ q + 1))
      (sq_nonneg ‖c‖))
  have h := mul_le_mul_of_nonneg_left henergy (div_pos hA hq).le
  have hcancel : A / ((q : ℝ) + 1) * (((q : ℝ) + 1) * ‖c‖ ^ 2) = A * ‖c‖ ^ 2 := by
    field_simp
  rw [hcancel] at h
  have hfinal := h.trans (hbound r hr centred hcentred c)
  rw [heq] at hfinal
  exact hfinal

/-- Intrinsic width version: all finite node lists of diameter at most `D`
and size at most `q` share one actual window floor. This is stronger than
the weakly ordered source formulation and includes every confluent boundary. -/
theorem exists_groupedFiniteExponential_localFloor_of_diameter (q : ℕ) {W D : ℝ}
    (hW : 0 < W) (hD : 0 ≤ D) :
    ∃ A : ℝ, 0 < A ∧ ∀ r : ℕ, r ≤ q → ∀ nodes : Fin r → ℝ,
      (∀ i j, dist (nodes i) (nodes j) ≤ D) → ∀ c : Fin r → ℂ,
        A * (∑ j, ‖c j‖ ^ 2) ≤
          ∫ t in Icc (-W) W, ‖∑ j, c j * groupedExponentialInitial nodes j t‖ ^ 2 := by
  obtain ⟨A, hA, hbound⟩ := exists_groupedFiniteExponential_localFloor q hW hD
  refine ⟨A, hA, ?_⟩
  intro r hr nodes hdiam c
  by_cases hpos : 0 < r
  · apply hbound r hr (nodes ⟨0, hpos⟩) nodes
    intro j
    simpa only [Real.dist_eq] using hdiam j ⟨0, hpos⟩
  · have hrzero : r = 0 := by omega
    subst r
    simp

end

end MeyerGeneralProblem
