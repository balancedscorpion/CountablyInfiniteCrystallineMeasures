module

public import MeyerGeneralProblem.Sampling.GroupedExponential
public import Mathlib.Topology.Order.Compact
import all Mathlib.Topology.Order.Compact

@[expose] public section

/-!
# A genuine two-node confluent window floor

The basis consists of the original Fourier phase and its actual first
frequency divided difference. The latter has value zero and time derivative
`2πi` at time zero, also at a node collision. These genuine jets prove
linear independence on every positive window. Compactness then gives one
positive energy bound before choosing the gap or coefficients.

This local two-node result is not a grouped density theorem or a lower bound
for infinitely many interacting clusters.
-/

namespace MeyerGeneralProblem

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

/-- The actual first divided difference at `x, x + δ`, including `δ = 0`. -/
def twoNodeGroupedExponential (x δ t : ℝ) : ℂ :=
  groupedExponential (finiteNodeSequence ![x, x + δ]) 1 t

/-- The two-node basis is the actual extended divided slope in frequency. -/
theorem twoNodeGroupedExponential_eq_dslope (x δ t : ℝ) :
    twoNodeGroupedExponential x δ t = dslope (fun s => gramPhase s t) x (x + δ) := by
  simp [twoNodeGroupedExponential, groupedExponential, analyticDividedDifference_succ,
    analyticDividedDifference_zero, finiteNodeSequence]

/-- The exact confluent value is the frequency derivative of the phase. -/
theorem twoNodeGroupedExponential_zero_gap (x t : ℝ) :
    twoNodeGroupedExponential x 0 t = gramPhaseFrequencyMultiplier t * gramPhase x t := by
  rw [twoNodeGroupedExponential_eq_dslope, add_zero, dslope_same]
  exact (hasDerivAt_gramPhase_frequency x t).deriv

/-- Away from collision, the actual divided difference has its ordinary
quotient formula. No estimate uses this inverse gap. -/
theorem twoNodeGroupedExponential_nonzero_gap (x δ t : ℝ) (hδ : δ ≠ 0) :
    twoNodeGroupedExponential x δ t =
      (δ⁻¹ : ℝ) • (gramPhase (x + δ) t - gramPhase x t) := by
  rw [twoNodeGroupedExponential_eq_dslope, dslope_of_ne _ (by simpa using hδ),
    slope_def_module, add_sub_cancel_left]

/-- Removing the frequency anchor multiplies the actual confluent basis
by the original unit-modulus phase, even at collision. -/
theorem twoNodeGroupedExponential_anchor (x δ t : ℝ) :
    twoNodeGroupedExponential x δ t = gramPhase x t * twoNodeGroupedExponential 0 δ t := by
  by_cases hδ : δ = 0
  · subst δ
    simp only [twoNodeGroupedExponential_zero_gap, gramPhase_zero_left, mul_one]
    ring
  · rw [twoNodeGroupedExponential_nonzero_gap _ _ _ hδ,
      twoNodeGroupedExponential_nonzero_gap _ _ _ hδ, zero_add,
      gramPhase_zero_left, gramPhase_add]
    simp only [Complex.real_smul]
    ring

/-- Both finite frequency nodes and time vary continuously through collision. -/
theorem continuous_twoNodeGroupedExponential :
    Continuous (fun p : (ℝ × ℝ) × ℝ => twoNodeGroupedExponential p.1.1 p.1.2 p.2) := by
  exact (continuous_groupedExponential_nodes_time 1).comp
    (show Continuous (fun p : (ℝ × ℝ) × ℝ =>
      (![p.1.1, p.1.1 + p.1.2], p.2)) by fun_prop)

/-- The actual first basis value at time zero is one. -/
theorem twoNodeFirstBasis_zero (x : ℝ) : gramPhase x 0 = 1 := gramPhase_zero_right x

/-- The actual second basis value at time zero is zero, regardless of gap. -/
theorem twoNodeGroupedExponential_time_zero (x δ : ℝ) :
    twoNodeGroupedExponential x δ 0 = 0 := by
  by_cases hδ : δ = 0
  · subst δ
    simp [twoNodeGroupedExponential_zero_gap, gramPhaseFrequencyMultiplier]
  · simp [twoNodeGroupedExponential_nonzero_gap _ _ _ hδ]

private theorem gramPhase_swap (x t : ℝ) : gramPhase x t = gramPhase t x := by
  have h : 2 * Real.pi * x * t = 2 * Real.pi * t * x := by ring
  rw [gramPhase, gramPhase, h]

/-- The Fourier phase has its genuine time derivative. -/
theorem hasDerivAt_gramPhase_time (x t : ℝ) :
    HasDerivAt (gramPhase x) (gramPhaseFrequencyMultiplier x * gramPhase x t) t := by
  simpa only [gramPhase_swap] using hasDerivAt_gramPhase_frequency t x

private theorem frequencyMultiplier_mul (δ : ℝ) :
    gramPhaseFrequencyMultiplier δ = (δ : ℂ) * gramPhaseFrequencyMultiplier 1 := by
  unfold gramPhaseFrequencyMultiplier
  push_cast
  ring

/-- The confluent second basis has the exact first time jet `2πi`, including
at collision. The proof differentiates the actual functions, not their limits. -/
theorem hasDerivAt_twoNodeGroupedExponential_zero (δ : ℝ) :
    HasDerivAt (twoNodeGroupedExponential 0 δ) (gramPhaseFrequencyMultiplier 1) 0 := by
  by_cases hδ : δ = 0
  · subst δ
    have hfun : twoNodeGroupedExponential 0 0 =
        fun t : ℝ => (t : ℂ) * gramPhaseFrequencyMultiplier 1 := by
      funext t
      simp only [twoNodeGroupedExponential_zero_gap, gramPhase_zero_left, mul_one]
      exact frequencyMultiplier_mul t
    rw [hfun]
    simpa using (Complex.ofRealCLM.hasDerivAt).mul_const (gramPhaseFrequencyMultiplier 1)
  · have hfun : twoNodeGroupedExponential 0 δ =
        fun t : ℝ => (δ⁻¹ : ℝ) • (gramPhase δ t - 1) := by
      funext t
      simp only [twoNodeGroupedExponential_nonzero_gap _ _ _ hδ,
        zero_add, gramPhase_zero_left]
    rw [hfun]
    have h := ((hasDerivAt_gramPhase_time δ 0).sub_const 1).const_smul (δ⁻¹ : ℝ)
    simpa only [Pi.smul_def, gramPhase_zero_right, mul_one, frequencyMultiplier_mul δ,
      Complex.real_smul, Complex.ofReal_inv, ← mul_assoc,
      inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hδ), one_mul] using h

/-- The anchored second basis has the same first time jet as the centred
basis, since its value at zero vanishes. -/
theorem hasDerivAt_twoNodeGroupedExponential_time_zero (x δ : ℝ) :
    HasDerivAt (twoNodeGroupedExponential x δ) (gramPhaseFrequencyMultiplier 1) 0 := by
  have hfun : twoNodeGroupedExponential x δ =
      fun t => gramPhase x t * twoNodeGroupedExponential 0 δ t :=
    funext (twoNodeGroupedExponential_anchor x δ)
  rw [hfun]
  simpa only [Pi.mul_def, twoNodeGroupedExponential_time_zero, mul_zero, gramPhase_zero_right,
    zero_add, one_mul] using
    (hasDerivAt_gramPhase_time x 0).mul (hasDerivAt_twoNodeGroupedExponential_zero δ)

/-- The actual centred two-node synthesis amplitude. -/
def twoNodeGroupedAmplitude (δ : ℝ) (c : ℂ × ℂ) (t : ℝ) : ℂ :=
  c.1 + c.2 * twoNodeGroupedExponential 0 δ t

/-- Joint continuity of gap, coefficients, and time, including gap zero. -/
theorem continuous_twoNodeGroupedAmplitude :
    Continuous (fun p : (ℝ × (ℂ × ℂ)) × ℝ => twoNodeGroupedAmplitude p.1.1 p.1.2 p.2) := by
  have hc := continuous_twoNodeGroupedExponential.comp
    (show Continuous (fun p : (ℝ × (ℂ × ℂ)) × ℝ => ((0, p.1.1), p.2)) by fun_prop)
  exact (continuous_fst.snd.fst).add ((continuous_fst.snd.snd).mul hc)

/-- Exact homogeneity of the actual two-node synthesis. -/
theorem twoNodeGroupedAmplitude_smul (δ t : ℝ) (z : ℂ) (c : ℂ × ℂ) :
    twoNodeGroupedAmplitude δ (z • c) t = z * twoNodeGroupedAmplitude δ c t := by
  simp only [twoNodeGroupedAmplitude, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- The true window energy, with Lebesgue measure on the closed window. -/
def twoNodeGroupedWindowEnergy (W δ : ℝ) (c : ℂ × ℂ) : ℝ :=
  ∫ t in Icc (-W) W, ‖twoNodeGroupedAmplitude δ c t‖ ^ 2

/-- The true energy is continuous jointly in gap and coefficients. -/
theorem continuous_twoNodeGroupedWindowEnergy (W : ℝ) :
    Continuous (fun p : ℝ × (ℂ × ℂ) => twoNodeGroupedWindowEnergy W p.1 p.2) := by
  exact continuous_parametric_integral_of_continuous
    (continuous_twoNodeGroupedAmplitude.norm.pow 2) isCompact_Icc

/-- Exact quadratic homogeneity of the actual integral. -/
theorem twoNodeGroupedWindowEnergy_smul (W δ : ℝ) (z : ℂ) (c : ℂ × ℂ) :
    twoNodeGroupedWindowEnergy W δ (z • c) = ‖z‖ ^ 2 * twoNodeGroupedWindowEnergy W δ c := by
  simp only [twoNodeGroupedWindowEnergy, twoNodeGroupedAmplitude_smul, norm_mul, mul_pow]
  exact integral_const_mul _ _

/-- Actual value and derivative jets exclude a nonzero coefficient vector
whose synthesis vanishes throughout a positive window. -/
theorem exists_twoNodeGroupedAmplitude_ne_zero {W : ℝ} (hW : 0 < W)
    (δ : ℝ) (c : ℂ × ℂ) (hc : c ≠ 0) :
    ∃ t ∈ Icc (-W) W, twoNodeGroupedAmplitude δ c t ≠ 0 := by
  by_contra hnone
  push Not at hnone
  have hczero := hnone 0 (show (0 : ℝ) ∈ Icc (-W) W by constructor <;> linarith)
  have hc0 : c.1 = 0 := by
    simpa only [twoNodeGroupedAmplitude, twoNodeGroupedExponential_time_zero,
      mul_zero, add_zero] using hczero
  have hder : HasDerivAt (twoNodeGroupedAmplitude δ c)
      (c.2 * gramPhaseFrequencyMultiplier 1) 0 :=
    ((hasDerivAt_twoNodeGroupedExponential_zero δ).const_mul c.2).const_add c.1
  have heq : twoNodeGroupedAmplitude δ c =ᶠ[𝓝 0] (fun _ => (0 : ℂ)) := by
    filter_upwards [Ioo_mem_nhds (show -W < 0 by linarith) hW] with t ht
    exact hnone t ⟨ht.1.le, ht.2.le⟩
  have hderzero : HasDerivAt (twoNodeGroupedAmplitude δ c) 0 0 :=
    (hasDerivAt_const 0 (0 : ℂ)).congr_of_eventuallyEq heq
  have hmult : gramPhaseFrequencyMultiplier 1 ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [norm_gramPhaseFrequencyMultiplier]
    positivity
  have hc1 : c.2 = 0 := (mul_eq_zero.mp (hder.unique hderzero)).resolve_right hmult
  exact hc (Prod.ext hc0 hc1)

/-- The window energy is genuinely positive for every nonzero coefficient
vector, even when the two frequency nodes coincide. -/
theorem twoNodeGroupedWindowEnergy_pos {W : ℝ} (hW : 0 < W)
    (δ : ℝ) (c : ℂ × ℂ) (hc : c ≠ 0) :
    0 < twoNodeGroupedWindowEnergy W δ c := by
  have hcontinuous : Continuous (twoNodeGroupedAmplitude δ c) :=
    continuous_twoNodeGroupedAmplitude.comp
      (show Continuous (fun t : ℝ => ((δ, c), t)) by fun_prop)
  obtain ⟨t, ht, hne⟩ := exists_twoNodeGroupedAmplitude_ne_zero hW δ c hc
  have hpos := intervalIntegral.integral_pos (show -W < W by linarith)
    (hcontinuous.norm.pow 2).continuousOn (fun t _ => sq_nonneg _)
    ⟨t, ht, sq_pos_of_pos (norm_pos_iff.mpr hne)⟩
  simpa only [Pi.pow_apply, twoNodeGroupedWindowEnergy,
    intervalIntegral.integral_of_le (show -W ≤ W by linarith),
    integral_Icc_eq_integral_Ioc] using hpos

/-- One positive centred window floor is chosen before the gap in `[0,D]`
and before the coefficient vector. This includes the confluent endpoint. -/
theorem exists_twoNodeGroupedWindowEnergy_floor {W D : ℝ} (hW : 0 < W) (_hD : 0 ≤ D) :
    ∃ A : ℝ, 0 < A ∧ ∀ δ ∈ Icc 0 D, ∀ c : ℂ × ℂ,
      A * ‖c‖ ^ 2 ≤ twoNodeGroupedWindowEnergy W δ c := by
  have hcompact : IsCompact (Icc (0 : ℝ) D ×ˢ Metric.sphere (0 : ℂ × ℂ) 1) :=
    isCompact_Icc.prod (isCompact_sphere 0 1)
  obtain ⟨A, hA, hbound⟩ := hcompact.exists_forall_le'
    (continuous_twoNodeGroupedWindowEnergy W).continuousOn (a := (0 : ℝ)) (by
      rintro ⟨δ, c⟩ ⟨hδ, hc⟩
      apply twoNodeGroupedWindowEnergy_pos hW δ c
      intro hz
      simp [hz] at hc)
  refine ⟨A, hA, ?_⟩
  intro δ hδ c
  by_cases hc : c = 0
  · simp [hc, twoNodeGroupedWindowEnergy, twoNodeGroupedAmplitude]
  have hnorm : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hunit : ((‖c‖⁻¹ : ℝ) : ℂ) • c ∈ Metric.sphere (0 : ℂ × ℂ) 1 := by
    simp only [Metric.mem_sphere, dist_zero_right, norm_smul, Complex.norm_real,
      Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg c)]
    exact inv_mul_cancel₀ hnorm.ne'
  have h := hbound (δ, ((‖c‖⁻¹ : ℝ) : ℂ) • c) ⟨hδ, hunit⟩
  rw [twoNodeGroupedWindowEnergy_smul] at h
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_inv,
    abs_of_nonneg (norm_nonneg c), inv_pow] at h
  apply (le_div_iff₀ (sq_pos_of_pos hnorm)).mp
  simpa only [div_eq_mul_inv, mul_comm] using h

/-- Anchor removal preserves the actual squared synthesis norm pointwise. -/
theorem norm_twoNodeGroupedSynthesis_eq (x δ t : ℝ) (c0 c1 : ℂ) :
    ‖c0 * gramPhase x t + c1 * twoNodeGroupedExponential x δ t‖ =
      ‖twoNodeGroupedAmplitude δ (c0, c1) t‖ := by
  rw [twoNodeGroupedExponential_anchor]
  have heq : c0 * gramPhase x t + c1 * (gramPhase x t * twoNodeGroupedExponential 0 δ t) =
      gramPhase x t * twoNodeGroupedAmplitude δ (c0, c1) t := by
    unfold twoNodeGroupedAmplitude
    ring
  rw [heq, norm_mul, norm_gramPhase, one_mul]

/-- A uniform actual two-node confluent `L²` window lower bound, including
gap zero, with the constant chosen before anchor, gap, and coefficients. -/
theorem exists_twoNodeGroupedExponential_localFloor {W D : ℝ}
    (hW : 0 < W) (hD : 0 ≤ D) :
    ∃ A : ℝ, 0 < A ∧ ∀ x : ℝ, ∀ δ ∈ Icc 0 D, ∀ c0 c1 : ℂ,
      A * (‖c0‖ ^ 2 + ‖c1‖ ^ 2) ≤
        ∫ t in Icc (-W) W,
          ‖c0 * gramPhase x t + c1 * twoNodeGroupedExponential x δ t‖ ^ 2 := by
  obtain ⟨A, hA, hbound⟩ := exists_twoNodeGroupedWindowEnergy_floor hW hD
  refine ⟨A / 2, half_pos hA, ?_⟩
  intro x δ hδ c0 c1
  have h0 : ‖c0‖ ≤ ‖(c0, c1)‖ := le_max_left _ _
  have h1 : ‖c1‖ ≤ ‖(c0, c1)‖ := le_max_right _ _
  have hsum : ‖c0‖ ^ 2 + ‖c1‖ ^ 2 ≤ 2 * ‖(c0, c1)‖ ^ 2 := by
    nlinarith [norm_nonneg c0, norm_nonneg c1, norm_nonneg (c0, c1)]
  have h := (mul_le_mul_of_nonneg_left hsum (half_pos hA).le).trans
    (show A / 2 * (2 * ‖(c0, c1)‖ ^ 2) ≤ twoNodeGroupedWindowEnergy W δ (c0, c1) by
      convert hbound δ hδ (c0, c1) using 1; ring)
  simpa only [norm_twoNodeGroupedSynthesis_eq, twoNodeGroupedWindowEnergy] using h

/-- The same lower bound stated directly with the actual analytic divided
difference of the two Fourier exponentials, with no auxiliary basis notation. -/
theorem exists_twoNodeAnalyticDividedDifference_localFloor {W D : ℝ}
    (hW : 0 < W) (hD : 0 ≤ D) :
    ∃ A : ℝ, 0 < A ∧ ∀ x : ℝ, ∀ δ ∈ Icc 0 D, ∀ c0 c1 : ℂ,
      A * (‖c0‖ ^ 2 + ‖c1‖ ^ 2) ≤
        ∫ t in Icc (-W) W,
          ‖c0 * gramPhase x t + c1 *
            analyticDividedDifference (finiteNodeSequence ![x, x + δ]) 1
              (fun s => gramPhase s t)‖ ^ 2 := by
  exact exists_twoNodeGroupedExponential_localFloor hW hD

/-- A full-collision regression: the true derivative-jet basis itself has
a positive window floor, uniformly in its anchor. -/
theorem exists_twoNodeConfluentExponential_localFloor {W : ℝ} (hW : 0 < W) :
    ∃ A : ℝ, 0 < A ∧ ∀ x : ℝ, ∀ c0 c1 : ℂ,
      A * (‖c0‖ ^ 2 + ‖c1‖ ^ 2) ≤
        ∫ t in Icc (-W) W,
          ‖c0 * gramPhase x t +
            c1 * (gramPhaseFrequencyMultiplier t * gramPhase x t)‖ ^ 2 := by
  obtain ⟨A, hA, hbound⟩ :=
    exists_twoNodeGroupedExponential_localFloor hW (le_refl (0 : ℝ))
  refine ⟨A, hA, ?_⟩
  intro x c0 c1
  simpa only [twoNodeGroupedExponential_zero_gap] using
    hbound x 0 ⟨le_refl _, le_refl _⟩ c0 c1

end

end MeyerGeneralProblem
