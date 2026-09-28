module

public import MeyerGeneralProblem.Hermite.MehlerBounds

@[expose] public section

/-!
# Refined off-diagonal Mehler bounds

The signed-square estimate alone loses the spatial scale that cancels the
two diagonal normalization factors.  This module retains half of that decay
and half of the positive spatial part of the Mehler quadratic.  Its Laplace
integral is the analytic input for a normalized carrier Gram estimate.
-/

namespace MeyerGeneralProblem

noncomputable section

/-- The slow spatial coefficient in the heat-time Mehler quadratic. -/
def mehlerSpatialRate (t : ℝ) : ℝ :=
  (1 - Real.exp (-t)) / (1 + Real.exp (-t))

theorem mehlerSpatialRate_pos {t : ℝ} (ht : 0 < t) :
    0 < mehlerSpatialRate t := by
  unfold mehlerSpatialRate
  have hr0 : 0 < Real.exp (-t) := Real.exp_pos _
  have hr1 : Real.exp (-t) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  positivity

/-- Besides its signed-square lower bound, the Mehler quadratic retains a
positive multiple of `X² + Y²`. -/
theorem mehlerSpatialRate_mul_sq_add_sq_le_quadratic
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (X Y : ℝ) :
    (1 - r) / (1 + r) * (X ^ 2 + Y ^ 2) ≤
      ((1 + r ^ 2) * (X ^ 2 + Y ^ 2) - 4 * r * X * Y) /
        (1 - r ^ 2) := by
  have hplus : 0 < 1 + r := by linarith
  have hminus : 0 < 1 - r := by linarith
  have hsq : 0 < 1 - r ^ 2 := by nlinarith
  rw [← sub_nonneg]
  rw [show
      ((1 + r ^ 2) * (X ^ 2 + Y ^ 2) - 4 * r * X * Y) /
            (1 - r ^ 2) -
          (1 - r) / (1 + r) * (X ^ 2 + Y ^ 2) =
        2 * r / (1 - r ^ 2) * (X - Y) ^ 2 by
    field_simp [hplus.ne', hminus.ne', hsq.ne']
    ring]
  positivity

/-- Averaging the two independent lower bounds retains simultaneous
signed-square and spatial damping. -/
theorem signedSquare_add_spatial_le_two_mul_mehlerQuadratic
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (X Y : ℝ) :
    |X * abs X - Y * abs Y| +
        (1 - r) / (1 + r) * (X ^ 2 + Y ^ 2) ≤
      2 * (((1 + r ^ 2) * (X ^ 2 + Y ^ 2) - 4 * r * X * Y) /
        (1 - r ^ 2)) := by
  have hsigned :=
    abs_mul_abs_sub_mul_abs_le_mehlerQuadratic hr0 hr1 X Y
  have hspatial :=
    mehlerSpatialRate_mul_sq_add_sq_le_quadratic hr0 hr1 X Y
  linarith

/-- Elementary lower tangent for `1 - exp (-t)`. -/
theorem mul_exp_neg_le_one_sub_exp_neg (t : ℝ) :
    t * Real.exp (-t) ≤ 1 - Real.exp (-t) := by
  have h := Real.add_one_le_exp t
  have hmul := mul_le_mul_of_nonneg_right h (Real.exp_pos (-t)).le
  rw [← Real.exp_add] at hmul
  norm_num at hmul
  nlinarith

/-- Uniform comparison of the Mehler spatial rate with `min t 1`.  Keeping
the explicit positive constant avoids any numerical approximation to `e`. -/
theorem exp_neg_one_div_two_mul_min_le_mehlerSpatialRate
    {t : ℝ} (ht : 0 < t) :
    Real.exp (-1) / 2 * min t 1 ≤ mehlerSpatialRate t := by
  have hr0 : 0 < Real.exp (-t) := Real.exp_pos _
  have hr1 : Real.exp (-t) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hrle : Real.exp (-t) ≤ 1 := hr1.le
  by_cases ht1 : t ≤ 1
  · rw [min_eq_left ht1]
    have hrexplower : Real.exp (-1) ≤ Real.exp (-t) := by
      apply Real.exp_le_exp.mpr
      linarith
    have hnum := mul_exp_neg_le_one_sub_exp_neg t
    unfold mehlerSpatialRate
    rw [le_div_iff₀ (by positivity : 0 < 1 + Real.exp (-t))]
    have hleft :
        Real.exp (-1) / 2 * t * (1 + Real.exp (-t)) ≤
          t * Real.exp (-1) := by
      have ht0 : 0 ≤ t := ht.le
      calc
        Real.exp (-1) / 2 * t * (1 + Real.exp (-t)) =
            (t * Real.exp (-1)) * ((1 + Real.exp (-t)) / 2) := by
          ring
        _ ≤ (t * Real.exp (-1)) * 1 := by
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg ht0 (Real.exp_pos _).le)
          linarith
        _ = t * Real.exp (-1) := by ring
    have hmid : t * Real.exp (-1) ≤ t * Real.exp (-t) := by
      gcongr
    linarith
  · have ht1' : 1 ≤ t := le_of_not_ge ht1
    rw [min_eq_right ht1']
    have hrhalf : Real.exp (-t) ≤ 1 / 2 := by
      have hrexple : Real.exp (-t) ≤ Real.exp (-1) := by
        apply Real.exp_le_exp.mpr
        linarith
      have he : (2 : ℝ) ≤ Real.exp 1 := by
        simpa only [one_add_one_eq_two] using Real.add_one_le_exp 1
      have hinv : (Real.exp 1)⁻¹ ≤ (2 : ℝ)⁻¹ :=
        (inv_le_inv₀ (by positivity : 0 < Real.exp 1)
          (by norm_num : (0 : ℝ) < 2)).2 he
      have hneg : Real.exp (-1) = (Real.exp 1)⁻¹ := by
        rw [Real.exp_neg]
      calc
        Real.exp (-t) ≤ Real.exp (-1) := hrexple
        _ = (Real.exp 1)⁻¹ := hneg
        _ ≤ (2 : ℝ)⁻¹ := hinv
        _ = 1 / 2 := by norm_num
    have hehalf : Real.exp (-1) ≤ 1 / 2 := by
      calc
        Real.exp (-1) = (Real.exp 1)⁻¹ := by rw [Real.exp_neg]
        _ ≤ (2 : ℝ)⁻¹ := by
          apply (inv_le_inv₀ (by positivity : 0 < Real.exp 1)
            (by norm_num : (0 : ℝ) < 2)).2
          simpa only [one_add_one_eq_two] using Real.add_one_le_exp 1
        _ = 1 / 2 := by norm_num
    unfold mehlerSpatialRate
    rw [le_div_iff₀ (by positivity : 0 < 1 + Real.exp (-t))]
    have hleft :
        Real.exp (-1) / 2 * (1 + Real.exp (-t)) ≤ 3 / 8 := by
      calc
        Real.exp (-1) / 2 * (1 + Real.exp (-t)) ≤
            (1 / 2 : ℝ) / 2 * (1 + 1 / 2) := by
          gcongr
        _ = 3 / 8 := by norm_num
    have hright : (1 / 2 : ℝ) ≤ 1 - Real.exp (-t) := by
      linarith
    linarith

/-- Constant in the sharp small-time upper bound for the Mehler prefactor. -/
def smallTimeMehlerPrefactorConstant : ℝ :=
  Real.sqrt 2 / Real.sqrt (2 * Real.exp (-2))

theorem smallTimeMehlerPrefactorConstant_pos :
    0 < smallTimeMehlerPrefactorConstant := by
  unfold smallTimeMehlerPrefactorConstant
  positivity

/-- Matching upper estimate for the Mehler square-root prefactor on
`0 < t ≤ 1`. -/
theorem mehlerPrefactor_le_smallTimeConstant_div_sqrt
    {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    Real.sqrt 2 / Real.sqrt (1 - Real.exp (-t) ^ 2) ≤
      smallTimeMehlerPrefactorConstant / Real.sqrt t := by
  have hsq : Real.exp (-t) ^ 2 = Real.exp (-2 * t) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hrexplower : Real.exp (-2) ≤ Real.exp (-2 * t) := by
    apply Real.exp_le_exp.mpr
    linarith
  have hbase := mul_exp_neg_le_one_sub_exp_neg (2 * t)
  have hbase' :
      2 * t * Real.exp (-2 * t) ≤ 1 - Real.exp (-2 * t) := by
    simpa only [neg_mul] using hbase
  have hden :
      2 * t * Real.exp (-2) ≤ 1 - Real.exp (-t) ^ 2 := by
    rw [hsq]
    calc
      2 * t * Real.exp (-2) ≤ 2 * t * Real.exp (-2 * t) := by
        gcongr
      _ ≤ 1 - Real.exp (-2 * t) := hbase'
  have hsqrt :
      Real.sqrt (2 * Real.exp (-2)) * Real.sqrt t ≤
        Real.sqrt (1 - Real.exp (-t) ^ 2) := by
    calc
      Real.sqrt (2 * Real.exp (-2)) * Real.sqrt t =
          Real.sqrt ((2 * Real.exp (-2)) * t) := by
        rw [Real.sqrt_mul (by positivity : 0 ≤ 2 * Real.exp (-2))]
      _ = Real.sqrt (2 * t * Real.exp (-2)) := by ring_nf
      _ ≤ Real.sqrt (1 - Real.exp (-t) ^ 2) :=
        Real.sqrt_le_sqrt hden
  have hdenpos : 0 < 1 - Real.exp (-t) ^ 2 := by
    have hr0 := Real.exp_pos (-t)
    have hr1 : Real.exp (-t) < 1 := by
      rw [Real.exp_lt_one_iff]
      linarith
    nlinarith
  calc
    Real.sqrt 2 / Real.sqrt (1 - Real.exp (-t) ^ 2) ≤
        Real.sqrt 2 /
          (Real.sqrt (2 * Real.exp (-2)) * Real.sqrt t) := by
      gcongr
    _ = smallTimeMehlerPrefactorConstant / Real.sqrt t := by
      unfold smallTimeMehlerPrefactorConstant
      field_simp

/-- Constant controlling the nonsingular large-time Mehler prefactor. -/
def largeTimeMehlerPrefactorConstant : ℝ :=
  Real.sqrt 2 / Real.sqrt (1 - Real.exp (-2))

theorem largeTimeMehlerPrefactorConstant_pos :
    0 < largeTimeMehlerPrefactorConstant := by
  unfold largeTimeMehlerPrefactorConstant
  have h : Real.exp (-2) < 1 := by
    rw [Real.exp_lt_one_iff]
    norm_num
  positivity

theorem mehlerPrefactor_le_largeTimeConstant
    {t : ℝ} (ht1 : 1 ≤ t) :
    Real.sqrt 2 / Real.sqrt (1 - Real.exp (-t) ^ 2) ≤
      largeTimeMehlerPrefactorConstant := by
  have ht : 0 < t := zero_lt_one.trans_le ht1
  have hsq : Real.exp (-t) ^ 2 = Real.exp (-2 * t) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hsq1 : Real.exp (-2 * t) ≤ Real.exp (-2) := by
    apply Real.exp_le_exp.mpr
    linarith
  have hden : 1 - Real.exp (-2) ≤ 1 - Real.exp (-t) ^ 2 := by
    rw [hsq]
    linarith
  unfold largeTimeMehlerPrefactorConstant
  have hconstden : 0 < 1 - Real.exp (-2) := by
    have : Real.exp (-2) < 1 := by
      rw [Real.exp_lt_one_iff]
      norm_num
    linarith
  gcongr

/-- Refined heat-kernel bound: one half of the Mehler exponent supplies
signed-square Gaussian decay and the other supplies the spatial damping
needed for sharp normalization. -/
theorem norm_hermiteHeatKernel_le_signedSquare_mul_spatial
    {t : ℝ} (ht : 0 < t) (X Y : ℝ) :
    ‖hermiteHeatKernel t X Y‖ ≤
      Real.sqrt 2 / Real.sqrt (1 - Real.exp (-t) ^ 2) *
        Real.exp
          (-(Real.pi / 2) * |X * abs X - Y * abs Y|) *
        Real.exp
          (-(Real.pi / 2) * mehlerSpatialRate t * (X ^ 2 + Y ^ 2)) := by
  let r := Real.exp (-t)
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by
    dsimp [r]
    rw [Real.exp_lt_one_iff]
    linarith
  have hqpos : 0 < 1 - r ^ 2 := by nlinarith
  have hpref : 0 ≤ Real.sqrt 2 / Real.sqrt (1 - r ^ 2) := by
    positivity
  rw [hermiteHeatKernel_eq_closed ht, Complex.norm_real, Real.norm_eq_abs]
  unfold normalizedHermiteMehlerClosed
  rw [abs_of_nonneg (mul_nonneg hpref (Real.exp_pos _).le)]
  change
    Real.sqrt 2 / Real.sqrt (1 - r ^ 2) *
        Real.exp
          (-Real.pi *
            (((1 + r ^ 2) * (X ^ 2 + Y ^ 2) - 4 * r * X * Y) /
              (1 - r ^ 2))) ≤
      Real.sqrt 2 / Real.sqrt (1 - r ^ 2) *
        Real.exp (-(Real.pi / 2) * |X * abs X - Y * abs Y|) *
        Real.exp
          (-(Real.pi / 2) * ((1 - r) / (1 + r)) * (X ^ 2 + Y ^ 2))
  have hcombined :=
    signedSquare_add_spatial_le_two_mul_mehlerQuadratic hr0 hr1 X Y
  calc
    Real.sqrt 2 / Real.sqrt (1 - r ^ 2) *
          Real.exp
            (-Real.pi *
              (((1 + r ^ 2) * (X ^ 2 + Y ^ 2) - 4 * r * X * Y) /
                (1 - r ^ 2))) ≤
        Real.sqrt 2 / Real.sqrt (1 - r ^ 2) *
          (Real.exp (-(Real.pi / 2) * |X * abs X - Y * abs Y|) *
            Real.exp
              (-(Real.pi / 2) * ((1 - r) / (1 + r)) *
                (X ^ 2 + Y ^ 2))) := by
      apply mul_le_mul_of_nonneg_left _ hpref
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [Real.pi_pos]
    _ = Real.sqrt 2 / Real.sqrt (1 - r ^ 2) *
          Real.exp (-(Real.pi / 2) * |X * abs X - Y * abs Y|) *
          Real.exp
            (-(Real.pi / 2) * ((1 - r) / (1 + r)) *
              (X ^ 2 + Y ^ 2)) := by ring

/-- Version with the spatial rate replaced by an explicit multiple of
`min t 1`. -/
theorem norm_hermiteHeatKernel_le_signedSquare_mul_minTimeSpatial
    {t : ℝ} (ht : 0 < t) (X Y : ℝ) :
    ‖hermiteHeatKernel t X Y‖ ≤
      Real.sqrt 2 / Real.sqrt (1 - Real.exp (-t) ^ 2) *
        Real.exp
          (-(Real.pi / 2) * |X * abs X - Y * abs Y|) *
        Real.exp
          (-(Real.pi / 2) * (Real.exp (-1) / 2) * min t 1 *
            (X ^ 2 + Y ^ 2)) := by
  refine (norm_hermiteHeatKernel_le_signedSquare_mul_spatial ht X Y).trans ?_
  have hrate := exp_neg_one_div_two_mul_min_le_mehlerSpatialRate ht
  have hS : 0 ≤ X ^ 2 + Y ^ 2 := by positivity
  have hpref :
      0 ≤ Real.sqrt 2 / Real.sqrt (1 - Real.exp (-t) ^ 2) := by
    positivity
  have hsigned :
      0 ≤ Real.exp (-(Real.pi / 2) * |X * abs X - Y * abs Y|) :=
    (Real.exp_pos _).le
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hpref hsigned)
  apply Real.exp_le_exp.mpr
  have hmul :
      (Real.exp (-1) / 2 * min t 1) * (X ^ 2 + Y ^ 2) ≤
        mehlerSpatialRate t * (X ^ 2 + Y ^ 2) := by
    exact mul_le_mul_of_nonneg_right hrate hS
  calc
    -(Real.pi / 2) * mehlerSpatialRate t * (X ^ 2 + Y ^ 2) =
        -(Real.pi / 2) *
          (mehlerSpatialRate t * (X ^ 2 + Y ^ 2)) := by ring
    _ ≤ -(Real.pi / 2) *
          ((Real.exp (-1) / 2 * min t 1) * (X ^ 2 + Y ^ 2)) := by
      exact mul_le_mul_of_nonpos_left hmul
        (neg_nonpos.mpr (div_nonneg Real.pi_pos.le (by norm_num)))
    _ = -(Real.pi / 2) * (Real.exp (-1) / 2) * min t 1 *
          (X ^ 2 + Y ^ 2) := by ring

/-- Positive spatial damping constant retained in the refined bound. -/
def mehlerSpatialDamping : ℝ :=
  (Real.pi / 2) * (Real.exp (-1) / 2)

theorem mehlerSpatialDamping_pos : 0 < mehlerSpatialDamping := by
  unfold mehlerSpatialDamping
  positivity

/-- The Gamma shape of the sharply normalized small-time integral. -/
def hermiteResolventHalfShape (m : ℕ) : ℝ :=
  (2 * m : ℝ) - 1 / 2

theorem hermiteResolventHalfShape_pos
    {m : ℕ} (hm : 1 ≤ m) :
    0 < hermiteResolventHalfShape m := by
  unfold hermiteResolventHalfShape
  have hm' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  linarith

theorem natPow_div_sqrt_eq_rpow_sub_half
    (n : ℕ) {t : ℝ} (ht : 0 < t) :
    t ^ n / Real.sqrt t = t ^ ((n : ℝ) - 1 / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast]
  exact (Real.rpow_sub ht (n : ℝ) (1 / 2)).symm

/-- Norm integrand whose full positive-half-line integral controls the raw
Hermite resolvent kernel. -/
def hermiteResolventHeatNormIntegrand
    (m : ℕ) (X Y t : ℝ) : ℝ :=
  t ^ ((2 * m : ℕ) - 1) * Real.exp (-t) *
    ‖hermiteHeatKernel t X Y‖

theorem hermiteResolventHeatNormIntegrand_nonneg
    (m : ℕ) (X Y : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ hermiteResolventHeatNormIntegrand m X Y t := by
  unfold hermiteResolventHeatNormIntegrand
  positivity

theorem hermiteResolventHeatNormIntegrand_eq_norm_tsum
    (m : ℕ) (X Y : ℝ) {t : ℝ} (ht : 0 < t) :
    hermiteResolventHeatNormIntegrand m X Y t =
      ‖∑' n : ℕ, hermiteResolventLaplaceTerm m X Y n t‖ := by
  rw [tsum_hermiteResolventLaplaceTerm_eq_heatKernel]
  unfold hermiteResolventHeatNormIntegrand
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (by positivity) (Real.exp_pos _).le)]

/-- Absolute integrability of the summed heat-kernel norm integrand. -/
theorem integrableOn_hermiteResolventHeatNormIntegrand
    (m : ℕ) (hm : 1 ≤ m) (X Y : ℝ) :
    MeasureTheory.IntegrableOn
      (hermiteResolventHeatNormIntegrand m X Y) (Set.Ioi 0) := by
  let μ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))
  let F : ℕ → ℝ → ℂ := fun n t ↦
    hermiteResolventLaplaceTerm m X Y n t
  have hFint : ∀ n : ℕ, MeasureTheory.Integrable (F n) μ := by
    intro n
    exact integrableOn_hermiteResolventLaplaceTerm m X Y n
  have hsum : Summable (fun n : ℕ ↦ ∫ t, ‖F n t‖ ∂μ) := by
    simpa only [F, μ] using
      summable_integral_norm_hermiteResolventLaplaceTerm m hm X Y
  have hsum_nonneg : ∀ n : ℕ, 0 ≤ ∫ t, ‖F n t‖ ∂μ := by
    intro n
    exact MeasureTheory.integral_nonneg (fun t ↦ norm_nonneg (F n t))
  have hlintegral :
      (∫⁻ t, ∑' n : ℕ, ‖F n t‖ₑ ∂μ) < ⊤ := by
    rw [MeasureTheory.lintegral_tsum
      (fun n ↦ (hFint n).aestronglyMeasurable.enorm)]
    calc
      (∑' n : ℕ, ∫⁻ t, ‖F n t‖ₑ ∂μ) =
          ∑' n : ℕ, ENNReal.ofReal (∫ t, ‖F n t‖ ∂μ) := by
        apply tsum_congr
        intro n
        exact (MeasureTheory.ofReal_integral_norm_eq_lintegral_enorm
          (hFint n)).symm
      _ = ENNReal.ofReal (∑' n : ℕ, ∫ t, ‖F n t‖ ∂μ) :=
        (ENNReal.ofReal_tsum_of_nonneg hsum_nonneg hsum).symm
      _ < ⊤ := by simp
  refine ⟨?_, ?_⟩
  · change MeasureTheory.AEStronglyMeasurable
      (hermiteResolventHeatNormIntegrand m X Y) μ
    let g : ℝ → ℝ := fun t ↦
      t ^ ((2 * m : ℕ) - 1) * Real.exp (-t) *
        ‖(normalizedHermiteMehlerClosed (Real.exp (-t)) X Y : ℂ)‖
    have hg : MeasureTheory.AEStronglyMeasurable g μ := by
      change MeasureTheory.AEStronglyMeasurable
        (fun t : ℝ ↦
          t ^ ((2 * m : ℕ) - 1) * Real.exp (-t) *
            ‖(normalizedHermiteMehlerClosed (Real.exp (-t)) X Y : ℂ)‖) μ
      unfold normalizedHermiteMehlerClosed
      fun_prop
    apply hg.congr
    filter_upwards [MeasureTheory.ae_restrict_mem
      (μ := MeasureTheory.volume) measurableSet_Ioi] with t ht
    unfold g hermiteResolventHeatNormIntegrand
    rw [hermiteHeatKernel_eq_closed ht]
  · rw [MeasureTheory.hasFiniteIntegral_iff_enorm]
    apply lt_of_le_of_lt _ hlintegral
    apply MeasureTheory.lintegral_mono_ae
    filter_upwards [MeasureTheory.ae_restrict_mem
      (μ := MeasureTheory.volume) measurableSet_Ioi] with t ht
    have heq := hermiteResolventHeatNormIntegrand_eq_norm_tsum m X Y ht
    calc
      ‖hermiteResolventHeatNormIntegrand m X Y t‖ₑ =
          ‖∑' n : ℕ, F n t‖ₑ := by
        rw [Real.enorm_eq_ofReal
          (hermiteResolventHeatNormIntegrand_nonneg m X Y ht.le)]
        rw [← ofReal_norm]
        congr 1
      _ ≤ ∑' n : ℕ, ‖F n t‖ₑ := enorm_tsum_le_tsum_enorm

/-- On the small-time interval, the refined norm integrand is bounded by an
exact Gamma density with shape `2m - 1/2`. -/
theorem hermiteResolventHeatNormIntegrand_le_smallTimeGamma
    (m : ℕ) (hm : 1 ≤ m) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (X Y : ℝ) :
    hermiteResolventHeatNormIntegrand m X Y t ≤
      smallTimeMehlerPrefactorConstant *
        Real.exp (-(Real.pi / 2) * |X * abs X - Y * abs Y|) *
        (t ^ (hermiteResolventHalfShape m - 1) *
          Real.exp (-((1 + mehlerSpatialDamping * (X ^ 2 + Y ^ 2)) * t))) := by
  let p : ℕ := (2 * m : ℕ) - 1
  let D : ℝ := |X * abs X - Y * abs Y|
  let S : ℝ := X ^ 2 + Y ^ 2
  have hpref := mehlerPrefactor_le_smallTimeConstant_div_sqrt ht ht1
  have hheat :=
    norm_hermiteHeatKernel_le_signedSquare_mul_minTimeSpatial ht X Y
  have hmin : min t 1 = t := min_eq_left ht1
  have hpow :
      t ^ p / Real.sqrt t =
        t ^ (hermiteResolventHalfShape m - 1) := by
    rw [natPow_div_sqrt_eq_rpow_sub_half p ht]
    unfold p hermiteResolventHalfShape
    congr 1
    rw [Nat.cast_sub (by omega : 1 ≤ 2 * m)]
    push_cast
    ring
  have hheat' :
      ‖hermiteHeatKernel t X Y‖ ≤
        smallTimeMehlerPrefactorConstant / Real.sqrt t *
          Real.exp (-(Real.pi / 2) * D) *
          Real.exp (-mehlerSpatialDamping * t * S) := by
    calc
      ‖hermiteHeatKernel t X Y‖ ≤
          Real.sqrt 2 / Real.sqrt (1 - Real.exp (-t) ^ 2) *
            Real.exp (-(Real.pi / 2) * D) *
            Real.exp
              (-(Real.pi / 2) * (Real.exp (-1) / 2) * min t 1 * S) := by
        simpa only [D, S] using hheat
      _ ≤ smallTimeMehlerPrefactorConstant / Real.sqrt t *
            Real.exp (-(Real.pi / 2) * D) *
            Real.exp
              (-(Real.pi / 2) * (Real.exp (-1) / 2) * min t 1 * S) := by
        gcongr
      _ = smallTimeMehlerPrefactorConstant / Real.sqrt t *
            Real.exp (-(Real.pi / 2) * D) *
            Real.exp (-mehlerSpatialDamping * t * S) := by
        rw [hmin]
        unfold mehlerSpatialDamping
        ring_nf
  unfold hermiteResolventHeatNormIntegrand
  change t ^ p * Real.exp (-t) * ‖hermiteHeatKernel t X Y‖ ≤ _
  calc
    t ^ p * Real.exp (-t) * ‖hermiteHeatKernel t X Y‖ ≤
        t ^ p * Real.exp (-t) *
          (smallTimeMehlerPrefactorConstant / Real.sqrt t *
            Real.exp (-(Real.pi / 2) * D) *
            Real.exp (-mehlerSpatialDamping * t * S)) := by
      gcongr
    _ = smallTimeMehlerPrefactorConstant *
          Real.exp (-(Real.pi / 2) * D) *
          ((t ^ p / Real.sqrt t) *
            (Real.exp (-t) * Real.exp (-mehlerSpatialDamping * t * S))) := by
      ring
    _ = smallTimeMehlerPrefactorConstant *
          Real.exp (-(Real.pi / 2) * D) *
          (t ^ (hermiteResolventHalfShape m - 1) *
            Real.exp (-((1 + mehlerSpatialDamping * S) * t))) := by
      rw [hpow, ← Real.exp_add]
      congr 3
      ring
    _ = smallTimeMehlerPrefactorConstant *
          Real.exp (-(Real.pi / 2) *
            |X * abs X - Y * abs Y|) *
          (t ^ (hermiteResolventHalfShape m - 1) *
            Real.exp
              (-((1 + mehlerSpatialDamping * (X ^ 2 + Y ^ 2)) * t))) := by
      rfl

/-- Integrability of the exact small-time Gamma majorant. -/
theorem integrableOn_hermiteSmallTimeGammaDensity
    (m : ℕ) (hm : 1 ≤ m) (X Y : ℝ) :
    MeasureTheory.IntegrableOn
      (fun t : ℝ ↦
        t ^ (hermiteResolventHalfShape m - 1) *
          Real.exp
            (-((1 + mehlerSpatialDamping * (X ^ 2 + Y ^ 2)) * t)))
      (Set.Ioi 0) := by
  have hs : (-1 : ℝ) < hermiteResolventHalfShape m - 1 := by
    linarith [hermiteResolventHalfShape_pos hm]
  have hb : 0 < 1 + mehlerSpatialDamping * (X ^ 2 + Y ^ 2) := by
    have ha := mehlerSpatialDamping_pos
    positivity
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow
    (p := (1 : ℝ)) (s := hermiteResolventHalfShape m - 1)
    (b := 1 + mehlerSpatialDamping * (X ^ 2 + Y ^ 2))
    hs zero_lt_one hb
  convert h using 1
  ext t
  simp only [Real.rpow_one]
  congr 2
  ring

/-- Exact full-half-line integral of the small-time Gamma majorant. -/
theorem integral_hermiteSmallTimeGammaDensity
    (m : ℕ) (hm : 1 ≤ m) (X Y : ℝ) :
    (∫ t : ℝ in Set.Ioi 0,
        t ^ (hermiteResolventHalfShape m - 1) *
          Real.exp
            (-((1 + mehlerSpatialDamping * (X ^ 2 + Y ^ 2)) * t))) =
      (1 / (1 + mehlerSpatialDamping * (X ^ 2 + Y ^ 2))) ^
          hermiteResolventHalfShape m *
        Real.Gamma (hermiteResolventHalfShape m) := by
  have hs := hermiteResolventHalfShape_pos hm
  have hb : 0 < 1 + mehlerSpatialDamping * (X ^ 2 + Y ^ 2) := by
    have ha := mehlerSpatialDamping_pos
    positivity
  simpa only using
    (Real.integral_rpow_mul_exp_neg_mul_Ioi hs hb)

/-- Integrated small-time contribution, already carrying signed-square
Gaussian decay and the sharp spatial power. -/
theorem integral_Ioc_hermiteResolventHeatNormIntegrand_le_smallTime
    (m : ℕ) (hm : 1 ≤ m) (X Y : ℝ) :
    (∫ t : ℝ in Set.Ioc 0 1,
        hermiteResolventHeatNormIntegrand m X Y t) ≤
      smallTimeMehlerPrefactorConstant *
        Real.exp (-(Real.pi / 2) * |X * abs X - Y * abs Y|) *
        ((1 / (1 + mehlerSpatialDamping * (X ^ 2 + Y ^ 2))) ^
            hermiteResolventHalfShape m *
          Real.Gamma (hermiteResolventHalfShape m)) := by
  let g : ℝ → ℝ := fun t ↦
    t ^ (hermiteResolventHalfShape m - 1) *
      Real.exp
        (-((1 + mehlerSpatialDamping * (X ^ 2 + Y ^ 2)) * t))
  let C : ℝ := smallTimeMehlerPrefactorConstant *
    Real.exp (-(Real.pi / 2) * |X * abs X - Y * abs Y|)
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg smallTimeMehlerPrefactorConstant_pos.le
      (Real.exp_pos _).le
  have hf : MeasureTheory.IntegrableOn
      (hermiteResolventHeatNormIntegrand m X Y) (Set.Ioc 0 1) :=
    (integrableOn_hermiteResolventHeatNormIntegrand m hm X Y).mono_set
      (by intro t ht; exact ht.1)
  have hgFull : MeasureTheory.IntegrableOn g (Set.Ioi 0) := by
    simpa only [g] using integrableOn_hermiteSmallTimeGammaDensity m hm X Y
  have hg : MeasureTheory.IntegrableOn (fun t ↦ C * g t) (Set.Ioc 0 1) :=
    (hgFull.mono_set (by intro t ht; exact ht.1)).const_mul C
  have hpoint : ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      hermiteResolventHeatNormIntegrand m X Y t ≤ C * g t := by
    intro t ht
    simpa only [C, g] using
      hermiteResolventHeatNormIntegrand_le_smallTimeGamma m hm ht.1 ht.2 X Y
  have hmono :
      (∫ t : ℝ in Set.Ioc 0 1,
          hermiteResolventHeatNormIntegrand m X Y t) ≤
        ∫ t : ℝ in Set.Ioc 0 1, C * g t := by
    exact MeasureTheory.setIntegral_mono_on hf hg measurableSet_Ioc hpoint
  have hsub :
      (∫ t : ℝ in Set.Ioc 0 1, C * g t) ≤
        ∫ t : ℝ in Set.Ioi 0, C * g t := by
    apply MeasureTheory.setIntegral_mono_set (hgFull.const_mul C)
    · filter_upwards [MeasureTheory.ae_restrict_mem
        (μ := MeasureTheory.volume) measurableSet_Ioi] with t ht
      exact mul_nonneg hC (by
        dsimp [g]
        exact mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_pos _).le)
    · exact Filter.Eventually.of_forall (by
        intro t ht
        exact ht.1)
  calc
    (∫ t : ℝ in Set.Ioc 0 1,
        hermiteResolventHeatNormIntegrand m X Y t) ≤
        ∫ t : ℝ in Set.Ioc 0 1, C * g t := hmono
    _ ≤ ∫ t : ℝ in Set.Ioi 0, C * g t := hsub
    _ = C * ∫ t : ℝ in Set.Ioi 0, g t := by
      rw [MeasureTheory.integral_const_mul]
    _ = smallTimeMehlerPrefactorConstant *
          Real.exp (-(Real.pi / 2) * |X * abs X - Y * abs Y|) *
          ((1 / (1 + mehlerSpatialDamping * (X ^ 2 + Y ^ 2))) ^
              hermiteResolventHalfShape m *
            Real.Gamma (hermiteResolventHalfShape m)) := by
      rw [integral_hermiteSmallTimeGammaDensity m hm X Y]

/-- Large-time pointwise contribution.  Here the Mehler prefactor is
nonsingular and the spatial damping is a fixed Gaussian. -/
theorem hermiteResolventHeatNormIntegrand_le_largeTime
    (m : ℕ) {t : ℝ} (ht1 : 1 ≤ t) (X Y : ℝ) :
    hermiteResolventHeatNormIntegrand m X Y t ≤
      largeTimeMehlerPrefactorConstant *
        Real.exp (-(Real.pi / 2) * |X * abs X - Y * abs Y|) *
        Real.exp (-mehlerSpatialDamping * (X ^ 2 + Y ^ 2)) *
        (t ^ ((2 * m : ℕ) - 1) * Real.exp (-t)) := by
  have ht : 0 < t := zero_lt_one.trans_le ht1
  have hpref := mehlerPrefactor_le_largeTimeConstant ht1
  have hheat :=
    norm_hermiteHeatKernel_le_signedSquare_mul_minTimeSpatial ht X Y
  have hmin : min t 1 = 1 := min_eq_right ht1
  have hheat' :
      ‖hermiteHeatKernel t X Y‖ ≤
        largeTimeMehlerPrefactorConstant *
          Real.exp (-(Real.pi / 2) * |X * abs X - Y * abs Y|) *
          Real.exp (-mehlerSpatialDamping * (X ^ 2 + Y ^ 2)) := by
    calc
      ‖hermiteHeatKernel t X Y‖ ≤
          Real.sqrt 2 / Real.sqrt (1 - Real.exp (-t) ^ 2) *
            Real.exp (-(Real.pi / 2) * |X * abs X - Y * abs Y|) *
            Real.exp
              (-(Real.pi / 2) * (Real.exp (-1) / 2) * min t 1 *
                (X ^ 2 + Y ^ 2)) := hheat
      _ ≤ largeTimeMehlerPrefactorConstant *
            Real.exp (-(Real.pi / 2) * |X * abs X - Y * abs Y|) *
            Real.exp
              (-(Real.pi / 2) * (Real.exp (-1) / 2) * min t 1 *
                (X ^ 2 + Y ^ 2)) := by
        gcongr
      _ = largeTimeMehlerPrefactorConstant *
            Real.exp (-(Real.pi / 2) * |X * abs X - Y * abs Y|) *
            Real.exp (-mehlerSpatialDamping * (X ^ 2 + Y ^ 2)) := by
        rw [hmin]
        unfold mehlerSpatialDamping
        ring_nf
  unfold hermiteResolventHeatNormIntegrand
  calc
    t ^ ((2 * m : ℕ) - 1) * Real.exp (-t) *
          ‖hermiteHeatKernel t X Y‖ ≤
        t ^ ((2 * m : ℕ) - 1) * Real.exp (-t) *
          (largeTimeMehlerPrefactorConstant *
            Real.exp (-(Real.pi / 2) * |X * abs X - Y * abs Y|) *
            Real.exp (-mehlerSpatialDamping * (X ^ 2 + Y ^ 2))) := by
      gcongr
    _ = largeTimeMehlerPrefactorConstant *
          Real.exp (-(Real.pi / 2) * |X * abs X - Y * abs Y|) *
          Real.exp (-mehlerSpatialDamping * (X ^ 2 + Y ^ 2)) *
          (t ^ ((2 * m : ℕ) - 1) * Real.exp (-t)) := by ring

theorem integral_Ioi_one_hermiteResolventHeatNormIntegrand_le_largeTime
    (m : ℕ) (hm : 1 ≤ m) (X Y : ℝ) :
    (∫ t : ℝ in Set.Ioi 1,
        hermiteResolventHeatNormIntegrand m X Y t) ≤
      largeTimeMehlerPrefactorConstant *
        Real.exp (-(Real.pi / 2) * |X * abs X - Y * abs Y|) *
        Real.exp (-mehlerSpatialDamping * (X ^ 2 + Y ^ 2)) *
        ((2 * m - 1).factorial : ℝ) := by
  let q : ℝ := largeTimeMehlerPrefactorConstant *
    Real.exp (-(Real.pi / 2) * |X * abs X - Y * abs Y|) *
    Real.exp (-mehlerSpatialDamping * (X ^ 2 + Y ^ 2))
  let g : ℝ → ℝ := fun t ↦
    t ^ ((2 * m : ℕ) - 1) * Real.exp (-t)
  have hq : 0 ≤ q := by
    dsimp [q]
    exact mul_nonneg
      (mul_nonneg largeTimeMehlerPrefactorConstant_pos.le
        (Real.exp_pos _).le)
      (Real.exp_pos _).le
  have hf : MeasureTheory.IntegrableOn
      (hermiteResolventHeatNormIntegrand m X Y) (Set.Ioi 1) :=
    (integrableOn_hermiteResolventHeatNormIntegrand m hm X Y).mono_set
      (by intro t ht; exact zero_lt_one.trans (show (1 : ℝ) < t from ht))
  have hgFull : MeasureTheory.IntegrableOn g (Set.Ioi 0) := by
    have h := integrableOn_hermiteLaplaceDensity m 0
    refine h.congr_fun ?_ measurableSet_Ioi
    intro t ht
    unfold g hermiteLaplaceDensity
    norm_num
  have hqg : MeasureTheory.IntegrableOn (fun t ↦ q * g t) (Set.Ioi 1) :=
    (hgFull.mono_set (by
      intro t ht
      exact zero_lt_one.trans (show (1 : ℝ) < t from ht))).const_mul q
  have hpoint : ∀ t ∈ Set.Ioi (1 : ℝ),
      hermiteResolventHeatNormIntegrand m X Y t ≤ q * g t := by
    intro t ht
    simpa only [q, g] using
      hermiteResolventHeatNormIntegrand_le_largeTime m ht.le X Y
  have hmono :
      (∫ t : ℝ in Set.Ioi 1,
          hermiteResolventHeatNormIntegrand m X Y t) ≤
        ∫ t : ℝ in Set.Ioi 1, q * g t :=
    MeasureTheory.setIntegral_mono_on hf hqg measurableSet_Ioi hpoint
  have hsub :
      (∫ t : ℝ in Set.Ioi 1, q * g t) ≤
        ∫ t : ℝ in Set.Ioi 0, q * g t := by
    apply MeasureTheory.setIntegral_mono_set (hgFull.const_mul q)
    · filter_upwards [MeasureTheory.ae_restrict_mem
        (μ := MeasureTheory.volume) measurableSet_Ioi] with t ht
      exact mul_nonneg hq (by
        dsimp [g]
        exact mul_nonneg (pow_nonneg ht.le _) (Real.exp_pos _).le)
    · exact Filter.Eventually.of_forall (by
        intro t ht
        exact zero_lt_one.trans ht)
  have hgIntegral :
      (∫ t : ℝ in Set.Ioi 0, g t) = ((2 * m - 1).factorial : ℝ) := by
    have h := hermiteScaleWeight_laplace m hm 0
    simpa only [g, Nat.cast_zero, zero_add, one_mul, inv_one, one_pow,
      mul_one] using h
  calc
    (∫ t : ℝ in Set.Ioi 1,
        hermiteResolventHeatNormIntegrand m X Y t) ≤
        ∫ t : ℝ in Set.Ioi 1, q * g t := hmono
    _ ≤ ∫ t : ℝ in Set.Ioi 0, q * g t := hsub
    _ = q * ∫ t : ℝ in Set.Ioi 0, g t := by
      rw [MeasureTheory.integral_const_mul]
    _ = q * ((2 * m - 1).factorial : ℝ) := by rw [hgIntegral]
    _ = largeTimeMehlerPrefactorConstant *
          Real.exp (-(Real.pi / 2) * |X * abs X - Y * abs Y|) *
          Real.exp (-mehlerSpatialDamping * (X ^ 2 + Y ^ 2)) *
          ((2 * m - 1).factorial : ℝ) := by rfl

/-- Full positive-half-line raw heat-norm estimate, split into its sharp
small-time power and exponentially smaller large-time contribution. -/
theorem integral_hermiteResolventHeatNormIntegrand_le
    (m : ℕ) (hm : 1 ≤ m) (X Y : ℝ) :
    (∫ t : ℝ in Set.Ioi 0,
        hermiteResolventHeatNormIntegrand m X Y t) ≤
      Real.exp (-(Real.pi / 2) * |X * abs X - Y * abs Y|) *
        (smallTimeMehlerPrefactorConstant *
            ((1 / (1 + mehlerSpatialDamping * (X ^ 2 + Y ^ 2))) ^
                hermiteResolventHalfShape m *
              Real.Gamma (hermiteResolventHalfShape m)) +
          largeTimeMehlerPrefactorConstant *
            Real.exp (-mehlerSpatialDamping * (X ^ 2 + Y ^ 2)) *
              ((2 * m - 1).factorial : ℝ)) := by
  let f := hermiteResolventHeatNormIntegrand m X Y
  have hf := integrableOn_hermiteResolventHeatNormIntegrand m hm X Y
  have hsplit :
      (∫ t : ℝ in Set.Ioi 0, f t) =
        (∫ t : ℝ in Set.Ioc 0 1, f t) +
          ∫ t : ℝ in Set.Ioi 1, f t := by
    rw [← MeasureTheory.setIntegral_union Set.Ioc_disjoint_Ioi_same
      measurableSet_Ioi (hf.mono_set Set.Ioc_subset_Ioi_self)
      (hf.mono_set (Set.Ioi_subset_Ioi zero_le_one)),
      Set.Ioc_union_Ioi_eq_Ioi zero_le_one]
  have hsmall :=
    integral_Ioc_hermiteResolventHeatNormIntegrand_le_smallTime m hm X Y
  have hlarge :=
    integral_Ioi_one_hermiteResolventHeatNormIntegrand_le_largeTime m hm X Y
  rw [hsplit]
  calc
    (∫ t : ℝ in Set.Ioc 0 1, f t) + ∫ t : ℝ in Set.Ioi 1, f t ≤
        smallTimeMehlerPrefactorConstant *
            Real.exp (-(Real.pi / 2) * |X * abs X - Y * abs Y|) *
            ((1 / (1 + mehlerSpatialDamping * (X ^ 2 + Y ^ 2))) ^
                hermiteResolventHalfShape m *
              Real.Gamma (hermiteResolventHalfShape m)) +
          largeTimeMehlerPrefactorConstant *
            Real.exp (-(Real.pi / 2) * |X * abs X - Y * abs Y|) *
            Real.exp (-mehlerSpatialDamping * (X ^ 2 + Y ^ 2)) *
              ((2 * m - 1).factorial : ℝ) := by
      exact add_le_add hsmall hlarge
    _ = Real.exp (-(Real.pi / 2) * |X * abs X - Y * abs Y|) *
        (smallTimeMehlerPrefactorConstant *
            ((1 / (1 + mehlerSpatialDamping * (X ^ 2 + Y ^ 2))) ^
                hermiteResolventHalfShape m *
              Real.Gamma (hermiteResolventHalfShape m)) +
          largeTimeMehlerPrefactorConstant *
            Real.exp (-mehlerSpatialDamping * (X ^ 2 + Y ^ 2)) *
              ((2 * m - 1).factorial : ℝ)) := by ring

/-- The genuine raw Hermite resolvent kernel inherits the integrated refined
Mehler estimate. -/
theorem norm_hermiteResolventKernel_le_refined
    (m : ℕ) (hm : 1 ≤ m) (X Y : ℝ) :
    ‖hermiteResolventKernel m X Y‖ ≤
      ((2 * m - 1).factorial : ℝ)⁻¹ *
        Real.exp (-(Real.pi / 2) * |X * abs X - Y * abs Y|) *
        (smallTimeMehlerPrefactorConstant *
            ((1 / (1 + mehlerSpatialDamping * (X ^ 2 + Y ^ 2))) ^
                hermiteResolventHalfShape m *
              Real.Gamma (hermiteResolventHalfShape m)) +
          largeTimeMehlerPrefactorConstant *
            Real.exp (-mehlerSpatialDamping * (X ^ 2 + Y ^ 2)) *
              ((2 * m - 1).factorial : ℝ)) := by
  let F : ℝ := ((2 * m - 1).factorial : ℝ)
  let u : ℝ → ℂ := fun t ↦
    (((t ^ ((2 * m : ℕ) - 1) * Real.exp (-t) : ℝ) : ℂ)) *
      hermiteHeatKernel t X Y
  have hFinv : 0 ≤ F⁻¹ := by
    dsimp [F]
    positivity
  have hnormIntegral :
      ‖∫ t : ℝ in Set.Ioi 0, u t‖ ≤
        ∫ t : ℝ in Set.Ioi 0, ‖u t‖ :=
    MeasureTheory.norm_integral_le_integral_norm _
  have hnormEq :
      (∫ t : ℝ in Set.Ioi 0, ‖u t‖) =
        ∫ t : ℝ in Set.Ioi 0,
          hermiteResolventHeatNormIntegrand m X Y t := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp [u]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (pow_nonneg ht.le _) (Real.exp_pos _).le)]
    rfl
  have hraw := integral_hermiteResolventHeatNormIntegrand_le m hm X Y
  rw [hermiteResolventKernel_eq_laplaceIntegral m hm X Y]
  change ‖((F⁻¹ : ℝ) : ℂ) * ∫ t : ℝ in Set.Ioi 0, u t‖ ≤ _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hFinv]
  calc
    F⁻¹ * ‖∫ t : ℝ in Set.Ioi 0, u t‖ ≤
        F⁻¹ * ∫ t : ℝ in Set.Ioi 0, ‖u t‖ := by
      gcongr
    _ = F⁻¹ * ∫ t : ℝ in Set.Ioi 0,
          hermiteResolventHeatNormIntegrand m X Y t := by rw [hnormEq]
    _ ≤ F⁻¹ *
        (Real.exp (-(Real.pi / 2) * |X * abs X - Y * abs Y|) *
          (smallTimeMehlerPrefactorConstant *
              ((1 / (1 + mehlerSpatialDamping * (X ^ 2 + Y ^ 2))) ^
                  hermiteResolventHalfShape m *
                Real.Gamma (hermiteResolventHalfShape m)) +
            largeTimeMehlerPrefactorConstant *
              Real.exp (-mehlerSpatialDamping * (X ^ 2 + Y ^ 2)) *
                ((2 * m - 1).factorial : ℝ))) := by
      gcongr
    _ = ((2 * m - 1).factorial : ℝ)⁻¹ *
        Real.exp (-(Real.pi / 2) * |X * abs X - Y * abs Y|) *
        (smallTimeMehlerPrefactorConstant *
            ((1 / (1 + mehlerSpatialDamping * (X ^ 2 + Y ^ 2))) ^
                hermiteResolventHalfShape m *
              Real.Gamma (hermiteResolventHalfShape m)) +
          largeTimeMehlerPrefactorConstant *
            Real.exp (-mehlerSpatialDamping * (X ^ 2 + Y ^ 2)) *
              ((2 * m - 1).factorial : ℝ)) := by
      dsimp [F]
      ring

/-- A common positive spatial coefficient for both time regimes.  Dividing
by `shape + 1` makes the elementary exponential-to-power comparison exact. -/
def hermiteNormalizedSpatialCoefficient (m : ℕ) : ℝ :=
  mehlerSpatialDamping / (hermiteResolventHalfShape m + 1)

theorem hermiteNormalizedSpatialCoefficient_pos
    {m : ℕ} (hm : 1 ≤ m) :
    0 < hermiteNormalizedSpatialCoefficient m := by
  unfold hermiteNormalizedSpatialCoefficient
  exact div_pos mehlerSpatialDamping_pos (by
    linarith [hermiteResolventHalfShape_pos hm])

theorem hermiteNormalizedSpatialCoefficient_le_damping
    {m : ℕ} (hm : 1 ≤ m) :
    hermiteNormalizedSpatialCoefficient m ≤ mehlerSpatialDamping := by
  have hq := hermiteResolventHalfShape_pos hm
  unfold hermiteNormalizedSpatialCoefficient
  rw [div_le_iff₀ (by linarith : 0 < hermiteResolventHalfShape m + 1)]
  nlinarith [mehlerSpatialDamping_pos]

theorem hermiteNormalizedSpatialCoefficient_mul_shape_le_damping
    {m : ℕ} (hm : 1 ≤ m) :
    hermiteNormalizedSpatialCoefficient m *
        hermiteResolventHalfShape m ≤ mehlerSpatialDamping := by
  have hq := hermiteResolventHalfShape_pos hm
  unfold hermiteNormalizedSpatialCoefficient
  rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith :
    0 < hermiteResolventHalfShape m + 1)]
  nlinarith [mehlerSpatialDamping_pos]

/-- The small-time spatial power is dominated by the common normalization
power. -/
theorem smallTimeSpatialPower_le_normalizedSpatialPower
    (m : ℕ) (hm : 1 ≤ m) (X Y : ℝ) :
    (1 / (1 + mehlerSpatialDamping * (X ^ 2 + Y ^ 2))) ^
        hermiteResolventHalfShape m ≤
      (1 / (1 + hermiteNormalizedSpatialCoefficient m *
        (X ^ 2 + Y ^ 2))) ^ hermiteResolventHalfShape m := by
  have hS : 0 ≤ X ^ 2 + Y ^ 2 := by positivity
  have hc := hermiteNormalizedSpatialCoefficient_le_damping hm
  have hden :
      1 + hermiteNormalizedSpatialCoefficient m * (X ^ 2 + Y ^ 2) ≤
        1 + mehlerSpatialDamping * (X ^ 2 + Y ^ 2) := by
    gcongr
  have hinv :
      1 / (1 + mehlerSpatialDamping * (X ^ 2 + Y ^ 2)) ≤
        1 / (1 + hermiteNormalizedSpatialCoefficient m *
          (X ^ 2 + Y ^ 2)) := by
    apply one_div_le_one_div_of_le
    · have hcpos := hermiteNormalizedSpatialCoefficient_pos hm
      positivity
    · exact hden
  have hbase0 :
      0 ≤ 1 / (1 + mehlerSpatialDamping * (X ^ 2 + Y ^ 2)) := by
    exact one_div_nonneg.mpr (by
      have ha := mehlerSpatialDamping_pos
      positivity)
  exact Real.rpow_le_rpow hbase0 hinv
    (hermiteResolventHalfShape_pos hm).le

/-- The fixed large-time Gaussian is also dominated by the same spatial
power, by `1 + z ≤ exp z` raised to the positive half-integer shape. -/
theorem exp_neg_spatial_le_normalizedSpatialPower
    (m : ℕ) (hm : 1 ≤ m) (X Y : ℝ) :
    Real.exp (-mehlerSpatialDamping * (X ^ 2 + Y ^ 2)) ≤
      (1 / (1 + hermiteNormalizedSpatialCoefficient m *
        (X ^ 2 + Y ^ 2))) ^ hermiteResolventHalfShape m := by
  let q := hermiteResolventHalfShape m
  let c := hermiteNormalizedSpatialCoefficient m
  let S := X ^ 2 + Y ^ 2
  have hq : 0 < q := hermiteResolventHalfShape_pos hm
  have hc : 0 < c := hermiteNormalizedSpatialCoefficient_pos hm
  have hS : 0 ≤ S := by
    dsimp [S]
    positivity
  have hbase : 1 + c * S ≤ Real.exp (c * S) := by
    simpa only [add_comm] using Real.add_one_le_exp (c * S)
  have hrpow :
      (1 + c * S) ^ q ≤ Real.exp (mehlerSpatialDamping * S) := by
    calc
      (1 + c * S) ^ q ≤ Real.exp (c * S) ^ q :=
        Real.rpow_le_rpow (by positivity) hbase hq.le
      _ = Real.exp ((c * S) * q) := by
        rw [← Real.exp_mul]
      _ ≤ Real.exp (mehlerSpatialDamping * S) := by
        apply Real.exp_le_exp.mpr
        have hcq :=
          hermiteNormalizedSpatialCoefficient_mul_shape_le_damping hm
        change c * q ≤ mehlerSpatialDamping at hcq
        calc
          c * S * q = (c * q) * S := by ring
          _ ≤ mehlerSpatialDamping * S :=
            mul_le_mul_of_nonneg_right hcq hS
  have hpowpos : 0 < (1 + c * S) ^ q :=
    Real.rpow_pos_of_pos (by positivity) _
  have hexppos : 0 < Real.exp (mehlerSpatialDamping * S) := Real.exp_pos _
  calc
    Real.exp (-mehlerSpatialDamping * (X ^ 2 + Y ^ 2)) =
        (Real.exp (mehlerSpatialDamping * S))⁻¹ := by
      rw [show -mehlerSpatialDamping * (X ^ 2 + Y ^ 2) =
        -(mehlerSpatialDamping * S) by dsimp [S]; ring]
      rw [Real.exp_neg]
    _ ≤ ((1 + c * S) ^ q)⁻¹ :=
      (inv_le_inv₀ hexppos hpowpos).2 hrpow
    _ = (1 / (1 + c * S)) ^ q := by
      rw [one_div, Real.inv_rpow (by positivity : 0 ≤ 1 + c * S)]
    _ = (1 / (1 + hermiteNormalizedSpatialCoefficient m *
        (X ^ 2 + Y ^ 2))) ^ hermiteResolventHalfShape m := by rfl

/-- Refined raw resolvent estimate with a single spatial power. -/
theorem norm_hermiteResolventKernel_le_normalizedSpatialPower
    (m : ℕ) (hm : 1 ≤ m) (X Y : ℝ) :
    ‖hermiteResolventKernel m X Y‖ ≤
      (((2 * m - 1).factorial : ℝ)⁻¹ *
        (smallTimeMehlerPrefactorConstant *
            Real.Gamma (hermiteResolventHalfShape m) +
          largeTimeMehlerPrefactorConstant *
            ((2 * m - 1).factorial : ℝ))) *
        Real.exp (-(Real.pi / 2) * |X * abs X - Y * abs Y|) *
        (1 / (1 + hermiteNormalizedSpatialCoefficient m *
          (X ^ 2 + Y ^ 2))) ^ hermiteResolventHalfShape m := by
  have hsmall := smallTimeSpatialPower_le_normalizedSpatialPower m hm X Y
  have hlarge := exp_neg_spatial_le_normalizedSpatialPower m hm X Y
  have hGamma : 0 ≤ Real.Gamma (hermiteResolventHalfShape m) :=
    (Real.Gamma_pos_of_pos (hermiteResolventHalfShape_pos hm)).le
  have hfact : 0 ≤ ((2 * m - 1).factorial : ℝ) := by positivity
  have hsmallC : 0 ≤ smallTimeMehlerPrefactorConstant :=
    smallTimeMehlerPrefactorConstant_pos.le
  have hlargeC : 0 ≤ largeTimeMehlerPrefactorConstant :=
    largeTimeMehlerPrefactorConstant_pos.le
  have hraw := norm_hermiteResolventKernel_le_refined m hm X Y
  refine hraw.trans ?_
  have hbracket :
      smallTimeMehlerPrefactorConstant *
            ((1 / (1 + mehlerSpatialDamping * (X ^ 2 + Y ^ 2))) ^
                hermiteResolventHalfShape m *
              Real.Gamma (hermiteResolventHalfShape m)) +
          largeTimeMehlerPrefactorConstant *
            Real.exp (-mehlerSpatialDamping * (X ^ 2 + Y ^ 2)) *
              ((2 * m - 1).factorial : ℝ) ≤
        (smallTimeMehlerPrefactorConstant *
            Real.Gamma (hermiteResolventHalfShape m) +
          largeTimeMehlerPrefactorConstant *
            ((2 * m - 1).factorial : ℝ)) *
          (1 / (1 + hermiteNormalizedSpatialCoefficient m *
            (X ^ 2 + Y ^ 2))) ^ hermiteResolventHalfShape m := by
    calc
      smallTimeMehlerPrefactorConstant *
              ((1 / (1 + mehlerSpatialDamping * (X ^ 2 + Y ^ 2))) ^
                  hermiteResolventHalfShape m *
                Real.Gamma (hermiteResolventHalfShape m)) +
            largeTimeMehlerPrefactorConstant *
              Real.exp (-mehlerSpatialDamping * (X ^ 2 + Y ^ 2)) *
                ((2 * m - 1).factorial : ℝ) ≤
          smallTimeMehlerPrefactorConstant *
              ((1 / (1 + hermiteNormalizedSpatialCoefficient m *
                (X ^ 2 + Y ^ 2))) ^ hermiteResolventHalfShape m *
                Real.Gamma (hermiteResolventHalfShape m)) +
            largeTimeMehlerPrefactorConstant *
              (1 / (1 + hermiteNormalizedSpatialCoefficient m *
                (X ^ 2 + Y ^ 2))) ^ hermiteResolventHalfShape m *
                ((2 * m - 1).factorial : ℝ) := by
        gcongr
      _ = (smallTimeMehlerPrefactorConstant *
              Real.Gamma (hermiteResolventHalfShape m) +
            largeTimeMehlerPrefactorConstant *
              ((2 * m - 1).factorial : ℝ)) *
            (1 / (1 + hermiteNormalizedSpatialCoefficient m *
              (X ^ 2 + Y ^ 2))) ^ hermiteResolventHalfShape m := by ring
  have hfinv : 0 ≤ ((2 * m - 1).factorial : ℝ)⁻¹ := by positivity
  have hexp : 0 ≤ Real.exp
      (-(Real.pi / 2) * |X * abs X - Y * abs Y|) := (Real.exp_pos _).le
  calc
    ((2 * m - 1).factorial : ℝ)⁻¹ *
          Real.exp (-(Real.pi / 2) * |X * abs X - Y * abs Y|) *
          (smallTimeMehlerPrefactorConstant *
              ((1 / (1 + mehlerSpatialDamping * (X ^ 2 + Y ^ 2))) ^
                  hermiteResolventHalfShape m *
                Real.Gamma (hermiteResolventHalfShape m)) +
            largeTimeMehlerPrefactorConstant *
              Real.exp (-mehlerSpatialDamping * (X ^ 2 + Y ^ 2)) *
                ((2 * m - 1).factorial : ℝ)) ≤
        ((2 * m - 1).factorial : ℝ)⁻¹ *
          Real.exp (-(Real.pi / 2) * |X * abs X - Y * abs Y|) *
          ((smallTimeMehlerPrefactorConstant *
              Real.Gamma (hermiteResolventHalfShape m) +
            largeTimeMehlerPrefactorConstant *
              ((2 * m - 1).factorial : ℝ)) *
            (1 / (1 + hermiteNormalizedSpatialCoefficient m *
              (X ^ 2 + Y ^ 2))) ^ hermiteResolventHalfShape m) := by
      gcongr
    _ = (((2 * m - 1).factorial : ℝ)⁻¹ *
          (smallTimeMehlerPrefactorConstant *
              Real.Gamma (hermiteResolventHalfShape m) +
            largeTimeMehlerPrefactorConstant *
              ((2 * m - 1).factorial : ℝ))) *
          Real.exp (-(Real.pi / 2) * |X * abs X - Y * abs Y|) *
          (1 / (1 + hermiteNormalizedSpatialCoefficient m *
            (X ^ 2 + Y ^ 2))) ^ hermiteResolventHalfShape m := by ring

/-- Loss incurred when comparing the retained spatial damping with the two
diagonal scales. -/
def hermiteSpatialNormalizationConstant (m : ℕ) : ℝ :=
  ((1 + hermiteNormalizedSpatialCoefficient m) /
      hermiteNormalizedSpatialCoefficient m) ^
    hermiteResolventHalfShape m

theorem hermiteSpatialNormalizationConstant_pos
    {m : ℕ} (hm : 1 ≤ m) :
    0 < hermiteSpatialNormalizationConstant m := by
  unfold hermiteSpatialNormalizationConstant
  have hc := hermiteNormalizedSpatialCoefficient_pos hm
  exact Real.rpow_pos_of_pos (div_pos (by linarith) hc) _

/-- The product of the two quadratic spatial weights is controlled by the
square of their sum weight. -/
theorem sqrt_one_add_sq_mul_one_add_sq_le
    (X Y : ℝ) :
    Real.sqrt ((1 + X ^ 2) * (1 + Y ^ 2)) ≤
      1 + (X ^ 2 + Y ^ 2) := by
  have hright : 0 ≤ 1 + (X ^ 2 + Y ^ 2) := by positivity
  rw [Real.sqrt_le_iff]
  refine ⟨hright, ?_⟩
  rw [← sub_nonneg]
  rw [show
      (1 + (X ^ 2 + Y ^ 2)) ^ 2 -
          (1 + X ^ 2) * (1 + Y ^ 2) =
        X ^ 4 + Y ^ 4 + X ^ 2 + Y ^ 2 + X ^ 2 * Y ^ 2 by ring]
  positivity

private theorem one_div_mul_sqrt_rpow_eq
    {k A B q : ℝ} (hk : 0 < k) (hA : 0 < A) (hB : 0 < B) :
    (1 / (k * Real.sqrt (A * B))) ^ q =
      (1 / k) ^ q * (1 / (A * B)) ^ (q / 2) := by
  have hAB : 0 < A * B := mul_pos hA hB
  have hsqrt : 0 < Real.sqrt (A * B) := Real.sqrt_pos.2 hAB
  calc
    (1 / (k * Real.sqrt (A * B))) ^ q =
        ((1 / k) * (1 / Real.sqrt (A * B))) ^ q := by
      congr 1
      field_simp
    _ = (1 / k) ^ q * (1 / Real.sqrt (A * B)) ^ q := by
      rw [Real.mul_rpow (by positivity) (by positivity)]
    _ = (1 / k) ^ q * (1 / (A * B)) ^ (q / 2) := by
      congr 1
      calc
        (1 / Real.sqrt (A * B)) ^ q =
            (Real.sqrt (A * B) ^ q)⁻¹ := by
          rw [one_div, Real.inv_rpow hsqrt.le]
        _ = ((A * B) ^ (q / 2))⁻¹ := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hAB.le]
          congr 2
          ring
        _ = ((A * B)⁻¹) ^ (q / 2) := by
          rw [Real.inv_rpow hAB.le]
        _ = (1 / (A * B)) ^ (q / 2) := by rw [one_div]

/-- The common spatial power has exactly the product scale needed to cancel
the two sharp diagonal norm floors. -/
theorem normalizedSpatialPower_le_diagonalScales
    (m : ℕ) (hm : 1 ≤ m) (X Y : ℝ) :
    (1 / (1 + hermiteNormalizedSpatialCoefficient m *
        (X ^ 2 + Y ^ 2))) ^ hermiteResolventHalfShape m ≤
      hermiteSpatialNormalizationConstant m *
        (hermiteDiagonalScale X * hermiteDiagonalScale Y) ^
          (hermiteResolventHalfShape m / 2) := by
  let c := hermiteNormalizedSpatialCoefficient m
  let k := c / (1 + c)
  let A := 1 + X ^ 2
  let B := 1 + Y ^ 2
  let S := X ^ 2 + Y ^ 2
  let q := hermiteResolventHalfShape m
  have hc : 0 < c := hermiteNormalizedSpatialCoefficient_pos hm
  have hk : 0 < k := by
    dsimp [k]
    positivity
  have hA : 0 < A := by
    dsimp [A]
    positivity
  have hB : 0 < B := by
    dsimp [B]
    positivity
  have hS : 0 ≤ S := by
    dsimp [S]
    positivity
  have hq : 0 < q := hermiteResolventHalfShape_pos hm
  have hsqrt : Real.sqrt (A * B) ≤ 1 + S := by
    simpa only [A, B, S] using sqrt_one_add_sq_mul_one_add_sq_le X Y
  have hkSum : k * (1 + S) ≤ 1 + c * S := by
    dsimp [k]
    rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith : 0 < 1 + c)]
    nlinarith [sq_nonneg c, mul_nonneg (sq_nonneg c) hS]
  have hden : k * Real.sqrt (A * B) ≤ 1 + c * S :=
    (mul_le_mul_of_nonneg_left hsqrt hk.le).trans hkSum
  have hinv :
      1 / (1 + c * S) ≤ 1 / (k * Real.sqrt (A * B)) := by
    exact one_div_le_one_div_of_le (by positivity) hden
  have hrpow :
      (1 / (1 + c * S)) ^ q ≤
        (1 / (k * Real.sqrt (A * B))) ^ q :=
    Real.rpow_le_rpow (by positivity) hinv hq.le
  calc
    (1 / (1 + hermiteNormalizedSpatialCoefficient m *
          (X ^ 2 + Y ^ 2))) ^ hermiteResolventHalfShape m =
        (1 / (1 + c * S)) ^ q := by rfl
    _ ≤ (1 / (k * Real.sqrt (A * B))) ^ q := hrpow
    _ = (1 / k) ^ q * (1 / (A * B)) ^ (q / 2) :=
      one_div_mul_sqrt_rpow_eq hk hA hB
    _ = hermiteSpatialNormalizationConstant m *
          (hermiteDiagonalScale X * hermiteDiagonalScale Y) ^
            (hermiteResolventHalfShape m / 2) := by
      have hkInv : 1 / k = (1 + c) / c := by
        dsimp [k]
        field_simp
      rw [hkInv]
      unfold hermiteSpatialNormalizationConstant hermiteDiagonalScale
      change ((1 + c) / c) ^ q * (1 / (A * B)) ^ (q / 2) =
        ((1 + c) / c) ^ q *
          (A⁻¹ * B⁻¹) ^ (q / 2)
      congr 1
      congr 1
      field_simp

/-- Constant in the exact power form of the sharp diagonal floor. -/
def hermiteDiagonalFloorConstant (m : ℕ) : ℝ :=
  ((2 * m - 1).factorial : ℝ)⁻¹ *
    Real.exp (-2) * Real.exp (-4 * Real.pi) / Real.sqrt 2

theorem hermiteDiagonalFloorConstant_pos (m : ℕ) :
    0 < hermiteDiagonalFloorConstant m := by
  unfold hermiteDiagonalFloorConstant
  positivity

/-- Exact reformulation of the window floor as the sharp half-integer power
`T^(2m-1/2)`. -/
theorem hermitePointMassDiagonalFloor_eq_rpow
    (m : ℕ) (hm : 1 ≤ m) (X : ℝ) :
    hermitePointMassDiagonalFloor m X =
      hermiteDiagonalFloorConstant m *
        hermiteDiagonalScale X ^ hermiteResolventHalfShape m := by
  let T := hermiteDiagonalScale X
  have hT : 0 < T := hermiteDiagonalScale_pos X
  have hpowNat : T * T ^ ((2 * m : ℕ) - 1) = T ^ (2 * m) := by
    rw [← pow_succ']
    congr 1
    omega
  have hpowReal :
      T ^ (2 * m) / Real.sqrt T =
        T ^ hermiteResolventHalfShape m := by
    simpa only [hermiteResolventHalfShape, Nat.cast_mul, Nat.cast_ofNat] using
      natPow_div_sqrt_eq_rpow_sub_half (2 * m) hT
  unfold hermitePointMassDiagonalFloor hermiteDiagonalWindowFloor
  unfold hermiteDiagonalFloorConstant
  change
    ((2 * m - 1).factorial : ℝ)⁻¹ *
        (T * (T ^ ((2 * m : ℕ) - 1) * Real.exp (-2) *
          (1 / Real.sqrt (2 * T) * Real.exp (-4 * Real.pi)))) =
      ((2 * m - 1).factorial : ℝ)⁻¹ * Real.exp (-2) *
        Real.exp (-4 * Real.pi) / Real.sqrt 2 *
          T ^ hermiteResolventHalfShape m
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  rw [show
      T * (T ^ ((2 * m : ℕ) - 1) * Real.exp (-2) *
          (1 / (Real.sqrt 2 * Real.sqrt T) * Real.exp (-4 * Real.pi))) =
        (T * T ^ ((2 * m : ℕ) - 1)) * Real.exp (-2) *
          (1 / (Real.sqrt 2 * Real.sqrt T) * Real.exp (-4 * Real.pi)) by
    ring]
  rw [hpowNat]
  rw [show
      T ^ (2 * m) * Real.exp (-2) *
          (1 / (Real.sqrt 2 * Real.sqrt T) * Real.exp (-4 * Real.pi)) =
        Real.exp (-2) * Real.exp (-4 * Real.pi) / Real.sqrt 2 *
          (T ^ (2 * m) / Real.sqrt T) by
    field_simp [Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2),
      (Real.sqrt_pos.2 hT).ne']]
  rw [hpowReal]
  ring

/-- The product of two diagonal floors has exactly the spatial power in the
squared raw-kernel estimate. -/
theorem mul_hermitePointMassDiagonalFloor_eq
    (m : ℕ) (hm : 1 ≤ m) (X Y : ℝ) :
    hermitePointMassDiagonalFloor m X *
        hermitePointMassDiagonalFloor m Y =
      hermiteDiagonalFloorConstant m ^ 2 *
        (hermiteDiagonalScale X * hermiteDiagonalScale Y) ^
          hermiteResolventHalfShape m := by
  rw [hermitePointMassDiagonalFloor_eq_rpow m hm X,
    hermitePointMassDiagonalFloor_eq_rpow m hm Y]
  have hTX : 0 ≤ hermiteDiagonalScale X :=
    (hermiteDiagonalScale_pos X).le
  have hTY : 0 ≤ hermiteDiagonalScale Y :=
    (hermiteDiagonalScale_pos Y).le
  rw [Real.mul_rpow hTX hTY]
  ring

/-- Constant in the raw kernel estimate after comparison with the product
of diagonal spatial scales. -/
def hermiteRawNormalizationConstant (m : ℕ) : ℝ :=
  (((2 * m - 1).factorial : ℝ)⁻¹ *
      (smallTimeMehlerPrefactorConstant *
          Real.Gamma (hermiteResolventHalfShape m) +
        largeTimeMehlerPrefactorConstant *
          ((2 * m - 1).factorial : ℝ))) *
    hermiteSpatialNormalizationConstant m

theorem hermiteRawNormalizationConstant_pos
    {m : ℕ} (hm : 1 ≤ m) :
    0 < hermiteRawNormalizationConstant m := by
  unfold hermiteRawNormalizationConstant
  have hGamma := Real.Gamma_pos_of_pos (hermiteResolventHalfShape_pos hm)
  have hsmall := smallTimeMehlerPrefactorConstant_pos
  have hlarge := largeTimeMehlerPrefactorConstant_pos
  have hspatial := hermiteSpatialNormalizationConstant_pos hm
  positivity

/-- Raw kernel bound in the exact product scale canceled by the two diagonal
floors. -/
theorem norm_hermiteResolventKernel_le_diagonalScales
    (m : ℕ) (hm : 1 ≤ m) (X Y : ℝ) :
    ‖hermiteResolventKernel m X Y‖ ≤
      hermiteRawNormalizationConstant m *
        Real.exp (-(Real.pi / 2) * |X * abs X - Y * abs Y|) *
        (hermiteDiagonalScale X * hermiteDiagonalScale Y) ^
          (hermiteResolventHalfShape m / 2) := by
  have hraw := norm_hermiteResolventKernel_le_normalizedSpatialPower
    m hm X Y
  have hspatial := normalizedSpatialPower_le_diagonalScales m hm X Y
  refine hraw.trans ?_
  have hcoeff : 0 ≤
      ((2 * m - 1).factorial : ℝ)⁻¹ *
        (smallTimeMehlerPrefactorConstant *
            Real.Gamma (hermiteResolventHalfShape m) +
          largeTimeMehlerPrefactorConstant *
            ((2 * m - 1).factorial : ℝ)) := by
    have hfac : 0 < ((2 * m - 1).factorial : ℝ) := by positivity
    exact mul_nonneg (inv_nonneg.mpr hfac.le)
      (add_nonneg
        (mul_nonneg smallTimeMehlerPrefactorConstant_pos.le
          (Real.Gamma_pos_of_pos (hermiteResolventHalfShape_pos hm)).le)
        (mul_nonneg largeTimeMehlerPrefactorConstant_pos.le hfac.le))
  have hexp : 0 ≤ Real.exp
      (-(Real.pi / 2) * |X * abs X - Y * abs Y|) := (Real.exp_pos _).le
  calc
    (((2 * m - 1).factorial : ℝ)⁻¹ *
          (smallTimeMehlerPrefactorConstant *
              Real.Gamma (hermiteResolventHalfShape m) +
            largeTimeMehlerPrefactorConstant *
              ((2 * m - 1).factorial : ℝ))) *
        Real.exp (-(Real.pi / 2) * |X * abs X - Y * abs Y|) *
        (1 / (1 + hermiteNormalizedSpatialCoefficient m *
          (X ^ 2 + Y ^ 2))) ^ hermiteResolventHalfShape m ≤
      (((2 * m - 1).factorial : ℝ)⁻¹ *
          (smallTimeMehlerPrefactorConstant *
              Real.Gamma (hermiteResolventHalfShape m) +
            largeTimeMehlerPrefactorConstant *
              ((2 * m - 1).factorial : ℝ))) *
        Real.exp (-(Real.pi / 2) * |X * abs X - Y * abs Y|) *
        (hermiteSpatialNormalizationConstant m *
          (hermiteDiagonalScale X * hermiteDiagonalScale Y) ^
            (hermiteResolventHalfShape m / 2)) := by
      gcongr
    _ = hermiteRawNormalizationConstant m *
        Real.exp (-(Real.pi / 2) * |X * abs X - Y * abs Y|) *
        (hermiteDiagonalScale X * hermiteDiagonalScale Y) ^
          (hermiteResolventHalfShape m / 2) := by
      unfold hermiteRawNormalizationConstant
      ring

/-- Squaring the refined raw estimate exposes exactly the product of the two
sharp diagonal scales.  This is the form in which normalization cancels. -/
theorem norm_hermiteResolventKernel_sq_le_diagonalScales
    (m : ℕ) (hm : 1 ≤ m) (X Y : ℝ) :
    ‖hermiteResolventKernel m X Y‖ ^ 2 ≤
      hermiteRawNormalizationConstant m ^ 2 *
        Real.exp (-Real.pi * |X * abs X - Y * abs Y|) *
        (hermiteDiagonalScale X * hermiteDiagonalScale Y) ^
          hermiteResolventHalfShape m := by
  have hraw := norm_hermiteResolventKernel_le_diagonalScales m hm X Y
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hraw 2
  have hscale : 0 ≤ hermiteDiagonalScale X * hermiteDiagonalScale Y :=
    mul_nonneg (hermiteDiagonalScale_pos X).le
      (hermiteDiagonalScale_pos Y).le
  have hrpow :
      ((hermiteDiagonalScale X * hermiteDiagonalScale Y) ^
          (hermiteResolventHalfShape m / 2)) ^ 2 =
        (hermiteDiagonalScale X * hermiteDiagonalScale Y) ^
          hermiteResolventHalfShape m := by
    rw [← Real.rpow_mul_natCast hscale]
    congr 1
    norm_num
  have hexp :
      Real.exp (-(Real.pi / 2) * |X * abs X - Y * abs Y|) ^ 2 =
        Real.exp (-Real.pi * |X * abs X - Y * abs Y|) := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  calc
    ‖hermiteResolventKernel m X Y‖ ^ 2 ≤
        (hermiteRawNormalizationConstant m *
          Real.exp (-(Real.pi / 2) * |X * abs X - Y * abs Y|) *
          (hermiteDiagonalScale X * hermiteDiagonalScale Y) ^
            (hermiteResolventHalfShape m / 2)) ^ 2 := hsq
    _ = hermiteRawNormalizationConstant m ^ 2 *
        Real.exp (-Real.pi * |X * abs X - Y * abs Y|) *
        (hermiteDiagonalScale X * hermiteDiagonalScale Y) ^
          hermiteResolventHalfShape m := by
      rw [mul_pow, mul_pow, hexp, hrpow]

end

end MeyerGeneralProblem
