module

public import MeyerGeneralProblem.Hermite.MehlerFormula

@[expose] public section

/-!
# Quantitative Mehler bounds

This module develops the sharp diagonal normalization estimates needed to
turn signed-square heat-kernel decay into a bound for the normalized Hermite
Gram kernel.  The square-root Mehler prefactor is retained explicitly; losing
it would give the wrong power of the point-evaluation norm.
-/

namespace MeyerGeneralProblem

noncomputable section

/-- Elementary small-time bound for the Mehler denominator. -/
theorem one_sub_exp_neg_two_mul_le (t : ℝ) :
    1 - Real.exp (-2 * t) ≤ 2 * t := by
  linarith [Real.add_one_le_exp (-2 * t)]

/-- On the diagonal, the Mehler quadratic has only the slow sum-coordinate
term. -/
theorem mehlerQuadratic_self
    {r : ℝ} (hr : |r| < 1) (X : ℝ) :
    ((1 + r ^ 2) * (X ^ 2 + X ^ 2) - 4 * r * X * X) /
        (1 - r ^ 2) =
      2 * (1 - r) / (1 + r) * X ^ 2 := by
  have hrange := abs_lt.mp hr
  have hplus : 1 + r ≠ 0 := by linarith
  have hminus : 1 - r ≠ 0 := by linarith
  have hsq : 1 - r ^ 2 ≠ 0 := by nlinarith
  field_simp [hplus, hminus, hsq]
  ring

/-- Exact real diagonal of the normalized closed Mehler kernel. -/
theorem normalizedHermiteMehlerClosed_self
    {r : ℝ} (hr : |r| < 1) (X : ℝ) :
    normalizedHermiteMehlerClosed r X X =
      Real.sqrt 2 / Real.sqrt (1 - r ^ 2) *
        Real.exp
          (-Real.pi * (2 * (1 - r) / (1 + r) * X ^ 2)) := by
  unfold normalizedHermiteMehlerClosed
  rw [mehlerQuadratic_self hr]

/-- Exact heat-time diagonal, as a positive real scalar inside `ℂ`. -/
theorem hermiteHeatKernel_self_eq_real
    {t : ℝ} (ht : 0 < t) (X : ℝ) :
    hermiteHeatKernel t X X =
      ((Real.sqrt 2 /
          Real.sqrt (1 - Real.exp (-t) ^ 2) *
        Real.exp
          (-Real.pi *
            (2 * (1 - Real.exp (-t)) /
              (1 + Real.exp (-t)) * X ^ 2)) : ℝ) : ℂ) := by
  rw [hermiteHeatKernel_eq_closed ht]
  norm_cast
  apply normalizedHermiteMehlerClosed_self
  rw [abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]
  linarith

/-- The Mehler square-root prefactor dominates the sharp `t⁻¹ᐟ²` scale. -/
theorem one_div_sqrt_le_mehlerPrefactor
    {t : ℝ} (ht : 0 < t) :
    1 / Real.sqrt t ≤
      Real.sqrt 2 / Real.sqrt (1 - Real.exp (-t) ^ 2) := by
  have hexp0 : 0 < Real.exp (-t) := Real.exp_pos _
  have hexp1 : Real.exp (-t) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hq : 0 < 1 - Real.exp (-t) ^ 2 := by nlinarith
  have hden :
      1 - Real.exp (-t) ^ 2 ≤ 2 * t := by
    rw [show Real.exp (-t) ^ 2 = Real.exp (-2 * t) by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring]
    exact one_sub_exp_neg_two_mul_le t
  have hsqrt :
      Real.sqrt (1 - Real.exp (-t) ^ 2) ≤
        Real.sqrt 2 * Real.sqrt t := by
    calc
      Real.sqrt (1 - Real.exp (-t) ^ 2) ≤ Real.sqrt (2 * t) :=
        Real.sqrt_le_sqrt hden
      _ = Real.sqrt 2 * Real.sqrt t := by
        rw [Real.sqrt_mul (by positivity : 0 ≤ (2 : ℝ))]
  rw [div_le_div_iff₀ (Real.sqrt_pos.2 ht) (Real.sqrt_pos.2 hq)]
  simpa only [one_mul] using hsqrt

/-- The natural heat-time scale at the spatial point `X`.  Its reciprocal is
exactly the quadratic weight occurring in the diagonal asymptotics. -/
def hermiteDiagonalScale (X : ℝ) : ℝ :=
  (1 + X ^ 2)⁻¹

theorem hermiteDiagonalScale_pos (X : ℝ) :
    0 < hermiteDiagonalScale X := by
  unfold hermiteDiagonalScale
  positivity

theorem hermiteDiagonalScale_le_one (X : ℝ) :
    hermiteDiagonalScale X ≤ 1 := by
  unfold hermiteDiagonalScale
  apply (inv_le_one₀ (by positivity : 0 < 1 + X ^ 2)).2
  nlinarith [sq_nonneg X]

/-- Multiplication by `X²` does not destroy the diagonal heat scale. -/
theorem hermiteDiagonalScale_mul_sq_le_one (X : ℝ) :
    hermiteDiagonalScale X * X ^ 2 ≤ 1 := by
  unfold hermiteDiagonalScale
  apply (inv_mul_le_one₀ (by positivity : 0 < 1 + X ^ 2)).2
  nlinarith [sq_nonneg X]

/-- The slow diagonal Mehler quadratic stays uniformly bounded on the
small-time window selected by `hermiteDiagonalScale`. -/
theorem mehlerDiagonalQuadratic_le_four
    {t : ℝ} (X : ℝ) (ht : 0 < t)
    (htT : t ≤ 2 * hermiteDiagonalScale X) :
    2 * (1 - Real.exp (-t)) / (1 + Real.exp (-t)) * X ^ 2 ≤ 4 := by
  have hexp : 0 < Real.exp (-t) := Real.exp_pos _
  have hone : 1 - Real.exp (-t) ≤ t := by
    linarith [Real.add_one_le_exp (-t)]
  have hratio :
      (1 - Real.exp (-t)) / (1 + Real.exp (-t)) ≤ t := by
    rw [div_le_iff₀ (by positivity : 0 < 1 + Real.exp (-t))]
    nlinarith
  have htx : t * X ^ 2 ≤ 2 := by
    calc
      t * X ^ 2 ≤ (2 * hermiteDiagonalScale X) * X ^ 2 :=
        mul_le_mul_of_nonneg_right htT (sq_nonneg X)
      _ ≤ 2 := by
        nlinarith [hermiteDiagonalScale_mul_sq_le_one X]
  calc
    2 * (1 - Real.exp (-t)) / (1 + Real.exp (-t)) * X ^ 2 =
        2 * (((1 - Real.exp (-t)) / (1 + Real.exp (-t))) * X ^ 2) := by
      ring
    _ ≤ 2 * (t * X ^ 2) := by
      gcongr
    _ ≤ 4 := by linarith

/-- The real scalar represented by the diagonal heat kernel. -/
def hermiteHeatDiagonalReal (t X : ℝ) : ℝ :=
  Real.sqrt 2 / Real.sqrt (1 - Real.exp (-t) ^ 2) *
    Real.exp
      (-Real.pi *
        (2 * (1 - Real.exp (-t)) /
          (1 + Real.exp (-t)) * X ^ 2))

theorem hermiteHeatKernel_self_eq_ofReal
    {t : ℝ} (ht : 0 < t) (X : ℝ) :
    hermiteHeatKernel t X X = (hermiteHeatDiagonalReal t X : ℂ) := by
  simpa only [hermiteHeatDiagonalReal] using hermiteHeatKernel_self_eq_real ht X

/-- Retaining the exact Mehler prefactor gives the sharp lower scale on the
diagonal small-time window. -/
theorem hermiteHeatDiagonalReal_lower
    {t : ℝ} (X : ℝ) (ht : 0 < t)
    (htT : t ≤ 2 * hermiteDiagonalScale X) :
    1 / Real.sqrt (2 * hermiteDiagonalScale X) *
        Real.exp (-4 * Real.pi) ≤
      hermiteHeatDiagonalReal t X := by
  have hsqrt : Real.sqrt t ≤
      Real.sqrt (2 * hermiteDiagonalScale X) :=
    Real.sqrt_le_sqrt htT
  have hinv :
      1 / Real.sqrt (2 * hermiteDiagonalScale X) ≤
        1 / Real.sqrt t := by
    exact one_div_le_one_div_of_le (Real.sqrt_pos.2 ht) hsqrt
  have hpref := one_div_sqrt_le_mehlerPrefactor ht
  have hquad := mehlerDiagonalQuadratic_le_four X ht htT
  have hexp :
      Real.exp (-4 * Real.pi) ≤
        Real.exp
          (-Real.pi *
            (2 * (1 - Real.exp (-t)) /
              (1 + Real.exp (-t)) * X ^ 2)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos]
  unfold hermiteHeatDiagonalReal
  calc
    1 / Real.sqrt (2 * hermiteDiagonalScale X) *
          Real.exp (-4 * Real.pi) ≤
        (1 / Real.sqrt t) * Real.exp (-4 * Real.pi) := by
      gcongr
    _ ≤ (Real.sqrt 2 / Real.sqrt (1 - Real.exp (-t) ^ 2)) *
          Real.exp (-4 * Real.pi) := by
      gcongr
    _ ≤ (Real.sqrt 2 / Real.sqrt (1 - Real.exp (-t) ^ 2)) *
          Real.exp
            (-Real.pi *
              (2 * (1 - Real.exp (-t)) /
                (1 + Real.exp (-t)) * X ^ 2)) := by
      gcongr

/-- The real diagonal Laplace integrand for the Hermite resolvent. -/
def hermiteResolventDiagonalIntegrand
    (m : ℕ) (X t : ℝ) : ℝ :=
  t ^ ((2 * m : ℕ) - 1) * Real.exp (-t) *
    hermiteHeatDiagonalReal t X

theorem hermiteResolventDiagonalIntegrand_nonneg
    (m : ℕ) (X : ℝ) {t : ℝ} (ht : 0 < t) :
    0 ≤ hermiteResolventDiagonalIntegrand m X t := by
  unfold hermiteResolventDiagonalIntegrand hermiteHeatDiagonalReal
  positivity

/-- The complex diagonal Laplace integrand is exactly the real scalar above,
embedded in `ℂ`. -/
theorem hermiteResolventLaplaceIntegrand_self_eq_ofReal
    (m : ℕ) (X : ℝ) {t : ℝ} (ht : 0 < t) :
    (((t ^ ((2 * m : ℕ) - 1) * Real.exp (-t) : ℝ) : ℂ)) *
        hermiteHeatKernel t X X =
      (hermiteResolventDiagonalIntegrand m X t : ℂ) := by
  rw [hermiteHeatKernel_self_eq_ofReal ht X]
  norm_cast

/-- The justified complex Laplace identity restricts on the diagonal to a
genuine real integral. -/
theorem factorial_mul_hermiteResolventKernel_self_eq_realIntegral
    (m : ℕ) (hm : 1 ≤ m) (X : ℝ) :
    (((2 * m - 1).factorial : ℝ) : ℂ) *
        hermiteResolventKernel m X X =
      ((∫ t : ℝ in Set.Ioi 0,
          hermiteResolventDiagonalIntegrand m X t : ℝ) : ℂ) := by
  rw [factorial_mul_hermiteResolventKernel_eq_laplaceIntegral m hm X X]
  calc
    (∫ t : ℝ in Set.Ioi 0,
        (((t ^ ((2 * m : ℕ) - 1) * Real.exp (-t) : ℝ) : ℂ)) *
          hermiteHeatKernel t X X) =
        ∫ t : ℝ in Set.Ioi 0,
          ((hermiteResolventDiagonalIntegrand m X t : ℝ) : ℂ) := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      exact hermiteResolventLaplaceIntegrand_self_eq_ofReal m X ht
    _ = ((∫ t : ℝ in Set.Ioi 0,
        hermiteResolventDiagonalIntegrand m X t : ℝ) : ℂ) :=
      integral_ofReal

/-- The real diagonal Laplace integrand is integrable.  The proof reuses the
absolute `tsum`/integral estimate from `MehlerKernel`; in particular it is
valid at the endpoint order `m = 1`. -/
theorem integrableOn_hermiteResolventDiagonalIntegrand
    (m : ℕ) (hm : 1 ≤ m) (X : ℝ) :
    MeasureTheory.IntegrableOn
      (hermiteResolventDiagonalIntegrand m X) (Set.Ioi 0) := by
  let μ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))
  let F : ℕ → ℝ → ℂ := fun n t ↦
    hermiteResolventLaplaceTerm m X X n t
  have hFint : ∀ n : ℕ, MeasureTheory.Integrable (F n) μ := by
    intro n
    exact integrableOn_hermiteResolventLaplaceTerm m X X n
  have hsum : Summable (fun n : ℕ ↦ ∫ t, ‖F n t‖ ∂μ) := by
    simpa only [F, μ] using
      summable_integral_norm_hermiteResolventLaplaceTerm m hm X X
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
      (hermiteResolventDiagonalIntegrand m X) μ
    unfold hermiteResolventDiagonalIntegrand hermiteHeatDiagonalReal
    fun_prop
  · rw [MeasureTheory.hasFiniteIntegral_iff_enorm]
    apply lt_of_le_of_lt _ hlintegral
    apply MeasureTheory.lintegral_mono_ae
    filter_upwards [MeasureTheory.ae_restrict_mem
      (μ := MeasureTheory.volume) measurableSet_Ioi] with t ht
    have heq :
        ((hermiteResolventDiagonalIntegrand m X t : ℝ) : ℂ) =
          ∑' n : ℕ, F n t := by
      calc
        ((hermiteResolventDiagonalIntegrand m X t : ℝ) : ℂ) =
            (((t ^ ((2 * m : ℕ) - 1) * Real.exp (-t) : ℝ) : ℂ)) *
              hermiteHeatKernel t X X :=
          (hermiteResolventLaplaceIntegrand_self_eq_ofReal m X ht).symm
        _ = ∑' n : ℕ, F n t := by
          symm
          simpa only [F] using
            tsum_hermiteResolventLaplaceTerm_eq_heatKernel m X X t
    calc
      ‖hermiteResolventDiagonalIntegrand m X t‖ₑ =
          ‖((hermiteResolventDiagonalIntegrand m X t : ℝ) : ℂ)‖ₑ := by
        apply enorm_eq_iff_norm_eq.mpr
        exact (Complex.norm_real _).symm
      _ = ‖∑' n : ℕ, F n t‖ₑ := by rw [heq]
      _ ≤ ∑' n : ℕ, ‖F n t‖ₑ := enorm_tsum_le_tsum_enorm

/-- Constant lower floor for the diagonal Laplace integrand on the window
`[T, 2T]`, where `T = hermiteDiagonalScale X`. -/
def hermiteDiagonalWindowFloor (m : ℕ) (X : ℝ) : ℝ :=
  hermiteDiagonalScale X ^ ((2 * m : ℕ) - 1) *
    Real.exp (-2) *
      (1 / Real.sqrt (2 * hermiteDiagonalScale X) *
        Real.exp (-4 * Real.pi))

theorem hermiteDiagonalWindowFloor_nonneg (m : ℕ) (X : ℝ) :
    0 ≤ hermiteDiagonalWindowFloor m X := by
  have hT : 0 < hermiteDiagonalScale X := hermiteDiagonalScale_pos X
  unfold hermiteDiagonalWindowFloor
  positivity

theorem hermiteDiagonalWindowFloor_le_integrand
    (m : ℕ) (X : ℝ) {t : ℝ}
    (hTt : hermiteDiagonalScale X ≤ t)
    (ht2T : t ≤ 2 * hermiteDiagonalScale X) :
    hermiteDiagonalWindowFloor m X ≤
      hermiteResolventDiagonalIntegrand m X t := by
  have hT : 0 < hermiteDiagonalScale X := hermiteDiagonalScale_pos X
  have ht : 0 < t := hT.trans_le hTt
  have ht2 : t ≤ 2 := by
    exact ht2T.trans (by
      nlinarith [hermiteDiagonalScale_le_one X])
  have hpow :
      hermiteDiagonalScale X ^ ((2 * m : ℕ) - 1) ≤
        t ^ ((2 * m : ℕ) - 1) := by
    gcongr
  have hexp : Real.exp (-2) ≤ Real.exp (-t) := by
    apply Real.exp_le_exp.mpr
    linarith
  have hheat := hermiteHeatDiagonalReal_lower X ht ht2T
  unfold hermiteDiagonalWindowFloor hermiteResolventDiagonalIntegrand
  gcongr

/-- Integrating the pointwise window floor preserves exactly one factor of
the natural heat scale, the length of `[T, 2T]`. -/
theorem hermiteDiagonalScale_mul_windowFloor_le_integral
    (m : ℕ) (hm : 1 ≤ m) (X : ℝ) :
    hermiteDiagonalScale X * hermiteDiagonalWindowFloor m X ≤
      ∫ t : ℝ in Set.Ioi 0,
        hermiteResolventDiagonalIntegrand m X t := by
  let T := hermiteDiagonalScale X
  let f := hermiteResolventDiagonalIntegrand m X
  let b := hermiteDiagonalWindowFloor m X
  have hT : 0 < T := hermiteDiagonalScale_pos X
  have hsub : Set.Icc T (2 * T) ⊆ Set.Ioi (0 : ℝ) := by
    intro t ht
    exact hT.trans_le ht.1
  have hf : MeasureTheory.IntegrableOn f (Set.Ioi (0 : ℝ)) := by
    simpa only [f] using
      integrableOn_hermiteResolventDiagonalIntegrand m hm X
  have hfIcc : MeasureTheory.IntegrableOn f (Set.Icc T (2 * T)) :=
    hf.mono_set hsub
  have hbIcc : MeasureTheory.IntegrableOn (fun _ : ℝ ↦ b)
      (Set.Icc T (2 * T)) := MeasureTheory.integrableOn_const (by
        rw [Real.volume_Icc]
        exact ENNReal.ofReal_ne_top)
  have hwindow :
      ∫ t : ℝ in Set.Icc T (2 * T), b ≤
        ∫ t : ℝ in Set.Icc T (2 * T), f t := by
    apply MeasureTheory.setIntegral_mono_on hbIcc hfIcc measurableSet_Icc
    intro t ht
    exact hermiteDiagonalWindowFloor_le_integrand m X ht.1 ht.2
  have hfull :
      ∫ t : ℝ in Set.Icc T (2 * T), f t ≤
        ∫ t : ℝ in Set.Ioi 0, f t := by
    apply MeasureTheory.setIntegral_mono_set hf
    · filter_upwards [MeasureTheory.ae_restrict_mem
        (μ := MeasureTheory.volume) measurableSet_Ioi] with t ht
      exact hermiteResolventDiagonalIntegrand_nonneg m X ht
    · exact Filter.Eventually.of_forall hsub
  calc
    hermiteDiagonalScale X * hermiteDiagonalWindowFloor m X = T * b := by
      rfl
    _ = ∫ _t : ℝ in Set.Icc T (2 * T), b := by
      rw [MeasureTheory.setIntegral_const]
      change T * b = (MeasureTheory.volume (Set.Icc T (2 * T))).toReal • b
      rw [Real.volume_Icc, ENNReal.toReal_ofReal (by linarith : 0 ≤ 2 * T - T)]
      change T * b = (2 * T - T) * b
      ring
    _ ≤ ∫ t : ℝ in Set.Icc T (2 * T), f t := hwindow
    _ ≤ ∫ t : ℝ in Set.Ioi 0, f t := hfull

/-- Real-valued diagonal form of the resolvent kernel, with the exact Gamma
factor divided out. -/
theorem hermiteResolventKernel_self_eq_realIntegral
    (m : ℕ) (hm : 1 ≤ m) (X : ℝ) :
    hermiteResolventKernel m X X =
      ((((2 * m - 1).factorial : ℝ)⁻¹ *
          ∫ t : ℝ in Set.Ioi 0,
            hermiteResolventDiagonalIntegrand m X t : ℝ) : ℂ) := by
  let F : ℝ := ((2 * m - 1).factorial : ℝ)
  let I : ℝ := ∫ t : ℝ in Set.Ioi 0,
    hermiteResolventDiagonalIntegrand m X t
  have hF : F ≠ 0 := by
    dsimp [F]
    exact_mod_cast Nat.factorial_ne_zero (2 * m - 1)
  have hFc : (F : ℂ) ≠ 0 := by exact_mod_cast hF
  have h := factorial_mul_hermiteResolventKernel_self_eq_realIntegral
    m hm X
  change (F : ℂ) * hermiteResolventKernel m X X = (I : ℂ) at h
  change hermiteResolventKernel m X X = ((F⁻¹ * I : ℝ) : ℂ)
  calc
    hermiteResolventKernel m X X =
        (F : ℂ)⁻¹ * ((F : ℂ) * hermiteResolventKernel m X X) := by
      field_simp
    _ = (F : ℂ)⁻¹ * (I : ℂ) := by rw [h]
    _ = ((F⁻¹ * I : ℝ) : ℂ) := by norm_cast

/-- Exact real integral formula for the squared norm of a negative-scale
Hermite point mass. -/
theorem norm_hermitePointMass_sq_eq_realIntegral
    (m : ℕ) (hm : 1 ≤ m) (X : ℝ) :
    ‖hermitePointMass m hm X‖ ^ 2 =
      ((2 * m - 1).factorial : ℝ)⁻¹ *
        ∫ t : ℝ in Set.Ioi 0,
          hermiteResolventDiagonalIntegrand m X t := by
  have hcomplex :
      ((‖hermitePointMass m hm X‖ ^ 2 : ℝ) : ℂ) =
        ((((2 * m - 1).factorial : ℝ)⁻¹ *
          ∫ t : ℝ in Set.Ioi 0,
            hermiteResolventDiagonalIntegrand m X t : ℝ) : ℂ) := by
    calc
      ((‖hermitePointMass m hm X‖ ^ 2 : ℝ) : ℂ) =
          inner ℂ (hermitePointMass m hm X)
            (hermitePointMass m hm X) := by
        rw [inner_self_eq_norm_sq_to_K]
        norm_cast
      _ = hermiteResolventKernel m X X :=
        inner_hermitePointMass_eq_resolventKernel m hm X X
      _ = ((((2 * m - 1).factorial : ℝ)⁻¹ *
          ∫ t : ℝ in Set.Ioi 0,
            hermiteResolventDiagonalIntegrand m X t : ℝ) : ℂ) :=
        hermiteResolventKernel_self_eq_realIntegral m hm X
  exact_mod_cast hcomplex

/-- The explicit sharp diagonal floor.  Its scale is
`T^(2m) / sqrt (2T)`, hence `T^(2m-1/2)` rather than the insufficient
`T^(2m)` bound. -/
def hermitePointMassDiagonalFloor (m : ℕ) (X : ℝ) : ℝ :=
  ((2 * m - 1).factorial : ℝ)⁻¹ *
    (hermiteDiagonalScale X * hermiteDiagonalWindowFloor m X)

theorem hermitePointMassDiagonalFloor_pos
    (m : ℕ) (X : ℝ) :
    0 < hermitePointMassDiagonalFloor m X := by
  unfold hermitePointMassDiagonalFloor hermiteDiagonalWindowFloor
  have hT : 0 < hermiteDiagonalScale X := hermiteDiagonalScale_pos X
  positivity

/-- Sharp polynomial lower bound for the genuine point-mass diagonal norm. -/
theorem hermitePointMassDiagonalFloor_le_norm_sq
    (m : ℕ) (hm : 1 ≤ m) (X : ℝ) :
    hermitePointMassDiagonalFloor m X ≤
      ‖hermitePointMass m hm X‖ ^ 2 := by
  rw [norm_hermitePointMass_sq_eq_realIntegral m hm X]
  unfold hermitePointMassDiagonalFloor
  gcongr
  exact hermiteDiagonalScale_mul_windowFloor_le_integral m hm X

theorem sqrt_hermitePointMassDiagonalFloor_le_norm
    (m : ℕ) (hm : 1 ≤ m) (X : ℝ) :
    Real.sqrt (hermitePointMassDiagonalFloor m X) ≤
      ‖hermitePointMass m hm X‖ := by
  rw [Real.sqrt_le_iff]
  exact ⟨norm_nonneg _, hermitePointMassDiagonalFloor_le_norm_sq m hm X⟩

/-- Squared reciprocal form of the sharp diagonal estimate, ready for the
two normalization factors in the normalized Gram kernel. -/
theorem inv_norm_hermitePointMass_sq_le_diagonalFloor_inv
    (m : ℕ) (hm : 1 ≤ m) (X : ℝ) :
    ‖hermitePointMass m hm X‖⁻¹ ^ 2 ≤
      (hermitePointMassDiagonalFloor m X)⁻¹ := by
  have hfloor := hermitePointMassDiagonalFloor_pos m X
  have hlower := hermitePointMassDiagonalFloor_le_norm_sq m hm X
  rw [inv_pow]
  exact (inv_le_inv₀ (hfloor.trans_le hlower) hfloor).2 hlower

end

end MeyerGeneralProblem
