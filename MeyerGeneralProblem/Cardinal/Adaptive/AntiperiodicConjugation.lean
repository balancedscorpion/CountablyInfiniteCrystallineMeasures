module

public import MeyerGeneralProblem.Cardinal.Adaptive.PeriodicDescent
public import MeyerGeneralProblem.Distribution.FiniteFourierMotif

@[expose] public section

/-! # Actual modulation conjugacy for local antiperiodic differences -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section

/-- Half a frequency dual to the nonzero physical period. -/
def halfPeriodFrequency (P : ℝ) : ℝ := 1/(2*P)

/-- The exact half-period character equals minus one. -/
theorem halfPeriodCharacter (P : ℝ) (hP : P ≠ 0) :
    combModulationCharacter (halfPeriodFrequency P) P = -1 := by
  rw [combModulationCharacter_eq_exp]
  have he : 2*(Real.pi:ℂ)*Complex.I*(halfPeriodFrequency P:ℂ)*(P:ℂ) =
      (Real.pi:ℂ)*Complex.I := by
    simp only [halfPeriodFrequency, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_mul, Complex.ofReal_ofNat]
    field_simp [Complex.ofReal_ne_zero.mpr hP]
  rw [he, Complex.exp_pi_mul_I]

/-- The actual modulation character flips sign under one physical period. -/
theorem halfPeriodCharacter_shift (P : ℝ) (hP : P ≠ 0) (x : ℝ) :
    combModulationCharacter (halfPeriodFrequency P) (P+x) =
      -combModulationCharacter (halfPeriodFrequency P) x := by
  have he (a u v : ℝ) : combModulationCharacter a (u+v) =
      combModulationCharacter a u * combModulationCharacter a v := by
    simp only [combModulationCharacter_eq_exp, Complex.ofReal_add, mul_add, Complex.exp_add]
  rw [he, halfPeriodCharacter P hP, neg_one_mul]

/-- Modulation and translation anticommute at the exact half-period frequency,
with the sign proved on every actual Schwartz test. -/
theorem halfPeriodModulation_translation (P : ℝ) (hP : P ≠ 0)
    (T : TemperedDistribution ℝ ℂ) :
    combDistributionTranslation P (combDistributionModulation (halfPeriodFrequency P) T) =
      -combDistributionModulation (halfPeriodFrequency P) (combDistributionTranslation P T) := by
  ext f
  change T (combSchwartzModulation (halfPeriodFrequency P) (combSchwartzTranslation P f)) =
    -T (combSchwartzTranslation P (combSchwartzModulation (halfPeriodFrequency P) f))
  have he : combSchwartzModulation (halfPeriodFrequency P) (combSchwartzTranslation P f) =
      -combSchwartzTranslation P (combSchwartzModulation (halfPeriodFrequency P) f) := by
    ext x
    simp only [combSchwartzModulation_apply, combSchwartzTranslation_apply, neg_apply,
      halfPeriodCharacter_shift P hP, neg_mul, neg_neg]
  rw [he, map_neg]

/-- The actual translation-plus-identity operator on whole distributions. -/
def distributionAntidifference (P : ℝ) :
    TemperedDistribution ℝ ℂ →L[ℂ] TemperedDistribution ℝ ℂ :=
  combDistributionTranslation P + ContinuousLinearMap.id ℂ _

/-- Conjugating one antiperiodic difference gives an ordinary difference,
with its full scalar sign retained. -/
theorem halfPeriodModulation_difference (P : ℝ) (hP : P ≠ 0)
    (T : TemperedDistribution ℝ ℂ) :
    distributionDifference P (combDistributionModulation (halfPeriodFrequency P) T) =
      -combDistributionModulation (halfPeriodFrequency P) (distributionAntidifference P T) := by
  simp only [distributionDifference, distributionAntidifference, sub_apply, add_apply,
    ContinuousLinearMap.id_apply, map_add, halfPeriodModulation_translation P hP]
  abel

/-- Actual modulation turns every power of the antiperiodic equation into the
corresponding ordinary finite-difference equation. -/
theorem halfPeriodModulation_iter_difference (P : ℝ) (hP : P ≠ 0) (d : ℕ)
    (T : TemperedDistribution ℝ ℂ) :
    (distributionDifference P : TemperedDistribution ℝ ℂ → TemperedDistribution ℝ ℂ)^[d]
      (combDistributionModulation (halfPeriodFrequency P) T) =
    ((-1:ℂ)^d) • combDistributionModulation (halfPeriodFrequency P)
      ((distributionAntidifference P : TemperedDistribution ℝ ℂ → TemperedDistribution ℝ ℂ)^[d] T) := by
  induction d with
  | zero => simp only [Function.iterate_zero_apply, pow_zero, one_smul]
  | succ d ih =>
      rw [Function.iterate_succ_apply', ih, map_smul, halfPeriodModulation_difference P hP,
        Function.iterate_succ_apply']
      rw [pow_succ, mul_smul, neg_one_smul, smul_neg]

/-- Exact composition of whole modulation operators. -/
theorem distributionModulation_add (a b : ℝ) (T : TemperedDistribution ℝ ℂ) :
    combDistributionModulation a (combDistributionModulation b T) =
      combDistributionModulation (a+b) T := by
  ext f
  change T (combSchwartzModulation b (combSchwartzModulation a f)) =
    T (combSchwartzModulation (a+b) f)
  congr 1
  ext x
  simp only [combSchwartzModulation_apply, combModulationCharacter_add_left]
  ring

/-- Actual opposite modulation recovers the entire source. -/
theorem distributionModulation_neg_cancel (a : ℝ) (T : TemperedDistribution ℝ ℂ) :
    combDistributionModulation (-a) (combDistributionModulation a T) = T := by
  rw [distributionModulation_add, neg_add_cancel]
  ext f
  change T (combSchwartzModulation 0 f) = T f
  congr 1
  ext x
  simp only [combSchwartzModulation_apply, combModulationCharacter_zero_left, one_mul]

/-- Modulation preserves annihilation of compact tests on any region. -/
theorem DistributionVanishesOn.modulation {O : Set ℝ} {T : TemperedDistribution ℝ ℂ}
    (hT : DistributionVanishesOn O T) (a : ℝ) :
    DistributionVanishesOn O (combDistributionModulation a T) := by
  intro f hf hs
  change T (combSchwartzModulation a f) = 0
  have he : (combSchwartzModulation a f : ℝ → ℂ) =
      (combModulationCharacter a) * (f : ℝ → ℂ) := by
    ext x
    exact combSchwartzModulation_apply a f x
  have hc : HasCompactSupport (combSchwartzModulation a f : ℝ → ℂ) := by
    rw [he]
    exact hf.mul_left
  have hsupport : tsupport (combSchwartzModulation a f : ℝ → ℂ) ⊆ tsupport (f : ℝ → ℂ) := by
    rw [he]
    exact tsupport_mul_subset_right
  exact hT _ hc (hsupport.trans hs)

/-- The conjugated native source satisfies its local ordinary difference
condition whenever the original source satisfies the antiperiodic condition. -/
theorem nativeModulation_local_difference (q d : ℕ) (P : ℝ) (hP : P ≠ 0)
    (O : Set ℝ) (T : HermiteScale (-(q:ℤ)))
    (hT : DistributionVanishesOn O
      ((distributionAntidifference P : TemperedDistribution ℝ ℂ → TemperedDistribution ℝ ℂ)^[d]
        (hermiteScaleDistribution q T))) :
    DistributionVanishesOn O
      ((distributionDifference P : TemperedDistribution ℝ ℂ → TemperedDistribution ℝ ℂ)^[d]
        (hermiteScaleDistribution q (nativeModulation q (halfPeriodFrequency P) T))) := by
  rw [nativeModulation_realizes, halfPeriodModulation_iter_difference P hP]
  intro f hf hs
  simp only [smul_apply, smul_eq_mul, hT.modulation (halfPeriodFrequency P) f hf hs, mul_zero]

end
end MeyerGeneralProblem.Adaptive
