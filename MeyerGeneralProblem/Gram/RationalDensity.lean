module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import all Mathlib.MeasureTheory.Integral.Bochner.Basic

public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import all Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.LinearAlgebra.Dimension.Finite
import all Mathlib.LinearAlgebra.Dimension.Finite

@[expose] public section

/-!
# Rational universal Gram density

The universal same-side model is defined from its positive Fourier density.
Modified Bessel functions are not used: the normalization is the reciprocal of
the integral itself.
-/

namespace MeyerGeneralProblem

open MeasureTheory

noncomputable section

/-- Unnormalised rational density at Hermite order `m`. -/
def rawGramDensity (m : ℕ) (η : ℝ) : ℝ :=
  Real.rpow (1 + 4 * η ^ 2) (-(2 * (m : ℝ)))

theorem rawGramDensity_pos (m : ℕ) (η : ℝ) : 0 < rawGramDensity m η := by
  unfold rawGramDensity
  exact Real.rpow_pos_of_pos (by nlinarith [sq_nonneg η]) _

theorem rawGramDensity_nonneg (m : ℕ) (η : ℝ) : 0 ≤ rawGramDensity m η :=
  (rawGramDensity_pos m η).le

/-- At integer Hermite order the real power in the rational density is the
ordinary inverse power used by the endpoint floor. -/
theorem rawGramDensity_eq_inv_pow (m : ℕ) (η : ℝ) :
    rawGramDensity m η = (1 + 4 * η ^ 2)⁻¹ ^ (2 * m) := by
  unfold rawGramDensity
  change (1 + 4 * η ^ 2) ^ (-(2 * (m : ℝ))) = _
  rw [show -(2 * (m : ℝ)) = -((2 * m : ℕ) : ℝ) by
    push_cast
    ring]
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast, inv_pow]

/-- The rational density is integrable at every positive Hermite order. -/
theorem integrable_rawGramDensity {m : ℕ} (hm : 1 ≤ m) :
    Integrable (rawGramDensity m) := by
  have hrank : (Module.finrank ℝ ℝ : ℝ) < 4 * (m : ℝ) := by
    simp only [Module.finrank_self, Nat.cast_one]
    exact_mod_cast (show 1 < 4 * m by omega)
  have href := integrable_rpow_neg_one_add_norm_sq (E := ℝ)
    (μ := MeasureTheory.volume) hrank
  have href' : Integrable
      (fun η : ℝ ↦ Real.rpow (1 + η ^ 2) (-(2 * (m : ℝ)))) := by
    convert href using 1
    funext η
    congr 1
    · rw [Real.norm_eq_abs, sq_abs]
    · ring
  apply href'.mono'
  · apply Continuous.aestronglyMeasurable
    refine continuous_iff_continuousAt.mpr fun η ↦ ?_
    change ContinuousAt
      (fun x : ℝ ↦ Real.rpow (1 + 4 * x ^ 2) (-(2 * (m : ℝ)))) η
    have hbase : ContinuousAt (fun x : ℝ ↦ 1 + 4 * x ^ 2) η := by
      fun_prop
    exact hbase.rpow_const (.inl (by positivity))
  · filter_upwards with η
    have hpow : rawGramDensity m η ≤
        Real.rpow (1 + η ^ 2) (-(2 * (m : ℝ))) := by
      unfold rawGramDensity
      apply Real.rpow_le_rpow_of_nonpos (by positivity)
      · nlinarith [sq_nonneg η]
      · exact neg_nonpos.mpr (by positivity)
    rw [Real.norm_of_nonneg (rawGramDensity_nonneg m η)]
    exact hpow

/-- Total unnormalised mass. -/
def rawGramMass (m : ℕ) : ℝ :=
  ∫ η : ℝ, rawGramDensity m η

theorem rawGramMass_pos {m : ℕ} (hm : 1 ≤ m) : 0 < rawGramMass m := by
  unfold rawGramMass
  rw [integral_pos_iff_support_of_nonneg (rawGramDensity_nonneg m)
    (integrable_rawGramDensity hm)]
  have hsupp : Function.support (rawGramDensity m) = Set.univ := by
    ext η
    simp [Function.mem_support, (rawGramDensity_pos m η).ne']
  rw [hsupp]
  simp

/-- Normalizing constant chosen so `2 cₘ` times the raw density has mass one. -/
def gramNormalization (m : ℕ) : ℝ :=
  (2 * rawGramMass m)⁻¹

theorem gramNormalization_pos {m : ℕ} (hm : 1 ≤ m) :
    0 < gramNormalization m := by
  unfold gramNormalization
  exact inv_pos.mpr (mul_pos two_pos (rawGramMass_pos hm))

/-- The normalized universal Gram density. -/
def gramDensity (m : ℕ) (η : ℝ) : ℝ :=
  2 * gramNormalization m * rawGramDensity m η

theorem gramDensity_nonneg {m : ℕ} (hm : 1 ≤ m) (η : ℝ) :
    0 ≤ gramDensity m η := by
  unfold gramDensity
  exact mul_nonneg (mul_nonneg (by norm_num) (gramNormalization_pos hm).le)
    (rawGramDensity_nonneg m η)

theorem integrable_gramDensity {m : ℕ} (hm : 1 ≤ m) :
    Integrable (gramDensity m) := by
  have h := (integrable_rawGramDensity hm).const_mul (2 * gramNormalization m)
  convert h using 1
  funext η
  simp only [gramDensity]

/-- Pointwise density floor on the Ingham frequency window `[-a,a]`. -/
theorem gramDensity_lower_bound_on_Icc
    {m : ℕ} (hm : 1 ≤ m) {a η : ℝ}
    (hη : η ∈ Set.Icc (-a) a) :
    2 * gramNormalization m * (1 + 4 * a ^ 2)⁻¹ ^ (2 * m) ≤
      gramDensity m η := by
  have hηsq : η ^ 2 ≤ a ^ 2 := by
    rcases hη with ⟨hleft, hright⟩
    nlinarith [sq_nonneg (η + a), sq_nonneg (a - η)]
  have hbase : 1 + 4 * η ^ 2 ≤ 1 + 4 * a ^ 2 := by nlinarith
  have hraw : rawGramDensity m a ≤ rawGramDensity m η := by
    unfold rawGramDensity
    apply Real.rpow_le_rpow_of_nonpos (by positivity) hbase
    exact neg_nonpos.mpr (by positivity)
  calc
    2 * gramNormalization m * (1 + 4 * a ^ 2)⁻¹ ^ (2 * m) =
        2 * gramNormalization m * rawGramDensity m a := by
      rw [rawGramDensity_eq_inv_pow]
    _ ≤ 2 * gramNormalization m * rawGramDensity m η := by
      exact mul_le_mul_of_nonneg_left hraw
        (mul_nonneg (by norm_num) (gramNormalization_pos hm).le)
    _ = gramDensity m η := by rfl

/-- The universal density has total mass exactly one. -/
theorem integral_gramDensity {m : ℕ} (hm : 1 ≤ m) :
    ∫ η : ℝ, gramDensity m η = 1 := by
  change (∫ η : ℝ, (2 * gramNormalization m) * rawGramDensity m η) = 1
  rw [integral_const_mul]
  unfold gramNormalization rawGramMass
  calc
    2 * (2 * (∫ η : ℝ, rawGramDensity m η))⁻¹ *
        (∫ η : ℝ, rawGramDensity m η) =
        (2 * (∫ η : ℝ, rawGramDensity m η))⁻¹ *
          (2 * (∫ η : ℝ, rawGramDensity m η)) := by ring
    _ = 1 := inv_mul_cancel₀
      (mul_ne_zero two_ne_zero (rawGramMass_pos hm).ne')

end

end MeyerGeneralProblem
