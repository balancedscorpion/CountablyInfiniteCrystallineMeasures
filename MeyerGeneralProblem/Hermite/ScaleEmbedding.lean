module

public import MeyerGeneralProblem.Atomic.HermiteDistribution

@[expose] public section

/-!
# Coherent adjacent inclusions in the negative Hermite scale

This file records the bounded, one-step part of the negative Hermite-scale
filtration.  In normalized coordinates the inclusion from order `-m` to
order `-(m+1)` is multiplication by `(n+1)⁻¹`.  The map is a contraction,
is injective, preserves the decoded raw coefficients, and is natural for both
distribution realization and the diagonal Hermite Fourier action.

No exhaustion of tempered distributions, or identification with a total
union of negative scales, is asserted here.
-/

open MeasureTheory
open scoped ComplexConjugate FourierTransform lp SchwartzMap

namespace MeyerGeneralProblem

noncomputable section

/-- Coordinate multiplier for one adjacent inclusion in the negative Hermite
scale. -/
def hermiteScaleStepMultiplier (n : ℕ) : ℂ :=
  ((((n : ℝ) + 1)⁻¹ : ℝ) : ℂ)

private theorem hermiteScaleStepMultiplier_norm_le_one (n : ℕ) :
    ‖hermiteScaleStepMultiplier n‖ ≤ 1 := by
  rw [hermiteScaleStepMultiplier, Complex.norm_real, Real.norm_eq_abs,
    abs_inv, abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
  exact (inv_le_one₀ (by positivity)).2 (by norm_num)

private theorem hermiteScaleStepMultiplier_ne_zero (n : ℕ) :
    hermiteScaleStepMultiplier n ≠ 0 := by
  unfold hermiteScaleStepMultiplier
  exact_mod_cast inv_ne_zero (by positivity : (n : ℝ) + 1 ≠ 0)

def hermiteScaleInclusionLinear (m : ℕ) :
    HermiteScale (-(m : ℤ)) →ₗ[ℂ] HermiteScale (-((m + 1 : ℕ) : ℤ)) where
  toFun u :=
    ⟨fun n => hermiteScaleStepMultiplier n * u n,
      by
        apply (lp.memℓp u).norm.mono
        intro n
        rw [norm_mul]
        exact (mul_le_mul_of_nonneg_right
          (hermiteScaleStepMultiplier_norm_le_one n) (norm_nonneg (u n))).trans_eq
            (one_mul ‖u n‖)⟩
  map_add' u v := by
    apply Subtype.ext
    funext n
    simp only [Pi.add_apply, lp.coeFn_add]
    exact mul_add _ _ _
  map_smul' c u := by
    apply Subtype.ext
    funext n
    simp only [Pi.smul_apply, lp.coeFn_smul, smul_eq_mul, RingHom.id_apply]
    ring

/-- The adjacent inclusion `H_(-m) → H_(-(m+1))` in normalized Hermite
coordinates.  It is multiplication by `(n+1)⁻¹` in coordinate `n`. -/
def hermiteScaleInclusion (m : ℕ) :
    HermiteScale (-(m : ℤ)) →L[ℂ] HermiteScale (-((m + 1 : ℕ) : ℤ)) :=
  (hermiteScaleInclusionLinear m).mkContinuous 1 fun u => by
    simpa only [one_mul] using
      (lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0) fun n => by
        change ‖hermiteScaleStepMultiplier n * u n‖ ≤ ‖u n‖
        rw [norm_mul]
        exact (mul_le_mul_of_nonneg_right
          (hermiteScaleStepMultiplier_norm_le_one n) (norm_nonneg (u n))).trans_eq
            (one_mul ‖u n‖))

@[simp]
theorem hermiteScaleInclusion_apply (m : ℕ) (u : HermiteScale (-(m : ℤ)))
    (n : ℕ) :
    hermiteScaleInclusion m u n = hermiteScaleStepMultiplier n * u n :=
  rfl

/-- The adjacent negative-scale inclusion is a contraction. -/
theorem hermiteScaleInclusion_norm_le (m : ℕ) :
    ‖hermiteScaleInclusion m‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  simpa only [one_mul] using
    (lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0) fun n => by
      rw [hermiteScaleInclusion_apply, norm_mul]
      exact (mul_le_mul_of_nonneg_right
        (hermiteScaleStepMultiplier_norm_le_one n) (norm_nonneg (u n))).trans_eq
          (one_mul ‖u n‖))

/-- No coefficient is lost by the adjacent negative-scale inclusion. -/
theorem hermiteScaleInclusion_injective (m : ℕ) :
    Function.Injective (hermiteScaleInclusion m) := by
  intro u v huv
  apply Subtype.ext
  funext n
  have hn := congrArg (fun w : HermiteScale (-((m + 1 : ℕ) : ℤ)) => w n) huv
  rw [hermiteScaleInclusion_apply, hermiteScaleInclusion_apply] at hn
  exact mul_left_cancel₀ (hermiteScaleStepMultiplier_ne_zero n) hn

/-- Adjacent inclusion preserves the decoded raw Hermite coefficient. -/
@[simp]
theorem rawHermiteCoefficients_hermiteScaleInclusion
    (m : ℕ) (u : HermiteScale (-(m : ℤ))) (n : ℕ) :
    rawHermiteCoefficients (-((m + 1 : ℕ) : ℤ))
        (hermiteScaleInclusion m u) n =
      rawHermiteCoefficients (-(m : ℤ)) u n := by
  rw [rawHermiteCoefficients, rawHermiteCoefficients,
    hermiteScaleInclusion_apply]
  change (hermiteScaleWeight (-((m + 1 : ℕ) : ℤ)) n : ℂ)⁻¹ *
      (((((n : ℝ) + 1)⁻¹ : ℝ) : ℂ) * u n) =
    (hermiteScaleWeight (-(m : ℤ)) n : ℂ)⁻¹ * u n
  rw [show -((m + 1 : ℕ) : ℤ) = -(m : ℤ) + (-1 : ℤ) by omega,
    hermiteScaleWeight_add]
  simp only [hermiteScaleWeight, zpow_neg_one]
  push_cast
  field_simp

private theorem schwartzHermiteCoefficients_normalizedHermiteSchwartz
    (i j : ℕ) :
    schwartzHermiteCoefficients (normalizedHermiteSchwartz i) j =
      if j = i then 1 else 0 := by
  rw [schwartzHermiteCoefficients_apply_repr,
    normalizedHermiteSchwartz_eq_twoPi,
    TauCeti.toLp_twoPiHermiteSchwartzMap]
  have hb : TauCeti.twoPiHermiteFunctionLp ℂ i =
      (TauCeti.twoPiHermiteHilbertBasis ℂ) i := by
    exact (congrFun (TauCeti.coe_twoPiHermiteHilbertBasis (𝕜 := ℂ)) i).symm
  rw [hb, HilbertBasis.repr_self]
  simp [lp.single_apply, Pi.single_apply]

/-- Realization of a negative Hermite-scale vector as a tempered
distribution is injective. -/
theorem hermiteScaleDistribution_injective (m : ℕ) :
    Function.Injective (hermiteScaleDistribution m) := by
  intro T U hTU
  apply Subtype.ext
  funext i
  have hi := DFunLike.congr_fun hTU (normalizedHermiteSchwartz i)
  rw [hermiteScaleDistribution_apply_raw,
    hermiteScaleDistribution_apply_raw] at hi
  simp_rw [schwartzHermiteCoefficients_normalizedHermiteSchwartz] at hi
  simp only [mul_ite, mul_one, mul_zero, tsum_ite_eq] at hi
  have hw : (hermiteScaleWeight (-(m : ℤ)) i : ℂ) ≠ 0 := by
    exact_mod_cast hermiteScaleWeight_ne_zero (-(m : ℤ)) i
  change (hermiteScaleWeight (-(m : ℤ)) i : ℂ)⁻¹ * T i =
    (hermiteScaleWeight (-(m : ℤ)) i : ℂ)⁻¹ * U i at hi
  exact mul_left_cancel₀ (inv_ne_zero hw) hi

/-- The adjacent inclusion realizes as the same tempered distribution. -/
theorem hermiteScaleDistribution_inclusion
    (m : ℕ) (u : HermiteScale (-(m : ℤ))) :
    hermiteScaleDistribution (m + 1) (hermiteScaleInclusion m u) =
      hermiteScaleDistribution m u := by
  ext f
  rw [hermiteScaleDistribution_apply_raw,
    hermiteScaleDistribution_apply_raw]
  apply tsum_congr
  intro n
  rw [rawHermiteCoefficients_hermiteScaleInclusion]

/-- The adjacent inclusion commutes with the diagonal Hermite Fourier
action. -/
theorem hermiteFourier_inclusion_commute
    (m : ℕ) (u : HermiteScale (-(m : ℤ))) :
    hermiteScaleInclusion m (hermiteFourier (-(m : ℤ)) u) =
      hermiteFourier (-((m + 1 : ℕ) : ℤ)) (hermiteScaleInclusion m u) := by
  apply Subtype.ext
  funext n
  rw [hermiteScaleInclusion_apply, hermiteFourier_apply,
    hermiteFourier_apply, hermiteScaleInclusion_apply]
  ring

end

end MeyerGeneralProblem
