module

public import MeyerGeneralProblem.Cardinal.Adaptive.NativeMultipliers

@[expose] public section

/-!
# Actual multipliers between original negative Hermite scales

The positive map goes from order `q` to order `p`; its bilinear transpose goes
from order `-p` to order `-q`. Dense extension and conjugation of the Hilbert
adjoint construct the operator. The distributional action and bounds below are
derived from the checked positive estimates, including the sixfold selector loss.
-/
namespace MeyerGeneralProblem.Adaptive
noncomputable section

def multiplierPositiveLift (p q : ℕ) (χ : ℝ → ℂ) :
    HermiteScale (q:ℤ) →L[ℂ] HermiteScale (p:ℤ) :=
  ((schwartzToHermiteScale p).comp (SchwartzMap.smulLeftCLM ℂ χ)).toLinearMap.extendOfNorm
    (schwartzToHermiteScale q).toLinearMap

def multiplierTransposeLM (p q : ℕ)
    (A : HermiteScale (q:ℤ) →L[ℂ] HermiteScale (p:ℤ)) :
    HermiteScale (-(p:ℤ)) →ₗ[ℂ] HermiteScale (-(q:ℤ)) where
  toFun T := star (A.adjoint (star T))
  map_add' T S := by simp
  map_smul' c T := by simp

/-- The native multiplier constructed by dense extension and bilinear duality.
Its distributional interpretation is established under explicit derivative
bounds by `nativeMultiplier_realizes`. -/
def nativeMultiplier (p q : ℕ) (χ : ℝ → ℂ) :
    HermiteScale (-(p:ℤ)) →L[ℂ] HermiteScale (-(q:ℤ)) :=
  (multiplierTransposeLM p q (multiplierPositiveLift p q χ)).mkContinuous
    ‖multiplierPositiveLift p q χ‖ fun T => by
      change ‖star ((multiplierPositiveLift p q χ).adjoint (star T))‖ ≤ _
      simpa only [norm_star, LinearIsometryEquiv.norm_map] using
        (multiplierPositiveLift p q χ).adjoint.le_opNorm (star T)

private theorem nativeMultiplier_norm_le (p q : ℕ) (χ : ℝ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ f : SchwartzMap ℝ ℂ,
      ‖schwartzToHermiteScale p (SchwartzMap.smulLeftCLM ℂ χ f)‖ ≤
        B * ‖schwartzToHermiteScale q f‖) : ‖nativeMultiplier p q χ‖ ≤ B := by
  have hl : ‖multiplierPositiveLift p q χ‖ ≤ B :=
    LinearMap.opNorm_extendOfNorm_le (schwartzToHermiteScale_denseRange q) hB hb
  apply ContinuousLinearMap.opNorm_le_bound _ hB
  intro T
  change ‖star ((multiplierPositiveLift p q χ).adjoint (star T))‖ ≤ _
  have h := (multiplierPositiveLift p q χ).adjoint.le_opNorm (star T)
  simp only [norm_star, LinearIsometryEquiv.norm_map] at h ⊢
  exact h.trans (mul_le_mul_of_nonneg_right hl (norm_nonneg _))

private theorem nativeMultiplier_realizes_of_bound (p q : ℕ) (χ : ℝ → ℂ)
    (hb : ∃ B : ℝ, ∀ f : SchwartzMap ℝ ℂ,
      ‖schwartzToHermiteScale p (SchwartzMap.smulLeftCLM ℂ χ f)‖ ≤
        B * ‖schwartzToHermiteScale q f‖)
    (T : HermiteScale (-(p:ℤ))) :
    hermiteScaleDistribution q (nativeMultiplier p q χ T) =
      TemperedDistribution.smulLeftCLM ℂ χ (hermiteScaleDistribution p T) := by
  have hp (r : ℕ) (U : HermiteScale (-(r:ℤ))) (u : HermiteScale (r:ℤ)) :
      hermiteScalePairing (r:ℤ) U u = inner ℂ (star U) u := by
    rw [hermiteScalePairing, lp.inner_eq_tsum]
    apply tsum_congr
    intro n
    simp [RCLike.inner_apply, mul_comm]
  have hl (f : SchwartzMap ℝ ℂ) :
      multiplierPositiveLift p q χ (schwartzToHermiteScale q f) =
        schwartzToHermiteScale p (SchwartzMap.smulLeftCLM ℂ χ f) :=
    LinearMap.extendOfNorm_eq (schwartzToHermiteScale_denseRange q) hb f
  ext f
  rw [TemperedDistribution.smulLeftCLM_apply_apply, hermiteScaleDistribution_apply,
    hermiteScaleDistribution_apply, hp, hp]
  change inner ℂ (star (star ((multiplierPositiveLift p q χ).adjoint (star T))))
    (schwartzToHermiteScale q f) = _
  rw [star_star, ContinuousLinearMap.adjoint_inner_left, hl]

/-- Exact whole-distribution action of the constructed native multiplier,
derived from polynomial derivative bounds with the checked integer order budget. -/
theorem nativeMultiplier_realizes (p q d : ℕ) (hdegree : 2*p+d ≤ 2*q)
    (A : ℝ) (hA : 0 ≤ A) (χ : ℝ → ℂ) (hχ : χ.HasTemperateGrowth)
    (hb : ∀ r ≤ 2*p, ∀ x, ‖iteratedDeriv r χ x‖ ≤ A*(1+|x|)^d)
    (T : HermiteScale (-(p:ℤ))) :
    hermiteScaleDistribution q (nativeMultiplier p q χ T) =
      TemperedDistribution.smulLeftCLM ℂ χ (hermiteScaleDistribution p T) := by
  obtain ⟨B,hB,hbound⟩ := exists_native_polynomial_multiplier_bound p q d hdegree A hA
  exact nativeMultiplier_realizes_of_bound p q χ ⟨B,hbound χ hχ hb⟩ T

/-- A single original operator-norm bound controls every multiplier in the
given polynomial derivative class, before the multiplier is chosen. -/
theorem exists_nativeMultiplier_polynomial_norm_bound (p q d : ℕ)
    (hdegree : 2*p+d ≤ 2*q) (A : ℝ) (hA : 0 ≤ A) :
    ∃ B : ℝ, 0 < B ∧ ∀ (χ : ℝ → ℂ), χ.HasTemperateGrowth →
      (∀ r ≤ 2*p, ∀ x, ‖iteratedDeriv r χ x‖ ≤ A*(1+|x|)^d) →
        ‖nativeMultiplier p q χ‖ ≤ B := by
  obtain ⟨B,hB,hbound⟩ := exists_native_polynomial_multiplier_bound p q d hdegree A hA
  exact ⟨B,hB,fun χ hχ hb => nativeMultiplier_norm_le p q χ B hB.le (hbound χ hχ hb)⟩

/-- Uniformly bounded derivatives give a same-order operator on the negative
original Hermite scale. -/
theorem exists_nativeMultiplier_bounded_norm_bound (p : ℕ) (A : ℝ) (hA : 0 ≤ A) :
    ∃ B : ℝ, 0 < B ∧ ∀ (χ : ℝ → ℂ), χ.HasTemperateGrowth →
      (∀ r ≤ 2*p, ∀ x, ‖iteratedDeriv r χ x‖ ≤ A) →
        ‖nativeMultiplier p p χ‖ ≤ B := by
  simpa only [pow_zero, mul_one] using
    exists_nativeMultiplier_polynomial_norm_bound p p 0 (by omega) A hA


/-- Actual selectors with derivative growth `5*r` act from original H_-p to
H_-(6*p), with equality of whole distributions on every Schwartz test. -/
theorem nativeMultiplier_selector_realizes (p : ℕ) (C : ℕ → ℝ)
    (χ : ℝ → ℂ) (hχ : χ.HasTemperateGrowth)
    (hb : ∀ r ≤ 2*p, ∀ x, ‖iteratedDeriv r χ x‖ ≤ C r*(1+|x|)^(5*r))
    (T : HermiteScale (-(p:ℤ))) :
    hermiteScaleDistribution (6*p) (nativeMultiplier p (6*p) χ T) =
      TemperedDistribution.smulLeftCLM ℂ χ (hermiteScaleDistribution p T) := by
  obtain ⟨B,hB,hbound⟩ := exists_native_selector_multiplier_bound p C
  exact nativeMultiplier_realizes_of_bound p (6*p) χ ⟨B,hbound χ hχ hb⟩ T

/-- The negative selector bound depends only on p and the fixed derivative
constants, not the selector, selected subset, support, or cardinality. -/
theorem exists_nativeMultiplier_selector_norm_bound (p : ℕ) (C : ℕ → ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ (χ : ℝ → ℂ), χ.HasTemperateGrowth →
      (∀ r ≤ 2*p, ∀ x, ‖iteratedDeriv r χ x‖ ≤ C r*(1+|x|)^(5*r)) →
        ‖nativeMultiplier p (6*p) χ‖ ≤ B := by
  obtain ⟨B,hB,hbound⟩ := exists_native_selector_multiplier_bound p C
  exact ⟨B,hB,fun χ hχ hb => nativeMultiplier_norm_le p (6*p) χ B hB.le (hbound χ hχ hb)⟩

/-- Actual selectors with derivative growth `6*r` act from original H_-p to
H_-(6*p), with equality of whole distributions on every Schwartz test. -/
theorem nativeMultiplier_selector_six_growth_realizes (p : ℕ) (C : ℕ → ℝ)
    (χ : ℝ → ℂ) (hχ : χ.HasTemperateGrowth)
    (hb : ∀ r ≤ 2*p, ∀ x, ‖iteratedDeriv r χ x‖ ≤ C r*(1+|x|)^(6*r))
    (T : HermiteScale (-(p:ℤ))) :
    hermiteScaleDistribution (6*p) (nativeMultiplier p (6*p) χ T) =
      TemperedDistribution.smulLeftCLM ℂ χ (hermiteScaleDistribution p T) := by
  obtain ⟨B,hB,hbound⟩ := exists_native_selector_six_growth_bound p C
  exact nativeMultiplier_realizes_of_bound p (6*p) χ ⟨B,hbound χ hχ hb⟩ T

/-- The negative selector bound depends only on p and the fixed derivative
constants, not the selector, selected subset, support, or cardinality. -/
theorem exists_nativeMultiplier_selector_six_growth_norm_bound (p : ℕ) (C : ℕ → ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ (χ : ℝ → ℂ), χ.HasTemperateGrowth →
      (∀ r ≤ 2*p, ∀ x, ‖iteratedDeriv r χ x‖ ≤ C r*(1+|x|)^(6*r)) →
        ‖nativeMultiplier p (6*p) χ‖ ≤ B := by
  obtain ⟨B,hB,hbound⟩ := exists_native_selector_six_growth_bound p C
  exact ⟨B,hB,fun χ hχ hb => nativeMultiplier_norm_le p (6*p) χ B hB.le (hbound χ hχ hb)⟩

end
end MeyerGeneralProblem.Adaptive
