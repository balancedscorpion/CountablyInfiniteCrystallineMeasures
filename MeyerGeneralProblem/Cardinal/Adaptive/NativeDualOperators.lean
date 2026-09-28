module

public import MeyerGeneralProblem.Cardinal.Adaptive.NativeTranslations
public import MeyerGeneralProblem.Hermite.DistributionCoherence
public import Mathlib.Analysis.Normed.Operator.Extend
import all Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.Analysis.InnerProductSpace.Adjoint
import all Mathlib.Analysis.InnerProductSpace.Adjoint

@[expose] public section

/-!
# Constructed native operators on negative Hermite scales

The positive operators are extended from the actual dense Schwartz image using
the proved original norm estimates. Their bilinear transposes are obtained by
conjugating the Hilbert adjoint on both sides. This matches the distributional
pairing `sum T_n*u_n`, rather than the sesquilinear Hilbert pairing. The public
operators realize the complete distributional dilation, translation and modulation
on every Schwartz test and retain the proved same-order bounds.
-/

namespace MeyerGeneralProblem.Adaptive
noncomputable section

def positiveLift (m : ℕ) (U : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ) :
    HermiteScale (m : ℤ) →L[ℂ] HermiteScale (m : ℤ) :=
  ((schwartzToHermiteScale m).comp U).toLinearMap.extendOfNorm
    (schwartzToHermiteScale m).toLinearMap

private theorem positiveLift_schwartz (m : ℕ)
    (U : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ)
    (hU : ∃ C : ℝ, ∀ f, ‖schwartzToHermiteScale m (U f)‖ ≤
      C * ‖schwartzToHermiteScale m f‖) (f : SchwartzMap ℝ ℂ) :
    positiveLift m U (schwartzToHermiteScale m f) = schwartzToHermiteScale m (U f) :=
  LinearMap.extendOfNorm_eq (schwartzToHermiteScale_denseRange m) hU f

private theorem positiveLift_opNorm_le (m : ℕ)
    (U : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hU : ∀ f, ‖schwartzToHermiteScale m (U f)‖ ≤ C * ‖schwartzToHermiteScale m f‖) :
    ‖positiveLift m U‖ ≤ C :=
  LinearMap.opNorm_extendOfNorm_le (schwartzToHermiteScale_denseRange m) hC hU

def bilinearTransposeLM (m : ℕ)
    (A : HermiteScale (m : ℤ) →L[ℂ] HermiteScale (m : ℤ)) :
    HermiteScale (-(m : ℤ)) →ₗ[ℂ] HermiteScale (-(m : ℤ)) where
  toFun T := star (A.adjoint (star T))
  map_add' T S := by simp
  map_smul' c T := by simp

def bilinearTranspose (m : ℕ)
    (A : HermiteScale (m : ℤ) →L[ℂ] HermiteScale (m : ℤ)) :
    HermiteScale (-(m : ℤ)) →L[ℂ] HermiteScale (-(m : ℤ)) :=
  (bilinearTransposeLM m A).mkContinuous ‖A‖ fun T => by
    change ‖star (A.adjoint (star T))‖ ≤ _
    simpa only [norm_star, LinearIsometryEquiv.norm_map] using A.adjoint.le_opNorm (star T)

private theorem bilinearTranspose_opNorm_le (m : ℕ)
    (A : HermiteScale (m : ℤ) →L[ℂ] HermiteScale (m : ℤ)) :
    ‖bilinearTranspose m A‖ ≤ ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro T
  change ‖star (A.adjoint (star T))‖ ≤ _
  simpa only [norm_star, LinearIsometryEquiv.norm_map] using A.adjoint.le_opNorm (star T)

private theorem pairing_inner (m : ℕ) (T : HermiteScale (-(m : ℤ)))
    (u : HermiteScale (m : ℤ)) :
    hermiteScalePairing (m : ℤ) T u = inner ℂ (star T) u := by
  rw [hermiteScalePairing, lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  simp [RCLike.inner_apply, mul_comm]

private theorem bilinearTranspose_pairing (m : ℕ)
    (A : HermiteScale (m : ℤ) →L[ℂ] HermiteScale (m : ℤ))
    (T : HermiteScale (-(m : ℤ))) (u : HermiteScale (m : ℤ)) :
    hermiteScalePairing (m : ℤ) (bilinearTranspose m A T) u =
      hermiteScalePairing (m : ℤ) T (A u) := by
  rw [pairing_inner, pairing_inner]
  change inner ℂ (star (star (A.adjoint (star T)))) u = inner ℂ (star T) (A u)
  rw [star_star, ContinuousLinearMap.adjoint_inner_left]

private theorem native_pullback_apply (m : ℕ)
    (U : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ)
    (hU : ∃ C : ℝ, ∀ f, ‖schwartzToHermiteScale m (U f)‖ ≤
      C * ‖schwartzToHermiteScale m f‖)
    (T : HermiteScale (-(m : ℤ))) (f : SchwartzMap ℝ ℂ) :
    hermiteScaleDistribution m (bilinearTranspose m (positiveLift m U) T) f =
      hermiteScaleDistribution m T (U f) := by
  rw [hermiteScaleDistribution_apply, hermiteScaleDistribution_apply,
    bilinearTranspose_pairing, positiveLift_schwartz m U hU]

theorem nonzero_of_dilation_range (a : ℝ) (ha : a ∈ Set.Icc (1/2:ℝ) 2) : a ≠ 0 := by
  have h : 0 < a := by linarith [ha.1]
  exact h.ne'

/-- Constructed same-order native dilation on the whole negative Hermite scale. -/
def nativeDilation (m : ℕ) (a : ℝ) (ha : a ∈ Set.Icc (1/2:ℝ) 2) :
    HermiteScale (-(m : ℤ)) →L[ℂ] HermiteScale (-(m : ℤ)) :=
  bilinearTranspose m (positiveLift m (combSchwartzDilation a (nonzero_of_dilation_range a ha)))

/-- The native dilation realizes the actual complete distributional pushforward. -/
theorem nativeDilation_realizes (m : ℕ) (a : ℝ) (ha : a ∈ Set.Icc (1/2:ℝ) 2)
    (T : HermiteScale (-(m : ℤ))) :
    hermiteScaleDistribution m (nativeDilation m a ha T) =
      combDistributionDilation a (nonzero_of_dilation_range a ha) (hermiteScaleDistribution m T) := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_hermite_dilation_bound m
  ext f
  exact native_pullback_apply m _ ⟨C, hbound a _ ha⟩ T f

/-- One operator-norm bound controls all compact-range native dilations. -/
theorem exists_nativeDilation_norm_bound (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℝ) (ha : a ∈ Set.Icc (1/2:ℝ) 2),
      ‖nativeDilation m a ha‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_hermite_dilation_bound m
  refine ⟨C, hC, ?_⟩
  intro a ha
  exact (bilinearTranspose_opNorm_le m _).trans
    (positiveLift_opNorm_le m _ C hC.le (hbound a _ ha))

/-- Constructed actual translation operator at the same negative Hermite order. -/
def nativeTranslation (m : ℕ) (a : ℝ) :
    HermiteScale (-(m : ℤ)) →L[ℂ] HermiteScale (-(m : ℤ)) :=
  bilinearTranspose m (positiveLift m (combSchwartzTranslation a))

/-- Native translation agrees with the whole distribution on every Schwartz test. -/
theorem nativeTranslation_realizes (m : ℕ) (a : ℝ) (T : HermiteScale (-(m : ℤ))) :
    hermiteScaleDistribution m (nativeTranslation m a T) =
      combDistributionTranslation a (hermiteScaleDistribution m T) := by
  obtain ⟨C, hC, hbound⟩ := exists_hermite_translation_bound m
  ext f
  exact native_pullback_apply m _ ⟨C * (1+|a|)^(2*m), hbound a⟩ T f

/-- Native translation retains the original degree-`2*m` polynomial norm bound. -/
theorem exists_nativeTranslation_norm_bound (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : ℝ, ‖nativeTranslation m a‖ ≤ C * (1+|a|)^(2*m) := by
  obtain ⟨C, hC, hbound⟩ := exists_hermite_translation_bound m
  refine ⟨C, hC, ?_⟩
  intro a
  exact (bilinearTranspose_opNorm_le m _).trans
    (positiveLift_opNorm_le m _ _ (by positivity) (hbound a))

/-- Constructed multiplication by the actual character on the same negative scale. -/
def nativeModulation (m : ℕ) (a : ℝ) :
    HermiteScale (-(m : ℤ)) →L[ℂ] HermiteScale (-(m : ℤ)) :=
  bilinearTranspose m (positiveLift m (combSchwartzModulation a))

/-- Native modulation realizes actual distributional multiplication without a
representation premise or any loss of Hermite order. -/
theorem nativeModulation_realizes (m : ℕ) (a : ℝ) (T : HermiteScale (-(m : ℤ))) :
    hermiteScaleDistribution m (nativeModulation m a T) =
      combDistributionModulation a (hermiteScaleDistribution m T) := by
  obtain ⟨C, hC, hbound⟩ := exists_hermite_modulation_bound m
  ext f
  exact native_pullback_apply m _ ⟨C * (1+|a|)^(2*m), hbound a⟩ T f

/-- Native modulation has the same uniform polynomial degree as translation. -/
theorem exists_nativeModulation_norm_bound (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : ℝ, ‖nativeModulation m a‖ ≤ C * (1+|a|)^(2*m) := by
  obtain ⟨C, hC, hbound⟩ := exists_hermite_modulation_bound m
  refine ⟨C, hC, ?_⟩
  intro a
  exact (bilinearTranspose_opNorm_le m _).trans
    (positiveLift_opNorm_le m _ _ (by positivity) (hbound a))

end
end MeyerGeneralProblem.Adaptive
