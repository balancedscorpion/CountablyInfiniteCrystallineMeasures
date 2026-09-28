module

public import MeyerGeneralProblem.Cardinal.Adaptive.DistributionDifferences
public import MeyerGeneralProblem.Cardinal.Adaptive.NativePeriodization

@[expose] public section

/-! # Whole finite differences with original native bounds -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section

/-- Actual translation difference at one fixed original native order. -/
def nativeDifference (q : ℕ) (P : ℝ) :
    HermiteScale (-(q:ℤ)) →L[ℂ] HermiteScale (-(q:ℤ)) :=
  nativeTranslation q P - ContinuousLinearMap.id ℂ _

/-- Every native difference realizes the whole distributional difference. -/
theorem nativeDifference_realizes (q : ℕ) (P : ℝ) (T : HermiteScale (-(q:ℤ))) :
    hermiteScaleDistribution q (nativeDifference q P T) =
      distributionDifference P (hermiteScaleDistribution q T) := by
  simp only [nativeDifference, distributionDifference, sub_apply,
    ContinuousLinearMap.id_apply]
  rw [← hermiteScaleDistributionCLM_apply, map_sub]
  simp only [hermiteScaleDistributionCLM_apply, nativeTranslation_realizes]

/-- The original order is unchanged by every fixed finite difference. -/
theorem nativeDifference_pow_realizes (q d : ℕ) (P : ℝ) (T : HermiteScale (-(q:ℤ))) :
    hermiteScaleDistribution q (((nativeDifference q P)^d) T) =
      (distributionDifference P : TemperedDistribution ℝ ℂ → TemperedDistribution ℝ ℂ)^[d]
        (hermiteScaleDistribution q T) := by
  induction d with
  | zero => rfl
  | succ d ih =>
      rw [pow_succ', mul_apply_eq_comp, nativeDifference_realizes, ih,
        Function.iterate_succ_apply']

/-- One uniform bound for each finite difference power over the full allowed
period interval, fixed before the source and period are chosen. -/
theorem exists_nativeDifference_pow_bound (q d : ℕ) :
    ∃ B > 0, ∀ P ∈ Set.Icc (1/2:ℝ) 2, ‖(nativeDifference q P)^d‖ ≤ B := by
  obtain ⟨A,hA,hb⟩ := exists_nativeTranslation_norm_bound q
  let C := A*3^(2*q)+1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C^d, pow_pos hC d, ?_⟩
  intro P hP
  have hp : |P| ≤ 2 := by rw [abs_of_nonneg (by linarith [hP.1])]; exact hP.2
  have ht : ‖nativeTranslation q P‖ ≤ A*3^(2*q) :=
    (hb P).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (by linarith : 1+|P| ≤ 3) _) hA.le)
  have hn : ‖nativeDifference q P‖ ≤ C := by
    apply (norm_sub_le _ _).trans
    exact add_le_add ht (ContinuousLinearMap.norm_id_le (𝕜 := ℂ) (E := HermiteScale (-(q:ℤ))))
  cases d with
  | zero =>
      change ‖ContinuousLinearMap.id ℂ (HermiteScale (-(q:ℤ)))‖ ≤ 1
      exact ContinuousLinearMap.norm_id_le
  | succ d =>
      exact (norm_pow_le' (nativeDifference q P) (Nat.succ_pos d)).trans
        (pow_le_pow_left₀ (norm_nonneg _) hn (d+1))

/-- The native monomial is exactly the whole distributional monomial map. -/
theorem nativeMonomial_realizes (q d : ℕ) (T : HermiteScale (-(q:ℤ))) :
    hermiteScaleDistribution (q+d) (nativeMonomial q d T) =
      monomialDistribution d (hermiteScaleDistribution q T) := by
  ext f
  exact nativeMonomial_apply q d T f

end
end MeyerGeneralProblem.Adaptive
