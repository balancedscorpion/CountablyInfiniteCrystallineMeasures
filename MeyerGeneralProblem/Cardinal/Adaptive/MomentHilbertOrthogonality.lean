module

public import MeyerGeneralProblem.Cardinal.Adaptive.MomentHilbertOperators

@[expose] public section

/-! # Exact Hilbert norm splitting for literal moment coordinate projections -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section

variable {ι : Type*}

theorem moment_norm_sq (u : MomentHilbert ι) : ‖u‖^2=∑' i, ‖u i‖^2 := by
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using lp.norm_rpow_eq_tsum (f := u) (by norm_num)

theorem moment_norm_sq_summable (u : MomentHilbert ι) : Summable (fun i => ‖u i‖^2) := by
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using (lp.memℓp u).summable (by norm_num)

/-- Disjoint coordinate supports are genuinely orthogonal in the complete
Hilbert norm; this includes infinite coordinate sets. -/
theorem moment_disjoint_norm_sq (u v : MomentHilbert ι)
    (hdisj : ∀ i, u i=0 ∨ v i=0) : ‖u+v‖^2=‖u‖^2+‖v‖^2 := by
  rw [moment_norm_sq,moment_norm_sq,moment_norm_sq,← (moment_norm_sq_summable u).tsum_add (moment_norm_sq_summable v)]
  apply tsum_congr
  intro i
  change ‖u i+v i‖^2=‖u i‖^2+‖v i‖^2
  rcases hdisj i with h | h <;> simp [h]

theorem momentProjection_add_compl (s : Set ι) (u : MomentHilbert ι) :
    momentProjection s u+momentProjection sᶜ u=u := by
  ext i
  change momentProjection s u i+momentProjection sᶜ u i=u i
  simp only [momentProjection_apply,Set.mem_compl_iff]
  by_cases h : i ∈ s <;> simp [h]

/-- Exact Pythagorean splitting across any actual coordinate partition. -/
theorem momentProjection_norm_sq_split (s : Set ι) (u : MomentHilbert ι) :
    ‖momentProjection s u‖^2+‖momentProjection sᶜ u‖^2=‖u‖^2 := by
  rw [← moment_disjoint_norm_sq, momentProjection_add_compl]
  intro i
  simp only [momentProjection_apply,Set.mem_compl_iff]
  by_cases h : i ∈ s <;> simp [h]

/-- A genuine two-block estimate in the Hilbert norm. Each input coordinate
is charged to its own partition exactly once. -/
theorem moment_partition_operator_bound (s : Set ι) (A B : MomentHilbert ι →L[ℂ] MomentHilbert ι)
    (K : ℝ) (hK : 0 ≤ K)
    (hA : ∀ u, ‖A u‖ ≤ K*‖momentProjection s u‖)
    (hB : ∀ u, ‖B u‖ ≤ K*‖momentProjection sᶜ u‖)
    (hdisj : ∀ u i, A u i=0 ∨ B u i=0) : ‖A+B‖ ≤ K := by
  apply ContinuousLinearMap.opNorm_le_bound _ hK
  intro u
  have ha := hA u
  have hb := hB u
  have hsq := moment_disjoint_norm_sq (A u) (B u) (hdisj u)
  have hsplit := momentProjection_norm_sq_split s u
  change ‖A u+B u‖ ≤ K*‖u‖
  have hqa : ‖A u‖^2 ≤ K^2*‖momentProjection s u‖^2 := by
    nlinarith [norm_nonneg (A u),norm_nonneg (momentProjection s u)]
  have hqb : ‖B u‖^2 ≤ K^2*‖momentProjection sᶜ u‖^2 := by
    nlinarith [norm_nonneg (B u),norm_nonneg (momentProjection sᶜ u)]
  have hscaled := congrArg (fun x : ℝ => K^2*x) hsplit
  nlinarith [norm_nonneg u,norm_nonneg (A u+B u),mul_nonneg hK (norm_nonneg u)]

end
end MeyerGeneralProblem.Adaptive
