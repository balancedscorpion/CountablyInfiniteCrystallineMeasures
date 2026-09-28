module

public import MeyerGeneralProblem.Atomic.PointMass
public import MeyerGeneralProblem.Carrier.TwoSided

@[expose] public section

/-!
# Schwartz tests isolating one carrier node

Every node of a strictly increasing two-sided carrier has two positive
neighbour gaps.  A smooth bump supported inside half the smaller gap therefore
equals one at the selected node and vanishes at every other carrier node.
This is the distributional coordinate test used to prove injectivity of the
genuine Dirac synthesis.
-/

namespace MeyerGeneralProblem

noncomputable section

open scoped ContDiff

namespace TwoSidedCarrier

variable (Λ : TwoSidedCarrier)

/-- The smaller of the two physical gaps adjacent to a carrier node. -/
def isolationGap (i : ℤ) : ℝ :=
  min (Λ i - Λ (i - 1)) (Λ (i + 1) - Λ i)

theorem isolationGap_pos (i : ℤ) : 0 < Λ.isolationGap i := by
  apply lt_min
  · exact sub_pos.mpr (Λ.point_lt_point (by omega))
  · exact sub_pos.mpr (Λ.point_lt_point (by omega))

/-- A bump whose support radius is half the smaller adjacent carrier gap. -/
def isolationBump (i : ℤ) : ContDiffBump (Λ i) where
  rIn := Λ.isolationGap i / 4
  rOut := Λ.isolationGap i / 2
  rIn_pos := div_pos (Λ.isolationGap_pos i) (by norm_num)
  rIn_lt_rOut := by
    have h := Λ.isolationGap_pos i
    linarith

/-- Complex Schwartz test equal to one at `Λ i` and supported before either
neighbouring carrier node. -/
def isolationSchwartz (i : ℤ) : SchwartzMap ℝ ℂ := by
  let b := Λ.isolationBump i
  let f : ℝ → ℂ := Complex.ofRealCLM ∘ b
  have hfSupport : HasCompactSupport f :=
    b.hasCompactSupport.comp_left rfl
  have hfSmooth : ContDiff ℝ ∞ f :=
    Complex.ofRealCLM.contDiff.comp b.contDiff
  exact hfSupport.toSchwartzMap hfSmooth

@[simp]
theorem isolationSchwartz_self (i : ℤ) :
    Λ.isolationSchwartz i (Λ i) = 1 := by
  simp only [isolationSchwartz]
  change ((Λ.isolationBump i (Λ i) : ℝ) : ℂ) = 1
  rw [(Λ.isolationBump i).one_of_mem_closedBall]
  · norm_num
  · simpa using (Λ.isolationBump i).rIn_pos.le

theorem isolationGap_le_dist {i j : ℤ} (hij : i ≠ j) :
    Λ.isolationGap i ≤ dist (Λ j) (Λ i) := by
  rcases lt_or_gt_of_ne hij.symm with hji | hij'
  · have hindex : j ≤ i - 1 := by omega
    have hpoint : Λ j ≤ Λ (i - 1) := Λ.point_le_point hindex
    have hleft : Λ.isolationGap i ≤ Λ i - Λ (i - 1) := min_le_left _ _
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr (hpoint.trans
      (Λ.point_le_point (by omega))))]
    linarith
  · have hindex : i + 1 ≤ j := by omega
    have hpoint : Λ (i + 1) ≤ Λ j := Λ.point_le_point hindex
    have hright : Λ.isolationGap i ≤ Λ (i + 1) - Λ i := min_le_right _ _
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr
      (Λ.point_le_point (by omega)))]
    linarith

@[simp]
theorem isolationSchwartz_of_ne {i j : ℤ} (hij : i ≠ j) :
    Λ.isolationSchwartz i (Λ j) = 0 := by
  simp only [isolationSchwartz]
  change ((Λ.isolationBump i (Λ j) : ℝ) : ℂ) = 0
  rw [(Λ.isolationBump i).zero_of_le_dist]
  · norm_num
  · change Λ.isolationGap i / 2 ≤ dist (Λ j) (Λ i)
    exact (div_le_self (Λ.isolationGap_pos i).le (by norm_num)).trans
      (Λ.isolationGap_le_dist hij)

end TwoSidedCarrier

end

end MeyerGeneralProblem
