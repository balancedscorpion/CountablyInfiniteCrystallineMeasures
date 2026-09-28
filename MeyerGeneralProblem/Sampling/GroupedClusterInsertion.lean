module

public import MeyerGeneralProblem.Sampling.GroupedHarauxInsertion
public import MeyerGeneralProblem.Sampling.GroupedFiniteFloor

@[expose] public section

/-!
# Uniform insertion of an actual bounded cluster into an Ingham family

The original separated-family lower and upper inequalities and the local
cluster lower inequality are all discharged by proved theorems. Only the
geometric inputs remain: exterior separation, positive exterior-to-cluster
distance, bounded cluster size and diameter, and strict Ingham window slack.
-/

namespace MeyerGeneralProblem

noncomputable section

open MeasureTheory

/-- An actual bounded cluster can be added uniformly to a separated Ingham
family. The constant is chosen before all finite dimensions, nodes and
coefficients; no internal cluster gap or analytic lower bound is an input. -/
theorem exists_uniform_finite_cosineIngham_insert_cluster
    (q : ℕ) {b r L d D : ℝ} (hb : 0 < b) (hr : 0 < r)
    (hL : 0 < L) (hd : 0 < d) (hD : 0 ≤ D) (hgap : 1 < 2 * b * L) :
    ∃ A' : ℝ, 0 < A' ∧ ∀ n k : ℕ, k ≤ q →
      ∀ (s : Fin n → ℝ) (ω : Fin k → ℝ),
      PairwiseFrequencySeparated s L → Function.Injective ω →
      (∀ i j, dist (ω i) (ω j) ≤ D) →
      (∀ i j, d ≤ |s i - ω j|) →
      ∀ (c : Fin n → ℂ) (a : Fin k → ℂ),
        A' * ((∑ i, ‖c i‖ ^ 2) + ∑ j, ‖a j‖ ^ 2) ≤
          ∫ t : ℝ in Set.Icc (-(b + q * r)) (b + q * r),
            ‖gramFourierPolynomial s c t + groupedExponentialPolynomial ω a t‖ ^ 2 := by
  have hW : 0 < b + (q:ℝ) * r := by positivity
  obtain ⟨C, hC, hcluster⟩ := exists_groupedFiniteExponential_localFloor_of_diameter q hW hD
  let B := fourierIntervalLargeSieveConstant * (2 * (b + q * r) + L⁻¹)
  have hB : 0 ≤ B := mul_nonneg fourierIntervalLargeSieveConstant_pos.le (by positivity)
  obtain ⟨A', hA', hinsert⟩ := exists_uniform_finite_lowerBound_insert_cluster q hr hd
    (cosineInghamFloorFactor_pos hb hgap) hB hC
  refine ⟨A', hA', ?_⟩
  intro n k hk s ω hs hω hdiam hsep
  apply hinsert b hb.le n k hk s ω hω hsep
  · exact finite_cosineIngham hb hgap s hs
  · intro c
    have hu := integral_norm_sq_le_interval_largeSieve hL
      (by linarith : -(b + q * r) ≤ b + q * r) s hs c
    convert hu using 1
    dsimp [B]
    congr 2
    ring
  · exact hcluster k hk ω hdiam

end

end MeyerGeneralProblem
