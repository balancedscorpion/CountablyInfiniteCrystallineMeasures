module

public import MeyerGeneralProblem.Atomic.BesselSynthesis
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import all Mathlib.Algebra.Order.BigOperators.Ring.Finset

@[expose] public section

/-!
# Finite Gram-form Schur bounds

This module connects pointwise localization of a Hermitian Gram kernel to the
finite quadratic estimate needed by `BesselAnalysis.of_finsupp_gram_bound`.
The scalar lemma is deliberately finite: no infinite matrix or bounded
operator is assumed before the row estimate has been proved.
-/

namespace MeyerGeneralProblem

noncomputable section

open scoped BigOperators

/-- A symmetric nonnegative finite kernel with row sums bounded by `R` has
quadratic form at most `R` times the coefficient energy. -/
theorem finite_symmetric_schur_quadratic_le
    {ι : Type*} (s : Finset ι) (g : ι → ι → ℝ) (a : ι → ℝ) {R : ℝ}
    (hg : ∀ i ∈ s, ∀ j ∈ s, 0 ≤ g i j)
    (hsymm : ∀ i ∈ s, ∀ j ∈ s, g i j = g j i)
    (hrow : ∀ i ∈ s, ∑ j ∈ s, g i j ≤ R) :
    ∑ i ∈ s, ∑ j ∈ s, g i j * a i * a j ≤
      R * ∑ i ∈ s, a i ^ 2 := by
  let Q : ℝ := ∑ i ∈ s, ∑ j ∈ s, g i j * a i * a j
  have htwo : 2 * Q ≤
      ∑ i ∈ s, ∑ j ∈ s, g i j * (a i ^ 2 + a j ^ 2) := by
    dsimp [Q]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    calc
      2 * (g i j * a i * a j) =
          g i j * (2 * a i * a j) := by ring
      _ ≤ g i j * (a i ^ 2 + a j ^ 2) := by
        exact mul_le_mul_of_nonneg_left (two_mul_le_add_sq (a i) (a j))
          (hg i hi j hj)
  have hsplit :
      (∑ i ∈ s, ∑ j ∈ s, g i j * (a i ^ 2 + a j ^ 2)) =
        2 * ∑ i ∈ s, a i ^ 2 * (∑ j ∈ s, g i j) := by
    calc
      (∑ i ∈ s, ∑ j ∈ s, g i j * (a i ^ 2 + a j ^ 2)) =
          (∑ i ∈ s, ∑ j ∈ s, g i j * a i ^ 2) +
          ∑ i ∈ s, ∑ j ∈ s, g i j * a j ^ 2 := by
        simp only [mul_add, Finset.sum_add_distrib]
      _ = (∑ i ∈ s, a i ^ 2 * (∑ j ∈ s, g i j)) +
          ∑ j ∈ s, a j ^ 2 * (∑ i ∈ s, g j i) := by
        congr 1
        · apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          ring
        · rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro j hj
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          rw [hsymm i hi j hj]
          ring
      _ = 2 * ∑ i ∈ s, a i ^ 2 * (∑ j ∈ s, g i j) := by ring
  have hrows :
      ∑ i ∈ s, a i ^ 2 * (∑ j ∈ s, g i j) ≤
        R * ∑ i ∈ s, a i ^ 2 := by
    calc
      (∑ i ∈ s, a i ^ 2 * (∑ j ∈ s, g i j)) ≤
          ∑ i ∈ s, a i ^ 2 * R := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (hrow i hi) (sq_nonneg (a i))
      _ = R * ∑ i ∈ s, a i ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
  rw [hsplit] at htwo
  dsimp [Q] at htwo
  nlinarith

variable {ι H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Uniform absolute row-sum control of all finite Gram sections bounds the
explicit finite Gram form.  Hermitian symmetry supplies the column estimate,
so only row sums appear in the hypothesis. -/
theorem BesselAnalysis.finsuppGramForm_re_le_of_row_bound
    (v : ι → H) {R : ℝ}
    (hrow : ∀ s : Finset ι, ∀ i ∈ s,
      ∑ j ∈ s, ‖inner ℂ (v i) (v j)‖ ≤ R)
    (c : ι →₀ ℂ) :
    (BesselAnalysis.finsuppGramForm v c).re ≤
      R * (c.sum fun _ z ↦ ‖z‖ ^ 2) := by
  let s : Finset ι := c.support
  have hnorm :
      ‖BesselAnalysis.finsuppGramForm v c‖ ≤
        ∑ j ∈ s, ∑ i ∈ s,
          ‖inner ℂ (v j) (v i)‖ * ‖c j‖ * ‖c i‖ := by
    rw [BesselAnalysis.finsuppGramForm, Finsupp.sum]
    change ‖∑ j ∈ s, c j *
      ∑ i ∈ s, starRingEnd ℂ (c i) * inner ℂ (v i) (v j)‖ ≤ _
    calc
      ‖∑ j ∈ s, c j *
          ∑ i ∈ s, starRingEnd ℂ (c i) * inner ℂ (v i) (v j)‖ ≤
          ∑ j ∈ s, ‖c j *
            ∑ i ∈ s, starRingEnd ℂ (c i) * inner ℂ (v i) (v j)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ j ∈ s, ∑ i ∈ s,
          ‖inner ℂ (v j) (v i)‖ * ‖c j‖ * ‖c i‖ := by
        apply Finset.sum_le_sum
        intro j hj
        rw [norm_mul]
        calc
          ‖c j‖ * ‖∑ i ∈ s,
              starRingEnd ℂ (c i) * inner ℂ (v i) (v j)‖ ≤
              ‖c j‖ * ∑ i ∈ s,
                ‖starRingEnd ℂ (c i) * inner ℂ (v i) (v j)‖ := by
            exact mul_le_mul_of_nonneg_left (norm_sum_le _ _)
              (norm_nonneg (c j))
          _ = ∑ i ∈ s,
              ‖inner ℂ (v j) (v i)‖ * ‖c j‖ * ‖c i‖ := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            rw [norm_mul, RCLike.norm_conj, norm_inner_symm]
            ring
  calc
    (BesselAnalysis.finsuppGramForm v c).re ≤
        ‖BesselAnalysis.finsuppGramForm v c‖ := Complex.re_le_norm _
    _ ≤ ∑ j ∈ s, ∑ i ∈ s,
        ‖inner ℂ (v j) (v i)‖ * ‖c j‖ * ‖c i‖ := hnorm
    _ ≤ R * ∑ j ∈ s, ‖c j‖ ^ 2 := by
      apply finite_symmetric_schur_quadratic_le
      · intro i hi j hj
        exact norm_nonneg _
      · intro i hi j hj
        exact norm_inner_symm (v i) (v j)
      · intro i hi
        exact hrow s i hi
    _ = R * (c.sum fun _ z ↦ ‖z‖ ^ 2) := by
      rw [Finsupp.sum]

variable [CompleteSpace H]

/-- Construct Bessel data from a uniform absolute row-sum bound on every
finite Gram section.  The row ceiling is written as `C²` so that `C` is the
resulting synthesis bound. -/
def BesselAnalysis.of_finsupp_gram_row_bound
    [DecidableEq ι] (v : ι → H) (C : ℝ) (hC : 0 ≤ C)
    (hrow : ∀ s : Finset ι, ∀ i ∈ s,
      ∑ j ∈ s, ‖inner ℂ (v i) (v j)‖ ≤ C ^ 2) :
    BesselAnalysis v :=
  BesselAnalysis.of_finsupp_gram_bound v C hC fun c ↦
    BesselAnalysis.finsuppGramForm_re_le_of_row_bound v hrow c

/-- Construct Bessel data from summable absolute Gram rows with one uniform
`tsum` ceiling.  Every finite section is bounded by the corresponding full
row sum, so this is the infinite-kernel form of the Schur interface. -/
def BesselAnalysis.of_summable_gram_rows
    [DecidableEq ι] (v : ι → H) (C : ℝ) (hC : 0 ≤ C)
    (hsummable : ∀ i, Summable (fun j ↦ ‖inner ℂ (v i) (v j)‖))
    (hrow : ∀ i, ∑' j, ‖inner ℂ (v i) (v j)‖ ≤ C ^ 2) :
    BesselAnalysis v :=
  BesselAnalysis.of_finsupp_gram_row_bound v C hC fun s i _hi ↦
    ((hsummable i).sum_le_tsum s (fun _ _ ↦ norm_nonneg _)).trans (hrow i)

end

end MeyerGeneralProblem
