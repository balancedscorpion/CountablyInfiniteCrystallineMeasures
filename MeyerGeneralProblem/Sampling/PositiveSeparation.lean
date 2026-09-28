module

public import MeyerGeneralProblem.Sampling.SeparatedDecay
public import MeyerGeneralProblem.Gram.UniversalDecay
public import MeyerGeneralProblem.Gram.UniversalOperator
public import MeyerGeneralProblem.Atomic.GramSchur

@[expose] public section

/-!
# Positive-separation geometry and universal Gram boundedness

The separation-only part of the density-sharp argument needs `d > 0`, not
`d > 1`.  Rescaling the frequencies before taking integer floor shells
removes that artificial restriction from summable rows, uniform tails, and
the bounded universal Gram model.  No density or interpolation theorem is
assumed here.
-/

namespace MeyerGeneralProblem

open MeasureTheory

noncomputable section

/-- A dilation which turns any positive separation into separation at least
two and never contracts distances. -/
def positiveSeparationScale (d : ℝ) : ℝ := max 1 (2 / d)

theorem one_le_positiveSeparationScale (d : ℝ) :
    1 ≤ positiveSeparationScale d := le_max_left _ _

theorem positiveSeparationScale_pos (d : ℝ) :
    0 < positiveSeparationScale d := zero_lt_one.trans_le
      (one_le_positiveSeparationScale d)

theorem two_le_positiveSeparationScale_mul {d : ℝ} (hd : 0 < d) :
    2 ≤ positiveSeparationScale d * d :=
  (div_le_iff₀ hd).mp (le_max_right _ _)

theorem positiveSeparationScale_separated
    {ι : Type*} (s : ι → ℝ) {d : ℝ} (hd : 0 < d)
    (hsep : ∀ i j, i ≠ j → d ≤ |s i - s j|) :
    ∀ i j, i ≠ j →
      2 ≤ |positiveSeparationScale d * s i - positiveSeparationScale d * s j| := by
  intro i j hij
  rw [← mul_sub, abs_mul, abs_of_pos (positiveSeparationScale_pos d)]
  exact (two_le_positiveSeparationScale_mul hd).trans
    (mul_le_mul_of_nonneg_left (hsep i j hij) (positiveSeparationScale_pos d).le)

/-- Dilating the shell coordinate loses at most the square of the dilation
in the inverse-square distance envelope. -/
theorem inverseSquareDistance_le_scaled {q : ℝ} (hq : 1 ≤ q) (x : ℝ) :
    1 / (1 + |x|) ^ 2 ≤ q ^ 2 * (1 / (1 + |q * x|) ^ 2) := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  rw [abs_mul, abs_of_pos hq0, mul_one_div]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hlin : 1 + q * |x| ≤ q * (1 + |x|) := by nlinarith
  have hsq : (1 + q * |x|) ^ 2 ≤ (q * (1 + |x|)) ^ 2 := by
    gcongr
  nlinarith [hsq]

/-- Explicit uniform inverse-square row bound for a `d`-separated family. -/
def positiveSeparationSchurConstant (d : ℝ) : ℝ :=
  4 * positiveSeparationScale d ^ 2 * ∑' k : ℤ, integerUnitSlabEnvelope k

theorem positiveSeparationSchurConstant_nonneg (d : ℝ) :
    0 ≤ positiveSeparationSchurConstant d := by
  unfold positiveSeparationSchurConstant
  apply mul_nonneg (by positivity)
  apply tsum_nonneg
  intro k
  unfold integerUnitSlabEnvelope
  positivity

/-- Every finite inverse-square row has a bound independent of its center
and finite support under positive separation alone. -/
theorem sum_inverseSquareDistance_le_of_posSeparated
    {ι : Type*} [DecidableEq ι] (s : ι → ℝ) {d : ℝ} (hd : 0 < d)
    (hsep : ∀ i j, i ≠ j → d ≤ |s i - s j|)
    (a : ℝ) (U : Finset ι) :
    ∑ i ∈ U, 1 / (1 + |s i - a|) ^ 2 ≤ positiveSeparationSchurConstant d := by
  let q := positiveSeparationScale d
  let shell : ι → ℤ := fun i => ⌊q * (s i - a)⌋
  have hq : 1 ≤ q := one_le_positiveSeparationScale d
  have hshell : Function.Injective shell := by
    intro i j hij
    by_contra hne
    have hfar := positiveSeparationScale_separated s hd hsep i j hne
    have hnear : |q * (s i - a) - q * (s j - a)| < 1 :=
      Int.abs_sub_lt_one_of_floor_eq_floor hij
    have heq : q * (s i - a) - q * (s j - a) = q * s i - q * s j := by ring
    rw [heq] at hnear
    linarith
  have hmajorant (i : ι) : 1 / (1 + |s i - a|) ^ 2 ≤
      (4 * q ^ 2) * integerUnitSlabEnvelope (shell i) := by
    calc
      _ ≤ q ^ 2 * (1 / (1 + |q * (s i - a)|) ^ 2) :=
        inverseSquareDistance_le_scaled hq _
      _ ≤ q ^ 2 * (4 * integerUnitSlabEnvelope (shell i)) :=
        mul_le_mul_of_nonneg_left
          (inverseSquareDistance_le_floorMajorant _) (sq_nonneg q)
      _ = _ := by ring
  calc
    _ ≤ ∑ i ∈ U, (4 * q ^ 2) * integerUnitSlabEnvelope (shell i) :=
      Finset.sum_le_sum fun i hi => hmajorant i
    _ = ∑ k ∈ U.image shell, (4 * q ^ 2) * integerUnitSlabEnvelope k :=
      (Finset.sum_image (s := U)
        (f := fun k => (4 * q ^ 2) * integerUnitSlabEnvelope k) hshell.injOn).symm
    _ ≤ ∑' k : ℤ, (4 * q ^ 2) * integerUnitSlabEnvelope k :=
      (summable_integerUnitSlabEnvelope.mul_left (4 * q ^ 2)).sum_le_tsum _
        (fun k hk => by unfold integerUnitSlabEnvelope; positivity)
    _ = positiveSeparationSchurConstant d := by
      rw [tsum_mul_left]
      rfl

/-- Positive separation suffices for summability of each distance row. -/
theorem summable_inverseSquareDistance_of_posSeparated
    {ι : Type*} [DecidableEq ι] (s : ι → ℝ) {d : ℝ} (hd : 0 < d)
    (hsep : ∀ i j, i ≠ j → d ≤ |s i - s j|) (a : ℝ) :
    Summable (fun i : ι => 1 / (1 + |s i - a|) ^ 2) := by
  let q := positiveSeparationScale d
  have hscaled := summable_inverseSquareDistance_of_separated
    (fun i => q * s i) (by norm_num : (1 : ℝ) < 2)
    (positiveSeparationScale_separated s hd hsep) (q * a)
  apply Summable.of_nonneg_of_le (fun i => by positivity) _ (hscaled.mul_left (q ^ 2))
  intro i
  simpa only [← mul_sub] using
    inverseSquareDistance_le_scaled (one_le_positiveSeparationScale d) (s i - a)

/-- The inverse-square tails are uniformly small, with no lower bound on
the positive separation other than strict positivity. -/
theorem exists_uniform_sum_inverseSquareDistance_tail_of_posSeparated
    {ι : Type*} [DecidableEq ι] (s : ι → ℝ) {d : ℝ} (hd : 0 < d)
    (hsep : ∀ i j, i ≠ j → d ≤ |s i - s j|) :
    ∀ ε > 0, ∃ L ≥ 0, ∀ a : ℝ, ∀ U : Finset ι,
      ∑ i ∈ U with L < |s i - a|, 1 / (1 + |s i - a|) ^ 2 ≤ ε := by
  intro ε hε
  let q := positiveSeparationScale d
  have hq : 0 < q := positiveSeparationScale_pos d
  obtain ⟨L, hL, htail⟩ := exists_uniform_sum_inverseSquareDistance_tail_of_separated
    (fun i => q * s i) (by norm_num : (1 : ℝ) < 2)
    (positiveSeparationScale_separated s hd hsep) (ε / q ^ 2) (by positivity)
  refine ⟨L / q, by positivity, fun a U => ?_⟩
  have hfilter : U.filter (fun i => L / q < |s i - a|) =
      U.filter (fun i => L < |q * s i - q * a|) := by
    apply Finset.filter_congr
    intro i hi
    rw [div_lt_iff₀ hq, ← mul_sub, abs_mul, abs_of_pos hq, mul_comm]
  calc
    _ ≤ ∑ i ∈ U with L / q < |s i - a|,
        q ^ 2 * (1 / (1 + |q * s i - q * a|) ^ 2) := by
      apply Finset.sum_le_sum
      intro i hi
      simpa only [← mul_sub] using
        inverseSquareDistance_le_scaled (one_le_positiveSeparationScale d) (s i - a)
    _ = q ^ 2 * ∑ i ∈ U with L < |q * s i - q * a|,
        1 / (1 + |q * s i - q * a|) ^ 2 := by rw [hfilter, Finset.mul_sum]
    _ ≤ q ^ 2 * (ε / q ^ 2) :=
      mul_le_mul_of_nonneg_left (htail (q * a) U) (sq_nonneg q)
    _ = ε := by field_simp

/-- Finite rows of the universal Gram kernel are uniformly bounded on any
positively separated family. -/
theorem sum_norm_universalGramKernel_le_of_posSeparated
    {ι : Type*} [DecidableEq ι] {m : ℕ} (hm : 1 ≤ m)
    (s : ι → ℝ) {d : ℝ} (hd : 0 < d)
    (hsep : ∀ i j, i ≠ j → d ≤ |s i - s j|) (a : ℝ) (U : Finset ι) :
    ∑ i ∈ U, ‖universalGramKernel m (s i - a)‖ ≤
      universalGramDecayConstant m * positiveSeparationSchurConstant d := by
  calc
    _ ≤ ∑ i ∈ U, universalGramDecayConstant m * (1 / (1 + |s i - a|) ^ 2) := by
      apply Finset.sum_le_sum
      intro i hi
      simpa only [mul_one_div] using norm_universalGramKernel_le_inv_sq hm (s i - a)
    _ = universalGramDecayConstant m * ∑ i ∈ U, 1 / (1 + |s i - a|) ^ 2 := by
      rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (sum_inverseSquareDistance_le_of_posSeparated s hd hsep a U)
      (universalGramDecayConstant_nonneg hm)

/-- Bessel analysis for the actual universal-kernel atoms with any positive
separation.  Boundedness follows from proved Gram row estimates. -/
def positiveSeparatedUniversalGramBesselAnalysis
    {ι : Type*} [DecidableEq ι] {m : ℕ} (hm : 1 ≤ m)
    (s : ι → ℝ) {d : ℝ} (hd : 0 < d)
    (hsep : ∀ i j, i ≠ j → d ≤ |s i - s j|) :
    BesselAnalysis (fun i => universalGramAtom m hm (s i)) :=
  BesselAnalysis.of_finsupp_gram_row_bound _
    (Real.sqrt (universalGramDecayConstant m * positiveSeparationSchurConstant d))
    (Real.sqrt_nonneg _) (by
        intro U i hi
        rw [Real.sq_sqrt (mul_nonneg (universalGramDecayConstant_nonneg hm)
          (positiveSeparationSchurConstant_nonneg d))]
        simp_rw [inner_universalGramAtom]
        exact sum_norm_universalGramKernel_le_of_posSeparated hm s hd hsep (s i) U)

/-- The bounded universal Gram on a positively separated family. -/
def positiveSeparatedUniversalGramOperator
    {ι : Type*} [DecidableEq ι] {m : ℕ} (hm : 1 ≤ m)
    (s : ι → ℝ) {d : ℝ} (hd : 0 < d)
    (hsep : ∀ i j, i ≠ j → d ≤ |s i - s j|) :
    CoefficientSpace ι →L[ℂ] CoefficientSpace ι :=
  coefficientGram (positiveSeparatedUniversalGramBesselAnalysis hm s hd hsep).synthesis

theorem positiveSeparatedUniversalGramOperator_entry
    {ι : Type*} [DecidableEq ι] {m : ℕ} (hm : 1 ≤ m)
    (s : ι → ℝ) {d : ℝ} (hd : 0 < d)
    (hsep : ∀ i j, i ≠ j → d ≤ |s i - s j|) (i j : ι) :
    inner ℂ (coefficientAtom i)
      (positiveSeparatedUniversalGramOperator hm s hd hsep (coefficientAtom j)) =
      universalGramKernel m (s j - s i) := by
  rw [positiveSeparatedUniversalGramOperator, coefficientGram,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    BesselAnalysis.synthesis_coefficientAtom, BesselAnalysis.synthesis_coefficientAtom,
    inner_universalGramAtom]

/-- On the legacy strict-gap domain the new positive-separation synthesis
is the same continuous operator, not a competing realization. -/
theorem positiveSeparatedUniversalGramSynthesis_eq_legacy
    {ι : Type*} [DecidableEq ι] {m : ℕ} (hm : 1 ≤ m)
    (s : ι → ℝ) {d : ℝ} (hd : 1 < d)
    (hsep : ∀ i j, i ≠ j → d ≤ |s i - s j|) :
    (positiveSeparatedUniversalGramBesselAnalysis hm s (zero_lt_one.trans hd) hsep).synthesis =
      universalGramSynthesis hm hd s hsep := by
  apply ContinuousLinearMap.ext_on
  · rw [Submodule.dense_iff_topologicalClosure_eq_top]
    exact coefficientAtom_dense_span
  · rintro _ ⟨i, rfl⟩
    rw [universalGramSynthesis, BesselAnalysis.synthesis_coefficientAtom,
      BesselAnalysis.synthesis_coefficientAtom]

/-- The extension to all positive separations preserves the existing
universal Gram operator on its original strict-gap domain. -/
theorem positiveSeparatedUniversalGramOperator_eq_legacy
    {ι : Type*} [DecidableEq ι] {m : ℕ} (hm : 1 ≤ m)
    (s : ι → ℝ) {d : ℝ} (hd : 1 < d)
    (hsep : ∀ i j, i ≠ j → d ≤ |s i - s j|) :
    positiveSeparatedUniversalGramOperator hm s (zero_lt_one.trans hd) hsep =
      universalGramOperator hm hd s hsep := by
  unfold positiveSeparatedUniversalGramOperator universalGramOperator
  rw [positiveSeparatedUniversalGramSynthesis_eq_legacy hm s hd hsep]

end

end MeyerGeneralProblem
