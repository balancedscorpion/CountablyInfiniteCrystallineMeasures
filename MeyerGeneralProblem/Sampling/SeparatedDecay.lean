module

public import MeyerGeneralProblem.Sampling.UpperLargeSieve
public import MeyerGeneralProblem.Sampling.CosineIngham
public import Mathlib.Algebra.Order.Floor.Ring
import all Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Analysis.Normed.Group.FunctionSeries
import all Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.PSeries
import all Mathlib.Analysis.PSeries

@[expose] public section

/-!
# Summable decay on separated frequencies

Floor shells inject a family separated by more than one into the integers.
This turns the summable inverse-square integer envelope into both summable
rows and a finite-sum tail estimate uniform in the row center.
-/

namespace MeyerGeneralProblem

noncomputable section

/-- Negative real powers are summable on a separated family that stays
outside the central unit interval.  Rounding toward zero is injective under
separation by more than one and does not increase absolute value, so the
claim reduces directly to the two-sided integer `p`-series. -/
theorem summable_abs_rpow_of_separated_away
    {ι : Type*} [DecidableEq ι] (s : ι → ℝ)
    {d b : ℝ} (hd : 1 < d) (hb : 1 < b)
    (hsep : ∀ i j, i ≠ j → d ≤ |s i - s j|)
    (hlarge : ∀ i, 1 ≤ |s i|) :
    Summable (fun i : ι ↦ |s i| ^ (-b)) := by
  let shell : ι → ℤ := fun i ↦ towardZeroFloor (s i)
  have hshell : Function.Injective shell := by
    intro i j hij
    by_contra hne
    have hfar := hsep i j hne
    have hnear := abs_sub_lt_one_of_towardZeroFloor_eq
      (hlarge i) (hlarge j) hij
    linarith
  have hmajorant : Summable (fun k : ℤ ↦ |(k : ℝ)| ^ (-b)) :=
    Real.summable_abs_int_rpow hb
  have hshellMajorant :
      Summable (fun i : ι ↦ |((shell i : ℤ) : ℝ)| ^ (-b)) :=
    hmajorant.comp_injective hshell
  refine Summable.of_nonneg_of_le
    (fun i ↦ Real.rpow_nonneg (abs_nonneg (s i)) _) ?_
    hshellMajorant
  intro i
  apply Real.rpow_le_rpow_of_nonpos
  · have hne : shell i ≠ 0 := towardZeroFloor_ne_zero (hlarge i)
    exact abs_pos.mpr (by exact_mod_cast hne)
  · exact abs_towardZeroFloor_cast_le_abs (s i)
  · linarith

/-- A real number lies at absolute distance at most one beyond the absolute
value of its floor. -/
theorem abs_le_abs_floor_add_one (x : ℝ) :
    |x| ≤ |((⌊x⌋ : ℤ) : ℝ)| + 1 := by
  by_cases hx : 0 ≤ x
  · have hk : (0 : ℤ) ≤ ⌊x⌋ := Int.floor_nonneg.mpr hx
    rw [abs_of_nonneg hx, abs_of_nonneg (by exact_mod_cast hk)]
    have hlt := Int.lt_floor_add_one x
    linarith
  · have hx' : x < 0 := lt_of_not_ge hx
    have hk : (((⌊x⌋ : ℤ) : ℝ)) ≤ 0 :=
      (Int.floor_le x).trans hx'.le
    rw [abs_of_nonpos hx'.le, abs_of_nonpos hk]
    have hfloor := Int.floor_le x
    linarith

/-- Taking the floor increases absolute value by at most one. -/
theorem abs_floor_le_abs_add_one (x : ℝ) :
    |((⌊x⌋ : ℤ) : ℝ)| ≤ |x| + 1 := by
  by_cases hx : 0 ≤ x
  · have hk : (0 : ℤ) ≤ ⌊x⌋ := Int.floor_nonneg.mpr hx
    rw [abs_of_nonneg hx, abs_of_nonneg (by exact_mod_cast hk)]
    exact (Int.floor_le x).trans (le_add_of_nonneg_right zero_le_one)
  · have hx' : x < 0 := lt_of_not_ge hx
    have hk : (((⌊x⌋ : ℤ) : ℝ)) ≤ 0 :=
      (Int.floor_le x).trans hx'.le
    rw [abs_of_nonpos hx'.le, abs_of_nonpos hk]
    have hlt := Int.lt_floor_add_one x
    linarith

/-- The continuous inverse-square distance envelope is controlled by four
times its integer floor-shell envelope. -/
theorem inverseSquareDistance_le_floorMajorant (x : ℝ) :
    1 / (1 + |x|) ^ 2 ≤
      4 * integerUnitSlabEnvelope ⌊x⌋ := by
  have hq : 0 < 1 + |x| := by positivity
  have hr : 0 < 1 + |(((⌊x⌋ : ℤ) : ℝ))| := by positivity
  have hlin : 1 + |(((⌊x⌋ : ℤ) : ℝ))| ≤ 2 * (1 + |x|) := by
    nlinarith [abs_floor_le_abs_add_one x, abs_nonneg x]
  unfold integerUnitSlabEnvelope
  rw [show 4 * (1 / (1 + |(((⌊x⌋ : ℤ) : ℝ))|) ^ 2) =
    4 / (1 + |(((⌊x⌋ : ℤ) : ℝ))|) ^ 2 by ring]
  rw [div_le_div_iff₀ (sq_pos_of_pos hq) (sq_pos_of_pos hr)]
  have hprod : 0 ≤
      (2 * (1 + |x|) - (1 + |(((⌊x⌋ : ℤ) : ℝ))|)) *
        (2 * (1 + |x|) + (1 + |(((⌊x⌋ : ℤ) : ℝ))|)) :=
    mul_nonneg (sub_nonneg.mpr hlin) (by positivity)
  nlinarith

/-- Inverse-square distance from any center is summable on every family
separated by more than one. -/
theorem summable_inverseSquareDistance_of_separated
    {ι : Type*} [DecidableEq ι] (s : ι → ℝ)
    {d : ℝ} (hd : 1 < d)
    (hsep : ∀ i j, i ≠ j → d ≤ |s i - s j|)
    (a : ℝ) :
    Summable (fun i : ι => 1 / (1 + |s i - a|) ^ 2) := by
  let shell : ι → ℤ := fun i => ⌊s i - a⌋
  have hshell : Function.Injective shell := by
    intro i j hij
    by_contra hne
    have hfar := hsep i j hne
    have hnearRaw : |(s i - a) - (s j - a)| < 1 :=
      Int.abs_sub_lt_one_of_floor_eq_floor hij
    have hnear : |s i - s j| < 1 := by
      simpa only [sub_sub_sub_cancel_right] using hnearRaw
    linarith
  have hmajorant : Summable (fun k : ℤ =>
      4 * integerUnitSlabEnvelope k) :=
    summable_integerUnitSlabEnvelope.mul_left 4
  exact Summable.of_nonneg_of_le (fun _ => by positivity)
    (fun i => inverseSquareDistance_le_floorMajorant (s i - a))
    (hmajorant.comp_injective hshell)

/-- A bounded metric band in a family separated by more than one has a
uniform finite cardinality bound, independent of its center and of the finite
section. -/
theorem card_metricBand_le_integerFloorBand_of_separated
    {ι : Type*} [DecidableEq ι] (s : ι → ℝ)
    {d : ℝ} (hd : 1 < d)
    (hsep : ∀ i j, i ≠ j → d ≤ |s i - s j|)
    (L a : ℝ) (U : Finset ι) :
    (U.filter (fun i => |s i - a| ≤ L)).card ≤
      (Finset.Icc ⌊-L⌋ ⌊L⌋).card := by
  let band := U.filter (fun i => |s i - a| ≤ L)
  let shell : ι → ℤ := fun i => ⌊s i - a⌋
  have hshell : Function.Injective shell := by
    intro i j hij
    by_contra hne
    have hfar := hsep i j hne
    have hnearRaw : |(s i - a) - (s j - a)| < 1 :=
      Int.abs_sub_lt_one_of_floor_eq_floor hij
    have hnear : |s i - s j| < 1 := by
      simpa only [sub_sub_sub_cancel_right] using hnearRaw
    linarith
  have himage : band.image shell ⊆ Finset.Icc ⌊-L⌋ ⌊L⌋ := by
    intro k hk
    rw [Finset.mem_image] at hk
    obtain ⟨i, hi, rfl⟩ := hk
    have hi' := hi
    dsimp only [band] at hi'
    have hiband := (Finset.mem_filter.mp hi').2
    rw [abs_le] at hiband
    rw [Finset.mem_Icc]
    exact ⟨Int.floor_mono hiband.1, Int.floor_mono hiband.2⟩
  calc
    (U.filter (fun i => |s i - a| ≤ L)).card = band.card := by rfl
    _ = (band.image shell).card :=
      (Finset.card_image_of_injOn hshell.injOn).symm
    _ ≤ (Finset.Icc ⌊-L⌋ ⌊L⌋).card := Finset.card_le_card himage

/-- Uniform finite-sum tail extraction for inverse-square distance on a
separated family.  The cutoff is independent of the center and of the finite
set being summed. -/
theorem exists_uniform_sum_inverseSquareDistance_tail_of_separated
    {ι : Type*} [DecidableEq ι] (s : ι → ℝ)
    {d : ℝ} (hd : 1 < d)
    (hsep : ∀ i j, i ≠ j → d ≤ |s i - s j|) :
    ∀ ε > 0, ∃ L ≥ 0, ∀ a : ℝ,
      ∀ U : Finset ι,
        ∑ i ∈ U with L < |s i - a|,
          1 / (1 + |s i - a|) ^ 2 ≤ ε := by
  intro ε hε
  have hsmallEventually :=
    (tendsto_order.1
      (tendsto_tsum_compl_atTop_zero integerUnitSlabEnvelope)).2
        (ε / 4) (by positivity)
  simp only [Filter.eventually_atTop] at hsmallEventually
  obtain ⟨K, hK⟩ := hsmallEventually
  let L : ℝ := 1 + ∑ k ∈ K, |(k : ℝ)|
  have hL : 0 ≤ L := by
    dsimp [L]
    positivity
  refine ⟨L, hL, ?_⟩
  intro a U
  let Ufar := U.filter (fun i => L < |s i - a|)
  let shell : ι → ℤ := fun i => ⌊s i - a⌋
  have hshell : Function.Injective shell := by
    intro i j hij
    by_contra hne
    have hfar := hsep i j hne
    have hnearRaw : |(s i - a) - (s j - a)| < 1 :=
      Int.abs_sub_lt_one_of_floor_eq_floor hij
    have hnear : |s i - s j| < 1 := by
      simpa only [sub_sub_sub_cancel_right] using hnearRaw
    linarith
  have hnotK {i : ι} (hi : i ∈ Ufar) : shell i ∉ K := by
    intro hk
    have hkBound : |((shell i : ℤ) : ℝ)| ≤
        ∑ k ∈ K, |(k : ℝ)| :=
      Finset.single_le_sum (s := K)
        (f := fun k : ℤ => |(k : ℝ)|)
        (fun k _ => abs_nonneg (k : ℝ)) hk
    have hdist := abs_le_abs_floor_add_one (s i - a)
    have hiFar : L < |s i - a| := by
      have hi' := hi
      dsimp only [Ufar] at hi'
      exact (Finset.mem_filter.mp hi').2
    dsimp only [L, shell] at hkBound hdist hiFar
    linarith
  have himage :
      ∑ k ∈ Ufar.image shell, 4 * integerUnitSlabEnvelope k =
        ∑ i ∈ Ufar, 4 * integerUnitSlabEnvelope (shell i) :=
    Finset.sum_image hshell.injOn
  have hindicator : Summable
      (({k : ℤ | k ∉ K}).indicator
        (fun k => 4 * integerUnitSlabEnvelope k)) :=
    (summable_integerUnitSlabEnvelope.mul_left 4).indicator _
  calc
    (∑ i ∈ U with L < |s i - a|,
        1 / (1 + |s i - a|) ^ 2) =
        ∑ i ∈ Ufar, 1 / (1 + |s i - a|) ^ 2 := by rfl
    _ ≤ ∑ i ∈ Ufar, 4 * integerUnitSlabEnvelope (shell i) := by
      apply Finset.sum_le_sum
      intro i hi
      exact inverseSquareDistance_le_floorMajorant (s i - a)
    _ = ∑ k ∈ Ufar.image shell, 4 * integerUnitSlabEnvelope k :=
      himage.symm
    _ = ∑ k ∈ Ufar.image shell,
        ({k : ℤ | k ∉ K}).indicator
          (fun k => 4 * integerUnitSlabEnvelope k) k := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_image] at hk
      obtain ⟨i, hi, rfl⟩ := hk
      simp [hnotK hi]
    _ ≤ ∑' k : ℤ, ({k : ℤ | k ∉ K}).indicator
          (fun k => 4 * integerUnitSlabEnvelope k) k :=
      hindicator.sum_le_tsum _ (fun k _ => by
          by_cases hk : k ∈ K <;> simp [hk]
          unfold integerUnitSlabEnvelope
          positivity)
    _ = 4 * ∑' k : {k : ℤ // k ∈ {q : ℤ | q ∉ K}},
          integerUnitSlabEnvelope k := by
      rw [← tsum_subtype]
      rw [tsum_mul_left]
    _ ≤ ε := by
      have hsmall := hK K (by rfl)
      have hsmall' :
          (∑' k : {k : ℤ // k ∈ {q : ℤ | q ∉ K}},
            integerUnitSlabEnvelope k) < ε / 4 := by
        simpa using hsmall
      nlinarith

end

end MeyerGeneralProblem
