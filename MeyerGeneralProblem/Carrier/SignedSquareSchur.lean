module

public import MeyerGeneralProblem.Carrier.SignedSquare
public import Mathlib.Algebra.Order.Floor.Ring
import all Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Analysis.Normed.Group.FunctionSeries
import all Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import all Mathlib.Topology.Algebra.InfiniteSum.NatInt

@[expose] public section

/-!
# Signed-square Schur summation

This module isolates the discrete summation step used by the same-side Gram
estimate.  A finite exceptional set and separation in signed-square
coordinates turn any exponential off-diagonal kernel bound into absolutely
summable carrier rows.  The analytic Mehler estimate and its normalization are
kept in the Hermite modules.
-/

namespace MeyerGeneralProblem

noncomputable section

/-- The two-sided integer exponential is summable at every positive rate. -/
theorem summable_int_exp_neg_mul_abs {c : ℝ} (hc : 0 < c) :
    Summable (fun k : ℤ ↦ Real.exp (-c * |(k : ℝ)|)) := by
  apply Summable.of_add_one_of_neg_add_one
  · have hq : Summable (fun n : ℕ ↦ (Real.exp (-c)) ^ (n + 1)) :=
      (summable_geometric_of_lt_one (Real.exp_pos _).le
        (by rw [Real.exp_lt_one_iff]; linarith)).comp_injective
          (fun _ _ h ↦ Nat.add_right_cancel h)
    convert hq using 1
    ext n
    rw [abs_of_nonneg (by positivity)]
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  · have hq : Summable (fun n : ℕ ↦ (Real.exp (-c)) ^ (n + 1)) :=
      (summable_geometric_of_lt_one (Real.exp_pos _).le
        (by rw [Real.exp_lt_one_iff]; linarith)).comp_injective
          (fun _ _ h ↦ Nat.add_right_cancel h)
    convert hq using 1
    ext n
    rw [abs_of_nonpos (by
      exact_mod_cast (show -((n : ℤ) + 1) ≤ 0 by omega))]
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring

/-- Rounding a real center to its integer shell loses at most the factor
`exp c` in an exponential-distance majorant. -/
theorem exp_neg_mul_abs_le_floorMajorant
    {c : ℝ} (hc : 0 < c) (x : ℝ) :
    Real.exp (-c * |x|) ≤
      Real.exp c * Real.exp (-c * |((⌊x⌋ : ℤ) : ℝ)|) := by
  have hfloorAbs : |((⌊x⌋ : ℤ) : ℝ)| ≤ |x| + 1 := by
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
  have hexponent :
      -c * |x| ≤ c + (-c * |((⌊x⌋ : ℤ) : ℝ)|) := by
    nlinarith
  calc
    Real.exp (-c * |x|) ≤
        Real.exp (c + (-c * |((⌊x⌋ : ℤ) : ℝ)|)) :=
      Real.exp_le_exp.mpr hexponent
    _ = Real.exp c * Real.exp (-c * |((⌊x⌋ : ℤ) : ℝ)|) := by
      rw [Real.exp_add]

/-- Exponential distance from any center is summable on a family that is
uniformly separated outside a finite exceptional set. -/
theorem summable_exp_neg_abs_sub_of_finite_separated
    {ι : Type*} [DecidableEq ι] (s : ι → ℝ) (F : Finset ι)
    {d c : ℝ} (hd : 1 < d) (hc : 0 < c)
    (hsep : ∀ i j, i ∉ F → j ∉ F → i ≠ j → d ≤ |s i - s j|)
    (a : ℝ) :
    Summable (fun i : ι ↦ Real.exp (-c * |s i - a|)) := by
  let tail := {i : ι // i ∉ F}
  let shell : tail → ℤ := fun i ↦ ⌊s i - a⌋
  have hshell : Function.Injective shell := by
    intro i j hij
    apply Subtype.ext
    by_contra hne
    have hfar := hsep i j i.property j.property hne
    have hnearRaw : |(s i - a) - (s j - a)| < 1 :=
      Int.abs_sub_lt_one_of_floor_eq_floor hij
    have hnear : |s i - s j| < 1 := by
      simpa only [sub_sub_sub_cancel_right] using hnearRaw
    linarith
  have hmajorant : Summable (fun k : ℤ ↦
      Real.exp c * Real.exp (-c * |(k : ℝ)|)) :=
    (summable_int_exp_neg_mul_abs hc).mul_left (Real.exp c)
  have htailMajorant : Summable (fun i : tail ↦
      Real.exp c * Real.exp (-c * |(shell i : ℝ)|)) :=
    hmajorant.comp_injective hshell
  have htail : Summable (fun i : tail ↦
      Real.exp (-c * |s i - a|)) := by
    refine Summable.of_nonneg_of_le (fun _ ↦ (Real.exp_pos _).le) ?_
      htailMajorant
    intro i
    exact exp_neg_mul_abs_le_floorMajorant hc (s i - a)
  have htailIndicator : Summable
      ({i : ι | i ∉ F}.indicator (fun i ↦ Real.exp (-c * |s i - a|))) := by
    exact summable_subtype_iff_indicator.mp htail
  have hfiniteIndicator : Summable
      ((F : Set ι).indicator (fun i ↦ Real.exp (-c * |s i - a|))) := by
    apply summable_of_ne_finset_zero (s := F)
    intro i hi
    simp [Set.indicator_of_notMem, hi]
  apply (hfiniteIndicator.add htailIndicator).congr
  intro i
  by_cases hi : i ∈ F <;> simp [hi]

/-- Uniform quantitative version of
`summable_exp_neg_abs_sub_of_finite_separated`.  The bound is independent of
the center `a`. -/
theorem tsum_exp_neg_abs_sub_le_of_finite_separated
    {ι : Type*} [DecidableEq ι] (s : ι → ℝ) (F : Finset ι)
    {d c : ℝ} (hd : 1 < d) (hc : 0 < c)
    (hsep : ∀ i j, i ∉ F → j ∉ F → i ≠ j → d ≤ |s i - s j|)
    (a : ℝ) :
    ∑' i : ι, Real.exp (-c * |s i - a|) ≤
      (F.card : ℝ) +
        ∑' k : ℤ, Real.exp c * Real.exp (-c * |(k : ℝ)|) := by
  let tail := {i : ι // i ∉ F}
  let shell : tail → ℤ := fun i ↦ ⌊s i - a⌋
  have hshell : Function.Injective shell := by
    intro i j hij
    apply Subtype.ext
    by_contra hne
    have hfar := hsep i j i.property j.property hne
    have hnearRaw : |(s i - a) - (s j - a)| < 1 :=
      Int.abs_sub_lt_one_of_floor_eq_floor hij
    have hnear : |s i - s j| < 1 := by
      simpa only [sub_sub_sub_cancel_right] using hnearRaw
    linarith
  have hsum : Summable (fun i : ι ↦
      Real.exp (-c * |s i - a|)) :=
    summable_exp_neg_abs_sub_of_finite_separated
      s F hd hc hsep a
  have hmajorant : Summable (fun k : ℤ ↦
      Real.exp c * Real.exp (-c * |(k : ℝ)|)) :=
    (summable_int_exp_neg_mul_abs hc).mul_left (Real.exp c)
  have htail : Summable (fun i : tail ↦
      Real.exp (-c * |s i - a|)) := hsum.subtype _
  have htailBound :
      ∑' i : tail, Real.exp (-c * |s i - a|) ≤
        ∑' k : ℤ, Real.exp c * Real.exp (-c * |(k : ℝ)|) := by
    exact htail.tsum_le_tsum_of_inj shell hshell
      (fun _ _ ↦ (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le))
      (fun i ↦ exp_neg_mul_abs_le_floorMajorant hc (s i - a))
      hmajorant
  have hfiniteBound :
      ∑ i ∈ F, Real.exp (-c * |s i - a|) ≤ (F.card : ℝ) := by
    calc
      ∑ i ∈ F, Real.exp (-c * |s i - a|) ≤ ∑ _i ∈ F, (1 : ℝ) := by
        gcongr with i hi
        rw [Real.exp_le_one_iff]
        exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc.le) (abs_nonneg _)
      _ = (F.card : ℝ) := by simp
  rw [← hsum.sum_add_tsum_subtype_compl F]
  exact add_le_add hfiniteBound htailBound

/-- On a family separated by more than one, the finite sum of exponential
distance terms beyond a sufficiently large radius is uniformly small in the
center and in the finite set being summed. -/
theorem exists_uniform_sum_exp_neg_abs_tail_of_separated
    {ι : Type*} [DecidableEq ι] (s : ι → ℝ)
    {d c : ℝ} (hd : 1 < d) (hc : 0 < c)
    (hsep : ∀ i j, i ≠ j → d ≤ |s i - s j|) :
    ∀ ε > 0, ∃ L ≥ 0, ∀ a : ℝ, ∀ U : Finset ι,
      ∑ i ∈ U with L < |s i - a|,
        Real.exp (-c * |s i - a|) ≤ ε := by
  intro ε hε
  let majorant : ℤ → ℝ := fun k =>
    Real.exp c * Real.exp (-c * |(k : ℝ)|)
  have hmajorant : Summable majorant := by
    dsimp only [majorant]
    exact (summable_int_exp_neg_mul_abs hc).mul_left (Real.exp c)
  have hsmallEventually :=
    (tendsto_order.1 (tendsto_tsum_compl_atTop_zero majorant)).2
      ε hε
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
    have hdist : |s i - a| ≤ |((⌊s i - a⌋ : ℤ) : ℝ)| + 1 := by
      by_cases hx : 0 ≤ s i - a
      · have hk0 : (0 : ℤ) ≤ ⌊s i - a⌋ := Int.floor_nonneg.mpr hx
        rw [abs_of_nonneg hx, abs_of_nonneg (by exact_mod_cast hk0)]
        have hlt := Int.lt_floor_add_one (s i - a)
        linarith
      · have hx' : s i - a < 0 := lt_of_not_ge hx
        have hk0 : (((⌊s i - a⌋ : ℤ) : ℝ)) ≤ 0 :=
          (Int.floor_le (s i - a)).trans hx'.le
        rw [abs_of_nonpos hx'.le, abs_of_nonpos hk0]
        have hfloor := Int.floor_le (s i - a)
        linarith
    have hiFar : L < |s i - a| := by
      have hi' := hi
      dsimp only [Ufar] at hi'
      exact (Finset.mem_filter.mp hi').2
    dsimp only [L, shell] at hkBound hiFar
    linarith
  have himage :
      ∑ k ∈ Ufar.image shell, majorant k =
        ∑ i ∈ Ufar, majorant (shell i) :=
    Finset.sum_image hshell.injOn
  have hindicator : Summable
      (({k : ℤ | k ∉ K}).indicator majorant) :=
    hmajorant.indicator _
  calc
    (∑ i ∈ U with L < |s i - a|,
        Real.exp (-c * |s i - a|)) =
        ∑ i ∈ Ufar, Real.exp (-c * |s i - a|) := by rfl
    _ ≤ ∑ i ∈ Ufar, majorant (shell i) := by
      apply Finset.sum_le_sum
      intro i hi
      exact exp_neg_mul_abs_le_floorMajorant hc (s i - a)
    _ = ∑ k ∈ Ufar.image shell, majorant k := himage.symm
    _ = ∑ k ∈ Ufar.image shell,
        ({k : ℤ | k ∉ K}).indicator majorant k := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_image] at hk
      obtain ⟨i, hi, rfl⟩ := hk
      simp [hnotK hi]
    _ ≤ ∑' k : ℤ, ({k : ℤ | k ∉ K}).indicator majorant k :=
      hindicator.sum_le_tsum _ (fun k _ => by
        by_cases hk : k ∈ K <;> simp [hk, majorant]
        positivity)
    _ = ∑' k : {k : ℤ // k ∈ {q : ℤ | q ∉ K}}, majorant k := by
      rw [← tsum_subtype]
    _ ≤ ε := by
      have hsmall := hK K (by rfl)
      have hsmall' :
          (∑' k : {k : ℤ // k ∈ {q : ℤ | q ∉ K}}, majorant k) < ε := by
        simpa using hsmall
      exact hsmall'.le

/-- Strict-subcritical carrier geometry makes every signed-square Gaussian
row absolutely summable. -/
theorem TwoSidedCarrier.StrictSubcritical.summable_signedSquareGaussian
    {Λ : TwoSidedCarrier} (hΛ : Λ.StrictSubcritical)
    {c : ℝ} (hc : 0 < c) (i : ℤ) :
    Summable (fun j : ℤ ↦
      Real.exp
        (-c * |signedSquare (Λ j) - signedSquare (Λ i)|)) := by
  rcases strictSubcritical_signedSquare_separated hΛ with
    ⟨d, hd, F, hsep⟩
  exact summable_exp_neg_abs_sub_of_finite_separated
    (fun j : ℤ ↦ signedSquare (Λ j)) F hd hc hsep
      (signedSquare (Λ i))

/-- The signed-square Gaussian rows of a strict-subcritical carrier have one
uniform `tsum` ceiling. -/
theorem TwoSidedCarrier.StrictSubcritical.exists_uniform_signedSquareGaussianRowBound
    {Λ : TwoSidedCarrier} (hΛ : Λ.StrictSubcritical)
    {c : ℝ} (hc : 0 < c) :
    ∃ B ≥ 0, ∀ i : ℤ,
      ∑' j : ℤ,
        Real.exp
          (-c * |signedSquare (Λ j) - signedSquare (Λ i)|) ≤ B := by
  rcases strictSubcritical_signedSquare_separated hΛ with
    ⟨d, hd, F, hsep⟩
  let B : ℝ := (F.card : ℝ) +
    ∑' k : ℤ, Real.exp c * Real.exp (-c * |(k : ℝ)|)
  have hB : 0 ≤ B := by
    dsimp [B]
    exact add_nonneg (Nat.cast_nonneg _)
      (tsum_nonneg fun _ ↦
        mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
  refine ⟨B, hB, ?_⟩
  intro i
  exact tsum_exp_neg_abs_sub_le_of_finite_separated
    (fun j : ℤ ↦ signedSquare (Λ j)) F hd hc hsep
      (signedSquare (Λ i))

/-- Any nonnegative kernel dominated by a signed-square Gaussian on a
strict-subcritical carrier has summable rows with one uniform ceiling. -/
theorem TwoSidedCarrier.StrictSubcritical.exists_uniform_kernelRowBound_of_signedSquareGaussian
    {Λ : TwoSidedCarrier} (hΛ : Λ.StrictSubcritical)
    (K : ℤ → ℤ → ℝ) {A c : ℝ}
    (hA : 0 ≤ A) (hc : 0 < c)
    (hK : ∀ i j,
      0 ≤ K i j ∧
        K i j ≤ A * Real.exp
          (-c * |signedSquare (Λ j) - signedSquare (Λ i)|)) :
    ∃ R ≥ 0,
      (∀ i : ℤ, Summable (K i)) ∧
      ∀ i : ℤ, ∑' j : ℤ, K i j ≤ R := by
  rcases hΛ.exists_uniform_signedSquareGaussianRowBound hc with
    ⟨B, hB, hBrow⟩
  refine ⟨A * B, mul_nonneg hA hB, ?_, ?_⟩
  · intro i
    have hgauss := hΛ.summable_signedSquareGaussian hc i
    have hmajorant := hgauss.mul_left A
    exact Summable.of_nonneg_of_le (fun j ↦ (hK i j).1)
      (fun j ↦ (hK i j).2) hmajorant
  · intro i
    have hgauss := hΛ.summable_signedSquareGaussian hc i
    have hrow : Summable (K i) :=
      Summable.of_nonneg_of_le (fun j ↦ (hK i j).1)
        (fun j ↦ (hK i j).2) (hgauss.mul_left A)
    calc
      ∑' j : ℤ, K i j ≤
          ∑' j : ℤ, A * Real.exp
            (-c * |signedSquare (Λ j) - signedSquare (Λ i)|) :=
        hrow.tsum_le_tsum (fun j ↦ (hK i j).2) (hgauss.mul_left A)
      _ = A * ∑' j : ℤ,
          Real.exp
            (-c * |signedSquare (Λ j) - signedSquare (Λ i)|) :=
        tsum_mul_left
      _ ≤ A * B := mul_le_mul_of_nonneg_left (hBrow i) hA

end

end MeyerGeneralProblem
