module

public import MeyerGeneralProblem.Sampling.CosineIngham
public import Mathlib.Analysis.PSeries
import all Mathlib.Analysis.PSeries

@[expose] public section

/-!
# Upper large sieve for separated frequencies

This module proves the upper companion to the cosine-window Ingham floor.
It first obtains a uniform bound on every translated unit interval, then
partitions the rational-density energy into integer slabs dominated by a
summable inverse-square envelope.  The resulting finite universal Gram bound
is unconditional and is the boundedness input for the infinite universal
tail Gram model.
-/

namespace MeyerGeneralProblem

open MeasureTheory ComplexConjugate

noncomputable section

/-- Upper companion to `finite_kernel_quadratic_re_ge_of_offdiag_row`. -/
theorem finite_kernel_quadratic_re_le_of_offdiag_row
    {n : ℕ} (K : Fin n → Fin n → ℂ) (c : Fin n → ℂ) (D R : ℝ)
    (hdiag : ∀ i, K i i = (D : ℂ))
    (hsymm : ∀ i j, ‖K i j‖ = ‖K j i‖)
    (hrow : ∀ i, ∑ j ∈ Finset.univ.erase i, ‖K i j‖ ≤ R) :
    (∑ i, ∑ j, conj (c i) * c j * K i j).re ≤
      (D + R) * ∑ i, ‖c i‖ ^ 2 := by
  let K' : Fin n → Fin n → ℂ := fun i j =>
    if i = j then (D : ℂ) else -K i j
  let E : ℝ := ∑ i, ‖c i‖ ^ 2
  have hdiag' (i : Fin n) : K' i i = (D : ℂ) := by
    simp [K']
  have hsymm' (i j : Fin n) : ‖K' i j‖ = ‖K' j i‖ := by
    by_cases hij : i = j
    · subst j
      rfl
    · simp only [K', ite_eq_right hij, ite_eq_right (Ne.symm hij), norm_neg]
      exact hsymm i j
  have hrow' (i : Fin n) :
      ∑ j ∈ Finset.univ.erase i, ‖K' i j‖ ≤ R := by
    convert hrow i using 1
    apply Finset.sum_congr rfl
    intro j hj
    simp [K', Ne.symm (Finset.ne_of_mem_erase hj)]
  have hlower := finite_kernel_quadratic_re_ge_of_offdiag_row
    K' c D R hdiag' hsymm' hrow'
  have hsum :
      (∑ i, ∑ j, conj (c i) * c j * K' i j) +
          (∑ i, ∑ j, conj (c i) * c j * K i j) =
        ((2 * D * E : ℝ) : ℂ) := by
    rw [← Finset.sum_add_distrib]
    calc
      ∑ i, ((∑ j, conj (c i) * c j * K' i j) +
          ∑ j, conj (c i) * c j * K i j) =
          ∑ i, ∑ j,
            (conj (c i) * c j * K' i j +
              conj (c i) * c j * K i j) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [← Finset.sum_add_distrib]
      _ = ∑ i, ((2 * D * ‖c i‖ ^ 2 : ℝ) : ℂ) := by
        apply Finset.sum_congr rfl
        intro i hi
        calc
          ∑ j, (conj (c i) * c j * K' i j +
              conj (c i) * c j * K i j) =
              conj (c i) * c i * K' i i +
                conj (c i) * c i * K i i := by
            rw [← Finset.add_sum_erase Finset.univ
              (fun j => conj (c i) * c j * K' i j +
                conj (c i) * c j * K i j) (Finset.mem_univ i)]
            have hoff : ∑ j ∈ Finset.univ.erase i,
                (conj (c i) * c j * K' i j +
                  conj (c i) * c j * K i j) = 0 := by
              apply Finset.sum_eq_zero
              intro j hj
              rw [show K' i j = -K i j by
                simp [K', Ne.symm (Finset.ne_of_mem_erase hj)]]
              ring
            rw [hoff, add_zero]
          _ = ((2 * D * ‖c i‖ ^ 2 : ℝ) : ℂ) := by
            rw [hdiag', hdiag,
              ← Complex.normSq_eq_conj_mul_self,
              Complex.normSq_eq_norm_sq]
            push_cast
            ring
      _ = ((2 * D * E : ℝ) : ℂ) := by
        dsimp only [E]
        push_cast
        rw [Finset.mul_sum]
  have hsumRe := congrArg Complex.re hsum
  simp only [Complex.add_re, Complex.ofReal_re] at hsumRe
  dsimp only [E] at hlower hsumRe ⊢
  linarith

/-- The cosine-weighted energy on `[-1,1]` has an explicit finite upper
large-sieve bound for frequencies separated by `d > 1`. -/
theorem integral_cosineWeight_one_mul_norm_sq_le
    {d : ℝ} (hd : 1 < d) {n : ℕ} (x : Fin n → ℝ)
    (hsep : PairwiseFrequencySeparated x d) (c : Fin n → ℂ) :
    (∫ η : ℝ in Set.Icc (-1 : ℝ) 1,
        cosineInghamWeight 1 η *
          ‖gramFourierPolynomial x c η‖ ^ 2) ≤
      (4 / Real.pi) * (1 + (2 * d)⁻¹ ^ 2) *
        ∑ i, ‖c i‖ ^ 2 := by
  let q : ℝ := 2 * d
  let D : ℝ := 4 / Real.pi
  let R : ℝ := D * q⁻¹ ^ 2
  let K : Fin n → Fin n → ℂ := fun i j =>
    cosineWindowKernel 1 (x j - x i)
  have hq : 1 < q := by
    dsimp only [q]
    linarith
  have hscaled (i j : Fin n) (hij : i ≠ j) :
      q ≤ |2 * (x j - x i)| := by
    calc
      q = 2 * d := rfl
      _ ≤ 2 * |x j - x i| := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        simpa only [abs_sub_comm] using hsep i j hij
      _ = |2 * (x j - x i)| := by norm_num
  have hdiag (i : Fin n) : K i i = (D : ℂ) := by
    dsimp only [K, D]
    rw [sub_self, cosineWindowKernel_zero (by norm_num : (0 : ℝ) < 1)]
    norm_num
  have hsymm (i j : Fin n) : ‖K i j‖ = ‖K j i‖ := by
    by_cases hij : i = j
    · subst j
      rfl
    · have hfar : 1 < |2 * (x j - x i)| :=
        hq.trans_le (hscaled i j hij)
      dsimp only [K]
      rw [show x i - x j = -(x j - x i) by ring,
        cosineWindowKernel_neg_of_far (by norm_num) (by simpa using hfar)]
  have hrow (i : Fin n) :
      ∑ j ∈ Finset.univ.erase i, ‖K i j‖ ≤ R := by
    dsimp only [K, R, D, q]
    have hh := sum_norm_cosineWindowKernel_offdiag_le Finset.univ x
      (by norm_num : (0 : ℝ) < 1) hq
      (fun i hi j hj hij => by
        simpa only [mul_one] using hscaled i j hij)
      i (Finset.mem_univ i)
    dsimp only [q] at hh
    norm_num at hh ⊢
    exact hh
  have hupper := finite_kernel_quadratic_re_le_of_offdiag_row
    K c D R hdiag hsymm hrow
  rw [integral_cosineWeight_mul_norm_sq_eq_kernel_re]
  calc
    (∑ i, ∑ j, conj (c i) * c j *
        cosineWindowKernel 1 (x j - x i)).re ≤
        (D + R) * ∑ i, ‖c i‖ ^ 2 := by
      simpa only [K] using hupper
    _ = (4 / Real.pi) * (1 + (2 * d)⁻¹ ^ 2) *
        ∑ i, ‖c i‖ ^ 2 := by
      dsimp only [D, R, q]
      ring

/-- On the central half of `[-1,1]`, the unit cosine taper is bounded below
by its endpoint value `cos (π/4)`. -/
theorem cos_pi_div_four_le_cosineInghamWeight_one
    {η : ℝ} (hη : η ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) :
    Real.cos (Real.pi / 4) ≤ cosineInghamWeight 1 η := by
  have hηabs : |η| ≤ (1 / 2 : ℝ) := by
    rw [abs_le]
    exact hη
  have harg : |Real.pi * η / (2 * (1 : ℝ))| ≤ Real.pi / 4 := by
    rw [abs_div, abs_mul, abs_of_pos Real.pi_pos]
    norm_num
    have hmul := mul_le_mul_of_nonneg_left hηabs Real.pi_pos.le
    nlinarith
  unfold cosineInghamWeight
  have hπ : Real.pi / 4 ≤ Real.pi := by nlinarith [Real.pi_pos]
  have hcos := Real.cos_le_cos_of_nonneg_of_le_pi
    (abs_nonneg (Real.pi * η / (2 * (1 : ℝ)))) hπ harg
  simpa only [Real.cos_abs] using hcos

/-- Explicit upper large-sieve constant for a centered interval of length
one. -/
def unitIntervalLargeSieveConstant (d : ℝ) : ℝ :=
  (Real.cos (Real.pi / 4))⁻¹ *
    ((4 / Real.pi) * (1 + (2 * d)⁻¹ ^ 2))

theorem unitIntervalLargeSieveConstant_pos (d : ℝ) :
    0 < unitIntervalLargeSieveConstant d := by
  unfold unitIntervalLargeSieveConstant
  rw [Real.cos_pi_div_four]
  positivity

/-- Frequencies separated by `d > 1` satisfy a uniform upper large-sieve
bound on the centered unit interval. -/
theorem integral_norm_sq_le_unitIntervalLargeSieveConstant
    {d : ℝ} (hd : 1 < d) {n : ℕ} (x : Fin n → ℝ)
    (hsep : PairwiseFrequencySeparated x d) (c : Fin n → ℂ) :
    (∫ η : ℝ in Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ),
        ‖gramFourierPolynomial x c η‖ ^ 2) ≤
      unitIntervalLargeSieveConstant d * ∑ i, ‖c i‖ ^ 2 := by
  let energy : ℝ → ℝ := fun η => ‖gramFourierPolynomial x c η‖ ^ 2
  let weighted : ℝ → ℝ := fun η =>
    cosineInghamWeight 1 η * energy η
  let w₀ : ℝ := Real.cos (Real.pi / 4)
  let U : ℝ := (4 / Real.pi) * (1 + (2 * d)⁻¹ ^ 2)
  have hw₀ : 0 < w₀ := by
    dsimp only [w₀]
    rw [Real.cos_pi_div_four]
    positivity
  have henergy : Continuous energy := by
    dsimp only [energy]
    exact (continuous_gramFourierPolynomial x c).norm.pow 2
  have hweighted : Continuous weighted := by
    dsimp only [weighted]
    exact (by
      unfold cosineInghamWeight
      fun_prop : Continuous (cosineInghamWeight 1)).mul henergy
  have hsmall :
      w₀ * (∫ η : ℝ in Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ),
          energy η) ≤
        ∫ η : ℝ in Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ),
          weighted η := by
    rw [← integral_const_mul]
    apply integral_mono_ae
      (ContinuousOn.integrableOn_compact isCompact_Icc
        (henergy.const_mul w₀).continuousOn)
      (ContinuousOn.integrableOn_compact isCompact_Icc
        hweighted.continuousOn)
    filter_upwards [ae_restrict_mem measurableSet_Icc] with η hη
    dsimp only [weighted]
    exact mul_le_mul_of_nonneg_right
      (cos_pi_div_four_le_cosineInghamWeight_one hη)
      (sq_nonneg _)
  have hsets : Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ) ⊆
      Set.Icc (-1 : ℝ) 1 := by
    intro η hη
    constructor <;> linarith [hη.1, hη.2]
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Icc (-1 : ℝ) 1)] weighted := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with η hη
    dsimp only [weighted]
    exact mul_nonneg
      (cosineInghamWeight_nonneg_on_Icc (by norm_num) hη)
      (sq_nonneg _)
  have hmono :
      (∫ η : ℝ in Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ), weighted η) ≤
        ∫ η : ℝ in Set.Icc (-1 : ℝ) 1, weighted η := by
    apply setIntegral_mono_set
      (ContinuousOn.integrableOn_compact isCompact_Icc
        hweighted.continuousOn)
      hnonneg
    exact ae_of_all _ hsets
  have hbig :
      (∫ η : ℝ in Set.Icc (-1 : ℝ) 1, weighted η) ≤
        U * ∑ i, ‖c i‖ ^ 2 := by
    dsimp only [weighted, energy, U]
    exact integral_cosineWeight_one_mul_norm_sq_le hd x hsep c
  have hcombined :
      w₀ * (∫ η : ℝ in Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ),
        energy η) ≤ U * ∑ i, ‖c i‖ ^ 2 :=
    hsmall.trans (hmono.trans hbig)
  change (∫ η : ℝ in Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ),
      energy η) ≤ _
  calc
    (∫ η : ℝ in Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ), energy η) ≤
        (U * ∑ i, ‖c i‖ ^ 2) / w₀ := by
      rw [le_div_iff₀ hw₀]
      simpa only [mul_comm] using hcombined
    _ = unitIntervalLargeSieveConstant d * ∑ i, ‖c i‖ ^ 2 := by
      dsimp only [unitIntervalLargeSieveConstant, U, w₀]
      rw [div_eq_mul_inv]
      ring

/-- The Fourier phase factors translations in its frequency variable. -/
@[simp]
theorem gramPhase_add_right (t η r : ℝ) :
    gramPhase t (η + r) = gramPhase t η * gramPhase t r := by
  simp only [gramPhase, ← Complex.exp_add]
  apply congrArg Complex.exp
  push_cast
  ring

/-- The unit-interval upper large-sieve estimate is translation invariant. -/
theorem integral_norm_sq_le_shiftedUnitIntervalLargeSieveConstant
    {d : ℝ} (hd : 1 < d) {n : ℕ} (x : Fin n → ℝ)
    (hsep : PairwiseFrequencySeparated x d) (c : Fin n → ℂ) (r : ℝ) :
    (∫ η : ℝ in Set.Icc (r - 1 / 2) (r + 1 / 2),
        ‖gramFourierPolynomial x c η‖ ^ 2) ≤
      unitIntervalLargeSieveConstant d * ∑ i, ‖c i‖ ^ 2 := by
  let c' : Fin n → ℂ := fun i => c i * gramPhase (x i) r
  have hpoly (η : ℝ) :
      gramFourierPolynomial x c' η =
        gramFourierPolynomial x c (η + r) := by
    unfold gramFourierPolynomial
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only [c']
    rw [gramPhase_add_right]
    ring
  have hcoeff : (∑ i, ‖c' i‖ ^ 2) = ∑ i, ‖c i‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [c']
  have hcenter := integral_norm_sq_le_unitIntervalLargeSieveConstant
    hd x hsep c'
  rw [hcoeff] at hcenter
  have htranslate :
      (∫ η : ℝ in Set.Icc (r - 1 / 2) (r + 1 / 2),
          ‖gramFourierPolynomial x c η‖ ^ 2) =
        ∫ η : ℝ in Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ),
          ‖gramFourierPolynomial x c (η + r)‖ ^ 2 := by
    calc
      (∫ η : ℝ in Set.Icc (r - 1 / 2) (r + 1 / 2),
          ‖gramFourierPolynomial x c η‖ ^ 2) =
          ∫ η : ℝ in (r - 1 / 2)..(r + 1 / 2),
            ‖gramFourierPolynomial x c η‖ ^ 2 := by
        rw [intervalIntegral.integral_of_le (by linarith),
          ← integral_Icc_eq_integral_Ioc]
      _ = ∫ η : ℝ in (-(1 / 2 : ℝ))..(1 / 2 : ℝ),
            ‖gramFourierPolynomial x c (η + r)‖ ^ 2 := by
        symm
        simpa only [sub_eq_add_neg, neg_div, add_comm] using
          (intervalIntegral.integral_comp_add_right
            (fun η : ℝ => ‖gramFourierPolynomial x c η‖ ^ 2)
            (a := -(1 / 2 : ℝ)) (b := (1 / 2 : ℝ)) r)
      _ = ∫ η : ℝ in Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ),
            ‖gramFourierPolynomial x c (η + r)‖ ^ 2 := by
        rw [intervalIntegral.integral_of_le (by norm_num),
          ← integral_Icc_eq_integral_Ioc]
  rw [htranslate]
  simpa only [← hpoly] using hcenter

/-- A summable polynomial envelope for the unit slabs centered at integers. -/
def integerUnitSlabEnvelope (k : ℤ) : ℝ :=
  1 / (1 + |(k : ℝ)|) ^ 2

theorem summable_integerUnitSlabEnvelope :
    Summable integerUnitSlabEnvelope := by
  apply Summable.of_add_one_of_neg_add_one
  · have hp : Summable (fun n : ℕ => (((n : ℝ) ^ 2))⁻¹) :=
      Real.summable_nat_pow_inv.mpr (by norm_num)
    have hshift : Summable
        (fun n : ℕ => ((((n + 2 : ℕ) : ℝ) ^ 2))⁻¹) :=
      hp.comp_injective (fun _ _ h => Nat.add_right_cancel h)
    convert hshift using 1
    ext n
    unfold integerUnitSlabEnvelope
    rw [abs_of_nonneg (by positivity)]
    push_cast
    ring
  · have hp : Summable (fun n : ℕ => (((n : ℝ) ^ 2))⁻¹) :=
      Real.summable_nat_pow_inv.mpr (by norm_num)
    have hshift : Summable
        (fun n : ℕ => ((((n + 2 : ℕ) : ℝ) ^ 2))⁻¹) :=
      hp.comp_injective (fun _ _ h => Nat.add_right_cancel h)
    convert hshift using 1
    ext n
    unfold integerUnitSlabEnvelope
    rw [abs_of_nonpos (by
      exact_mod_cast (show -((n : ℤ) + 1) ≤ 0 by omega))]
    push_cast
    ring

/-- On the unit slab centered at `k`, the rational Gram density is bounded by
a fixed multiple of a summable inverse-square integer envelope. -/
theorem gramDensity_le_integerUnitSlabEnvelope
    {m : ℕ} (hm : 1 ≤ m) {k : ℤ} {η : ℝ}
    (hη : η ∈ Set.Icc ((k : ℝ) - 1 / 2) ((k : ℝ) + 1 / 2)) :
    gramDensity m η ≤
      16 * gramNormalization m * integerUnitSlabEnvelope k := by
  have hnear : |η - (k : ℝ)| ≤ 1 / 2 := by
    rw [abs_le]
    constructor <;> linarith [hη.1, hη.2]
  have hkabs : |(k : ℝ)| ≤ |η| + 1 / 2 := by
    calc
      |(k : ℝ)| = |η - (η - (k : ℝ))| := by ring_nf
      _ ≤ |η| + |η - (k : ℝ)| := abs_sub _ _
      _ ≤ |η| + 1 / 2 := by linarith
  let b : ℝ := 1 + 4 * η ^ 2
  let q : ℝ := 1 + |(k : ℝ)|
  have hb : 0 < b := by dsimp only [b]; positivity
  have hq : 0 < q := by dsimp only [q]; positivity
  have hsq : q ^ 2 ≤ 8 * b := by
    dsimp only [q, b]
    nlinarith [sq_nonneg (|η| - 1), sq_abs η]
  have hinv : b⁻¹ ≤ 8 * q⁻¹ ^ 2 := by
    have hq8 : 0 < q ^ 2 / 8 := by positivity
    have hsmall : q ^ 2 / 8 ≤ b := by nlinarith
    calc
      b⁻¹ ≤ (q ^ 2 / 8)⁻¹ :=
        (inv_le_inv₀ hb hq8).2 hsmall
      _ = 8 * q⁻¹ ^ 2 := by
        rw [inv_div, inv_pow]
        rw [div_eq_mul_inv]
  have hbInv0 : 0 ≤ b⁻¹ := inv_nonneg.mpr hb.le
  have hbInv1 : b⁻¹ ≤ 1 := (inv_le_one₀ hb).2 (by
    dsimp only [b]
    nlinarith [sq_nonneg η])
  have hpow : b⁻¹ ^ (2 * m) ≤ b⁻¹ := by
    simpa only [pow_one] using
      pow_le_pow_of_le_one hbInv0 hbInv1 (show 1 ≤ 2 * m by omega)
  rw [gramDensity, rawGramDensity_eq_inv_pow]
  change 2 * gramNormalization m * b⁻¹ ^ (2 * m) ≤ _
  calc
    2 * gramNormalization m * b⁻¹ ^ (2 * m) ≤
        2 * gramNormalization m * b⁻¹ := by
      exact mul_le_mul_of_nonneg_left hpow
        (mul_nonneg (by norm_num) (gramNormalization_pos hm).le)
    _ ≤ 2 * gramNormalization m * (8 * q⁻¹ ^ 2) := by
      exact mul_le_mul_of_nonneg_left hinv
        (mul_nonneg (by norm_num) (gramNormalization_pos hm).le)
    _ = 16 * gramNormalization m * integerUnitSlabEnvelope k := by
      unfold integerUnitSlabEnvelope
      dsimp only [q]
      rw [one_div, inv_pow]
      ring

/-- Explicit global large-sieve constant for the universal rational density. -/
def universalGramLargeSieveConstant (m : ℕ) (d : ℝ) : ℝ :=
  16 * gramNormalization m *
    (∑' k : ℤ, integerUnitSlabEnvelope k) *
      unitIntervalLargeSieveConstant d

theorem universalGramLargeSieveConstant_nonneg
    {m : ℕ} (hm : 1 ≤ m) (d : ℝ) :
    0 ≤ universalGramLargeSieveConstant m d := by
  unfold universalGramLargeSieveConstant
  have henv : 0 ≤ ∑' k : ℤ, integerUnitSlabEnvelope k := by
    apply tsum_nonneg
    intro k
    unfold integerUnitSlabEnvelope
    positivity
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (by norm_num) (gramNormalization_pos hm).le) henv)
    (unitIntervalLargeSieveConstant_pos d).le

/-- The rational-density Fourier energy of every finite `d`-separated family
has a uniform upper bound.  This is the boundedness companion to the finite
universal Gram floor. -/
theorem integral_gramDensity_mul_norm_sq_le_of_separated
    {m : ℕ} (hm : 1 ≤ m) {d : ℝ} (hd : 1 < d)
    {n : ℕ} (x : Fin n → ℝ) (hsep : PairwiseFrequencySeparated x d)
    (c : Fin n → ℂ) :
    (∫ η : ℝ, gramDensity m η *
        ‖gramFourierPolynomial x c η‖ ^ 2) ≤
      universalGramLargeSieveConstant m d * ∑ i, ‖c i‖ ^ 2 := by
  let energy : ℝ → ℝ := fun η => ‖gramFourierPolynomial x c η‖ ^ 2
  let weighted : ℝ → ℝ := fun η => gramDensity m η * energy η
  let E : ℝ := ∑ i, ‖c i‖ ^ 2
  let U : ℝ := unitIntervalLargeSieveConstant d
  let A : ℝ := 16 * gramNormalization m
  have hweighted : Integrable weighted := by
    apply (integrable_gramDensity hm).mul_bdd
    · dsimp only [energy]
      exact (continuous_gramFourierPolynomial x c).norm.pow 2
        |>.aestronglyMeasurable
    · refine ae_of_all _ fun η => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _)
        (norm_gramFourierPolynomial_le x c η) 2
  have hsum := hweighted.hasSum_intervalIntegral (-(1 / 2 : ℝ))
  have hterm (k : ℤ) :
      (∫ η : ℝ in (-(1 / 2 : ℝ) + k)..(-(1 / 2 : ℝ) + k + 1),
          weighted η) ≤
        (A * U * E) * integerUnitSlabEnvelope k := by
    have hinterval :
        (∫ η : ℝ in (-(1 / 2 : ℝ) + k)..(-(1 / 2 : ℝ) + k + 1),
            weighted η) =
          ∫ η : ℝ in Set.Icc ((k : ℝ) - 1 / 2) ((k : ℝ) + 1 / 2),
            weighted η := by
      rw [intervalIntegral.integral_of_le (by
        exact le_add_of_nonneg_right zero_le_one),
        ← integral_Icc_eq_integral_Ioc]
      congr 1
      · ring
    rw [hinterval]
    have henergyInt : IntegrableOn energy
        (Set.Icc ((k : ℝ) - 1 / 2) ((k : ℝ) + 1 / 2)) := by
      apply ContinuousOn.integrableOn_compact isCompact_Icc
      dsimp only [energy]
      exact (continuous_gramFourierPolynomial x c).norm.pow 2 |>.continuousOn
    have hweightedInt : IntegrableOn weighted
        (Set.Icc ((k : ℝ) - 1 / 2) ((k : ℝ) + 1 / 2)) :=
      hweighted.integrableOn
    have hpointwise :
        (∫ η : ℝ in Set.Icc ((k : ℝ) - 1 / 2) ((k : ℝ) + 1 / 2),
            weighted η) ≤
          ∫ η : ℝ in Set.Icc ((k : ℝ) - 1 / 2) ((k : ℝ) + 1 / 2),
            (A * integerUnitSlabEnvelope k) * energy η := by
      apply integral_mono_ae hweightedInt
        (henergyInt.const_mul (A * integerUnitSlabEnvelope k))
      filter_upwards [ae_restrict_mem measurableSet_Icc] with η hη
      dsimp only [weighted]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      dsimp only [A]
      exact gramDensity_le_integerUnitSlabEnvelope hm hη
    calc
      (∫ η : ℝ in Set.Icc ((k : ℝ) - 1 / 2) ((k : ℝ) + 1 / 2),
          weighted η) ≤
          ∫ η : ℝ in Set.Icc ((k : ℝ) - 1 / 2) ((k : ℝ) + 1 / 2),
            (A * integerUnitSlabEnvelope k) * energy η := hpointwise
      _ = (A * integerUnitSlabEnvelope k) *
          (∫ η : ℝ in Set.Icc ((k : ℝ) - 1 / 2) ((k : ℝ) + 1 / 2),
            energy η) := by rw [integral_const_mul]
      _ ≤ (A * integerUnitSlabEnvelope k) * (U * E) := by
        apply mul_le_mul_of_nonneg_left _
          (mul_nonneg (by
            dsimp only [A]
            exact mul_nonneg (by norm_num) (gramNormalization_pos hm).le)
            (by unfold integerUnitSlabEnvelope; positivity))
        dsimp only [energy, U, E]
        exact integral_norm_sq_le_shiftedUnitIntervalLargeSieveConstant
          hd x hsep c (k : ℝ)
      _ = (A * U * E) * integerUnitSlabEnvelope k := by ring
  have hmajorant : Summable
      (fun k : ℤ => (A * U * E) * integerUnitSlabEnvelope k) :=
    summable_integerUnitSlabEnvelope.mul_left (A * U * E)
  change (∫ η : ℝ, weighted η) ≤ _
  calc
    (∫ η : ℝ, weighted η) =
        ∑' k : ℤ,
          ∫ η : ℝ in (-(1 / 2 : ℝ) + k)..(-(1 / 2 : ℝ) + k + 1),
            weighted η := hsum.tsum_eq.symm
    _ ≤ ∑' k : ℤ, (A * U * E) * integerUnitSlabEnvelope k :=
      hsum.summable.tsum_le_tsum hterm hmajorant
    _ = (A * U * E) * ∑' k : ℤ, integerUnitSlabEnvelope k :=
      tsum_mul_left
    _ = universalGramLargeSieveConstant m d * ∑ i, ‖c i‖ ^ 2 := by
      dsimp only [universalGramLargeSieveConstant, A, U, E]
      ring

/-- Finite upper bound for the universal Gram quadratic form on every
`d`-separated family. -/
theorem universalGramKernel_quadratic_re_le_of_separated
    {m : ℕ} (hm : 1 ≤ m) {d : ℝ} (hd : 1 < d)
    {n : ℕ} (x : Fin n → ℝ) (hsep : PairwiseFrequencySeparated x d)
    (c : Fin n → ℂ) :
    (∑ i, ∑ j, conj (c i) * c j *
        universalGramKernel m (x j - x i)).re ≤
      universalGramLargeSieveConstant m d * ∑ i, ‖c i‖ ^ 2 := by
  rw [universalGramKernel_quadratic_re_eq_integral hm x c]
  exact integral_gramDensity_mul_norm_sq_le_of_separated hm hd x hsep c

/-- Reindexed finite-type form of the universal Gram upper bound. -/
theorem universalGramKernel_quadratic_re_le_of_finite_separated
    {ι : Type*} [Fintype ι] {m : ℕ} (hm : 1 ≤ m)
    {d : ℝ} (hd : 1 < d) (x : ι → ℝ)
    (hsep : ∀ i j, i ≠ j → d ≤ |x i - x j|) (c : ι → ℂ) :
    (∑ i, ∑ j, conj (c i) * c j *
        universalGramKernel m (x j - x i)).re ≤
      universalGramLargeSieveConstant m d * ∑ i, ‖c i‖ ^ 2 := by
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let x' : Fin (Fintype.card ι) → ℝ := fun i => x (e.symm i)
  let c' : Fin (Fintype.card ι) → ℂ := fun i => c (e.symm i)
  have hsep' : PairwiseFrequencySeparated x' d := by
    intro i j hij
    apply hsep
    exact e.symm.injective.ne hij
  have hfin := universalGramKernel_quadratic_re_le_of_separated
    hm hd x' hsep' c'
  dsimp only [x', c'] at hfin
  have hQ :
      (∑ i : Fin (Fintype.card ι),
          ∑ j : Fin (Fintype.card ι),
            conj (c (e.symm i)) * c (e.symm j) *
              universalGramKernel m (x (e.symm j) - x (e.symm i))) =
        ∑ i : ι, ∑ j : ι,
          conj (c i) * c j * universalGramKernel m (x j - x i) := by
    calc
      (∑ i : Fin (Fintype.card ι),
          ∑ j : Fin (Fintype.card ι),
            conj (c (e.symm i)) * c (e.symm j) *
              universalGramKernel m (x (e.symm j) - x (e.symm i))) =
          ∑ i : Fin (Fintype.card ι), ∑ j : ι,
            conj (c (e.symm i)) * c j *
              universalGramKernel m (x j - x (e.symm i)) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact e.symm.sum_comp (fun j : ι =>
          conj (c (e.symm i)) * c j *
            universalGramKernel m (x j - x (e.symm i)))
      _ = ∑ i : ι, ∑ j : ι,
          conj (c i) * c j * universalGramKernel m (x j - x i) :=
        e.symm.sum_comp (fun i : ι => ∑ j : ι,
          conj (c i) * c j * universalGramKernel m (x j - x i))
  have hE :
      (∑ i : Fin (Fintype.card ι), ‖c (e.symm i)‖ ^ 2) =
        ∑ i : ι, ‖c i‖ ^ 2 :=
    e.symm.sum_comp (fun i : ι => ‖c i‖ ^ 2)
  rw [hQ, hE] at hfin
  exact hfin

end

end MeyerGeneralProblem
