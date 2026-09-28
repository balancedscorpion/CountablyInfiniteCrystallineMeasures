module

public import MeyerGeneralProblem.Interpolation.BlockPartition
public import Mathlib.Algebra.Order.Floor.Semiring
import all Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Order.Interval.Finset.Nat
import all Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import all Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import all Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import all Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section

/-!
# Actual block-overlap bounds

The explicit enlarged block intervals have at most three active natural
indices on the positive half-line. The same enclosure holds for every
derivative. These geometric facts control the energy of the actual locally
finite sum, without assuming an overlap certificate.
-/

namespace MeyerGeneralProblem

open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology

noncomputable section

/-- Three adjacent natural indices containing every active enlarged block. -/
def blockOverlapIndices (B s : ℝ) : Finset ℕ :=
  Finset.Icc (⌊s / B⌋₊ - 1) (⌊s / B⌋₊ + 1)

/-- The displayed set of possible active indices has cardinality at most three. -/
theorem card_blockOverlapIndices_le (B s : ℝ) :
    (blockOverlapIndices B s).card ≤ 3 := by
  simp only [blockOverlapIndices, Nat.card_Icc]
  omega

/-- Actual enlarged block membership forces one of the three adjacent indices. -/
theorem mem_blockOverlapIndices_of_mem_interval {B s : ℝ} (hB : 0 < B)
    (hs : 0 ≤ s) {b : ℕ}
    (hb : s ∈ Icc ((b : ℝ) * B - B / 8) (((b : ℝ) + 1) * B + B / 8)) :
    b ∈ blockOverlapIndices B s := by
  have hfloor := Nat.floor_le (div_nonneg hs hB.le)
  have hceil := Nat.lt_floor_add_one (s / B)
  have hleft : (b : ℝ) - 1 / 8 ≤ s / B := (le_div_iff₀ hB).mpr (by nlinarith [hb.1])
  have hright : s / B ≤ (b : ℝ) + 9 / 8 := (div_le_iff₀ hB).mpr (by nlinarith [hb.2])
  have hlo : ⌊s / B⌋₊ ≤ b + 1 := by
    have h : (⌊s / B⌋₊ : ℝ) < (b : ℝ) + 2 := by linarith
    have : ⌊s / B⌋₊ < b + 2 := by exact_mod_cast h
    omega
  have hhi : b ≤ ⌊s / B⌋₊ + 1 := by
    have h : (b : ℝ) < (⌊s / B⌋₊ : ℝ) + 2 := by linarith
    have : b < ⌊s / B⌋₊ + 2 := by exact_mod_cast h
    omega
  simp only [blockOverlapIndices, Finset.mem_Icc]
  omega

/-- Every iterated derivative is supported in the original closed block enclosure. -/
theorem tsupport_iteratedDeriv_blockCutoff_subset {B : ℝ} (hB : 0 < B)
    (b j : ℕ) :
    tsupport (iteratedDeriv j (blockCutoff B b)) ⊆
      Icc ((b : ℝ) * B - B / 8) (((b : ℝ) + 1) * B + B / 8) := by
  induction j with
  | zero =>
    simpa only [iteratedDeriv_zero, tsupport] using
      closure_minimal (support_blockCutoff_subset hB b) isClosed_Icc
  | succ j ih =>
    simpa only [iteratedDeriv_succ] using tsupport_deriv_subset.trans ih

/-- The derivative of any order vanishes outside the same three indices. -/
theorem iteratedDeriv_blockCutoff_eq_zero_of_notMem {B s : ℝ}
    (hB : 0 < B) (hs : 0 ≤ s) (b j : ℕ)
    (hb : b ∉ blockOverlapIndices B s) :
    iteratedDeriv j (blockCutoff B b) s = 0 := by
  by_contra h
  exact hb (mem_blockOverlapIndices_of_mem_interval hB hs
    (tsupport_iteratedDeriv_blockCutoff_subset hB b j (subset_closure h)))

/-- A finite vector sum has squared norm bounded by its cardinality times energy. -/
theorem norm_sum_sq_le_card_mul_sum_norm_sq {E : Type*} [NormedAddCommGroup E]
    (S : Finset ℕ) (v : ℕ → E) :
    ‖∑ b ∈ S, v b‖ ^ 2 ≤ (S.card : ℝ) * ∑ b ∈ S, ‖v b‖ ^ 2 := by
  calc
    ‖∑ b ∈ S, v b‖ ^ 2 ≤ (∑ b ∈ S, ‖v b‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    _ ≤ (S.card : ℝ) * ∑ b ∈ S, ‖v b‖ ^ 2 := by
      simpa using Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℝ)) (fun b => ‖v b‖)

/-- Actual cutoff derivatives times arbitrary values have finite support and
the overlap-three pointwise energy bound, uniformly in derivative order. -/
theorem norm_tsum_blockCutoff_derivative_smul_sq_le {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {B s : ℝ}
    (hB : 0 < B) (hs : 0 ≤ s) (j : ℕ) (v : ℕ → E) :
    ‖∑' b : ℕ, iteratedDeriv j (blockCutoff B b) s • v b‖ ^ 2 ≤
      3 * ∑' b : ℕ, ‖iteratedDeriv j (blockCutoff B b) s • v b‖ ^ 2 := by
  classical
  have hz (b : ℕ) (hb : b ∉ blockOverlapIndices B s) :
      iteratedDeriv j (blockCutoff B b) s • v b = 0 := by
    rw [iteratedDeriv_blockCutoff_eq_zero_of_notMem hB hs b j hb, zero_smul]
  rw [tsum_eq_sum hz, tsum_eq_sum (fun b hb => by simp [hz b hb])]
  exact (norm_sum_sq_le_card_mul_sum_norm_sq _ _).trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast card_blockOverlapIndices_le B s)
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

/-- The actual physical-space local summand obtained by composing a block
cutoff with the signed-square chart on one ray. -/
def quadraticBlockPiece (B : ℝ) (b : ℕ) (p : ℝ → ℂ) (x : ℝ) : ℂ :=
  blockCutoff B b (x ^ 2) • p x

/-- Every derivative is supported in the original topological support. -/
theorem tsupport_iteratedDeriv_subset_original {f : ℝ → ℂ} (j : ℕ) :
    tsupport (iteratedDeriv j f) ⊆ tsupport f := by
  induction j with
  | zero => simp
  | succ j ih => simpa only [iteratedDeriv_succ] using tsupport_deriv_subset.trans ih

/-- The actual physical summand and all its derivatives stay in the same
quadratic block enclosure, independently of the local polynomial. -/
theorem tsupport_iteratedDeriv_quadraticBlockPiece_subset {B : ℝ} (hB : 0 < B)
    (b j : ℕ) (p : ℝ → ℂ) :
    tsupport (iteratedDeriv j (quadraticBlockPiece B b p)) ⊆
      (fun x : ℝ => x ^ 2) ⁻¹'
        Icc ((b : ℝ) * B - B / 8) (((b : ℝ) + 1) * B + B / 8) := by
  apply (tsupport_iteratedDeriv_subset_original j).trans
  apply closure_minimal _ (isClosed_Icc.preimage (by fun_prop))
  intro x hx
  apply support_blockCutoff_subset hB b
  intro hz
  exact hx (by simp [quadraticBlockPiece, hz])

/-- The actual physical summand is as smooth as its local factor. -/
theorem contDiff_quadraticBlockPiece (B : ℝ) (b : ℕ) {p : ℝ → ℂ}
    {j : ℕ∞} (hp : ContDiff ℝ j p) : ContDiff ℝ j (quadraticBlockPiece B b p) :=
  ((contDiff_blockCutoff B b).comp (by fun_prop)).smul hp

/-- All physical derivative summands have the same overlap-three energy
bound. This includes the growth from differentiating the quadratic chart. -/
theorem norm_tsum_iteratedDeriv_quadraticBlockPiece_sq_le {B : ℝ} (hB : 0 < B)
    (p : ℕ → ℝ → ℂ) (j : ℕ) (x : ℝ) :
    ‖∑' b : ℕ, iteratedDeriv j (quadraticBlockPiece B b (p b)) x‖ ^ 2 ≤
      3 * ∑' b : ℕ, ‖iteratedDeriv j (quadraticBlockPiece B b (p b)) x‖ ^ 2 := by
  classical
  have hz (b : ℕ) (hb : b ∉ blockOverlapIndices B (x ^ 2)) :
      iteratedDeriv j (quadraticBlockPiece B b (p b)) x = 0 := by
    by_contra h
    exact hb (mem_blockOverlapIndices_of_mem_interval hB (sq_nonneg x)
      (tsupport_iteratedDeriv_quadraticBlockPiece_subset hB b j (p b) (subset_closure h)))
  rw [tsum_eq_sum hz, tsum_eq_sum (fun b hb => by simp [hz b hb])]
  have hcard : ((blockOverlapIndices B (x ^ 2)).card : ℝ) ≤ 3 := by
    exact Nat.cast_le.mpr (card_blockOverlapIndices_le B (x ^ 2))
  apply (norm_sum_sq_le_card_mul_sum_norm_sq (blockOverlapIndices B (x ^ 2))
    (fun b => iteratedDeriv j (quadraticBlockPiece B b (p b)) x)).trans
  exact mul_le_mul_of_nonneg_right hcard (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

/-- Actual differentiation commutes with the locally finite physical sum;
no convergence of a formal derivative series is an input. -/
theorem iteratedDeriv_tsum_quadraticBlockPiece {B : ℝ} (hB : 0 < B)
    (p : ℕ → ℝ → ℂ) (j : ℕ) (hp : ∀ b, ContDiff ℝ j (p b)) (x : ℝ) :
    iteratedDeriv j (fun y => ∑' b : ℕ, quadraticBlockPiece B b (p b) y) x =
      ∑' b : ℕ, iteratedDeriv j (quadraticBlockPiece B b (p b)) x := by
  classical
  let I : ℕ → Set ℝ := fun b => (fun y : ℝ => y ^ 2) ⁻¹'
    Icc ((b : ℝ) * B - B / 8) (((b : ℝ) + 1) * B + B / 8)
  have hloc : LocallyFinite I :=
    (locallyFinite_blockCutoff_intervals hB).preimage_continuous (by fun_prop)
  let S : Finset ℕ := (hloc.point_finite x).toFinset
  have hnear := hloc.eventually_subset (fun _ => isClosed_Icc.preimage (by fun_prop)) x
  have heq : (fun y => ∑' b : ℕ, quadraticBlockPiece B b (p b) y) =ᶠ[𝓝 x]
      (fun y => ∑ b ∈ S, quadraticBlockPiece B b (p b) y) := by
    filter_upwards [hnear] with y hy
    apply tsum_eq_sum
    intro b hb
    by_contra h
    have hI : y ∈ I b := tsupport_iteratedDeriv_quadraticBlockPiece_subset hB b 0 (p b)
      (subset_closure (by simpa only [iteratedDeriv_zero, Function.mem_support] using h))
    exact hb (by simpa only [S, Set.Finite.mem_toFinset] using hy hI)
  rw [heq.iteratedDeriv_eq j, iteratedDeriv_fun_sum
    (fun b _ => (contDiff_quadraticBlockPiece B b (hp b)).contDiffAt)]
  symm
  apply tsum_eq_sum
  intro b hb
  by_contra h
  exact hb (by simpa only [S, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, I, Set.mem_preimage] using
    tsupport_iteratedDeriv_quadraticBlockPiece_subset hB b j (p b) (subset_closure h))

/-- Tonelli and actual overlap control global weighted derivative energy.
The extended-valued right side exposes, rather than assumes, any remaining
summability obligation for the local interpolation estimates. -/
theorem lintegral_iteratedDeriv_tsum_quadraticBlockPiece_le {B : ℝ} (hB : 0 < B)
    (p : ℕ → ℝ → ℂ) (j : ℕ) (hp : ∀ b, ContDiff ℝ j (p b))
    (w : ℝ → ℝ≥0∞) (hw : Measurable w) :
    (∫⁻ x : ℝ, w x * ENNReal.ofReal
      (‖iteratedDeriv j (fun y => ∑' b : ℕ, quadraticBlockPiece B b (p b) y) x‖ ^ 2)) ≤
      3 * ∑' b : ℕ, ∫⁻ x : ℝ,
        w x * ENNReal.ofReal (‖iteratedDeriv j (quadraticBlockPiece B b (p b)) x‖ ^ 2) := by
  classical
  have hpoint (x : ℝ) :
      ENNReal.ofReal
        (‖iteratedDeriv j (fun y => ∑' b : ℕ, quadraticBlockPiece B b (p b) y) x‖ ^ 2) ≤
        3 * ∑' b : ℕ,
          ENNReal.ofReal (‖iteratedDeriv j (quadraticBlockPiece B b (p b)) x‖ ^ 2) := by
    rw [iteratedDeriv_tsum_quadraticBlockPiece hB p j hp]
    have hs : Summable (fun b : ℕ => ‖iteratedDeriv j (quadraticBlockPiece B b (p b)) x‖ ^ 2) := by
      apply summable_of_hasFiniteSupport
      apply (blockOverlapIndices B (x ^ 2)).finite_toSet.subset
      intro b hb
      apply mem_blockOverlapIndices_of_mem_interval hB (sq_nonneg x)
      apply tsupport_iteratedDeriv_quadraticBlockPiece_subset hB b j (p b)
      apply subset_closure
      intro hz
      exact hb (by simp [hz])
    have h := ENNReal.ofReal_le_ofReal (norm_tsum_iteratedDeriv_quadraticBlockPiece_sq_le hB p j x)
    simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3),
      ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hs, ENNReal.ofReal_ofNat] using h
  calc
    _ ≤ ∫⁻ x : ℝ, 3 * ∑' b : ℕ,
        w x * ENNReal.ofReal (‖iteratedDeriv j (quadraticBlockPiece B b (p b)) x‖ ^ 2) := by
      apply lintegral_mono
      intro x
      have h := mul_le_mul' (le_refl (w x)) (hpoint x)
      simpa only [ENNReal.tsum_mul_left, mul_left_comm (w x) 3] using h
    _ = _ := by
      rw [lintegral_const_mul' _ _ (by norm_num), lintegral_tsum]
      intro b
      exact (hw.mul ((((contDiff_quadraticBlockPiece B b (hp b)).continuous_iteratedDeriv' j).norm.pow 2).measurable.ennreal_ofReal)).aemeasurable

end

end MeyerGeneralProblem
