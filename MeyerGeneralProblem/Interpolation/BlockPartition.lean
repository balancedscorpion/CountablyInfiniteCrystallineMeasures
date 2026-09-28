module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import all Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import all Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.Deriv.Support
import all Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.Analysis.Normed.Group.Bounded
import all Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Topology.LocallyFinite
import all Mathlib.Topology.LocallyFinite
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import all Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Topology.Algebra.InfiniteSum.Module
import all Mathlib.Topology.Algebra.InfiniteSum.Module

@[expose] public section

/-!
# Explicit smooth block partition

Translated differences of one fixed smooth step give the partition used by
the weighted grouped interpolant. Support widths and derivative constants
are independent of the block index. This module constructs the cutoffs; it
does not assume a partition or prove the global weighted interpolation bound.
-/

namespace MeyerGeneralProblem

open Set Filter
open scoped Topology BigOperators

noncomputable section

/-- A fixed smooth step with transition region `[-1/8, 1/8]`. -/
def unitBlockTransition (s : ℝ) : ℝ := Real.smoothTransition (4 * s + 1 / 2)

/-- The compactly supported unit-width block cutoff. -/
def unitBlockCutoff (s : ℝ) : ℝ := unitBlockTransition s - unitBlockTransition (s - 1)

/-- The smooth step at block boundary `b * B`. -/
def blockTransition (B : ℝ) (b : ℕ) (s : ℝ) : ℝ :=
  unitBlockTransition (s / B - b)

/-- The actual cutoff for block `b`, obtained by subtracting adjacent steps. -/
def blockCutoff (B : ℝ) (b : ℕ) (s : ℝ) : ℝ :=
  blockTransition B b s - blockTransition B (b + 1) s

/-- The fixed step is smooth of every order. -/
theorem contDiff_unitBlockTransition {n : ℕ∞} : ContDiff ℝ n unitBlockTransition := by
  exact Real.smoothTransition.contDiff.comp (by fun_prop)

/-- The fixed cutoff is smooth of every order. -/
theorem contDiff_unitBlockCutoff {n : ℕ∞} : ContDiff ℝ n unitBlockCutoff := by
  exact contDiff_unitBlockTransition.sub (contDiff_unitBlockTransition.comp (by fun_prop))

/-- The fixed step vanishes to the left of the declared transition region. -/
theorem unitBlockTransition_zero {s : ℝ} (hs : s ≤ -(1 / 8 : ℝ)) :
    unitBlockTransition s = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

/-- The fixed step equals one to the right of the transition region. -/
theorem unitBlockTransition_one {s : ℝ} (hs : (1 / 8 : ℝ) ≤ s) :
    unitBlockTransition s = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

/-- The fixed transition is nondecreasing. -/
theorem monotone_unitBlockTransition : Monotone unitBlockTransition := by
  intro x y hxy
  exact Real.smoothTransition.monotone (by linarith)

/-- Every cutoff value lies between zero and one. -/
theorem unitBlockCutoff_mem_Icc (s : ℝ) : unitBlockCutoff s ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact sub_nonneg.mpr (monotone_unitBlockTransition (by linarith))
  · have h1 := Real.smoothTransition.le_one (4 * s + 1 / 2)
    have h0 := Real.smoothTransition.nonneg (4 * (s - 1) + 1 / 2)
    dsimp [unitBlockCutoff, unitBlockTransition]
    linarith

/-- The unit cutoff is supported in the specified slightly enlarged block. -/
theorem support_unitBlockCutoff_subset :
    Function.support unitBlockCutoff ⊆ Icc (-(1 / 8 : ℝ)) (9 / 8) := by
  intro s hs
  rw [Function.mem_support] at hs
  constructor
  · by_contra h
    have hleft : s ≤ -(1 / 8 : ℝ) := le_of_not_ge h
    have hleft' : s - 1 ≤ -(1 / 8 : ℝ) := by linarith
    exact hs (by simp [unitBlockCutoff, unitBlockTransition_zero hleft,
      unitBlockTransition_zero hleft'])
  · by_contra h
    have hright : (1 / 8 : ℝ) ≤ s := by linarith [lt_of_not_ge h]
    have hright' : (1 / 8 : ℝ) ≤ s - 1 := by linarith [lt_of_not_ge h]
    exact hs (by simp [unitBlockCutoff, unitBlockTransition_one hright,
      unitBlockTransition_one hright'])

/-- The fixed unit cutoff has genuine compact support. -/
theorem hasCompactSupport_unitBlockCutoff : HasCompactSupport unitBlockCutoff :=
  HasCompactSupport.intro isCompact_Icc fun _s hs =>
    Function.notMem_support.mp (fun h => hs (support_unitBlockCutoff_subset h))

/-- Every block cutoff is a translate and rescaling of the single unit cutoff. -/
theorem blockCutoff_eq_unit (B : ℝ) (b : ℕ) (s : ℝ) :
    blockCutoff B b s = unitBlockCutoff (s / B - b) := by
  simp only [blockCutoff, blockTransition, unitBlockCutoff, Nat.cast_add, Nat.cast_one]
  congr 2
  ring

/-- The actual block cutoff is smooth at every order. -/
theorem contDiff_blockCutoff (B : ℝ) (b : ℕ) {n : ℕ∞} :
    ContDiff ℝ n (blockCutoff B b) := by
  have heq : blockCutoff B b = fun s => unitBlockCutoff (s / B - b) :=
    funext (blockCutoff_eq_unit B b)
  rw [heq]
  exact contDiff_unitBlockCutoff.comp (by fun_prop)

/-- The actual cutoffs are nonnegative and at most one. -/
theorem blockCutoff_mem_Icc (B : ℝ) (b : ℕ) (s : ℝ) :
    blockCutoff B b s ∈ Icc (0 : ℝ) 1 := by
  rw [blockCutoff_eq_unit]
  exact unitBlockCutoff_mem_Icc _

/-- Every cutoff has exactly the support enclosure required by the retained
three-block construction, with no dependence on a carrier's node gaps. -/
theorem support_blockCutoff_subset {B : ℝ} (hB : 0 < B) (b : ℕ) :
    Function.support (blockCutoff B b) ⊆
      Icc ((b : ℝ) * B - B / 8) (((b : ℝ) + 1) * B + B / 8) := by
  intro s hs
  have hu : s / B - b ∈ Function.support unitBlockCutoff := by
    simpa only [Function.mem_support, blockCutoff_eq_unit] using hs
  have hb := support_unitBlockCutoff_subset hu
  have hl : ((b : ℝ) - 1 / 8) * B ≤ s :=
    (le_div_iff₀ hB).mp (by linarith [hb.1])
  have hr : s ≤ ((b : ℝ) + 9 / 8) * B :=
    (div_le_iff₀ hB).mp (by linarith [hb.2])
  constructor <;> nlinarith

/-- Every derivative of the unit cutoff still has compact support. -/
theorem hasCompactSupport_iteratedDeriv_unitBlockCutoff (j : ℕ) :
    HasCompactSupport (iteratedDeriv j unitBlockCutoff) := by
  induction j with
  | zero => simpa using hasCompactSupport_unitBlockCutoff
  | succ j ih => simpa only [iteratedDeriv_succ] using ih.deriv

/-- Every fixed derivative order admits a bound for the unit cutoff. -/
theorem exists_bound_iteratedDeriv_unitBlockCutoff (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s, ‖iteratedDeriv j unitBlockCutoff s‖ ≤ C := by
  obtain ⟨C, hC⟩ := (hasCompactSupport_iteratedDeriv_unitBlockCutoff j).exists_bound_of_continuous
    (contDiff_unitBlockCutoff.continuous_iteratedDeriv' j)
  refine ⟨max C 0 + 1, by positivity, fun s => (hC s).trans ?_⟩
  exact (le_max_left C 0).trans (by linarith)

/-- Differentiation of the cutoffs has the exact scale factor `B⁻¹ ^ j`.
All block-index dependence is a translation of one fixed derivative. -/
theorem iteratedDeriv_blockCutoff (B : ℝ) (b j : ℕ) :
    iteratedDeriv j (blockCutoff B b) =
      fun s => (B⁻¹) ^ j * iteratedDeriv j unitBlockCutoff (s / B - b) := by
  have heq : blockCutoff B b =
      fun s => (fun u => unitBlockCutoff (u - b)) (B⁻¹ * s) := by
    funext s
    rw [blockCutoff_eq_unit]
    congr 1
    rw [div_eq_mul_inv, mul_comm]
  have hshift : ContDiff ℝ (j : ℕ∞) (fun u : ℝ => unitBlockCutoff (u - (b : ℝ))) :=
    contDiff_unitBlockCutoff.comp (by fun_prop)
  rw [heq, iteratedDeriv_comp_const_mul hshift B⁻¹, iteratedDeriv_comp_sub_const]
  simp only [div_eq_mul_inv, mul_comm B⁻¹]

/-- One positive constant per derivative order works for every positive
block width, block index and position, with the retained `B⁻ʲ` scaling. -/
theorem exists_uniform_blockCutoff_derivative_bound (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℝ), 0 < B → ∀ (b : ℕ) (s : ℝ),
      ‖iteratedDeriv j (blockCutoff B b) s‖ ≤ C * (B⁻¹) ^ j := by
  obtain ⟨C, hCpos, hC⟩ := exists_bound_iteratedDeriv_unitBlockCutoff j
  refine ⟨C, hCpos, fun B hB b s => ?_⟩
  rw [iteratedDeriv_blockCutoff, norm_mul, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hB.le) _), mul_comm C]
  exact mul_le_mul_of_nonneg_left (hC _) (by positivity)

/-- The cutoff support intervals are locally finite, proved directly from
their diverging left endpoints. -/
theorem locallyFinite_blockCutoff_intervals {B : ℝ} (hB : 0 < B) :
    LocallyFinite (fun b : ℕ =>
      Icc ((b : ℝ) * B - B / 8) (((b : ℝ) + 1) * B + B / 8)) := by
  intro x
  obtain ⟨N, hN⟩ := exists_nat_gt ((x + 1 + B / 8) / B)
  refine ⟨Iio (x + 1), Iio_mem_nhds (by linarith), (Set.finite_Iio N).subset ?_⟩
  rintro b ⟨s, hs, hxs⟩
  change b < N
  by_contra h
  have hNb : (N : ℝ) ≤ b := by exact_mod_cast (le_of_not_gt h)
  have hlarge : x + 1 + B / 8 < (N : ℝ) * B := (div_lt_iff₀ hB).mp hN
  have hmul := mul_le_mul_of_nonneg_right hNb hB.le
  have hx : s < x + 1 := hxs
  linarith [hs.1]

/-- The actual cutoff supports form a locally finite family. -/
theorem locallyFinite_blockCutoff_support {B : ℝ} (hB : 0 < B) :
    LocallyFinite (fun b : ℕ => Function.support (blockCutoff B b)) :=
  (locallyFinite_blockCutoff_intervals hB).subset (support_blockCutoff_subset hB)

/-- Finite sums telescope exactly, starting at any tail block. -/
theorem sum_range_blockCutoff (B : ℝ) (start n : ℕ) (s : ℝ) :
    (∑ b ∈ Finset.range n, blockCutoff B (start + b) s) =
      blockTransition B start s - blockTransition B (start + n) s := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [blockCutoff, Nat.add_succ]
      ring

/-- At a fixed point all sufficiently distant transition steps vanish. -/
theorem eventually_blockTransition_eq_zero (B : ℝ) (start : ℕ) (s : ℝ) :
    ∀ᶠ n : ℕ in atTop, blockTransition B (start + n) s = 0 := by
  obtain ⟨N, hN⟩ := exists_nat_gt (s / B - start + 1)
  apply eventually_atTop.mpr
  refine ⟨N, fun n hn => ?_⟩
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
  apply unitBlockTransition_zero
  push_cast
  linarith

/-- The actual infinite tail of cutoffs sums to the initial transition;
this is a proved partition identity, not an input to the construction. -/
theorem hasSum_blockCutoff (B : ℝ) (start : ℕ) (s : ℝ) :
    HasSum (fun n : ℕ => blockCutoff B (start + n) s) (blockTransition B start s) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun n => (blockCutoff_mem_Icc B _ s).1) _).mpr
  have heq : (fun n : ℕ => ∑ b ∈ Finset.range n, blockCutoff B (start + b) s)
      =ᶠ[atTop] fun _ => blockTransition B start s := by
    filter_upwards [eventually_blockTransition_eq_zero B start s] with n hn
    simp only [sum_range_blockCutoff, hn, sub_zero]
  exact tendsto_const_nhds.congr' heq.symm

/-- Adding the central cutoff to the actual tail gives exactly one. -/
theorem central_add_tsum_blockCutoff (B : ℝ) (start : ℕ) (s : ℝ) :
    (1 - blockTransition B start s) + ∑' n : ℕ, blockCutoff B (start + n) s = 1 := by
  rw [(hasSum_blockCutoff B start s).tsum_eq]
  ring

/-- Multiplying arbitrary functions by the actual tail cutoffs leaves a
finite sum at each point, irrespective of growth of those functions. -/
theorem summable_blockCutoff_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {B : ℝ} (hB : 0 < B) (start : ℕ) (f : ℕ → ℝ → E) (s : ℝ) :
    Summable (fun n => blockCutoff B (start + n) s • f n s) := by
  have hloc : LocallyFinite (fun n => Function.support (blockCutoff B (start + n))) :=
    (locallyFinite_blockCutoff_support hB).comp_injective
      (show Function.Injective (fun n : ℕ => start + n) from fun _ _ h => Nat.add_left_cancel h)
  apply summable_of_hasFiniteSupport
  apply (hloc.point_finite s).subset
  intro n hn
  rw [Function.mem_support] at hn
  change blockCutoff B (start + n) s ≠ 0
  exact fun hzero => hn (by simp [hzero])

/-- The actual locally finite cutoff sum is smooth when its summands are
smooth. No convergence of an infinite derivative series is presumed. -/
theorem contDiff_tsum_blockCutoff_smul {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {B : ℝ} (hB : 0 < B) (start : ℕ) (f : ℕ → ℝ → E) {k : ℕ∞}
    (hf : ∀ n, ContDiff ℝ k (f n)) :
    ContDiff ℝ k (fun s => ∑' n : ℕ, blockCutoff B (start + n) s • f n s) := by
  classical
  apply contDiff_iff_contDiffAt.mpr
  intro x
  let I : ℕ → Set ℝ := fun n =>
    Icc (((start + n : ℕ) : ℝ) * B - B / 8)
      ((((start + n : ℕ) : ℝ) + 1) * B + B / 8)
  have hloc : LocallyFinite I :=
    (locallyFinite_blockCutoff_intervals hB).comp_injective
      (show Function.Injective (fun n : ℕ => start + n) from fun _ _ h => Nat.add_left_cancel h)
  let S : Finset ℕ := (hloc.point_finite x).toFinset
  have hnear := hloc.eventually_subset (fun _ => isClosed_Icc) x
  have heq : (fun s => ∑' n : ℕ, blockCutoff B (start + n) s • f n s) =ᶠ[𝓝 x]
      (fun s => ∑ n ∈ S, blockCutoff B (start + n) s • f n s) := by
    filter_upwards [hnear] with s hs
    apply tsum_eq_sum
    intro n hn
    have hzero : blockCutoff B (start + n) s = 0 := by
      by_contra hnonzero
      have hsI := support_blockCutoff_subset hB (start + n) hnonzero
      have hxI := hs hsI
      exact hn (by simpa only [S, Set.Finite.mem_toFinset] using hxI)
    simp [hzero]
  exact (ContDiffAt.sum (fun n _ =>
    ((contDiff_blockCutoff B (start + n)).smul (hf n)).contDiffAt)).congr_of_eventuallyEq heq

/-- The actual central-plus-tail gluing operator on smooth local pieces. -/
def blockGluing {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : ℝ) (start : ℕ) (central : ℝ → E) (pieces : ℕ → ℝ → E) (s : ℝ) : E :=
  (1 - blockTransition B start s) • central s +
    ∑' n : ℕ, blockCutoff B (start + n) s • pieces n s

/-- The central step is smooth, with no restriction on the index. -/
theorem contDiff_blockTransition (B : ℝ) (b : ℕ) {k : ℕ∞} :
    ContDiff ℝ k (blockTransition B b) :=
  contDiff_unitBlockTransition.comp (by fun_prop)

/-- The explicitly constructed gluing is smooth. Local finiteness, not an
unproved globally summable derivative bound, justifies the infinite sum. -/
theorem contDiff_blockGluing {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {B : ℝ} (hB : 0 < B) (start : ℕ) (central : ℝ → E) (pieces : ℕ → ℝ → E)
    {k : ℕ∞} (hcentral : ContDiff ℝ k central) (hpieces : ∀ n, ContDiff ℝ k (pieces n)) :
    ContDiff ℝ k (blockGluing B start central pieces) :=
  ((contDiff_const.sub (contDiff_blockTransition B start)).smul hcentral).add
    (contDiff_tsum_blockCutoff_smul hB start pieces hpieces)

/-- The partition preserves a value whenever every active local piece
interpolates it. This reduces global interpolation to actual local values. -/
theorem blockGluing_eq_of_active_values {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : ℝ) (start : ℕ) (central : ℝ → E) (pieces : ℕ → ℝ → E) (s : ℝ) (v : E)
    (hcentral : 1 - blockTransition B start s ≠ 0 → central s = v)
    (hpieces : ∀ n, blockCutoff B (start + n) s ≠ 0 → pieces n s = v) :
    blockGluing B start central pieces s = v := by
  have h0 : (1 - blockTransition B start s) • central s =
      (1 - blockTransition B start s) • v := by
    by_cases h : 1 - blockTransition B start s = 0
    · simp [h]
    · rw [hcentral h]
  have hn (n : ℕ) : blockCutoff B (start + n) s • pieces n s =
      blockCutoff B (start + n) s • v := by
    by_cases h : blockCutoff B (start + n) s = 0
    · simp [h]
    · rw [hpieces n h]
  simp only [blockGluing, h0, hn, ((hasSum_blockCutoff B start s).smul_const v).tsum_eq]
  rw [← add_smul]
  simp

end

end MeyerGeneralProblem
