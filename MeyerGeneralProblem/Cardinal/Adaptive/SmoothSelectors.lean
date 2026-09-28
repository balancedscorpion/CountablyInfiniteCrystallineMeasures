module

public import MeyerGeneralProblem.Cardinal.Adaptive.NativeDualMultipliers
public import MeyerGeneralProblem.Cardinal.Adaptive.UnitPartition
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
import all Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import all Mathlib.Analysis.Calculus.BumpFunction.Convolution

@[expose] public section

/-! Smooth neighbourhood selectors with constants independent of the chosen set. -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open MeasureTheory Set Function
open scoped Convolution ContDiff Topology

/-- The open union of radius-ε neighbourhoods; no measurability of S is assumed. -/
def selectorNeighborhood (ε : ℝ) (S : Set ℝ) : Set ℝ := ⋃ y ∈ S, Metric.ball y ε

theorem selectorNeighborhood_isOpen (ε : ℝ) (S : Set ℝ) :
    IsOpen (selectorNeighborhood ε S) := isOpen_iUnion fun _ => isOpen_iUnion fun _ => Metric.isOpen_ball

/-- Smoothing an actual indicator, rather than summing one bump per atom. -/
def smoothIndicator (κ : ℝ → ℝ) (U : Set ℝ) : ℝ → ℝ :=
  κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] U.indicator (fun _ => (1:ℝ))

private theorem indicator_locallyIntegrable (U : Set ℝ) (hU : MeasurableSet U) :
    LocallyIntegrable (U.indicator (fun _ => (1:ℝ))) volume :=
  (locallyIntegrable_const 1).indicator hU

theorem smoothIndicator_contDiff (κ : ℝ → ℝ) (hκ : HasCompactSupport κ)
    (hc : ContDiff ℝ ∞ κ) (U : Set ℝ) (hU : MeasurableSet U) :
    ContDiff ℝ ∞ (smoothIndicator κ U) :=
  hκ.contDiff_convolution_left _ hc (indicator_locallyIntegrable U hU)

private theorem compact_iteratedDeriv (κ : ℝ → ℝ) (hκ : HasCompactSupport κ) (r : ℕ) :
    HasCompactSupport (iteratedDeriv r κ) := by
  induction r with
  | zero => simpa only [iteratedDeriv_zero] using hκ
  | succ r ih => rw [iteratedDeriv_succ]; exact ih.deriv

private theorem smooth_iteratedDeriv (κ : ℝ → ℝ) (hc : ContDiff ℝ ∞ κ) (r : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv r κ) := by
  induction r with
  | zero => simpa only [iteratedDeriv_zero] using hc
  | succ r ih => rw [iteratedDeriv_succ]; exact (contDiff_infty_iff_deriv.mp ih).2

/-- Every derivative falls on the fixed kernel. -/
theorem smoothIndicator_iteratedDeriv (κ : ℝ → ℝ) (hκ : HasCompactSupport κ)
    (hc : ContDiff ℝ ∞ κ) (U : Set ℝ) (hU : MeasurableSet U) (r : ℕ) :
    iteratedDeriv r (smoothIndicator κ U) = smoothIndicator (iteratedDeriv r κ) U := by
  induction r with
  | zero => simp only [iteratedDeriv_zero]
  | succ r ih =>
      rw [iteratedDeriv_succ, ih, iteratedDeriv_succ]
      ext x
      exact ((compact_iteratedDeriv κ hκ r).hasDerivAt_convolution_left _
        ((smooth_iteratedDeriv κ hc r).of_le (by simp))
        (indicator_locallyIntegrable U hU) x).deriv

/-- The complete derivative estimate uses the kernel L1 norm and no count of atoms. -/
theorem smoothIndicator_derivative_bound (κ : ℝ → ℝ) (hκ : HasCompactSupport κ)
    (hc : ContDiff ℝ ∞ κ) (U : Set ℝ) (hU : MeasurableSet U) (r : ℕ) (x : ℝ) :
    ‖iteratedDeriv r (smoothIndicator κ U) x‖ ≤ ∫ t : ℝ, ‖iteratedDeriv r κ t‖ := by
  rw [smoothIndicator_iteratedDeriv κ hκ hc U hU r]
  unfold smoothIndicator
  rw [convolution_def]
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
    (((smooth_iteratedDeriv κ hc r).continuous.integrable_of_hasCompactSupport
      (compact_iteratedDeriv κ hκ r)).norm)
  apply Filter.Eventually.of_forall
  intro t
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, norm_mul]
  have hi : ‖U.indicator (fun _ => (1:ℝ)) (x-t)‖ ≤ 1 := by
    by_cases h : x-t ∈ U <;> simp [h]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hi (norm_nonneg _)

/-- A normalized bump supplies the local smoothing kernel. -/
def selectorKernelBump (ε : ℝ) (hε : 0 < ε) : ContDiffBump (0:ℝ) where
  rIn := ε/2
  rOut := ε
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

/-- Local selector at a fixed geometric resolution. -/
def neighborhoodSelector (ε : ℝ) (hε : 0 < ε) (S : Set ℝ) : ℝ → ℝ :=
  smoothIndicator ((selectorKernelBump ε hε).normed volume) (selectorNeighborhood (2*ε) S)

theorem neighborhoodSelector_contDiff (ε : ℝ) (hε : 0 < ε) (S : Set ℝ) :
    ContDiff ℝ ∞ (neighborhoodSelector ε hε S) :=
  smoothIndicator_contDiff _ (selectorKernelBump ε hε).hasCompactSupport_normed
    (selectorKernelBump ε hε).contDiff_normed _ (selectorNeighborhood_isOpen _ _).measurableSet

theorem neighborhoodSelector_derivative_bound (ε : ℝ) (hε : 0 < ε) (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (S : Set ℝ) (x : ℝ),
      ‖iteratedDeriv r (neighborhoodSelector ε hε S) x‖ ≤ C := by
  refine ⟨∫ t : ℝ, ‖iteratedDeriv r ((selectorKernelBump ε hε).normed volume) t‖,
    integral_nonneg (fun _ => norm_nonneg _), ?_⟩
  intro S x
  exact smoothIndicator_derivative_bound _ (selectorKernelBump ε hε).hasCompactSupport_normed
    (selectorKernelBump ε hε).contDiff_normed _ (selectorNeighborhood_isOpen _ _).measurableSet r x

/-- The selector is identically one near every selected point. -/
theorem neighborhoodSelector_eq_one (ε : ℝ) (hε : 0 < ε) (S : Set ℝ)
    (y : ℝ) (hy : y ∈ S) (x : ℝ) (hx : dist x y < ε) :
    neighborhoodSelector ε hε S x = 1 := by
  have hin (z : ℝ) (hz : dist z x < ε) : z ∈ selectorNeighborhood (2*ε) S := by
    exact mem_iUnion.mpr ⟨y, mem_iUnion.mpr ⟨hy,
      (dist_triangle z x y).trans_lt (by linarith)⟩⟩
  have hxU := hin x (by simpa using hε)
  have he := (selectorKernelBump ε hε).normed_convolution_eq_right (μ := volume)
    (g := (selectorNeighborhood (2*ε) S).indicator (fun _ => (1:ℝ))) (x₀ := x) (by
      intro z hz
      have hz' : dist z x < ε := hz
      simp only [indicator_of_mem (hin z hz'), indicator_of_mem hxU])
  simpa only [neighborhoodSelector, smoothIndicator, indicator_of_mem hxU] using he

/-- Separation from the selected set gives a whole neighbourhood of value zero. -/
theorem neighborhoodSelector_eq_zero (ε : ℝ) (hε : 0 < ε) (S : Set ℝ)
    (y : ℝ) (hy : ∀ z ∈ S, 4*ε ≤ dist y z) (x : ℝ) (hx : dist x y < ε) :
    neighborhoodSelector ε hε S x = 0 := by
  have hout (z : ℝ) (hz : dist z x < ε) : z ∉ selectorNeighborhood (2*ε) S := by
    intro hzU
    obtain ⟨w,hw⟩ := mem_iUnion.mp hzU
    obtain ⟨hwS,hw⟩ := mem_iUnion.mp hw
    have hw' : dist z w < 2*ε := hw
    have hdist := dist_triangle y x w
    have hdist' := dist_triangle x z w
    rw [dist_comm y x] at hdist
    rw [dist_comm x z] at hdist'
    have hsep := hy w hwS
    linarith
  have hxU := hout x (by simpa using hε)
  have he := (selectorKernelBump ε hε).normed_convolution_eq_right (μ := volume)
    (g := (selectorNeighborhood (2*ε) S).indicator (fun _ => (1:ℝ))) (x₀ := x) (by
      intro z hz
      have hz' : dist z x < ε := hz
      simp only [indicator_of_notMem (hout z hz'), indicator_of_notMem hxU])
  simpa only [neighborhoodSelector, smoothIndicator, indicator_of_notMem hxU] using he

private theorem selectorKernelBump_scale (ε : ℝ) (hε : 0 < ε) (x : ℝ) :
    selectorKernelBump ε hε x = selectorKernelBump 1 zero_lt_one (ε⁻¹*x) := by
  rw [ContDiffBump.apply, ContDiffBump.apply]
  congr 1 <;> simp only [selectorKernelBump, smul_eq_mul, sub_zero] <;> field_simp

private theorem selectorKernelBump_integral (ε : ℝ) (hε : 0 < ε) :
    (∫ x : ℝ, selectorKernelBump ε hε x) = ε * ∫ x : ℝ, selectorKernelBump 1 zero_lt_one x := by
  simp_rw [selectorKernelBump_scale ε hε]
  rw [Measure.integral_comp_mul_left, inv_inv, abs_of_pos hε, smul_eq_mul]

theorem selectorKernel_scale (ε : ℝ) (hε : 0 < ε) (x : ℝ) :
    (selectorKernelBump ε hε).normed volume x =
      ε⁻¹ * (selectorKernelBump 1 zero_lt_one).normed volume (ε⁻¹*x) := by
  simp only [ContDiffBump.normed_def]
  rw [selectorKernelBump_scale ε hε, selectorKernelBump_integral ε hε]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

private theorem selectorKernel_derivative_scale (ε : ℝ) (hε : 0 < ε) (r : ℕ) (x : ℝ) :
    iteratedDeriv r ((selectorKernelBump ε hε).normed volume) x =
      ε⁻¹ * (ε⁻¹)^r * iteratedDeriv r ((selectorKernelBump 1 zero_lt_one).normed volume) (ε⁻¹*x) := by
  have he : (selectorKernelBump ε hε).normed volume =
      fun x => ε⁻¹ * (selectorKernelBump 1 zero_lt_one).normed volume (ε⁻¹*x) :=
    funext (selectorKernel_scale ε hε)
  have hcomp : ContDiff ℝ r (fun x : ℝ => (selectorKernelBump 1 zero_lt_one).normed volume (ε⁻¹*x)) :=
    (selectorKernelBump 1 zero_lt_one).contDiff_normed.comp (contDiff_const.mul contDiff_id)
  rw [he, iteratedDeriv_const_mul ε⁻¹ hcomp.contDiffAt,
    iteratedDeriv_comp_const_mul (selectorKernelBump 1 zero_lt_one).contDiff_normed]
  ring

/-- The same derivative constants work for every subset and every radius. -/
theorem neighborhoodSelector_scaled_derivative_bound (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ε : ℝ) (hε : 0 < ε) (S : Set ℝ) (x : ℝ),
      ‖iteratedDeriv r (neighborhoodSelector ε hε S) x‖ ≤ C * (ε⁻¹)^r := by
  let C : ℝ := ∫ t : ℝ, ‖iteratedDeriv r ((selectorKernelBump 1 zero_lt_one).normed volume) t‖
  refine ⟨C, integral_nonneg (fun _ => norm_nonneg _), ?_⟩
  intro ε hε S x
  have hb := smoothIndicator_derivative_bound ((selectorKernelBump ε hε).normed volume) (selectorKernelBump ε hε).hasCompactSupport_normed
    (selectorKernelBump ε hε).contDiff_normed _ (selectorNeighborhood_isOpen (2*ε) S).measurableSet r x
  apply hb.trans_eq
  simp_rw [selectorKernel_derivative_scale ε hε r, norm_mul,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hε), abs_of_nonneg (pow_nonneg (inv_pos.mpr hε).le r)]
  rw [integral_const_mul]
  have hI := Measure.integral_comp_mul_left
    (fun t : ℝ => |iteratedDeriv r ((selectorKernelBump 1 zero_lt_one).normed volume) t|) ε⁻¹
  simp only [inv_inv, abs_of_pos hε, smul_eq_mul] at hI
  rw [hI]
  change ε⁻¹ * ε⁻¹^r * (ε*C) = C*ε⁻¹^r
  field_simp

/-- Padded cells are wider than the compact partition support. -/
def selectorCell (S : Set ℝ) (n : ℤ) : Set ℝ := S ∩ Icc (-(n:ℝ)-2) (-(n:ℝ)+2)

/-- The cell-dependent smoothing radius, with the prescribed sixth-power decay. -/
def selectorRadius (σ : ℝ) (n : ℤ) : ℝ := σ / (4*5^6*(1+|(n:ℝ)|)^6)

theorem selectorRadius_pos (σ : ℝ) (hσ : 0 < σ) (n : ℤ) : 0 < selectorRadius σ n := by
  unfold selectorRadius
  positivity

/-- One smooth selector packet weighted by the integer partition of unity. -/
def selectorPacket (σ : ℝ) (hσ : 0 < σ) (S : Set ℝ) (n : ℤ) (x : ℝ) : ℝ :=
  unitPartition (x+n) * neighborhoodSelector (selectorRadius σ n) (selectorRadius_pos σ hσ n)
    (selectorCell S n) x

/-- The full locally finite partition construction. -/
def polynomialSelector (σ : ℝ) (hσ : 0 < σ) (S : Set ℝ) (x : ℝ) : ℝ :=
  ∑' n : ℤ, selectorPacket σ hσ S n x

private theorem selectorPacket_support (σ : ℝ) (hσ : 0 < σ) (S : Set ℝ) (n : ℤ)
    (x : ℝ) (hx : selectorPacket σ hσ S n x ≠ 0) : x+n ∈ Icc (-1) 1 := by
  apply unitPartition_support
  intro h
  apply hx
  simp only [selectorPacket, h, zero_mul]

theorem selectorPacket_contDiff (σ : ℝ) (hσ : 0 < σ) (S : Set ℝ) (n : ℤ) :
    ContDiff ℝ ∞ (selectorPacket σ hσ S n) :=
  (unitPartition_contDiff.comp (contDiff_id.add contDiff_const)).mul
    (neighborhoodSelector_contDiff _ _ _)

private theorem polynomialSelector_eventually_finite (σ : ℝ) (hσ : 0 < σ) (S : Set ℝ)
    (x : ℝ) : ∃ I : Finset ℤ,
      polynomialSelector σ hσ S =ᶠ[𝓝 x] fun y => ∑ n ∈ I, selectorPacket σ hσ S n y := by
  classical
  obtain ⟨N:ℕ,hN⟩ := exists_nat_gt (|x|+3)
  let I : Finset ℤ := Finset.Icc (-(N:ℤ)) (N:ℤ)
  refine ⟨I, ?_⟩
  filter_upwards [Ioo_mem_nhds (by linarith : x-1<x) (by linarith : x<x+1)] with y hy
  apply tsum_eq_sum
  intro n hn
  by_contra hne
  obtain ⟨hlo,hhi⟩ := selectorPacket_support σ hσ S n y hne
  have ha := neg_abs_le x
  have hb := le_abs_self x
  have hlo' : -(N:ℤ) ≤ n := by exact_mod_cast (by linarith [hy.2] : -(N:ℝ) ≤ (n:ℝ))
  have hhi' : n ≤ (N:ℤ) := by exact_mod_cast (by linarith [hy.1] : (n:ℝ) ≤ (N:ℝ))
  exact hn (Finset.mem_Icc.mpr ⟨hlo',hhi'⟩)

theorem polynomialSelector_contDiff (σ : ℝ) (hσ : 0 < σ) (S : Set ℝ) :
    ContDiff ℝ ∞ (polynomialSelector σ hσ S) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  obtain ⟨I, hI⟩ := polynomialSelector_eventually_finite σ hσ S x
  exact (ContDiff.sum (s := I) fun n _ => selectorPacket_contDiff σ hσ S n).contDiffAt.congr_of_eventuallyEq hI

/-- Exact selected values hold for the full selector. -/
theorem polynomialSelector_eq_one (σ : ℝ) (hσ : 0 < σ) (S : Set ℝ) (x : ℝ) (hx : x ∈ S) :
    polynomialSelector σ hσ S x = 1 := by
  rw [polynomialSelector, ← unitPartition_sum x]
  apply tsum_congr
  intro n
  by_cases hn : unitPartition (x+n) = 0
  · simp only [selectorPacket, hn, zero_mul]
  · have hh := unitPartition_support hn
    have hcell : x ∈ selectorCell S n := ⟨hx, by constructor <;> linarith [hh.1,hh.2]⟩
    rw [selectorPacket, neighborhoodSelector_eq_one _ _ _ x hcell x (by simpa using selectorRadius_pos σ hσ n), mul_one]

private theorem selectorCell_distance (σ : ℝ) (hσ : 0 < σ) (S T : Set ℝ)
    (hsep : ∀ x ∈ S, ∀ y ∈ T, σ/(1+|x|+|y|)^6 ≤ |x-y|)
    (n : ℤ) (y : ℝ) (hy : y ∈ T) (hyn : |y+n| ≤ 2) :
    ∀ z ∈ selectorCell S n, 4*selectorRadius σ n ≤ dist y z := by
  intro z hz
  have hzn : |z+n| ≤ 2 := by rw [abs_le]; constructor <;> linarith [hz.2.1,hz.2.2]
  have hza : |z| ≤ 2+|(n:ℝ)| := by
    have hh : |z| ≤ |z+n|+|(n:ℝ)| := by simpa [Real.norm_eq_abs] using norm_add_le (z+n) (-(n:ℝ))
    linarith
  have hya : |y| ≤ 2+|(n:ℝ)| := by
    have hh : |y| ≤ |y+n|+|(n:ℝ)| := by simpa [Real.norm_eq_abs] using norm_add_le (y+n) (-(n:ℝ))
    linarith
  have hbase : 1+|z|+|y| ≤ 5*(1+|(n:ℝ)|) := by linarith [abs_nonneg (n:ℝ)]
  have hp : (1+|z|+|y|)^6 ≤ 5^6*(1+|(n:ℝ)|)^6 := by
    calc
      _ ≤ (5*(1+|(n:ℝ)|))^6 := pow_le_pow_left₀ (by positivity) hbase 6
      _ = _ := mul_pow _ _ _
  have hh : σ/(5^6*(1+|(n:ℝ)|)^6) ≤ σ/(1+|z|+|y|)^6 :=
    div_le_div_of_nonneg_left hσ.le (by positivity) hp
  have he : 4*selectorRadius σ n = σ/(5^6*(1+|(n:ℝ)|)^6) := by
    unfold selectorRadius
    field_simp
  rw [he, Real.dist_eq, abs_sub_comm]
  exact hh.trans (hsep z hz.1 y hy)

/-- Correct excluded values under actual polynomial cross-set separation. -/
theorem polynomialSelector_eq_zero (σ : ℝ) (hσ : 0 < σ) (S T : Set ℝ)
    (hsep : ∀ x ∈ S, ∀ y ∈ T, σ/(1+|x|+|y|)^6 ≤ |x-y|)
    (x : ℝ) (hx : x ∈ T) : polynomialSelector σ hσ S x = 0 := by
  change (∑' n : ℤ, selectorPacket σ hσ S n x) = 0
  suffices hh : ∀ n : ℤ, selectorPacket σ hσ S n x = 0 by simp only [hh, tsum_zero]
  intro n
  by_cases hn : unitPartition (x+n) = 0
  · simp only [selectorPacket, hn, zero_mul]
  · have hh := unitPartition_support hn
    have hxn : |x+n| ≤ 2 := by rw [abs_le]; constructor <;> linarith [hh.1,hh.2]
    rw [selectorPacket, neighborhoodSelector_eq_zero _ _ _ x
      (selectorCell_distance σ hσ S T hsep n x hx hxn) x
      (by simpa using selectorRadius_pos σ hσ n), mul_zero]

private theorem polynomialSelector_five_term_local (σ : ℝ) (hσ : 0 < σ)
    (x : ℝ) : ∃ I : Finset ℤ, I.card = 5 ∧ (∀ n ∈ I, |(n:ℝ)| ≤ |x|+3) ∧
      ∀ S : Set ℝ, polynomialSelector σ hσ S =ᶠ[𝓝 x] fun y => ∑ n ∈ I, selectorPacket σ hσ S n y := by
  classical
  let N : ℤ := ⌊-x⌋
  let I : Finset ℤ := Finset.Icc (N-2) (N+2)
  have hlo := Int.floor_le (-x)
  have hhi := Int.lt_floor_add_one (-x)
  change (N:ℝ) ≤ -x at hlo
  change -x < (N:ℝ)+1 at hhi
  refine ⟨I, ?_, ?_, ?_⟩
  · simp only [I, Int.card_Icc]
    omega
  · intro n hn
    obtain ⟨hnl,hnh⟩ := Finset.mem_Icc.mp hn
    have hnl' : (N:ℝ)-2 ≤ n := by exact_mod_cast hnl
    have hnh' : (n:ℝ) ≤ N+2 := by exact_mod_cast hnh
    rw [abs_le]
    constructor <;> linarith [le_abs_self x, neg_abs_le x]
  · intro S
    filter_upwards [Ioo_mem_nhds (by linarith : x-1/2<x) (by linarith : x<x+1/2)] with y hy
    apply tsum_eq_sum
    intro n hn
    by_contra hne
    obtain ⟨ha,hb⟩ := selectorPacket_support σ hσ S n y hne
    have hnl : N-2 ≤ n := by exact_mod_cast (by linarith [hy.2] : (N:ℝ)-2 ≤ n)
    have hnh : n ≤ N+2 := by
      have hh : (n:ℝ) < N+3 := by linarith [hy.1]
      have hh' : n < N+3 := by exact_mod_cast hh
      omega
    exact hn (Finset.mem_Icc.mpr ⟨hnl,hnh⟩)

private theorem selectorRadius_inverse_power (σ : ℝ) (hσ : 0 < σ) (n : ℤ)
    (x : ℝ) (hn : |(n:ℝ)| ≤ |x|+3) (s r : ℕ) (hs : s ≤ r) :
    (selectorRadius σ n)⁻¹^s ≤
      (4*5^6/σ)^s * 4^(6*s) * (1+|x|)^(6*r) := by
  have he : (selectorRadius σ n)⁻¹ = (4*5^6/σ)*(1+|(n:ℝ)|)^6 := by
    unfold selectorRadius
    rw [inv_div]
    ring
  rw [he, mul_pow, ← pow_mul]
  have hbase : 1+|(n:ℝ)| ≤ 4*(1+|x|) := by linarith [abs_nonneg x]
  have hp : (1+|(n:ℝ)|)^(6*s) ≤ 4^(6*s)*(1+|x|)^(6*r) := by
    calc
      _ ≤ (4*(1+|x|))^(6*s) := pow_le_pow_left₀ (by positivity) hbase _
      _ = 4^(6*s)*(1+|x|)^(6*s) := mul_pow _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ (by linarith [abs_nonneg x]) (by omega)) (by positivity)
  exact (mul_le_mul_of_nonneg_left hp (by positivity)).trans_eq (by ring)

private theorem selectorPacket_local_derivative_bound (σ : ℝ) (hσ : 0 < σ) (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (S : Set ℝ) (n : ℤ) (x : ℝ), |(n:ℝ)| ≤ |x|+3 →
      ‖iteratedDeriv r (selectorPacket σ hσ S n) x‖ ≤ C*(1+|x|)^(6*r) := by
  classical
  choose A hA hAbound using neighborhoodSelector_scaled_derivative_bound
  have hd (j : ℕ) := (compact_iteratedDeriv unitPartition unitPartition_hasCompactSupport j).exists_bound_of_continuous
    (smooth_iteratedDeriv unitPartition unitPartition_contDiff j).continuous
  choose D hD using hd
  have hD0 (j : ℕ) : 0 ≤ D j := (norm_nonneg _).trans (hD j 0)
  let C : ℝ := ∑ j ∈ Finset.range (r+1),
    (r.choose j:ℝ)*D j*A (r-j)*(4*5^6/σ)^(r-j)*4^(6*(r-j))
  refine ⟨C, Finset.sum_nonneg (fun j hj => by
    have := hD0 j
    have := hA (r-j)
    positivity), ?_⟩
  intro S n x hn
  have hχ := neighborhoodSelector_contDiff (selectorRadius σ n) (selectorRadius_pos σ hσ n) (selectorCell S n)
  have hφ : ContDiff ℝ ∞ (fun y : ℝ => unitPartition (y+n)) :=
    unitPartition_contDiff.comp (contDiff_id.add contDiff_const)
  change ‖iteratedDeriv r ((fun y : ℝ => unitPartition (y+n)) *
    neighborhoodSelector (selectorRadius σ n) (selectorRadius_pos σ hσ n) (selectorCell S n)) x‖ ≤ _
  rw [iteratedDeriv_mul (hφ.of_le (by simp)).contDiffAt (hχ.of_le (by simp)).contDiffAt]
  apply (norm_sum_le _ _).trans
  rw [show C*(1+|x|)^(6*r) = ∑ j ∈ Finset.range (r+1),
      ((r.choose j:ℝ)*D j*A (r-j)*(4*5^6/σ)^(r-j)*4^(6*(r-j)))*(1+|x|)^(6*r) by
    simp only [C, Finset.sum_mul]]
  apply Finset.sum_le_sum
  intro j hj
  have hjr : j ≤ r := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj
  simp only [norm_mul, Real.norm_natCast, iteratedDeriv_comp_add_const]
  have hb := hAbound (r-j) (selectorRadius σ n) (selectorRadius_pos σ hσ n) (selectorCell S n) x
  have hp := selectorRadius_inverse_power σ hσ n x hn (r-j) r (by omega)
  calc
    _ ≤ (r.choose j:ℝ) * D j * (A (r-j) * (selectorRadius σ n)⁻¹^(r-j)) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hD j (x+n)) (by positivity))
        hb (norm_nonneg _) (mul_nonneg (by positivity) (hD0 j))
    _ ≤ (r.choose j:ℝ) * D j *
        (A (r-j) * ((4*5^6/σ)^(r-j)*4^(6*(r-j))*(1+|x|)^(6*r))) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp (hA (r-j)))
        (mul_nonneg (by positivity) (hD0 j))
    _ = _ := by ring

/-- Global derivative growth with constants independent of the chosen subset. -/
theorem polynomialSelector_derivative_bound (σ : ℝ) (hσ : 0 < σ) (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (S : Set ℝ) (x : ℝ),
      ‖iteratedDeriv r (polynomialSelector σ hσ S) x‖ ≤ C*(1+|x|)^(6*r) := by
  classical
  obtain ⟨C,hC,hbound⟩ := selectorPacket_local_derivative_bound σ hσ r
  refine ⟨5*C, by positivity, ?_⟩
  intro S x
  obtain ⟨I,hcard,hI,hEq⟩ := polynomialSelector_five_term_local σ hσ x
  rw [(hEq S).iteratedDeriv_eq r]
  rw [iteratedDeriv_fun_sum (fun n hn => ((selectorPacket_contDiff σ hσ S n).of_le (by simp)).contDiffAt)]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ n ∈ I, C*(1+|x|)^(6*r) :=
      Finset.sum_le_sum fun n hn => hbound S n x (hI n hn)
    _ = (5*C)*(1+|x|)^(6*r) := by simp only [Finset.sum_const,hcard,nsmul_eq_mul]; ring

private theorem partition_shift_eventually_zero (x : ℝ) (n : ℤ) (h : ¬|x+n| ≤ 2) :
    (fun y : ℝ => unitPartition (y+n)) =ᶠ[𝓝 x] fun _ => 0 := by
  have h' : 2 < |x+n| := lt_of_not_ge h
  filter_upwards [Ioo_mem_nhds (by linarith : x-1/2<x) (by linarith : x<x+1/2)] with y hy
  by_contra hn
  have hh := unitPartition_support hn
  apply h
  rw [abs_le]
  constructor <;> linarith [hy.1,hy.2,hh.1,hh.2]

private theorem selectorPacket_near_selected (σ : ℝ) (hσ : 0 < σ) (S : Set ℝ)
    (x : ℝ) (hx : x ∈ S) (n : ℤ) :
    selectorPacket σ hσ S n =ᶠ[𝓝 x] fun y => unitPartition (y+n) := by
  by_cases hn : |x+n| ≤ 2
  · have hcell : x ∈ selectorCell S n := ⟨hx, by
      obtain ⟨ha,hb⟩ := abs_le.mp hn
      constructor <;> linarith⟩
    filter_upwards [Metric.ball_mem_nhds x (selectorRadius_pos σ hσ n)] with y hy
    rw [selectorPacket, neighborhoodSelector_eq_one _ _ _ x hcell y hy, mul_one]
  · filter_upwards [partition_shift_eventually_zero x n hn] with y hy
    simp only [selectorPacket, hy, zero_mul]

private theorem selectorPacket_near_excluded (σ : ℝ) (hσ : 0 < σ) (S T : Set ℝ)
    (hsep : ∀ x ∈ S, ∀ y ∈ T, σ/(1+|x|+|y|)^6 ≤ |x-y|)
    (x : ℝ) (hx : x ∈ T) (n : ℤ) :
    selectorPacket σ hσ S n =ᶠ[𝓝 x] fun _ => 0 := by
  by_cases hn : |x+n| ≤ 2
  · filter_upwards [Metric.ball_mem_nhds x (selectorRadius_pos σ hσ n)] with y hy
    rw [selectorPacket, neighborhoodSelector_eq_zero _ _ _ x
      (selectorCell_distance σ hσ S T hsep n x hx hn) y hy, mul_zero]
  · filter_upwards [partition_shift_eventually_zero x n hn] with y hy
    simp only [selectorPacket, hy, zero_mul]

/-- The selector equals one on a neighbourhood of every selected point. -/
theorem polynomialSelector_near_selected (σ : ℝ) (hσ : 0 < σ) (S : Set ℝ)
    (x : ℝ) (hx : x ∈ S) : polynomialSelector σ hσ S =ᶠ[𝓝 x] fun _ => 1 := by
  classical
  obtain ⟨I,_,_,hI⟩ := polynomialSelector_five_term_local σ hσ x
  have hS := (I.eventually_all).mpr (fun n hn => selectorPacket_near_selected σ hσ S x hx n)
  have hU := (I.eventually_all).mpr (fun n hn => selectorPacket_near_selected σ hσ univ x (mem_univ _) n)
  filter_upwards [hI S,hI univ,hS,hU] with y hyS hyU hySn hyUn
  rw [hyS, ← polynomialSelector_eq_one σ hσ univ y (mem_univ _), hyU]
  apply Finset.sum_congr rfl
  intro n hn
  rw [hySn n hn,hyUn n hn]

/-- The selector equals zero near every point in the separated complementary set. -/
theorem polynomialSelector_near_excluded (σ : ℝ) (hσ : 0 < σ) (S T : Set ℝ)
    (hsep : ∀ x ∈ S, ∀ y ∈ T, σ/(1+|x|+|y|)^6 ≤ |x-y|)
    (x : ℝ) (hx : x ∈ T) : polynomialSelector σ hσ S =ᶠ[𝓝 x] fun _ => 0 := by
  classical
  obtain ⟨I,_,_,hI⟩ := polynomialSelector_five_term_local σ hσ x
  have hS := (I.eventually_all).mpr (fun n hn => selectorPacket_near_excluded σ hσ S T hsep x hx n)
  filter_upwards [hI S,hS] with y hyS hySn
  rw [hyS]
  apply Finset.sum_eq_zero
  exact hySn

/-- Temperate growth follows from the constructed bounds at every derivative order. -/
theorem polynomialSelector_hasTemperateGrowth (σ : ℝ) (hσ : 0 < σ) (S : Set ℝ) :
    (polynomialSelector σ hσ S).HasTemperateGrowth := by
  refine ⟨polynomialSelector_contDiff σ hσ S, ?_⟩
  intro r
  obtain ⟨C,_,hC⟩ := polynomialSelector_derivative_bound σ hσ r
  refine ⟨6*r,C,fun x => ?_⟩
  simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] using hC S x

/-- Complex-valued multiplier used by the original distribution interface. -/
def complexPolynomialSelector (σ : ℝ) (hσ : 0 < σ) (S : Set ℝ) (x : ℝ) : ℂ :=
  polynomialSelector σ hσ S x

private theorem complex_iteratedDeriv (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (r : ℕ) :
    iteratedDeriv r (fun x => (f x : ℂ)) = fun x => Complex.ofReal (iteratedDeriv r f x) := by
  induction r with
  | zero => simp only [iteratedDeriv_zero]
  | succ r ih =>
      rw [iteratedDeriv_succ, ih, iteratedDeriv_succ]
      funext x
      have hd : HasDerivAt (iteratedDeriv r f) (deriv (iteratedDeriv r f) x) x :=
        ((smooth_iteratedDeriv f hf r).differentiable (by simp)).differentiableAt.hasDerivAt
      exact (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x hd).deriv

theorem complexPolynomialSelector_hasTemperateGrowth (σ : ℝ) (hσ : 0 < σ) (S : Set ℝ) :
    (complexPolynomialSelector σ hσ S).HasTemperateGrowth :=
  Complex.ofRealCLM.hasTemperateGrowth.comp (polynomialSelector_hasTemperateGrowth σ hσ S)

/-- All subsets share one set of derivative constants. -/
theorem complexPolynomialSelector_derivative_bound (σ : ℝ) (hσ : 0 < σ) (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (S : Set ℝ) (x : ℝ),
      ‖iteratedDeriv r (complexPolynomialSelector σ hσ S) x‖ ≤ C*(1+|x|)^(6*r) := by
  obtain ⟨C,hC,hbound⟩ := polynomialSelector_derivative_bound σ hσ r
  refine ⟨C,hC,fun S x => ?_⟩
  change ‖iteratedDeriv r (fun y => (polynomialSelector σ hσ S y : ℂ)) x‖ ≤ _
  rw [complex_iteratedDeriv _ (polynomialSelector_contDiff σ hσ S), Complex.norm_real]
  exact hbound S x

/-- The constructed selectors, with no derivative-bound premise, define actual
whole-distribution multipliers in the prescribed native order. -/
theorem complexPolynomialSelector_native_realizes (σ : ℝ) (hσ : 0 < σ)
    (p : ℕ) (S : Set ℝ) (T : HermiteScale (-(p:ℤ))) :
    hermiteScaleDistribution (6*p) (nativeMultiplier p (6*p) (complexPolynomialSelector σ hσ S) T) =
      TemperedDistribution.smulLeftCLM ℂ (complexPolynomialSelector σ hσ S) (hermiteScaleDistribution p T) := by
  choose C hC hbound using complexPolynomialSelector_derivative_bound σ hσ
  exact nativeMultiplier_selector_six_growth_realizes p C _
    (complexPolynomialSelector_hasTemperateGrowth σ hσ S) (fun r hr x => hbound r S x) T

/-- Uniform original operator norm, independent of every selected subset. -/
theorem exists_complexPolynomialSelector_native_norm_bound (σ : ℝ) (hσ : 0 < σ) (p : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ S : Set ℝ,
      ‖nativeMultiplier p (6*p) (complexPolynomialSelector σ hσ S)‖ ≤ B := by
  choose C hC hbound using complexPolynomialSelector_derivative_bound σ hσ
  obtain ⟨B,hB,hb⟩ := exists_nativeMultiplier_selector_six_growth_norm_bound p C
  exact ⟨B,hB,fun S => hb _ (complexPolynomialSelector_hasTemperateGrowth σ hσ S)
    (fun r hr x => hbound r S x)⟩

/-- The complete actual union belonging to an arbitrary subset of labels. -/
def selectedSectorUnion (R : ℕ+ → ℕ) (s : ℕ+ → ℝ) (E : Set Label) : Set ℝ :=
  ⋃ b ∈ E, sectorSet R s b

/-- The actual constructed complex selector for a labelled subfamily. -/
def actualSectorSelector (σ : ℝ) (hσ : 0 < σ) (R : ℕ+ → ℕ) (s : ℕ+ → ℝ)
    (E : Set Label) : ℝ → ℂ := complexPolynomialSelector σ hσ (selectedSectorUnion R s E)

theorem actualSectorSelector_hasTemperateGrowth (σ : ℝ) (hσ : 0 < σ)
    (R : ℕ+ → ℕ) (s : ℕ+ → ℝ) (E : Set Label) :
    (actualSectorSelector σ hσ R s E).HasTemperateGrowth :=
  complexPolynomialSelector_hasTemperateGrowth σ hσ _

/-- Near every selected actual atom the full selector is exactly one. -/
theorem actualSectorSelector_near_selected (σ : ℝ) (hσ : 0 < σ)
    (R : ℕ+ → ℕ) (s : ℕ+ → ℝ) (E : Set Label) (b : Label) (hb : b ∈ E)
    (x : ℝ) (hx : x ∈ sectorSet R s b) :
    actualSectorSelector σ hσ R s E =ᶠ[𝓝 x] fun _ => (1:ℂ) := by
  have hxS : x ∈ selectedSectorUnion R s E := mem_iUnion.mpr ⟨b,mem_iUnion.mpr ⟨hb,hx⟩⟩
  filter_upwards [polynomialSelector_near_selected σ hσ _ x hxS] with y hy
  simp only [actualSectorSelector,complexPolynomialSelector,hy,Complex.ofReal_one]

/-- Under the actual separation estimate, the selector is zero near every
atom with an unselected label, including an arbitrary infinite complement. -/
theorem actualSectorSelector_near_excluded (σ : ℝ) (hσ : 0 < σ)
    (R : ℕ+ → ℕ) (s : ℕ+ → ℝ)
    (hsep : ∀ b d : Label, b ≠ d → ∀ x ∈ sectorSet R s b,
      ∀ y ∈ sectorSet R s d, σ/(1+|x|+|y|)^6 ≤ |x-y|)
    (E : Set Label) (b : Label) (hb : b ∉ E) (x : ℝ) (hx : x ∈ sectorSet R s b) :
    actualSectorSelector σ hσ R s E =ᶠ[𝓝 x] fun _ => (0:ℂ) := by
  have hs : ∀ y ∈ selectedSectorUnion R s E, ∀ z ∈ sectorSet R s b,
      σ/(1+|y|+|z|)^6 ≤ |y-z| := by
    intro y hy z hz
    obtain ⟨d,hd⟩ := mem_iUnion.mp hy
    obtain ⟨hdE,hd⟩ := mem_iUnion.mp hd
    exact hsep d b (by intro he; subst d; exact hb hdE) y hd z hz
  filter_upwards [polynomialSelector_near_excluded σ hσ _ _ hs x hx] with y hy
  simp only [actualSectorSelector,complexPolynomialSelector,hy,Complex.ofReal_zero]

/-- Uniform native control before the subset of actual labels is selected. -/
theorem exists_actualSectorSelector_native_norm_bound (σ : ℝ) (hσ : 0 < σ)
    (p : ℕ) : ∃ B : ℝ, 0 < B ∧ ∀ (R : ℕ+ → ℕ) (s : ℕ+ → ℝ) (E : Set Label),
      ‖nativeMultiplier p (6*p) (actualSectorSelector σ hσ R s E)‖ ≤ B := by
  obtain ⟨B,hB,hbound⟩ := exists_complexPolynomialSelector_native_norm_bound σ hσ p
  exact ⟨B,hB,fun R s E => hbound _⟩

theorem actualSectorSelector_native_realizes (σ : ℝ) (hσ : 0 < σ)
    (p : ℕ) (R : ℕ+ → ℕ) (s : ℕ+ → ℝ) (E : Set Label) (T : HermiteScale (-(p:ℤ))) :
    hermiteScaleDistribution (6*p) (nativeMultiplier p (6*p) (actualSectorSelector σ hσ R s E) T) =
      TemperedDistribution.smulLeftCLM ℂ (actualSectorSelector σ hσ R s E) (hermiteScaleDistribution p T) :=
  complexPolynomialSelector_native_realizes σ hσ p _ T

/-- Whole Schwartz annihilation proves independence of the chosen selector. -/
theorem atomic_multiplier_eq_of_eqOn (L : LocallyFiniteCarrier) (U : TemperedDistribution ℝ ℂ)
    (hU : AtomicOnCarrier L U) (χ ψ : ℝ → ℂ)
    (hχ : χ.HasTemperateGrowth) (hψ : ψ.HasTemperateGrowth)
    (heq : ∀ x ∈ L.carrier, χ x = ψ x) :
    TemperedDistribution.smulLeftCLM ℂ χ U = TemperedDistribution.smulLeftCLM ℂ ψ U := by
  ext f
  simp only [TemperedDistribution.smulLeftCLM_apply_apply]
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply hU
  intro x hx
  simp only [_root_.sub_apply, SchwartzMap.smulLeftCLM_apply_apply hχ,
    SchwartzMap.smulLeftCLM_apply_apply hψ, heq x hx, sub_self]

/-- The same independence holds from the independently defined local value-only action. -/
theorem locally_atomic_multiplier_eq_of_eqOn (L : LocallyFiniteCarrier)
    (U : TemperedDistribution ℝ ℂ) (hU : HasLocallyAtomicAction L U)
    (χ ψ : ℝ → ℂ) (hχ : χ.HasTemperateGrowth) (hψ : ψ.HasTemperateGrowth)
    (heq : ∀ x ∈ L.carrier, χ x = ψ x) :
    TemperedDistribution.smulLeftCLM ℂ χ U = TemperedDistribution.smulLeftCLM ℂ ψ U :=
  atomic_multiplier_eq_of_eqOn L U (hasLocallyAtomicAction_atomicOnCarrier L U hU) χ ψ hχ hψ heq

/-- Multiplication by a selector produces an actual value-only restricted source. -/
theorem atomic_multiplier_restrict (L : LocallyFiniteCarrier) (U : TemperedDistribution ℝ ℂ)
    (hU : AtomicOnCarrier L U) (A : Set ℝ) (hA : A ⊆ L.carrier)
    (χ : ℝ → ℂ) (hχ : χ.HasTemperateGrowth)
    (hz : ∀ x ∈ L.carrier, x ∉ A → χ x = 0) :
    AtomicOnCarrier (L.restrict A hA) (TemperedDistribution.smulLeftCLM ℂ χ U) := by
  intro f hf
  rw [TemperedDistribution.smulLeftCLM_apply_apply]
  apply hU
  intro x hx
  rw [SchwartzMap.smulLeftCLM_apply_apply hχ]
  by_cases ha : x ∈ A
  · rw [hf x ha, smul_zero]
  · rw [hz x hx ha, zero_smul]

/-- Complementary pointwise selectors split the complete original source. -/
theorem atomic_multiplier_split (L : LocallyFiniteCarrier) (U : TemperedDistribution ℝ ℂ)
    (hU : AtomicOnCarrier L U) (χ ψ : ℝ → ℂ)
    (hχ : χ.HasTemperateGrowth) (hψ : ψ.HasTemperateGrowth)
    (heq : ∀ x ∈ L.carrier, χ x + ψ x = 1) :
    TemperedDistribution.smulLeftCLM ℂ χ U + TemperedDistribution.smulLeftCLM ℂ ψ U = U := by
  ext f
  simp only [_root_.add_apply, TemperedDistribution.smulLeftCLM_apply_apply]
  apply sub_eq_zero.mp
  rw [← map_add, ← map_sub]
  apply hU
  intro x hx
  simp only [_root_.sub_apply, _root_.add_apply, SchwartzMap.smulLeftCLM_apply_apply hχ,
    SchwartzMap.smulLeftCLM_apply_apply hψ, smul_eq_mul]
  rw [← add_mul, heq x hx, one_mul, sub_self]

/-- Selected and complementary label multipliers give an exact whole-source decomposition. -/
theorem actualSectorSelector_atomic_split (σ : ℝ) (hσ : 0 < σ)
    (R : ℕ+ → ℕ) (s : ℕ+ → ℝ)
    (hsep : ∀ b d : Label, b ≠ d → ∀ x ∈ sectorSet R s b,
      ∀ y ∈ sectorSet R s d, σ/(1+|x|+|y|)^6 ≤ |x-y|)
    (L : LocallyFiniteCarrier) (hL : L.carrier ⊆ selectedSectorUnion R s univ)
    (U : TemperedDistribution ℝ ℂ) (hU : AtomicOnCarrier L U) (E : Set Label) :
    TemperedDistribution.smulLeftCLM ℂ (actualSectorSelector σ hσ R s E) U +
      TemperedDistribution.smulLeftCLM ℂ (actualSectorSelector σ hσ R s Eᶜ) U = U := by
  apply atomic_multiplier_split L U hU _ _
    (actualSectorSelector_hasTemperateGrowth σ hσ R s E)
    (actualSectorSelector_hasTemperateGrowth σ hσ R s Eᶜ)
  intro x hx
  obtain ⟨b,hb⟩ := mem_iUnion.mp (hL hx)
  obtain ⟨_,hb⟩ := mem_iUnion.mp hb
  by_cases he : b ∈ E
  · rw [(actualSectorSelector_near_selected σ hσ R s E b he x hb).eq_of_nhds,
      (actualSectorSelector_near_excluded σ hσ R s hsep Eᶜ b (by simpa) x hb).eq_of_nhds]
    simp
  · rw [(actualSectorSelector_near_excluded σ hσ R s hsep E b he x hb).eq_of_nhds,
      (actualSectorSelector_near_selected σ hσ R s Eᶜ b he x hb).eq_of_nhds]
    simp

/-- The selected whole distribution is genuinely value-only on the selected carrier. -/
theorem actualSectorSelector_atomic_restrict (σ : ℝ) (hσ : 0 < σ)
    (R : ℕ+ → ℕ) (s : ℕ+ → ℝ)
    (hsep : ∀ b d : Label, b ≠ d → ∀ x ∈ sectorSet R s b,
      ∀ y ∈ sectorSet R s d, σ/(1+|x|+|y|)^6 ≤ |x-y|)
    (L : LocallyFiniteCarrier) (hL : L.carrier ⊆ selectedSectorUnion R s univ)
    (U : TemperedDistribution ℝ ℂ) (hU : AtomicOnCarrier L U) (E : Set Label) :
    AtomicOnCarrier (L.restrict (L.carrier ∩ selectedSectorUnion R s E) inter_subset_left)
      (TemperedDistribution.smulLeftCLM ℂ (actualSectorSelector σ hσ R s E) U) := by
  apply atomic_multiplier_restrict L U hU _ inter_subset_left _
    (actualSectorSelector_hasTemperateGrowth σ hσ R s E)
  intro x hx hnot
  obtain ⟨b,hb⟩ := mem_iUnion.mp (hL hx)
  obtain ⟨_,hb⟩ := mem_iUnion.mp hb
  have hbE : b ∉ E := by
    intro hbe
    exact hnot ⟨hx,mem_iUnion.mpr ⟨b,mem_iUnion.mpr ⟨hbe,hb⟩⟩⟩
  exact (actualSectorSelector_near_excluded σ hσ R s hsep E b hbE x hb).eq_of_nhds

end
end MeyerGeneralProblem.Adaptive
