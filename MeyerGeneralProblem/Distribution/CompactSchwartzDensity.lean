module

public import MeyerGeneralProblem.Distribution.AtomicOnCarrier
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import all Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.SpecificLimits.Basic
import all Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-!
# Compactly supported cutoff approximation in Schwartz space

A fixed smooth bump equal to one on the unit ball is dilated through the
radii `N + 1`.  Multiplication by these dilates preserves carrier zeros and
compactly supports every Schwartz test.  The derivative scaling formula,
Leibniz rule, and one additional power of Schwartz decay prove convergence
in every defining Schwartz seminorm.
-/

open Filter
open scoped ContDiff SchwartzMap Topology

namespace MeyerGeneralProblem

noncomputable section

/-- The fixed real bump underlying the expanding cutoffs. -/
def compactSchwartzCutoffBump : ContDiffBump (0 : ℝ) where
  rIn := 1
  rOut := 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- A compactly supported complex Schwartz cutoff equal to one on the unit
interval. -/
def compactSchwartzCutoff : SchwartzMap ℝ ℂ := by
  let b := compactSchwartzCutoffBump
  let g : ℝ → ℂ := Complex.ofRealCLM ∘ b
  have hgSupport : HasCompactSupport g :=
    b.hasCompactSupport.comp_left rfl
  have hgSmooth : ContDiff ℝ ∞ g :=
    Complex.ofRealCLM.contDiff.comp b.contDiff
  exact hgSupport.toSchwartzMap hgSmooth

@[simp]
theorem compactSchwartzCutoff_apply (x : ℝ) :
    compactSchwartzCutoff x = (compactSchwartzCutoffBump x : ℂ) :=
  rfl

theorem compactSchwartzCutoff_hasCompactSupport :
    HasCompactSupport compactSchwartzCutoff := by
  change HasCompactSupport
    (fun x : ℝ => (compactSchwartzCutoffBump x : ℂ))
  exact compactSchwartzCutoffBump.hasCompactSupport.comp_left
    (show ((0 : ℝ) : ℂ) = 0 by norm_num)

theorem compactSchwartzCutoff_eq_one {x : ℝ} (hx : |x| ≤ 1) :
    compactSchwartzCutoff x = 1 := by
  rw [compactSchwartzCutoff_apply]
  rw [compactSchwartzCutoffBump.one_of_mem_closedBall]
  · norm_num
  · simpa [Metric.mem_closedBall, Real.dist_eq,
      compactSchwartzCutoffBump] using hx

theorem norm_compactSchwartzCutoff_le_one (x : ℝ) :
    ‖compactSchwartzCutoff x‖ ≤ 1 := by
  rw [compactSchwartzCutoff_apply, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg compactSchwartzCutoffBump.nonneg]
  exact compactSchwartzCutoffBump.le_one

/-- Reciprocal dilation factor for the cutoff of radius `N + 1`. -/
def compactSchwartzCutoffScale (N : ℕ) : ℝ :=
  ((N : ℝ) + 1)⁻¹

theorem compactSchwartzCutoffScale_pos (N : ℕ) :
    0 < compactSchwartzCutoffScale N := by
  simp only [compactSchwartzCutoffScale]
  positivity

theorem compactSchwartzCutoffScale_le_one (N : ℕ) :
    compactSchwartzCutoffScale N ≤ 1 := by
  exact (inv_le_one₀ (by positivity : (0 : ℝ) < (N : ℝ) + 1)).2 (by norm_num)

/-- The unbundled fixed cutoff dilated to radius `N + 1`. -/
def scaledCompactSchwartzCutoffFunction (N : ℕ) (x : ℝ) : ℂ :=
  compactSchwartzCutoff (compactSchwartzCutoffScale N * x)

theorem scaledCompactSchwartzCutoffFunction_hasCompactSupport (N : ℕ) :
    HasCompactSupport (scaledCompactSchwartzCutoffFunction N) := by
  let c := compactSchwartzCutoffScale N
  have hc : c ≠ 0 := (compactSchwartzCutoffScale_pos N).ne'
  change HasCompactSupport
    (fun x : ℝ => compactSchwartzCutoff
      (compactSchwartzCutoffScale N * x))
  simpa only [c, Function.comp_def, Homeomorph.coe_mulLeft₀] using
    compactSchwartzCutoff_hasCompactSupport.comp_homeomorph
      (Homeomorph.mulLeft₀ c hc)

theorem scaledCompactSchwartzCutoffFunction_contDiff (N : ℕ) :
    ContDiff ℝ ∞ (scaledCompactSchwartzCutoffFunction N) := by
  exact (compactSchwartzCutoff.smooth ⊤).comp
    (contDiff_const.mul contDiff_id)

/-- The fixed cutoff dilated to be one on `[-(N+1), N+1]`. -/
def scaledCompactSchwartzCutoff (N : ℕ) : SchwartzMap ℝ ℂ :=
  (scaledCompactSchwartzCutoffFunction_hasCompactSupport N).toSchwartzMap
    (scaledCompactSchwartzCutoffFunction_contDiff N)

@[simp]
theorem scaledCompactSchwartzCutoff_apply (N : ℕ) (x : ℝ) :
    scaledCompactSchwartzCutoff N x =
      compactSchwartzCutoff (compactSchwartzCutoffScale N * x) :=
  rfl

theorem scaledCompactSchwartzCutoff_hasCompactSupport (N : ℕ) :
    HasCompactSupport (scaledCompactSchwartzCutoff N) := by
  exact scaledCompactSchwartzCutoffFunction_hasCompactSupport N

theorem scaledCompactSchwartzCutoff_eq_one
    (N : ℕ) {x : ℝ} (hx : |x| ≤ (N : ℝ) + 1) :
    scaledCompactSchwartzCutoff N x = 1 := by
  rw [scaledCompactSchwartzCutoff_apply,
    compactSchwartzCutoff_eq_one]
  rw [abs_mul, abs_of_pos (compactSchwartzCutoffScale_pos N)]
  calc
    compactSchwartzCutoffScale N * |x| ≤
        compactSchwartzCutoffScale N * ((N : ℝ) + 1) := by
      exact mul_le_mul_of_nonneg_left hx
        (compactSchwartzCutoffScale_pos N).le
    _ = 1 := by
      rw [compactSchwartzCutoffScale, inv_mul_cancel₀]
      positivity

/-- Multiplication by the radius-`N+1` cutoff. -/
def compactSchwartzApproximation (N : ℕ) (f : SchwartzMap ℝ ℂ) :
    SchwartzMap ℝ ℂ :=
  SchwartzMap.smulLeftCLM ℂ (scaledCompactSchwartzCutoff N) f

@[simp]
theorem compactSchwartzApproximation_apply
    (N : ℕ) (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    compactSchwartzApproximation N f x =
      scaledCompactSchwartzCutoff N x * f x := by
  rw [compactSchwartzApproximation,
    SchwartzMap.smulLeftCLM_apply_apply
      (scaledCompactSchwartzCutoff N).hasTemperateGrowth]
  rfl

theorem compactSchwartzApproximation_hasCompactSupport
    (N : ℕ) (f : SchwartzMap ℝ ℂ) :
    HasCompactSupport (compactSchwartzApproximation N f) := by
  change IsCompact (tsupport (compactSchwartzApproximation N f))
  rw [show (compactSchwartzApproximation N f : ℝ → ℂ) =
      fun x => scaledCompactSchwartzCutoff N x * f x by
    funext x
    exact compactSchwartzApproximation_apply N f x]
  exact (scaledCompactSchwartzCutoff_hasCompactSupport N).mul_right

theorem compactSchwartzApproximation_preserves_vanishing
    (S : LocallyFiniteCarrier) (N : ℕ) (f : SchwartzMap ℝ ℂ)
    (hf : SchwartzVanishesOn S f) :
    SchwartzVanishesOn S (compactSchwartzApproximation N f) := by
  intro x hx
  rw [compactSchwartzApproximation_apply, hf x hx, mul_zero]

theorem iteratedDeriv_scaledCompactSchwartzCutoff
    (N i : ℕ) (x : ℝ) :
    iteratedDeriv i (scaledCompactSchwartzCutoff N) x =
      compactSchwartzCutoffScale N ^ i •
        iteratedDeriv i compactSchwartzCutoff
          (compactSchwartzCutoffScale N * x) := by
  have h := iteratedDeriv_comp_const_smul
    (compactSchwartzCutoff.smooth i)
    (compactSchwartzCutoffScale N)
  exact congrFun h x

theorem norm_iteratedDeriv_scaledCompactSchwartzCutoff_le
    (N i : ℕ) (x : ℝ) :
    ‖iteratedDeriv i (scaledCompactSchwartzCutoff N) x‖ ≤
      compactSchwartzCutoffScale N ^ i *
        SchwartzMap.seminorm ℂ 0 i compactSchwartzCutoff := by
  rw [iteratedDeriv_scaledCompactSchwartzCutoff, norm_smul,
    Real.norm_eq_abs, abs_pow,
    abs_of_pos (compactSchwartzCutoffScale_pos N)]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg
    (compactSchwartzCutoffScale_pos N).le i)
  have h := SchwartzMap.le_seminorm' ℂ 0 i compactSchwartzCutoff
    (compactSchwartzCutoffScale N * x)
  simpa only [pow_zero, one_mul] using h

theorem norm_iteratedDeriv_scaledCompactSchwartzCutoff_sub_one_le
    (N i : ℕ) (hi : i ≠ 0) (x : ℝ) :
    ‖iteratedDeriv i
        (fun y : ℝ => scaledCompactSchwartzCutoff N y - 1) x‖ ≤
      compactSchwartzCutoffScale N *
        SchwartzMap.seminorm ℂ 0 i compactSchwartzCutoff := by
  change ‖iteratedDeriv i
      ((fun y : ℝ => scaledCompactSchwartzCutoff N y) - fun _ => 1) x‖ ≤ _
  rw [iteratedDeriv_sub
    ((scaledCompactSchwartzCutoff N).smooth i).contDiffAt
    contDiffAt_const, iteratedDeriv_const, if_neg hi, sub_zero]
  exact (norm_iteratedDeriv_scaledCompactSchwartzCutoff_le N i x).trans
    (mul_le_mul_of_nonneg_right
      (pow_le_of_le_one (compactSchwartzCutoffScale_pos N).le
        (compactSchwartzCutoffScale_le_one N) hi)
      (by positivity))

theorem norm_scaledCompactSchwartzCutoff_sub_one_le_two
    (N : ℕ) (x : ℝ) :
    ‖scaledCompactSchwartzCutoff N x - 1‖ ≤ 2 := by
  calc
    ‖scaledCompactSchwartzCutoff N x - 1‖ ≤
        ‖scaledCompactSchwartzCutoff N x‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ ≤ 1 + 1 := add_le_add
      (by
        rw [scaledCompactSchwartzCutoff_apply]
        exact norm_compactSchwartzCutoff_le_one _)
      (by norm_num)
    _ = 2 := by norm_num

private theorem weighted_iteratedDeriv_le_cutoffScale
    (N k n : ℕ) (f : SchwartzMap ℝ ℂ) (x : ℝ)
    (hx : (N : ℝ) + 1 ≤ |x|) :
    |x| ^ k * ‖iteratedDeriv n f x‖ ≤
      compactSchwartzCutoffScale N * SchwartzMap.seminorm ℂ (k + 1) n f := by
  have hscaleAbs : 1 ≤ compactSchwartzCutoffScale N * |x| := by
    rw [compactSchwartzCutoffScale, inv_mul_eq_div]
    exact (le_div_iff₀ (by positivity : (0 : ℝ) < (N : ℝ) + 1)).2
      (by simpa only [one_mul] using hx)
  have hnonneg : 0 ≤ |x| ^ k * ‖iteratedDeriv n f x‖ := by positivity
  calc
    |x| ^ k * ‖iteratedDeriv n f x‖ =
        1 * (|x| ^ k * ‖iteratedDeriv n f x‖) := by rw [one_mul]
    _ ≤ (compactSchwartzCutoffScale N * |x|) *
        (|x| ^ k * ‖iteratedDeriv n f x‖) :=
      mul_le_mul_of_nonneg_right hscaleAbs hnonneg
    _ = compactSchwartzCutoffScale N *
        (|x| ^ (k + 1) * ‖iteratedDeriv n f x‖) := by
      rw [pow_succ]
      ring
    _ ≤ compactSchwartzCutoffScale N *
        SchwartzMap.seminorm ℂ (k + 1) n f :=
      mul_le_mul_of_nonneg_left
        (SchwartzMap.le_seminorm' ℂ (k + 1) n f x)
        (compactSchwartzCutoffScale_pos N).le

/-- A finite constant controlling one Schwartz seminorm of the cutoff error. -/
def compactSchwartzApproximationBound
    (k n : ℕ) (f : SchwartzMap ℝ ℂ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
    if i = 0 then
      2 * SchwartzMap.seminorm ℂ (k + 1) n f
    else
      SchwartzMap.seminorm ℂ 0 i compactSchwartzCutoff *
        SchwartzMap.seminorm ℂ k (n - i) f

theorem compactSchwartzApproximationBound_nonneg
    (k n : ℕ) (f : SchwartzMap ℝ ℂ) :
    0 ≤ compactSchwartzApproximationBound k n f := by
  apply Finset.sum_nonneg
  intro i hi
  apply mul_nonneg
  · positivity
  · split_ifs <;> positivity

theorem iteratedDeriv_compactSchwartzApproximation_sub
    (N n : ℕ) (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    iteratedDeriv n (compactSchwartzApproximation N f - f) x =
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℂ) *
        iteratedDeriv i
          (fun y : ℝ => scaledCompactSchwartzCutoff N y - 1) x *
        iteratedDeriv (n - i) f x := by
  have hg : ContDiff ℝ n
      (fun y : ℝ => scaledCompactSchwartzCutoff N y - 1) :=
    (scaledCompactSchwartzCutoff N).smooth n |>.sub contDiff_const
  have hmul := iteratedDeriv_mul
    (x := x) (n := n)
    hg.contDiffAt (f.smooth n).contDiffAt
  rw [← hmul]
  congr 1
  funext y
  change compactSchwartzApproximation N f y - f y =
    (scaledCompactSchwartzCutoff N y - 1) * f y
  rw [compactSchwartzApproximation_apply]
  ring

private theorem compactSchwartzApproximation_summand_le
    (N k n i : ℕ) (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    |x| ^ k * ‖(n.choose i : ℂ) *
        iteratedDeriv i
          (fun y : ℝ => scaledCompactSchwartzCutoff N y - 1) x *
        iteratedDeriv (n - i) f x‖ ≤
      compactSchwartzCutoffScale N * ((n.choose i : ℝ) *
        if i = 0 then
          2 * SchwartzMap.seminorm ℂ (k + 1) n f
        else
          SchwartzMap.seminorm ℂ 0 i compactSchwartzCutoff *
            SchwartzMap.seminorm ℂ k (n - i) f) := by
  by_cases hi : i = 0
  · subst i
    simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, if_pos,
      Nat.sub_zero, iteratedDeriv_zero]
    by_cases hx : |x| ≤ (N : ℝ) + 1
    · rw [scaledCompactSchwartzCutoff_eq_one N hx, sub_self,
        zero_mul, norm_zero, mul_zero]
      exact mul_nonneg (compactSchwartzCutoffScale_pos N).le
        (mul_nonneg (by norm_num)
          (apply_nonneg (SchwartzMap.seminorm ℂ (k + 1) n) f))
    · have htail := weighted_iteratedDeriv_le_cutoffScale
        N k n f x (le_of_not_ge hx)
      calc
        |x| ^ k * ‖(scaledCompactSchwartzCutoff N x - 1) *
            iteratedDeriv n f x‖ =
            ‖scaledCompactSchwartzCutoff N x - 1‖ *
              (|x| ^ k * ‖iteratedDeriv n f x‖) := by
          rw [norm_mul]
          ring
        _ ≤ 2 * (compactSchwartzCutoffScale N *
            SchwartzMap.seminorm ℂ (k + 1) n f) :=
          mul_le_mul
            (norm_scaledCompactSchwartzCutoff_sub_one_le_two N x)
            htail (by positivity) (by positivity)
        _ = compactSchwartzCutoffScale N *
            (2 * SchwartzMap.seminorm ℂ (k + 1) n f) := by ring
  · simp only [if_neg hi]
    have hg := norm_iteratedDeriv_scaledCompactSchwartzCutoff_sub_one_le
      N i hi x
    have hf := SchwartzMap.le_seminorm' ℂ k (n - i) f x
    calc
      |x| ^ k * ‖(n.choose i : ℂ) *
          iteratedDeriv i
            (fun y : ℝ => scaledCompactSchwartzCutoff N y - 1) x *
          iteratedDeriv (n - i) f x‖ =
          (n.choose i : ℝ) *
            ‖iteratedDeriv i
              (fun y : ℝ => scaledCompactSchwartzCutoff N y - 1) x‖ *
            (|x| ^ k * ‖iteratedDeriv (n - i) f x‖) := by
        rw [norm_mul, norm_mul, RCLike.norm_natCast]
        ring
      _ ≤ (n.choose i : ℝ) *
          (compactSchwartzCutoffScale N *
            SchwartzMap.seminorm ℂ 0 i compactSchwartzCutoff) *
          SchwartzMap.seminorm ℂ k (n - i) f := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hg (Nat.cast_nonneg _)) hf
          (by positivity)
          (mul_nonneg (Nat.cast_nonneg _)
            (mul_nonneg (compactSchwartzCutoffScale_pos N).le
              (apply_nonneg (SchwartzMap.seminorm ℂ 0 i)
                compactSchwartzCutoff)))
      _ = compactSchwartzCutoffScale N *
          ((n.choose i : ℝ) *
            (SchwartzMap.seminorm ℂ 0 i compactSchwartzCutoff *
              SchwartzMap.seminorm ℂ k (n - i) f)) := by ring

theorem compactSchwartzApproximation_pointwise_le
    (N k n : ℕ) (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    |x| ^ k *
        ‖iteratedDeriv n (compactSchwartzApproximation N f - f) x‖ ≤
      compactSchwartzCutoffScale N *
        compactSchwartzApproximationBound k n f := by
  rw [iteratedDeriv_compactSchwartzApproximation_sub]
  calc
    |x| ^ k * ‖∑ i ∈ Finset.range (n + 1), (n.choose i : ℂ) *
        iteratedDeriv i
          (fun y : ℝ => scaledCompactSchwartzCutoff N y - 1) x *
        iteratedDeriv (n - i) f x‖ ≤
        |x| ^ k * ∑ i ∈ Finset.range (n + 1),
          ‖(n.choose i : ℂ) *
            iteratedDeriv i
              (fun y : ℝ => scaledCompactSchwartzCutoff N y - 1) x *
            iteratedDeriv (n - i) f x‖ :=
      mul_le_mul_of_nonneg_left
        (norm_sum_le (Finset.range (n + 1)) fun i =>
          (n.choose i : ℂ) *
            iteratedDeriv i
              (fun y : ℝ => scaledCompactSchwartzCutoff N y - 1) x *
            iteratedDeriv (n - i) f x)
        (by positivity)
    _ = ∑ i ∈ Finset.range (n + 1), |x| ^ k *
          ‖(n.choose i : ℂ) *
            iteratedDeriv i
              (fun y : ℝ => scaledCompactSchwartzCutoff N y - 1) x *
            iteratedDeriv (n - i) f x‖ := by
      rw [Finset.mul_sum]
    _ ≤ ∑ i ∈ Finset.range (n + 1),
        compactSchwartzCutoffScale N * ((n.choose i : ℝ) *
          if i = 0 then
            2 * SchwartzMap.seminorm ℂ (k + 1) n f
          else
            SchwartzMap.seminorm ℂ 0 i compactSchwartzCutoff *
              SchwartzMap.seminorm ℂ k (n - i) f) := by
      exact Finset.sum_le_sum fun i hi =>
        compactSchwartzApproximation_summand_le N k n i f x
    _ = compactSchwartzCutoffScale N *
        compactSchwartzApproximationBound k n f := by
      rw [compactSchwartzApproximationBound, Finset.mul_sum]

theorem compactSchwartzApproximation_seminorm_le
    (N k n : ℕ) (f : SchwartzMap ℝ ℂ) :
    SchwartzMap.seminorm ℂ k n (compactSchwartzApproximation N f - f) ≤
      compactSchwartzCutoffScale N *
        compactSchwartzApproximationBound k n f := by
  exact SchwartzMap.seminorm_le_bound' ℂ k n
    (compactSchwartzApproximation N f - f)
    (mul_nonneg (compactSchwartzCutoffScale_pos N).le
      (compactSchwartzApproximationBound_nonneg k n f))
    (compactSchwartzApproximation_pointwise_le N k n f)

theorem compactSchwartzCutoffScale_tendsto :
    Tendsto compactSchwartzCutoffScale atTop (nhds 0) := by
  have hdenom : Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  change Tendsto (fun N : ℕ => ((N : ℝ) + 1)⁻¹) atTop (nhds 0)
  simpa [Function.comp_def] using
    tendsto_inv_atTop_zero.comp hdenom

/-- Expanding compact cutoffs converge to the identity in the full Schwartz
topology, rather than merely pointwise or in a fixed norm. -/
theorem compactSchwartzApproximation_tendsto (f : SchwartzMap ℝ ℂ) :
    Tendsto (fun N => compactSchwartzApproximation N f) atTop (nhds f) := by
  rw [(schwartz_withSeminorms ℂ ℝ ℂ).tendsto_nhds_atTop]
  rintro ⟨k, n⟩ ε hε
  have hbound : Tendsto
      (fun N => compactSchwartzCutoffScale N *
        compactSchwartzApproximationBound k n f)
      atTop (nhds 0) := by
    simpa using (compactSchwartzCutoffScale_tendsto.mul_const
      (compactSchwartzApproximationBound k n f))
  have hevent : ∀ᶠ N : ℕ in atTop,
      compactSchwartzCutoffScale N *
        compactSchwartzApproximationBound k n f < ε :=
    hbound.eventually (eventually_lt_nhds hε)
  rcases Filter.eventually_atTop.1 hevent with ⟨N₀, hN₀⟩
  refine ⟨N₀, fun N hN => ?_⟩
  exact lt_of_le_of_lt
    (compactSchwartzApproximation_seminorm_le N k n f) (hN₀ N hN)

/-- A local atomic formula on compactly supported Schwartz tests extends to
the full Schwartz vanishing ideal by cutoff density and continuity. -/
theorem hasLocallyAtomicAction_atomicOnCarrier
    (S : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ)
    (hT : HasLocallyAtomicAction S T) :
    AtomicOnCarrier S T := by
  intro f hf
  have hzero : ∀ N : ℕ, T (compactSchwartzApproximation N f) = 0 := by
    intro N
    exact hasLocallyAtomicAction_apply_eq_zero_of_hasCompactSupport
      S T hT (compactSchwartzApproximation N f)
      (compactSchwartzApproximation_hasCompactSupport N f)
      (compactSchwartzApproximation_preserves_vanishing S N f hf)
  have hlimit : Tendsto
      (fun N => T (compactSchwartzApproximation N f))
      atTop (nhds (T f)) :=
    (T.continuous.tendsto f).comp (compactSchwartzApproximation_tendsto f)
  have hzeroLimit : Tendsto
      (fun N => T (compactSchwartzApproximation N f))
      atTop (nhds 0) := by
    simpa only [hzero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (nhds 0))
  exact tendsto_nhds_unique hlimit hzeroLimit

/-- Intrinsic order-zero support on `S` is equivalent to the independently
quantified locally finite atomic formula on compactly supported tests. -/
theorem atomicOnCarrier_iff_hasLocallyAtomicAction
    (S : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ) :
    AtomicOnCarrier S T ↔ HasLocallyAtomicAction S T :=
  ⟨atomicOnCarrier_hasLocallyAtomicAction S T,
    hasLocallyAtomicAction_atomicOnCarrier S T⟩

end

end MeyerGeneralProblem
