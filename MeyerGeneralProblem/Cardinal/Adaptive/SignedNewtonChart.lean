module

public import MeyerGeneralProblem.Cardinal.Adaptive.SignedNewtonParity
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import all Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import all Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
import all Mathlib.Analysis.Calculus.ContDiff.Bounds

@[expose] public section

/-! # A fixed smooth chart for the signed characteristic grid

One fixed cutoff keeps the inverse sine away from its singular endpoints. The
chart is literal inverse sine on the tested small interval and does not depend
on the finite grid or on the test function.
-/
open scoped ContDiff
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open Set

/-- A fixed smooth function has one finite bound for the finitely many declared
derivatives on the fixed chart interval. -/
theorem exists_chart_derivative_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ℝ → E) (hg : ContDiff ℝ ∞ g) (N : ℕ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ n ≤ N, ∀ w ∈ Icc (-1/2:ℝ) (1/2), ‖iteratedDeriv n g w‖ ≤ B := by
  classical
  have hb (n : Fin (N+1)) : ∃ B : ℝ, ∀ w ∈ Icc (-1/2:ℝ) (1/2), ‖iteratedDeriv n g w‖ ≤ B :=
    isCompact_Icc.exists_bound_of_continuousOn
      (hg.continuous_iteratedDeriv n (by simp)).continuousOn
  choose B hB using hb
  refine ⟨1+∑ n, max (B n) 0,?_,?_⟩
  · have hs : 0 ≤ ∑ n : Fin (N+1), max (B n) 0 := Finset.sum_nonneg (fun n _ => le_max_right _ _)
    linarith
  · intro n hn w hw
    have h1 := hB ⟨n,by omega⟩ w hw
    have h2 : max (B ⟨n,by omega⟩) 0 ≤ ∑ j : Fin (N+1), max (B j) 0 :=
      Finset.single_le_sum (fun j _ => le_max_right _ _) (Finset.mem_univ (⟨n,by omega⟩ : Fin (N+1)))
    have h3 := le_max_left (B ⟨n,by omega⟩) 0
    linarith

/-- Every fixed weighted smooth coordinate change is bounded at each finite
order, uniformly in the varying test function. No derivative above `N` enters. -/
theorem exists_weighted_chart_derivative_bound (g : ℝ → ℝ) (a : ℝ → ℂ)
    (hg : ContDiff ℝ ∞ g) (ha : ContDiff ℝ ∞ a) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : ℝ → ℂ, ContDiff ℝ N f → ∀ A : ℝ, 0 ≤ A →
      (∀ n ≤ N, ∀ w ∈ Icc (-1/2:ℝ) (1/2), ‖iteratedDeriv n f (g w)‖ ≤ A) →
      ∀ n ≤ N, ∀ w ∈ Icc (-1/2:ℝ) (1/2),
        ‖iteratedDeriv n (fun v => a v*f (g v)) w‖ ≤ C*A := by
  obtain ⟨B,hB,hader⟩ := exists_chart_derivative_bound a ha N
  obtain ⟨D,hD,hgder⟩ := exists_chart_derivative_bound g hg N
  let c : ℕ → ℝ := fun n => ∑ j ∈ Finset.range (n+1),
    (n.choose j:ℝ)*B*((n-j).factorial*D^(n-j))
  have hc (n : ℕ) : 0 ≤ c n := Finset.sum_nonneg (fun j _ => by positivity)
  let C : ℝ := 1+∑ n ∈ Finset.range (N+1), c n
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro f hf A hA hfder n hn w hw
  have hcomp (r : ℕ) (hr : r ≤ N) :
      ‖iteratedDeriv r (fun v => f (g v)) w‖ ≤ (r.factorial:ℝ)*A*D^r := by
    have hh := norm_iteratedFDeriv_comp_le hf (hg.of_le (by simp) : ContDiff ℝ N g)
      (by exact_mod_cast hr) w
      (fun j hj => by rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]; exact hfder j (hj.trans hr) w hw)
      (fun j hj hjr => by
        rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
        exact (hgder j (hjr.trans hr) w hw).trans (le_self_pow₀ hD (by omega)))
    simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv,Function.comp_def] using hh
  have hmul := norm_iteratedFDeriv_mul_le (ha.of_le (by simp) : ContDiff ℝ N a)
    (hf.comp (hg.of_le (by simp))) w (by exact_mod_cast hn)
  simp only [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hmul
  have hs : (∑ j ∈ Finset.range (n+1), (n.choose j:ℝ)*‖iteratedDeriv j a w‖*
      ‖iteratedDeriv (n-j) (fun v => f (g v)) w‖) ≤ c n*A := by
    dsimp only [c]
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j hj
    have hjn : j ≤ n := by have := Finset.mem_range.mp hj; omega
    calc
      _ ≤ (n.choose j:ℝ)*B*((n-j).factorial*A*D^(n-j)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hader j (hjn.trans hn) w hw) (by positivity))
          (hcomp (n-j) (by omega)) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hcC : c n ≤ C := by
    have hh := Finset.single_le_sum (fun j (_ : j ∈ Finset.range (N+1)) => hc j)
      (Finset.mem_range.mpr (show n < N+1 by omega))
    dsimp [C]
    linarith
  exact hmul.trans (hs.trans (mul_le_mul_of_nonneg_right hcC hA))

/-- Fixed chart cutoff, equal to one on the half interval and zero beyond three quarters. -/
def signedChartBump : ContDiffBump (0:ℝ) where
  rIn := 1/2
  rOut := 3/4
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- A globally bounded sine coordinate before applying inverse sine. -/
def signedChartCoordinate (w : ℝ) : ℝ := signedChartBump w*w

/-- The chart coordinate stays a uniform distance from both singular endpoints. -/
theorem signedChartCoordinate_abs_le (w : ℝ) : |signedChartCoordinate w| ≤ 3/4 := by
  by_cases hw : |w| < 3/4
  · rw [signedChartCoordinate,abs_mul,abs_of_nonneg signedChartBump.nonneg]
    have := mul_le_mul_of_nonneg_right (signedChartBump.le_one (x := w)) (abs_nonneg w)
    linarith
  · have hz := signedChartBump.zero_of_le_dist (x := w) (by simpa [Real.dist_eq,signedChartBump] using le_of_not_gt hw)
    norm_num [signedChartCoordinate,hz]

/-- The chart coordinate is exactly the original coordinate on the tested interval. -/
theorem signedChartCoordinate_eq (w : ℝ) (hw : |w| ≤ 1/2) : signedChartCoordinate w=w := by
  have hh := signedChartBump.one_of_mem_closedBall (x := w) (by
    simpa [Metric.mem_closedBall,Real.dist_eq,signedChartBump] using hw)
  simp [signedChartCoordinate,hh]

/-- A fixed globally smooth inverse sine chart. -/
def signedNewtonChart (w : ℝ) : ℝ := Real.arcsin (signedChartCoordinate w)/Real.pi

/-- Global smoothness costs no derivatives of the varying test function. -/
theorem signedNewtonChart_contDiff : ContDiff ℝ ∞ signedNewtonChart := by
  have hg : ContDiff ℝ ∞ signedChartCoordinate := signedChartBump.contDiff.mul contDiff_id
  apply ContDiff.div_const
  rw [contDiff_iff_contDiffAt]
  intro w
  have hw := signedChartCoordinate_abs_le w
  exact (Real.contDiffAt_arcsin (by intro h; rw [h] at hw; norm_num at hw)
    (by intro h; rw [h] at hw; norm_num at hw)).comp w hg.contDiffAt

/-- The smooth chart is exactly inverse sine on the finite-grid domain. -/
theorem signedNewtonChart_eq (w : ℝ) (hw : |w| ≤ 1/2) :
    signedNewtonChart w=Real.arcsin w/Real.pi := by
  rw [signedNewtonChart,signedChartCoordinate_eq w hw]

/-- Cosine never vanishes in the fixed global chart. -/
theorem signedNewtonChart_cos_pos (w : ℝ) : 0 < Real.cos (Real.pi*signedNewtonChart w) := by
  rw [signedNewtonChart,mul_div_cancel₀ _ Real.pi_ne_zero,Real.cos_arcsin]
  apply Real.sqrt_pos.mpr
  have hw := abs_le.mp (signedChartCoordinate_abs_le w)
  nlinarith [sq_nonneg (signedChartCoordinate w-3/4)]

/-- Fixed multiplier for the even cosine parity; the odd parity has multiplier one. -/
def signedNewtonChartWeight (odd : Bool) (w : ℝ) : ℂ :=
  if odd then 1 else ((Real.cos (Real.pi*signedNewtonChart w):ℂ))⁻¹

/-- Both fixed parity multipliers are globally smooth. -/
theorem signedNewtonChartWeight_contDiff (odd : Bool) : ContDiff ℝ ∞ (signedNewtonChartWeight odd) := by
  cases odd
  · apply ContDiff.inv
    · exact Complex.ofRealCLM.contDiff.comp (Real.contDiff_cos.comp (contDiff_const.mul signedNewtonChart_contDiff))
    · intro w
      exact_mod_cast (signedNewtonChart_cos_pos w).ne'
  · exact contDiff_const

/-- The globally smooth signed chart applied to the literal even or odd test projection. -/
def signedNewtonChartTrace (odd : Bool) (f : ℝ → ℂ) (w : ℝ) : ℂ :=
  signedNewtonChartWeight odd w * signParityPiece odd f (signedNewtonChart w)

/-- A chart trace preserves exactly the supplied finite differentiability order. -/
theorem signedNewtonChartTrace_contDiff (odd : Bool) (f : ℝ → ℂ) (N : ℕ)
    (hf : ContDiff ℝ N f) : ContDiff ℝ N (signedNewtonChartTrace odd f) := by
  have hg : ContDiff ℝ N (signParityPiece odd f) :=
    (hf.add (contDiff_const.mul (hf.comp contDiff_neg))).div_const 2
  exact ((signedNewtonChartWeight_contDiff odd).of_le (by simp)).mul
    (hg.comp (signedNewtonChart_contDiff.of_le (by simp)))

/-- The fixed chart and its reflection stay in the same test interval. -/
theorem signedNewtonChart_mem_Icc (w : ℝ) : signedNewtonChart w ∈ Icc (-1/2:ℝ) (1/2) := by
  constructor
  · rw [signedNewtonChart,le_div_iff₀ Real.pi_pos]
    linarith [Real.neg_pi_div_two_le_arcsin (signedChartCoordinate w)]
  · rw [signedNewtonChart,div_le_iff₀ Real.pi_pos]
    linarith [Real.arcsin_le_pi_div_two (signedChartCoordinate w)]

/-- One fixed constant controls the whole signed parity trace at every order up
to `N`, from the same orders of the original test on the fixed interval. -/
theorem exists_signedNewtonChartTrace_derivative_bound (odd : Bool) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : ℝ → ℂ, ContDiff ℝ N f → ∀ A : ℝ, 0 ≤ A →
      (∀ n ≤ N, ∀ x ∈ Icc (-1/2:ℝ) (1/2), ‖iteratedDeriv n f x‖ ≤ A) →
      ∀ n ≤ N, ∀ w ∈ Icc (-1/2:ℝ) (1/2),
        ‖iteratedDeriv n (signedNewtonChartTrace odd f) w‖ ≤ C*A := by
  let a : ℝ → ℂ := fun w => signedNewtonChartWeight odd w/2
  let b : ℝ → ℂ := fun w => (if odd then (-1:ℂ) else 1)*signedNewtonChartWeight odd w/2
  have ha : ContDiff ℝ ∞ a := (signedNewtonChartWeight_contDiff odd).div_const 2
  have hb : ContDiff ℝ ∞ b := (contDiff_const.mul (signedNewtonChartWeight_contDiff odd)).div_const 2
  obtain ⟨C₁,hC₁,h₁⟩ := exists_weighted_chart_derivative_bound signedNewtonChart a signedNewtonChart_contDiff ha N
  obtain ⟨C₂,hC₂,h₂⟩ := exists_weighted_chart_derivative_bound (fun w => -signedNewtonChart w) b signedNewtonChart_contDiff.neg hb N
  refine ⟨C₁+C₂,add_pos hC₁ hC₂,?_⟩
  intro f hf A hA hder n hn w hw
  have h1 := h₁ f hf A hA (fun i hi v _ => hder i hi _ (signedNewtonChart_mem_Icc v)) n hn w hw
  have h2 := h₂ f hf A hA (fun i hi v _ => hder i hi _ (by
    have hh := signedNewtonChart_mem_Icc v
    constructor <;> linarith [hh.1,hh.2])) n hn w hw
  have he : signedNewtonChartTrace odd f = fun w =>
      a w*f (signedNewtonChart w)+b w*f (-signedNewtonChart w) := by
    funext w
    dsimp [signedNewtonChartTrace,signParityPiece,a,b]
    ring
  have hs1 : ContDiff ℝ n (fun w => a w*f (signedNewtonChart w)) :=
    ((ha.of_le (by simp)).mul (hf.comp (signedNewtonChart_contDiff.of_le (by simp)))).of_le (by exact_mod_cast hn)
  have hs2 : ContDiff ℝ n (fun w => b w*f (-signedNewtonChart w)) :=
    ((hb.of_le (by simp)).mul (hf.comp (signedNewtonChart_contDiff.neg.of_le (by simp)))).of_le (by exact_mod_cast hn)
  rw [he,iteratedDeriv_fun_add hs1.contDiffAt hs2.contDiffAt]
  exact (norm_add_le _ _).trans (by nlinarith)

/-- The chart really inverts sine at every tested signed phase. -/
theorem signedNewtonChart_sin (t : ℝ) (ht : |t| ≤ 1/2)
    (hs : |Real.sin (Real.pi*t)| ≤ 1/2) :
    signedNewtonChart (Real.sin (Real.pi*t))=t := by
  rw [signedNewtonChart_eq _ hs,Real.arcsin_sin]
  · exact mul_div_cancel_left₀ t Real.pi_ne_zero
  · have hh := abs_le.mp ht
    nlinarith [Real.pi_pos]
  · have hh := abs_le.mp ht
    nlinarith [Real.pi_pos]

/-- The even signed trace is the literal cosine quotient at all tested phases. -/
theorem signedNewtonChartTrace_even_sin (f : ℝ → ℂ) (t : ℝ) (ht : |t| ≤ 1/2)
    (hs : |Real.sin (Real.pi*t)| ≤ 1/2) :
    signedNewtonChartTrace false f (Real.sin (Real.pi*t))=parityGridQuotient false f t := by
  simp only [signedNewtonChartTrace,signedNewtonChartWeight,Bool.false_eq_true,ite_false,
    signedNewtonChart_sin t ht hs,parityGridQuotient,false_and,parityTrigFactor]
  rw [div_eq_mul_inv,mul_comm]

/-- The odd signed trace is the literal odd test projection, without a quotient. -/
theorem signedNewtonChartTrace_odd_sin (f : ℝ → ℂ) (t : ℝ) (ht : |t| ≤ 1/2)
    (hs : |Real.sin (Real.pi*t)| ≤ 1/2) :
    signedNewtonChartTrace true f (Real.sin (Real.pi*t))=signParityPiece true f t := by
  simp only [signedNewtonChartTrace,signedNewtonChartWeight,ite_true,one_mul,signedNewtonChart_sin t ht hs]


end
end MeyerGeneralProblem.Adaptive
