module

public import MeyerGeneralProblem.Cardinal.Adaptive.PhaseClosure
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import all Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import all Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import all Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import all Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
import all Mathlib.Topology.Instances.Real.Lemmas

@[expose] public section

/-!
# Smooth periodic functions annihilating exactly the actual phase closures

The compactly supported generator is constructed on the complement of the
closed periodic phase set. Its integer periodization is smooth because only
finitely many translates meet any bounded neighbourhood. A flat scalar
composition will retain the exact zero set before mean normalization.
-/

namespace MeyerGeneralProblem.Adaptive
noncomputable section
open Set Filter Function MeasureTheory
open scoped Topology ContDiff

/-- Integer shifts preserve the full periodic phase set, including its seams. -/
theorem periodicPhaseSet_add_int_iff (P R : ℕ) (x : ℝ) (z : ℤ) :
    x+(z:ℝ) ∈ periodicPhaseSet P R ↔ x ∈ periodicPhaseSet P R := by
  constructor
  · rintro ⟨n,β,hβ,h⟩
    refine ⟨n-z,β,hβ,?_⟩
    push_cast
    linarith
  · rintro ⟨n,β,hβ,h⟩
    refine ⟨n+z,β,hβ,?_⟩
    push_cast
    linarith

/-- Periodize an actual compactly supported real function. -/
def unitPeriodization (f : ℝ → ℝ) (x : ℝ) : ℝ := ∑' n : ℤ, f (x+n)

private theorem translate_support_finite (f : ℝ → ℝ)
    (hs : support f ⊆ Icc (-1) 1) (x : ℝ) :
    (support (fun n : ℤ => f (x+n))).Finite := by
  obtain ⟨N:ℕ,hN⟩ := exists_nat_gt (|x|+2)
  apply (Set.finite_Icc (-(N:ℤ)) (N:ℤ)).subset
  intro n hn
  obtain ⟨hlo,hhi⟩ := hs hn
  have ha := neg_abs_le x
  have hb := le_abs_self x
  constructor
  · exact_mod_cast (by linarith : -(N:ℝ) ≤ (n:ℝ))
  · exact_mod_cast (by linarith : (n:ℝ) ≤ (N:ℝ))

/-- Every periodized series is summable, with no conditional infinite sum. -/
theorem summable_unitPeriodization (f : ℝ → ℝ)
    (hs : support f ⊆ Icc (-1) 1) (x : ℝ) :
    Summable (fun n : ℤ => f (x+n)) :=
  summable_of_hasFiniteSupport (translate_support_finite f hs x)

theorem unitPeriodization_periodic (f : ℝ → ℝ) : Periodic (unitPeriodization f) 1 := by
  intro x
  unfold unitPeriodization
  have h := (Equiv.addRight (1:ℤ)).tsum_eq (fun n:ℤ => f (x+n))
  convert h using 1
  congr 1
  funext n
  simp only [Equiv.coe_addRight,Int.cast_add,Int.cast_one]
  congr 1
  ring

/-- The integer periodization is a locally finite smooth sum. -/
theorem unitPeriodization_contDiff (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (hs : support f ⊆ Icc (-1) 1) : ContDiff ℝ ∞ (unitPeriodization f) := by
  classical
  apply contDiff_iff_contDiffAt.mpr
  intro x
  obtain ⟨N:ℕ,hN⟩ := exists_nat_gt (|x|+3)
  let I : Finset ℤ := Finset.Icc (-(N:ℤ)) (N:ℤ)
  have heq : unitPeriodization f =ᶠ[𝓝 x] fun y => ∑ n ∈ I, f (y+n) := by
    filter_upwards [Ioo_mem_nhds (by linarith : x-1<x) (by linarith : x<x+1)] with y hy
    apply tsum_eq_sum
    intro n hn
    by_contra hne
    obtain ⟨hlo,hhi⟩ := hs hne
    have ha := neg_abs_le x
    have hb := le_abs_self x
    have hlo' : -(N:ℤ) ≤ n := by exact_mod_cast (by linarith [hy.2] : -(N:ℝ) ≤ (n:ℝ))
    have hhi' : n ≤ (N:ℤ) := by exact_mod_cast (by linarith [hy.1] : (n:ℝ) ≤ (N:ℝ))
    exact hn (Finset.mem_Icc.mpr ⟨hlo',hhi'⟩)
  have hfinite : ContDiff ℝ ∞ (fun y => ∑ n ∈ I, f (y+n)) :=
    ContDiff.sum fun n _ => hf.comp (contDiff_id.add contDiff_const)
  exact hfinite.contDiffAt.congr_of_eventuallyEq heq

/-- An actual smooth nonnegative periodic function has precisely the required
zero set; no countability-only or indicator-function surrogate is used. -/
theorem exists_smooth_periodic_zero_set {P R : ℕ} (hP : 1 ≤ P) (hR : 1 ≤ R) :
    ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧ Periodic g 1 ∧
      (∀ x, 0 ≤ g x) ∧ (∀ x, g x = 0 ↔ x ∈ periodicPhaseSet P R) := by
  let U := Ioo (-1:ℝ) 1 ∩ (periodicPhaseSet P R)ᶜ
  have hU : IsOpen U := isOpen_Ioo.inter (periodicPhaseSet_isClosed hP hR).isOpen_compl
  obtain ⟨f,hfs,hf,hfrange⟩ := hU.exists_contDiff_support_eq (n := ⊤)
  have hs : support f ⊆ Icc (-1) 1 := by
    rw [hfs]
    exact fun _ h => ⟨h.1.1.le,h.1.2.le⟩
  have hfnonneg (x:ℝ) : 0 ≤ f x := (hfrange ⟨x,rfl⟩).1
  refine ⟨unitPeriodization f,unitPeriodization_contDiff f hf hs,
    unitPeriodization_periodic f,fun x => tsum_nonneg (fun n => hfnonneg (x+n)),?_⟩
  intro x
  constructor
  · intro hz
    by_contra hx
    let n : ℤ := -⌊x⌋
    have hxn : x+(n:ℝ) ∈ support f := by
      rw [hfs]
      refine ⟨⟨?_,?_⟩,?_⟩
      · have h := Int.floor_le x
        dsimp [n]
        push_cast
        linarith
      · have h := Int.lt_floor_add_one x
        dsimp [n]
        push_cast
        linarith
      · exact fun h => hx ((periodicPhaseSet_add_int_iff P R x n).mp h)
    have hpos : 0 < f (x+n) := lt_of_le_of_ne (hfnonneg _) (Ne.symm hxn)
    have hle := (summable_unitPeriodization f hs x).le_tsum n (fun n _ => hfnonneg (x+n))
    change f (x+n) ≤ unitPeriodization f x at hle
    linarith
  · intro hx
    have hall (n:ℤ) : f (x+n) = 0 := by
      by_contra hn
      have hm : x+(n:ℝ) ∈ support f := hn
      rw [hfs] at hm
      exact hm.2 ((periodicPhaseSet_add_int_iff P R x n).mpr hx)
    simp [unitPeriodization,hall]

private theorem flat_polynomial_zero (n : ℕ) (p : Polynomial ℝ)
    (u v : ℝ → ℝ) (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (x : ℝ) (hx : u x = 0) :
    iteratedDeriv n (fun y => p.eval (u y)⁻¹ * expNegInvGlue (u y) * v y) x = 0 := by
  induction n generalizing p v with
  | zero => simp [iteratedDeriv_zero,hx,expNegInvGlue.zero]
  | succ n ih =>
    let q : Polynomial ℝ := Polynomial.X^2 * (p-p.derivative)
    have hud : ContDiff ℝ ∞ (deriv u) := (contDiff_infty_iff_deriv.mp hu).2
    have hvd : ContDiff ℝ ∞ (deriv v) := (contDiff_infty_iff_deriv.mp hv).2
    have hd : deriv (fun y => p.eval (u y)⁻¹ * expNegInvGlue (u y) * v y) =
        fun y => q.eval (u y)⁻¹ * expNegInvGlue (u y) * (deriv u y * v y) +
          p.eval (u y)⁻¹ * expNegInvGlue (u y) * deriv v y := by
      funext y
      have hd := ((expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul p (u y)).comp y
        ((hu.differentiable (by simp)) y).hasDerivAt).mul
          ((hv.differentiable (by simp)) y).hasDerivAt
      have hd' : HasDerivAt
          (fun z => p.eval (u z)⁻¹ * expNegInvGlue (u z) * v z)
          (q.eval (u y)⁻¹ * expNegInvGlue (u y) * deriv u y * v y +
            p.eval (u y)⁻¹ * expNegInvGlue (u y) * deriv v y) y := hd
      simpa only [mul_assoc] using hd'.deriv
    have hq : ContDiff ℝ ∞ (fun y => q.eval (u y)⁻¹ * expNegInvGlue (u y) *
        (deriv u y * v y)) :=
      ((expNegInvGlue.contDiff_polynomial_eval_inv_mul (n := ⊤) q).comp hu).mul (hud.mul hv)
    have hp : ContDiff ℝ ∞ (fun y => p.eval (u y)⁻¹ * expNegInvGlue (u y) * deriv v y) :=
      ((expNegInvGlue.contDiff_polynomial_eval_inv_mul (n := ⊤) p).comp hu).mul hvd
    rw [iteratedDeriv_succ',hd,iteratedDeriv_fun_add
      (hq.of_le (by simp)).contDiffAt (hp.of_le (by simp)).contDiffAt]
    rw [ih q (fun y => deriv u y * v y) (hud.mul hv),ih p (deriv v) hvd]
    simp

/-- The scalar flattening has every derivative zero at every zero of its
smooth input, including isolated phase points. -/
theorem iteratedDeriv_flatten_zero (u : ℝ → ℝ) (hu : ContDiff ℝ ∞ u)
    (x : ℝ) (hx : u x = 0) (n : ℕ) :
    iteratedDeriv n (fun y => expNegInvGlue (u y)) x = 0 := by
  simpa using flat_polynomial_zero n 1 u (fun _ => 1) hu contDiff_const x hx

/-- Flatness, periodicity and the exact zero set hold simultaneously for a
single concrete smooth function for every positive block. -/
theorem exists_flat_periodic_zero_set {P R : ℕ} (hP : 1 ≤ P) (hR : 1 ≤ R) :
    ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧ Periodic g 1 ∧
      (∀ x, 0 ≤ g x) ∧ (∀ x, g x = 0 ↔ x ∈ periodicPhaseSet P R) ∧
        (∀ x ∈ periodicPhaseSet P R, ∀ n, iteratedDeriv n g x = 0) := by
  obtain ⟨u,hu,hperiod,hnonneg,hzero⟩ := exists_smooth_periodic_zero_set hP hR
  refine ⟨fun x => expNegInvGlue (u x),expNegInvGlue.contDiff.comp hu,
    fun x => congrArg expNegInvGlue (hperiod x),
    fun x => expNegInvGlue.nonneg _,?_,?_⟩
  · intro x
    rw [expNegInvGlue.zero_iff_nonpos]
    exact ⟨fun h => (hzero x).mp (le_antisymm h (hnonneg x)),
      fun h => ((hzero x).mpr h).le⟩
  · intro x hx n
    exact iteratedDeriv_flatten_zero u hu x ((hzero x).mpr hx) n

/-- Normalize the flat periodic annihilator by its actual positive integral.
The result has mean exactly one and retains every zero jet on the phase set. -/
theorem exists_mean_one_flat_periodic_annihilator {P R : ℕ}
    (hP : 1 ≤ P) (hR : 1 ≤ R) :
    ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧ Periodic g 1 ∧
      (∀ x, 0 ≤ g x) ∧ (∀ x, g x = 0 ↔ x ∈ periodicPhaseSet P R) ∧
        (∀ x ∈ periodicPhaseSet P R, ∀ n, iteratedDeriv n g x = 0) ∧
          (∫ x in (0:ℝ)..1, g x) = 1 := by
  obtain ⟨u,hu,hperiod,hnonneg,hzero,hflat⟩ := exists_flat_periodic_zero_set hP hR
  have hposzero : 0 < u 0 := lt_of_le_of_ne (hnonneg 0)
    (Ne.symm (fun h => zero_not_mem_periodicPhaseSet hP hR ((hzero 0).mp h)))
  let c : ℝ := ∫ x in (0:ℝ)..1, u x
  have hc : 0 < c := by
    have h := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
      (by norm_num : (0:ℝ)<1) continuous_const.continuousOn hu.continuous.continuousOn
      (fun x _ => hnonneg x) ⟨0,by norm_num,hposzero⟩
    simpa only [intervalIntegral.integral_zero] using h
  refine ⟨fun x => u x / c,hu.div_const c,fun x => congrArg (fun z => z/c) (hperiod x),
    fun x => div_nonneg (hnonneg x) hc.le,?_,?_,?_⟩
  · intro x
    simpa only [div_eq_zero_iff,hc.ne',or_false] using hzero x
  · intro x hx n
    rw [iteratedDeriv_div_const,hflat x hx n,zero_div]
  · rw [intervalIntegral.integral_div]
    exact div_self hc.ne'

/-- Every derivative of a smooth periodic function is bounded on the whole
line. Constants depend on the function and derivative order only. -/
theorem smoothPeriodic_derivatives_bounded (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g)
    (hperiod : Periodic g 1) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x, ‖iteratedDeriv n g x‖ ≤ C := by
  have hp : Periodic (iteratedDeriv n g) 1 := by
    intro x
    have he : (fun y => g (y+1)) = g := funext hperiod
    have h := congrFun (iteratedDeriv_comp_add_const n g 1) x
    rw [he] at h
    exact h.symm
  have hc := hg.continuous_iteratedDeriv n (by simp)
  obtain ⟨C,hC,hbound⟩ := (hp.isBounded_of_continuous (by norm_num) hc).exists_pos_norm_le
  exact ⟨C,hC,fun x => hbound _ ⟨x,rfl⟩⟩

/-- One chosen annihilator depends only on the block's positive order and gap. -/
def phaseAnnihilator (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) : ℝ → ℝ :=
  Classical.choose (exists_mean_one_flat_periodic_annihilator hP hR)

theorem phaseAnnihilator_spec (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) :
    let g := phaseAnnihilator P R hP hR
    ContDiff ℝ ∞ g ∧ Periodic g 1 ∧
      (∀ x, 0 ≤ g x) ∧ (∀ x, g x = 0 ↔ x ∈ periodicPhaseSet P R) ∧
        (∀ x ∈ periodicPhaseSet P R, ∀ n, iteratedDeriv n g x = 0) ∧
          (∫ x in (0:ℝ)..1, g x) = 1 :=
  Classical.choose_spec (exists_mean_one_flat_periodic_annihilator hP hR)

/-- Every fixed-order global derivative bound is chosen before any scales. -/
theorem phaseAnnihilator_derivatives_bounded (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R)
    (n : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ x,
      ‖iteratedDeriv n (phaseAnnihilator P R hP hR) x‖ ≤ C :=
  smoothPeriodic_derivatives_bounded _ (phaseAnnihilator_spec P R hP hR).1
    (phaseAnnihilator_spec P R hP hR).2.1 n

end
end MeyerGeneralProblem.Adaptive
