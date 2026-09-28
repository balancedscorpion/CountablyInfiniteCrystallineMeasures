module

public import MeyerGeneralProblem.Cardinal.Adaptive.ReverseZakChart
public import MeyerGeneralProblem.Cardinal.Adaptive.SignedNewtonChart

@[expose] public section

/-! The fixed compact-chart Zak gauge has uniform bounds at each finite mixed order. -/

noncomputable section
open scoped BigOperators ContDiff

namespace MeyerGeneralProblem.Adaptive

private theorem contDiff_const_mul_real (c : ℂ) (N : ℕ∞ω) :
    ContDiff ℝ N (fun x : ℝ => c*x) :=
  contDiff_const.mul (show ContDiff ℝ N (fun x : ℝ => (x:ℂ)) from Complex.ofRealCLM.contDiff)

/-- Literal fixed gauge from the compact Zak admission chart. -/
def fixedZakGauge (x y : ℝ) : ℂ :=
  Complex.exp (((-2*Real.pi:ℝ):ℂ)*Complex.I*x*y)

/-- Exact real derivatives of a complex linear exponential. -/
theorem iteratedDeriv_exp_real_linear (c : ℂ) (a : ℕ) :
    iteratedDeriv a (fun x : ℝ => Complex.exp (c*x)) =
      fun x : ℝ => c^a*Complex.exp (c*x) := by
  induction a with
  | zero => simp only [iteratedDeriv_zero,pow_zero,one_mul]
  | succ a ih =>
      rw [iteratedDeriv_succ,ih]
      funext x
      have hh := ((((hasDerivAt_id x).ofReal_comp.const_mul c).cexp).const_mul (c^a)).deriv
      simpa only [id_eq,Complex.ofReal_one,mul_one,one_mul,pow_succ,mul_assoc,mul_left_comm,mul_comm] using hh

/-- The fixed gauge has unit modulus on the whole real plane. -/
theorem fixedZakGauge_norm (x y : ℝ) : ‖fixedZakGauge x y‖ = 1 := by
  rw [fixedZakGauge,Complex.norm_exp]
  simp [Complex.mul_re,Complex.mul_im]

/-- Exact spatial derivatives of the fixed gauge. -/
theorem iteratedDeriv_fixedZakGauge_x (a : ℕ) (y : ℝ) :
    iteratedDeriv a (fun x => fixedZakGauge x y) =
      fun x => (((-2*Real.pi:ℝ):ℂ)*Complex.I*y)^a*fixedZakGauge x y := by
  have he : (fun x => fixedZakGauge x y) =
      (fun x : ℝ => Complex.exp ((((-2*Real.pi:ℝ):ℂ)*Complex.I*y)*x)) := by
    funext x
    unfold fixedZakGauge
    congr 1
    ring
  rw [he,iteratedDeriv_exp_real_linear]
  funext x
  unfold fixedZakGauge
  congr 2
  ring

/-- Every spatial derivative of the fixed gauge is smooth in the other coordinate. -/
theorem fixedZakGauge_mixed_contDiff (a : ℕ) (x : ℝ) :
    ContDiff ℝ ∞ (fun y => iteratedDeriv a (fun x => fixedZakGauge x y) x) := by
  simp only [iteratedDeriv_fixedZakGauge_x]
  unfold fixedZakGauge
  exact ((contDiff_const_mul_real (((-2*Real.pi:ℝ):ℂ)*Complex.I) ∞).pow a).mul
    ((contDiff_const_mul_real (((-2*Real.pi:ℝ):ℂ)*Complex.I*x) ∞).cexp)

/-- All mixed derivatives on the fixed half-cell have one bound depending
only on the declared finite order. No rapid-grid or source parameters occur. -/
theorem exists_fixedZakGauge_mixed_bound (N : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ a ≤ N, ∀ b ≤ N,
      ∀ x ∈ Set.Icc (-1/2:ℝ) (1/2), ∀ y ∈ Set.Icc (-1/2:ℝ) (1/2),
      ‖iteratedDeriv b (fun v => iteratedDeriv a (fun u => fixedZakGauge u v) x) y‖ ≤ B := by
  classical
  let c : ℂ := ((-2*Real.pi:ℝ):ℂ)*Complex.I
  have hc : c.re=0 := by simp [c,Complex.mul_re]
  have hbound (a : Fin (N+1)) := exists_weighted_chart_derivative_bound
    (fun y : ℝ => y) (fun y : ℝ => (c*y)^a.val) (by fun_prop) ((contDiff_const_mul_real c ∞).pow a.val) N
  choose C hC hbound using hbound
  let A : ℝ := (1+‖c‖)^N
  let B : ℝ := (∑ a, C a)*A
  have hCA : 0 < A := by dsimp [A]; positivity
  have hsum : 0 < ∑ a, C a := (hC 0).trans_le
    (Finset.single_le_sum (fun j _ => (hC j).le) (Finset.mem_univ 0))
  refine ⟨B,mul_pos hsum hCA,?_⟩
  intro a ha b hb x hx y hy
  have htest : ∀ k ≤ N, ∀ w ∈ Set.Icc (-1/2:ℝ) (1/2),
      ‖iteratedDeriv k (fun v : ℝ => Complex.exp ((c*x)*v)) w‖ ≤ A := by
    intro k hk w _hw
    rw [iteratedDeriv_exp_real_linear,norm_mul,norm_pow]
    have he : ‖Complex.exp ((c*x)*w)‖=1 := by
      rw [Complex.norm_exp]
      simp [Complex.mul_re,Complex.mul_im,hc]
    rw [he,mul_one]
    have hx1 : |x| ≤ 1 := abs_le.mpr ⟨by linarith [hx.1],by linarith [hx.2]⟩
    have hcx : ‖c*(x:ℂ)‖ ≤ 1+‖c‖ := by
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
      nlinarith [norm_nonneg c]
    exact (pow_le_pow_left₀ (norm_nonneg _) hcx k).trans
      (pow_le_pow_right₀ (by linarith [norm_nonneg c]) hk)
  have hh := hbound ⟨a,by omega⟩ (fun v : ℝ => Complex.exp ((c*x)*v))
    ((contDiff_const_mul_real (c*x) N).cexp) A hCA.le htest b hb y hy
  have he (v : ℝ) : iteratedDeriv a (fun u => fixedZakGauge u v) x =
      (c*v)^a*Complex.exp ((c*x)*v) := by
    rw [iteratedDeriv_fixedZakGauge_x]
    rfl
  simp_rw [he]
  apply hh.trans
  exact mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun j _ => (hC j).le) (Finset.mem_univ (⟨a,by omega⟩ : Fin (N+1)))) hCA.le

end MeyerGeneralProblem.Adaptive
