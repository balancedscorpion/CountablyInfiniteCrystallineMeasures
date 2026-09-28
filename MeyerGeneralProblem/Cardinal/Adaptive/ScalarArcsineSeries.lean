module

public import Mathlib.Analysis.Analytic.Binomial
import all Mathlib.Analysis.Analytic.Binomial
public import Mathlib.Analysis.Calculus.SmoothSeries
import all Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import all Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
public import Mathlib.Data.Nat.Choose.Central
import all Mathlib.Data.Nat.Choose.Central

@[expose] public section

/-! # Explicit scalar arcsine series on the source chart -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open Polynomial

/-- The positive real coefficients of the scalar arcsine factor. -/
def scalarArcsineCoefficient (n : ℕ) : ℝ :=
  (Nat.centralBinom n : ℝ) / (4^n * (2*n+1))

/-- The constant coefficient is exactly one. -/
theorem scalarArcsineCoefficient_zero : scalarArcsineCoefficient 0=1 := by
  norm_num [scalarArcsineCoefficient,Nat.centralBinom]

/-- Every scalar coefficient is nonnegative. -/
theorem scalarArcsineCoefficient_nonneg (n : ℕ) : 0 ≤ scalarArcsineCoefficient n := by
  unfold scalarArcsineCoefficient
  positivity

/-- The central binomial estimate bounds every coefficient by one. -/
theorem scalarArcsineCoefficient_le_one (n : ℕ) : scalarArcsineCoefficient n ≤ 1 := by
  unfold scalarArcsineCoefficient
  apply (div_le_one (by positivity)).2
  have h : (Nat.centralBinom n : ℝ) ≤ (4:ℝ)^n := by
    exact_mod_cast Nat.centralBinom_le_four_pow n
  exact h.trans (le_mul_of_one_le_right (by positivity) (by have h : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith))

private theorem multichoose_step (a : ℝ) (n : ℕ) :
    (n+1 : ℝ)*Ring.multichoose a (n+1)=(a+n)*Ring.multichoose a n := by
  have h0 := Ring.factorial_nsmul_multichoose_eq_ascPochhammer a n
  have h1 := Ring.factorial_nsmul_multichoose_eq_ascPochhammer a (n+1)
  rw [ascPochhammer_smeval_eq_eval] at h0 h1
  rw [ascPochhammer_succ_right,eval_mul,eval_add,eval_X,eval_natCast] at h1
  simp only [nsmul_eq_mul,Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one] at h0 h1
  have hn : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  apply (mul_left_cancel₀ hn)
  calc
    _ = ((n+1 : ℝ)*(n.factorial:ℝ))*Ring.multichoose a (n+1) := by ring
    _ = (ascPochhammer ℝ n).eval a*(a+n) := h1
    _ = _ := by rw [←h0]; ring

/-- The half-order binomial coefficients are the actual central binomial numbers. -/
theorem half_multichoose_eq_centralBinom (n : ℕ) :
    Ring.multichoose (1/2 : ℝ) n=(Nat.centralBinom n : ℝ)/4^n := by
  induction n with
  | zero => norm_num [Ring.multichoose_zero_right,Nat.centralBinom]
  | succ n ih =>
    have hs := multichoose_step (1/2) n
    rw [ih] at hs
    have hc : (n+1 : ℝ)*(Nat.centralBinom (n+1):ℝ)=
        2*(2*n+1)*(Nat.centralBinom n:ℝ) := by
      exact_mod_cast Nat.succ_mul_centralBinom_succ n
    rw [pow_succ]
    have h4 : (4:ℝ)^n ≠ 0 := pow_ne_zero _ (by norm_num)
    apply (eq_div_iff (mul_ne_zero h4 (by norm_num))).2
    field_simp at hs
    nlinarith

/-- The derivative series is the full positive half-order binomial expansion. -/
theorem centralBinom_hasSum_inv_sqrt (t : ℝ) (ht : |t| < 1) :
    HasSum (fun n => (Nat.centralBinom n : ℝ)/4^n*t^(2*n))
      (1/Real.sqrt (1-t^2)) := by
  have hsq : |t^2| < 1 := by
    rw [abs_pow]
    nlinarith [abs_nonneg t]
  have he : t^2 ∈ Metric.eball (0:ℝ) 1 := by
    simpa [Metric.mem_eball,edist_dist,Real.dist_eq,sub_zero,ENNReal.ofReal_lt_one] using hsq
  have h := (Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero (1/2)).hasSum_sub he
  simp only [sub_zero,FormalMultilinearSeries.ofScalars_apply_eq,smul_eq_mul] at h
  rw [←Real.sqrt_eq_rpow] at h
  simpa only [←Ring.multichoose_eq,half_multichoose_eq_centralBinom,pow_mul] using h

/-- The literal odd power series with the prescribed central binomial coefficients. -/
def scalarArcsineSeries (t : ℝ) : ℝ :=
  ∑' n, scalarArcsineCoefficient n*t^(2*n+1)

private theorem coefficient_derivative (n : ℕ) :
    scalarArcsineCoefficient n*(2*n+1)=(Nat.centralBinom n:ℝ)/4^n := by
  unfold scalarArcsineCoefficient
  have hn : (2*n+1:ℝ) ≠ 0 := by positivity
  field_simp

/-- The full odd series has the actual arcsine derivative throughout the open unit interval. -/
theorem hasDerivAt_scalarArcsineSeries (t : ℝ) (ht : |t| < 1) :
    HasDerivAt scalarArcsineSeries (1/Real.sqrt (1-t^2)) t := by
  obtain ⟨q,htq,hq⟩ := exists_between ht
  have hq0 : 0 < q := lt_of_le_of_lt (abs_nonneg t) htq
  have hq2 : |q^2| < 1 := by rw [abs_pow,abs_of_pos hq0]; nlinarith
  have hu : Summable (fun n : ℕ => (q^2)^n) := summable_geometric_of_abs_lt_one hq2
  have hd (n : ℕ) (y : ℝ) : HasDerivAt
      (fun x : ℝ => scalarArcsineCoefficient n*x^(2*n+1))
      ((Nat.centralBinom n:ℝ)/4^n*y^(2*n)) y := by
    have hh := ((hasDerivAt_id y).pow (2*n+1)).const_mul (scalarArcsineCoefficient n)
    simp only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,mul_one] at hh
    rw [←mul_assoc,coefficient_derivative] at hh
    exact hh
  have hb (n : ℕ) (y : ℝ) (hy : y ∈ Set.Ioo (-q) q) :
      ‖(Nat.centralBinom n:ℝ)/4^n*y^(2*n)‖ ≤ (q^2)^n := by
    have hyq : |y| ≤ q := (abs_lt.mpr hy).le
    have hc : (Nat.centralBinom n:ℝ)/4^n ≤ 1 := by
      apply (div_le_one (by positivity)).2
      exact_mod_cast Nat.centralBinom_le_four_pow n
    rw [Real.norm_eq_abs,abs_mul,abs_div,abs_of_nonneg (Nat.cast_nonneg _),
      abs_of_pos (by positivity : (0:ℝ)<4^n),abs_pow]
    calc
      _ ≤ 1*q^(2*n) := mul_le_mul hc (pow_le_pow_left₀ (abs_nonneg y) hyq _) (by positivity) (by norm_num)
      _ = _ := by rw [one_mul,pow_mul]
  have hz : Summable (fun n : ℕ => scalarArcsineCoefficient n*(0:ℝ)^(2*n+1)) := by simp
  have hh := hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo (convex_Ioo (-q) q).isPreconnected
    (fun n y _ => hd n y) hb (show (0:ℝ) ∈ Set.Ioo (-q) q by constructor <;> linarith) hz
    (show t ∈ Set.Ioo (-q) q from abs_lt.mp htq)
  rw [(centralBinom_hasSum_inv_sqrt t ht).tsum_eq] at hh
  exact hh

/-- The entire literal coefficient series is the actual real arcsine. -/
theorem scalarArcsineSeries_eq_arcsin (t : ℝ) (ht : |t| < 1) :
    scalarArcsineSeries t=Real.arcsin t := by
  have hd (x : ℝ) (hx : x ∈ Set.Ioo (-1:ℝ) 1) :=
    hasDerivAt_scalarArcsineSeries x (abs_lt.mpr hx)
  have ha (x : ℝ) (hx : x ∈ Set.Ioo (-1:ℝ) 1) :=
    Real.hasDerivAt_arcsin (ne_of_gt hx.1) (ne_of_lt hx.2)
  have hz : scalarArcsineSeries 0=Real.arcsin 0 := by
    simp [scalarArcsineSeries]
  exact isOpen_Ioo.eqOn_of_deriv_eq (convex_Ioo (-1:ℝ) 1).isPreconnected
    (fun x hx => (hd x hx).differentiableAt.differentiableWithinAt)
    (fun x hx => (ha x hx).differentiableAt.differentiableWithinAt)
    (fun x hx => (hd x hx).deriv.trans (ha x hx).deriv.symm)
    (show (0:ℝ) ∈ Set.Ioo (-1:ℝ) 1 by constructor <;> norm_num) hz (abs_lt.mp ht)

/-- The literal arcsine series recovers the physical coordinate throughout
its strictly interior quarter-cell, with the exact two-pi normalization. -/
theorem scalarArcsineSeries_sin_coordinate (x : ℝ) (hx : |x| < 1/4) :
    scalarArcsineSeries (Real.sin (2*Real.pi*x))/(2*Real.pi)=x := by
  have hx' := abs_lt.mp hx
  have hangle : -(Real.pi/2) < 2*Real.pi*x ∧ 2*Real.pi*x < Real.pi/2 := by
    constructor <;> nlinarith [Real.pi_pos]
  have hs : |Real.sin (2*Real.pi*x)| < 1 := by
    have hc := Real.cos_pos_of_mem_Ioo hangle
    have hsq := Real.sin_sq_add_cos_sq (2*Real.pi*x)
    rw [abs_lt]
    constructor <;> nlinarith [sq_nonneg (Real.sin (2*Real.pi*x)+1),sq_nonneg (Real.sin (2*Real.pi*x)-1)]
  rw [scalarArcsineSeries_eq_arcsin _ hs,Real.arcsin_sin hangle.1.le hangle.2.le]
  field_simp

/-- Absolute summability of the full coefficient factor on the open unit disk. -/
theorem scalarArcsineCoefficient_norm_summable (z : ℂ) (hz : ‖z‖ < 1) :
    Summable (fun n => ‖(scalarArcsineCoefficient n : ℂ)*z^n‖) := by
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) _
    (summable_geometric_of_lt_one (norm_nonneg z) hz)
  intro n
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (scalarArcsineCoefficient_nonneg n)]
  exact mul_le_of_le_one_left (by positivity) (scalarArcsineCoefficient_le_one n)

/-- The complex coefficient is precisely the central choose expression used
by the bounded coordinate operator. -/
theorem scalarArcsineCoefficient_complex (n : ℕ) :
    (scalarArcsineCoefficient n : ℂ)=
      (Nat.choose (2*n) n : ℂ)/(4^n*(2*n+1)) := by
  unfold scalarArcsineCoefficient Nat.centralBinom
  push_cast
  rfl

/-- Uniform unit bound for the literal complex coefficient sequence. -/
theorem scalarArcsineCoefficient_complex_norm_le_one (n : ℕ) :
    ‖(Nat.choose (2*n) n : ℂ)/(4^n*(2*n+1))‖ ≤ 1 := by
  rw [←scalarArcsineCoefficient_complex,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (scalarArcsineCoefficient_nonneg n)]
  exact scalarArcsineCoefficient_le_one n

/-- The full complex factor series recovers arcsine without any finite cutoff. -/
theorem scalarArcsineFactor_identity (t : ℝ) (ht : |t| < 1) :
    (t : ℂ)*(∑' n, (scalarArcsineCoefficient n : ℂ)*((t:ℂ)^2)^n)=
      (Real.arcsin t : ℂ) := by
  have ht' : ‖(t:ℂ)^2‖ < 1 := by
    rw [norm_pow,Complex.norm_real,Real.norm_eq_abs]
    nlinarith [abs_nonneg t]
  have hs := (scalarArcsineCoefficient_norm_summable ((t:ℂ)^2) ht').of_norm
  have he : (fun n : ℕ => (t:ℂ)*((scalarArcsineCoefficient n:ℂ)*((t:ℂ)^2)^n))=
      (fun n => ((scalarArcsineCoefficient n*t^(2*n+1):ℝ):ℂ)) := by
    funext n
    push_cast
    rw [pow_succ _ (2*n),pow_mul]
    ring
  have hr : Summable (fun n => scalarArcsineCoefficient n*t^(2*n+1)) := by
    have hh := hs.mul_left (t:ℂ)
    rw [he] at hh
    simpa only [Complex.reCLM_apply,Complex.ofReal_re] using (Complex.reCLM.hasSum hh.hasSum).summable
  rw [←hs.tsum_mul_left,he]
  have hh := (Complex.ofRealCLM.hasSum hr.hasSum).tsum_eq
  change (∑' n, ((scalarArcsineCoefficient n*t^(2*n+1):ℝ):ℂ))=(scalarArcsineSeries t:ℂ) at hh
  rw [scalarArcsineSeries_eq_arcsin t ht] at hh
  exact hh

/-- Exact scalar coordinate formula matching the infinite operator factor h(Tsin²). -/
theorem scalarArcsineFactor_sin_coordinate (x : ℝ) (hx : |x| < 1/4) :
    (2*Real.pi : ℂ)⁻¹*(Real.sin (2*Real.pi*x):ℂ)*
      (∑' n, (scalarArcsineCoefficient n:ℂ)*((Real.sin (2*Real.pi*x):ℂ)^2)^n)=(x:ℂ) := by
  have hx' := abs_lt.mp hx
  have ha : -(Real.pi/2) < 2*Real.pi*x ∧ 2*Real.pi*x < Real.pi/2 := by
    constructor <;> nlinarith [Real.pi_pos]
  have hs : |Real.sin (2*Real.pi*x)| < 1 := by
    have hc := Real.cos_pos_of_mem_Ioo ha
    have hsq := Real.sin_sq_add_cos_sq (2*Real.pi*x)
    rw [abs_lt]
    constructor <;> nlinarith [sq_nonneg (Real.sin (2*Real.pi*x)+1),sq_nonneg (Real.sin (2*Real.pi*x)-1)]
  rw [mul_assoc,scalarArcsineFactor_identity _ hs,Real.arcsin_sin ha.1.le ha.2.le]
  push_cast
  have hp : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

end
end MeyerGeneralProblem.Adaptive
