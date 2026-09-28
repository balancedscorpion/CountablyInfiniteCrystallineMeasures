module

public import MeyerGeneralProblem.Cardinal.Adaptive.GaugedReverseZak

@[expose] public section

/-! Reverse Zak transfer in the literal linear HalfNewton coordinate convention. -/

noncomputable section
open scoped BigOperators ContDiff

namespace MeyerGeneralProblem.Adaptive

private theorem finite_order_le_infty (N : ℕ) : (N : ℕ∞ω) ≤ ∞ := by
  exact_mod_cast (le_top : (N : ℕ∞) ≤ ⊤)

/-- The inverse of the literal linear character weight in HalfNewton coordinates. -/
def halfCoordinateGauge (x y : ℝ) : ℂ :=
  Complex.exp (-(Real.pi:ℂ)*Complex.I*x)*Complex.exp ((Real.pi:ℂ)*Complex.I*y)

/-- Unit modulus of the actual linear half-coordinate gauge. -/
theorem halfCoordinateGauge_norm (x y : ℝ) : ‖halfCoordinateGauge x y‖=1 := by
  simp [halfCoordinateGauge,Complex.norm_exp,Complex.mul_re,Complex.mul_im]

/-- Exact spatial derivatives of the actual half-coordinate gauge. -/
theorem iteratedDeriv_halfCoordinateGauge_x (a : ℕ) (y : ℝ) :
    iteratedDeriv a (fun x => halfCoordinateGauge x y) =
      fun x => (-(Real.pi:ℂ)*Complex.I)^a*halfCoordinateGauge x y := by
  funext x
  unfold halfCoordinateGauge
  rw [iteratedDeriv_mul_const_field,iteratedDeriv_exp_real_linear]
  simp only [mul_assoc]

/-- Exact mixed derivatives; the multiplier costs no test-function derivative. -/
theorem halfCoordinateGauge_mixed_derivative (a b : ℕ) (x y : ℝ) :
    iteratedDeriv b (fun v => iteratedDeriv a (fun u => halfCoordinateGauge u v) x) y =
      (-(Real.pi:ℂ)*Complex.I)^a*((Real.pi:ℂ)*Complex.I)^b*halfCoordinateGauge x y := by
  simp_rw [iteratedDeriv_halfCoordinateGauge_x]
  simp only [halfCoordinateGauge,← mul_assoc]
  rw [iteratedDeriv_const_mul_field,iteratedDeriv_exp_real_linear]
  ring

/-- Smoothness in the spatial variable of the fixed linear multiplier. -/
theorem halfCoordinateGauge_contDiff_x (y : ℝ) : ContDiff ℝ ∞ (fun x => halfCoordinateGauge x y) := by
  exact ((contDiff_const.mul (show ContDiff ℝ ∞ (fun x : ℝ => (x:ℂ)) from
    Complex.ofRealCLM.contDiff)).cexp).mul contDiff_const

/-- Smoothness of every mixed section of the fixed linear multiplier. -/
theorem halfCoordinateGauge_mixed_contDiff (a : ℕ) (x : ℝ) :
    ContDiff ℝ ∞ (fun y => iteratedDeriv a (fun x => halfCoordinateGauge x y) x) := by
  simp_rw [iteratedDeriv_halfCoordinateGauge_x]
  simp only [halfCoordinateGauge,← mul_assoc]
  exact contDiff_const.mul ((contDiff_const.mul
    (show ContDiff ℝ ∞ (fun y : ℝ => (y:ℂ)) from Complex.ofRealCLM.contDiff)).cexp)

/-- Every declared finite square of derivatives of the literal linear gauge
has a uniform bound on the entire plane. -/
theorem exists_halfCoordinateGauge_mixed_bound (N : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ a ≤ N, ∀ b ≤ N,
      ∀ x ∈ Set.Icc (-1/2:ℝ) (1/2), ∀ y ∈ Set.Icc (-1/2:ℝ) (1/2),
      ‖iteratedDeriv b (fun v => iteratedDeriv a (fun u => halfCoordinateGauge u v) x) y‖ ≤ B := by
  refine ⟨(1+Real.pi)^(2*N),by positivity,?_⟩
  intro a ha b hb x _hx y _hy
  rw [halfCoordinateGauge_mixed_derivative]
  simp only [norm_mul,norm_pow,norm_neg,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos Real.pi_pos,Complex.norm_I,mul_one,halfCoordinateGauge_norm]
  rw [← pow_add]
  exact (pow_le_pow_left₀ Real.pi_pos.le (by linarith) (a+b)).trans
    (pow_le_pow_right₀ (by linarith [Real.pi_pos]) (by omega))

/-- The actual reverse chart matching the literal compact HalfNewton coordinates. -/
def halfCoordinateReverseZakChart (f : SchwartzMap ℝ ℂ) (x y : ℝ) : ℂ :=
  halfCoordinateGauge x y*reverseZakChart f x y

private theorem reverseZakChart_contDiff_mixed (f : SchwartzMap ℝ ℂ) (a : ℕ) (x : ℝ) :
    ContDiff ℝ ∞ (fun y => iteratedDeriv a (fun x => reverseZakChart f x y) x) := by
  simpa only [reverseZakChart,iteratedDeriv_reverseZakJet_x,zero_add] using
    reverseZakJet_contDiff_y f a 0 x

/-- The literal gauged reverse chart is smooth in its first coordinate. -/
theorem halfCoordinateReverseZakChart_contDiff_x (f : SchwartzMap ℝ ℂ) (y : ℝ) :
    ContDiff ℝ ∞ (fun x => halfCoordinateReverseZakChart f x y) :=
  (halfCoordinateGauge_contDiff_x y).mul (reverseZakJet_contDiff_x f 0 0 y)

/-- Every actual spatial derivative of the half-coordinate chart is smooth in the
second coordinate, as required by finite tensor interpolation. -/
theorem halfCoordinateReverseZakChart_contDiff_mixed (f : SchwartzMap ℝ ℂ) (a : ℕ) (x : ℝ) :
    ContDiff ℝ ∞ (fun y => iteratedDeriv a (fun x => halfCoordinateReverseZakChart f x y) x) :=
  mixed_product_contDiff_y halfCoordinateGauge (reverseZakChart f) halfCoordinateGauge_contDiff_x
    (reverseZakJet_contDiff_x f 0 0) halfCoordinateGauge_mixed_contDiff
    (reverseZakChart_contDiff_mixed f) a x

/-- Multiplying by the actual fixed linear gauge preserves the sharp original order:
all mixed derivatives through `N` cost exactly `H_(N+1)`. -/
theorem exists_halfCoordinateReverseZakChart_mixed_bound (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : SchwartzMap ℝ ℂ) (a b : ℕ), a ≤ N → b ≤ N →
      ∀ x ∈ Set.Icc (-1/2:ℝ) (1/2), ∀ y ∈ Set.Icc (-1/2:ℝ) (1/2),
      ‖iteratedDeriv b (fun v => iteratedDeriv a (fun u => halfCoordinateReverseZakChart f u v) x) y‖ ≤
        C*‖schwartzToHermiteScale (N+1) f‖ := by
  obtain ⟨A,hA,hg⟩ := exists_halfCoordinateGauge_mixed_bound N
  obtain ⟨B,hB,hf⟩ := exists_reverseZakChart_mixed_bound N
  let c : ℕ → ℝ := fun a => ∑ i ∈ Finset.range (a+1), (a.choose i:ℝ)
  let D : ℝ := 1+∑ a ∈ Finset.range (N+1), c a
  have hc (a : ℕ) : 0 ≤ c a := Finset.sum_nonneg (fun i hi => by positivity)
  have hD : 0 < D := by dsimp [D]; positivity
  have hcD (a : ℕ) (ha : a ≤ N) : c a ≤ D := by
    have hh := Finset.single_le_sum (fun j _ => hc j)
      (Finset.mem_range.mpr (show a < N+1 by omega))
    dsimp only [D]
    linarith
  refine ⟨D^2*A*B,by positivity,?_⟩
  intro f a b ha hb x hx y hy
  have hh := norm_mixed_product_le halfCoordinateGauge (reverseZakChart f)
    halfCoordinateGauge_contDiff_x (reverseZakJet_contDiff_x f 0 0)
    halfCoordinateGauge_mixed_contDiff (reverseZakChart_contDiff_mixed f)
    N a b ha hb x y A (B*‖schwartzToHermiteScale (N+1) f‖) hA.le (by positivity)
    (fun i hi j hj => hg i hi j hj x hx y hy)
    (fun i hi j hj => hf f i j hi hj x y (abs_le.mpr ⟨by linarith [hx.1],by linarith [hx.2]⟩))
  apply hh.trans
  change c a*c b*A*(B*‖schwartzToHermiteScale (N+1) f‖) ≤ _
  have hp : c a*c b ≤ D^2 := by
    simpa only [pow_two] using mul_le_mul (hcD a ha) (hcD b hb) (hc b) hD.le
  calc
    _ ≤ D^2*A*(B*‖schwartzToHermiteScale (N+1) f‖) := by gcongr
    _ = _ := by ring

/-- The actual gauged reverse chart satisfies rapid-grid interpolation at the
accepted original norm `H_(2*L+2)`, with constants independent of every cap. -/
theorem exists_halfCoordinateReverseZak_rapidGridCoefficient_bound (e d : Bool) (L : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ P R : ℕ, ∀ hP : 1 ≤ P, ∀ hR : 1 ≤ R, ∀ k : ℕ,
      ∀ f : SchwartzMap ℝ ℂ, ∀ i j : Fin (k+1),
      ‖rapidGridCoefficient P R hP hR k e d (halfCoordinateReverseZakChart f) i j‖ ≤
        4^(i.val+j.val)*(C*‖schwartzToHermiteScale (2*L+2) f‖)/
          (rapidCharacteristicProduct P R (i.val-L)*rapidCharacteristicProduct P R (j.val-L)) := by
  obtain ⟨A,hA,ha⟩ := exists_rapidGridCoefficient_bound e d L
  obtain ⟨B,hB,hb⟩ := exists_halfCoordinateReverseZakChart_mixed_bound (2*L+1)
  refine ⟨A*B,by positivity,?_⟩
  intro P R hP hR k f i j
  have hfx (y : ℝ) : ContDiff ℝ (2*L+1) (fun x => halfCoordinateReverseZakChart f x y) := by
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] using
      (halfCoordinateReverseZakChart_contDiff_x f y).of_le (finite_order_le_infty (2*L+1))
  have hfxy (a : ℕ) (_ha : a ≤ 2*L+1) (x : ℝ) : ContDiff ℝ (2*L+1)
      (fun y => iteratedDeriv a (fun x => halfCoordinateReverseZakChart f x y) x) := by
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] using
      (halfCoordinateReverseZakChart_contDiff_mixed f a x).of_le (finite_order_le_infty (2*L+1))
  have hbound := ha P R hP hR k (halfCoordinateReverseZakChart f) hfx hfxy
    (B*‖schwartzToHermiteScale (2*L+2) f‖) (by positivity)
    (by
      intro a ha b hb' x hx y hy
      simpa only [show 2*L+1+1=2*L+2 by omega] using hb f a b ha hb' x hx y hy) i j
  rw [rapidGrid_prefix_product_eq P R k (i.val-L) (by omega),
    rapidGrid_prefix_product_eq P R k (j.val-L) (by omega)] at hbound
  simpa only [mul_assoc] using hbound

end MeyerGeneralProblem.Adaptive
