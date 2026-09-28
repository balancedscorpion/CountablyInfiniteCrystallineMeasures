module

public import MeyerGeneralProblem.Cardinal.Adaptive.FixedZakGauge
public import MeyerGeneralProblem.Cardinal.Adaptive.ReverseZakInterpolation

@[expose] public section

/-! Fixed-gauge transfer of the exact original-native reverse Zak estimate. -/

noncomputable section
open scoped BigOperators ContDiff

namespace MeyerGeneralProblem.Adaptive

private theorem finite_order_le_infty (N : ℕ) : (N : ℕ∞ω) ≤ ∞ := by
  exact_mod_cast (le_top : (N : ℕ∞) ≤ ⊤)

/-- The literal compact-chart gauge times the actual reverse Zak test. -/
def gaugedReverseZakChart (f : SchwartzMap ℝ ℂ) (x y : ℝ) : ℂ :=
  fixedZakGauge x y * reverseZakChart f x y

/-- Smooth mixed sections are preserved by the literal product. -/
theorem mixed_product_contDiff_y (g f : ℝ → ℝ → ℂ)
    (hgx : ∀ y, ContDiff ℝ ∞ (fun x => g x y))
    (hfx : ∀ y, ContDiff ℝ ∞ (fun x => f x y))
    (hgy : ∀ a x, ContDiff ℝ ∞ (fun y => iteratedDeriv a (fun x => g x y) x))
    (hfy : ∀ a x, ContDiff ℝ ∞ (fun y => iteratedDeriv a (fun x => f x y) x))
    (a : ℕ) (x : ℝ) :
    ContDiff ℝ ∞ (fun y => iteratedDeriv a (fun u => g u y*f u y) x) := by
  have he (y : ℝ) := iteratedDeriv_fun_mul
    ((hgx y).of_le (finite_order_le_infty a)).contDiffAt
    ((hfx y).of_le (finite_order_le_infty a)).contDiffAt (x := x)
  simp_rw [he]
  apply ContDiff.sum
  intro i hi
  exact (contDiff_const.mul (hgy i x)).mul (hfy (a-i) x)

/-- Exact finite-order mixed Leibniz bound, retaining the declared derivatives only. -/
theorem norm_mixed_product_le (g f : ℝ → ℝ → ℂ)
    (hgx : ∀ y, ContDiff ℝ ∞ (fun x => g x y))
    (hfx : ∀ y, ContDiff ℝ ∞ (fun x => f x y))
    (hgy : ∀ a x, ContDiff ℝ ∞ (fun y => iteratedDeriv a (fun x => g x y) x))
    (hfy : ∀ a x, ContDiff ℝ ∞ (fun y => iteratedDeriv a (fun x => f x y) x))
    (N a b : ℕ) (ha : a ≤ N) (hb : b ≤ N) (x y A B : ℝ) (hA : 0 ≤ A) (_hB : 0 ≤ B)
    (hg : ∀ i ≤ N, ∀ j ≤ N,
      ‖iteratedDeriv j (fun v => iteratedDeriv i (fun u => g u v) x) y‖ ≤ A)
    (hf : ∀ i ≤ N, ∀ j ≤ N,
      ‖iteratedDeriv j (fun v => iteratedDeriv i (fun u => f u v) x) y‖ ≤ B) :
    ‖iteratedDeriv b (fun v => iteratedDeriv a (fun u => g u v*f u v) x) y‖ ≤
      (∑ i ∈ Finset.range (a+1), (a.choose i:ℝ))*
      (∑ j ∈ Finset.range (b+1), (b.choose j:ℝ))*A*B := by
  have he (v : ℝ) := iteratedDeriv_fun_mul
    ((hgx v).of_le (finite_order_le_infty a)).contDiffAt
    ((hfx v).of_le (finite_order_le_infty a)).contDiffAt (x := x)
  simp_rw [he]
  rw [iteratedDeriv_fun_sum (fun i hi =>
    (((contDiff_const.mul (hgy i x)).mul (hfy (a-i) x)).of_le
      (finite_order_le_infty b)).contDiffAt)]
  apply (norm_sum_le _ _).trans
  have hterm (i : ℕ) (hi : i ∈ Finset.range (a+1)) :
      ‖iteratedDeriv b (fun v => (a.choose i:ℂ)*iteratedDeriv i (fun u => g u v) x *
        iteratedDeriv (a-i) (fun u => f u v) x) y‖ ≤
      (a.choose i:ℝ)*((∑ j ∈ Finset.range (b+1), (b.choose j:ℝ))*A*B) := by
    have hiN : i ≤ N := by have := Finset.mem_range.mp hi; omega
    have haiN : a-i ≤ N := by omega
    have hp := norm_iteratedFDeriv_mul_le
      ((hgy i x).of_le (finite_order_le_infty b))
      ((hfy (a-i) x).of_le (finite_order_le_infty b)) y (by exact_mod_cast (le_refl b))
    simp only [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hp
    have hp' : ‖iteratedDeriv b (fun v => iteratedDeriv i (fun u => g u v) x *
        iteratedDeriv (a-i) (fun u => f u v) x) y‖ ≤
        (∑ j ∈ Finset.range (b+1), (b.choose j:ℝ))*A*B := by
      apply hp.trans
      calc
        _ ≤ ∑ j ∈ Finset.range (b+1), (b.choose j:ℝ)*A*B := by
          apply Finset.sum_le_sum
          intro j hj
          have hjN : j ≤ N := by have := Finset.mem_range.mp hj; omega
          have hbjN : b-j ≤ N := by omega
          gcongr
          · exact hg i hiN j hjN
          · exact hf (a-i) haiN (b-j) hbjN
        _ = _ := by rw [Finset.sum_mul,Finset.sum_mul]
    simp_rw [mul_assoc]
    rw [iteratedDeriv_const_mul_field,norm_mul,Complex.norm_natCast]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hp' (by positivity : 0 ≤ (a.choose i:ℝ))
  calc
    _ ≤ ∑ i ∈ Finset.range (a+1), (a.choose i:ℝ)*
      ((∑ j ∈ Finset.range (b+1), (b.choose j:ℝ))*A*B) := Finset.sum_le_sum hterm
    _ = _ := by rw [← Finset.sum_mul]; ring

private theorem fixedZakGauge_contDiff_x (y : ℝ) : ContDiff ℝ ∞ (fun x => fixedZakGauge x y) := by
  unfold fixedZakGauge
  exact ((contDiff_const.mul (show ContDiff ℝ ∞ (fun x : ℝ => (x:ℂ)) from
    Complex.ofRealCLM.contDiff)).mul contDiff_const).cexp

private theorem reverseZakChart_contDiff_mixed (f : SchwartzMap ℝ ℂ) (a : ℕ) (x : ℝ) :
    ContDiff ℝ ∞ (fun y => iteratedDeriv a (fun x => reverseZakChart f x y) x) := by
  simpa only [reverseZakChart,iteratedDeriv_reverseZakJet_x,zero_add] using
    reverseZakJet_contDiff_y f a 0 x

/-- The literal gauged reverse chart is smooth in its first coordinate. -/
theorem gaugedReverseZakChart_contDiff_x (f : SchwartzMap ℝ ℂ) (y : ℝ) :
    ContDiff ℝ ∞ (fun x => gaugedReverseZakChart f x y) :=
  (fixedZakGauge_contDiff_x y).mul (reverseZakJet_contDiff_x f 0 0 y)

/-- Every actual spatial derivative of the gauged chart is smooth in the
second coordinate, as required by finite tensor interpolation. -/
theorem gaugedReverseZakChart_contDiff_mixed (f : SchwartzMap ℝ ℂ) (a : ℕ) (x : ℝ) :
    ContDiff ℝ ∞ (fun y => iteratedDeriv a (fun x => gaugedReverseZakChart f x y) x) :=
  mixed_product_contDiff_y fixedZakGauge (reverseZakChart f) fixedZakGauge_contDiff_x
    (reverseZakJet_contDiff_x f 0 0) fixedZakGauge_mixed_contDiff
    (reverseZakChart_contDiff_mixed f) a x

/-- Multiplying by the actual fixed gauge preserves the sharp original order:
all mixed derivatives through `N` cost exactly `H_(N+1)`. -/
theorem exists_gaugedReverseZakChart_mixed_bound (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : SchwartzMap ℝ ℂ) (a b : ℕ), a ≤ N → b ≤ N →
      ∀ x ∈ Set.Icc (-1/2:ℝ) (1/2), ∀ y ∈ Set.Icc (-1/2:ℝ) (1/2),
      ‖iteratedDeriv b (fun v => iteratedDeriv a (fun u => gaugedReverseZakChart f u v) x) y‖ ≤
        C*‖schwartzToHermiteScale (N+1) f‖ := by
  obtain ⟨A,hA,hg⟩ := exists_fixedZakGauge_mixed_bound N
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
  have hh := norm_mixed_product_le fixedZakGauge (reverseZakChart f)
    fixedZakGauge_contDiff_x (reverseZakJet_contDiff_x f 0 0)
    fixedZakGauge_mixed_contDiff (reverseZakChart_contDiff_mixed f)
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
theorem exists_gaugedReverseZak_rapidGridCoefficient_bound (e d : Bool) (L : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ P R : ℕ, ∀ hP : 1 ≤ P, ∀ hR : 1 ≤ R, ∀ k : ℕ,
      ∀ f : SchwartzMap ℝ ℂ, ∀ i j : Fin (k+1),
      ‖rapidGridCoefficient P R hP hR k e d (gaugedReverseZakChart f) i j‖ ≤
        4^(i.val+j.val)*(C*‖schwartzToHermiteScale (2*L+2) f‖)/
          (rapidCharacteristicProduct P R (i.val-L)*rapidCharacteristicProduct P R (j.val-L)) := by
  obtain ⟨A,hA,ha⟩ := exists_rapidGridCoefficient_bound e d L
  obtain ⟨B,hB,hb⟩ := exists_gaugedReverseZakChart_mixed_bound (2*L+1)
  refine ⟨A*B,by positivity,?_⟩
  intro P R hP hR k f i j
  have hfx (y : ℝ) : ContDiff ℝ (2*L+1) (fun x => gaugedReverseZakChart f x y) := by
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] using
      (gaugedReverseZakChart_contDiff_x f y).of_le (finite_order_le_infty (2*L+1))
  have hfxy (a : ℕ) (_ha : a ≤ 2*L+1) (x : ℝ) : ContDiff ℝ (2*L+1)
      (fun y => iteratedDeriv a (fun x => gaugedReverseZakChart f x y) x) := by
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] using
      (gaugedReverseZakChart_contDiff_mixed f a x).of_le (finite_order_le_infty (2*L+1))
  have hbound := ha P R hP hR k (gaugedReverseZakChart f) hfx hfxy
    (B*‖schwartzToHermiteScale (2*L+2) f‖) (by positivity)
    (by
      intro a ha b hb' x hx y hy
      simpa only [show 2*L+1+1=2*L+2 by omega] using hb f a b ha hb' x hx y hy) i j
  rw [rapidGrid_prefix_product_eq P R k (i.val-L) (by omega),
    rapidGrid_prefix_product_eq P R k (j.val-L) (by omega)] at hbound
  simpa only [mul_assoc] using hbound

end MeyerGeneralProblem.Adaptive
