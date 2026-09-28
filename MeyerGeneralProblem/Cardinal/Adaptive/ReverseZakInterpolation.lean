module

public import MeyerGeneralProblem.Cardinal.Adaptive.ReverseZakChart
public import MeyerGeneralProblem.Cardinal.Adaptive.RapidAdmissionSeries

@[expose] public section

/-! Actual rapid-grid interpolation of the reverse Zak chart in the original norm. -/

noncomputable section
open scoped BigOperators ContDiff

namespace MeyerGeneralProblem.Adaptive

/-- The exact rapid-grid coefficients of the reverse Zak chart obey the
admission estimate in the original order `2*L+2`, uniformly in the finite cap. -/
theorem exists_reverseZak_rapidGridCoefficient_bound (e d : Bool) (L : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ P R : ℕ, ∀ hP : 1 ≤ P, ∀ hR : 1 ≤ R, ∀ k : ℕ,
      ∀ f : SchwartzMap ℝ ℂ, ∀ i j : Fin (k+1),
      ‖rapidGridCoefficient P R hP hR k e d (reverseZakChart f) i j‖ ≤
        4^(i.val+j.val)*(C*‖schwartzToHermiteScale (2*L+2) f‖)/
          (rapidCharacteristicProduct P R (i.val-L)*rapidCharacteristicProduct P R (j.val-L)) := by
  have horder (N : ℕ) : (N : ℕ∞ω) ≤ ∞ := by
    exact_mod_cast (le_top : (N : ℕ∞) ≤ ⊤)
  obtain ⟨A,hA,ha⟩ := exists_rapidGridCoefficient_bound e d L
  obtain ⟨B,hB,hb⟩ := exists_reverseZakChart_mixed_bound (2*L+1)
  refine ⟨A*B,by positivity,?_⟩
  intro P R hP hR k f i j
  have hfx (y : ℝ) : ContDiff ℝ (2*L+1) (fun x => reverseZakChart f x y) := by
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,reverseZakChart] using
      (reverseZakJet_contDiff_x f 0 0 y).of_le (horder (2*L+1))
  have hfxy (a : ℕ) (_ha : a ≤ 2*L+1) (x : ℝ) : ContDiff ℝ (2*L+1)
      (fun y => iteratedDeriv a (fun x => reverseZakChart f x y) x) := by
    simpa only [reverseZakChart,iteratedDeriv_reverseZakJet_x,zero_add,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] using
      (reverseZakJet_contDiff_y f a 0 x).of_le (horder (2*L+1))
  have hbound := ha P R hP hR k (reverseZakChart f) hfx hfxy
    (B*‖schwartzToHermiteScale (2*L+2) f‖) (by positivity)
    (by
      intro a ha b hb' x hx y _hy
      simpa only [show 2*L+1+1=2*L+2 by omega] using
        hb f a b ha hb' x y (abs_le.mpr ⟨by linarith [hx.1],by linarith [hx.2]⟩)) i j
  rw [rapidGrid_prefix_product_eq P R k (i.val-L) (by omega),
    rapidGrid_prefix_product_eq P R k (j.val-L) (by omega)] at hbound
  simpa only [mul_assoc] using hbound

end MeyerGeneralProblem.Adaptive
