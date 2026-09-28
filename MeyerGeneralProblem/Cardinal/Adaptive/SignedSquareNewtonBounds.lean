module

public import MeyerGeneralProblem.Cardinal.Adaptive.SignedNewtonChart
public import MeyerGeneralProblem.Cardinal.Adaptive.LowOrderNewtonBounds

@[expose] public section

/-! # Actual finite-smoothness parity coefficients at square nodes -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open Set

/-- The fixed bounded chart is odd, including outside its identity interval. -/
theorem signedNewtonChart_neg (w : ℝ) : signedNewtonChart (-w)= -signedNewtonChart w := by
  simp [signedNewtonChart,signedChartCoordinate,signedChartBump.neg,Real.arcsin_neg,neg_div]

/-- The exact inverse-sine chart returns the tested sine coordinate. -/
theorem sin_signedNewtonChart (w : ℝ) (hw : |w| ≤ 1/2) :
    Real.sin (Real.pi*signedNewtonChart w)=w := by
  rw [signedNewtonChart_eq w hw,mul_div_cancel₀ _ Real.pi_ne_zero]
  apply Real.sin_arcsin <;> have hh := abs_le.mp hw <;> linarith [hh.1,hh.2]

/-- Literal finite quotient values on the square coordinate; no smooth extension
at zero is assumed or required. -/
def squareParityGridQuotient (odd : Bool) (f : ℝ → ℂ) (u : ℝ) : ℂ :=
  parityGridQuotient odd f (signedNewtonChart (Real.sqrt u))

/-- Taking a square does not change the finite parity quotient data. -/
theorem squareParityGridQuotient_sq (odd : Bool) (f : ℝ → ℂ) (w : ℝ) :
    squareParityGridQuotient odd f (w^2)=parityGridQuotient odd f (signedNewtonChart w) := by
  rw [squareParityGridQuotient,Real.sqrt_sq_eq_abs]
  by_cases hw : 0 ≤ w
  · rw [abs_of_nonneg hw]
  · rw [abs_of_neg (lt_of_not_ge hw),signedNewtonChart_neg,parityGridQuotient_neg]

/-- The even square quotient is the actual smooth signed trace at either sign. -/
theorem squareParityGridQuotient_even_trace (f : ℝ → ℂ) (w : ℝ) :
    squareParityGridQuotient false f (w^2)=signedNewtonChartTrace false f w := by
  rw [squareParityGridQuotient_sq]
  simp only [parityGridQuotient,Bool.false_eq_true,false_and,ite_false,
    signedNewtonChartTrace,signedNewtonChartWeight,parityTrigFactor]
  rw [div_eq_mul_inv,mul_comm]

/-- Multiplication by the signed coordinate recovers the odd smooth trace,
including zero; only tested values enter the identity. -/
theorem squareParityGridQuotient_odd_trace (f : ℝ → ℂ) (w : ℝ) (hw : |w| ≤ 1/2) :
    squareParityGridQuotient true f (w^2)*(w:ℂ)=signedNewtonChartTrace true f w := by
  rw [squareParityGridQuotient_sq]
  have hnz : ¬(true ∧ signedNewtonChart w=0) → parityTrigFactor true (signedNewtonChart w) ≠ 0 := by
    intro hh
    simp only [parityTrigFactor,ite_true,sin_signedNewtonChart w hw]
    have hwne : w ≠ 0 := by
      intro hz
      apply hh
      simp [hz,signedNewtonChart,signedChartCoordinate]
    exact_mod_cast hwne
  have he := parityGridQuotient_reconstruct true f (signedNewtonChart w) hnz
  simp only [parityTrigFactor,ite_true,sin_signedNewtonChart w hw] at he
  simpa only [signedNewtonChartTrace,signedNewtonChartWeight,ite_true,one_mul,mul_comm] using he

/-- Uniform finite-smoothness coefficients for the even parity, including a
terminal zero and arbitrary interpolation order. -/
theorem exists_even_square_Newton_bound (L : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ r : ℕ → ℝ,
      (∀ j ≤ n, 0 ≤ r j) →
      (∀ i j, i < j → j ≤ n → r j < r i) →
      (∀ j < n, r (j+1)^2 ≤ r j^2/2) → r 0 ≤ 1/2 →
      ∀ f : ℝ → ℂ, ContDiff ℝ (2*L+1) f → ∀ A : ℝ, 0 ≤ A →
      (∀ m ≤ 2*L+1, ∀ x ∈ Icc (-1/2:ℝ) (1/2), ‖iteratedDeriv m f x‖ ≤ A) →
      ‖analyticDividedDifference (fun j => r j^2) n (squareParityGridQuotient false f)‖ ≤
        4^n*(C*A)/(∏ j ∈ Finset.range (n-L), r j^2) := by
  obtain ⟨C,hC,hbound⟩ := exists_signedNewtonChartTrace_derivative_bound false (2*L+1)
  refine ⟨C,hC,?_⟩
  intro n r hnonneg hanti hratio hr f hf A hA hder
  apply norm_dividedDifference_decreasing_of_low_order L n (fun j => r j^2)
    (fun j _ => sq_nonneg _) (by
      intro i j hij hj
      have hi := hnonneg i (by omega)
      have h := hanti i j hij hj
      have hjp := hnonneg j hj
      nlinarith) hratio _ (C*A) (by positivity)
  intro a k hak hk
  have hupper (j : ℕ) (hj : j ≤ n) : r j ≤ 1/2 := by
    by_cases hj0 : j=0
    · simpa [hj0] using hr
    · exact (hanti 0 j (by omega) hj).le.trans hr
  have hvalue (j : ℕ) (hj : j ≤ 2*k) : signedNewtonChartTrace false f (signedNewtonNode (fun i => r (a+i)) j)=
      squareParityGridQuotient false f (r (a+j/2)^2) := by
    rw [← squareParityGridQuotient_even_trace,signedNewtonNode_sq]
  have hb := norm_square_dividedDifference_even (fun j => r (a+j)) k
    (fun j hj => hnonneg (a+j) (by omega))
    (fun i j hij hj => hanti (a+i) (a+j) (by omega) (by omega))
    (squareParityGridQuotient false f) (signedNewtonChartTrace false f) hvalue
    ((signedNewtonChartTrace_contDiff false f (2*L+1) hf).of_le (by exact_mod_cast (show 2*k ≤ 2*L+1 by omega))) (C*A)
    (fun x hx => hbound f hf A hA hder (2*k) (by omega) x (by
      have hu := hupper a (by omega)
      simp only [Nat.add_zero] at hx
      constructor <;> linarith [hx.1,hx.2]))
  have hfact : (1:ℝ) ≤ (2*k).factorial := by exact_mod_cast (Nat.factorial_pos (2*k))
  exact hb.trans (div_le_self (by positivity) hfact)

/-- Uniform finite-smoothness coefficients for the odd parity at strictly
positive radii and arbitrary interpolation order. -/
theorem exists_odd_square_Newton_bound (L : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ r : ℕ → ℝ,
      (∀ j ≤ n, 0 < r j) →
      (∀ i j, i < j → j ≤ n → r j < r i) →
      (∀ j < n, r (j+1)^2 ≤ r j^2/2) → r 0 ≤ 1/2 →
      ∀ f : ℝ → ℂ, ContDiff ℝ (2*L+1) f → ∀ A : ℝ, 0 ≤ A →
      (∀ m ≤ 2*L+1, ∀ x ∈ Icc (-1/2:ℝ) (1/2), ‖iteratedDeriv m f x‖ ≤ A) →
      ‖analyticDividedDifference (fun j => r j^2) n (squareParityGridQuotient true f)‖ ≤
        4^n*(C*A)/(∏ j ∈ Finset.range (n-L), r j^2) := by
  obtain ⟨C,hC,hbound⟩ := exists_signedNewtonChartTrace_derivative_bound true (2*L+1)
  refine ⟨C,hC,?_⟩
  intro n r hnonneg hanti hratio hr f hf A hA hder
  apply norm_dividedDifference_decreasing_of_low_order L n (fun j => r j^2)
    (fun j _ => sq_nonneg _) (by
      intro i j hij hj
      have hi := hnonneg i (by omega)
      have h := hanti i j hij hj
      have hjp := hnonneg j hj
      nlinarith) hratio _ (C*A) (by positivity)
  intro a k hak hk
  have hupper (j : ℕ) (hj : j ≤ n) : r j ≤ 1/2 := by
    by_cases hj0 : j=0
    · simpa [hj0] using hr
    · exact (hanti 0 j (by omega) hj).le.trans hr
  have hvalue (j : ℕ) (hj : j ≤ 2*k+1) : signedNewtonChartTrace true f (signedNewtonNode (fun i => r (a+i)) j)=
      squareParityGridQuotient true f (r (a+j/2)^2)*(signedNewtonNode (fun i => r (a+i)) j:ℂ) := by
    have hw := signedNewtonNode_mem_Icc (fun i => r (a+i)) k j
      (fun i hi => (hnonneg (a+i) (by omega)).le)
      (fun i l hil hl => hanti (a+i) (a+l) (by omega) (by omega)) (by omega)
    have hu := hupper a (by omega)
    simp only [Nat.add_zero] at hw
    rw [← squareParityGridQuotient_odd_trace f _ (abs_le.mpr ⟨by linarith [hw.1],by linarith [hw.2]⟩),signedNewtonNode_sq]

  have hb := norm_square_dividedDifference_odd (fun j => r (a+j)) k
    (fun j hj => hnonneg (a+j) (by omega))
    (fun i j hij hj => hanti (a+i) (a+j) (by omega) (by omega))
    (squareParityGridQuotient true f) (signedNewtonChartTrace true f) hvalue
    ((signedNewtonChartTrace_contDiff true f (2*L+1) hf).of_le (by exact_mod_cast (show 2*k+1 ≤ 2*L+1 by omega))) (C*A)
    (fun x hx => hbound f hf A hA hder (2*k+1) (by omega) x (by
      have hu := hupper a (by omega)
      simp only [Nat.add_zero] at hx
      constructor <;> linarith [hx.1,hx.2]))
  have hfact : (1:ℝ) ≤ (2*k+1).factorial := by exact_mod_cast (Nat.factorial_pos (2*k+1))
  exact hb.trans (div_le_self (by positivity) hfact)

end
end MeyerGeneralProblem.Adaptive
