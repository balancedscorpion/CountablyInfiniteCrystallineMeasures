module

public import MeyerGeneralProblem.Cardinal.Adaptive.CharacteristicNewtonBounds

@[expose] public section

/-! # Mixed finite-smoothness characteristic tensor coefficients -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open Set

/-- The two original test evaluation points for one characteristic quotient. -/
def characteristicEvaluationPoint (z : ℝ) (neg : Bool) : ℝ :=
  if neg then -signedNewtonChart (Real.sqrt (z/2)) else signedNewtonChart (Real.sqrt (z/2))

/-- Fixed finite evaluation weights for the actual quotient, with its prescribed
zero odd endpoint. These weights do not depend on the varying test. -/
def characteristicEvaluationWeight (odd : Bool) (z : ℝ) (neg : Bool) : ℂ :=
  let t := signedNewtonChart (Real.sqrt (z/2))
  if odd ∧ t=0 then 0 else
    (if neg then (if odd then (-1:ℂ) else 1) else 1)/(2*parityTrigFactor odd t)

/-- The actual characteristic quotient is precisely a fixed two-value functional. -/
theorem characteristicParityGridQuotient_eq_sum (odd : Bool) (f : ℝ → ℂ) (z : ℝ) :
    characteristicParityGridQuotient odd f z =
      ∑ neg : Bool, characteristicEvaluationWeight odd z neg*f (characteristicEvaluationPoint z neg) := by
  by_cases hz : odd ∧ signedNewtonChart (Real.sqrt (z/2))=0
  · simp only [characteristicParityGridQuotient,squareParityGridQuotient,parityGridQuotient,
      characteristicEvaluationWeight,hz,and_self,ite_true,zero_mul,Finset.sum_const_zero]
  · simp only [characteristicParityGridQuotient,squareParityGridQuotient,parityGridQuotient,
      characteristicEvaluationWeight,characteristicEvaluationPoint,hz,ite_false,Fintype.sum_bool,
      ite_true,Bool.false_eq_true]
    unfold signParityPiece
    ring

/-- Finite parameter smoothness passes through the actual characteristic quotient. -/
theorem contDiff_characteristicQuotient_parameter (odd : Bool) (z : ℝ) (N : ℕ)
    (f : ℝ → ℝ → ℂ) (hf : ∀ t, ContDiff ℝ N (fun x => f x t)) :
    ContDiff ℝ N (fun x => characteristicParityGridQuotient odd (f x) z) := by
  simp_rw [characteristicParityGridQuotient_eq_sum]
  exact ContDiff.sum (fun neg _ => contDiff_const.mul (hf (characteristicEvaluationPoint z neg)))

/-- Only the declared parameter derivatives pass through the two-value functional. -/
theorem iteratedDeriv_characteristicQuotient_parameter (odd : Bool) (z : ℝ) (r : ℕ)
    (f : ℝ → ℝ → ℂ) (hf : ∀ t, ContDiff ℝ r (fun x => f x t)) (x : ℝ) :
    iteratedDeriv r (fun x => characteristicParityGridQuotient odd (f x) z) x =
      characteristicParityGridQuotient odd (fun t => iteratedDeriv r (fun x => f x t) x) z := by
  have hd (neg : Bool) : ContDiffAt ℝ r
      (fun x => characteristicEvaluationWeight odd z neg*f x (characteristicEvaluationPoint z neg)) x :=
    (contDiff_const.mul (hf (characteristicEvaluationPoint z neg))).contDiffAt
  simp_rw [characteristicParityGridQuotient_eq_sum]
  rw [iteratedDeriv_fun_sum (fun neg _ => hd neg)]
  simp_rw [iteratedDeriv_const_mul_field]

/-- All original evaluation points stay in the same fixed test interval. -/
theorem characteristicEvaluationPoint_mem_Icc (z : ℝ) (neg : Bool) :
    characteristicEvaluationPoint z neg ∈ Icc (-1/2:ℝ) (1/2) := by
  have h := signedNewtonChart_mem_Icc (Real.sqrt (z/2))
  cases neg
  · exact h
  · change -signedNewtonChart (Real.sqrt (z/2)) ∈ _
    constructor <;> linarith [h.1,h.2]

/-- Literal tensor coefficient, applying both actual parity quotient functionals. -/
def characteristicTensorDividedDifference (e d : Bool) (x : ℕ → ℝ) (i : ℕ)
    (y : ℕ → ℝ) (j : ℕ) (f : ℝ → ℝ → ℂ) : ℂ :=
  analyticDividedDifference x i (characteristicParityGridQuotient e
    (fun a => analyticDividedDifference y j (characteristicParityGridQuotient d (f a))))

/-- Actual divided differences commute with the other finite parity functional. -/
theorem characteristicQuotient_dividedDifference_commute (e d : Bool) (x : ℝ)
    (y : ℕ → ℝ) (j : ℕ) (hy : ∀ a ≤ j, ∀ b ≤ j, a ≠ b → y a ≠ y b)
    (f : ℝ → ℝ → ℂ) :
    characteristicParityGridQuotient e
      (fun a => analyticDividedDifference y j (characteristicParityGridQuotient d (f a))) x =
    analyticDividedDifference y j
      (fun v => characteristicParityGridQuotient e (fun a => characteristicParityGridQuotient d (f a) v) x) := by
  rw [characteristicParityGridQuotient_eq_sum e]
  simp_rw [analyticDividedDifference_eq_prefix_weights y j hy]
  simp_rw [characteristicParityGridQuotient_eq_sum e,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro neg _
  ring


/-- Concrete geometric input for one parity prefix: the odd terminal zero is
omitted, while the even prefix may retain it. -/
structure CharacteristicRadiusPrefix (odd : Bool) (n : ℕ) (r : ℕ → ℝ) : Prop where
  nonneg : ∀ j ≤ n, 0 ≤ r j
  decreasing : ∀ i j, i < j → j ≤ n → r j < r i
  squareRatio : ∀ j < n, r (j+1)^2 ≤ r j^2/2
  upper : r 0 ≤ 1/2
  oddPositive : odd=true → ∀ j ≤ n, 0 < r j

/-- The literal characteristic tensor coefficient has the source product bound
with only `2L+1` derivatives in each variable, including both coordinate arms. -/
theorem exists_characteristic_tensor_Newton_bound (e d : Bool) (L : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ i j : ℕ, ∀ x y : ℕ → ℝ,
      CharacteristicRadiusPrefix e i x → CharacteristicRadiusPrefix d j y →
      ∀ f : ℝ → ℝ → ℂ,
      (∀ b, ContDiff ℝ (2*L+1) (fun a => f a b)) →
      (∀ r ≤ 2*L+1, ∀ a, ContDiff ℝ (2*L+1)
        (fun b => iteratedDeriv r (fun a => f a b) a)) →
      ∀ A : ℝ, 0 ≤ A →
      (∀ r ≤ 2*L+1, ∀ q ≤ 2*L+1, ∀ a ∈ Icc (-1/2:ℝ) (1/2),
        ∀ b ∈ Icc (-1/2:ℝ) (1/2),
        ‖iteratedDeriv q (fun b => iteratedDeriv r (fun a => f a b) a) b‖ ≤ A) →
      ‖characteristicTensorDividedDifference e d (fun k => 2*x k^2) i (fun k => 2*y k^2) j f‖ ≤
        4^(i+j)*(C*A)/((∏ k ∈ Finset.range (i-L), 2*x k^2)*(∏ k ∈ Finset.range (j-L), 2*y k^2)) := by
  obtain ⟨Cx,hCx,hxb⟩ := exists_characteristic_Newton_bound e L
  obtain ⟨Cy,hCy,hyb⟩ := exists_characteristic_Newton_bound d L
  refine ⟨Cx*Cy,mul_pos hCx hCy,?_⟩
  intro i j x y hx hy f hfx hfxy A hA hder
  let ys : ℕ → ℝ := fun k => 2*y k^2
  have hyd : ∀ a ≤ j, ∀ b ≤ j, a ≠ b → ys a ≠ ys b := by
    intro a ha b hb hab he
    exact squared_nodes_distinct y j hy.nonneg hy.decreasing a ha b hb hab
      (mul_left_cancel₀ (by norm_num : (2:ℝ) ≠ 0) he)
  let g : ℝ → ℂ := fun a => analyticDividedDifference ys j (characteristicParityGridQuotient d (f a))
  have hg : ContDiff ℝ (2*L+1) g :=
    contDiff_parametric_dividedDifference ys j (2*L+1) hyd
      (fun v a => characteristicParityGridQuotient d (f a) v)
      (fun v => contDiff_characteristicQuotient_parameter d v (2*L+1) f hfx)
  have hp : 0 < ∏ k ∈ Finset.range (j-L), 2*y k^2 := by
    rw [Finset.prod_mul_distrib]
    have h := square_prefix_product_pos y j L hy.nonneg hy.decreasing
    simpa using mul_pos (by positivity : 0 < ∏ _k ∈ Finset.range (j-L), (2:ℝ)) h
  let B : ℝ := 4^j*(Cy*A)/(∏ k ∈ Finset.range (j-L), 2*y k^2)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hgd : ∀ r ≤ 2*L+1, ∀ a ∈ Icc (-1/2:ℝ) (1/2), ‖iteratedDeriv r g a‖ ≤ B := by
    intro r hr a ha
    have he := iteratedDeriv_parametric_dividedDifference ys j r hyd
      (fun v a => characteristicParityGridQuotient d (f a) v)
      (fun v => contDiff_characteristicQuotient_parameter d v r f
        (fun b => (hfx b).of_le (by exact_mod_cast hr))) a
    change iteratedDeriv r g a = _ at he
    rw [he]
    simp_rw [iteratedDeriv_characteristicQuotient_parameter d _ r f
      (fun b => (hfx b).of_le (by exact_mod_cast hr)) a]
    exact hyb j y hy.nonneg hy.decreasing hy.squareRatio hy.upper hy.oddPositive
      (fun b => iteratedDeriv r (fun a => f a b) a) (hfxy r hr a) A hA
      (fun q hq b hb => hder r hr q hq a ha b hb)
  have hb := hxb i x hx.nonneg hx.decreasing hx.squareRatio hx.upper hx.oddPositive g hg B hB hgd
  change ‖characteristicTensorDividedDifference e d (fun k => 2*x k^2) i (fun k => 2*y k^2) j f‖ ≤ _ at hb
  apply hb.trans_eq
  dsimp [B]
  rw [pow_add]
  ring


/-- The bounded tensor coefficients are the actual coefficients of the finite
Newton interpolant of the two parity quotient values. -/
theorem characteristicTensorDividedDifference_eq_coefficients {m n : ℕ}
    (e d : Bool) (x : Fin m → ℝ) (y : Fin n → ℝ)
    (hx : Function.Injective x) (hy : Function.Injective y)
    (f : ℝ → ℝ → ℂ) (i : Fin m) (j : Fin n) :
    characteristicTensorDividedDifference e d (finiteNodeSequence x) i (finiteNodeSequence y) j f =
      tensorNewtonCoefficients (fun a => (x a:ℂ)) (fun b => (y b:ℂ))
        (Complex.ofReal_injective.comp hx) (Complex.ofReal_injective.comp hy)
        (fun a b => characteristicParityGridQuotient e (fun t => characteristicParityGridQuotient d (f t) (y b)) (x a)) i j := by
  rw [← tensorAnalyticDividedDifference_eq_coefficients x y hx hy
    (fun u v => characteristicParityGridQuotient e (fun t => characteristicParityGridQuotient d (f t) v) u)]
  unfold characteristicTensorDividedDifference tensorAnalyticDividedDifference
  congr 1
  funext u
  apply characteristicQuotient_dividedDifference_commute
  intro a ha b hb hab he
  have haj : a < n := lt_of_le_of_lt ha j.isLt
  have hbj : b < n := lt_of_le_of_lt hb j.isLt
  simp only [finiteNodeSequence,dite_eq_left haj,dite_eq_left hbj] at he
  exact hab (congrArg Fin.val (hy he))

/-- At an admissible signed phase, the literal characteristic quotient is exactly
the original cosine/sine quotient. -/
theorem characteristicParityGridQuotient_at_phase (odd : Bool) (f : ℝ → ℂ) (t : ℝ)
    (ht : |t| ≤ 1/2) (hs : |Real.sin (Real.pi*t)| ≤ 1/2) :
    characteristicParityGridQuotient odd f (parityNewtonCoordinate t)=parityGridQuotient odd f t := by
  rw [parityNewtonCoordinate_eq,characteristicParityGridQuotient_double,
    squareParityGridQuotient_sq,signedNewtonChart_sin t ht hs]


end
end MeyerGeneralProblem.Adaptive
