module

public import MeyerGeneralProblem.Cardinal.Adaptive.SignedSquareNewtonBounds

@[expose] public section

/-! # Literal characteristic-coordinate normalization for finite Newton data -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open Set

/-- Scaling distinct nodes gives the exact inverse power on their divided difference,
without a differentiability assumption on the function. -/
theorem analyticDividedDifference_scale_nodes (c : ℝ) (hc : c ≠ 0) (nodes : ℕ → ℝ)
    (n : ℕ) (hd : ∀ i ≤ n, ∀ j ≤ n, i ≠ j → nodes i ≠ nodes j) (f : ℝ → ℂ) :
    analyticDividedDifference (fun j => c*nodes j) n f =
      ((c:ℂ)^n)⁻¹*analyticDividedDifference nodes n (fun x => f (c*x)) := by
  induction n generalizing nodes with
  | zero => simp [analyticDividedDifference_zero]
  | succ n ih =>
    have hs : ∀ i ≤ n+1, ∀ j ≤ n+1, i ≠ j → c*nodes i ≠ c*nodes j := by
      intro i hi j hj hij he
      exact hd i hi j hj hij (mul_left_cancel₀ hc he)
    rw [analyticDividedDifference_endpoint _ n f hs,
      ih (fun j => nodes (j+1)) (fun i hi j hj hij => hd (i+1) (by omega) (j+1) (by omega) (by omega)),
      ih nodes (fun i hi j hj hij => hd i (by omega) j (by omega) hij),
      analyticDividedDifference_endpoint nodes n _ hd]
    have hn := hd (n+1) le_rfl 0 (by omega) (by omega)
    have hc' : (c:ℂ) ≠ 0 := by exact_mod_cast hc
    have hn' : (nodes (n+1):ℂ)-(nodes 0:ℂ) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr hn
    simp only [Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_sub,Complex.ofReal_mul,pow_succ]
    have hdiff : (c:ℂ)*(nodes (n+1):ℂ)-(c:ℂ)*(nodes 0:ℂ) ≠ 0 := by
      rw [← mul_sub]
      exact mul_ne_zero hc' hn'
    field_simp

/-- Actual finite parity quotient in the literal `z=2 sin²(pi t)` coordinate. -/
def characteristicParityGridQuotient (odd : Bool) (f : ℝ → ℂ) (z : ℝ) : ℂ :=
  squareParityGridQuotient odd f (z/2)

/-- The source normalization is exact at each supplied sine-square node. -/
theorem characteristicParityGridQuotient_double (odd : Bool) (f : ℝ → ℂ) (u : ℝ) :
    characteristicParityGridQuotient odd f (2*u)=squareParityGridQuotient odd f u := by
  simp [characteristicParityGridQuotient]

/-- The literal characteristic-node divided difference has the exact factor `2⁻ⁿ`. -/
theorem characteristic_dividedDifference_eq (odd : Bool) (f : ℝ → ℂ) (r : ℕ → ℝ)
    (n : ℕ) (hd : ∀ i ≤ n, ∀ j ≤ n, i ≠ j → r i^2 ≠ r j^2) :
    analyticDividedDifference (fun j => 2*r j^2) n (characteristicParityGridQuotient odd f) =
      ((2:ℂ)^n)⁻¹*analyticDividedDifference (fun j => r j^2) n (squareParityGridQuotient odd f) := by
  rw [analyticDividedDifference_scale_nodes 2 (by norm_num) _ n hd]
  simp only [characteristicParityGridQuotient_double,Complex.ofReal_ofNat]

/-- A decreasing nonnegative radius prefix has distinct squared nodes. -/
theorem squared_nodes_distinct (r : ℕ → ℝ) (n : ℕ)
    (hnonneg : ∀ j ≤ n, 0 ≤ r j)
    (hanti : ∀ i j, i < j → j ≤ n → r j < r i) :
    ∀ i ≤ n, ∀ j ≤ n, i ≠ j → r i^2 ≠ r j^2 := by
  intro i hi j hj hij he
  have hp := hnonneg i hi
  have hq := hnonneg j hj
  have he' : r i=r j := by nlinarith
  rcases lt_or_gt_of_ne hij with hh|hh
  · exact (hanti i j hh hj).ne he'.symm
  · exact (hanti j i hh hi).ne he'

/-- The denominator product never contains a possibly zero terminal node. -/
theorem square_prefix_product_pos (r : ℕ → ℝ) (n L : ℕ)
    (hnonneg : ∀ j ≤ n, 0 ≤ r j)
    (hanti : ∀ i j, i < j → j ≤ n → r j < r i) :
    0 < ∏ j ∈ Finset.range (n-L), r j^2 := by
  apply Finset.prod_pos
  intro j hj
  have hjn : j < n := by have := Finset.mem_range.mp hj; omega
  have hp := (hnonneg n le_rfl).trans_lt (hanti j n hjn le_rfl)
  positivity

/-- Passing to the literal characteristic coordinate improves the coefficient
bound sufficiently to pay for every factor two in its denominator product. -/
theorem norm_characteristic_dividedDifference_le (odd : Bool) (f : ℝ → ℂ)
    (r : ℕ → ℝ) (n L : ℕ)
    (hnonneg : ∀ j ≤ n, 0 ≤ r j)
    (hanti : ∀ i j, i < j → j ≤ n → r j < r i)
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ‖analyticDividedDifference (fun j => r j^2) n (squareParityGridQuotient odd f)‖ ≤
      B/(∏ j ∈ Finset.range (n-L), r j^2)) :
    ‖analyticDividedDifference (fun j => 2*r j^2) n (characteristicParityGridQuotient odd f)‖ ≤
      B/(∏ j ∈ Finset.range (n-L), 2*r j^2) := by
  have hP := square_prefix_product_pos r n L hnonneg hanti
  have hpow : (2:ℝ)^(n-L) ≤ 2^n := pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
  rw [characteristic_dividedDifference_eq odd f r n (squared_nodes_distinct r n hnonneg hanti),
    norm_mul,norm_inv,norm_pow]
  norm_num only [Complex.norm_ofNat]
  have hprod : (∏ j ∈ Finset.range (n-L), 2*r j^2) =
      (2:ℝ)^(n-L)*(∏ j ∈ Finset.range (n-L), r j^2) := by
    rw [Finset.prod_mul_distrib]
    simp
  rw [hprod]
  calc
    _ ≤ ((2:ℝ)^n)⁻¹*(B/(∏ j ∈ Finset.range (n-L), r j^2)) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = B/((2:ℝ)^n*(∏ j ∈ Finset.range (n-L), r j^2)) := by ring
    _ ≤ _ := div_le_div_of_nonneg_left hB (by positivity) (mul_le_mul_of_nonneg_right hpow hP.le)

/-- One finite-order constant works for the literal cosine or sine parity
coefficients at all finite prefixes, with the exact source denominator. -/
theorem exists_characteristic_Newton_bound (odd : Bool) (L : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ r : ℕ → ℝ,
      (∀ j ≤ n, 0 ≤ r j) →
      (∀ i j, i < j → j ≤ n → r j < r i) →
      (∀ j < n, r (j+1)^2 ≤ r j^2/2) → r 0 ≤ 1/2 →
      (odd=true → ∀ j ≤ n, 0 < r j) →
      ∀ f : ℝ → ℂ, ContDiff ℝ (2*L+1) f → ∀ A : ℝ, 0 ≤ A →
      (∀ m ≤ 2*L+1, ∀ x ∈ Icc (-1/2:ℝ) (1/2), ‖iteratedDeriv m f x‖ ≤ A) →
      ‖analyticDividedDifference (fun j => 2*r j^2) n (characteristicParityGridQuotient odd f)‖ ≤
        4^n*(C*A)/(∏ j ∈ Finset.range (n-L), 2*r j^2) := by
  cases odd with
  | false =>
    obtain ⟨C,hC,hb⟩ := exists_even_square_Newton_bound L
    refine ⟨C,hC,?_⟩
    intro n r hn ha hr hu _ f hf A hA hd
    exact norm_characteristic_dividedDifference_le false f r n L hn ha _ (by positivity)
      (hb n r hn ha hr hu f hf A hA hd)
  | true =>
    obtain ⟨C,hC,hb⟩ := exists_odd_square_Newton_bound L
    refine ⟨C,hC,?_⟩
    intro n r hn ha hr hu hp f hf A hA hd
    exact norm_characteristic_dividedDifference_le true f r n L hn ha _ (by positivity)
      (hb n r (hp rfl) ha hr hu f hf A hA hd)


end
end MeyerGeneralProblem.Adaptive
