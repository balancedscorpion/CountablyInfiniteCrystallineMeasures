module

public import MeyerGeneralProblem.Cardinal.Adaptive.DecreasingNewtonBounds

@[expose] public section

/-! # High Newton orders from uniformly bounded low orders

The endpoint recurrence consumes finite divided-difference data only. This
version allows signed-square charts to supply the low orders without claiming
smoothness of a quotient at zero.
-/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open Set

/-- Decreasing-node control above order L needs only the actual low-order
consecutive divided differences, not derivatives of the quotient function. -/
theorem norm_dividedDifference_decreasing_of_low_order (L n : ℕ) (nodes : ℕ → ℝ)
    (hnonneg : ∀ j ≤ n, 0 ≤ nodes j)
    (hanti : ∀ i j, i < j → j ≤ n → nodes j < nodes i)
    (hratio : ∀ j < n, nodes (j+1) ≤ nodes j/2)
    (f : ℝ → ℂ) (A : ℝ) (hA : 0 ≤ A)
    (hlow : ∀ a k, a+k ≤ n → k ≤ L →
      ‖analyticDividedDifference (fun j => nodes (a+j)) k f‖ ≤ A) :
    ‖analyticDividedDifference nodes n f‖ ≤
      (4:ℝ)^n*A/(∏ j ∈ Finset.range (n-L), nodes j) := by
  induction n generalizing nodes with
  | zero =>
    simpa only [Nat.zero_add,Nat.zero_sub,Finset.range_zero,Finset.prod_empty,
      pow_zero,one_mul,div_one] using hlow 0 0 (by omega) (by omega)
  | succ n ih =>
    by_cases hsmall : n+1 ≤ L
    · have hbound := hlow 0 (n+1) (by omega) hsmall
      simp only [Nat.zero_add] at hbound
      have hpow : (1:ℝ) ≤ 4^(n+1) := one_le_pow₀ (by norm_num)
      simpa only [Nat.sub_eq_zero_of_le hsmall,Finset.range_zero,Finset.prod_empty,div_one] using
        hbound.trans (by nlinarith)
    · have hLn : L ≤ n := by omega
      have hstart : 0 < nodes 0 := (hnonneg (n+1) le_rfl).trans_lt (hanti 0 (n+1) (by omega) le_rfl)
      have h10 : nodes 1 ≤ nodes 0 := (hanti 0 1 (by omega) (by omega)).le
      have hend : nodes (n+1) ≤ nodes 1 := by
        by_cases hn : n=0
        · subst n; exact le_rfl
        · exact (hanti 1 (n+1) (by omega) le_rfl).le
      have hgap : nodes 0/2 ≤ nodes 0-nodes (n+1) := by linarith [hratio 0 (by omega)]
      have hgapPos : 0 < nodes 0-nodes (n+1) := sub_pos.mpr (hanti 0 (n+1) (by omega) le_rfl)
      let P := ∏ j ∈ Finset.range (n-L), nodes j
      let Q := ∏ j ∈ Finset.range (n-L), nodes (j+1)
      have hP : 0 < P := Finset.prod_pos (fun j hj =>
        (hnonneg (n+1) le_rfl).trans_lt (hanti j (n+1) (by have := Finset.mem_range.mp hj; omega) le_rfl))
      have hQ : 0 < Q := Finset.prod_pos (fun j hj =>
        (hnonneg (n+1) le_rfl).trans_lt (hanti (j+1) (n+1) (by have := Finset.mem_range.mp hj; omega) le_rfl))
      have hQP : Q ≤ P := Finset.prod_le_prod₀
        (fun j hj => hnonneg (j+1) (by have := Finset.mem_range.mp hj; omega))
        (fun j hj => (hanti j (j+1) (by omega) (by have := Finset.mem_range.mp hj; omega)).le)
      have hp := ih nodes (fun j hj => hnonneg j (by omega))
        (fun i j hij hj => hanti i j hij (by omega)) (fun j hj => hratio j (by omega)) (fun a k hak hk => hlow a k (by omega) hk)
      have hq := ih (fun j => nodes (j+1)) (fun j hj => hnonneg (j+1) (by omega))
        (fun i j hij hj => hanti (i+1) (j+1) (by omega) (by omega))
        (fun j hj => hratio (j+1) (by omega))
        (fun a k hak hk => by
          simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hlow (a+1) k (by omega) hk)
      have hp' : ‖analyticDividedDifference nodes n f‖ ≤ (4:ℝ)^n*A/Q :=
        hp.trans (div_le_div_of_nonneg_left (by positivity) hQ hQP)
      have hsum : ‖analyticDividedDifference (fun j => nodes (j+1)) n f-
          analyticDividedDifference nodes n f‖ ≤ 2*((4:ℝ)^n*A/Q) := by
        have ht := norm_sub_le (analyticDividedDifference (fun j => nodes (j+1)) n f)
          (analyticDividedDifference nodes n f)
        linarith
      have hinv : (nodes 0-nodes (n+1))⁻¹ ≤ 2/nodes 0 := by
        rw [inv_eq_one_div,div_le_div_iff₀ hgapPos hstart]
        linarith
      have hprod : (∏ j ∈ Finset.range (n+1-L), nodes j) = nodes 0*Q := by
        rw [show n+1-L=(n-L)+1 by omega,Finset.prod_range_succ']
        exact mul_comm _ _
      rw [analyticDividedDifference_endpoint nodes n f (by
        intro i hi j hj hij
        rcases lt_or_gt_of_ne hij with hij | hji
        · exact (hanti i j hij hj).ne'
        · exact (hanti j i hji hi).ne),norm_smul,Real.norm_eq_abs,abs_inv,
        abs_of_neg (by linarith : nodes (n+1)-nodes 0 < 0)]
      rw [show -(nodes (n+1)-nodes 0)=nodes 0-nodes (n+1) by ring,hprod]
      calc
        _ ≤ (2/nodes 0)*(2*((4:ℝ)^n*A/Q)) :=
          mul_le_mul hinv hsum (norm_nonneg _) (by positivity)
        _ = (4:ℝ)^(n+1)*A/(nodes 0*Q) := by rw [pow_succ]; ring

end
end MeyerGeneralProblem.Adaptive
