module

public import MeyerGeneralProblem.Interpolation.HermiteGenocchiNodeMotion
public import MeyerGeneralProblem.Sampling.GroupedExponential
public import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import all Mathlib.Analysis.Calculus.ContDiff.Polynomial

@[expose] public section

/-! # Finite-smoothness Newton estimates at decreasing nodes

The endpoint recurrence is proved for the actual analytic divided difference
through finite polynomial interpolation, so high orders require no hidden
higher derivatives of the original function.
-/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open Set

/-- Cyclic symmetry places the first node after all remaining anchors. -/
theorem analyticDividedDifference_eq_tailAnchored_at_first (nodes : ℕ → ℝ) (n : ℕ)
    {f : ℝ → ℂ} (hf : ContDiff ℝ n f) :
    analyticDividedDifference nodes n f =
      iteratedAnchoredDslope (fun j => nodes (j+1)) n f (nodes 0) := by
  cases n with
  | zero => rfl
  | succ n =>
    rw [analyticDividedDifference_cyclic nodes n hf,analyticDividedDifference_eq_iteratedAnchoredDslope]
    rw [ite_eq_right (show ¬ n+1 ≤ n by omega)]
    have he : iteratedAnchoredDslope (fun j => if j ≤ n then nodes (j+1) else nodes 0) (n+1) f =
        iteratedAnchoredDslope (fun j => nodes (j+1)) (n+1) f := by
      apply iteratedAnchoredDslope_congr
      intro j hj
      rw [ite_eq_left (by omega : j ≤ n)]
    rw [he]

/-- Smooth functions satisfy the usual endpoint divided-difference recurrence. -/
theorem analyticDividedDifference_endpoint_of_contDiff (nodes : ℕ → ℝ) (n : ℕ)
    {f : ℝ → ℂ} (hf : ContDiff ℝ (n+1) f) (hne : nodes (n+1) ≠ nodes 0) :
    analyticDividedDifference nodes (n+1) f =
      (nodes (n+1)-nodes 0)⁻¹ •
        (analyticDividedDifference (fun j => nodes (j+1)) n f-analyticDividedDifference nodes n f) := by
  rw [analyticDividedDifference_succ,analyticDividedDifference_eq_iteratedAnchoredDslope,
    iteratedAnchoredDslope_dslope_comm _ n hf,dslope_of_ne _ hne,slope_def_module]
  rw [← analyticDividedDifference_eq_iteratedAnchoredDslope,
    ← analyticDividedDifference_eq_tailAnchored_at_first nodes n (hf.of_le (by exact_mod_cast Nat.le_succ n))]

/-- At distinct nodes, the endpoint recurrence needs only function values.
The interpolating polynomial supplies the temporary smooth comparison. -/
theorem analyticDividedDifference_endpoint (nodes : ℕ → ℝ) (n : ℕ) (f : ℝ → ℂ)
    (hnodes : ∀ i ≤ n+1, ∀ j ≤ n+1, i ≠ j → nodes i ≠ nodes j) :
    analyticDividedDifference nodes (n+1) f =
      (nodes (n+1)-nodes 0)⁻¹ •
        (analyticDividedDifference (fun j => nodes (j+1)) n f-analyticDividedDifference nodes n f) := by
  classical
  let xs : Fin (n+2) → ℝ := fun i => nodes i.val
  have hxs : Function.Injective xs := by
    intro i j hij
    apply Fin.ext
    by_contra hne
    exact hnodes i.val (by omega) j.val (by omega) hne hij
  let z : Fin (n+2) → ℂ := fun i => (xs i:ℂ)
  let hz : Function.Injective z := Complex.ofReal_injective.comp hxs
  let P := newtonInterpolantFromValues z hz (fun i => f (xs i))
  let F : ℝ → ℂ := fun x => P.eval (x:ℂ)
  have hvalues (j : ℕ) (hj : j ≤ n+1) : f (nodes j)=F (nodes j) := by
    exact (eval_newtonInterpolantFromValues_at_node z hz (fun i => f (xs i)) ⟨j,by omega⟩).symm
  have hfull := analyticDividedDifference_congr_values_of_distinct nodes (n+1) f F hnodes hvalues
  have hprefix := analyticDividedDifference_congr_values_of_distinct nodes n f F
    (fun i hi j hj hij => hnodes i (by omega) j (by omega) hij) (fun j hj => hvalues j (by omega))
  have htail := analyticDividedDifference_congr_values_of_distinct (fun j => nodes (j+1)) n f F
    (fun i hi j hj hij => hnodes (i+1) (by omega) (j+1) (by omega) (by omega))
    (fun j hj => hvalues (j+1) (by omega))
  rw [hfull,hprefix,htail]
  apply analyticDividedDifference_endpoint_of_contDiff
  · have hpoly : ContDiff ℝ (n+1) (fun z : ℂ => P.eval z) := by
      simpa using (P.contDiff_aeval (𝕜 := ℂ) (n+1)).restrict_scalars ℝ
    exact hpoly.comp Complex.ofRealCLM.contDiff
  · exact hnodes (n+1) (by omega) 0 (by omega) (by omega)

/-- The actual divided difference at a decreasing finite prefix needs only L
bounded derivatives. A single final zero node is allowed; no denominator uses it. -/
theorem norm_dividedDifference_decreasing_finite_smoothness (L n : ℕ) (nodes : ℕ → ℝ)
    (hnonneg : ∀ j ≤ n, 0 ≤ nodes j)
    (hanti : ∀ i j, i < j → j ≤ n → nodes j < nodes i)
    (hratio : ∀ j < n, nodes (j+1) ≤ nodes j/2)
    (f : ℝ → ℂ) (hf : ContDiff ℝ L f) (A : ℝ) (hA : 0 ≤ A)
    (hderiv : ∀ k ≤ L, ∀ x ∈ Icc (0:ℝ) (nodes 0), ‖iteratedDeriv k f x‖ ≤ A) :
    ‖analyticDividedDifference nodes n f‖ ≤
      (4:ℝ)^n*A/(∏ j ∈ Finset.range (n-L), nodes j) := by
  induction n generalizing nodes with
  | zero =>
    simpa only [analyticDividedDifference_zero,Nat.zero_sub,Finset.range_zero,Finset.prod_empty,
      pow_zero,one_mul,div_one,iteratedDeriv_zero] using hderiv 0 (by omega) (nodes 0) ⟨hnonneg 0 le_rfl,le_rfl⟩
  | succ n ih =>
    by_cases hsmall : n+1 ≤ L
    · have hbound := norm_analyticDividedDifference_le_of_contDiff nodes (n+1)
        (hf.of_le (by exact_mod_cast hsmall))
        (fun j hj => ⟨hnonneg j hj,by
          by_cases hj0 : j=0
          · subst j; exact le_rfl
          · exact (hanti 0 j (by omega) hj).le⟩)
        (hderiv (n+1) hsmall)
      have hfact : (1:ℝ) ≤ (n+1).factorial := by exact_mod_cast (show 1 ≤ (n+1).factorial by have := Nat.factorial_pos (n+1); omega)
      have hfpos : (0:ℝ) < (n+1).factorial := by positivity
      have hfirst : A/((n+1).factorial:ℝ) ≤ A := by apply (div_le_iff₀ hfpos).mpr; nlinarith
      have hpow : (1:ℝ) ≤ 4^(n+1) := one_le_pow₀ (by norm_num)
      simpa only [Nat.sub_eq_zero_of_le hsmall,Finset.range_zero,Finset.prod_empty,div_one] using
        hbound.trans (hfirst.trans (by nlinarith))
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
        (fun i j hij hj => hanti i j hij (by omega)) (fun j hj => hratio j (by omega)) hderiv
      have hq := ih (fun j => nodes (j+1)) (fun j hj => hnonneg (j+1) (by omega))
        (fun i j hij hj => hanti (i+1) (j+1) (by omega) (by omega))
        (fun j hj => hratio (j+1) (by omega))
        (fun k hk x hx => hderiv k hk x ⟨hx.1,hx.2.trans h10⟩)
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
