module

public import MeyerGeneralProblem.Cardinal.Adaptive.ShrinkingNewtonWeights
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import all Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import all Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.Real.Pi.Bounds
import all Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import all Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

@[expose] public section

/-! Fixed-order derivative estimates for complete shrinking Newton products. -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open Finset
open scoped ContDiff

/-- A finite product of smooth factors with geometric derivative bounds has
an explicit fixed-order product bound. The number of factors enters only
through the sum of derivative rates, rather than an exponential order loss. -/
theorem iteratedDeriv_product_geometric_bound (q : ℕ) (f : Fin q → ℝ → ℝ)
    (hf : ∀ j, ContDiff ℝ ∞ (f j)) (A B : Fin q → ℝ)
    (hA : ∀ j, 0 ≤ A j) (hB : ∀ j, 0 ≤ B j) (n : ℕ) (x : ℝ)
    (hbound : ∀ j r, r ≤ n → ‖iteratedDeriv r (f j) x‖ ≤ A j*(B j)^r) :
    ‖iteratedDeriv n (fun y => ∏ j, f j y) x‖ ≤
      (∏ j, A j)*(∑ j, B j)^n := by
  induction q generalizing n with
  | zero =>
    have he : (fun y : ℝ => ∏ j : Fin 0, f j y) = fun _ => (1:ℝ) := by ext; simp
    rw [he]
    cases n <;> simp [iteratedDeriv_const]
  | succ q ih =>
    have ht : ContDiff ℝ ∞ (fun y => ∏ j : Fin q, f j.succ y) := by fun_prop
    simp only [Fin.prod_univ_succ,Fin.sum_univ_succ]
    change ‖iteratedDeriv n ((f 0)*(fun y => ∏ j : Fin q, f j.succ y)) x‖ ≤ _
    rw [iteratedDeriv_mul ((hf 0).of_le (by simp)).contDiffAt (ht.of_le (by simp)).contDiffAt]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ k ∈ Finset.range (n+1), (n.choose k:ℝ)*(A 0*(B 0)^k)*
          ((∏ j : Fin q, A j.succ)*(∑ j : Fin q, B j.succ)^(n-k)) := by
        apply Finset.sum_le_sum
        intro k hk
        simp only [norm_mul,Real.norm_natCast]
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left (hbound 0 k (by simpa using hk)) (by positivity)
        · exact ih (fun j => f j.succ) (fun j => hf j.succ) (fun j => A j.succ)
            (fun j => B j.succ) (fun j => hA j.succ) (fun j => hB j.succ) (n-k)
            (fun j r hr => hbound j.succ r (hr.trans (Nat.sub_le _ _)))
        · exact norm_nonneg _
        · exact mul_nonneg (by positivity) (mul_nonneg (hA 0) (pow_nonneg (hB 0) _))
      _ = _ := by
        rw [add_pow,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        ring

/-- A Newton factor on its retained tail has its full quadratic smallness. -/
theorem shrinkingNewton_cos_factor_le (ε x : ℝ) (hε : 0 ≤ ε) (hεhalf : ε ≤ 1/2)
    (hx : |x| ≤ ε) : |Real.cos (2*Real.pi*ε)-Real.cos (2*Real.pi*x)| ≤ 32*ε^2 := by
  have hcos : Real.cos (2*Real.pi*ε) ≤ Real.cos (2*Real.pi*x) := by
    rw [← Real.cos_abs (2*Real.pi*x)]
    apply Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _)
    · nlinarith [Real.pi_pos]
    · rw [abs_mul,abs_of_pos (by positivity : 0 < 2*Real.pi)]
      exact mul_le_mul_of_nonneg_left hx (by positivity)
  rw [abs_of_nonpos (sub_nonpos.mpr hcos)]
  have hs := (Real.abs_sin_le_abs (x := Real.pi*ε))
  rw [abs_of_nonneg (mul_nonneg Real.pi_pos.le hε)] at hs
  have hs2 : Real.sin (Real.pi*ε)^2 ≤ (Real.pi*ε)^2 := by
    nlinarith [sq_abs (Real.sin (Real.pi*ε)),abs_nonneg (Real.sin (Real.pi*ε))]
  have hdouble := Real.cos_two_mul (Real.pi*ε)
  have htrig := Real.sin_sq_add_cos_sq (Real.pi*ε)
  have hpi := Real.pi_lt_four
  have hpi2 : Real.pi^2 ≤ 16 := by nlinarith [Real.pi_pos]
  have hprod := mul_le_mul_of_nonneg_right hpi2 (sq_nonneg ε)
  have hcx := Real.cos_le_one (2*Real.pi*x)
  have he : 2*(Real.pi*ε)=2*Real.pi*ε := by ring
  rw [he] at hdouble
  nlinarith

/-- Every derivative of a Newton factor has a geometric envelope normalized
by the smallest retained distance, with its zeroth-order smallness preserved. -/
theorem shrinkingNewton_cos_factor_derivative_le (ε δ x : ℝ)
    (hδ : 0 < δ) (hδε : δ ≤ ε) (hεhalf : ε ≤ 1/2) (hx : |x| ≤ ε) (n : ℕ) :
    ‖iteratedDeriv n (fun y => Real.cos (2*Real.pi*ε)-Real.cos (2*Real.pi*y)) x‖ ≤
      (32*ε^2)*(2*Real.pi/δ^2)^n := by
  by_cases hn : n=0
  · subst n
    simpa only [iteratedDeriv_zero,pow_zero,mul_one,Real.norm_eq_abs] using
      shrinkingNewton_cos_factor_le ε x (hδ.le.trans hδε) hεhalf hx
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have he : iteratedDeriv n (fun y => Real.cos (2*Real.pi*ε)-Real.cos (2*Real.pi*y)) x =
        -((2*Real.pi)^n*iteratedDeriv n Real.cos (2*Real.pi*x)) := by
      rw [iteratedDeriv_const_sub hnpos,iteratedDeriv_neg]
      have hh := congrFun (iteratedDeriv_comp_const_mul (n := n)
        (Real.contDiff_cos : ContDiff ℝ n Real.cos) (2*Real.pi)) x
      simpa only [Pi.neg_apply] using congrArg Neg.neg hh
    rw [he,norm_neg,norm_mul,norm_pow,Real.norm_eq_abs,abs_of_pos (by positivity : 0 < 2*Real.pi)]
    calc
      _ ≤ (2*Real.pi)^n*1 := mul_le_mul_of_nonneg_left
        (Real.abs_iteratedDeriv_cos_le_one n _) (by positivity)
      _ ≤ _ := by
        rw [mul_one,div_pow,← mul_div_assoc]
        apply (le_div_iff₀ (pow_pos (sq_pos_of_pos hδ) n)).mpr
        have hδ1 : δ ≤ 1 := by linarith
        have hpow : (δ^2)^n ≤ δ^2 := by
          rw [← pow_mul]
          exact pow_le_pow_of_le_one hδ.le hδ1 (by omega)
        have hsq : δ^2 ≤ 32*ε^2 := by nlinarith [sq_nonneg ε]
        exact (mul_le_mul_of_nonneg_left (hpow.trans hsq) (by positivity)).trans_eq (mul_comm _ _)

/-- The actual finite Newton product retains all squared distance factors
under every fixed derivative order on the retained tail. -/
theorem shrinkingNewton_product_derivative_le (ε : ℕ → ℝ) (i n : ℕ) (δ x : ℝ)
    (hδ : 0 < δ) (hε : ∀ l < i, δ ≤ ε (l+1) ∧ ε (l+1) ≤ 1/2)
    (hx : |x| ≤ δ) :
    ‖iteratedDeriv n (fun y => ∏ l ∈ Finset.range i,
      (Real.cos (2*Real.pi*ε (l+1))-Real.cos (2*Real.pi*y))) x‖ ≤
      (32:ℝ)^i*(shrinkingNewtonWeight ε i)^2*((i:ℝ)*(2*Real.pi/δ^2))^n := by
  have h := iteratedDeriv_product_geometric_bound i
    (fun l y => Real.cos (2*Real.pi*ε (l.val+1))-Real.cos (2*Real.pi*y))
    (fun _ => by fun_prop) (fun l => 32*ε (l.val+1)^2) (fun _ => 2*Real.pi/δ^2)
    (fun _ => by positivity) (fun _ => by positivity) n x
    (fun l r _ => shrinkingNewton_cos_factor_derivative_le _ δ x hδ (hε l.val l.isLt).1
      (hε l.val l.isLt).2 (hx.trans (hε l.val l.isLt).1) r)
  have he (y : ℝ) :
      (∏ j : Fin i, (Real.cos (2*Real.pi*ε (j.val+1))-Real.cos (2*Real.pi*y))) =
      ∏ l ∈ Finset.range i, (Real.cos (2*Real.pi*ε (l+1))-Real.cos (2*Real.pi*y)) :=
    Fin.prod_univ_eq_prod_range (fun l : ℕ => Real.cos (2*Real.pi*ε (l+1))-Real.cos (2*Real.pi*y)) i
  have ha : (∏ j : Fin i, 32*ε (j.val+1)^2) =
      (32:ℝ)^i*(shrinkingNewtonWeight ε i)^2 := by
    rw [Fin.prod_univ_eq_prod_range (fun j => 32*ε (j+1)^2) i,
      Finset.prod_mul_distrib,Finset.prod_const,Finset.card_range,Finset.prod_pow]
    rfl
  simpa only [he,ha,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using h

end
end MeyerGeneralProblem.Adaptive
