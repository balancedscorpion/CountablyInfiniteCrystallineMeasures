module

public import MeyerGeneralProblem.Cardinal.Adaptive.CriticalHeadInverse
public import Mathlib.Algebra.Polynomial.Reverse
import all Mathlib.Algebra.Polynomial.Reverse

@[expose] public section

/-! # Reflected Green coefficients and exact critical trigonometric normalization -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open scoped BigOperators
open Polynomial

/-- The actual monic polynomial of all signed head roots. -/
def criticalHeadPolynomial {k : ℕ} (α : Fin k → ℝ) : ℂ[X] :=
  Lagrange.nodal Finset.univ (criticalHeadRoots α)

private theorem character_pair (a : ℝ) :
    criticalCharacter 1 a + criticalCharacter 1 (-a) = 2*(Real.cos (2*Real.pi*a) : ℂ) ∧
    criticalCharacter 1 a * criticalCharacter 1 (-a) = 1 := by
  have hp : criticalCharacter 1 a = Complex.exp (((2*Real.pi*a : ℝ) : ℂ)*Complex.I) := by
    unfold criticalCharacter
    congr 1
    push_cast
    ring
  have hn : criticalCharacter 1 (-a) = Complex.exp (-(((2*Real.pi*a : ℝ) : ℂ)*Complex.I)) := by
    unfold criticalCharacter
    congr 1
    push_cast
    ring
  rw [hp,hn]
  constructor
  · rw [show -(((2*Real.pi*a : ℝ) : ℂ)*Complex.I) = ((-(2*Real.pi*a : ℝ) : ℝ) : ℂ)*Complex.I by push_cast; ring]
    simp only [Complex.exp_mul_I,Complex.ofReal_cos,Complex.ofReal_neg,
      Complex.cos_neg,Complex.sin_neg]
    ring
  · rw [← Complex.exp_add,add_neg_cancel,Complex.exp_zero]

/-- Pairing the two signed roots gives the exact real cosine quadratic. -/
theorem criticalHeadPolynomial_factorization {k : ℕ} (α : Fin k → ℝ) :
    criticalHeadPolynomial α = ∏ i : Fin k,
      (X^2-C (2*(Real.cos (2*Real.pi*α i) : ℂ))*X+1) := by
  classical
  unfold criticalHeadPolynomial
  rw [Lagrange.nodal_eq]
  have he := Fintype.prod_equiv (Fintype.equivFin (Fin k × Bool))
    (fun a => X-C (criticalCharacter 1 (criticalSignedPhase a.2 (α a.1))))
    (fun i => X-C (criticalHeadRoots α i)) (by intro a; simp [criticalHeadRoots])
  rw [← he,Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro i _
  simp only [Fintype.prod_bool,criticalSignedPhase,ite_true,Bool.false_eq_true,ite_false]
  obtain ⟨hs,hm⟩ := character_pair (α i)
  calc
    (X-C (criticalCharacter 1 (-α i))) * (X-C (criticalCharacter 1 (α i))) =
        X^2-C (criticalCharacter 1 (α i)+criticalCharacter 1 (-α i))*X+
          C (criticalCharacter 1 (α i)*criticalCharacter 1 (-α i)) := by
            simp only [map_add,map_mul]; ring
    _ = _ := by rw [hs,hm]; simp

private theorem reverse_quadratic (c : ℂ) :
    (X^2-C c*X+1 : ℂ[X]).reverse = X^2-C c*X+1 := by
  have he : (X^2-C c*X+1 : ℂ[X]) = (X+C (-c))*X+C 1 := by simp; ring
  rw [he,Polynomial.reverse_add_C,Polynomial.reverse_mul_X,Polynomial.reverse_add_C]
  have hd : ((X+C (-c))*X : ℂ[X]).natDegree = 2 := by compute_degree!
  rw [hd]
  simp [Polynomial.reverse]
  ring

/-- The signed root polynomial is exactly reciprocal. -/
theorem criticalHeadPolynomial_reverse {k : ℕ} (α : Fin k → ℝ) :
    (criticalHeadPolynomial α).reverse = criticalHeadPolynomial α := by
  rw [criticalHeadPolynomial_factorization]
  have hf (s : Finset (Fin k)) :
      (∏ i ∈ s, (X^2-C (2*(Real.cos (2*Real.pi*α i) : ℂ))*X+1)).reverse =
      ∏ i ∈ s, (X^2-C (2*(Real.cos (2*Real.pi*α i) : ℂ))*X+1) := by
    induction s using Finset.induction_on with
    | empty => simp [Polynomial.reverse]
    | @insert a s ha ih =>
      rw [Finset.prod_insert ha,Polynomial.reverse_mul_of_domain,reverse_quadratic,ih]
  exact hf Finset.univ

/-- Exact coefficient symmetry, including both endpoint coefficients. -/
theorem criticalHeadPolynomial_coeff_reflect {k : ℕ} (α : Fin k → ℝ)
    (i : Fin (Fintype.card (Fin k × Bool)+1)) :
    (criticalHeadPolynomial α).coeff i.rev = (criticalHeadPolynomial α).coeff i := by
  have he := congrArg (fun p : ℂ[X] => p.coeff i) (criticalHeadPolynomial_reverse α)
  rw [Polynomial.coeff_reverse,Polynomial.revAt_le] at he
  · simpa [criticalHeadPolynomial,Fin.rev] using he
  · simpa [criticalHeadPolynomial] using Nat.le_of_lt_succ i.isLt

/-- Ascending Green coefficients, reflected from the checked descending sequence. -/
def criticalHeadPositiveGreen {k : ℕ} (α : Fin k → ℝ) (t : ℤ) : ℂ :=
  criticalHeadNegativeGreen α (-t)

/-- Ascending coefficients vanish before the source threshold k. -/
theorem criticalHeadPositiveGreen_eq_zero {k : ℕ} (α : Fin k → ℝ) (t : ℤ)
    (ht : t < k) : criticalHeadPositiveGreen α t = 0 :=
  criticalHeadNegativeGreen_eq_zero α (-t) (by omega)

/-- The reflected sequence is an exact right inverse for the SAME centered
Laurent symbol, by proved reciprocal coefficient symmetry. -/
theorem criticalHeadPositiveGreen_impulse {k : ℕ} (hk : 1 ≤ k) (α : Fin k → ℝ) (t : ℤ) :
    ∑ i : Fin (Fintype.card (Fin k × Bool)+1),
      (criticalHeadPolynomial α).coeff i *
        criticalHeadPositiveGreen α (t-((i : ℤ)-(k : ℤ))) = if t=0 then 1 else 0 := by
  rw [← Equiv.sum_comp (Fin.revPerm)]
  simp only [Fin.revPerm_apply,criticalHeadPolynomial_coeff_reflect,criticalHeadPositiveGreen]
  have he (i : Fin (Fintype.card (Fin k × Bool)+1)) :
      -(t-((i.rev : ℤ)-(k : ℤ))) = -t-((i : ℤ)-(k : ℤ)) := by
    have hv : i.rev.val+i.val=Fintype.card (Fin k × Bool) := Fin.rev_add_cast i
    have hc : Fintype.card (Fin k × Bool) = 2*k := by simp; omega
    have hv' : i.rev.val+i.val=2*k := hv.trans hc
    omega
  simp only [he]
  simpa only [criticalHeadPolynomial,neg_eq_zero] using criticalHeadNegativeGreen_impulse hk α (-t)

/-- The ascending coefficients are uniformly bounded with the same finite
head-dependent bound; no summability is claimed. -/
theorem criticalHeadPositiveGreen_uniform_bound {k : ℕ} (α : Fin k → ℝ)
    (hα : Function.Injective α) (hinside : ∀ i, 0 < α i ∧ α i < 1/2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℤ, ‖criticalHeadPositiveGreen α t‖ ≤ C := by
  obtain ⟨C,hC,h⟩ := criticalHeadNegativeGreen_uniform_bound α hα hinside
  exact ⟨C,hC,fun t => h (-t)⟩


/-- The exact trigonometric head product from the critical source. -/
def criticalHeadTrigProduct {k : ℕ} (α : Fin k → ℝ) (x : ℝ) : ℂ :=
  ∏ i, (criticalNewtonNode x-criticalNewtonNode (α i))

private theorem eval_quadratic_character (a x : ℝ) :
    (X^2-C (2*(Real.cos (2*Real.pi*a) : ℂ))*X+1).eval (criticalCharacter 1 x) =
      (-2 : ℂ)*criticalCharacter 1 x*(criticalNewtonNode x-criticalNewtonNode a) := by
  obtain ⟨hs,hm⟩ := character_pair x
  simp only [eval_add,eval_sub,eval_pow,eval_X,eval_mul,eval_C,eval_one,criticalNewtonNode]
  simp only [Complex.ofReal_sub,Complex.ofReal_one]
  linear_combination criticalCharacter 1 x * hs - hm

/-- Exact scalar normalization between the signed-root polynomial and the
source product of Newton factors. In particular the leading Laurent coefficient
is (-1/2)^k, not 1. -/
theorem criticalHeadPolynomial_eval_character {k : ℕ} (α : Fin k → ℝ) (x : ℝ) :
    (criticalHeadPolynomial α).eval (criticalCharacter 1 x) =
      (-2 : ℂ)^k * (criticalCharacter 1 x)^k * criticalHeadTrigProduct α x := by
  rw [criticalHeadPolynomial_factorization,Polynomial.eval_prod]
  simp only [eval_quadratic_character,Finset.prod_mul_distrib,Finset.prod_const,
    Finset.card_univ,Fintype.card_fin,criticalHeadTrigProduct]

private theorem criticalCharacter_nat_pow (n : ℕ) (x : ℝ) :
    criticalCharacter (n : ℤ) x = (criticalCharacter 1 x)^n := by
  induction n with
  | zero => simp [criticalCharacter]
  | succ n ih =>
    have h := congrFun (criticalCharacter_mul (n : ℤ) 1) x
    simpa [Nat.cast_add,ih,pow_succ] using h.symm

/-- Coefficients of the actual centered trigonometric difference operator. -/
def criticalHeadDifferenceCoeff {k : ℕ} (α : Fin k → ℝ)
    (i : Fin (Fintype.card (Fin k × Bool)+1)) : ℂ :=
  (-1/2 : ℂ)^k*(criticalHeadPolynomial α).coeff i

/-- The whole finite Laurent sum equals exactly the original trigonometric
head multiplier, retaining the Fourier character normalization and centered indices. -/
theorem criticalHeadDifferenceCoeff_symbol {k : ℕ} (α : Fin k → ℝ) (x : ℝ) :
    ∑ i : Fin (Fintype.card (Fin k × Bool)+1),
      criticalHeadDifferenceCoeff α i * criticalCharacter ((i : ℤ)-(k : ℤ)) x =
      criticalHeadTrigProduct α x := by
  have hc : criticalCharacter (k : ℤ) x ≠ 0 := Complex.exp_ne_zero _
  apply mul_right_cancel₀ hc
  rw [Finset.sum_mul]
  have hchar (i : Fin (Fintype.card (Fin k × Bool)+1)) :
      criticalCharacter ((i : ℤ)-(k : ℤ)) x * criticalCharacter (k : ℤ) x =
      (criticalCharacter 1 x)^i.val := by
    have h := congrFun (criticalCharacter_mul ((i : ℤ)-(k : ℤ)) (k : ℤ)) x
    simpa [criticalCharacter_nat_pow] using h
  simp only [criticalHeadDifferenceCoeff,mul_assoc,hchar]
  rw [← Finset.mul_sum]
  have he := Polynomial.eval_eq_sum_range (p := criticalHeadPolynomial α) (criticalCharacter 1 x)
  simp only [criticalHeadPolynomial,Lagrange.natDegree_nodal,Finset.card_univ,Fintype.card_fin] at he
  rw [← Fin.sum_univ_eq_sum_range] at he
  change _ * (∑ i : Fin (Fintype.card (Fin k × Bool)+1),
    (criticalHeadPolynomial α).coeff i*(criticalCharacter 1 x)^i.val) = _
  change (criticalHeadPolynomial α).eval (criticalCharacter 1 x) =
    ∑ i : Fin (Fintype.card (Fin k × Bool)+1),
      (criticalHeadPolynomial α).coeff i*(criticalCharacter 1 x)^i.val at he
  rw [← he,criticalHeadPolynomial_eval_character,criticalCharacter_nat_pow]
  have hp : (-1/2 : ℂ)^k * (-2 : ℂ)^k = 1 := by rw [← mul_pow]; norm_num
  calc
    (-1/2 : ℂ)^k*((-2 : ℂ)^k*(criticalCharacter 1 x)^k*criticalHeadTrigProduct α x) =
      ((-1/2 : ℂ)^k*(-2 : ℂ)^k)*((criticalCharacter 1 x)^k*criticalHeadTrigProduct α x) := by ring
    _ = criticalHeadTrigProduct α x*(criticalCharacter 1 x)^k := by rw [hp]; ring

/-- Both oriented Green sequences with the exact original multiplier scalar. -/
def criticalHeadGreen {k : ℕ} (positive : Bool) (α : Fin k → ℝ) (t : ℤ) : ℂ :=
  (-2 : ℂ)^k * if positive then criticalHeadPositiveGreen α t else criticalHeadNegativeGreen α t

/-- Both oriented sequences invert the exact source coefficient family. -/
theorem criticalHeadGreen_impulse {k : ℕ} (hk : 1 ≤ k) (positive : Bool)
    (α : Fin k → ℝ) (t : ℤ) :
    ∑ i : Fin (Fintype.card (Fin k × Bool)+1), criticalHeadDifferenceCoeff α i *
      criticalHeadGreen positive α (t-((i : ℤ)-(k : ℤ))) = if t=0 then 1 else 0 := by
  have hp : (-1/2 : ℂ)^k * (-2 : ℂ)^k = 1 := by rw [← mul_pow]; norm_num
  have he (a b : ℂ) : ((-1/2 : ℂ)^k*a)*((-2 : ℂ)^k*b)=a*b := by
    calc
      _ = ((-1/2 : ℂ)^k*(-2 : ℂ)^k)*(a*b) := by ring
      _ = _ := by rw [hp,one_mul]
  cases positive <;> simp only [criticalHeadDifferenceCoeff,criticalHeadGreen,
    Bool.false_eq_true,ite_false,ite_true,he]
  · exact criticalHeadNegativeGreen_impulse hk α t
  · exact criticalHeadPositiveGreen_impulse hk α t

/-- Both actual Green sequences have finite uniform coefficient bounds. -/
theorem criticalHeadGreen_bounded {k : ℕ} (positive : Bool) (α : Fin k → ℝ)
    (hα : Function.Injective α) (hinside : ∀ i, 0 < α i ∧ α i < 1/2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℤ, ‖criticalHeadGreen positive α t‖ ≤ C := by
  have h : ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℤ,
      ‖if positive then criticalHeadPositiveGreen α t else criticalHeadNegativeGreen α t‖ ≤ C := by
    cases positive
    · exact criticalHeadNegativeGreen_uniform_bound α hα hinside
    · exact criticalHeadPositiveGreen_uniform_bound α hα hinside
  obtain ⟨C,hC,h⟩ := h
  refine ⟨‖(-2 : ℂ)^k‖*C,mul_nonneg (norm_nonneg _) hC,fun t => ?_⟩
  rw [criticalHeadGreen,norm_mul]
  exact mul_le_mul_of_nonneg_left (h t) (norm_nonneg _)

end
end MeyerGeneralProblem.Adaptive
