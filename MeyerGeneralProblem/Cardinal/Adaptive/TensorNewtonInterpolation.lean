module

public import MeyerGeneralProblem.Cardinal.Adaptive.DecreasingNewtonBounds

@[expose] public section

/-! # Exact finite tensor Newton interpolation and mixed-derivative estimates -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open Set

/-- Actual finite Newton coefficients in both coordinates. -/
def tensorNewtonCoefficients {m n : ℕ} (x : Fin m → ℂ) (y : Fin n → ℂ)
    (hx : Function.Injective x) (hy : Function.Injective y) (v : Fin m → Fin n → ℂ) :
    Fin m → Fin n → ℂ :=
  fun i j => dividedDifferences x hx (fun a => dividedDifferences y hy (v a) j) i

/-- The actual tensor Newton sum has the given value at every finite grid point. -/
theorem tensorNewton_interpolates {m n : ℕ} (x : Fin m → ℂ) (y : Fin n → ℂ)
    (hx : Function.Injective x) (hy : Function.Injective y) (v : Fin m → Fin n → ℂ)
    (a : Fin m) (b : Fin n) :
    (∑ i, ∑ j, tensorNewtonCoefficients x y hx hy v i j *
      (newtonBasisPolynomial x i).eval (x a) * (newtonBasisPolynomial y j).eval (y b)) = v a b := by
  have hrow (j : Fin n) : (∑ i, tensorNewtonCoefficients x y hx hy v i j *
      (newtonBasisPolynomial x i).eval (x a)) = dividedDifferences y hy (v a) j := by
    have he := eval_newtonInterpolantFromValues_at_node x hx (fun a => dividedDifferences y hy (v a) j) a
    rw [newtonInterpolantFromValues_eq_sum] at he
    simpa only [Polynomial.eval_finsetSum,Polynomial.eval_mul,Polynomial.eval_C,tensorNewtonCoefficients] using he
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul,hrow]
  have he := eval_newtonInterpolantFromValues_at_node y hy (v a) b
  rw [newtonInterpolantFromValues_eq_sum] at he
  simpa only [Polynomial.eval_finsetSum,Polynomial.eval_mul,Polynomial.eval_C] using he

/-- An actual analytic divided difference at a distinct prefix is a finite fixed
linear combination of values. No smoothness is required for this identity. -/
theorem analyticDividedDifference_eq_prefix_weights (nodes : ℕ → ℝ) (n : ℕ)
    (hnodes : ∀ i ≤ n, ∀ j ≤ n, i ≠ j → nodes i ≠ nodes j) (f : ℝ → ℂ) :
    analyticDividedDifference nodes n f =
      ∑ j : Fin (n+1), groupedNewtonWeight (fun i : Fin (n+1) => (nodes i:ℂ)) (Fin.last n) j * f (nodes j) := by
  let xs : Fin (n+1) → ℝ := fun i => nodes i
  have hxs : Function.Injective xs := by
    intro i j hij
    apply Fin.ext
    by_contra hne
    exact hnodes i.val (by omega) j.val (by omega) hne hij
  calc
    _ = analyticDividedDifference (finiteNodeSequence xs) n f := by
      apply analyticDividedDifference_congr_nodes
      intro j hj
      simp only [finiteNodeSequence,dite_eq_left (by omega : j < n+1),xs]
    _ = dividedDifferences (fun i => (xs i:ℂ)) (Complex.ofReal_injective.comp hxs)
        (fun i => f (xs i)) (Fin.last n) := analyticDividedDifference_eq_dividedDifferences xs hxs f (Fin.last n)
    _ = _ := dividedDifferences_eq_groupedNewtonWeights _ _ _ _

/-- Finite parameter smoothness passes through an actual divided difference by
its finite fixed value formula, independently of the interpolation order. -/
theorem contDiff_parametric_dividedDifference (nodes : ℕ → ℝ) (n L : ℕ)
    (hnodes : ∀ i ≤ n, ∀ j ≤ n, i ≠ j → nodes i ≠ nodes j)
    (f : ℝ → ℝ → ℂ) (hf : ∀ x, ContDiff ℝ L (f x)) :
    ContDiff ℝ L (fun y => analyticDividedDifference nodes n (fun x => f x y)) := by
  have he : (fun y => analyticDividedDifference nodes n (fun x => f x y)) =
      fun y => ∑ j : Fin (n+1), groupedNewtonWeight (fun i : Fin (n+1) => (nodes i:ℂ)) (Fin.last n) j * f (nodes j) y :=
    funext (fun y => analyticDividedDifference_eq_prefix_weights nodes n hnodes (fun x => f x y))
  rw [he]
  exact ContDiff.sum (fun j _ => contDiff_const.mul (hf (nodes j)))

/-- Mixed derivatives commute exactly through finite interpolation in the other
variable; no derivative beyond the declared parameter order is used. -/
theorem iteratedDeriv_parametric_dividedDifference (nodes : ℕ → ℝ) (n r : ℕ)
    (hnodes : ∀ i ≤ n, ∀ j ≤ n, i ≠ j → nodes i ≠ nodes j)
    (f : ℝ → ℝ → ℂ) (hf : ∀ x, ContDiff ℝ r (f x)) (y : ℝ) :
    iteratedDeriv r (fun y => analyticDividedDifference nodes n (fun x => f x y)) y =
      analyticDividedDifference nodes n (fun x => iteratedDeriv r (f x) y) := by
  have he : (fun y => analyticDividedDifference nodes n (fun x => f x y)) =
      fun y => ∑ j : Fin (n+1), groupedNewtonWeight (fun i : Fin (n+1) => (nodes i:ℂ)) (Fin.last n) j * f (nodes j) y :=
    funext (fun y => analyticDividedDifference_eq_prefix_weights nodes n hnodes (fun x => f x y))
  have hd (j : Fin (n+1)) : ContDiffAt ℝ r
      (fun y => groupedNewtonWeight (fun i : Fin (n+1) => (nodes i:ℂ)) (Fin.last n) j * f (nodes j) y) y :=
    (contDiff_const.mul (hf (nodes j))).contDiffAt
  rw [he,iteratedDeriv_fun_sum (fun j _ => hd j)]
  simp_rw [iteratedDeriv_const_mul_field]
  exact (analyticDividedDifference_eq_prefix_weights nodes n hnodes (fun x => iteratedDeriv r (f x) y)).symm

/-- Actual Newton extraction in two coordinates, retaining the two finite orders. -/
def tensorAnalyticDividedDifference (x : ℕ → ℝ) (i : ℕ) (y : ℕ → ℝ) (j : ℕ)
    (f : ℝ → ℝ → ℂ) : ℂ :=
  analyticDividedDifference x i (fun a => analyticDividedDifference y j (f a))

/-- The decreasing-node estimate tensors with mixed derivatives at fixed order L.
Both coordinate arms and a final zero in either coordinate are included. -/
theorem norm_tensor_dividedDifference_decreasing (L i j : ℕ) (x y : ℕ → ℝ)
    (hxnonneg : ∀ k ≤ i, 0 ≤ x k) (hynonneg : ∀ k ≤ j, 0 ≤ y k)
    (hxanti : ∀ a b, a < b → b ≤ i → x b < x a)
    (hyanti : ∀ a b, a < b → b ≤ j → y b < y a)
    (hxratio : ∀ k < i, x (k+1) ≤ x k/2) (hyratio : ∀ k < j, y (k+1) ≤ y k/2)
    (f : ℝ → ℝ → ℂ) (hfx : ∀ b, ContDiff ℝ L (fun a => f a b))
    (hfxy : ∀ r ≤ L, ∀ a, ContDiff ℝ L (fun b => iteratedDeriv r (fun a => f a b) a))
    (A : ℝ) (hA : 0 ≤ A)
    (hderiv : ∀ r ≤ L, ∀ q ≤ L, ∀ a ∈ Icc (0:ℝ) (x 0), ∀ b ∈ Icc (0:ℝ) (y 0),
      ‖iteratedDeriv q (fun b => iteratedDeriv r (fun a => f a b) a) b‖ ≤ A) :
    ‖tensorAnalyticDividedDifference x i y j f‖ ≤
      (4:ℝ)^(i+j)*A/((∏ k ∈ Finset.range (i-L), x k)*(∏ k ∈ Finset.range (j-L), y k)) := by
  have hydist : ∀ a ≤ j, ∀ b ≤ j, a ≠ b → y a ≠ y b := by
    intro a ha b hb hab
    rcases lt_or_gt_of_ne hab with hab | hba
    · exact (hyanti a b hab hb).ne'
    · exact (hyanti b a hba ha).ne
  let G : ℝ → ℂ := fun a => analyticDividedDifference y j (f a)
  have hG : ContDiff ℝ L G :=
    contDiff_parametric_dividedDifference y j L hydist (fun b a => f a b) hfx
  let Ay : ℝ := (4:ℝ)^j*A/(∏ k ∈ Finset.range (j-L), y k)
  have hAy : 0 ≤ Ay := div_nonneg (mul_nonneg (pow_nonneg (by norm_num) _) hA)
    (Finset.prod_nonneg (fun k hk => hynonneg k (by have := Finset.mem_range.mp hk; omega)))
  have hGderiv : ∀ r ≤ L, ∀ a ∈ Icc (0:ℝ) (x 0), ‖iteratedDeriv r G a‖ ≤ Ay := by
    intro r hr a ha
    change ‖iteratedDeriv r (fun a => analyticDividedDifference y j (fun b => f a b)) a‖ ≤ Ay
    rw [iteratedDeriv_parametric_dividedDifference y j r hydist (fun b a => f a b)
      (fun b => (hfx b).of_le (by exact_mod_cast hr)) a]
    exact norm_dividedDifference_decreasing_finite_smoothness L j y hynonneg hyanti hyratio
      (fun b => iteratedDeriv r (fun a => f a b) a) (hfxy r hr a) A hA
      (fun q hq b hb => hderiv r hr q hq a ha b hb)
  have hbound := norm_dividedDifference_decreasing_finite_smoothness L i x hxnonneg hxanti hxratio
    G hG Ay hAy hGderiv
  calc
    _ ≤ (4:ℝ)^i*Ay/(∏ k ∈ Finset.range (i-L), x k) := hbound
    _ = _ := by dsimp [Ay]; rw [pow_add]; ring

/-- The analytic tensor coefficients are the coefficients of the exact tensor
Newton interpolant on every distinct finite grid, including zero endpoints. -/
theorem tensorAnalyticDividedDifference_eq_coefficients {m n : ℕ}
    (x : Fin m → ℝ) (y : Fin n → ℝ) (hx : Function.Injective x) (hy : Function.Injective y)
    (f : ℝ → ℝ → ℂ) (i : Fin m) (j : Fin n) :
    tensorAnalyticDividedDifference (finiteNodeSequence x) i (finiteNodeSequence y) j f =
      tensorNewtonCoefficients (fun a => (x a:ℂ)) (fun b => (y b:ℂ))
        (Complex.ofReal_injective.comp hx) (Complex.ofReal_injective.comp hy)
        (fun a b => f (x a) (y b)) i j := by
  unfold tensorAnalyticDividedDifference tensorNewtonCoefficients
  simp_rw [analyticDividedDifference_eq_dividedDifferences y hy]
  exact analyticDividedDifference_eq_dividedDifferences x hx _ i

end
end MeyerGeneralProblem.Adaptive
