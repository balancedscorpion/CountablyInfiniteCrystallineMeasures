module

public import MeyerGeneralProblem.Interpolation.ConfluentUnisolvence
public import Mathlib.Analysis.Calculus.DSlope
import all Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
import all Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import all Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.Complex.RealDeriv
import all Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import all Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import all Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

/-!
# Analytic divided differences and low-order Hermite–Genocchi formulas

The analytic recursion uses the actual extended divided slope, whose value at a
collapsed node is the derivative.  It agrees with synthetic polynomial divided
differences at every order, including repeated nodes.  Integral representations
and exact derivative bounds are proved at orders one and two, without a
positive node gap.  Differentiation under the first integral is justified by
compact domination, and the extended slope is jointly continuous in its nodes.

The arbitrary-order simplex integral representation is not asserted here.
-/

namespace MeyerGeneralProblem

noncomputable section

open MeasureTheory Set Polynomial
open scoped Topology Interval

section Banach

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The first Hermite–Genocchi identity, including coincident endpoints. -/
theorem dslope_eq_integral_derivative {f f' : ℝ → E} {a b : ℝ}
    (hderiv : ∀ x ∈ uIcc a b, HasDerivAt f (f' x) x)
    (hint : IntervalIntegrable f' volume a b) :
    dslope f a b = ∫ t in (0 : ℝ)..1, f' (a + (b - a) * t) := by
  by_cases hab : b = a
  · subst b
    simp only [dslope_same, sub_self, zero_mul, add_zero,
      intervalIntegral.integral_const, sub_zero, one_smul]
    exact (hderiv a (by simp)).deriv
  · rw [dslope_of_ne f hab, slope_def_module,
      intervalIntegral.integral_comp_add_mul f' (sub_ne_zero.mpr hab) a]
    simp only [mul_zero, add_zero, mul_one]
    rw [show a + (b - a) = b by ring]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]

/-- Every affine interpolation point lies between its two endpoints. -/
theorem affineNode_mem_uIcc (a b : ℝ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    a + (b - a) * t ∈ uIcc a b := by
  rcases le_total a b with hab | hba
  · rw [uIcc_of_le hab]
    constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr hab) ht.1,
      mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr ht.2)]
  · rw [uIcc_of_ge hba]
    constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr hba) ht.1,
      mul_nonneg (sub_nonneg.mpr hba) (sub_nonneg.mpr ht.2)]

/-- A derivative bound controls the divided slope with no inverse-gap factor. -/
theorem norm_dslope_le_of_derivative_bound {f f' : ℝ → E} {a b M : ℝ}
    (hderiv : ∀ x ∈ uIcc a b, HasDerivAt f (f' x) x)
    (hint : IntervalIntegrable f' volume a b)
    (hbound : ∀ x ∈ uIcc a b, ‖f' x‖ ≤ M) :
    ‖dslope f a b‖ ≤ M := by
  rw [dslope_eq_integral_derivative hderiv hint]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (C := M)
    (f := fun t => f' (a + (b - a) * t)) (by
      intro t ht
      have ht' : t ∈ Ioc (0 : ℝ) 1 := by simpa using ht
      exact hbound _ (affineNode_mem_uIcc a b ⟨ht'.1.le, ht'.2⟩))
  simpa using h

/-- A continuously differentiable function has a jointly continuous extended
divided slope; in particular both nodes may coalesce simultaneously. -/
theorem continuous_dslope_of_continuous_derivative {f f' : ℝ → E}
    (hderiv : ∀ x, HasDerivAt f (f' x) x) (hcont : Continuous f') :
    Continuous (fun ab : ℝ × ℝ => dslope f ab.1 ab.2) := by
  have hc : Continuous (fun ab : ℝ × ℝ =>
      ∫ t in Icc (0 : ℝ) 1, f' (ab.1 + (ab.2 - ab.1) * t)) :=
    continuous_parametric_integral_of_continuous (by fun_prop) isCompact_Icc
  convert hc using 1
  funext ab
  rw [dslope_eq_integral_derivative (fun x _ => hderiv x) (hcont.intervalIntegrable _ _),
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_Icc_eq_integral_Ioc]

/-- Differentiating the genuine divided slope gives a weighted second-derivative
integral, including at the collapsed node.  Compactness supplies the domination
needed for differentiation under the integral; no global derivative bound is
assumed. -/
theorem hasDerivAt_dslope_integral {f f' f'' : ℝ → E}
    (hderiv : ∀ x, HasDerivAt f (f' x) x)
    (hderiv' : ∀ x, HasDerivAt f' (f'' x) x) (hcont'' : Continuous f'')
    (a b : ℝ) :
    HasDerivAt (dslope f a)
      (∫ t in (0 : ℝ)..1, t • f'' (a + (b - a) * t)) b := by
  have hcont' : Continuous f' := continuous_iff_continuousAt.mpr
    (fun x => (hderiv' x).continuousAt)
  have hcontinuous : Continuous (fun z : ℝ × ℝ =>
      ‖z.2 • f'' (a + (z.1 - a) * z.2)‖) := by fun_prop
  obtain ⟨M, hM⟩ := ((isCompact_Icc : IsCompact (Icc (b - 1) (b + 1))).prod
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1))).bddAbove_image
      hcontinuous.continuousOn
  have hi := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun x t : ℝ => f' (a + (x - a) * t))
    (F' := fun x t : ℝ => t • f'' (a + (x - a) * t))
    (bound := fun _ => M) (μ := volume)
    (a := (0 : ℝ)) (b := 1) (s := Ioo (b - 1) (b + 1)) (x₀ := b)
    (Ioo_mem_nhds (by linarith) (by linarith))
    (Filter.Eventually.of_forall (fun x =>
      (show Continuous (fun t : ℝ => f' (a + (x - a) * t)) by fun_prop).aestronglyMeasurable))
    (show IntervalIntegrable (fun t : ℝ => f' (a + (b - a) * t)) volume 0 1 from
      (by fun_prop : Continuous (fun t : ℝ => f' (a + (b - a) * t))).intervalIntegrable _ _)
    (show AEStronglyMeasurable (fun t : ℝ => t • f'' (a + (b - a) * t))
        (volume.restrict (Ι (0 : ℝ) 1)) from
      (by fun_prop : Continuous (fun t : ℝ => t • f'' (a + (b - a) * t))).aestronglyMeasurable)
    (Filter.Eventually.of_forall (by
      intro t ht x hx
      have ht' : t ∈ Ioc (0 : ℝ) 1 := by simpa using ht
      exact hM (mem_image_of_mem _ (show (x, t) ∈
        Icc (b - 1) (b + 1) ×ˢ Icc (0 : ℝ) 1 from
          ⟨⟨hx.1.le, hx.2.le⟩, ht'.1.le, ht'.2⟩))))
    (intervalIntegrable_const)
    (Filter.Eventually.of_forall (by
      intro t _ x _
      have hinner : HasDerivAt (fun y : ℝ => a + (y - a) * t) t x := by
        simpa using (((hasDerivAt_id x).sub_const a).mul_const t).const_add a
      exact (hderiv' _).scomp x hinner))
  convert hi.2 using 1
  funext x
  exact dslope_eq_integral_derivative (fun y _ => hderiv y) (hcont'.intervalIntegrable _ _)

omit [CompleteSpace E] in
/-- The derivative integral in the divided-slope recursion is continuous. -/
theorem continuous_dslope_derivative_integral {g : ℝ → E} (hg : Continuous g) (a : ℝ) :
    Continuous (fun b : ℝ => ∫ t in (0 : ℝ)..1, t • g (a + (b - a) * t)) := by
  have hc : Continuous (fun b : ℝ =>
      ∫ t in Icc (0 : ℝ) 1, t • g (a + (b - a) * t)) :=
    continuous_parametric_integral_of_continuous (by fun_prop) isCompact_Icc
  simpa only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_Icc_eq_integral_Ioc] using hc

omit [CompleteSpace E] in
/-- The weighted derivative integral has the exact factorial bound `M / 2`. -/
theorem norm_dslope_derivative_integral_le {g : ℝ → E} {a b M : ℝ}
    (hbound : ∀ x ∈ uIcc a b, ‖g x‖ ≤ M) :
    ‖∫ t in (0 : ℝ)..1, t • g (a + (b - a) * t)‖ ≤ M / 2 := by
  have h := intervalIntegral.norm_integral_le_of_norm_le
    (f := fun t : ℝ => t • g (a + (b - a) * t))
    (μ := volume)
    (a := (0 : ℝ)) (b := 1) (g := fun t => t * M) (by norm_num)
    (Filter.Eventually.of_forall (by
      intro t ht
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1.le]
      exact mul_le_mul_of_nonneg_left
        (hbound _ (affineNode_mem_uIcc a b ⟨ht.1.le, ht.2⟩)) ht.1.le))
    ((continuous_id.mul continuous_const).intervalIntegrable _ _)
  rw [intervalIntegral.integral_mul_const, integral_id] at h
  convert h using 1; ring

/-- Two analytic Newton steps give a weighted double Hermite–Genocchi integral,
even if any or all three nodes coincide. -/
theorem dslope_dslope_eq_integral {f f' f'' : ℝ → E}
    (hderiv : ∀ x, HasDerivAt f (f' x) x)
    (hderiv' : ∀ x, HasDerivAt f' (f'' x) x) (hcont'' : Continuous f'')
    (a b c : ℝ) :
    dslope (dslope f a) b c =
      ∫ u in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1,
        t • f'' (a + (b + (c - b) * u - a) * t) :=
  dslope_eq_integral_derivative
    (fun x _ => hasDerivAt_dslope_integral hderiv hderiv' hcont'' a x)
    ((continuous_dslope_derivative_integral hcont'' a).intervalIntegrable _ _)

/-- The second analytic Newton step has no dependence on any node gap. -/
theorem norm_dslope_dslope_le {f f' f'' : ℝ → E} {a b c L U M : ℝ}
    (hderiv : ∀ x, HasDerivAt f (f' x) x)
    (hderiv' : ∀ x, HasDerivAt f' (f'' x) x) (hcont'' : Continuous f'')
    (ha : a ∈ Icc L U) (hb : b ∈ Icc L U) (hc : c ∈ Icc L U)
    (hbound : ∀ x ∈ Icc L U, ‖f'' x‖ ≤ M) :
    ‖dslope (dslope f a) b c‖ ≤ M / 2 := by
  apply norm_dslope_le_of_derivative_bound
    (fun x _ => hasDerivAt_dslope_integral hderiv hderiv' hcont'' a x)
    ((continuous_dslope_derivative_integral hcont'' a).intervalIntegrable _ _)
  intro x hx
  apply norm_dslope_derivative_integral_le
  intro y hy
  exact hbound y (uIcc_subset_Icc ha (uIcc_subset_Icc hb hc hx) hy)

/-- Full collapse at second order gives half the second derivative, not the
unnormalized second derivative. -/
theorem dslope_dslope_same {f f' f'' : ℝ → E}
    (hderiv : ∀ x, HasDerivAt f (f' x) x)
    (hderiv' : ∀ x, HasDerivAt f' (f'' x) x) (hcont'' : Continuous f'') (a : ℝ) :
    dslope (dslope f a) a a = (1 / 2 : ℝ) • f'' a := by
  rw [dslope_same, (hasDerivAt_dslope_integral hderiv hderiv' hcont'' a a).deriv]
  simp only [sub_self, zero_mul, add_zero, intervalIntegral.integral_smul_const,
    integral_id, one_pow, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    sub_zero]

end Banach

section Analytic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Analytic Newton recursion using actual derivatives at coincident nodes. -/
def analyticDividedDifference (nodes : ℕ → ℝ) : ℕ → (ℝ → E) → E
  | 0, f => f (nodes 0)
  | order + 1, f => analyticDividedDifference (fun i => nodes (i + 1)) order
      (dslope f (nodes 0))

/-- Order-zero analytic divided differences are values. -/
@[simp]
theorem analyticDividedDifference_zero (nodes : ℕ → ℝ) (f : ℝ → E) :
    analyticDividedDifference nodes 0 f = f (nodes 0) := rfl

/-- The analytic successor strips one extended divided slope. -/
theorem analyticDividedDifference_succ (nodes : ℕ → ℝ) (order : ℕ) (f : ℝ → E) :
    analyticDividedDifference nodes (order + 1) f =
      analyticDividedDifference (fun i => nodes (i + 1)) order (dslope f (nodes 0)) := rfl

/-- Order-one analytic divided differences are extended slopes. -/
@[simp]
theorem analyticDividedDifference_one (nodes : ℕ → ℝ) (f : ℝ → E) :
    analyticDividedDifference nodes 1 f = dslope f (nodes 0) (nodes 1) := rfl

/-- Order two consists of two genuine extended divided slopes. -/
@[simp]
theorem analyticDividedDifference_two (nodes : ℕ → ℝ) (f : ℝ → E) :
    analyticDividedDifference nodes 2 f =
      dslope (dslope f (nodes 0)) (nodes 1) (nodes 2) := rfl

/-- At first order the analytic recursion has the Hermite–Genocchi integral
representation, with no ordering or separation hypothesis on the nodes. -/
theorem analyticDividedDifference_one_eq_integral [CompleteSpace E]
    (nodes : ℕ → ℝ) {f f' : ℝ → E}
    (hderiv : ∀ x ∈ uIcc (nodes 0) (nodes 1), HasDerivAt f (f' x) x)
    (hint : IntervalIntegrable f' volume (nodes 0) (nodes 1)) :
    analyticDividedDifference nodes 1 f =
      ∫ t in (0 : ℝ)..1, f' (nodes 0 + (nodes 1 - nodes 0) * t) :=
  dslope_eq_integral_derivative hderiv hint

/-- Order-two Hermite–Genocchi formula for the analytic divided difference,
including all partially and fully collapsed node configurations. -/
theorem analyticDividedDifference_two_eq_integral [CompleteSpace E]
    (nodes : ℕ → ℝ) {f f' f'' : ℝ → E}
    (hderiv : ∀ x, HasDerivAt f (f' x) x)
    (hderiv' : ∀ x, HasDerivAt f' (f'' x) x) (hcont'' : Continuous f'') :
    analyticDividedDifference nodes 2 f =
      ∫ u in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1,
        t • f'' (nodes 0 + (nodes 1 + (nodes 2 - nodes 1) * u - nodes 0) * t) :=
  dslope_dslope_eq_integral hderiv hderiv' hcont'' _ _ _

end Analytic

/-- Extended real divided slopes of a complex polynomial are its exact Newton
quotient, also at the base point. -/
theorem dslope_polynomial_eval (p : ℂ[X]) (a b : ℝ) :
    dslope (fun x : ℝ => p.eval (x : ℂ)) a b =
      (newtonQuotient (a : ℂ) p).eval (b : ℂ) := by
  by_cases hab : b = a
  · subst b
    rw [dslope_same, ((p.hasDerivAt (a : ℂ)).comp_ofReal).deriv]
    exact (polynomialDividedDifference_repeated_node_one (a : ℂ) p).symm
  · have hab' : (b : ℂ) - (a : ℂ) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr hab
    have hfactor := congrArg (fun q : ℂ[X] => q.eval (b : ℂ))
      (X_sub_C_mul_newtonQuotient (a : ℂ) p)
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C] at hfactor
    rw [dslope_of_ne _ hab, slope_def_module, Complex.real_smul,
      Complex.ofReal_inv, Complex.ofReal_sub]
    rw [← hfactor, ← mul_assoc, inv_mul_cancel₀ hab', one_mul]

/-- Every analytic divided difference of a polynomial agrees with the existing
synthetic divided difference, without distinctness or ordering assumptions. -/
theorem analyticDividedDifference_polynomial_eval (nodes : ℕ → ℝ) (order : ℕ)
    (p : ℂ[X]) :
    analyticDividedDifference nodes order (fun x : ℝ => p.eval (x : ℂ)) =
      polynomialDividedDifference (fun i => (nodes i : ℂ)) order p := by
  induction order generalizing nodes p with
  | zero => rfl
  | succ order ih =>
      change analyticDividedDifference (fun i => nodes (i + 1)) order
        (dslope (fun x : ℝ => p.eval (x : ℂ)) (nodes 0)) = _
      rw [show dslope (fun x : ℝ => p.eval (x : ℂ)) (nodes 0) =
        (fun x : ℝ => (newtonQuotient (nodes 0 : ℂ) p).eval (x : ℂ)) from
          funext (dslope_polynomial_eval p (nodes 0))]
      exact ih _ _

/-- Fully collapsed polynomial nodes in the analytic recursion have exactly the
Taylor/Hasse normalization already certified by confluent unisolvence. -/
theorem analyticDividedDifference_polynomial_repeated_node
    (a : ℝ) (order : ℕ) (p : ℂ[X]) :
    analyticDividedDifference (fun _ => a) order (fun x : ℝ => p.eval (x : ℂ)) =
      (Polynomial.taylor (a : ℂ) p).coeff order := by
  rw [analyticDividedDifference_polynomial_eval,
    polynomialDividedDifference_repeated_node]

/-- The first synthetic polynomial divided difference is an actual derivative
integral, including repeated real nodes. -/
theorem polynomialDividedDifference_one_eq_integral (nodes : ℕ → ℝ) (p : ℂ[X]) :
    polynomialDividedDifference (fun i => (nodes i : ℂ)) 1 p =
      ∫ t in (0 : ℝ)..1,
        p.derivative.eval ((nodes 0 + (nodes 1 - nodes 0) * t : ℝ) : ℂ) := by
  rw [← analyticDividedDifference_polynomial_eval]
  apply analyticDividedDifference_one_eq_integral (f' := fun x : ℝ => p.derivative.eval (x : ℂ))
  · intro x _
    exact (p.hasDerivAt (x : ℂ)).comp_ofReal
  · exact (p.derivative.differentiable.continuous.comp
      Complex.continuous_ofReal).intervalIntegrable _ _

end

end MeyerGeneralProblem
