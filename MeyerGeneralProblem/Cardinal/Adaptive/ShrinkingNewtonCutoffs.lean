module

public import MeyerGeneralProblem.Cardinal.Adaptive.ShrinkingNewtonDerivatives
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import all Mathlib.Analysis.SpecialFunctions.SmoothTransition

@[expose] public section

/-! Genuine smooth tail cutoffs with fixed-order gap derivative costs. -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open Filter Set
open scoped Topology ContDiff

/-- The actual smooth tail cutoff equals one on the smaller interval and
vanishes outside the larger one, with transitions paid by their gap. -/
def shrinkingTailCutoff (a b : ℝ) (x : ℝ) : ℝ :=
  Real.smoothTransition ((x+b)/(b-a))*Real.smoothTransition ((b-x)/(b-a))

/-- The constructed cutoff is smooth for every pair of radii. -/
theorem shrinkingTailCutoff_smooth (a b : ℝ) : ContDiff ℝ ∞ (shrinkingTailCutoff a b) := by
  unfold shrinkingTailCutoff
  fun_prop

/-- The cutoff retains the entire inner tail, including the accumulation point. -/
theorem shrinkingTailCutoff_one (a b x : ℝ) (hab : a < b) (hx : |x| ≤ a) :
    shrinkingTailCutoff a b x = 1 := by
  have hg : 0 < b-a := sub_pos.mpr hab
  have hp : 1 ≤ (x+b)/(b-a) := (le_div_iff₀ hg).mpr (by linarith [(abs_le.mp hx).1])
  have hm : 1 ≤ (b-x)/(b-a) := (le_div_iff₀ hg).mpr (by linarith [(abs_le.mp hx).2])
  simp only [shrinkingTailCutoff,Real.smoothTransition.one_of_one_le hp,
    Real.smoothTransition.one_of_one_le hm,mul_one]

/-- No cutoff support is introduced outside the outer tail radius. -/
theorem shrinkingTailCutoff_zero (a b x : ℝ) (hab : a < b) (hx : b ≤ |x|) :
    shrinkingTailCutoff a b x = 0 := by
  have hg : 0 ≤ b-a := (sub_pos.mpr hab).le
  rcases le_abs.mp hx with hx | hx
  · have hm : (b-x)/(b-a) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hg
    simp [shrinkingTailCutoff,Real.smoothTransition.zero_of_nonpos hm]
  · have hp : (x+b)/(b-a) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hg
    simp [shrinkingTailCutoff,Real.smoothTransition.zero_of_nonpos hp]

/-- Every derivative of the fixed transition function has a global finite bound. -/
theorem smoothTransition_iteratedDeriv_bound (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x, ‖iteratedDeriv n Real.smoothTransition x‖ ≤ C := by
  have hs : ContDiff ℝ ∞ Real.smoothTransition := by fun_prop
  have hc := hs.continuous_iteratedDeriv n (by simp)
  obtain ⟨C,hC⟩ := (isCompact_Icc : IsCompact (Icc (-1:ℝ) 2)).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨|C|+1,by positivity,fun x => ?_⟩
  by_cases hx : x ∈ Icc (-1:ℝ) 2
  · exact (hC x hx).trans (by linarith [le_abs_self C])
  · have hconstant : ∃ c : ℝ, |c| ≤ 1 ∧ Real.smoothTransition =ᶠ[𝓝 x] (fun _ => c) := by
      have hx' : x < -1 ∨ 2 < x := by simpa only [mem_Icc,not_and_or,not_le] using hx
      rcases hx' with hh | hh
      · refine ⟨0,by norm_num,?_⟩
        filter_upwards [eventually_lt_nhds (show x < 0 by linarith)] with y hy
        exact Real.smoothTransition.zero_of_nonpos hy.le
      · refine ⟨1,by norm_num,?_⟩
        filter_upwards [eventually_gt_nhds (show 1 < x by linarith)] with y hy
        exact Real.smoothTransition.one_of_one_le hy.le
    obtain ⟨c,hc,hce⟩ := hconstant
    rw [hce.iteratedDeriv_eq n,iteratedDeriv_const]
    split_ifs <;> simp only [norm_zero,Real.norm_eq_abs]
    · linarith [abs_nonneg C]
    · positivity

/-- A translated affine transition pays exactly one inverse width per derivative. -/
theorem smoothTransition_affine_derivative_bound (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ a c x : ℝ,
      ‖iteratedDeriv n (fun y => Real.smoothTransition (a*y+c)) x‖ ≤ C*|a|^n := by
  obtain ⟨C,hC,hbound⟩ := smoothTransition_iteratedDeriv_bound n
  refine ⟨C,hC,fun a c x => ?_⟩
  have hs : ContDiff ℝ n (fun y => Real.smoothTransition (y+c)) := by fun_prop
  have he := congrFun (iteratedDeriv_comp_const_mul (n := n) hs a) x
  rw [he]
  have hh := congrFun (iteratedDeriv_comp_add_const n Real.smoothTransition c) (a*x)
  rw [hh,norm_mul,norm_pow,Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left (hbound _) (by positivity)).trans_eq (mul_comm _ _)

/-- Every fixed derivative order of the actual tail cutoff has the precise
gap cost needed by shrinking Newton membership. Constants do not depend on
the tail index, either radius, or the distance of the support to the boundary. -/
theorem shrinkingTailCutoff_derivative_bound (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ a b : ℝ, a < b → ∀ x : ℝ,
      ‖iteratedDeriv n (shrinkingTailCutoff a b) x‖ ≤ C/(b-a)^n := by
  choose C hC hbound using smoothTransition_affine_derivative_bound
  let D : ℝ := ∑ k ∈ Finset.range (n+1), (n.choose k:ℝ)*C k*C (n-k)
  have hD : 0 ≤ D := Finset.sum_nonneg (fun k _ =>
    mul_nonneg (mul_nonneg (by positivity) (hC k).le) (hC (n-k)).le)
  refine ⟨D+1,by positivity,fun a b hab x => ?_⟩
  have hg : 0 < b-a := sub_pos.mpr hab
  let f := fun y : ℝ => Real.smoothTransition ((y+b)/(b-a))
  let g := fun y : ℝ => Real.smoothTransition ((b-y)/(b-a))
  have hf : ContDiff ℝ n f := by dsimp [f]; fun_prop
  have hgg : ContDiff ℝ n g := by dsimp [g]; fun_prop
  have hfb (r : ℕ) : ‖iteratedDeriv r f x‖ ≤ C r/(b-a)^r := by
    have he : f = fun y => Real.smoothTransition ((b-a)⁻¹*y+b/(b-a)) := by
      ext y; dsimp [f]; congr 1; ring
    rw [he]
    simpa only [abs_of_pos (inv_pos.mpr hg),inv_pow,div_eq_mul_inv] using
      hbound r (b-a)⁻¹ (b/(b-a)) x
  have hgb (r : ℕ) : ‖iteratedDeriv r g x‖ ≤ C r/(b-a)^r := by
    have he : g = fun y => Real.smoothTransition (-(b-a)⁻¹*y+b/(b-a)) := by
      ext y; dsimp [g]; congr 1; ring
    rw [he]
    simpa only [abs_neg,abs_of_pos (inv_pos.mpr hg),inv_pow,div_eq_mul_inv] using
      hbound r (-(b-a)⁻¹) (b/(b-a)) x
  change ‖iteratedDeriv n (f*g) x‖ ≤ _
  rw [iteratedDeriv_mul hf.contDiffAt hgg.contDiffAt]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ k ∈ Finset.range (n+1), (n.choose k:ℝ)*(C k/(b-a)^k)*(C (n-k)/(b-a)^(n-k)) := by
      apply Finset.sum_le_sum
      intro k hk
      simp only [norm_mul,Real.norm_natCast]
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hfb k) (by positivity)) (hgb (n-k))
        (norm_nonneg _) (mul_nonneg (by positivity) (div_nonneg (hC k).le (by positivity)))
    _ = D/(b-a)^n := by
      dsimp only [D]
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro k hk
      have hkn : k+(n-k)=n := Nat.add_sub_of_le (by simpa using hk)
      have hpow : (b-a)^n = (b-a)^k*(b-a)^(n-k) := by rw [← pow_add,hkn]
      rw [hpow]
      ring
    _ ≤ (D+1)/(b-a)^n := by gcongr; linarith

/-- The constructed cutoff is identically one on a neighborhood of every
point strictly inside its inner radius. -/
theorem shrinkingTailCutoff_eventually_one (a b x : ℝ) (hab : a < b) (hx : |x| < a) :
    shrinkingTailCutoff a b =ᶠ[𝓝 x] (fun _ => 1) := by
  filter_upwards [(continuous_abs.tendsto x).eventually (eventually_lt_nhds hx)] with y hy
  exact shrinkingTailCutoff_one a b y hab hy.le

private theorem two_factor_derivative_bound (n : ℕ) (x A B C D : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (f g : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hfb : ∀ r ≤ n, ‖iteratedDeriv r f x‖ ≤ A*B^r)
    (hgb : ∀ r ≤ n, ‖iteratedDeriv r g x‖ ≤ C*D^r) :
    ‖iteratedDeriv n (f*g) x‖ ≤ A*C*(B+D)^n := by
  have h := iteratedDeriv_product_geometric_bound 2 ![f,g]
    (by intro j; fin_cases j; exact hf; exact hg)
    ![A,C] ![B,D] (by intro j; fin_cases j <;> simp [hA,hC])
    (by intro j; fin_cases j <;> simp [hB,hD]) n x
    (by intro j r hr; fin_cases j; exact hfb r hr; exact hgb r hr)
  simpa only [Fin.prod_univ_two,Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one] using! h

/-- The complete cutoff Newton product satisfies the retained fixed-order
estimate, retaining every squared distance factor and exactly the gap and
inverse-distance derivative costs. -/
theorem shrinkingTailCutoff_newton_derivative_bound (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε : ℕ → ℝ) (i : ℕ) (a b δ : ℝ),
      a < b → b-a ≤ 1 → b ≤ δ → 0 < δ → δ ≤ 1 →
      (∀ l < i, δ ≤ ε (l+1) ∧ ε (l+1) ≤ 1/2) → ∀ x : ℝ,
      ‖iteratedDeriv n (fun y => shrinkingTailCutoff a b y *
        ∏ l ∈ Finset.range i, (Real.cos (2*Real.pi*ε (l+1))-Real.cos (2*Real.pi*y))) x‖ ≤
      C*((i:ℝ)+1)^n/(b-a)^n/δ^(2*n)*(32:ℝ)^i*(shrinkingNewtonWeight ε i)^2 := by
  choose E hE hEb using shrinkingTailCutoff_derivative_bound
  let A : ℝ := 1+∑ r ∈ Finset.range (n+1), E r
  have hA : 0 < A := by
    have hs : 0 ≤ ∑ r ∈ Finset.range (n+1), E r := Finset.sum_nonneg (fun r _ => (hE r).le)
    dsimp [A]
    linarith
  have hEA (r : ℕ) (hr : r ≤ n) : E r ≤ A := by
    have he := Finset.single_le_sum (s := Finset.range (n+1)) (f := E)
      (fun j _ => (hE j).le) (Finset.mem_range.mpr (by omega : r < n+1))
    dsimp [A]
    linarith
  refine ⟨A*(1+2*Real.pi)^n,by positivity,fun ε i a b δ hab hgap1 hbδ hδ hδ1 hε x => ?_⟩
  have hgap : 0 < b-a := sub_pos.mpr hab
  let f := shrinkingTailCutoff a b
  let g := fun y => ∏ l ∈ Finset.range i, (Real.cos (2*Real.pi*ε (l+1))-Real.cos (2*Real.pi*y))
  let K := (32:ℝ)^i*(shrinkingNewtonWeight ε i)^2
  by_cases hx : |x| ≤ δ
  · have hfb (r : ℕ) (hr : r ≤ n) : ‖iteratedDeriv r f x‖ ≤ A*((b-a)⁻¹)^r := by
      have he := (hEb r a b hab x).trans (div_le_div_of_nonneg_right (hEA r hr) (by positivity))
      simpa only [div_eq_mul_inv,inv_pow] using he
    have hgb (r : ℕ) (_hr : r ≤ n) : ‖iteratedDeriv r g x‖ ≤ K*((i:ℝ)*(2*Real.pi/δ^2))^r :=
      shrinkingNewton_product_derivative_le ε i r δ x hδ hε hx
    have hmain := two_factor_derivative_bound n x A (b-a)⁻¹ K ((i:ℝ)*(2*Real.pi/δ^2))
      hA.le (by positivity) (by dsimp [K]; positivity) (by positivity) f g
      (shrinkingTailCutoff_smooth a b) (by dsimp [g]; fun_prop) hfb hgb
    have hrate : (b-a)⁻¹+(i:ℝ)*(2*Real.pi/δ^2) ≤
        (1+2*Real.pi)*((i:ℝ)+1)/((b-a)*δ^2) := by
      apply (le_div_iff₀ (mul_pos hgap (sq_pos_of_pos hδ))).mpr
      have hgprod : (i:ℝ)*(2*Real.pi)*(b-a) ≤ (i:ℝ)*(2*Real.pi) := by
        exact (mul_le_mul_of_nonneg_left hgap1 (by positivity)).trans_eq (mul_one _)
      have he : ((b-a)⁻¹+(i:ℝ)*(2*Real.pi/δ^2))*((b-a)*δ^2) = δ^2+(i:ℝ)*(2*Real.pi)*(b-a) := by
        field_simp
      rw [he]
      nlinarith [Real.pi_pos]
    apply hmain.trans
    calc
      _ ≤ A*K*((1+2*Real.pi)*((i:ℝ)+1)/((b-a)*δ^2))^n := by gcongr
      _ = _ := by
        dsimp [K]
        simp only [div_pow,mul_pow,← pow_mul]
        ring
  · have hxb : b < |x| := lt_of_le_of_lt hbδ (lt_of_not_ge hx)
    have he : (fun y => f y*g y) =ᶠ[𝓝 x] (fun _ => (0:ℝ)) := by
      filter_upwards [(continuous_abs.tendsto x).eventually (eventually_gt_nhds hxb)] with y hy
      rw [show f y=0 from shrinkingTailCutoff_zero a b y hab hy.le,zero_mul]
    rw [he.iteratedDeriv_eq n]
    simp only [iteratedDeriv_const,ite_self,norm_zero]
    positivity

end
end MeyerGeneralProblem.Adaptive
