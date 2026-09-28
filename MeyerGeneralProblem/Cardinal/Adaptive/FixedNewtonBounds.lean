module

public import MeyerGeneralProblem.Cardinal.Adaptive.ShrinkingNewtonMembership

@[expose] public section

/-! # Fixed small-chart estimates for the complete Newton array -/
open scoped ContDiff
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open Set
open scoped FourierTransform Topology

/-- A small fixed chart bounds every cosine-difference factor, without a
positive lower bound on any phase; zero endpoint phases are included. -/
theorem fixedNewton_factor_bound (b ε x : ℝ) (hb : 0 < b) (hb' : b ≤ 1/2)
    (hε : |ε| ≤ b) (hx : |x| ≤ b) :
    |Real.cos (2*Real.pi*ε)-Real.cos (2*Real.pi*x)| ≤ 64*b^2 := by
  have h1 := shrinkingNewton_cos_factor_le b ε hb.le hb' hε
  have h2 := shrinkingNewton_cos_factor_le b x hb.le hb' hx
  have h := abs_sub_le (Real.cos (2*Real.pi*ε)) (Real.cos (2*Real.pi*b))
    (Real.cos (2*Real.pi*x))
  rw [abs_sub_comm (Real.cos (2*Real.pi*b)) (Real.cos (2*Real.pi*ε))] at h1
  linarith

/-- Fixed-chart geometric derivative bounds preserve the small zeroth-order
factor, including at phases exactly equal to zero. -/
theorem fixedNewton_factor_derivative_bound (b ε x : ℝ) (hb : 0 < b)
    (hb' : b ≤ 1/8) (hε : |ε| ≤ b) (hx : |x| ≤ b) (n : ℕ) :
    ‖iteratedDeriv n (fun y => Real.cos (2*Real.pi*ε)-Real.cos (2*Real.pi*y)) x‖ ≤
      (64*b^2)*(2*Real.pi/(64*b^2))^n := by
  by_cases hn : n=0
  · subst n
    simpa only [iteratedDeriv_zero,pow_zero,mul_one,Real.norm_eq_abs] using
      fixedNewton_factor_bound b ε x hb (by linarith) hε hx
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have he : iteratedDeriv n (fun y => Real.cos (2*Real.pi*ε)-Real.cos (2*Real.pi*y)) x =
        -((2*Real.pi)^n*iteratedDeriv n Real.cos (2*Real.pi*x)) := by
      rw [iteratedDeriv_const_sub hnpos,iteratedDeriv_neg]
      have hh := congrFun (iteratedDeriv_comp_const_mul (n := n)
        (Real.contDiff_cos : ContDiff ℝ n Real.cos) (2*Real.pi)) x
      simpa only [Pi.neg_apply] using congrArg Neg.neg hh
    rw [he,norm_neg,norm_mul,norm_pow,Real.norm_eq_abs,abs_of_pos (by positivity : 0 < 2*Real.pi)]
    have hθ0 : 0 < 64*b^2 := by positivity
    have hθ1 : 64*b^2 ≤ 1 := by nlinarith
    have hp : (64*b^2)^n ≤ 64*b^2 := by
      simpa only [pow_one] using pow_le_pow_of_le_one hθ0.le hθ1 hnpos
    calc
      _ ≤ (2*Real.pi)^n*1 := mul_le_mul_of_nonneg_left
        (Real.abs_iteratedDeriv_cos_le_one n _) (by positivity)
      _ ≤ _ := by
        rw [mul_one,div_pow,←mul_div_assoc]
        apply (le_div_iff₀ (pow_pos hθ0 n)).mpr
        nlinarith [mul_le_mul_of_nonneg_left hp (pow_nonneg (by positivity : 0 ≤ 2*Real.pi) n)]

/-- Every derivative of the complete finite Newton product has exponential
smallness in its level and only polynomial fixed-order loss. -/
theorem fixedNewton_product_derivative_bound (ε : ℕ → ℝ) (i n : ℕ) (b x : ℝ)
    (hb : 0 < b) (hb' : b ≤ 1/8) (hε : ∀ l < i, |ε (l+1)| ≤ b) (hx : |x| ≤ b) :
    ‖iteratedDeriv n (fun y => ∏ l ∈ Finset.range i,
      (Real.cos (2*Real.pi*ε (l+1))-Real.cos (2*Real.pi*y))) x‖ ≤
      (64*b^2)^i*((i:ℝ)*(2*Real.pi/(64*b^2)))^n := by
  have h := iteratedDeriv_product_geometric_bound i
    (fun l y => Real.cos (2*Real.pi*ε (l+1))-Real.cos (2*Real.pi*y))
    (by intro l; fun_prop) (fun _ => 64*b^2) (fun _ => 2*Real.pi/(64*b^2))
    (by intro l; positivity) (by intro l; positivity) n x
    (by intro l r hr; exact fixedNewton_factor_derivative_bound b (ε (l+1)) x hb hb' (hε l l.isLt) hx r)
  have he (y : ℝ) : (∏ j : Fin i, (Real.cos (2*Real.pi*ε (j.val+1))-Real.cos (2*Real.pi*y)))=
      ∏ l ∈ Finset.range i, (Real.cos (2*Real.pi*ε (l+1))-Real.cos (2*Real.pi*y)) :=
    Fin.prod_univ_eq_prod_range (fun l : ℕ => Real.cos (2*Real.pi*ε (l+1))-Real.cos (2*Real.pi*y)) i
  simpa only [he,Finset.prod_const,Finset.card_univ,Fintype.card_fin,
    Finset.sum_const,nsmul_eq_mul] using h

private theorem real_cast_iteratedDeriv (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (r : ℕ) :
    iteratedDeriv r (fun x => (f x : ℂ)) = fun x => Complex.ofReal (iteratedDeriv r f x) := by
  induction r with
  | zero => rfl
  | succ r ih =>
      rw [iteratedDeriv_succ,ih,iteratedDeriv_succ]
      funext x
      exact (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x
        (((hf.of_le (show ((r+1:ℕ):ℕ∞ω) ≤ ∞ by simp)).differentiable_iteratedDeriv' r).differentiableAt.hasDerivAt)).deriv

/-- The actual fixed compact Newton tests have exponential decay with only
polynomial level loss at each fixed derivative order, uniformly in all small phases. -/
theorem fixedNewtonTest_derivative_bound (a b : ℝ) (hab : a < b)
    (hb : 0 < b) (hb' : b ≤ 1/8) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε : ℕ → ℝ) (i : ℕ) (e : Bool),
      (∀ l < i, |ε (l+1)| ≤ b) → ∀ n ≤ m, ∀ x : ℝ,
      ‖iteratedDeriv n (shrinkingNewtonTest (fun j => ε j) i e a b hab) x‖ ≤
        C*(64*b^2)^i*((i:ℝ)+1)^m := by
  let f (e : Bool) := shrinkingNewtonTest (fun _ => 0) 0 e a b hab
  let A : ℝ := 1+∑ e : Bool, ∑ n ∈ Finset.range (m+1), SchwartzMap.seminorm ℂ 0 n (f e)
  let B : ℝ := 2*Real.pi/(64*b^2)
  have hA : 0 < A := by
    have hh : 0 ≤ ∑ e : Bool, ∑ n ∈ Finset.range (m+1), SchwartzMap.seminorm ℂ 0 n (f e) :=
      Finset.sum_nonneg (fun e _ => Finset.sum_nonneg (fun n _ => apply_nonneg (SchwartzMap.seminorm ℂ 0 n) (f e)))
    dsimp only [A]; linarith
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hf (e : Bool) (n : ℕ) (hn : n ≤ m) (x : ℝ) : ‖iteratedDeriv n (f e) x‖ ≤ A := by
    have hh := SchwartzMap.le_seminorm' ℂ 0 n (f e) x
    simp only [pow_zero,one_mul] at hh
    apply hh.trans
    have h1 := Finset.single_le_sum (s := Finset.range (m+1)) (a := n)
      (f := fun r => SchwartzMap.seminorm ℂ 0 r (f e)) (by intro r hr; exact apply_nonneg (SchwartzMap.seminorm ℂ 0 r) (f e))
      (Finset.mem_range.mpr (show n<m+1 by omega))
    have h2 := Finset.single_le_sum (s := Finset.univ) (a := e)
      (f := fun z => ∑ r ∈ Finset.range (m+1), SchwartzMap.seminorm ℂ 0 r (f z))
      (by intro z hz; exact Finset.sum_nonneg (fun r _ => apply_nonneg (SchwartzMap.seminorm ℂ 0 r) (f z))) (Finset.mem_univ e)
    dsimp only [A]
    linarith
  refine ⟨A*(1+B)^m,by positivity,fun ε i e hε n hn x => ?_⟩
  by_cases hx : |x| ≤ b
  · let D : ℝ → ℝ := fun y => ∏ l ∈ Finset.range i,
        (Real.cos (2*Real.pi*ε (l+1))-Real.cos (2*Real.pi*y))
    have hD : ContDiff ℝ ∞ D := by dsimp [D]; fun_prop
    have he : (shrinkingNewtonTest (fun j => ε j) i e a b hab : ℝ → ℂ)=
        (f e : ℝ → ℂ)*(fun y => (D y:ℂ)) := by
      funext y
      simp only [shrinkingNewtonTest_apply,halfNewtonFunction,halfNewtonProduct_cosine_product,
        Pi.mul_apply,f,D]
      have hz : halfNewtonProduct (fun _ => 0) 0 y=1 := by simp [halfNewtonProduct]
      rw [hz]
      split_ifs <;> ring
    have hDc : ContDiff ℝ ∞ (fun y => (D y:ℂ)) := Complex.ofRealCLM.contDiff.comp hD
    rw [he,iteratedDeriv_mul ((f e).smooth n).contDiffAt
      (hDc.of_le (by simp)).contDiffAt]
    apply (norm_sum_le _ _).trans
    have hp (r : ℕ) : ‖iteratedDeriv r (fun y => (D y:ℂ)) x‖ ≤
        (64*b^2)^i*((i:ℝ)*B)^r := by
      rw [real_cast_iteratedDeriv D hD,Complex.norm_real,Real.norm_eq_abs]
      exact fixedNewton_product_derivative_bound ε i r b x hb hb' hε hx
    calc
      _ ≤ ∑ l ∈ Finset.range (n+1), (n.choose l:ℝ)*A*((64*b^2)^i*((i:ℝ)*B)^(n-l)) := by
        apply Finset.sum_le_sum
        intro l hl
        simp only [norm_mul,Complex.norm_natCast]
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hf e l (by have := Finset.mem_range.mp hl; omega) x)
          (by positivity)) (hp (n-l)) (norm_nonneg _) (by positivity)
      _ = A*(64*b^2)^i*(1+(i:ℝ)*B)^n := by
        rw [add_pow,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l hl
        rw [one_pow]
        ring
      _ ≤ A*(64*b^2)^i*((1+B)*((i:ℝ)+1))^m := by
        gcongr
        exact pow_le_pow_left₀ (by positivity) (by nlinarith [Nat.cast_nonneg (α:=ℝ) i]) n |>.trans
          (pow_le_pow_right₀ (by nlinarith [Nat.cast_nonneg (α:=ℝ) i]) hn)
      _ = _ := by rw [mul_pow (1+B)]; ring
  · have hx' : b < |x| := lt_of_not_ge hx
    have hz : (shrinkingNewtonTest (fun j => ε j) i e a b hab : ℝ → ℂ)=ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [(isOpen_lt continuous_const continuous_abs).mem_nhds hx'] with y hy
      exact shrinkingNewtonTest_zero _ _ _ _ _ hab y hy.le
    rw [hz.iteratedDeriv_eq n]
    simp only [iteratedDeriv_const]
    split_ifs <;> simp only [norm_zero] <;> positivity

/-- The original positive Hermite norm of a complete fixed-chart Newton test
has the same exponential level decay and exactly 2p polynomial loss. -/
theorem fixedNewtonTest_native_bound (a b : ℝ) (hab : a < b)
    (hb : 0 < b) (hb' : b ≤ 1/8) (p : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε : ℕ → ℝ) (i : ℕ) (e : Bool),
      (∀ l < i, |ε (l+1)| ≤ b) →
      ‖schwartzToHermiteScale p (shrinkingNewtonTest (fun j => ε j) i e a b hab)‖ ≤
        C*(64*b^2)^i*((i:ℝ)+1)^(2*p) := by
  obtain ⟨C,hC,hbound⟩ := exists_hermite_norm_bound_of_compact_derivatives p
  obtain ⟨D,hD,hd⟩ := fixedNewtonTest_derivative_bound a b hab hb hb' (2*p)
  refine ⟨C*D,by positivity,fun ε i e hε => ?_⟩
  have hh := hbound (shrinkingNewtonTest (fun j => ε j) i e a b hab) b
    (D*(64*b^2)^i*((i:ℝ)+1)^(2*p)) (by linarith) (by positivity)
    (shrinkingNewtonTest_zero _ _ _ _ _ hab) (hd ε i e hε)
  simpa only [mul_assoc] using hh

/-- Pairing the original native source with two complete fixed-chart tests
has a uniform two-index exponential bound; neither infinite arm is removed. -/
theorem fixedNewtonBilinear_native_bound (a b : ℝ) (hab : a < b)
    (hb : 0 < b) (hb' : b ≤ 1/8) (p : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : HermiteScale (-(p:ℤ))) (ε δ : ℕ → ℝ)
      (i j : ℕ) (e f : Bool), (∀ l < i, |ε (l+1)| ≤ b) → (∀ l < j, |δ (l+1)| ≤ b) →
      ‖halfNewtonBilinear (hermiteScaleDistribution p T)
        (shrinkingNewtonTest (fun l => ε l) i e a b hab)
        (shrinkingNewtonTest (fun l => δ l) j f a b hab)‖ ≤
      C*‖T‖*((64*b^2)^i*((i:ℝ)+1)^(2*p))*((64*b^2)^j*((j:ℝ)+1)^(2*p)) := by
  obtain ⟨C,hC,hbound⟩ := exists_halfNewtonBilinear_native_bound p
  obtain ⟨D,hD,hd⟩ := fixedNewtonTest_native_bound a b hab hb hb' p
  refine ⟨C*D*D,by positivity,fun T ε δ i j e f hε hδ => ?_⟩
  have hh := hbound T (shrinkingNewtonTest (fun l => ε l) i e a b hab)
    (shrinkingNewtonTest (fun l => δ l) j f a b hab) b (by linarith)
    (shrinkingNewtonTest_zero _ _ _ _ _ hab) (shrinkingNewtonTest_zero _ _ _ _ _ hab)
  apply hh.trans
  calc
    _ ≤ C*‖T‖*(D*(64*b^2)^i*((i:ℝ)+1)^(2*p))*(D*(64*b^2)^j*((j:ℝ)+1)^(2*p)) := by
      gcongr
      · exact hd ε i e hε
      · exact hd δ j f hδ
    _ = _ := by ring

end
end MeyerGeneralProblem.Adaptive
