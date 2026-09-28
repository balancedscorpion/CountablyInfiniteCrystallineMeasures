module

public import MeyerGeneralProblem.Cardinal.Adaptive.ShrinkingNewtonTests
public import MeyerGeneralProblem.Cardinal.Adaptive.ZakSharpBounds

@[expose] public section

/-! Sharp fixed-order norm costs of genuine shrinking Newton Schwartz tests. -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open Set MeasureTheory
open scoped ContDiff

private theorem real_cast_iteratedDeriv (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (r : ℕ) :
    iteratedDeriv r (fun x => (f x : ℂ)) = fun x => Complex.ofReal (iteratedDeriv r f x) := by
  induction r with
  | zero => rfl
  | succ r ih =>
      rw [iteratedDeriv_succ,ih,iteratedDeriv_succ]
      funext x
      exact (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x
        (((hf.of_le (show ((r+1:ℕ):ℕ∞ω) ≤ ∞ by simp)).differentiable_iteratedDeriv' r).differentiableAt.hasDerivAt)).deriv

private theorem parity_derivative_bound (e : Bool) (n : ℕ) (x : ℝ) :
    ‖iteratedDeriv n (fun y => if e then Real.sin (Real.pi*y) else Real.cos (Real.pi*y)) x‖ ≤ Real.pi^n := by
  cases e
  · simp only [Bool.false_eq_true,ite_false]
    rw [iteratedDeriv_comp_const_mul (by fun_prop : ContDiff ℝ n Real.cos)]
    simp only [Pi.smul_apply,smul_eq_mul,norm_mul,norm_pow,Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
    exact (mul_le_mul_of_nonneg_left (Real.abs_iteratedDeriv_cos_le_one n _) (by positivity)).trans_eq (mul_one _)
  · simp only [ite_true]
    rw [iteratedDeriv_comp_const_mul (by fun_prop : ContDiff ℝ n Real.sin)]
    simp only [Pi.smul_apply,smul_eq_mul,norm_mul,norm_pow,Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
    exact (mul_le_mul_of_nonneg_left (Real.abs_iteratedDeriv_sin_le_one n _) (by positivity)).trans_eq (mul_one _)

/-- Both actual Newton parities retain precisely the same fixed-order shrinking
cutoff cost, with constants independent of the level and all phase values. -/
theorem shrinkingNewtonTest_derivative_bound (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε : ℕ → ℝ) (i : ℕ) (e : Bool) (a b δ : ℝ)
      (hab : a < b), b-a ≤ 1 → b ≤ δ → 0 < δ → δ ≤ 1 →
      (∀ l < i, δ ≤ ε (l+1) ∧ ε (l+1) ≤ 1/2) → ∀ x : ℝ,
      ‖iteratedDeriv n (shrinkingNewtonTest (fun j => ε j) i e a b hab) x‖ ≤
      C*((i:ℝ)+1)^n/(b-a)^n/δ^(2*n)*(32:ℝ)^i*(shrinkingNewtonWeight ε i)^2 := by
  choose E hE hEb using shrinkingTailCutoff_newton_derivative_bound
  let A : ℝ := 1+∑ r ∈ Finset.range (n+1), E r
  have hA : 0 < A := by
    have hs := Finset.sum_nonneg (s := Finset.range (n+1)) (f := E) (fun r _ => (hE r).le)
    dsimp [A]; linarith
  have hEA (r : ℕ) (hr : r ≤ n) : E r ≤ A := by
    have h := Finset.single_le_sum (s := Finset.range (n+1)) (f := E)
      (fun j _ => (hE j).le) (Finset.mem_range.mpr (show r<n+1 by omega))
    dsimp [A]; linarith
  refine ⟨A*(1+Real.pi)^n,by positivity,fun ε i e a b δ hab hgap1 hbδ hδ hδ1 hε x => ?_⟩
  let K : ℝ := ((i:ℝ)+1)/((b-a)*δ^2)
  let B : ℝ := (32:ℝ)^i*(shrinkingNewtonWeight ε i)^2
  let f : ℝ → ℝ := fun y => shrinkingTailCutoff a b y *
    ∏ l ∈ Finset.range i, (Real.cos (2*Real.pi*ε (l+1))-Real.cos (2*Real.pi*y))
  let g : ℝ → ℝ := fun y => if e then Real.sin (Real.pi*y) else Real.cos (Real.pi*y)
  have hgap : 0 < b-a := sub_pos.mpr hab
  have hK : 1 ≤ K := by
    apply (le_div_iff₀ (by positivity : 0 < (b-a)*δ^2)).mpr
    have hd2 : δ^2 ≤ 1 := pow_le_one₀ hδ.le hδ1
    have hg2 : (b-a)*δ^2 ≤ 1 := (mul_le_mul hgap1 hd2 (by positivity) (by norm_num)).trans_eq (one_mul 1)
    nlinarith [Nat.cast_nonneg (α := ℝ) i]
  have hfs : ContDiff ℝ ∞ f := by
    dsimp [f]; exact (shrinkingTailCutoff_smooth a b).mul (by fun_prop)
  have hgs : ContDiff ℝ ∞ g := by cases e <;> dsimp [g] <;> fun_prop
  have hfb (r : ℕ) (hr : r ≤ n) : ‖iteratedDeriv r f x‖ ≤ (A*B)*K^r := by
    have h := hEb r ε i a b δ hab hgap1 hbδ hδ hδ1 hε x
    have he : E r*((i:ℝ)+1)^r/(b-a)^r/δ^(2*r)*(32:ℝ)^i*(shrinkingNewtonWeight ε i)^2 =
        (E r*B)*K^r := by
      dsimp [B,K]
      rw [div_pow,mul_pow,show 2*r=r*2 by omega,pow_mul]
      ring
    change ‖iteratedDeriv r f x‖ ≤ _ at h
    rw [he] at h
    exact h.trans (by gcongr; exact hEA r hr)
  have hprod := iteratedDeriv_product_geometric_bound 2 ![f,g]
    (by intro j; fin_cases j; exact hfs; exact hgs)
    ![A*B,1] ![K,Real.pi] (by intro j; fin_cases j; change 0 ≤ A*B; dsimp [B]; positivity; norm_num)
    (by intro j; fin_cases j; exact hK.trans' zero_le_one; exact Real.pi_pos.le) n x
    (by intro j r hr; fin_cases j; exact hfb r hr; simpa using parity_derivative_bound e r x)
  have hp : ‖iteratedDeriv n (f*g) x‖ ≤ A*B*(K+Real.pi)^n := by
    simpa only [Fin.prod_univ_two,Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,mul_one] using! hprod
  have heq : (shrinkingNewtonTest (fun j => ε j) i e a b hab : ℝ → ℂ)=
      fun y => ((f*g) y : ℂ) := by
    funext y
    rw [shrinkingNewtonTest_apply,halfNewtonFunction,halfNewtonProduct_cosine_product]
    dsimp [f,g]
    simp only [Pi.mul_apply,Complex.ofReal_mul]
    split_ifs <;> ring
  rw [heq,real_cast_iteratedDeriv (f*g) (hfs.mul hgs),Complex.norm_real,Real.norm_eq_abs]
  change ‖iteratedDeriv n (f*g) x‖ ≤ _
  calc
    _ ≤ A*B*(K+Real.pi)^n := hp
    _ ≤ A*B*((1+Real.pi)*K)^n := by
      gcongr
      nlinarith [Real.pi_pos]
    _ = _ := by
      dsimp [B,K]
      rw [mul_pow,div_pow,mul_pow,show 2*n=n*2 by omega,pow_mul]
      ring


/-- Uniform compact derivative bounds through exactly 2p control the original
Hermite norm; the constant is independent of the support radius below one half. -/
theorem exists_hermite_norm_bound_of_compact_derivatives (p : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : SchwartzMap ℝ ℂ) (r A : ℝ), r < 1/2 → 0 ≤ A →
      (∀ x, r ≤ |x| → f x=0) →
      (∀ k ≤ 2*p, ∀ x, ‖iteratedDeriv k f x‖ ≤ A) →
      ‖schwartzToHermiteScale p f‖ ≤ C*A := by
  obtain ⟨C,hC,hbound⟩ := exists_hermite_norm_le_mixedL2Sum p
  let N : ℝ := (mixedIndices (2*p)).card
  let D : ℝ := ‖compactSchwartzCutoff.toLp 2 volume‖
  refine ⟨C*(N+1)*(D+1),by dsimp [N,D]; positivity,fun f r A hr hA hf hder => ?_⟩
  have hm (j k : ℕ) (hjk : j+k ≤ 2*p) :
      ‖(mixedSchwartz j k f).toLp 2 volume‖ ≤ A*D := by
    have hh := schwartz_norm_toLp_le_weighted_sum {()} (fun _ : Unit => A)
      (by intro u hu; exact hA) (mixedSchwartz j k f) (fun _ => compactSchwartzCutoff) ?_
    · simpa only [Finset.sum_singleton] using hh
    · intro x
      simp only [Finset.sum_singleton]
      by_cases hx : |x| ≤ 1
      · rw [compactSchwartzCutoff_eq_one hx,norm_one,mul_one,mixedSchwartz_apply,
          norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs]
        exact (mul_le_mul (pow_le_one₀ (abs_nonneg x) hx) (hder k (by omega) x)
          (norm_nonneg _) (by norm_num)).trans_eq (one_mul A)
      · have hz := compactChart_mixedDerivative_zero f r hr hf k x
          (show 1/2 ≤ |x| by linarith [lt_of_not_ge hx])
        simp only [mixedSchwartz_apply,pow_zero,one_mul] at hz
        rw [mixedSchwartz_apply,hz,mul_zero,norm_zero]
        exact mul_nonneg hA (norm_nonneg _)
  have hsum : mixedL2Sum (2*p) f ≤ N*(A*D) := by
    unfold mixedL2Sum
    calc
      _ ≤ ∑ z ∈ mixedIndices (2*p), A*D := Finset.sum_le_sum (fun z hz =>
        hm z.1 z.2 ((mem_mixedIndices _ _ _).mp hz))
      _ = _ := by simp [N]
  apply (hbound f).trans (mul_le_mul_of_nonneg_left hsum hC.le) |>.trans
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hD : 0 ≤ D := norm_nonneg _
  nlinarith [mul_nonneg hN hD, mul_nonneg hN hA, mul_nonneg hD hA,
    mul_nonneg (mul_nonneg hN hA) hD]


/-- The genuine shrinking Newton test satisfies the original H_p bound with
exactly 2p derivatives and all squared rapid-distance factors. -/
theorem shrinkingNewtonTest_native_bound (p : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε : ℕ → ℝ) (i : ℕ) (e : Bool) (a b δ : ℝ)
      (hab : a < b), b-a ≤ 1 → b ≤ δ → 0 < δ → δ ≤ 1/4 →
      (∀ l < i, δ ≤ ε (l+1) ∧ ε (l+1) ≤ 1/2) →
      ‖schwartzToHermiteScale p (shrinkingNewtonTest (fun j => ε j) i e a b hab)‖ ≤
      C*((i:ℝ)+1)^(2*p)/(b-a)^(2*p)/δ^(4*p)*(32:ℝ)^i*(shrinkingNewtonWeight ε i)^2 := by
  obtain ⟨C,hC,hbound⟩ := exists_hermite_norm_bound_of_compact_derivatives p
  choose E hE hEb using shrinkingNewtonTest_derivative_bound
  let A : ℝ := 1+∑ r ∈ Finset.range (2*p+1), E r
  have hA : 0 < A := by
    have hs := Finset.sum_nonneg (s := Finset.range (2*p+1)) (f := E) (fun r _ => (hE r).le)
    dsimp [A]; linarith
  have hEA (r : ℕ) (hr : r ≤ 2*p) : E r ≤ A := by
    have h := Finset.single_le_sum (s := Finset.range (2*p+1)) (f := E)
      (fun j _ => (hE j).le) (Finset.mem_range.mpr (show r<2*p+1 by omega))
    dsimp [A]; linarith
  refine ⟨C*A,mul_pos hC hA,fun ε i e a b δ hab hgap1 hbδ hδ hδ4 hε => ?_⟩
  let K : ℝ := ((i:ℝ)+1)/((b-a)*δ^2)
  let B : ℝ := (32:ℝ)^i*(shrinkingNewtonWeight ε i)^2
  have hgap : 0 < b-a := sub_pos.mpr hab
  have hK : 1 ≤ K := by
    apply (le_div_iff₀ (by positivity : 0 < (b-a)*δ^2)).mpr
    have hd2 : δ^2 ≤ 1 := pow_le_one₀ hδ.le (by linarith)
    have hg2 : (b-a)*δ^2 ≤ 1 := (mul_le_mul hgap1 hd2 (by positivity) (by norm_num)).trans_eq (one_mul 1)
    nlinarith [Nat.cast_nonneg (α := ℝ) i]
  have hnonneg : 0 ≤ A*B*K^(2*p) := by dsimp [B]; positivity
  have h := hbound (shrinkingNewtonTest (fun j => ε j) i e a b hab) b
    (A*B*K^(2*p)) (by linarith) hnonneg (shrinkingNewtonTest_zero _ _ _ _ _ _) ?_
  · apply h.trans_eq
    dsimp [B,K]
    rw [div_pow,mul_pow,show 4*p=(2*p)*2 by omega,pow_mul]
    ring
  · intro r hr x
    have hh := hEb r ε i e a b δ hab hgap1 hbδ hδ (by linarith) hε x
    have he : E r*((i:ℝ)+1)^r/(b-a)^r/δ^(2*r)*(32:ℝ)^i*(shrinkingNewtonWeight ε i)^2 =
        E r*B*K^r := by
      dsimp [B,K]
      rw [div_pow,mul_pow,show 2*r=r*2 by omega,pow_mul]
      ring
    rw [he] at hh
    apply hh.trans
    exact mul_le_mul (mul_le_mul_of_nonneg_right (hEA r hr) (by dsimp [B]; positivity))
      (pow_le_pow_right₀ hK hr) (by positivity) (by dsimp [B]; positivity)

end
end MeyerGeneralProblem.Adaptive
