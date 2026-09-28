module

public import MeyerGeneralProblem.Cardinal.Adaptive.ShrinkingNewtonMembership

@[expose] public section

/-! Complete analytic gauge series on genuine compact Newton tests. -/
open scoped ContDiff
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open Set MeasureTheory Filter

private theorem cast_real_derivative (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (r : ℕ) :
    iteratedDeriv r (fun x => (f x : ℂ)) = fun x => Complex.ofReal (iteratedDeriv r f x) := by
  induction r with
  | zero => rfl
  | succ r ih =>
      rw [iteratedDeriv_succ,ih,iteratedDeriv_succ]
      funext x
      exact (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x
        (((hf.of_le (show ((r+1:ℕ):ℕ∞ω) ≤ ∞ by simp)).differentiable_iteratedDeriv' r).differentiableAt.hasDerivAt)).deriv

private theorem monomial_derivative_norm (d k : ℕ) (x : ℝ) (hx : |x| ≤ 1) :
    ‖iteratedDeriv k (fun y : ℝ => (y:ℂ)^d) x‖ ≤ ((d:ℝ)+1)^k := by
  have he : (fun y : ℝ => (y:ℂ)^d)=(fun y : ℝ => Complex.ofReal (y^d)) := by
    funext y; simp
  rw [he,cast_real_derivative (fun y => y^d) (by fun_prop)]
  dsimp only
  rw [iteratedDeriv_pow,
    Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_pow,abs_of_nonneg (Nat.cast_nonneg _)]
  have hd : (d.descFactorial k:ℝ) ≤ (d:ℝ)^k := by exact_mod_cast Nat.descFactorial_le_pow d k
  calc
    _ ≤ (d:ℝ)^k*1 := mul_le_mul hd (pow_le_one₀ (abs_nonneg x) hx)
      (by positivity) (by positivity)
    _ ≤ ((d:ℝ)+1)^k := by rw [mul_one]; gcongr; linarith

/-- Multiplying a compact Schwartz test by any monomial costs polynomially
in its degree at each fixed derivative order. -/
theorem compact_monomial_derivative_bound (f : SchwartzMap ℝ ℂ) (r A : ℝ)
    (hr : r < 1/2) (hA : 0 ≤ A) (hf : ∀ x, r ≤ |x| → f x=0)
    (m : ℕ) (hder : ∀ k ≤ m, ∀ x, ‖iteratedDeriv k f x‖ ≤ A)
    (d k : ℕ) (hk : k ≤ m) (x : ℝ) :
    ‖iteratedDeriv k (mixedSchwartz d 0 f) x‖ ≤
      2^m*((d:ℝ)+1)^m*A := by
  have he : (mixedSchwartz d 0 f : ℝ → ℂ)=(fun y : ℝ => (y:ℂ)^d)*(f : ℝ → ℂ) := by
    funext y; simp only [mixedSchwartz_apply,iteratedDeriv_zero,Pi.mul_apply]
  have hpow : ContDiffAt ℝ k (fun y : ℝ => (y:ℂ)^d) x :=
    ((Complex.ofRealCLM.contDiff : ContDiff ℝ k Complex.ofRealCLM).pow d).contDiffAt
  by_cases hx : |x| ≤ 1
  · rw [he,iteratedDeriv_mul hpow
      (f.smooth k).contDiffAt]
    have hsum := norm_sum_le (Finset.range (k+1))
      (fun l => (k.choose l:ℂ)*iteratedDeriv l (fun y : ℝ => (y:ℂ)^d) x*iteratedDeriv (k-l) f x)
    apply hsum.trans
    calc
      _ ≤ ∑ l ∈ Finset.range (k+1), (k.choose l:ℝ)*((d:ℝ)+1)^k*A := by
        apply Finset.sum_le_sum
        intro l hl
        have hlk : l ≤ k := by have := Finset.mem_range.mp hl; omega
        simp only [norm_mul,Complex.norm_natCast]
        exact mul_le_mul (mul_le_mul_of_nonneg_left
          ((monomial_derivative_norm d l x hx).trans
            (pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) d] : (1:ℝ) ≤ (d:ℝ)+1) hlk)) (by positivity))
          (hder (k-l) (by omega) x) (norm_nonneg _) (by positivity)
      _ = (2:ℝ)^k*((d:ℝ)+1)^k*A := by
        rw [← Finset.sum_mul,← Finset.sum_mul]
        have h : (∑ l ∈ Finset.range (k+1), (k.choose l:ℝ))=2^k := by
          exact_mod_cast Nat.sum_range_choose k
        rw [h]
      _ ≤ _ := by gcongr <;> first | assumption | norm_num
  · have hz : (mixedSchwartz d 0 f : ℝ → ℂ) =ᶠ[nhds x] (fun _ => 0) := by
      have hrx : r < |x| := by linarith [lt_of_not_ge hx]
      filter_upwards [(continuous_abs.tendsto x).eventually (eventually_gt_nhds hrx)] with y hy
      rw [mixedSchwartz_apply,iteratedDeriv_zero,hf y hy.le,mul_zero]
    rw [hz.iteratedDeriv_eq k,iteratedDeriv_const]
    split_ifs <;> simp only [norm_zero] <;> positivity

/-- The entire Taylor coefficient of the literal source gauge exp(-2 pi i x y). -/
def halfNewtonGaugeCoefficient (r : ℕ) : ℂ := (-2*Real.pi*Complex.I)^r/(r.factorial:ℂ)

/-- Every fixed polynomial factor is harmless against the full factorial series. -/
theorem summable_polynomial_factorial (m : ℕ) (K : ℝ) (hK : 0 ≤ K) :
    Summable (fun r : ℕ => ((r:ℝ)+1)^m*K^r/(r.factorial:ℝ)) := by
  have hp (r : ℕ) : (r:ℝ)+1 ≤ (2:ℝ)^r := by
    induction r with
    | zero => norm_num
    | succ r ih =>
      rw [Nat.cast_add,Nat.cast_one,pow_succ]
      nlinarith [Nat.cast_nonneg (α := ℝ) r]
  apply Summable.of_nonneg_of_le (fun _ => by positivity) _
    (Real.summable_pow_div_factorial ((2:ℝ)^m*K))
  intro r
  rw [mul_pow]
  apply div_le_div_of_nonneg_right _ (by positivity)
  rw [← pow_mul, Nat.mul_comm m r, pow_mul]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (hp r) m) (by positivity)


private theorem compact_derivativeL2Sum_le (m : ℕ) (f : SchwartzMap ℝ ℂ) (r A : ℝ)
    (hr : r < 1/2) (hA : 0 ≤ A) (hf : ∀ x, r ≤ |x| → f x=0)
    (hder : ∀ k ≤ m, ∀ x, ‖iteratedDeriv k f x‖ ≤ A) :
    compactDerivativeL2Sum m f ≤ (m+1:ℕ)*A*‖compactSchwartzCutoff.toLp 2 volume‖ := by
  have hb (k : ℕ) (hk : k ≤ m) : ‖(mixedSchwartz 0 k f).toLp 2 volume‖ ≤
      A*‖compactSchwartzCutoff.toLp 2 volume‖ := by
    have h := schwartz_norm_toLp_le_weighted_sum {()} (fun _ : Unit => A)
      (by intro u hu; exact hA) (mixedSchwartz 0 k f) (fun _ => compactSchwartzCutoff) ?_
    · simpa only [Finset.sum_singleton] using h
    · intro x
      simp only [Finset.sum_singleton]
      by_cases hx : |x| ≤ 1
      · rw [compactSchwartzCutoff_eq_one hx,norm_one,mul_one,mixedSchwartz_apply,pow_zero,one_mul]
        exact hder k hk x
      · rw [compactChart_mixedDerivative_zero f r hr hf k x
          (show 1/2 ≤ |x| by linarith [lt_of_not_ge hx]),norm_zero]
        exact mul_nonneg hA (norm_nonneg _)
  calc
    _ ≤ ∑ k ∈ Finset.range (m+1), A*‖compactSchwartzCutoff.toLp 2 volume‖ := by
      apply Finset.sum_le_sum
      intro k hk
      exact hb k (by have := Finset.mem_range.mp hk; omega)
    _ = _ := by simp [mul_assoc]

/-- Compact monomial insertion has polynomial degree m in the complete derivative
L2 sum through m; no extra derivatives of the original compact test are used. -/
theorem exists_compact_monomial_derivativeL2Sum_bound (m : ℕ) (f : SchwartzMap ℝ ℂ)
    (r : ℝ) (hr : r < 1/2) (hf : ∀ x, r ≤ |x| → f x=0) :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ,
      compactDerivativeL2Sum m (mixedSchwartz d 0 f) ≤ C*((d:ℝ)+1)^m := by
  let A : ℝ := 1+∑ k ∈ Finset.range (m+1), SchwartzMap.seminorm ℂ 0 k f
  have hA : 0 < A := by
    have h := Finset.sum_nonneg (s := Finset.range (m+1))
      (f := fun k => SchwartzMap.seminorm ℂ 0 k f) (fun k _ => apply_nonneg _ _)
    dsimp [A]; linarith
  have hder (k : ℕ) (hk : k ≤ m) (x : ℝ) : ‖iteratedDeriv k f x‖ ≤ A := by
    have h := f.le_seminorm' ℂ 0 k x
    simp only [pow_zero,one_mul] at h
    have hs := Finset.single_le_sum (s := Finset.range (m+1)) (a := k)
      (f := fun k => SchwartzMap.seminorm ℂ 0 k f) (fun _ _ => apply_nonneg _ _)
      (Finset.mem_range.mpr (by omega))
    dsimp [A]; linarith
  let D : ℝ := ‖compactSchwartzCutoff.toLp 2 volume‖
  refine ⟨(m+1:ℕ)*2^m*A*(D+1),by dsimp [D]; positivity,fun d => ?_⟩
  have hg : ∀ x, r ≤ |x| → mixedSchwartz d 0 f x=0 := by
    intro x hx; rw [mixedSchwartz_apply,iteratedDeriv_zero,hf x hx,mul_zero]
  have hh := compact_derivativeL2Sum_le m (mixedSchwartz d 0 f) r
    (2^m*((d:ℝ)+1)^m*A) hr (by positivity) hg
    (fun k hk x => compact_monomial_derivative_bound f r A hr hA.le hf m hder d k hk x)
  apply hh.trans
  change (m+1:ℕ)*(2^m*((d:ℝ)+1)^m*A)*D ≤ _
  calc
    _ ≤ (m+1:ℕ)*(2^m*((d:ℝ)+1)^m*A)*(D+1) := by gcongr; linarith
    _ = _ := by ring

/-- Actual positive-native Taylor test vector, retaining the complete Zak transpose. -/
def halfNewtonGaugeTestTerm (p : ℕ) (f g : SchwartzMap ℝ ℂ) (d : ℕ) : HermiteScale (p:ℤ) :=
  halfNewtonGaugeCoefficient d • schwartzToHermiteScale p
    (zakSchwartzTranspose (mixedSchwartz d 0 g) (mixedSchwartz d 0 f))

/-- The complete analytic gauge Taylor series is absolutely summable in the
original positive native space, at precisely the original order p. -/
theorem halfNewtonGaugeTestTerm_norm_summable (p : ℕ) (f g : SchwartzMap ℝ ℂ)
    (r : ℝ) (hr : r < 1/2) (hf : ∀ x, r ≤ |x| → f x=0) (hg : ∀ x, r ≤ |x| → g x=0) :
    Summable (fun d : ℕ => ‖halfNewtonGaugeTestTerm p f g d‖) := by
  obtain ⟨C,hC,hbound⟩ := exists_zakSchwartzTranspose_native_bound p
  obtain ⟨A,hA,hfbound⟩ := exists_compact_monomial_derivativeL2Sum_bound (2*p) f r hr hf
  obtain ⟨B,hB,hgbound⟩ := exists_compact_monomial_derivativeL2Sum_bound (2*p) g r hr hg
  let K : ℝ := ‖(-2*Real.pi*Complex.I : ℂ)‖
  have hs := (summable_polynomial_factorial (4*p) K (norm_nonneg _)).mul_left (C*A*B)
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hs
  intro d
  have hsupport (u : SchwartzMap ℝ ℂ) (hu : ∀ x, r ≤ |x| → u x=0) :
      ∀ x, r ≤ |x| → mixedSchwartz d 0 u x=0 := by
    intro x hx; rw [mixedSchwartz_apply,iteratedDeriv_zero,hu x hx,mul_zero]
  have hb := hbound (mixedSchwartz d 0 f) (mixedSchwartz d 0 g) r hr (hsupport f hf) (hsupport g hg)
  have hfa : 0 ≤ compactDerivativeL2Sum (2*p) (mixedSchwartz d 0 f) :=
    Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hgb : 0 ≤ compactDerivativeL2Sum (2*p) (mixedSchwartz d 0 g) :=
    Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hh : ‖schwartzToHermiteScale p (zakSchwartzTranspose (mixedSchwartz d 0 g) (mixedSchwartz d 0 f))‖ ≤
      C*A*B*((d:ℝ)+1)^(4*p) := by
    apply hb.trans
    calc
      _ ≤ C*(A*((d:ℝ)+1)^(2*p))*(B*((d:ℝ)+1)^(2*p)) := by
        gcongr
        · exact hfbound d
        · exact hgbound d
      _ = _ := by rw [show 4*p=2*p+2*p by omega,pow_add]; ring
  rw [halfNewtonGaugeTestTerm,norm_smul,halfNewtonGaugeCoefficient,norm_div,norm_pow,Complex.norm_natCast]
  calc
    _ ≤ (K^d/(d.factorial:ℝ))*(C*A*B*((d:ℝ)+1)^(4*p)) :=
      mul_le_mul_of_nonneg_left hh (by dsimp [K]; positivity)
    _ = _ := by ring

/-- The full native Taylor vector sum exists by absolute convergence in the
original Hilbert space; later kernel identification may use this actual HasSum. -/
theorem halfNewtonGaugeTestTerm_hasSum (p : ℕ) (f g : SchwartzMap ℝ ℂ)
    (r : ℝ) (hr : r < 1/2) (hf : ∀ x, r ≤ |x| → f x=0) (hg : ∀ x, r ≤ |x| → g x=0) :
    HasSum (halfNewtonGaugeTestTerm p f g) (∑' d, halfNewtonGaugeTestTerm p f g d) :=
  (halfNewtonGaugeTestTerm_norm_summable p f g r hr hf hg).of_norm.hasSum


private theorem monomial_modulation (d : ℕ) (a : ℝ) (f : SchwartzMap ℝ ℂ) :
    mixedSchwartz d 0 (combSchwartzModulation a f)=combSchwartzModulation a (mixedSchwartz d 0 f) := by
  ext x
  simp only [mixedSchwartz_apply,iteratedDeriv_zero,combSchwartzModulation_apply]
  ring

/-- Complete Taylor action of the actual analytic gauge on the characteristic-adjusted source. -/
def halfNewtonGaugeBilinear (T : TemperedDistribution ℝ ℂ) (f g : SchwartzMap ℝ ℂ) : ℂ :=
  ∑' d : ℕ, halfNewtonGaugeCoefficient d * halfNewtonBilinear T (mixedSchwartz d 0 f) (mixedSchwartz d 0 g)

/-- The scalar gauge action is an absolutely convergent series of actual whole
source readings for every compact test pair and original native source. -/
theorem halfNewtonGaugeBilinear_norm_summable (p : ℕ) (T : HermiteScale (-(p:ℤ)))
    (f g : SchwartzMap ℝ ℂ) (r : ℝ) (hr : r < 1/2)
    (hf : ∀ x, r ≤ |x| → f x=0) (hg : ∀ x, r ≤ |x| → g x=0) :
    Summable (fun d : ℕ => ‖halfNewtonGaugeCoefficient d *
      halfNewtonBilinear (hermiteScaleDistribution p T) (mixedSchwartz d 0 f) (mixedSchwartz d 0 g)‖) := by
  let ff := combSchwartzModulation (1/2) f
  let gg := combSchwartzModulation (-1/2) g
  have hs (a : ℝ) (u : SchwartzMap ℝ ℂ) (hu : ∀ x, r ≤ |x| → u x=0) :
      ∀ x, r ≤ |x| → combSchwartzModulation a u x=0 := by
    intro x hx; rw [combSchwartzModulation_apply,hu x hx,mul_zero]
  have h := (halfNewtonGaugeTestTerm_norm_summable p ff gg r hr (hs _ _ hf) (hs _ _ hg)).mul_left ‖T‖
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ h
  intro d
  have he : halfNewtonBilinear (hermiteScaleDistribution p T) (mixedSchwartz d 0 f) (mixedSchwartz d 0 g)=
      hermiteScalePairing (p:ℤ) T (schwartzToHermiteScale p
        (zakSchwartzTranspose (mixedSchwartz d 0 gg) (mixedSchwartz d 0 ff))) := by
    unfold halfNewtonBilinear
    rw [← monomial_modulation,← monomial_modulation,← zakSchwartzTranspose_realizes,
      hermiteScaleDistribution_apply]
  rw [norm_mul,he,halfNewtonGaugeTestTerm,norm_smul]
  have hb := mul_le_mul_of_nonneg_left
    (norm_hermiteScalePairing_le (p:ℤ) T
      (schwartzToHermiteScale p (zakSchwartzTranspose (mixedSchwartz d 0 gg) (mixedSchwartz d 0 ff))))
    (norm_nonneg (halfNewtonGaugeCoefficient d))
  simpa only [mul_assoc,mul_left_comm,mul_comm] using hb

/-- The complete scalar Taylor action has its actual declared sum. -/
theorem halfNewtonGaugeBilinear_hasSum (p : ℕ) (T : HermiteScale (-(p:ℤ)))
    (f g : SchwartzMap ℝ ℂ) (r : ℝ) (hr : r < 1/2)
    (hf : ∀ x, r ≤ |x| → f x=0) (hg : ∀ x, r ≤ |x| → g x=0) :
    HasSum (fun d : ℕ => halfNewtonGaugeCoefficient d *
      halfNewtonBilinear (hermiteScaleDistribution p T) (mixedSchwartz d 0 f) (mixedSchwartz d 0 g))
      (halfNewtonGaugeBilinear (hermiteScaleDistribution p T) f g) :=
  (halfNewtonGaugeBilinear_norm_summable p T f g r hr hf hg).of_norm.hasSum

end
end MeyerGeneralProblem.Adaptive
