module

public import MeyerGeneralProblem.Cardinal.Adaptive.FixedNewtonBounds
public import MeyerGeneralProblem.Cardinal.Adaptive.ScalarArcsineSeries
public import MeyerGeneralProblem.Cardinal.Adaptive.NativeSchwartzSeries

@[expose] public section

/-! # Strong original-native sine series on the actual small chart -/
open scoped ContDiff
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open scoped Topology

/-- The literal periodic sine powers are genuine temperate multipliers. -/
theorem sinePower_hasTemperateGrowth (d : ℕ) :
    (fun x : ℝ => (Real.sin (2*Real.pi*x):ℂ)^d).HasTemperateGrowth := by
  refine smooth_periodic_hasTemperateGrowth (fun x : ℝ => (Real.sin (2*Real.pi*x):ℂ)^d) ?_ ?_
  · have hs : ContDiff ℝ ∞ (fun x : ℝ => Real.sin (2*Real.pi*x)) := by fun_prop
    exact (Complex.ofRealCLM.contDiff.comp hs).pow d
  · intro x
    dsimp only
    rw [show 2*Real.pi*(x+1)=2*Real.pi*x+2*Real.pi by ring,Real.sin_add_two_pi]

/-- Actual multiplication of a Schwartz test by an arbitrary sine power. -/
def compactSinePower (d : ℕ) (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => (Real.sin (2*Real.pi*x):ℂ)^d) f

/-- The multiplier is the literal sine power at every real point. -/
theorem compactSinePower_apply (d : ℕ) (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    compactSinePower d f x=(Real.sin (2*Real.pi*x):ℂ)^d*f x := by
  exact SchwartzMap.smulLeftCLM_apply_apply (sinePower_hasTemperateGrowth d) f x

private theorem sine_derivative_bound (b x : ℝ) (hb : 0 < b) (hb' : b ≤ 1/8)
    (hx : |x| ≤ b) (n : ℕ) :
    ‖iteratedDeriv n (fun y => Real.sin (2*Real.pi*y)) x‖ ≤ (8*b)*(2*Real.pi/(8*b))^n := by
  by_cases hn : n=0
  · subst n
    simp only [iteratedDeriv_zero,pow_zero,mul_one,Real.norm_eq_abs]
    apply (Real.abs_sin_le_abs).trans
    rw [abs_mul,abs_of_pos (by positivity : 0 < 2*Real.pi)]
    nlinarith [Real.pi_lt_four,Real.pi_pos]
  · have hp : (8*b)^n ≤ 8*b := by
      simpa only [pow_one] using pow_le_pow_of_le_one (by positivity : 0 ≤ 8*b)
        (by linarith : 8*b ≤ 1) (Nat.pos_of_ne_zero hn)
    have he := congrFun (iteratedDeriv_comp_const_mul (n:=n)
      (Real.contDiff_sin : ContDiff ℝ n Real.sin) (2*Real.pi)) x
    rw [he,norm_mul,norm_pow,Real.norm_eq_abs,abs_of_pos (by positivity : 0 < 2*Real.pi)]
    apply ((mul_le_mul_of_nonneg_left (Real.abs_iteratedDeriv_sin_le_one n _) (by positivity)).trans_eq (mul_one _)).trans
    rw [div_pow,←mul_div_assoc]
    apply (le_div_iff₀ (by positivity : 0 < (8*b)^n)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hp (pow_nonneg (by positivity : 0 ≤ 2*Real.pi) n)]

private theorem real_cast_iteratedDeriv (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (r : ℕ) :
    iteratedDeriv r (fun x => (f x : ℂ)) = fun x => Complex.ofReal (iteratedDeriv r f x) := by
  induction r with
  | zero => rfl
  | succ r ih =>
      rw [iteratedDeriv_succ,ih,iteratedDeriv_succ]
      funext x
      exact (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x
        (((hf.of_le (show ((r+1:ℕ):ℕ∞ω) ≤ ∞ by simp)).differentiable_iteratedDeriv' r).differentiableAt.hasDerivAt)).deriv

/-- Every derivative of a literal sine power retains exponential smallness
on the small chart, uniformly in its power. -/
theorem sinePower_derivative_bound (b x : ℝ) (hb : 0 < b) (hb' : b ≤ 1/8)
    (hx : |x| ≤ b) (d n : ℕ) :
    ‖iteratedDeriv n (fun y : ℝ => (Real.sin (2*Real.pi*y):ℂ)^d) x‖ ≤
      (8*b)^d*((d:ℝ)*(2*Real.pi/(8*b)))^n := by
  have h := iteratedDeriv_product_geometric_bound d (fun _ y => Real.sin (2*Real.pi*y))
    (by intro j; fun_prop) (fun _ => 8*b) (fun _ => 2*Real.pi/(8*b))
    (by intro j; positivity) (by intro j; positivity) n x
    (fun _ r _ => sine_derivative_bound b x hb hb' hx r)
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,Finset.sum_const,nsmul_eq_mul] at h
  have he : (fun y : ℝ => (Real.sin (2*Real.pi*y):ℂ)^d)=
      (fun y : ℝ => ((Real.sin (2*Real.pi*y)^d:ℝ):ℂ)) := by funext y; simp
  rw [he,real_cast_iteratedDeriv _ (by fun_prop),Complex.norm_real,Real.norm_eq_abs]
  exact h

/-- A fixed compact test multiplied by arbitrary sine powers has geometric
smallness in every fixed derivative order, with only polynomial power loss. -/
theorem compactSinePower_derivative_bound (f : SchwartzMap ℝ ℂ) (b : ℝ)
    (hb : 0 < b) (hb' : b ≤ 1/8) (hf : ∀ x, b ≤ |x| → f x=0) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ d n : ℕ, n ≤ m → ∀ x : ℝ,
      ‖iteratedDeriv n (compactSinePower d f) x‖ ≤ C*(8*b)^d*((d:ℝ)+1)^m := by
  let A : ℝ := 1+∑ n ∈ Finset.range (m+1), SchwartzMap.seminorm ℂ 0 n f
  let B : ℝ := 2*Real.pi/(8*b)
  have hA : 0 < A := by
    have hh : 0 ≤ ∑ n ∈ Finset.range (m+1), SchwartzMap.seminorm ℂ 0 n f :=
      Finset.sum_nonneg (fun n _ => apply_nonneg (SchwartzMap.seminorm ℂ 0 n) f)
    dsimp only [A]; linarith
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hfd (n : ℕ) (hn : n ≤ m) (x : ℝ) : ‖iteratedDeriv n f x‖ ≤ A := by
    have hh := SchwartzMap.le_seminorm' ℂ 0 n f x
    simp only [pow_zero,one_mul] at hh
    apply hh.trans
    have h1 := Finset.single_le_sum (s := Finset.range (m+1)) (a := n)
      (f := fun r => SchwartzMap.seminorm ℂ 0 r f)
      (by intro r hr; exact apply_nonneg (SchwartzMap.seminorm ℂ 0 r) f)
      (Finset.mem_range.mpr (show n<m+1 by omega))
    dsimp only [A]; linarith
  refine ⟨A*(1+B)^m,by positivity,fun d n hn x => ?_⟩
  by_cases hx : |x| ≤ b
  · have he : (compactSinePower d f : ℝ → ℂ)=
        (f : ℝ → ℂ)*(fun y => (Real.sin (2*Real.pi*y):ℂ)^d) := by
      funext y
      rw [compactSinePower_apply]
      exact mul_comm _ _
    rw [he,iteratedDeriv_mul (f.smooth n).contDiffAt
      ((sinePower_hasTemperateGrowth d).1.of_le (by simp)).contDiffAt]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ l ∈ Finset.range (n+1), (n.choose l:ℝ)*A*((8*b)^d*((d:ℝ)*B)^(n-l)) := by
        apply Finset.sum_le_sum
        intro l hl
        simp only [norm_mul,Complex.norm_natCast]
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hfd l (by have := Finset.mem_range.mp hl; omega) x)
          (by positivity)) (sinePower_derivative_bound b x hb hb' hx d (n-l))
          (norm_nonneg _) (by positivity)
      _ = A*(8*b)^d*(1+(d:ℝ)*B)^n := by
        rw [add_pow,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l hl
        rw [one_pow]
        ring
      _ ≤ A*(8*b)^d*((1+B)*((d:ℝ)+1))^m := by
        gcongr
        exact pow_le_pow_left₀ (by positivity) (by nlinarith [Nat.cast_nonneg (α:=ℝ) d]) n |>.trans
          (pow_le_pow_right₀ (by nlinarith [Nat.cast_nonneg (α:=ℝ) d]) hn)
      _ = _ := by rw [mul_pow (1+B)]; ring
  · have hx' : b < |x| := lt_of_not_ge hx
    have hz : (compactSinePower d f : ℝ → ℂ)=ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [(isOpen_lt continuous_const continuous_abs).mem_nhds hx'] with y hy
      rw [compactSinePower_apply,hf y hy.le,mul_zero]
    rw [hz.iteratedDeriv_eq n]
    simp only [iteratedDeriv_const]
    split_ifs <;> simp only [norm_zero] <;> positivity

/-- Sine powers of a fixed compact test have a summable geometric envelope
in the original H_p norm, with exactly the original 2p derivative cost. -/
theorem compactSinePower_native_bound (f : SchwartzMap ℝ ℂ) (b : ℝ)
    (hb : 0 < b) (hb' : b ≤ 1/8) (hf : ∀ x, b ≤ |x| → f x=0) (p : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ,
      ‖schwartzToHermiteScale p (compactSinePower d f)‖ ≤ C*(8*b)^d*((d:ℝ)+1)^(2*p) := by
  obtain ⟨C,hC,hbound⟩ := exists_hermite_norm_bound_of_compact_derivatives p
  obtain ⟨D,hD,hd⟩ := compactSinePower_derivative_bound f b hb hb' hf (2*p)
  refine ⟨C*D,by positivity,fun d => ?_⟩
  have hh := hbound (compactSinePower d f) b (D*(8*b)^d*((d:ℝ)+1)^(2*p))
    (by linarith) (by positivity)
    (by intro x hx; rw [compactSinePower_apply,hf x hx,mul_zero]) (hd d)
  simpa only [mul_assoc] using hh

private theorem summable_shifted_polynomial_geometric (q : ℝ) (hq : 0 < q) (hq1 : q < 1) (m : ℕ) :
    Summable (fun n : ℕ => q^n*((n:ℝ)+1)^m) := by
  have h := (summable_nat_add_iff 1).mpr
    (summable_pow_mul_geometric_of_norm_lt_one m (r := q) (by simpa only [Real.norm_eq_abs,abs_of_pos hq] using hq1))
  have hh := h.mul_right q⁻¹
  have he : (fun n : ℕ => ((n+1:ℕ):ℝ)^m*q^(n+1)*q⁻¹)=(fun n : ℕ => q^n*((n:ℝ)+1)^m) := by
    funext n
    push_cast
    rw [pow_succ]
    field_simp
  rwa [he] at hh

/-- The full literal odd arcsine series of Schwartz tests, with the physical
coordinate normalization kept inside each actual term. -/
def compactArcsineTerm (n : ℕ) (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  ((2*Real.pi:ℂ)⁻¹*(scalarArcsineCoefficient n:ℂ)) •compactSinePower (2*n+1) f

/-- The complete scalar coordinate series is absolutely summable in every
original positive Hermite norm on a strict small chart. -/
theorem compactArcsineTerm_native_norm_summable (f : SchwartzMap ℝ ℂ) (b : ℝ)
    (hb : 0 < b) (hb' : b < 1/8) (hf : ∀ x, b ≤ |x| → f x=0) (p : ℕ) :
    Summable (fun n => ‖schwartzToHermiteScale p (compactArcsineTerm n f)‖) := by
  obtain ⟨C,hC,hbound⟩ := compactSinePower_native_bound f b hb hb'.le hf p
  let σ : ℝ := 8*b
  have hσ : 0 < σ := by dsimp [σ]; positivity
  have hσ1 : σ < 1 := by dsimp [σ]; linarith
  have hs := (summable_shifted_polynomial_geometric (σ^2) (by positivity)
    (by nlinarith) (2*p)).mul_left (‖(2*Real.pi:ℂ)⁻¹‖*C*σ*2^(2*p))
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) _ hs
  intro n
  simp only [compactArcsineTerm,map_smul,norm_smul,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (scalarArcsineCoefficient_nonneg n)]
  calc
    _ ≤ (‖(2*Real.pi:ℂ)⁻¹‖*1)*(C*σ^(2*n+1)*((2*n+1:ℕ)+1:ℝ)^(2*p)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (scalarArcsineCoefficient_le_one n) (norm_nonneg _))
        (hbound (2*n+1)) (norm_nonneg _) (by positivity)
    _ = _ := by
      push_cast
      rw [show (2*(n:ℝ)+1)+1=2*((n:ℝ)+1) by ring,mul_pow (2:ℝ),pow_succ _ (2*n)]
      simp only [pow_mul]
      dsimp only [σ]
      ring

/-- The full pointwise arcsine sum of genuine compact tests is literal
multiplication by the physical coordinate. -/
theorem compactArcsineTerm_pointwise (f : SchwartzMap ℝ ℂ) (b : ℝ)
    (hb' : b < 1/8) (hf : ∀ x, b ≤ |x| → f x=0) (x : ℝ) :
    mixedSchwartz 1 0 f x=∑' n, compactArcsineTerm n f x := by
  by_cases hx : b ≤ |x|
  · simp [compactArcsineTerm,compactSinePower_apply,hf x hx,mixedSchwartz_apply,iteratedDeriv_zero]
  · have hxb : |x| < b := lt_of_not_ge hx
    have hxq : |x| < 1/4 := by linarith
    simp only [compactArcsineTerm,_root_.smul_apply,smul_eq_mul,compactSinePower_apply,
      mixedSchwartz_apply,iteratedDeriv_zero,pow_one]
    have he : (fun n : ℕ => ((2*Real.pi:ℂ)⁻¹*(scalarArcsineCoefficient n:ℂ))*
        ((Real.sin (2*Real.pi*x):ℂ)^(2*n+1)*f x))=
        (fun n => ((2*Real.pi:ℂ)⁻¹*(Real.sin (2*Real.pi*x):ℂ))*
          ((scalarArcsineCoefficient n:ℂ)*((Real.sin (2*Real.pi*x):ℂ)^2)^n)*f x) := by
      funext n
      rw [pow_succ _ (2*n),pow_mul]
      ring
    rw [he,tsum_mul_right,tsum_mul_left,scalarArcsineFactor_sin_coordinate x hxq]

/-- The literal physical coordinate is the strong sum of the full scalar
arcsine series in every original H_p, so all native source jets are covered. -/
theorem compactArcsineTerm_native_hasSum (f : SchwartzMap ℝ ℂ) (b : ℝ)
    (hb : 0 < b) (hb' : b < 1/8) (hf : ∀ x, b ≤ |x| → f x=0) (p : ℕ) :
    HasSum (fun n => schwartzToHermiteScale p (compactArcsineTerm n f))
      (schwartzToHermiteScale p (mixedSchwartz 1 0 f)) :=
  hasSum_native_schwartz_of_pointwise p _ _
    (compactArcsineTerm_native_norm_summable f b hb hb' hf p)
    (compactArcsineTerm_pointwise f b hb' hf)

/-- Every actual tempered distribution pairs with the complete coordinate
series term by term; the required native order is derived from the distribution. -/
theorem compactArcsineTerm_distribution_hasSum (f : SchwartzMap ℝ ℂ) (b : ℝ)
    (hb : 0 < b) (hb' : b < 1/8) (hf : ∀ x, b ≤ |x| → f x=0)
    (T : TemperedDistribution ℝ ℂ) :
    HasSum (fun n => T (compactArcsineTerm n f)) (T (mixedSchwartz 1 0 f)) := by
  obtain ⟨p,u,hu⟩ := exists_hermiteScale_representation T
  have hh := (hermiteScalePairingLeftCLM p u).hasSum (compactArcsineTerm_native_hasSum f b hb hb' hf p)
  simpa only [hermiteScalePairingLeftCLM_apply,←hermiteScaleDistribution_apply,hu] using hh

/-- Actual physical Zak slices permit the entire coordinate series in the
first test variable, including every original source jet. -/
theorem halfNewtonBilinear_arcsine_left_hasSum (T : TemperedDistribution ℝ ℂ)
    (f g : SchwartzMap ℝ ℂ) (b : ℝ) (hb : 0 < b) (hb' : b < 1/8)
    (hf : ∀ x, b ≤ |x| → f x=0) :
    HasSum (fun n => ((2*Real.pi:ℂ)⁻¹*(scalarArcsineCoefficient n:ℂ))*
      halfNewtonBilinear T (compactSinePower (2*n+1) f) g)
      (halfNewtonBilinear T (mixedSchwartz 1 0 f) g) := by
  have hh := compactArcsineTerm_distribution_hasSum f b hb hb' hf
    ((zakPhysicalSlice T (combSchwartzModulation (-1/2) g)).comp (combSchwartzModulation (1/2)))
  change HasSum (fun n => halfNewtonBilinear T (compactArcsineTerm n f) g)
    (halfNewtonBilinear T (mixedSchwartz 1 0 f) g) at hh
  simpa only [zakPhysicalSlice_apply,compactArcsineTerm,map_smul,
    zakTensorAction_smul_left,smul_eq_mul,halfNewtonBilinear] using hh

/-- Actual frequency Zak slices permit the entire coordinate series in the
second test variable with the same original characteristic conventions. -/
theorem halfNewtonBilinear_arcsine_right_hasSum (T : TemperedDistribution ℝ ℂ)
    (f g : SchwartzMap ℝ ℂ) (b : ℝ) (hb : 0 < b) (hb' : b < 1/8)
    (hg : ∀ x, b ≤ |x| → g x=0) :
    HasSum (fun n => ((2*Real.pi:ℂ)⁻¹*(scalarArcsineCoefficient n:ℂ))*
      halfNewtonBilinear T f (compactSinePower (2*n+1) g))
      (halfNewtonBilinear T f (mixedSchwartz 1 0 g)) := by
  have hh := compactArcsineTerm_distribution_hasSum g b hb hb' hg
    ((zakTensorSlice T (combSchwartzModulation (1/2) f)).comp (combSchwartzModulation (-1/2)))
  change HasSum (fun n => zakTensorSlice T (combSchwartzModulation (1/2) f)
      (combSchwartzModulation (-1/2) (compactArcsineTerm n g)))
    (zakTensorSlice T (combSchwartzModulation (1/2) f)
      (combSchwartzModulation (-1/2) (mixedSchwartz 1 0 g))) at hh
  simpa only [zakTensorSlice_apply,compactArcsineTerm,map_smul,
    zakTensorAction_smul_right,smul_eq_mul,halfNewtonBilinear] using hh

end
end MeyerGeneralProblem.Adaptive
