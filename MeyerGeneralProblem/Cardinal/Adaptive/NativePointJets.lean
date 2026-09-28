module

public import MeyerGeneralProblem.Distribution.SchwartzDividedDifferenceBounds
public import MeyerGeneralProblem.Cardinal.Adaptive.NativeDualMultipliers
public import MeyerGeneralProblem.Cardinal.Adaptive.ShrinkingBumpBounds
public import MeyerGeneralProblem.Cardinal.Adaptive.JetTailBudget

@[expose] public section

/-! Actual point-jet classification in the original native scale. -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff

private theorem complex_linear_factor_hasDerivAt (a x : ℝ) :
    HasDerivAt (fun y : ℝ => ((y-a:ℝ):ℂ)) 1 x := by
  simpa only [Function.comp_def, id_eq, Complex.ofRealCLM_apply, Complex.ofReal_one] using!
    (Complex.ofRealCLM.hasFDerivAt (x := x-a)).comp_hasDerivAt x ((hasDerivAt_id x).sub_const a)

theorem complex_linear_factor_smooth (a : ℝ) :
    ContDiff ℝ ∞ (fun y : ℝ => ((y-a:ℝ):ℂ)) :=
  Complex.ofRealCLM.contDiff.comp (contDiff_id.sub contDiff_const)

/-- The actual compact Schwartz quotient by one vanished linear factor. -/
def pointDivision (f : SchwartzMap ℝ ℂ) (hf : HasCompactSupport (f : ℝ → ℂ))
    (a : ℝ) (ha : f a = 0) : SchwartzMap ℝ ℂ :=
  compactSchwartzDivision f hf (fun y : ℝ => ((y-a:ℝ):ℂ)) (complex_linear_factor_smooth a)
    (fun y hy => by rw [(complex_linear_factor_hasDerivAt a y).deriv]; exact one_ne_zero)
    (fun y hy => by have he : y=a := sub_eq_zero.mp (Complex.ofReal_eq_zero.mp hy); simpa [he] using ha)

/-- The constructed removable quotient retains compact support. -/
theorem pointDivision_hasCompactSupport (f : SchwartzMap ℝ ℂ) (hf : HasCompactSupport (f : ℝ → ℂ))
    (a : ℝ) (ha : f a = 0) : HasCompactSupport (pointDivision f hf a ha : ℝ → ℂ) :=
  compactSchwartzDivision_hasCompactSupport _ _ _ _ _ _

/-- Exact multiplication by the vanished linear factor recovers the whole test. -/
theorem pointDivision_mul (f : SchwartzMap ℝ ℂ) (hf : HasCompactSupport (f : ℝ → ℂ))
    (a : ℝ) (ha : f a = 0) (x : ℝ) :
    ((x-a:ℝ):ℂ) * pointDivision f hf a ha x = f x := by
  change ((x-a:ℝ):ℂ) * removableQuotient f (fun y : ℝ => ((y-a:ℝ):ℂ)) x = f x
  exact mul_removableQuotient (ψ := (f : ℝ → ℂ)) (f := fun y : ℝ => ((y-a:ℝ):ℂ))
    (fun y hy => by
      have he : y=a := sub_eq_zero.mp (Complex.ofReal_eq_zero.mp hy)
      simpa [he] using ha) x

private theorem pointDivision_eq_dividedDifference (f : SchwartzMap ℝ ℂ)
    (hf : HasCompactSupport (f : ℝ → ℂ)) (a : ℝ) (ha : f a = 0) :
    (pointDivision f hf a ha : ℝ → ℂ) = smoothDividedDifference f a := by
  funext x
  by_cases hx : x=a
  · subst x
    simp only [pointDivision, compactSchwartzDivision_apply, removableQuotient,
      sub_self, Complex.ofReal_zero, ite_true, smoothDividedDifference_self,
      (complex_linear_factor_hasDerivAt a a).deriv, div_one]
  · apply mul_left_cancel₀ (show ((x-a:ℝ):ℂ) ≠ 0 from Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr hx))
    rw [pointDivision_mul, sub_mul_smoothDividedDifference (f.smooth ⊤), ha, sub_zero]

/-- One actual division removes one vanishing derivative, including its removable value. -/
theorem pointDivision_vanishing_derivative (f : SchwartzMap ℝ ℂ)
    (hf : HasCompactSupport (f : ℝ → ℂ)) (a : ℝ) (ha : f a = 0) (r : ℕ)
    (hr : iteratedDeriv (r+1) (f : ℝ → ℂ) a = 0) :
    iteratedDeriv r (pointDivision f hf a ha : ℝ → ℂ) a = 0 := by
  rw [pointDivision_eq_dividedDifference, iteratedDeriv_smoothDividedDifference]
  simp only [weightedDividedDifference, sub_self, mul_zero, add_zero, hr, smul_zero,
    intervalIntegral.integral_zero]

/-- Vanishing jets give a constructed compact Schwartz factor, with no factorization certificate. -/
theorem exists_compact_factor_of_vanishing_jets (n : ℕ) (f : SchwartzMap ℝ ℂ)
    (hf : HasCompactSupport (f : ℝ → ℂ)) (a : ℝ)
    (hj : ∀ r < n, iteratedDeriv r (f : ℝ → ℂ) a = 0) :
    ∃ g : SchwartzMap ℝ ℂ, HasCompactSupport (g : ℝ → ℂ) ∧
      ∀ x : ℝ, f x = ((x-a:ℝ):ℂ)^n * g x := by
  induction n generalizing f with
  | zero => exact ⟨f,hf,by intro x; simp⟩
  | succ n ih =>
      have ha : f a = 0 := by simpa only [iteratedDeriv_zero] using hj 0 (by omega)
      let g := pointDivision f hf a ha
      have hg : HasCompactSupport (g : ℝ → ℂ) := pointDivision_hasCompactSupport f hf a ha
      have hgj : ∀ r < n, iteratedDeriv r (g : ℝ → ℂ) a = 0 := by
        intro r hr
        exact pointDivision_vanishing_derivative f hf a ha r (hj (r+1) (by omega))
      obtain ⟨u,hu,he⟩ := ih g hg hgj
      refine ⟨u,hu,fun x => ?_⟩
      calc
        f x = ((x-a:ℝ):ℂ)*g x := (pointDivision_mul f hf a ha x).symm
        _ = ((x-a:ℝ):ℂ)^(n+1)*u x := by rw [he x,pow_succ]; ring

/-- A fixed profile evaluated at a shrinking affine scale. -/
def pointRescaledProfile (g : SchwartzMap ℝ ℂ) (a δ : ℝ) (hδ : 0 < δ) : SchwartzMap ℝ ℂ :=
  combSchwartzDilation δ hδ.ne' (combSchwartzTranslation a g)

/-- The rescaled Schwartz profile has its literal affine evaluation. -/
theorem pointRescaledProfile_apply (g : SchwartzMap ℝ ℂ) (a δ : ℝ) (hδ : 0 < δ) (x : ℝ) :
    pointRescaledProfile g a δ hδ x = g (a+δ*x) := by
  simp only [pointRescaledProfile, combSchwartzDilation_apply, combSchwartzTranslation_apply]

private theorem pointRescaledProfile_derivative (g : SchwartzMap ℝ ℂ) (a δ : ℝ)
    (hδ : 0 < δ) (r : ℕ) :
    iteratedDeriv r (pointRescaledProfile g a δ hδ : ℝ → ℂ) =
      fun x => δ^r • iteratedDeriv r (g : ℝ → ℂ) (a+δ*x) := by
  have he : (pointRescaledProfile g a δ hδ : ℝ → ℂ) = fun x => g (a+δ*x) :=
    funext (pointRescaledProfile_apply g a δ hδ)
  rw [he]
  have hc : ContDiff ℝ r (fun y : ℝ => g (a+y)) :=
    (g.smooth r).comp (contDiff_const.add contDiff_id)
  rw [iteratedDeriv_comp_const_smul hc]
  rw [iteratedDeriv_comp_const_add]

/-- The derivative constants of the affine profile are uniform as δ tends to zero. -/
theorem exists_pointRescaledProfile_derivative_bound (g : SchwartzMap ℝ ℂ) (a : ℝ) (m : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (δ : ℝ) (hδ : 0 < δ), δ ≤ 1 →
      ∀ r ≤ m, ∀ x : ℝ, ‖iteratedDeriv r (pointRescaledProfile g a δ hδ : ℝ → ℂ) x‖ ≤ A := by
  let A : ℝ := ∑ r ∈ Finset.range (m+1), SchwartzMap.seminorm ℂ 0 r g
  refine ⟨A, Finset.sum_nonneg (fun _ _ => apply_nonneg _ _), ?_⟩
  intro δ hδ hδ1 r hr x
  rw [pointRescaledProfile_derivative, norm_smul, Real.norm_eq_abs, abs_pow, abs_of_pos hδ]
  have hp : δ^r ≤ 1 := pow_le_one₀ hδ.le hδ1
  have hg := g.le_seminorm ℂ 0 r (a+δ*x)
  simp only [pow_zero, one_mul, norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hg
  apply (mul_le_mul hp hg (norm_nonneg _) zero_le_one).trans
  rw [one_mul]
  exact Finset.single_le_sum (fun _ _ => apply_nonneg _ _) (Finset.mem_range.mpr (by omega))

/-- Actual physical localization of a Schwartz test. -/
def pointLocalization (ψ : SchwartzMap ℝ ℂ) (a δ : ℝ) (hδ : 0 < δ)
    (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.smulLeftCLM ℂ (shrinkingBump ψ a δ hδ) f

/-- The vanishing power survives rescaling as the explicit scalar δ^n. -/
theorem pointLocalization_factorization (n : ℕ) (ψ f g : SchwartzMap ℝ ℂ) (a : ℝ)
    (hf : ∀ x : ℝ, f x = ((x-a:ℝ):ℂ)^n*g x) (δ : ℝ) (hδ : 0 < δ) :
    pointLocalization ψ a δ hδ f = (δ:ℂ)^n • combSchwartzTranslation (-a)
      (combSchwartzDilation δ⁻¹ (inv_ne_zero hδ.ne')
        (SchwartzMap.smulLeftCLM ℂ (pointRescaledProfile g a δ hδ) (mixedSchwartz n 0 ψ))) := by
  ext x
  simp only [pointLocalization, SchwartzMap.smulLeftCLM_apply_apply (shrinkingBump ψ a δ hδ).hasTemperateGrowth,
    shrinkingBump_apply, smul_apply, combSchwartzTranslation_apply, combSchwartzDilation_apply,
    SchwartzMap.smulLeftCLM_apply_apply (pointRescaledProfile g a δ hδ).hasTemperateGrowth,
    pointRescaledProfile_apply, mixedSchwartz_apply, iteratedDeriv_zero, smul_eq_mul, hf x]
  have he : δ⁻¹*(-a+x) = (x-a)/δ := by ring
  have hg : a+δ*(δ⁻¹*(-a+x)) = x := by field_simp; ring
  rw [hg, he]
  have hp : (δ:ℂ)^n * (((x-a)/δ:ℝ):ℂ)^n = ((x-a:ℝ):ℂ)^n := by
    rw [← mul_pow]
    congr 1
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hδ.ne']
  calc
    _ = ((x-a:ℝ):ℂ)^n * (g x * ψ ((x-a)/δ)) := by ring
    _ = _ := by rw [← hp]; ring

/-- A genuine vanished power yields a quantitative original-norm localization bound. -/
theorem exists_pointLocalization_norm_bound_of_factor (p : ℕ) (ψ f g : SchwartzMap ℝ ℂ)
    (a : ℝ) (hf : ∀ x : ℝ, f x = ((x-a:ℝ):ℂ)^(2*p+1)*g x) :
    ∃ K : ℝ, 0 < K ∧ ∀ (δ : ℝ) (hδ : 0 < δ), δ ≤ 1 →
      ‖schwartzToHermiteScale p (pointLocalization ψ a δ hδ f)‖ ≤ K*δ := by
  obtain ⟨A,hA,hAbound⟩ := exists_pointRescaledProfile_derivative_bound g a (2*p)
  obtain ⟨B,hB,hBbound⟩ := exists_native_bounded_multiplier_bound p A hA
  obtain ⟨D,hD,hDbound⟩ := exists_large_hermite_dilation_bound p
  obtain ⟨T,hT,hTbound⟩ := exists_hermite_translation_bound p
  let u := mixedSchwartz (2*p+1) 0 ψ
  let K : ℝ := T*(1+|a|)^(2*p)*D*B*‖schwartzToHermiteScale p u‖+1
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K,hK,?_⟩
  intro δ hδ hδ1
  let v := SchwartzMap.smulLeftCLM ℂ (pointRescaledProfile g a δ hδ) u
  have hv : ‖schwartzToHermiteScale p v‖ ≤ B*‖schwartzToHermiteScale p u‖ :=
    hBbound _ (pointRescaledProfile g a δ hδ).hasTemperateGrowth (hAbound δ hδ hδ1) u
  have hi : 1 ≤ δ⁻¹ := by
    rw [inv_eq_one_div]
    exact (le_div_iff₀ hδ).mpr (by simpa using hδ1)
  have hd := hDbound δ⁻¹ (inv_ne_zero hδ.ne') hi v
  have ht := hTbound (-a) (combSchwartzDilation δ⁻¹ (inv_ne_zero hδ.ne') v)
  rw [abs_neg] at ht
  rw [pointLocalization_factorization (2*p+1) ψ f g a hf δ hδ, map_smul, norm_smul,
    norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ]
  change δ^(2*p+1)*‖schwartzToHermiteScale p (combSchwartzTranslation (-a)
    (combSchwartzDilation δ⁻¹ (inv_ne_zero hδ.ne') v))‖ ≤ _
  have he : δ^(2*p+1)*δ⁻¹^(2*p) = δ := by
    rw [pow_succ]
    calc
      δ^(2*p)*δ*δ⁻¹^(2*p) = (δ*δ⁻¹)^(2*p)*δ := by rw [mul_pow]; ring
      _ = δ := by rw [mul_inv_cancel₀ hδ.ne', one_pow, one_mul]
  calc
    _ ≤ δ^(2*p+1)*(T*(1+|a|)^(2*p)*(D*δ⁻¹^(2*p)*(B*‖schwartzToHermiteScale p u‖))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact ht.trans (mul_le_mul_of_nonneg_left
        (hd.trans (mul_le_mul_of_nonneg_left hv (by positivity))) (by positivity))
    _ = (T*(1+|a|)^(2*p)*D*B*‖schwartzToHermiteScale p u‖)*δ := by
      calc
        _ = (T*(1+|a|)^(2*p)*D*B*‖schwartzToHermiteScale p u‖)*(δ^(2*p+1)*δ⁻¹^(2*p)) := by ring
        _ = _ := by rw [he]
    _ ≤ K*δ := by dsimp [K]; nlinarith

/-- Vanishing jets through order2p imply an original H_p localization norm O(δ).
The compact factor is constructed from the test; none is assumed. -/
theorem exists_pointLocalization_norm_bound_of_vanishing_jets (p : ℕ)
    (ψ f : SchwartzMap ℝ ℂ) (hf : HasCompactSupport (f : ℝ → ℂ)) (a : ℝ)
    (hj : ∀ r ≤ 2*p, iteratedDeriv r (f : ℝ → ℂ) a = 0) :
    ∃ K : ℝ, 0 < K ∧ ∀ (δ : ℝ) (hδ : 0 < δ), δ ≤ 1 →
      ‖schwartzToHermiteScale p (pointLocalization ψ a δ hδ f)‖ ≤ K*δ := by
  obtain ⟨g,hg,hfactor⟩ := exists_compact_factor_of_vanishing_jets (2*p+1) f hf a
    (fun r hr => hj r (by omega))
  exact exists_pointLocalization_norm_bound_of_factor p ψ f g a hfactor

/-- Ordinary point support on compact tests: every test vanishing near a is annihilated.
This permits derivatives of Dirac and is distinct from value-only atomicity. -/
def DistributionSupportedAt (a : ℝ) (U : TemperedDistribution ℝ ℂ) : Prop :=
  ∀ f : SchwartzMap ℝ ℂ, HasCompactSupport (f : ℝ → ℂ) →
    (f : ℝ → ℂ) =ᶠ[𝓝 a] (fun _ => 0) → U f = 0

/-- Multiplying a compact test by the physical cutoff preserves compact support. -/
theorem pointLocalization_hasCompactSupport (ψ f : SchwartzMap ℝ ℂ)
    (hf : HasCompactSupport (f : ℝ → ℂ)) (a δ : ℝ) (hδ : 0 < δ) :
    HasCompactSupport (pointLocalization ψ a δ hδ f : ℝ → ℂ) := by
  have he : (pointLocalization ψ a δ hδ f : ℝ → ℂ) =
      (shrinkingBump ψ a δ hδ : ℝ → ℂ) * (f : ℝ → ℂ) := by
    ext x
    simp only [pointLocalization, SchwartzMap.smulLeftCLM_apply_apply (shrinkingBump ψ a δ hδ).hasTemperateGrowth,
      Pi.mul_apply, smul_eq_mul]
  rw [he]
  exact hf.mul_left

/-- Actual point support allows localization at every positive radius. -/
theorem supportedAt_localization_eq (a : ℝ) (U : TemperedDistribution ℝ ℂ)
    (hU : DistributionSupportedAt a U) (f : SchwartzMap ℝ ℂ)
    (hf : HasCompactSupport (f : ℝ → ℂ)) (δ : ℝ) (hδ : 0 < δ) :
    U f = U (pointLocalization compactSchwartzCutoff a δ hδ f) := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply hU
  · exact hf.sub (pointLocalization_hasCompactSupport _ _ hf a δ hδ)
  · filter_upwards [Metric.ball_mem_nhds a hδ] with x hx
    change f x - pointLocalization compactSchwartzCutoff a δ hδ f x = 0
    rw [pointLocalization, SchwartzMap.smulLeftCLM_apply_apply (shrinkingBump compactSchwartzCutoff a δ hδ).hasTemperateGrowth,
      shrinkingBump_apply, compactSchwartzCutoff_eq_one, one_smul, sub_self]
    rw [abs_div, abs_of_pos hδ]
    apply (div_le_iff₀ hδ).mpr
    have hh : |x-a| < δ := by simpa only [Metric.mem_ball, Real.dist_eq] using hx
    linarith

/-- Original order p and point support force annihilation of every compact test
whose derivatives through2p vanish at the point. No jet representation is assumed. -/
theorem supportedAt_annihilates_vanishing_jets (p : ℕ) (T : HermiteScale (-(p:ℤ))) (a : ℝ)
    (hT : DistributionSupportedAt a (hermiteScaleDistribution p T))
    (f : SchwartzMap ℝ ℂ) (hf : HasCompactSupport (f : ℝ → ℂ))
    (hj : ∀ r ≤ 2*p, iteratedDeriv r (f : ℝ → ℂ) a = 0) :
    hermiteScaleDistribution p T f = 0 := by
  obtain ⟨K,hK,hbound⟩ := exists_pointLocalization_norm_bound_of_vanishing_jets p
    compactSchwartzCutoff f hf a hj
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ : ℝ := min 1 (ε/(‖T‖*K+1))
  have hδ : 0 < δ := lt_min zero_lt_one (div_pos hε (by positivity))
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδε : (‖T‖*K+1)*δ ≤ ε := by
    have hh := min_le_right (1:ℝ) (ε/(‖T‖*K+1))
    have hc : 0 < ‖T‖*K+1 := by positivity
    simpa only [δ, mul_comm] using (le_div_iff₀ hc).mp hh
  have hlocal := supportedAt_localization_eq a _ hT f hf δ hδ
  rw [hlocal, zero_add]
  rw [hermiteScaleDistribution_apply]
  have hpair := norm_hermiteScalePairing_le (p:ℤ) T
    (schwartzToHermiteScale p (pointLocalization compactSchwartzCutoff a δ hδ f))
  have hb := hbound δ hδ hδ1
  calc
    _ ≤ ‖T‖ * ‖schwartzToHermiteScale p (pointLocalization compactSchwartzCutoff a δ hδ f)‖ := hpair
    _ ≤ ‖T‖*(K*δ) := mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    _ ≤ ε := by nlinarith

/-- Fixed compact probes for the ordinary derivatives at the point. -/
def pointJetBasis (r : ℕ) (a : ℝ) : SchwartzMap ℝ ℂ :=
  localJetProbe compactSchwartzCutoff 1 zero_lt_one r a

/-- The fixed probes have compact support. -/
theorem pointJetBasis_hasCompactSupport (r : ℕ) (a : ℝ) :
    HasCompactSupport (pointJetBasis r a : ℝ → ℂ) := by
  have hs : HasCompactSupport (fun x : ℝ => compactSchwartzCutoff (x-a)) := by
    simpa only [Function.comp_def, Homeomorph.coe_addRight, sub_eq_add_neg] using
      compactSchwartzCutoff_hasCompactSupport.comp_homeomorph (Homeomorph.addRight (-a))
  have he : (pointJetBasis r a : ℝ → ℂ) =
      (fun x : ℝ => ((x-a:ℝ):ℂ)^r/(r.factorial:ℂ)) * (fun x => compactSchwartzCutoff (x-a)) := by
    funext x
    simp only [pointJetBasis,localJetProbe_apply,div_one,Pi.mul_apply]
  rw [he]
  exact hs.mul_left

/-- The probes recover one ordinary derivative and kill every other one. -/
theorem pointJetBasis_derivative (r n : ℕ) (a : ℝ) :
    iteratedDeriv n (pointJetBasis r a : ℝ → ℂ) a = if n=r then 1 else 0 := by
  apply localJetProbe_derivative_center
  filter_upwards [Metric.ball_mem_nhds (0:ℝ) zero_lt_one] with x hx
  have hh : |x| < 1 := by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using hx
  exact compactSchwartzCutoff_eq_one hh.le

/-- The finite compact interpolant of all jets through the prescribed order. -/
def pointJetInterpolant (N : ℕ) (a : ℝ) (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  ∑ r ∈ Finset.range (N+1), iteratedDeriv r (f : ℝ → ℂ) a • pointJetBasis r a

/-- Interpolation preserves compact support. -/
theorem pointJetInterpolant_hasCompactSupport (N : ℕ) (a : ℝ) (f : SchwartzMap ℝ ℂ) :
    HasCompactSupport (pointJetInterpolant N a f : ℝ → ℂ) := by
  classical
  change HasCompactSupport (fun x => (∑ r ∈ Finset.range (N+1),
    iteratedDeriv r (f : ℝ → ℂ) a • pointJetBasis r a) x)
  simp only [_root_.sum_apply,_root_.smul_apply]
  convert! (HasCompactSupport.finset_sum (s := Finset.range (N+1))
      (f := fun r => iteratedDeriv r (f : ℝ → ℂ) a • (pointJetBasis r a : ℝ → ℂ))
      (fun r hr => (pointJetBasis_hasCompactSupport r a).smul_left)) using 1
  ext x
  simp only [Finset.sum_apply,Pi.smul_apply]

/-- Every jet throughN is matched exactly. -/
theorem pointJetInterpolant_derivative (N n : ℕ) (hn : n ≤ N) (a : ℝ) (f : SchwartzMap ℝ ℂ) :
    iteratedDeriv n (pointJetInterpolant N a f : ℝ → ℂ) a = iteratedDeriv n (f : ℝ → ℂ) a := by
  have he : (pointJetInterpolant N a f : ℝ → ℂ) =
      fun x => ∑ r ∈ Finset.range (N+1), iteratedDeriv r (f : ℝ → ℂ) a • pointJetBasis r a x := by
    funext x
    simp only [pointJetInterpolant,_root_.sum_apply,_root_.smul_apply]
  rw [he,iteratedDeriv_fun_sum (fun r hr =>
    (((pointJetBasis r a).smooth n).const_smul _).contDiffAt)]
  simp only [iteratedDeriv_fun_const_smul_field,pointJetBasis_derivative]
  rw [Finset.sum_eq_single n]
  · simp
  · intro r hr hne
    simp [Ne.symm hne]
  · intro hnot
    exact (hnot (Finset.mem_range.mpr (by omega))).elim

/-- Finite native order and ordinary point support yield an actual finite jet formula
on compact tests, with coefficients read from the explicit probes. -/
theorem supportedAt_compact_jet_formula (p : ℕ) (T : HermiteScale (-(p:ℤ))) (a : ℝ)
    (hT : DistributionSupportedAt a (hermiteScaleDistribution p T))
    (f : SchwartzMap ℝ ℂ) (hf : HasCompactSupport (f : ℝ → ℂ)) :
    hermiteScaleDistribution p T f = ∑ r ∈ Finset.range (2*p+1),
      hermiteScaleDistribution p T (pointJetBasis r a) * iteratedDeriv r (f : ℝ → ℂ) a := by
  have hzero := supportedAt_annihilates_vanishing_jets p T a hT
    (f-pointJetInterpolant (2*p) a f) (hf.sub (pointJetInterpolant_hasCompactSupport _ _ _)) (by
      intro r hr
      change iteratedDeriv r ((f : ℝ → ℂ)-(pointJetInterpolant (2*p) a f : ℝ → ℂ)) a = 0
      rw [iteratedDeriv_sub (f.smooth r).contDiffAt ((pointJetInterpolant (2*p) a f).smooth r).contDiffAt,
        pointJetInterpolant_derivative (2*p) r hr,sub_self])
  rw [map_sub] at hzero
  rw [sub_eq_zero] at hzero
  rw [hzero,pointJetInterpolant,map_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [map_smul,smul_eq_mul,mul_comm]

/-- Equality on genuine compact Schwartz tests determines the complete distribution. -/
theorem distributions_eq_of_compact_test_eq (U V : TemperedDistribution ℝ ℂ)
    (h : ∀ f : SchwartzMap ℝ ℂ, HasCompactSupport (f : ℝ → ℂ) → U f = V f) : U = V := by
  ext f
  have hU : Tendsto (fun N : ℕ => U (compactSchwartzApproximation N f)) atTop (nhds (U f)) :=
    (U.continuous.tendsto f).comp (compactSchwartzApproximation_tendsto f)
  have hV : Tendsto (fun N : ℕ => V (compactSchwartzApproximation N f)) atTop (nhds (V f)) :=
    (V.continuous.tendsto f).comp (compactSchwartzApproximation_tendsto f)
  have he : (fun N : ℕ => U (compactSchwartzApproximation N f)) =
      fun N : ℕ => V (compactSchwartzApproximation N f) := by
    funext N
    exact h _ (compactSchwartzApproximation_hasCompactSupport N f)
  rw [he] at hU
  exact tendsto_nhds_unique hU hV

/-- A point-supported original H_-p source is an actual sum of Dirac derivatives
through degree2p. Coefficients and signs are derived, with no supplied jet certificate. -/
theorem supportedAt_eq_sum_diracDerivatives (p : ℕ) (T : HermiteScale (-(p:ℤ))) (a : ℝ)
    (hT : DistributionSupportedAt a (hermiteScaleDistribution p T)) :
    hermiteScaleDistribution p T = ∑ r ∈ Finset.range (2*p+1),
      ((-1:ℂ)^r * hermiteScaleDistribution p T (pointJetBasis r a)) • localDiracDerivative r a := by
  apply distributions_eq_of_compact_test_eq
  intro f hf
  rw [supportedAt_compact_jet_formula p T a hT f hf]
  simp only [_root_.sum_apply,_root_.smul_apply,localDiracDerivative_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro r hr
  have hs : (-1:ℂ)^r * (-1:ℂ)^r = 1 := by rw [← mul_pow]; simp
  calc
    _ = ((-1:ℂ)^r*(-1:ℂ)^r) *
      (hermiteScaleDistribution p T (pointJetBasis r a)*iteratedDeriv r (f : ℝ → ℂ) a) := by rw [hs,one_mul]
    _ = _ := by ring

end
end MeyerGeneralProblem.Adaptive
