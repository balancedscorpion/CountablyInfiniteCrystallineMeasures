module

public import MeyerGeneralProblem.Cardinal.Adaptive.NativeDifferences

@[expose] public section

/-! # Bounded leading-coefficient extraction for local difference equations -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section

/-- Vanishing on a region is tested against actual compact Schwartz functions
whose closed support lies in that region. -/
def DistributionVanishesOn (O : Set ℝ) (T : TemperedDistribution ℝ ℂ) : Prop :=
  ∀ f : SchwartzMap ℝ ℂ, HasCompactSupport (f : ℝ → ℂ) →
    tsupport (f : ℝ → ℂ) ⊆ O → T f = 0

/-- Linearity of the actual iterated difference under subtraction. -/
theorem distributionDifference_iter_sub (P : ℝ) (d : ℕ) (T U : TemperedDistribution ℝ ℂ) :
    (distributionDifference P : TemperedDistribution ℝ ℂ → TemperedDistribution ℝ ℂ)^[d] (T-U) =
    (distributionDifference P : TemperedDistribution ℝ ℂ → TemperedDistribution ℝ ℂ)^[d] T -
    (distributionDifference P : TemperedDistribution ℝ ℂ → TemperedDistribution ℝ ℂ)^[d] U := by
  induction d with
  | zero => rfl
  | succ d ih => simp only [Function.iterate_succ_apply', ih, map_sub]

/-- Linearity of the actual iterated difference under scalar multiplication. -/
theorem distributionDifference_iter_smul (P : ℝ) (d : ℕ) (c : ℂ)
    (T : TemperedDistribution ℝ ℂ) :
    (distributionDifference P : TemperedDistribution ℝ ℂ → TemperedDistribution ℝ ℂ)^[d] (c • T) =
    c • (distributionDifference P : TemperedDistribution ℝ ℂ → TemperedDistribution ℝ ℂ)^[d] T := by
  induction d with
  | zero => rfl
  | succ d ih => simp only [Function.iterate_succ_apply', ih, map_smul]

/-- Exact signed factorial used to normalize the leading periodic coefficient. -/
def differenceLeadingFactor (d : ℕ) (P : ℝ) : ℂ := (d.factorial:ℂ)*(-(P:ℂ))^d

/-- A nonzero period gives a nonzero leading factorial. -/
theorem differenceLeadingFactor_ne_zero (d : ℕ) (P : ℝ) (hP : P ≠ 0) :
    differenceLeadingFactor d P ≠ 0 := by
  unfold differenceLeadingFactor
  exact mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero d)
    (pow_ne_zero _ (neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr hP)))

/-- Extract the normalized top finite difference at the same original order,
then use the actual uniform periodization to extend its periodic restriction. -/
def nativePeriodicLeading (q d : ℕ) (P : ℝ) (hP : P ∈ Set.Icc (1/2:ℝ) 2) :
    HermiteScale (-(q:ℤ)) →L[ℂ] HermiteScale (-((q+2:ℕ):ℤ)) :=
  (nativePeriodization q P hP).comp
    ((differenceLeadingFactor d P)⁻¹ • (nativeDifference q P)^d)

/-- The extracted coefficient is globally periodic for every source. -/
theorem nativePeriodicLeading_periodic (q d : ℕ) (P : ℝ)
    (hP : P ∈ Set.Icc (1/2:ℝ) 2) (T : HermiteScale (-(q:ℤ))) :
    combDistributionTranslation P
      (hermiteScaleDistribution (q+2) (nativePeriodicLeading q d P hP T)) =
      hermiteScaleDistribution (q+2) (nativePeriodicLeading q d P hP T) :=
  nativePeriodization_periodic q P hP _

/-- On the region where the next difference vanishes, the constructed
coefficient agrees with the normalized top difference. -/
theorem nativePeriodicLeading_agrees (q d : ℕ) (P : ℝ)
    (hP : P ∈ Set.Icc (1/2:ℝ) 2) (O : Set ℝ) (hopen : IsOpen O)
    (hO : Function.Periodic (fun x => x ∈ O) P) (T : HermiteScale (-(q:ℤ)))
    (hT : DistributionVanishesOn O
      ((distributionDifference P : TemperedDistribution ℝ ℂ → TemperedDistribution ℝ ℂ)^[d+1]
        (hermiteScaleDistribution q T)))
    (f : SchwartzMap ℝ ℂ) (hf : HasCompactSupport (f : ℝ → ℂ))
    (hs : tsupport (f : ℝ → ℂ) ⊆ O) :
    hermiteScaleDistribution (q+2) (nativePeriodicLeading q d P hP T) f =
      (differenceLeadingFactor d P)⁻¹ *
        ((distributionDifference P : TemperedDistribution ℝ ℂ → TemperedDistribution ℝ ℂ)^[d]
          (hermiteScaleDistribution q T)) f := by
  let V := (differenceLeadingFactor d P)⁻¹ • ((nativeDifference q P)^d) T
  have hv : hermiteScaleDistribution q V = (differenceLeadingFactor d P)⁻¹ •
      (distributionDifference P : TemperedDistribution ℝ ℂ → TemperedDistribution ℝ ℂ)^[d]
        (hermiteScaleDistribution q T) := by
    rw [show V = (differenceLeadingFactor d P)⁻¹ • ((nativeDifference q P)^d) T from rfl,
      ← hermiteScaleDistributionCLM_apply, map_smul, hermiteScaleDistributionCLM_apply,
      nativeDifference_pow_realizes]
  have hp := nativePeriodization_agrees_of_translation_eq q P hP V O hopen hO
  have he := hp (by
    intro g hg hgs
    have hh := hT g hg hgs
    rw [Function.iterate_succ_apply', distributionDifference_apply] at hh
    rw [hv]
    simp only [smul_apply, smul_eq_mul]
    exact congrArg (fun z : ℂ => (differenceLeadingFactor d P)⁻¹*z) (sub_eq_zero.mp hh)) f hf hs
  change hermiteScaleDistribution (q+2) (nativePeriodization q P hP V) f = _
  rw [he, hv]
  rfl

/-- The actual remainder after subtracting the leading monomial, represented
at an explicitly bounded original order. -/
def nativePeriodicRemainder (q d : ℕ) (P : ℝ) (hP : P ∈ Set.Icc (1/2:ℝ) 2) :
    HermiteScale (-(q:ℤ)) →L[ℂ] HermiteScale (-((q+2+d:ℕ):ℤ)) :=
  nativeOrderInclusion q (q+2+d) -
    (nativeMonomial (q+2) d).comp (nativePeriodicLeading q d P hP)

/-- The native remainder has exactly the whole subtraction action. -/
theorem nativePeriodicRemainder_realizes (q d : ℕ) (P : ℝ)
    (hP : P ∈ Set.Icc (1/2:ℝ) 2) (T : HermiteScale (-(q:ℤ))) :
    hermiteScaleDistribution (q+2+d) (nativePeriodicRemainder q d P hP T) =
      hermiteScaleDistribution q T - monomialDistribution d
        (hermiteScaleDistribution (q+2) (nativePeriodicLeading q d P hP T)) := by
  change hermiteScaleDistribution (q+2+d)
    (nativeOrderInclusion q (q+2+d) T -
      nativeMonomial (q+2) d (nativePeriodicLeading q d P hP T)) = _
  rw [← hermiteScaleDistributionCLM_apply, map_sub, hermiteScaleDistributionCLM_apply,
    hermiteScaleDistributionCLM_apply, nativeOrderInclusion_realizes q (q+2+d) (by omega),
    nativeMonomial_realizes]

/-- One genuine bounded descent step: order d+1 local vanishing becomes order d
local vanishing after subtracting the constructed global periodic monomial. -/
theorem nativePeriodicRemainder_vanishes (q d : ℕ) (P : ℝ)
    (hP : P ∈ Set.Icc (1/2:ℝ) 2) (O : Set ℝ) (hopen : IsOpen O)
    (hO : Function.Periodic (fun x => x ∈ O) P) (T : HermiteScale (-(q:ℤ)))
    (hT : DistributionVanishesOn O
      ((distributionDifference P : TemperedDistribution ℝ ℂ → TemperedDistribution ℝ ℂ)^[d+1]
        (hermiteScaleDistribution q T))) :
    DistributionVanishesOn O
      ((distributionDifference P : TemperedDistribution ℝ ℂ → TemperedDistribution ℝ ℂ)^[d]
        (hermiteScaleDistribution (q+2+d) (nativePeriodicRemainder q d P hP T))) := by
  intro f hf hs
  rw [nativePeriodicRemainder_realizes, distributionDifference_iter_sub,
    distributionDifference_monomial_top P (by linarith [hP.1]) _
      (nativePeriodicLeading_periodic q d P hP T)]
  simp only [sub_apply, smul_apply, smul_eq_mul]
  rw [nativePeriodicLeading_agrees q d P hP O hopen hO T hT f hf hs]
  have hc := differenceLeadingFactor_ne_zero d P (by linarith [hP.1])
  change _ - differenceLeadingFactor d P * ((differenceLeadingFactor d P)⁻¹ * _) = 0
  rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul, sub_self]

/-- The inverse normalization is uniformly bounded over all allowed periods. -/
theorem differenceLeadingFactor_inv_norm_le (d : ℕ) (P : ℝ)
    (hP : P ∈ Set.Icc (1/2:ℝ) 2) : ‖(differenceLeadingFactor d P)⁻¹‖ ≤ 2^d := by
  have hp : 0 < P := by linarith [hP.1]
  have hi : P⁻¹ ≤ 2 := by
    rw [inv_eq_one_div, div_le_iff₀ hp]
    linarith [hP.1]
  have hf : (1:ℝ) ≤ (d.factorial:ℝ) := by exact_mod_cast Nat.factorial_pos d
  have hfi : (d.factorial:ℝ)⁻¹ ≤ 1 := (inv_le_one₀ (by positivity)).mpr hf
  rw [differenceLeadingFactor, norm_inv, norm_mul, norm_pow, norm_neg,
    Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp,
    mul_inv, ← inv_pow]
  calc
    (d.factorial:ℝ)⁻¹ * (P⁻¹)^d ≤ 1*2^d :=
      mul_le_mul hfi (pow_le_pow_left₀ (inv_nonneg.mpr hp.le) hi d)
        (by positivity) (by norm_num)
    _ = _ := one_mul _

/-- The constructed leading coefficient has a uniform original native norm
bound independent of the periodic region and the input source. -/
theorem exists_nativePeriodicLeading_norm_bound (q d : ℕ) :
    ∃ B > 0, ∀ (P : ℝ) (hP : P ∈ Set.Icc (1/2:ℝ) 2),
      ‖nativePeriodicLeading q d P hP‖ ≤ B := by
  obtain ⟨A,hA,ha⟩ := exists_nativePeriodization_norm_bound q
  obtain ⟨B,hB,hb⟩ := exists_nativeDifference_pow_bound q d
  refine ⟨A*(2^d*B), by positivity, ?_⟩
  intro P hP
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  rw [norm_smul]
  exact mul_le_mul (ha P hP)
    (mul_le_mul (differenceLeadingFactor_inv_norm_le d P hP) (hb P hP)
      (norm_nonneg _) (by positivity)) (by positivity) hA.le

/-- The genuine subtraction in the degree descent is uniformly bounded in the
original order q+2+d, with no dependence on the closed exceptional set. -/
theorem exists_nativePeriodicRemainder_norm_bound (q d : ℕ) :
    ∃ B > 0, ∀ (P : ℝ) (hP : P ∈ Set.Icc (1/2:ℝ) 2),
      ‖nativePeriodicRemainder q d P hP‖ ≤ B := by
  obtain ⟨A,hA,ha⟩ := exists_nativeMonomial_norm_bound (q+2) d
  obtain ⟨B,hB,hb⟩ := exists_nativePeriodicLeading_norm_bound q d
  refine ⟨1+A*B, by positivity, ?_⟩
  intro P hP
  apply (norm_sub_le _ _).trans
  apply add_le_add (nativeOrderInclusion_norm_le q (q+2+d) (by omega))
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul ha (hb P hP) (norm_nonneg _) hA.le)

end
end MeyerGeneralProblem.Adaptive
