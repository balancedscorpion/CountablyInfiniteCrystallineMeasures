module

public import MeyerGeneralProblem.Cardinal.Adaptive.NativeDiscreteJets
public import MeyerGeneralProblem.Cardinal.Adaptive.NativeFourierMultiplication

@[expose] public section

/-! Actual lattice support forces finite-order antiperiodic differences after Fourier transform. -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff FourierTransform

/-- A vanished smooth factor to power n kills all product jets below degree n. -/
theorem iteratedDeriv_pow_mul_eq_zero (χ ψ : ℝ → ℂ)
    (hχ : ContDiff ℝ ∞ χ) (hψ : ContDiff ℝ ∞ ψ) (a : ℝ) (ha : χ a = 0)
    (n r : ℕ) (hr : r < n) :
    iteratedDeriv r (fun x => χ x ^ n * ψ x) a = 0 := by
  induction n generalizing r with
  | zero => omega
  | succ n ih =>
      have he : (fun x => χ x ^ (n+1) * ψ x) = χ * (fun x => χ x ^ n * ψ x) := by
        ext x
        simp only [Pi.mul_apply,pow_succ]
        ring
      rw [he,iteratedDeriv_mul (hχ.of_le (by simp)).contDiffAt
        (((hχ.pow n).mul hψ).of_le (by simp)).contDiffAt]
      apply Finset.sum_eq_zero
      intro k hk
      by_cases hk0 : k=0
      · subst k
        simp only [iteratedDeriv_zero,ha,mul_zero,zero_mul]
      · have hkr : k ≤ r := by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hk
        rw [ih (r-k) (by omega),mul_zero]

/-- The actual character-plus-one Schwartz test operator. -/
def antiperiodicTest (P : ℝ) : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
  combSchwartzModulation P + ContinuousLinearMap.id ℂ _

/-- The test operator is multiplication by the positive character plus one. -/
theorem antiperiodicTest_apply (P : ℝ) (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    antiperiodicTest P f x = (combModulationCharacter P x+1)*f x := by
  simp only [antiperiodicTest,_root_.add_apply,ContinuousLinearMap.id_apply,
    combSchwartzModulation_apply]
  ring

/-- Actual iteration multiplies by the corresponding character power. -/
theorem antiperiodicTest_iter_apply (P : ℝ) (n : ℕ) (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    ((antiperiodicTest P : SchwartzMap ℝ ℂ → SchwartzMap ℝ ℂ)^[n] f) x =
      (combModulationCharacter P x+1)^n*f x := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply',antiperiodicTest_apply,ih,pow_succ]
      ring

/-- Iterated character multiplication preserves compact support. -/
theorem antiperiodicTest_iter_hasCompactSupport (P : ℝ) (n : ℕ) (f : SchwartzMap ℝ ℂ)
    (hf : HasCompactSupport (f : ℝ → ℂ)) :
    HasCompactSupport ((antiperiodicTest P : SchwartzMap ℝ ℂ → SchwartzMap ℝ ℂ)^[n] f : ℝ → ℂ) := by
  convert! hf.mul_left (f := fun x => (combModulationCharacter P x+1)^n) using 1
  ext x
  simp only [antiperiodicTest_iter_apply,Pi.mul_apply]

/-- Character smoothness, with the actual Fourier sign convention. -/
theorem contDiff_antiperiodic_character (P : ℝ) :
    ContDiff ℝ ∞ (fun x => combModulationCharacter P x+1) := by
  have he : (fun x => combModulationCharacter P x+1) =
      fun x : ℝ => Complex.exp (2*Real.pi*Complex.I*(P:ℂ)*(x:ℂ))+1 := by
    ext x
    rw [combModulationCharacter_eq_exp]
  rw [he]
  have hc : ContDiff ℝ ∞ (fun x : ℝ => (x:ℂ)) := Complex.ofRealCLM.contDiff
  fun_prop

/-- The original native jet bound proves annihilation by a sufficiently high character power. -/
theorem supportedOn_antiperiodicTest_annihilates (S : LocallyFiniteCarrier) (q : ℕ)
    (T : HermiteScale (-(q:ℤ)))
    (hT : DistributionSupportedOn S.carrier (hermiteScaleDistribution q T)) (P : ℝ)
    (hzero : ∀ a ∈ S.carrier, combModulationCharacter P a+1 = 0)
    (f : SchwartzMap ℝ ℂ) (hf : HasCompactSupport (f : ℝ → ℂ)) :
    hermiteScaleDistribution q T
      ((antiperiodicTest P : SchwartzMap ℝ ℂ → SchwartzMap ℝ ℂ)^[2*q+1] f) = 0 := by
  obtain ⟨E,hE,he⟩ := supportedOn_compact_jet_formula S q T hT _
    (antiperiodicTest_iter_hasCompactSupport P (2*q+1) f hf)
  rw [he]
  apply Finset.sum_eq_zero
  intro a ha
  apply Finset.sum_eq_zero
  intro r hr
  have hp : (((antiperiodicTest P : SchwartzMap ℝ ℂ → SchwartzMap ℝ ℂ)^[2*q+1] f) : ℝ → ℂ) =
      fun x => (combModulationCharacter P x+1)^(2*q+1)*f x := by
    ext x
    exact antiperiodicTest_iter_apply P (2*q+1) f x
  rw [hp,iteratedDeriv_pow_mul_eq_zero _ _ (contDiff_antiperiodic_character P)
    (f.smooth ⊤) a (hzero a a.property) (2*q+1) r (Finset.mem_range.mp hr),mul_zero]

/-- Actual distributional modulation plus the identity. -/
def antiperiodicModulation (P : ℝ) :
    TemperedDistribution ℝ ℂ →L[ℂ] TemperedDistribution ℝ ℂ :=
  combDistributionModulation P + ContinuousLinearMap.id ℂ _

/-- The actual positive translation plus identity on whole tempered distributions. -/
def antiperiodicDifference (P : ℝ) :
    TemperedDistribution ℝ ℂ →L[ℂ] TemperedDistribution ℝ ℂ :=
  combDistributionTranslation P + ContinuousLinearMap.id ℂ _

/-- Distributional iteration is the transpose of the genuine iterated Schwartz test operator. -/
theorem antiperiodicModulation_iter_apply (P : ℝ) (n : ℕ) (U : TemperedDistribution ℝ ℂ)
    (f : SchwartzMap ℝ ℂ) :
    ((antiperiodicModulation P : TemperedDistribution ℝ ℂ → TemperedDistribution ℝ ℂ)^[n] U) f =
      U ((antiperiodicTest P : SchwartzMap ℝ ℂ → SchwartzMap ℝ ℂ)^[n] f) := by
  induction n generalizing U with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply,ih,Function.iterate_succ_apply']
      simp only [antiperiodicModulation,antiperiodicTest,_root_.add_apply,
        ContinuousLinearMap.id_apply,combDistributionModulation_apply,map_add]

/-- Fourier carries every iterated character-plus-one operator to the positive translation-plus-one. -/
theorem fourier_antiperiodicModulation_iter (P : ℝ) (n : ℕ) (U : TemperedDistribution ℝ ℂ) :
    𝓕 ((antiperiodicModulation P : TemperedDistribution ℝ ℂ → TemperedDistribution ℝ ℂ)^[n] U) =
      (antiperiodicDifference P : TemperedDistribution ℝ ℂ → TemperedDistribution ℝ ℂ)^[n] (𝓕 U) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply',Function.iterate_succ_apply']
      change 𝓕 (combDistributionModulation P
          ((antiperiodicModulation P : TemperedDistribution ℝ ℂ → TemperedDistribution ℝ ℂ)^[n] U) +
          (antiperiodicModulation P : TemperedDistribution ℝ ℂ → TemperedDistribution ℝ ℂ)^[n] U) =
        combDistributionTranslation P
          ((antiperiodicDifference P : TemperedDistribution ℝ ℂ → TemperedDistribution ℝ ℂ)^[n] (𝓕 U)) +
          (antiperiodicDifference P : TemperedDistribution ℝ ℂ → TemperedDistribution ℝ ℂ)^[n] (𝓕 U)
      rw [FourierTransform.fourier_add,fourier_combDistributionModulation,ih]

/-- Ordinary native support on the character zero lattice gives a whole Fourier finite-difference
identity, with no value-only atomicity or jet certificate. -/
theorem supportedOn_fourier_antiperiodicDifference_eq_zero (S : LocallyFiniteCarrier) (q : ℕ)
    (T : HermiteScale (-(q:ℤ)))
    (hT : DistributionSupportedOn S.carrier (hermiteScaleDistribution q T)) (P : ℝ)
    (hzero : ∀ a ∈ S.carrier, combModulationCharacter P a+1 = 0) :
    (antiperiodicDifference P : TemperedDistribution ℝ ℂ → TemperedDistribution ℝ ℂ)^[2*q+1]
      (𝓕 (hermiteScaleDistribution q T)) = 0 := by
  have h : (antiperiodicModulation P : TemperedDistribution ℝ ℂ → TemperedDistribution ℝ ℂ)^[2*q+1]
      (hermiteScaleDistribution q T) = 0 := by
    apply distributions_eq_of_compact_test_eq
    intro f hf
    rw [antiperiodicModulation_iter_apply]
    exact supportedOn_antiperiodicTest_annihilates S q T hT P hzero f hf
  rw [← fourier_antiperiodicModulation_iter,h,FourierTransform.fourier_zero]


/-- The actual affine half-period lattice, with reciprocal frequency P. -/
def halfPeriodLatticeCarrier (P : ℝ) (hP : 0 < P) : LocallyFiniteCarrier where
  carrier := Set.range (fun n : ℤ => ((n:ℝ)+1/2)/P)
  finite_inter_Icc a b := by
    apply ((Set.finite_Icc ⌈a*P-1/2⌉ ⌊b*P-1/2⌋).image
      (fun n : ℤ => ((n:ℝ)+1/2)/P)).subset
    rintro x ⟨⟨n,rfl⟩,hlo,hhi⟩
    refine ⟨n,⟨Int.ceil_le.mpr ?_,Int.le_floor.mpr ?_⟩,rfl⟩
    · have h := (le_div_iff₀ hP).mp hlo
      linarith
    · have h := (div_le_iff₀ hP).mp hhi
      linarith

/-- The positive character is minus one at every actual half-period lattice point. -/
theorem combModulationCharacter_halfPeriod (P : ℝ) (hP : P ≠ 0) (n : ℤ) :
    combModulationCharacter P (((n:ℝ)+1/2)/P) = -1 := by
  rw [combModulationCharacter, mul_div_cancel₀ _ hP,Real.fourierChar_apply]
  have he : (((2*Real.pi*((n:ℝ)+1/2)):ℝ):ℂ)*Complex.I =
      (n:ℂ)*(2*Real.pi*Complex.I)+Real.pi*Complex.I := by
    push_cast
    ring
  rw [he,Complex.exp_add,Complex.exp_int_mul_two_pi_mul_I,Complex.exp_pi_mul_I,one_mul]

/-- Ordinary original H_-q support on the actual half-period lattice forces the whole
Fourier transform to satisfy (translation_P+I)^(2q+1)=0. -/
theorem halfPeriod_support_fourier_finite_difference (P : ℝ) (hP : 0 < P) (q : ℕ)
    (T : HermiteScale (-(q:ℤ)))
    (hT : DistributionSupportedOn (halfPeriodLatticeCarrier P hP).carrier
      (hermiteScaleDistribution q T)) :
    ((combDistributionTranslation P + ContinuousLinearMap.id ℂ (TemperedDistribution ℝ ℂ)) :
      TemperedDistribution ℝ ℂ → TemperedDistribution ℝ ℂ)^[2*q+1]
      (𝓕 (hermiteScaleDistribution q T)) = 0 := by
  apply supportedOn_fourier_antiperiodicDifference_eq_zero (halfPeriodLatticeCarrier P hP) q T hT P
  rintro a ⟨n,rfl⟩
  rw [combModulationCharacter_halfPeriod P hP.ne']
  ring

/-- The seam t*(Z+1/2) has the exact reciprocal positive translation period 1/t. -/
theorem scaledHalfInteger_support_fourier_finite_difference (t : ℝ) (ht : 0 < t) (q : ℕ)
    (T : HermiteScale (-(q:ℤ)))
    (hT : DistributionSupportedOn (Set.range (fun n : ℤ => t*((n:ℝ)+1/2)))
      (hermiteScaleDistribution q T)) :
    ((combDistributionTranslation t⁻¹ + ContinuousLinearMap.id ℂ (TemperedDistribution ℝ ℂ)) :
      TemperedDistribution ℝ ℂ → TemperedDistribution ℝ ℂ)^[2*q+1]
      (𝓕 (hermiteScaleDistribution q T)) = 0 := by
  apply halfPeriod_support_fourier_finite_difference t⁻¹ (inv_pos.mpr ht) q T
  have he : (halfPeriodLatticeCarrier t⁻¹ (inv_pos.mpr ht)).carrier =
      Set.range (fun n : ℤ => t*((n:ℝ)+1/2)) := by
    change Set.range (fun n : ℤ => ((n:ℝ)+1/2)/t⁻¹) = _
    congr 1
    funext n
    simp only [div_inv_eq_mul,mul_comm]
  rw [he]
  exact hT

end
end MeyerGeneralProblem.Adaptive
