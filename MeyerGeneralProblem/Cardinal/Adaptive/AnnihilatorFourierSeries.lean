module

public import MeyerGeneralProblem.Cardinal.Adaptive.UnitPartition
public import MeyerGeneralProblem.Distribution.IntegerComb
public import MeyerGeneralProblem.Cardinal.Adaptive.NativeDualOperators

@[expose] public section

/-!
# Complete periodic Fourier coefficients with every polynomial moment

The coefficients are actual samples of the Fourier transform of a compact
Schwartz representative. Poisson summation recovers the whole periodic
function; the original Schwartz seminorm estimate controls all integer
moments, with both infinite arms included.
-/

namespace MeyerGeneralProblem.Adaptive
noncomputable section
open Set Function MeasureTheory TopologicalSpace Filter
open scoped Topology ContDiff FourierTransform

/-- Every polynomial moment of the integer samples of an actual Schwartz
function is summable; the majorant keeps the central sample finite. -/
theorem summable_schwartz_integer_moments (f : SchwartzMap ℝ ℂ) (m : ℕ) :
    Summable (fun n:ℤ => (1+|(n:ℝ)|)^m * ‖f n‖) := by
  let C : ℝ := 2^(m+2) * (Finset.Iic (m+2,0)).sup (fun j : ℕ × ℕ => SchwartzMap.seminorm ℂ j.1 j.2) f
  apply Summable.of_norm_bounded (summable_integerCombDecay.mul_left C)
  intro n
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ)
    (m := (m+2,0)) (k := m+2) (n := 0) le_rfl le_rfl f (n:ℝ)
  have hpos : 0 < (1+|(n:ℝ)|)^2 := by positivity
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity),integerCombDecay,inv_pow,
    ← div_eq_mul_inv,le_div_iff₀ hpos]
  calc
    (1+|(n:ℝ)|)^m * ‖f n‖ * (1+|(n:ℝ)|)^2 = (1+|(n:ℝ)|)^(m+2) * ‖f n‖ := by
      rw [pow_add]
      ring
    _ ≤ C := by
      simpa only [C,Real.norm_eq_abs,norm_iteratedFDeriv_zero] using h

/-- Exact coefficients chosen from the full Fourier transform, before any cutoff. -/
def periodicCoefficient (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (n : ℤ) : ℂ :=
  𝓕 (periodicSchwartzRepresentative g hg) n

theorem periodicCoefficient_all_moments (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (m : ℕ) :
    Summable (fun n:ℤ => (1+|(n:ℝ)|)^m * ‖periodicCoefficient g hg n‖) :=
  summable_schwartz_integer_moments (𝓕 (periodicSchwartzRepresentative g hg)) m

/-- Full pointwise Fourier expansion with all coefficients retained. -/
theorem periodicCoefficient_expansion (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
    (hp : Periodic g 1) (x : ℝ) :
    g x = ∑' n:ℤ, periodicCoefficient g hg n * fourier n (x:UnitAddCircle) :=
  periodicSchwartzRepresentative_fourier g hg hp x

/-- The chosen Schwartz samples are the genuine circle Fourier coefficients,
so their normalization is independent of the compact partition. -/
theorem periodicCoefficient_eq_fourierCoeff (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
    (hp : Periodic g 1) (n : ℤ) : periodicCoefficient g hg n = fourierCoeff hp.lift n := by
  let F := periodicSchwartzRepresentative g hg
  let fc : C(ℝ,ℂ) := ⟨F,F.continuous⟩
  have hloc : ∀ K : Compacts ℝ,
      Summable (fun z : ℤ => ‖(fc.comp (ContinuousMap.addRight (z:ℝ))).restrict K‖) := by
    intro K
    exact summable_of_isBigO (Real.summable_abs_int_rpow (by norm_num : (1:ℝ)<2))
      ((isBigO_norm_restrict_cocompact (b:=2) fc (by norm_num)
        (F.isBigO_cocompact_rpow (-2)) K).comp_tendsto Int.tendsto_coe_cofinite)
  have hsum := ContinuousMap.summable_of_locally_summable_norm hloc
  have hpoint (x:ℝ) : (∑' z:ℤ, fc.comp (ContinuousMap.addRight (z:ℝ))) x = g x := by
    rw [← ContinuousMap.tsum_apply hsum]
    exact periodicSchwartzRepresentative_sum g hg hp x
  have hlift : (fc.periodic_tsum_comp_add_zsmul 1).lift = hp.lift := by
    funext x
    induction x using QuotientAddGroup.induction_on
    simp only [Periodic.lift_coe]
    simpa only [zsmul_eq_mul, mul_one] using hpoint _
  have h := Real.fourierCoeff_tsum_comp_add hloc n
  rw [hlift] at h
  exact h.symm

/-- The zeroth coefficient is the actual period integral. -/
theorem periodicCoefficient_zero (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
    (hp : Periodic g 1) : periodicCoefficient g hg 0 = ∫ x in (0:ℝ)..1, g x := by
  rw [periodicCoefficient_eq_fourierCoeff g hg hp, fourierCoeff_eq_intervalIntegral _ _ 0]
  simp only [neg_zero, fourier_zero, one_smul, one_div_one,
    zero_add, Periodic.lift_coe]

/-- Smooth periodic complex functions have globally bounded derivatives,
hence actual temperate growth with degree zero at every derivative order. -/
theorem smooth_periodic_hasTemperateGrowth (g : ℝ → ℂ)
    (hg : ContDiff ℝ ∞ g) (hp : Periodic g 1) : g.HasTemperateGrowth := by
  refine ⟨hg, ?_⟩
  intro n
  have hpn : Periodic (iteratedDeriv n g) 1 := by
    intro x
    have he : (fun y => g (y+1)) = g := funext hp
    have h := congrFun (iteratedDeriv_comp_add_const n g 1) x
    rw [he] at h
    exact h.symm
  obtain ⟨C,hC,hb⟩ := (hpn.isBounded_of_continuous (by norm_num)
    (hg.continuous_iteratedDeriv n (by simp))).exists_pos_norm_le
  refine ⟨0,C,fun x => ?_⟩
  simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, pow_zero, mul_one] using
    hb _ ⟨x,rfl⟩

/-- Complex-valued version of the chosen actual mean-one annihilator. -/
def complexPhaseAnnihilator (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) : ℝ → ℂ :=
  fun x => phaseAnnihilator P R hP hR x

theorem complexPhaseAnnihilator_smooth (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) :
    ContDiff ℝ ∞ (complexPhaseAnnihilator P R hP hR) :=
  Complex.ofRealCLM.contDiff.comp (phaseAnnihilator_spec P R hP hR).1

theorem complexPhaseAnnihilator_periodic (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) :
    Periodic (complexPhaseAnnihilator P R hP hR) 1 :=
  fun x => congrArg Complex.ofReal ((phaseAnnihilator_spec P R hP hR).2.1 x)

/-- Coefficients are fixed before scales and retain the exact constant term. -/
def phaseCoefficient (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) (n : ℤ) : ℂ :=
  periodicCoefficient _ (complexPhaseAnnihilator_smooth P R hP hR) n

theorem phaseCoefficient_zero (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) :
    phaseCoefficient P R hP hR 0 = 1 := by
  rw [phaseCoefficient, periodicCoefficient_zero _ _ (complexPhaseAnnihilator_periodic P R hP hR)]
  change (∫ x in (0:ℝ)..1, (phaseAnnihilator P R hP hR x : ℂ)) = 1
  rw [intervalIntegral.integral_ofReal, (phaseAnnihilator_spec P R hP hR).2.2.2.2.2]
  rfl

theorem phaseCoefficient_all_moments (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) (m : ℕ) :
    Summable (fun n : ℤ => (1+|(n:ℝ)|)^m * ‖phaseCoefficient P R hP hR n‖) :=
  periodicCoefficient_all_moments _ _ m

/-- Complete translation series converges in operator norm on the original
negative Hermite space whenever its actual frequency moment is summable. -/
theorem summable_native_translation_series {ι : Type*} (m : ℕ)
    (c : ι → ℂ) (freq : ι → ℝ)
    (h : Summable (fun i => (1+|freq i|)^(2*m) * ‖c i‖)) :
    Summable (fun i => c i • nativeTranslation m (freq i)) := by
  obtain ⟨C,hC,hbound⟩ := exists_nativeTranslation_norm_bound m
  apply Summable.of_norm_bounded (h.mul_left C)
  intro i
  rw [norm_smul]
  calc
    ‖c i‖ * ‖nativeTranslation m (freq i)‖ ≤ ‖c i‖ * (C*(1+|freq i|)^(2*m)) :=
      mul_le_mul_of_nonneg_left (hbound _) (norm_nonneg _)
    _ = C*((1+|freq i|)^(2*m)*‖c i‖) := by ring

/-- Applying the complete operator series gives the complete vector series,
without any finite Fourier cutoff or loss of Hermite order. -/
theorem native_translation_series_apply {ι : Type*} (m : ℕ)
    (c : ι → ℂ) (freq : ι → ℝ)
    (h : Summable (fun i => (1+|freq i|)^(2*m) * ‖c i‖))
    (T : HermiteScale (-(m:ℤ))) :
    (∑' i, c i • nativeTranslation m (freq i)) T =
      ∑' i, c i • nativeTranslation m (freq i) T := by
  exact ((ContinuousLinearMap.apply ℂ (HermiteScale (-(m:ℤ))) T).hasSum
    (summable_native_translation_series m c freq h).hasSum).tsum_eq.symm

/-- The native series realizes the entire distributional translation sum. -/
theorem native_translation_series_realizes {ι : Type*} (m : ℕ)
    (c : ι → ℂ) (freq : ι → ℝ)
    (h : Summable (fun i => (1+|freq i|)^(2*m) * ‖c i‖))
    (T : HermiteScale (-(m:ℤ))) :
    hermiteScaleDistribution m ((∑' i, c i • nativeTranslation m (freq i)) T) =
      ∑' i, c i • combDistributionTranslation (freq i) (hermiteScaleDistribution m T) := by
  have hv := (ContinuousLinearMap.apply ℂ (HermiteScale (-(m:ℤ))) T).hasSum
    (summable_native_translation_series m c freq h).hasSum
  have hd := (hermiteScaleDistributionCLM m).hasSum hv
  have he : HasSum
      (fun i => c i • combDistributionTranslation (freq i) (hermiteScaleDistribution m T))
      (hermiteScaleDistribution m ((∑' i, c i • nativeTranslation m (freq i)) T)) := by
    simpa only [ContinuousLinearMap.apply_apply, smul_apply,
      map_smul, hermiteScaleDistributionCLM_apply, nativeTranslation_realizes] using hd
  exact he.tsum_eq.symm

end
end MeyerGeneralProblem.Adaptive
