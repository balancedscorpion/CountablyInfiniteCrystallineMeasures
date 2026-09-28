module

public import MeyerGeneralProblem.Cardinal.Adaptive.NativeFourierMultiplication
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
import all Mathlib.Analysis.Normed.Ring.InfiniteSum
public import MeyerGeneralProblem.Distribution.FiniteFourierMotif

@[expose] public section

/-! # Complete finite products of periodic Fourier series

All integer tuples are retained. Product summability is proved from the
actual coefficient moments; no finite cutoff is inserted.
-/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open scoped BigOperators ContDiff FourierTransform

/-- Absolute product summability for finitely many independent indices. -/
theorem summable_fin_product_nonneg (q : ℕ) (f : Fin q → ℤ → ℝ)
    (hn : ∀ j n, 0 ≤ f j n) (hs : ∀ j, Summable (f j)) :
    Summable (fun k : Fin q → ℤ => ∏ j, f j (k j)) := by
  induction q with
  | zero => exact (hasSum_fintype _).summable
  | succ q ih =>
    have h := (hs 0).mul_of_nonneg (ih (fun j => f j.succ)
      (fun j => hn j.succ) (fun j => hs j.succ)) (hn 0)
      (fun k => Finset.prod_nonneg (fun j _ => hn j.succ (k j)))
    apply (Fin.consEquiv (fun _ : Fin (q+1) => ℤ)).summable_iff.mp
    simpa only [Function.comp_def, Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ] using h

/-- Every weighted coefficient product is summable on the whole integer cube. -/
theorem summable_fin_coefficient_moments (q : ℕ) (c : Fin q → ℤ → ℂ) (m : ℕ)
    (h : ∀ j, Summable (fun n:ℤ => (1+|(n:ℝ)|)^m * ‖c j n‖)) :
    Summable (fun k : Fin q → ℤ => ∏ j, (1+|(k j:ℝ)|)^m * ‖c j (k j)‖) :=
  summable_fin_product_nonneg q
    (fun j n => (1+|(n:ℝ)|)^m * ‖c j n‖)
    (fun _j _n => mul_nonneg (pow_nonneg (add_nonneg zero_le_one (abs_nonneg _)) _) (norm_nonneg _)) h

private theorem one_add_abs_add_le (a b : ℝ) :
    1+|a+b| ≤ (1+|a|)*(1+|b|) := by
  have h := abs_add_le a b
  have hpos := mul_nonneg (abs_nonneg a) (abs_nonneg b)
  nlinarith

/-- Uniform frequency control on a finite collection of bounded scales. -/
theorem finite_frequency_weight_le (q : ℕ) (s : Fin q → ℝ)
    (hs : ∀ j, |s j| ≤ 2) (k : Fin q → ℤ) :
    1+|∑ j, s j*(k j:ℝ)| ≤ ∏ j, (2*(1+|(k j:ℝ)|)) := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Fin.sum_univ_succ, Fin.prod_univ_succ]
    apply (one_add_abs_add_le _ _).trans
    apply mul_le_mul
    · rw [abs_mul]
      have h := mul_le_mul_of_nonneg_right (hs 0) (abs_nonneg (k 0:ℝ))
      linarith
    · exact ih (fun j => s j.succ) (fun j => hs j.succ) (fun j => k j.succ)
    · positivity
    · positivity

/-- Pointwise majorant independent of the scale tuple. -/
theorem finite_frequency_moment_le (q : ℕ) (c : Fin q → ℤ → ℂ)
    (s : Fin q → ℝ) (hs : ∀ j, |s j| ≤ 2) (m : ℕ) (k : Fin q → ℤ) :
    (1+|∑ j, s j*(k j:ℝ)|)^m * ‖∏ j, c j (k j)‖ ≤
      2^(q*m) * ∏ j, (1+|(k j:ℝ)|)^m * ‖c j (k j)‖ := by
  calc
    _ ≤ (∏ j, (2*(1+|(k j:ℝ)|)))^m * ‖∏ j, c j (k j)‖ := by
      gcongr
      exact finite_frequency_weight_le q s hs k
    _ = 2^(q*m) * ∏ j, (1+|(k j:ℝ)|)^m * ‖c j (k j)‖ := by
      rw [Finset.prod_mul_distrib, Fin.prod_const, mul_pow, ← pow_mul,
        Complex.norm_prod, ← Finset.prod_pow, Finset.prod_mul_distrib]
      ring

/-- The full frequency moment is summable, uniformly over scales bounded by two. -/
theorem summable_finite_frequency_moment (q : ℕ) (c : Fin q → ℤ → ℂ)
    (s : Fin q → ℝ) (hs : ∀ j, |s j| ≤ 2) (m : ℕ)
    (h : ∀ j, Summable (fun n:ℤ => (1+|(n:ℝ)|)^m * ‖c j n‖)) :
    Summable (fun k : Fin q → ℤ =>
      (1+|∑ j, s j*(k j:ℝ)|)^m * ‖∏ j, c j (k j)‖) :=
  Summable.of_nonneg_of_le (fun k => by positivity)
    (finite_frequency_moment_le q c s hs m)
    ((summable_fin_coefficient_moments q c m h).mul_left ((2:ℝ)^(q*m)))

/-- Absolute convergence of every finite product of summable complex families. -/
theorem summable_fin_product_norm (q : ℕ) (f : Fin q → ℤ → ℂ)
    (h : ∀ j, Summable (fun n => ‖f j n‖)) :
    Summable (fun k : Fin q → ℤ => ‖∏ j, f j (k j)‖) := by
  simpa only [Complex.norm_prod] using
    summable_fin_product_nonneg q (fun j n => ‖f j n‖) (fun _ _ => norm_nonneg _) h

/-- Multiply the complete series by summing over all tuples, not a cutoff. -/
theorem fin_product_tsum (q : ℕ) (f : Fin q → ℤ → ℂ)
    (h : ∀ j, Summable (fun n => ‖f j n‖)) :
    (∏ j, ∑' n, f j n) = ∑' k : Fin q → ℤ, ∏ j, f j (k j) := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Fin.prod_univ_succ, ih (fun j => f j.succ) (fun j => h j.succ),
      tsum_mul_tsum_of_summable_norm (h 0)
        (summable_fin_product_norm q (fun j => f j.succ) (fun j => h j.succ))]
    simpa only [Function.comp_def, Fin.consEquiv_apply, Fin.prod_univ_succ,
      Fin.cons_zero, Fin.cons_succ] using
      (Fin.consEquiv (fun _ : Fin (q+1) => ℤ)).tsum_eq
        (fun k : Fin (q+1) → ℤ => ∏ j, f j (k j))

private theorem scaled_fourier_eq_character (n : ℤ) (s x : ℝ) :
    fourier n ((s*x:ℝ):UnitAddCircle) = combModulationCharacter (s*n) x := by
  rw [fourier_coe_apply, combModulationCharacter_eq_exp]
  congr 1
  push_cast
  ring

/-- Exact whole Fourier expansion of a finite product of scaled periodic functions. -/
theorem finite_periodic_product_expansion (q : ℕ) (g : Fin q → ℝ → ℂ)
    (hg : ∀ j, ContDiff ℝ ∞ (g j)) (hp : ∀ j, Function.Periodic (g j) 1)
    (s : Fin q → ℝ) (x : ℝ) :
    (∏ j, g j (s j*x)) = ∑' k : Fin q → ℤ,
      (∏ j, periodicCoefficient (g j) (hg j) (k j)) *
        combModulationCharacter (∑ j, s j*(k j:ℝ)) x := by
  have hnorm (j : Fin q) : Summable (fun n : ℤ =>
      ‖periodicCoefficient (g j) (hg j) n * combModulationCharacter (s j*n) x‖) := by
    simpa only [norm_mul, norm_combModulationCharacter, mul_one, pow_zero, one_mul] using
      periodicCoefficient_all_moments (g j) (hg j) 0
  calc
    _ = ∏ j, ∑' n : ℤ, periodicCoefficient (g j) (hg j) n *
        combModulationCharacter (s j*n) x := by
      apply Finset.prod_congr rfl
      intro j _
      rw [periodicCoefficient_expansion (g j) (hg j) (hp j)]
      apply tsum_congr
      intro n
      rw [scaled_fourier_eq_character]
    _ = _ := by
      rw [fin_product_tsum q _ hnorm]
      apply tsum_congr
      intro k
      rw [Finset.prod_mul_distrib, combModulationCharacter_finset_sum]

/-- No-frequency cutoff is needed for convergence in the original native
operator norm, for an arbitrary finite collection of scaled periodic factors. -/
theorem finite_periodic_product_native_series (q m : ℕ) (g : Fin q → ℝ → ℂ)
    (hg : ∀ j, ContDiff ℝ ∞ (g j)) (s : Fin q → ℝ)
    (hs : ∀ j, |s j| ≤ 2) :
    Summable (fun k : Fin q → ℤ =>
      (∏ j, periodicCoefficient (g j) (hg j) (k j)) •
        nativeTranslation m (∑ j, s j*(k j:ℝ))) :=
  summable_native_translation_series m _ _
    (summable_finite_frequency_moment q _ s hs (2*m)
      (fun j => periodicCoefficient_all_moments (g j) (hg j) (2*m)))

/-- The entire finite-product operator series agrees with the entire
translation series on whole distributions at the same original order. -/
theorem finite_periodic_product_native_realizes (q m : ℕ) (g : Fin q → ℝ → ℂ)
    (hg : ∀ j, ContDiff ℝ ∞ (g j)) (s : Fin q → ℝ)
    (hs : ∀ j, |s j| ≤ 2) (T : HermiteScale (-(m:ℤ))) :
    hermiteScaleDistribution m ((∑' k : Fin q → ℤ,
      (∏ j, periodicCoefficient (g j) (hg j) (k j)) •
        nativeTranslation m (∑ j, s j*(k j:ℝ))) T) =
      ∑' k : Fin q → ℤ, (∏ j, periodicCoefficient (g j) (hg j) (k j)) •
        combDistributionTranslation (∑ j, s j*(k j:ℝ)) (hermiteScaleDistribution m T) :=
  native_translation_series_realizes m _ _
    (summable_finite_frequency_moment q _ s hs (2*m)
      (fun j => periodicCoefficient_all_moments (g j) (hg j) (2*m))) T

/-- The distinguished zero tuple has coefficient exactly one for the actual
chosen annihilators, before scales or truncations are selected. -/
theorem finite_phase_product_zero_coefficient (q : ℕ) (P R : Fin q → ℕ)
    (hP : ∀ j, 1 ≤ P j) (hR : ∀ j, 1 ≤ R j) :
    (∏ j, phaseCoefficient (P j) (R j) (hP j) (hR j) 0) = 1 := by
  simp only [phaseCoefficient_zero, Finset.prod_const_one]

/-- The actual finite scaled product is a valid Schwartz multiplier. -/
theorem finite_periodic_product_hasTemperateGrowth (q : ℕ) (g : Fin q → ℝ → ℂ)
    (hg : ∀ j, ContDiff ℝ ∞ (g j)) (hp : ∀ j, Function.Periodic (g j) 1)
    (s : Fin q → ℝ) : (fun x => ∏ j, g j (s j*x)).HasTemperateGrowth := by
  have hf (j : Fin q) : (fun x => g j (s j*x)).HasTemperateGrowth :=
    (smooth_periodic_hasTemperateGrowth (g j) (hg j) (hp j)).comp
      ((Function.HasTemperateGrowth.const (s j)).mul Function.HasTemperateGrowth.id')
  clear hg hp
  induction q with
  | zero => simp
  | succ q ih =>
    convert! (hf 0).mul (ih (fun j => g j.succ) (fun j => s j.succ) (fun j => hf j.succ)) using 1
    funext x
    simp only [Fin.prod_univ_succ, Pi.mul_apply]

/-- Complete multiplication-to-translation formula for the whole native
source and the whole finite periodic product. No omitted Fourier tail remains. -/
theorem finite_periodic_product_fourier_hasSum (q m : ℕ) (g : Fin q → ℝ → ℂ)
    (hg : ∀ j, ContDiff ℝ ∞ (g j)) (hp : ∀ j, Function.Periodic (g j) 1)
    (s : Fin q → ℝ) (hs : ∀ j, |s j| ≤ 2) (T : HermiteScale (-(m:ℤ))) :
    HasSum (fun k : Fin q → ℤ =>
      (∏ j, periodicCoefficient (g j) (hg j) (k j)) •
        combDistributionTranslation (∑ j, s j*(k j:ℝ)) (𝓕 (hermiteScaleDistribution m T)))
      (𝓕 (TemperedDistribution.smulLeftCLM ℂ (fun x => ∏ j, g j (s j*x))
        (hermiteScaleDistribution m T))) :=
  hasSum_fourier_multiplier_translations m _ _
    (summable_finite_frequency_moment q _ s hs (2*m)
      (fun j => periodicCoefficient_all_moments (g j) (hg j) (2*m)))
    _ (finite_periodic_product_hasTemperateGrowth q g hg hp s)
    (finite_periodic_product_expansion q g hg hp s) T

/-- Complete inverse-Fourier multiplication-to-translation formula for the whole native
source and the whole finite periodic product. No omitted Fourier tail remains. -/
theorem finite_periodic_product_fourierInv_hasSum (q m : ℕ) (g : Fin q → ℝ → ℂ)
    (hg : ∀ j, ContDiff ℝ ∞ (g j)) (hp : ∀ j, Function.Periodic (g j) 1)
    (s : Fin q → ℝ) (hs : ∀ j, |s j| ≤ 2) (T : HermiteScale (-(m:ℤ))) :
    HasSum (fun k : Fin q → ℤ =>
      (∏ j, periodicCoefficient (g j) (hg j) (k j)) •
        combDistributionTranslation (-(∑ j, s j*(k j:ℝ))) (𝓕⁻ (hermiteScaleDistribution m T)))
      (𝓕⁻ (TemperedDistribution.smulLeftCLM ℂ (fun x => ∏ j, g j (s j*x))
        (hermiteScaleDistribution m T))) :=
  hasSum_fourierInv_multiplier_translations m _ _
    (summable_finite_frequency_moment q _ s hs (2*m)
      (fun j => periodicCoefficient_all_moments (g j) (hg j) (2*m)))
    _ (finite_periodic_product_hasTemperateGrowth q g hg hp s)
    (finite_periodic_product_expansion q g hg hp s) T

/-- A single original operator bound is selected before all scales of a fixed
finite stage. It depends only on actual Fourier coefficient moments. -/
theorem exists_finite_product_native_norm_bound (q m : ℕ) (c : Fin q → ℤ → ℂ)
    (h : ∀ j, Summable (fun n:ℤ => (1+|(n:ℝ)|)^(2*m) * ‖c j n‖)) :
    ∃ B : ℝ, 0 < B ∧ ∀ (s : Fin q → ℝ), (∀ j, |s j| ≤ 2) →
      ‖∑' k : Fin q → ℤ, (∏ j, c j (k j)) •
        nativeTranslation m (∑ j, s j*(k j:ℝ))‖ ≤ B := by
  obtain ⟨C,hC,hbound⟩ := exists_nativeTranslation_norm_bound m
  let W (k : Fin q → ℤ) := ∏ j, (1+|(k j:ℝ)|)^(2*m) * ‖c j (k j)‖
  have hW : Summable W := summable_fin_coefficient_moments q c (2*m) h
  have hWpos : 0 ≤ ∑' k, W k := tsum_nonneg (fun k => Finset.prod_nonneg (fun j _ => by positivity))
  refine ⟨C*2^(q*(2*m))*(∑' k, W k)+1, by positivity, ?_⟩
  intro s hs
  have hb := (hW.hasSum.mul_left (C*2^(q*(2*m))))
  apply (tsum_of_norm_bounded hb (fun k => ?_)).trans (by linarith)
  rw [norm_smul]
  calc
    _ ≤ ‖∏ j, c j (k j)‖ * (C*(1+|∑ j, s j*(k j:ℝ)|)^(2*m)) :=
      mul_le_mul_of_nonneg_left (hbound _) (norm_nonneg _)
    _ = C*((1+|∑ j, s j*(k j:ℝ)|)^(2*m)*‖∏ j, c j (k j)‖) := by ring
    _ ≤ C*(2^(q*(2*m))*W k) :=
      mul_le_mul_of_nonneg_left (finite_frequency_moment_le q c s hs (2*m) k) hC.le
    _ = _ := by ring

end
end MeyerGeneralProblem.Adaptive
