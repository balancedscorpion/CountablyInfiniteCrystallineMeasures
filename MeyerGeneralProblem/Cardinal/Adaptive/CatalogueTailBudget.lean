module

public import MeyerGeneralProblem.Cardinal.Adaptive.FourierTailBounds
public import MeyerGeneralProblem.Cardinal.Adaptive.ShrinkingBumpBounds

@[expose] public section

/-! # Full Fourier tail budgets for shrinking catalogue bumps -/

namespace MeyerGeneralProblem.Adaptive
noncomputable section
open Filter
open scoped BigOperators Topology ContDiff

/-- A fixed prefix constant and exponent specify the shrinking isolation radius. -/
def polynomialIsolationRadius (a : ℝ) (β L : ℕ) : ℝ := a / (1+(L:ℝ))^β

/-- The isolation radius is positive at every truncation. -/
theorem polynomialIsolationRadius_pos {a : ℝ} (ha : 0 < a) (β L : ℕ) :
    0 < polynomialIsolationRadius a β L := by unfold polynomialIsolationRadius; positivity

/-- A prefix constant at most one keeps all isolation radii at most one. -/
theorem polynomialIsolationRadius_le_one {a : ℝ} (ha : a ≤ 1) (β L : ℕ) :
    polynomialIsolationRadius a β L ≤ 1 := by
  unfold polynomialIsolationRadius
  apply (div_le_iff₀ (by positivity : (0:ℝ) < (1+(L:ℝ))^β)).mpr
  simpa only [one_mul] using ha.trans (one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) L] : (1:ℝ) ≤ 1+(L:ℝ)))

/-- The complete omitted translation operator, at unchanged original order. -/
def fourierTranslationTail (q p : ℕ) (c : Fin q → ℤ → ℂ) (s : Fin q → ℝ) (L : ℕ) :
    HermiteScale (-(p:ℤ)) →L[ℂ] HermiteScale (-(p:ℤ)) :=
  ∑' k : {k : Fin q → ℤ // (L:ℝ) < ∑ j, |(k j:ℝ)|},
    (∏ j, c j (k.val j)) • nativeTranslation p (∑ j, s j*(k.val j:ℝ))

/-- Every polynomially shrinking bump is paid by one further Fourier moment.
All constants are chosen before scales, centers, widths and the source. -/
theorem exists_catalogue_tail_bump_bound (q p β : ℕ) (c : Fin q → ℤ → ℂ)
    (hc : ∀ j r, Summable (fun n : ℤ => (1+|(n:ℝ)|)^r * ‖c j n‖))
    (ψ : SchwartzMap ℝ ℂ) (H a : ℝ) (hH : 0 ≤ H) (ha : 0 < a) (ha1 : a ≤ 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ (L : ℕ) (s : Fin q → ℝ), (∀ j, |s j| ≤ 2) →
      ∀ (y : ℝ), |y| ≤ H → ∀ T : HermiteScale (-(p:ℤ)),
      ‖hermiteScaleDistribution p (fourierTranslationTail q p c s L T)
        (shrinkingBump ψ y (polynomialIsolationRadius a β L)
          (polynomialIsolationRadius_pos ha β L))‖ ≤ K/(1+(L:ℝ))*‖T‖ := by
  obtain ⟨B,hB,hBt⟩ := exists_finite_product_translation_tail_bound q p (β*(2*p+1)+1) c
    (fun j => hc j _)
  obtain ⟨C,hC,hCb⟩ := exists_fixed_shrinkingBump_norm_bound p ψ H hH
  refine ⟨B*C/a^(2*p+1),by positivity,fun L s hs y hy T => ?_⟩
  have ht : ‖fourierTranslationTail q p c s L‖ ≤ B/(1+(L:ℝ))^(β*(2*p+1)+1) := hBt s hs L
  have hb := hCb y (polynomialIsolationRadius a β L) (polynomialIsolationRadius_pos ha β L)
    hy (polynomialIsolationRadius_le_one ha1 β L)
  have hδ := polynomialIsolationRadius_pos ha β L
  rw [hermiteScaleDistribution_apply]
  apply (norm_hermiteScalePairing_le (p:ℤ) _ _).trans
  apply (mul_le_mul ((fourierTranslationTail q p c s L).le_opNorm T) hb (norm_nonneg _) (by positivity)).trans
  apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ht (norm_nonneg T)) (by positivity)).trans_eq
  unfold polynomialIsolationRadius
  rw [div_pow, ← pow_mul, pow_succ]
  field_simp

/-- One original order has an eventual complete tail budget, uniformly in
all compact scale choices, all bounded centers and every native source. -/
theorem eventually_catalogue_tail_bump (q p β : ℕ) (c : Fin q → ℤ → ℂ)
    (hc : ∀ j r, Summable (fun n : ℤ => (1+|(n:ℝ)|)^r * ‖c j n‖))
    (ψ : SchwartzMap ℝ ℂ) (H a ε : ℝ) (hH : 0 ≤ H) (ha : 0 < a)
    (ha1 : a ≤ 1) (hε : 0 < ε) :
    ∀ᶠ L : ℕ in atTop, ∀ (s : Fin q → ℝ), (∀ j, |s j| ≤ 2) →
      ∀ (y : ℝ), |y| ≤ H → ∀ T : HermiteScale (-(p:ℤ)),
      ‖hermiteScaleDistribution p (fourierTranslationTail q p c s L T)
        (shrinkingBump ψ y (polynomialIsolationRadius a β L)
          (polynomialIsolationRadius_pos ha β L))‖ ≤ ε*‖T‖ := by
  obtain ⟨K,hK,hb⟩ := exists_catalogue_tail_bump_bound q p β c hc ψ H a hH ha ha1
  obtain ⟨N,hN⟩ := exists_nat_gt (K/ε)
  filter_upwards [eventually_ge_atTop N] with L hL
  intro s hs y hy T
  apply (hb L s hs y hy T).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply (div_le_iff₀ (by positivity : (0:ℝ) < 1+(L:ℝ))).mpr
  have hNL : (N:ℝ) ≤ L := by exact_mod_cast hL
  have hKN : K < (N:ℝ)*ε := (div_lt_iff₀ hε).mp hN
  nlinarith

/-- A single deterministic cutoff pays every order up to M, before the scale
tuple or source is chosen. The bound holds at every subsequent cutoff too. -/
theorem exists_simultaneous_catalogue_cutoff (M q β : ℕ) (c : Fin q → ℤ → ℂ)
    (hc : ∀ j r, Summable (fun n : ℤ => (1+|(n:ℝ)|)^r * ‖c j n‖))
    (ψ : SchwartzMap ℝ ℂ) (H a ε : ℝ) (hH : 0 ≤ H) (ha : 0 < a)
    (ha1 : a ≤ 1) (hε : 0 < ε) :
    ∃ L₀ : ℕ, M ≤ L₀ ∧ ∀ L ≥ L₀, ∀ p ≤ M,
      ∀ (s : Fin q → ℝ), (∀ j, |s j| ≤ 2) →
      ∀ (y : ℝ), |y| ≤ H → ∀ T : HermiteScale (-(p:ℤ)),
      ‖hermiteScaleDistribution p (fourierTranslationTail q p c s L T)
        (shrinkingBump ψ y (polynomialIsolationRadius a β L)
          (polynomialIsolationRadius_pos ha β L))‖ ≤ ε*‖T‖ := by
  have h := eventually_all.mpr (fun p : Fin (M+1) =>
    eventually_catalogue_tail_bump q p β c hc ψ H a ε hH ha ha1 hε)
  obtain ⟨N,hN⟩ := eventually_atTop.mp h
  refine ⟨max M N,le_max_left _ _,fun L hL p hp => ?_⟩
  exact hN L ((le_max_right M N).trans hL) ⟨p,by omega⟩

/-- The omitted native operator is exactly the full omitted whole-distribution
translation sum. Thus its bump bound controls the actual infinite error. -/
theorem fourierTranslationTail_realizes (q p L : ℕ) (c : Fin q → ℤ → ℂ)
    (hc : ∀ j, Summable (fun n : ℤ => (1+|(n:ℝ)|)^(2*p) * ‖c j n‖))
    (s : Fin q → ℝ) (hs : ∀ j, |s j| ≤ 2) (T : HermiteScale (-(p:ℤ))) :
    hermiteScaleDistribution p (fourierTranslationTail q p c s L T) =
      ∑' k : {k : Fin q → ℤ // (L:ℝ) < ∑ j, |(k j:ℝ)|},
        (∏ j, c j (k.val j)) • combDistributionTranslation
          (∑ j, s j*(k.val j:ℝ)) (hermiteScaleDistribution p T) :=
  native_translation_series_realizes p _ _
    ((summable_finite_frequency_moment q c s hs (2*p) hc).subtype _) T

/-- Rescaling the prefix constant makes this radius smaller than the literal
source radius c/(10*(3+2L)^β), without any future-gap dependence. -/
theorem polynomialIsolationRadius_le_source (c : ℝ) (hc : 0 ≤ c) (β L : ℕ) :
    polynomialIsolationRadius (c/(10*3^β)) β L ≤ c/(10*(3+2*(L:ℝ))^β) := by
  unfold polynomialIsolationRadius
  rw [div_div]
  have he : 10*3^β*(1+(L:ℝ))^β = 10*(3*(1+(L:ℝ)))^β := by rw [mul_pow]; ring
  rw [he]
  apply div_le_div_of_nonneg_left hc (by positivity)
  gcongr
  linarith [Nat.cast_nonneg (α := ℝ) L]

/-- Actual Fourier coefficients of any fixed finite collection of smooth
periodic factors supply all moments, so the simultaneous choice needs no
Fourier decay certificate from the caller. -/
theorem exists_periodic_catalogue_cutoff (M q β : ℕ) (g : Fin q → ℝ → ℂ)
    (hg : ∀ j, ContDiff ℝ ∞ (g j))
    (ψ : SchwartzMap ℝ ℂ) (H a ε : ℝ) (hH : 0 ≤ H) (ha : 0 < a)
    (ha1 : a ≤ 1) (hε : 0 < ε) :
    ∃ L₀ : ℕ, M ≤ L₀ ∧ ∀ L ≥ L₀, ∀ p ≤ M,
      ∀ (s : Fin q → ℝ), (∀ j, |s j| ≤ 2) →
      ∀ (y : ℝ), |y| ≤ H → ∀ T : HermiteScale (-(p:ℤ)),
      ‖hermiteScaleDistribution p
        (fourierTranslationTail q p (fun j => periodicCoefficient (g j) (hg j)) s L T)
        (shrinkingBump ψ y (polynomialIsolationRadius a β L)
          (polynomialIsolationRadius_pos ha β L))‖ ≤ ε*‖T‖ :=
  exists_simultaneous_catalogue_cutoff M q β _
    (fun j r => periodicCoefficient_all_moments (g j) (hg j) r) ψ H a ε hH ha ha1 hε

end
end MeyerGeneralProblem.Adaptive
