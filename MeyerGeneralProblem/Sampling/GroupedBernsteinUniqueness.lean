module

public import MeyerGeneralProblem.Carrier.GroupedLimitJets
public import MeyerGeneralProblem.Carrier.IndexedMultisetCounts

@[expose] public section

/-!
# Grouped multiplicity uniqueness from actual source data

Whole-line indexed compactness preserves weighted counts. Actual full-prefix
source data force all jets of every collided fiber, including source groups
whose other nodes approach different centers. Sharp Jensen then contradicts
any normalized entire limit above the exact density threshold `τ / π`.

The final theorem performs both geometric and analytic subsequence extractions;
neither a limit carrier, vanishing jets, nor uniqueness is an assumption.
Its hypotheses are the concrete uniform geometry, radial count lower bound,
entire exponential type, real-axis normalization and small grouped data.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set Filter
open scoped Topology

/-- An actual indexed/grouped limit cannot have supercritical weighted density
and vanishing source data while its entire limit is nonzero at the origin. -/
theorem not_grouped_bernstein_limit_of_source_data
    {q : ℕ} {d H τ M ρ r₀ : ℝ} {S : ℕ → ℤ → ℝ} {B : ℕ → ℤ → Bool}
    {s : ℤ → ℝ} {b : ℤ → Bool}
    (hS : ∀ n, IndexedMultisetGeometry q d H (S n))
    (hinjective : ∀ n, Function.Injective (S n)) (hd : 0 < d)
    (hcoords : ∀ j, Tendsto (fun n => S n j) atTop (𝓝 (s j)))
    (hbits : ∀ j, ∀ᶠ n in atTop, B n j = b j)
    (hsep : ∀ n, IndexedGroupSeparation (S n) (B n) d)
    (P : ∀ n anchor, IndexedSourceBlock (B n) anchor)
    (hsize : ∀ n anchor, (P n anchor).size ≤ q)
    {F : ℕ → ℂ → ℂ} {G : ℂ → ℂ}
    (hF : ∀ n, Differentiable ℂ (F n)) (hG : Differentiable ℂ G)
    (hconv : TendstoLocallyUniformlyOn F G atTop univ)
    (hdata : ∀ anchor, Tendsto (fun n =>
      (P n anchor).dataNorm (S n) (fun x : ℝ => F n (x : ℂ))) atTop (𝓝 0))
    (hτ : 0 ≤ τ) (hM : 0 < M)
    (htype : ∀ ε > 0, ∃ C > 0, ∀ z,
      ‖G z‖ ≤ C * Real.exp ((τ + ε) * ‖z‖))
    (hreal : ∀ x : ℝ, ‖G x‖ ≤ M) (hzero : G 0 ≠ 0)
    (hρ : τ / Real.pi < ρ) (hr₀ : 0 < r₀)
    (hcounts : ∀ n R, r₀ ≤ R →
      2 * ρ * R ≤ (indexedMultisetIntervalCount (S n) (-R) R : ℝ)) : False := by
  have hs := IndexedMultisetGeometry.of_pointwise_tendsto hS hcoords
  obtain ⟨ρ', hρ'low, hρ'high⟩ := exists_between hρ
  obtain ⟨r₁, hr₁, hlimitcounts⟩ := weightedRealZeroCount_lower_of_pointwise_tendsto
    hS hs hd hcoords hρ'high hr₀ hcounts
  apply not_weighted_real_zero_density_gt_type (hs.toLocallyFiniteCarrier hd)
    (indexedMultisetMultiplicity s) hG hτ hM htype hreal hzero
    (fun x _ j hj => indexedMultiset_jets_of_sourceBlock_data hS hinjective hd hcoords
      hbits hsep P hsize hF hG hconv hdata x j hj) hρ'low hr₁ hlimitcounts

/-- No normalized sequence of entire functions of type τ can have asymptotically
zero full-group data on a common supercritical indexed class. Both the actual
grouped limit and its nonzero entire function are constructed in the proof. -/
theorem not_normalized_grouped_bernstein_sequence
    {q : ℕ} {d H τ ρ r₀ : ℝ} (S : ℕ → ℤ → ℝ) (B : ℕ → ℤ → Bool)
    (hS : ∀ n, IndexedMultisetGeometry q d H (S n))
    (hinjective : ∀ n, Function.Injective (S n)) (hd : 0 < d)
    (hsep : ∀ n, IndexedGroupSeparation (S n) (B n) d)
    (P : ∀ n anchor, IndexedSourceBlock (B n) anchor)
    (hsize : ∀ n anchor, (P n anchor).size ≤ q)
    (F : ℕ → ℂ → ℂ) (hF : ∀ n, Differentiable ℂ (F n)) (hτ : 0 ≤ τ)
    (htype : ∀ n, ∀ ε > 0, ∃ C > 0, ∀ z,
      ‖F n z‖ ≤ C * Real.exp ((τ + ε) * ‖z‖))
    (hreal : ∀ n, ∀ x : ℝ, ‖F n x‖ ≤ 1)
    (horigin : ∀ n, (1 / 2 : ℝ) ≤ ‖F n 0‖)
    (hdata : ∀ anchor, Tendsto (fun n =>
      (P n anchor).dataNorm (S n) (fun x : ℝ => F n (x : ℂ))) atTop (𝓝 0))
    (hρ : τ / Real.pi < ρ) (hr₀ : 0 < r₀)
    (hcounts : ∀ n R, r₀ ≤ R →
      2 * ρ * R ≤ (indexedMultisetIntervalCount (S n) (-R) R : ℝ)) : False := by
  obtain ⟨φ, s, b, hφ, hcoords, hbits, _⟩ := exists_indexedMultiset_subsequence S B hS
  obtain ⟨ψ, G, hψ, hG, hconv, hbound, _, hzero, _⟩ :=
    exists_normalized_bernstein_subsequence (fun n => hF (φ n)) hτ
      (fun n => htype (φ n)) (fun n => hreal (φ n)) (fun n => horigin (φ n))
  have hcoords' (j : ℤ) :
      Tendsto (fun n => S (φ (ψ n)) j) atTop (𝓝 (s j)) :=
    (hcoords j).comp hψ.tendsto_atTop
  have hbits' (j : ℤ) : ∀ᶠ n in atTop, B (φ (ψ n)) j = b j :=
    hψ.tendsto_atTop.eventually (hbits j)
  apply not_grouped_bernstein_limit_of_source_data
    (fun n => hS (φ (ψ n))) (fun n => hinjective (φ (ψ n))) hd hcoords' hbits'
    (fun n => hsep (φ (ψ n))) (fun n anchor => P (φ (ψ n)) anchor)
    (fun n anchor => hsize (φ (ψ n)) anchor) (fun n => hF (φ (ψ n))) hG hconv
    (fun anchor => ((hdata anchor).comp hφ.tendsto_atTop).comp hψ.tendsto_atTop)
    hτ (by norm_num : (0 : ℝ) < 1) ?_ ?_ hzero hρ hr₀
    (fun n => hcounts (φ (ψ n)))
  · intro ε hε
    refine ⟨1, zero_lt_one, fun z => (hbound z).trans ?_⟩
    rw [one_mul]
    apply Real.exp_le_exp.mpr
    have him : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
    have h1 := mul_le_mul_of_nonneg_left him hτ
    have h2 := mul_nonneg hε.le (norm_nonneg z)
    nlinarith
  · intro x
    simpa using hbound (x : ℂ)

/-- A common positive grouped-data floor follows for the entire normalized
geometric class. The constant depends only on its displayed parameters, not
on a carrier, group count, or smallest within-group gap. -/
theorem exists_uniform_grouped_bernstein_origin_floor
    {q : ℕ} {d H τ ρ r₀ : ℝ} (hd : 0 < d) (hτ : 0 ≤ τ)
    (hρ : τ / Real.pi < ρ) (hr₀ : 0 < r₀) :
    ∃ ε > 0, ∀ (s : ℤ → ℝ) (b : ℤ → Bool)
      (P : ∀ anchor, IndexedSourceBlock b anchor) (F : ℂ → ℂ),
      IndexedMultisetGeometry q d H s → Function.Injective s →
      IndexedGroupSeparation s b d → (∀ anchor, (P anchor).size ≤ q) →
      Differentiable ℂ F →
      (∀ η > 0, ∃ C > 0, ∀ z, ‖F z‖ ≤ C * Real.exp ((τ + η) * ‖z‖)) →
      (∀ x : ℝ, ‖F x‖ ≤ 1) → (1 / 2 : ℝ) ≤ ‖F 0‖ →
      (∀ R, r₀ ≤ R → 2 * ρ * R ≤ (indexedMultisetIntervalCount s (-R) R : ℝ)) →
      ∃ anchor, ε ≤ (P anchor).dataNorm s (fun x : ℝ => F (x : ℂ)) := by
  classical
  by_contra h
  push Not at h
  have hsequence := fun n : ℕ => h ((n : ℝ) + 1)⁻¹ (by positivity)
  choose S B P F hS hinjective hsep hsize hF htype hreal horigin hcounts hsmall
    using hsequence
  apply not_normalized_grouped_bernstein_sequence S B hS hinjective hd hsep P hsize
    F hF hτ htype hreal horigin ?_ hρ hr₀ hcounts
  intro anchor
  apply squeeze_zero (fun n => Finset.sum_nonneg (fun _ _ => norm_nonneg _))
    (fun n => (hsmall n anchor).le)
  simpa only [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)

end

end MeyerGeneralProblem
