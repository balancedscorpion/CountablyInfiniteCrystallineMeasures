module

public import MeyerGeneralProblem.Sampling.BernsteinJensen
public import MeyerGeneralProblem.Carrier.UniformDensity

@[expose] public section

/-!
# Multiplicity-sensitive zero counting and the sharp Jensen threshold

Finite radial counts are integrated against `1 / t`; the resulting logarithmic
weights are compared with the genuine zero divisor. No lower logarithmic-density
estimate or uniqueness statement is assumed.
-/

noncomputable section

open Set Filter Complex MeasureTheory Metric Real
open scoped Topology

namespace MeyerGeneralProblem

private theorem intervalIntegrable_cutoff_inv {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    (a : ℝ) : IntervalIntegrable (fun t => if a < t then t⁻¹ else 0) volume r R := by
  have hi : IntervalIntegrable (fun t : ℝ => t⁻¹) volume r R :=
    intervalIntegral.intervalIntegrable_inv
      (fun t ht => ne_of_gt (hr.trans_le ((uIcc_of_le hrR ▸ ht).1)))
      continuous_id.continuousOn
  change IntervalIntegrable ((Ioi a).indicator (fun t : ℝ => t⁻¹)) volume r R
  exact intervalIntegrable_iff.mpr (hi.def'.indicator measurableSet_Ioi)

private theorem integral_cutoff_inv {r R a : ℝ} (hr : 0 < r) (hrR : r ≤ R) (haR : a ≤ R) :
    (∫ t : ℝ in r..R, if a < t then t⁻¹ else 0) = Real.log (R / max a r) := by
  change (∫ t : ℝ in r..R, (Ioi a).indicator (fun t : ℝ => t⁻¹) t) = _
  have hinter : Ioi a ∩ Ioc r R = Ioc (max a r) R := by ext t; simp; tauto
  rw [intervalIntegral.integral_of_le hrR, MeasureTheory.integral_indicator measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi, hinter,
    ← intervalIntegral.integral_of_le (max_le haR hrR),
    integral_inv_of_pos (hr.trans_le (le_max_right _ _)) (hr.trans_le hrR)]

/-- A lower bound for every finite weighted radial count yields the sharp linear
lower bound for its logarithmic sum, without a loss in the density coefficient. -/
theorem finite_log_sum_ge_of_weighted_radial_counts
    {r R d : ℝ} (s : Finset ℂ) (m : ℂ → ℕ) (hr : 0 < r) (hrR : r ≤ R)
    (hnodes : ∀ z ∈ s, ‖z‖ ≤ R) (hzero : ∀ z ∈ s, z = 0 → m z = 0)
    (hcounts : ∀ t ∈ Icc r R,
      2 * d * t ≤ ∑ z ∈ s, if ‖z‖ < t then (m z : ℝ) else 0) :
    2 * d * (R - r) ≤ ∑ z ∈ s, (m z : ℝ) * Real.log (R * ‖z‖⁻¹) := by
  have hi (z : ℂ) : IntervalIntegrable
      (fun t : ℝ => (m z : ℝ) * (if ‖z‖ < t then t⁻¹ else 0)) volume r R :=
    (intervalIntegrable_cutoff_inv hr hrR ‖z‖).const_mul (m z : ℝ)
  have hlower : ∀ t ∈ Icc r R,
      2 * d ≤ ∑ z ∈ s, (m z : ℝ) * (if ‖z‖ < t then t⁻¹ else 0) := by
    intro t ht
    have ht0 : 0 < t := hr.trans_le ht.1
    have h := mul_le_mul_of_nonneg_right (hcounts t ht) (inv_pos.mpr ht0).le
    rw [mul_assoc, mul_inv_cancel₀ ht0.ne', mul_one, Finset.sum_mul] at h
    simpa only [ite_mul, zero_mul, mul_ite, mul_zero] using h
  calc
    2 * d * (R - r) = ∫ t : ℝ in r..R, 2 * d := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
      ring
    _ ≤ ∫ t : ℝ in r..R, ∑ z ∈ s, (m z : ℝ) * (if ‖z‖ < t then t⁻¹ else 0) :=
      intervalIntegral.integral_mono_on hrR intervalIntegrable_const
        (by simpa only [Finset.sum_fn] using IntervalIntegrable.sum s (fun z _ => hi z)) hlower
    _ = ∑ z ∈ s, (m z : ℝ) * Real.log (R / max ‖z‖ r) := by
      rw [intervalIntegral.integral_finsetSum (fun z _ => hi z)]
      apply Finset.sum_congr rfl
      intro z hz
      rw [intervalIntegral.integral_const_mul, integral_cutoff_inv hr hrR (hnodes z hz)]
    _ ≤ ∑ z ∈ s, (m z : ℝ) * Real.log (R * ‖z‖⁻¹) := by
      apply Finset.sum_le_sum
      intro z hz
      by_cases hz0 : z = 0
      · simp [hzero z hz hz0]
      · apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        apply Real.log_le_log (div_pos (hr.trans_le hrR) (hr.trans_le (le_max_right _ _)))
        rw [← div_eq_mul_inv]
        exact div_le_div_of_nonneg_left (hr.trans_le hrR).le (norm_pos_iff.mpr hz0)
          (le_max_left _ _)

/-- The total prescribed jet multiplicity in the open centered real interval
`(-R, R)`. The carrier, rather than a logarithmic density certificate, determines
the finite set being counted. -/
noncomputable def weightedRealZeroCount (S : LocallyFiniteCarrier) (m : ℝ → ℕ) (R : ℝ) : ℕ :=
  ∑ x ∈ (S.finite_inter_Ioo (-R) R).toFinset, m x

/-- A nonzero-at-origin bounded entire function of type at most `τ` cannot have
real jet zeros whose actual eventual radial multiplicity count is at least
`2 d R` for `d > τ / π`. There is no separation or minimum cluster-gap premise. -/
theorem not_weighted_real_zero_density_gt_type
    {G : ℂ → ℂ} {τ M d r₀ : ℝ} (S : LocallyFiniteCarrier) (m : ℝ → ℕ)
    (hG : Differentiable ℂ G) (hτ : 0 ≤ τ) (hM : 0 < M)
    (htype : ∀ ε > 0, ∃ C > 0, ∀ z,
      ‖G z‖ ≤ C * Real.exp ((τ + ε) * ‖z‖))
    (hreal : ∀ x : ℝ, ‖G x‖ ≤ M) (hzero : G 0 ≠ 0)
    (hjets : ∀ x ∈ S.carrier, ∀ j < m x, iteratedDeriv j G (x : ℂ) = 0)
    (hd : τ / π < d) (hr₀ : 0 < r₀)
    (hcounts : ∀ R ≥ r₀, 2 * d * R ≤ (weightedRealZeroCount S m R : ℝ)) : False := by
  classical
  have hmargin : 0 < 2 * d - 2 * τ / π := by rw [mul_div_assoc]; linarith
  obtain ⟨R, hR⟩ := exists_gt (max r₀
    ((Real.log M - Real.log ‖G 0‖ + 2 * d * r₀) / (2 * d - 2 * τ / π)))
  have hrR : r₀ ≤ R := (le_max_left _ _).trans hR.le
  have hRpos : 0 < R := hr₀.trans_le hrR
  have hlarge : Real.log M - Real.log ‖G 0‖ + 2 * d * r₀ <
      (2 * d - 2 * τ / π) * R := by
    have := (div_lt_iff₀ hmargin).mp ((le_max_right _ _).trans_lt hR)
    nlinarith
  let s : Finset ℝ := (S.finite_inter_Icc (-R) R).toFinset
  let sC : Finset ℂ := s.image Complex.ofReal
  let mC : ℂ → ℕ := fun z => m z.re
  have hmem {x : ℝ} : x ∈ s ↔ x ∈ S.carrier ∧ -R ≤ x ∧ x ≤ R := by
    simp [s]
  have hnodes : ∀ z ∈ sC, ‖z‖ ≤ R := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_le] using (hmem.mp hx).2
  have hjetC : ∀ z ∈ sC, ∀ j < mC z, iteratedDeriv j G z = 0 := by
    intro z hz j hj
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    exact hjets x (hmem.mp hx).1 j hj
  have hzeroC : ∀ z ∈ sC, z = 0 → mC z = 0 := by
    intro z hz hz0
    by_contra hm
    have h := hjetC z hz 0 (Nat.pos_of_ne_zero hm)
    simp only [iteratedDeriv_zero, hz0] at h
    exact hzero h
  have hfilter (t : ℝ) (ht : t ≤ R) : s.filter (fun x => |x| < t) =
      (S.finite_inter_Ioo (-t) t).toFinset := by
    ext x
    simp only [Finset.mem_filter, hmem, Set.Finite.mem_toFinset, mem_inter_iff,
      mem_Ioo, abs_lt]
    constructor
    · rintro ⟨⟨hx, _, _⟩, hlo, hhi⟩
      exact ⟨hx, hlo, hhi⟩
    · rintro ⟨hx, hlo, hhi⟩
      exact ⟨⟨hx, by linarith, hhi.le.trans ht⟩, hlo, hhi⟩
  have hcountsC : ∀ t ∈ Icc r₀ R,
      2 * d * t ≤ ∑ z ∈ sC, if ‖z‖ < t then (mC z : ℝ) else 0 := by
    intro t ht
    have heq : (∑ z ∈ sC, if ‖z‖ < t then (mC z : ℝ) else 0) =
        (weightedRealZeroCount S m t : ℝ) := by
      rw [Finset.sum_image (Complex.ofReal_injective.injOn)]
      simp only [mC, Complex.ofReal_re, Complex.norm_real, Real.norm_eq_abs]
      rw [← Finset.sum_filter, hfilter t ht.2]
      simp only [weightedRealZeroCount, Nat.cast_sum]
    rw [heq]
    exact hcounts t ht.1
  have hlower := finite_log_sum_ge_of_weighted_radial_counts sC mC hr₀ hrR
    hnodes hzeroC hcountsC
  have hupper := finite_jet_zero_log_sum_le_of_exponentialType sC mC hG hτ hM hRpos
    htype hreal hzero hnodes hjetC
  have hboth := hlower.trans hupper
  have hmul : 2 * τ * R / π = (2 * τ / π) * R := by ring
  rw [hmul] at hboth
  nlinarith

/-- Strict lower uniform density supplies a strict centered radial count after
shrinking each half-open source window by one unit at each end. The strict
margin absorbs these boundary losses. -/
theorem exists_radial_count_lower_bound_of_uniformLowerDensityGT
    (S : LocallyFiniteCarrier) {c : ℝ} (hD : UniformLowerDensityGT S c) :
    ∃ d > c, ∃ r₀ > 0, ∀ R ≥ r₀,
      2 * d * R ≤ (weightedRealZeroCount S (fun _ => 1) R : ℝ) := by
  classical
  obtain ⟨ε, hε, L₀, hL₀, hbound⟩ := hD
  refine ⟨c + ε / 2, by linarith, max (L₀ + 2) (2 * (c + ε) / ε + 1),
    lt_of_lt_of_le (by linarith) (le_max_left _ _), ?_⟩
  intro R hR
  have hRL : L₀ + 2 ≤ R := (le_max_left _ _).trans hR
  have hRE : 2 * (c + ε) / ε + 1 ≤ R := (le_max_right _ _).trans hR
  have hεR : 2 * (c + ε) ≤ ε * R := by
    have := (div_le_iff₀ hε).mp (show 2 * (c + ε) / ε ≤ R by linarith)
    nlinarith
  have hcard : windowCount S (-R + 1) (2 * R - 2) ≤
      weightedRealZeroCount S (fun _ => 1) R := by
    have hsubset : S.carrier ∩ Ico (-R + 1) (-R + 1 + (2 * R - 2)) ⊆
        S.carrier ∩ Ioo (-R) R := by
      intro x hx
      exact ⟨hx.1, by linarith [hx.2.1], by linarith [hx.2.2]⟩
    have := Set.ncard_le_ncard hsubset (S.finite_inter_Ioo (-R) R)
    simpa [windowCount, weightedRealZeroCount,
      Set.ncard_eq_toFinset_card _ (S.finite_inter_Ioo (-R) R)] using this
  have hwindow := hbound (2 * R - 2) (by linarith) (-R + 1)
  have hcast : (windowCount S (-R + 1) (2 * R - 2) : ℝ) ≤
      (weightedRealZeroCount S (fun _ => 1) R : ℝ) := by exact_mod_cast hcard
  nlinarith

/-- Ordinary lower uniform Beurling density strictly above `τ / π` excludes a
nonzero-at-origin entire function of type at most `τ` that vanishes on the
carrier. The numerical density is the repository's exact half-open density. -/
theorem not_real_zero_lowerUniformBeurlingDensity_gt_type
    {G : ℂ → ℂ} {τ M : ℝ} (S : LocallyFiniteCarrier)
    (hG : Differentiable ℂ G) (hτ : 0 ≤ τ) (hM : 0 < M)
    (htype : ∀ ε > 0, ∃ C > 0, ∀ z,
      ‖G z‖ ≤ C * Real.exp ((τ + ε) * ‖z‖))
    (hreal : ∀ x : ℝ, ‖G x‖ ≤ M) (hzero : G 0 ≠ 0)
    (hzeros : ∀ x ∈ S.carrier, G (x : ℂ) = 0)
    (hD : ENNReal.ofReal (τ / π) < lowerUniformBeurlingDensity S) : False := by
  have hpred := (uniformLowerDensityGT_iff_lt_lowerUniformBeurlingDensity S
    (div_nonneg hτ pi_pos.le)).mpr hD
  obtain ⟨d, hd, r₀, hr₀, hcount⟩ :=
    exists_radial_count_lower_bound_of_uniformLowerDensityGT S hpred
  apply not_weighted_real_zero_density_gt_type S (fun _ => 1) hG hτ hM htype hreal hzero
    (fun x hx j hj => ?_) hd hr₀ hcount
  have hj0 : j = 0 := by omega
  simpa only [hj0, iteratedDeriv_zero] using hzeros x hx

end MeyerGeneralProblem
