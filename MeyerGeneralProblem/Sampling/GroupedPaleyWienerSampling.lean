module

public import MeyerGeneralProblem.Sampling.GroupedPaleyWiener
public import MeyerGeneralProblem.Sampling.GroupedBiorthogonal
public import MeyerGeneralProblem.Sampling.GroupedExponentialUpper
public import MeyerGeneralProblem.Sampling.PaleyWienerRepresentative

@[expose] public section

/-!
# Genuine grouped sampling of Paley–Wiener representatives

The upper estimate is the Hilbert dual of the proved grouped exponential
synthesis estimate. Actual negative-Fourier divided differences equal those
Hilbert coefficients. Bounded nonnegative finite sums prove summability;
the class-uniform localization lower estimate then applies to the genuine
entire representative, with the exact angular bandwidth and Plancherel norm.
-/

namespace MeyerGeneralProblem

noncomputable section


open MeasureTheory Set Filter ComplexConjugate
open scoped Topology BigOperators ENNReal FourierTransform

/-- Finite Hilbert synthesis bounds give the same squared analysis bound.
This is applied below only after the actual grouped synthesis estimate has
been proved, and its conclusion concerns the original family coefficients. -/
theorem finite_analysis_bound_of_synthesis_bound
    {ι H : Type*} [Fintype ι] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (v : ι → H) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ c : ι → ℂ, ‖∑ i, c i • v i‖ ^ 2 ≤ B * ∑ i, ‖c i‖ ^ 2)
    (y : H) : (∑ i, ‖inner ℂ (v i) y‖ ^ 2) ≤ B * ‖y‖ ^ 2 := by
  let c : ι → ℂ := fun i => inner ℂ (v i) y
  let E : ℝ := ∑ i, ‖c i‖ ^ 2
  have hE : 0 ≤ E := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hpair : inner ℂ (∑ i, c i • v i) y = (E : ℂ) := by
    simp only [sum_inner, inner_smul_left, c, E, Complex.ofReal_sum,
      Complex.ofReal_pow, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  have hcs := norm_inner_le_norm (𝕜 := ℂ) (∑ i, c i • v i) y
  rw [hpair, Complex.norm_real, Real.norm_of_nonneg hE] at hcs
  have hsq := (sq_le_sq₀ hE (by positivity)).mpr hcs
  rw [mul_pow] at hsq
  have hmul := mul_le_mul_of_nonneg_right (hbound c) (sq_nonneg ‖y‖)
  change E ≤ B * ‖y‖ ^ 2
  by_cases hz : E = 0
  · rw [hz]; positivity
  · have hEpos : 0 < E := lt_of_le_of_ne hE (Ne.symm hz)
    nlinarith

/-- The actual grouped window vectors have a uniform finite analysis bound,
depending only on the maximum group size, window radius and separation of
different canonical hulls. No density or within-group separation is needed. -/
theorem exists_uniform_canonical_grouped_window_analysis_bound
    (q : ℕ) {a d : ℝ} (ha : 0 ≤ a) (hd : 0 < d) :
    ∃ B > 0, ∀ (S : LocallyFiniteCarrier) (horder : BoundedClusterOrder S d q)
      (n : ℕ) (groups : Fin n ↪ CanonicalClusterIndex S d) (y : FourierWindowSpace a),
      (∑ g, ∑ j : Fin (horder.clusterSize (groups g)),
        ‖inner ℂ (groupedFourierWindowVector a (horder.realClusterNode (groups g)) j) y‖ ^ 2) ≤
          B * ‖y‖ ^ 2 := by
  obtain ⟨B, hB, hupper⟩ := exists_groupedExponentialInitial_uniform_upper q ha hd
  refine ⟨B, hB, ?_⟩
  intro S horder n groups y
  let v : (Σ g : Fin n, Fin (horder.clusterSize (groups g))) → FourierWindowSpace a :=
    fun x => groupedFourierWindowVector a (horder.realClusterNode (groups x.1)) x.2
  have hb (c : (Σ g : Fin n, Fin (horder.clusterSize (groups g))) → ℂ) :
      ‖∑ i, c i • v i‖ ^ 2 ≤ B * ∑ i, ‖c i‖ ^ 2 := by
    change ‖∑ i, c i • continuousFourierWindowVector a
      (groupedExponentialInitial (horder.realClusterNode (groups i.1)) i.2)
      (continuous_groupedExponentialInitial _ _)‖ ^ 2 ≤ _
    rw [continuousFourierWindowVector_sum_norm_sq]
    simpa only [Fintype.sum_sigma] using hupper n
      (fun g => horder.clusterSize (groups g))
      (fun g => horder.clusterSize_pos (groups g))
      (fun g => horder.clusterSize_le (groups g))
      (fun g => horder.realClusterNode (groups g))
      (fun g => horder.clusterLower (groups g)) (fun g => horder.clusterUpper (groups g))
      (fun g => horder.realClusterNode_mem_hull (groups g))
      (fun g h hgh x hx z hz => horder.cluster_hulls_separated hd
        (groups.injective.ne hgh) hx hz) (fun g j => c ⟨g, j⟩)
  simpa only [Fintype.sum_sigma] using finite_analysis_bound_of_synthesis_bound v hB.le hb y

/-- Actual Fourier divided-difference samples of an arbitrary window L2
vector are square summable and satisfy a class-uniform upper estimate.
Summability is proved from bounded finite sums, not supplied as an input. -/
theorem exists_uniform_canonical_fourierWindow_sampling_upper
    (q : ℕ) {a d : ℝ} (ha : 0 ≤ a) (hd : 0 < d) :
    ∃ B > 0, ∀ (S : LocallyFiniteCarrier) (horder : BoundedClusterOrder S d q)
      (y : FourierWindowSpace a),
      Summable (fun C : CanonicalClusterIndex S d =>
        ∑ j : Fin (horder.clusterSize C),
          ‖analyticDividedDifference (finiteNodeSequence (horder.realClusterNode C)) j
            (𝓕 (fourierWindowKernel a y))‖ ^ 2) ∧
      (∑' C : CanonicalClusterIndex S d, ∑ j : Fin (horder.clusterSize C),
        ‖analyticDividedDifference (finiteNodeSequence (horder.realClusterNode C)) j
          (𝓕 (fourierWindowKernel a y))‖ ^ 2) ≤ B * ‖y‖ ^ 2 := by
  classical
  obtain ⟨B, hB, hbound⟩ := exists_uniform_canonical_grouped_window_analysis_bound q ha hd
  refine ⟨B, hB, ?_⟩
  intro S horder y
  let e : CanonicalClusterIndex S d → ℝ := fun C => ∑ j : Fin (horder.clusterSize C),
    ‖analyticDividedDifference (finiteNodeSequence (horder.realClusterNode C)) j
      (𝓕 (fourierWindowKernel a y))‖ ^ 2
  have he (C) : 0 ≤ e C := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hfinite (s : Finset (CanonicalClusterIndex S d)) :
      ∑ C ∈ s, e C ≤ B * ‖y‖ ^ 2 := by
    let E := (Fintype.equivFin s).symm
    let groups : Fin (Fintype.card s) ↪ CanonicalClusterIndex S d :=
      ⟨fun i => (E i).val, Subtype.val_injective.comp E.injective⟩
    calc
      _ = ∑ C : s, e C.val := (Finset.sum_coe_sort s e).symm
      _ = ∑ i : Fin (Fintype.card s), e (groups i) := (E.sum_comp (fun C : s => e C.val)).symm
      _ ≤ B * ‖y‖ ^ 2 := by
        simp only [e, analyticDividedDifference_fourierWindowKernel a _
          (horder.realClusterNode_strictMono _).injective]
        exact hbound S horder _ groups y
  exact ⟨summable_of_sum_le he hfinite, Real.tsum_le_of_sum_le he hfinite⟩

/-- The nonnegative squared-energy integral of an actual L2 vector is its
squared Hilbert norm, with no finite-integral convention left implicit. -/
theorem lintegral_norm_sq_eq_ofReal_L2_norm_sq
    {α : Type*} [MeasurableSpace α] {μ : Measure α} (g : Lp ℂ 2 μ) :
    (∫⁻ x, ENNReal.ofReal (‖g x‖ ^ 2) ∂μ) = ENNReal.ofReal (‖g‖ ^ 2) := by
  have hi : Integrable (fun x => ‖g x‖ ^ 2) μ := by
    convert (L2.integrable_inner g g).re using 1
    ext x
    exact norm_sq_eq_re_inner (𝕜 := ℂ) (g x)
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun x => sq_nonneg _))]
  congr 1
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), L2.inner_def,
    ← integral_re (L2.integrable_inner g g)]
  exact integral_congr_ae (Eventually.of_forall (fun x => norm_sq_eq_re_inner (𝕜 := ℂ) (g x)))

/-- An actual square-integrable function has the same nonnegative squared
energy as its genuine L2 class. -/
theorem lintegral_norm_sq_eq_ofReal_toLp_norm_sq
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℂ} (hf : MemLp f 2 μ) :
    (∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2) ∂μ) = ENNReal.ofReal (‖hf.toLp‖ ^ 2) := by
  rw [← lintegral_norm_sq_eq_ofReal_L2_norm_sq]
  apply lintegral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx]

/-- Extending a window vector by zero preserves its exact L2 norm. -/
theorem fourierWindowKernel_toLp_norm (a : ℝ) (y : FourierWindowSpace a) :
    ‖(memLp_fourierWindowKernel a y).toLp‖ = ‖y‖ := by
  rw [Lp.norm_toLp, Lp.norm_def]
  congr 1
  exact eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Icc

/-- Genuine two-sided grouped Paley–Wiener sampling on arbitrary window L2
frequency data. The sampled function is its actual classical Fourier
integral. Both constants precede the carrier and function, and square
summability is part of the conclusion. The strict enlarged angular bandwidth
remains below `π N / B₀`, exactly as required by the block-count class. -/
theorem groupedPaleyWiener_sampling_window
    {q N : ℕ} {d B₀ Ω Ω' : ℝ} (hd : 0 < d) (hΩ : 0 ≤ Ω)
    (hΩΩ' : Ω < Ω') (hgap : Ω' / Real.pi < (N : ℝ) / B₀) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧
      ∀ (Λ : TwoSidedCarrier) (hcluster : BoundedClusterOrder Λ.toLocallyFinite d q),
      (∀ t R, 0 < R → (N : ℝ) * ((⌊2 * R / B₀⌋ : ℝ) - 2) ≤
        ((Λ.toLocallyFinite.carrier ∩ Ioo (t - R) (t + R)).ncard : ℝ)) →
      ∀ y : FourierWindowSpace (Ω / (2 * Real.pi)),
      Summable (fun C : CanonicalClusterIndex Λ.toLocallyFinite d =>
        ∑ j : Fin (hcluster.clusterSize C),
          ‖analyticDividedDifference (finiteNodeSequence (hcluster.realClusterNode C)) j
            (𝓕 (fourierWindowKernel (Ω / (2 * Real.pi)) y))‖ ^ 2) ∧
      A * ‖y‖ ^ 2 ≤
        (∑' C : CanonicalClusterIndex Λ.toLocallyFinite d, ∑ j : Fin (hcluster.clusterSize C),
          ‖analyticDividedDifference (finiteNodeSequence (hcluster.realClusterNode C)) j
            (𝓕 (fourierWindowKernel (Ω / (2 * Real.pi)) y))‖ ^ 2) ∧
      (∑' C : CanonicalClusterIndex Λ.toLocallyFinite d, ∑ j : Fin (hcluster.clusterSize C),
        ‖analyticDividedDifference (finiteNodeSequence (hcluster.realClusterNode C)) j
          (𝓕 (fourierWindowKernel (Ω / (2 * Real.pi)) y))‖ ^ 2) ≤ B * ‖y‖ ^ 2 := by
  let a := Ω / (2 * Real.pi)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  obtain ⟨L, hL, hlower⟩ := exists_uniform_canonical_bernstein_lintegral_bound_of_block_count
    (q := q) hd hΩ hΩΩ' hgap
  obtain ⟨B, hB, hupper⟩ := exists_uniform_canonical_fourierWindow_sampling_upper q ha hd
  refine ⟨L⁻¹, B, inv_pos.mpr hL, hB, ?_⟩
  intro Λ hcluster hblock y
  obtain ⟨hsum, hu⟩ := hupper Λ.toLocallyFinite hcluster y
  refine ⟨hsum, ?_, hu⟩
  let G : ℝ → ℂ := fourierWindowKernel a y
  obtain ⟨E, hE, hreal, hbounded, htype, _hae, hE2, hnorm⟩ :=
    exists_bandLimited_L2_entire_representative (memLp_fourierWindowKernel a y) ha
      (support_fourierWindowKernel_subset a y)
  have hscale : 2 * Real.pi * a = Ω := by dsimp [a]; field_simp
  rw [hscale] at htype
  rw [fourierWindowKernel_toLp_norm] at hnorm
  have h := hlower Λ hcluster hblock E hE htype hbounded
  rw [lintegral_norm_sq_eq_ofReal_toLp_norm_sq hE2, hnorm] at h
  simp_rw [hreal] at h
  have he (C : CanonicalClusterIndex Λ.toLocallyFinite d) :
      0 ≤ ∑ j : Fin (hcluster.clusterSize C),
        ‖analyticDividedDifference (finiteNodeSequence (hcluster.realClusterNode C)) j
          (𝓕 (fourierWindowKernel a y))‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  rw [← ENNReal.ofReal_tsum_of_nonneg he hsum, ← ENNReal.ofReal_mul hL.le] at h
  have hrealBound := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hL.le (tsum_nonneg he))).mp h
  rw [inv_mul_eq_div]
  exact (div_le_iff₀ hL).mpr (by simpa only [mul_comm] using hrealBound)

/-- Every whole-line L2 class supported almost everywhere in the band is
the zero extension of a genuine window vector, with its exact original norm. -/
theorem exists_fourierWindowVector_of_bandLimited_L2
    (g : Lp ℂ 2 (volume : Measure ℝ)) (a : ℝ)
    (hs : ∀ᵐ t : ℝ, t ∉ Icc (-a) a → g t = 0) :
    ∃ y : FourierWindowSpace a,
      fourierWindowKernel a y =ᵐ[volume] (g : ℝ → ℂ) ∧ ‖y‖ = ‖g‖ := by
  let hy : MemLp (g : ℝ → ℂ) 2 (volume.restrict (Icc (-a) a)) :=
    (Lp.memLp g).restrict (Icc (-a) a)
  let y : FourierWindowSpace a := hy.toLp
  have hyae : (y : ℝ → ℂ) =ᵐ[volume.restrict (Icc (-a) a)] (g : ℝ → ℂ) := hy.coeFn_toLp
  have hkernel : fourierWindowKernel a y =ᵐ[volume] (g : ℝ → ℂ) := by
    have hin := (ae_restrict_iff' measurableSet_Icc).mp hyae
    filter_upwards [hin, hs] with t ht hz
    by_cases hm : t ∈ Icc (-a) a
    · exact (indicator_of_mem hm _).trans (ht hm)
    · exact (indicator_of_notMem hm _).trans (hz hm).symm
  refine ⟨y, hkernel, ?_⟩
  have hclass : (memLp_fourierWindowKernel a y).toLp = g :=
    Lp.ext ((memLp_fourierWindowKernel a y).coeFn_toLp.trans hkernel)
  rw [← fourierWindowKernel_toLp_norm a y, hclass]

/-- The class-uniform grouped Paley–Wiener sampling theorem for arbitrary
whole-line L2 frequency classes with almost-everywhere compact support.
The samples use the actual Fourier integral, not evaluations of a chosen L2
representative of its transform. The squared norm bounds and summability are
all conclusions of the geometric and bandwidth assumptions alone. -/
theorem groupedPaleyWiener_sampling
    {q N : ℕ} {d B₀ Ω Ω' : ℝ} (hd : 0 < d) (hΩ : 0 ≤ Ω)
    (hΩΩ' : Ω < Ω') (hgap : Ω' / Real.pi < (N : ℝ) / B₀) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧
      ∀ (Λ : TwoSidedCarrier) (hcluster : BoundedClusterOrder Λ.toLocallyFinite d q),
      (∀ t R, 0 < R → (N : ℝ) * ((⌊2 * R / B₀⌋ : ℝ) - 2) ≤
        ((Λ.toLocallyFinite.carrier ∩ Ioo (t - R) (t + R)).ncard : ℝ)) →
      ∀ g : Lp ℂ 2 (volume : Measure ℝ),
      (∀ᵐ t : ℝ, t ∉ Icc (-Ω / (2 * Real.pi)) (Ω / (2 * Real.pi)) → g t = 0) →
      Summable (fun C : CanonicalClusterIndex Λ.toLocallyFinite d =>
        ∑ j : Fin (hcluster.clusterSize C),
          ‖analyticDividedDifference (finiteNodeSequence (hcluster.realClusterNode C)) j
            (𝓕 (g : ℝ → ℂ))‖ ^ 2) ∧
      A * ‖g‖ ^ 2 ≤
        (∑' C : CanonicalClusterIndex Λ.toLocallyFinite d, ∑ j : Fin (hcluster.clusterSize C),
          ‖analyticDividedDifference (finiteNodeSequence (hcluster.realClusterNode C)) j
            (𝓕 (g : ℝ → ℂ))‖ ^ 2) ∧
      (∑' C : CanonicalClusterIndex Λ.toLocallyFinite d, ∑ j : Fin (hcluster.clusterSize C),
        ‖analyticDividedDifference (finiteNodeSequence (hcluster.realClusterNode C)) j
          (𝓕 (g : ℝ → ℂ))‖ ^ 2) ≤ B * ‖g‖ ^ 2 := by
  obtain ⟨A, B, hA, hB, hbound⟩ := groupedPaleyWiener_sampling_window
    (q := q) hd hΩ hΩΩ' hgap
  refine ⟨A, B, hA, hB, ?_⟩
  intro Λ hcluster hblock g hs
  obtain ⟨y, hyae, hynorm⟩ := exists_fourierWindowVector_of_bandLimited_L2
    g (Ω / (2 * Real.pi)) (by simpa only [neg_div] using hs)
  have hfourier : (𝓕 (fourierWindowKernel (Ω / (2 * Real.pi)) y) : ℝ → ℂ) =
      𝓕 (g : ℝ → ℂ) := funext (Real.fourier_congr_ae hyae)
  simpa only [hfourier, hynorm] using hbound Λ hcluster hblock y

set_option maxHeartbeats 2000000 in
/-- The same genuine sampling theorem for an actual square-integrable
frequency function. Fourier values and all divided differences are unchanged
by passage to its L2 class; the support hypothesis is almost-everywhere. -/
theorem groupedPaleyWiener_sampling_function
    {q N : ℕ} {d B₀ Ω Ω' : ℝ} (hd : 0 < d) (hΩ : 0 ≤ Ω)
    (hΩΩ' : Ω < Ω') (hgap : Ω' / Real.pi < (N : ℝ) / B₀) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧
      ∀ (Λ : TwoSidedCarrier) (hcluster : BoundedClusterOrder Λ.toLocallyFinite d q),
      (∀ t R, 0 < R → (N : ℝ) * ((⌊2 * R / B₀⌋ : ℝ) - 2) ≤
        ((Λ.toLocallyFinite.carrier ∩ Ioo (t - R) (t + R)).ncard : ℝ)) →
      ∀ (G : ℝ → ℂ) (hG : MemLp G 2),
      (∀ᵐ t : ℝ, t ∉ Icc (-Ω / (2 * Real.pi)) (Ω / (2 * Real.pi)) → G t = 0) →
      Summable (fun C : CanonicalClusterIndex Λ.toLocallyFinite d =>
        ∑ j : Fin (hcluster.clusterSize C),
          ‖analyticDividedDifference (finiteNodeSequence (hcluster.realClusterNode C)) j (𝓕 G)‖ ^ 2) ∧
      A * ‖(hG.toLp G : Lp ℂ 2 (volume : Measure ℝ))‖ ^ 2 ≤
        (∑' C : CanonicalClusterIndex Λ.toLocallyFinite d, ∑ j : Fin (hcluster.clusterSize C),
          ‖analyticDividedDifference (finiteNodeSequence (hcluster.realClusterNode C)) j (𝓕 G)‖ ^ 2) ∧
      (∑' C : CanonicalClusterIndex Λ.toLocallyFinite d, ∑ j : Fin (hcluster.clusterSize C),
        ‖analyticDividedDifference (finiteNodeSequence (hcluster.realClusterNode C)) j (𝓕 G)‖ ^ 2) ≤
          B * ‖(hG.toLp G : Lp ℂ 2 (volume : Measure ℝ))‖ ^ 2 := by
  obtain ⟨A, B, hA, hB, hbound⟩ := groupedPaleyWiener_sampling (q := q) hd hΩ hΩΩ' hgap
  refine ⟨A, B, hA, hB, ?_⟩
  intro Λ hcluster hblock G hG hs
  have hsupport : ∀ᵐ t : ℝ,
      t ∉ Icc (-Ω / (2 * Real.pi)) (Ω / (2 * Real.pi)) →
        ((hG.toLp G) : Lp ℂ 2 (volume : Measure ℝ)) t = 0 := by
    filter_upwards [hG.coeFn_toLp, hs] with t ht hs
    simpa only [ht] using hs
  have hfourier : (𝓕 ((hG.toLp G) : ℝ → ℂ) : ℝ → ℂ) = 𝓕 G :=
    funext (Real.fourier_congr_ae hG.coeFn_toLp)
  simpa only [hfourier] using hbound Λ hcluster hblock (hG.toLp G) hsupport

/-- Genuine grouped zeros force a band-limited L2 frequency class to vanish.
This is a consequence of the proved sampling bound, not a spectral or
uniqueness premise used in its construction. -/
theorem bandLimited_eq_zero_of_groupedZeros
    {q N : ℕ} {d B₀ Ω Ω' : ℝ} (hd : 0 < d) (hΩ : 0 ≤ Ω)
    (hΩΩ' : Ω < Ω') (hgap : Ω' / Real.pi < (N : ℝ) / B₀)
    (Λ : TwoSidedCarrier) (hcluster : BoundedClusterOrder Λ.toLocallyFinite d q)
    (hblock : ∀ t R, 0 < R → (N : ℝ) * ((⌊2 * R / B₀⌋ : ℝ) - 2) ≤
      ((Λ.toLocallyFinite.carrier ∩ Ioo (t - R) (t + R)).ncard : ℝ))
    (g : Lp ℂ 2 (volume : Measure ℝ))
    (hs : ∀ᵐ t : ℝ, t ∉ Icc (-Ω / (2 * Real.pi)) (Ω / (2 * Real.pi)) → g t = 0)
    (hzero : ∀ (C : CanonicalClusterIndex Λ.toLocallyFinite d) (j : Fin (hcluster.clusterSize C)),
      analyticDividedDifference (finiteNodeSequence (hcluster.realClusterNode C)) j
        (𝓕 (g : ℝ → ℂ)) = 0) : g = 0 := by
  obtain ⟨A, _B, hA, _hB, hbound⟩ := groupedPaleyWiener_sampling (q := q) hd hΩ hΩΩ' hgap
  have h := (hbound Λ hcluster hblock g hs).2.1
  simp only [hzero, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    Finset.sum_const_zero, tsum_zero] at h
  have hnorm : ‖g‖ ^ 2 ≤ 0 := by
    by_contra hn
    exact (not_lt_of_ge h) (mul_pos hA (lt_of_not_ge hn))
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg g])

end

end MeyerGeneralProblem
