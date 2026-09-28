module

public import MeyerGeneralProblem.Sampling.GroupedPaleyWienerSampling
public import MeyerGeneralProblem.Sampling.FourierBandCutoff
public import MeyerGeneralProblem.Sampling.LocalSobolev

@[expose] public section

/-!
# Actual grouped Sobolev sampling and spectral-gap composition

The high-frequency tail is not band limited. Its grouped samples are instead
controlled by genuine Hermite–Genocchi averaging and separated local Sobolev
estimates. These estimates use the fixed maximum group size, not the final
derivative order, and impose no minimum gap within a group.
-/

namespace MeyerGeneralProblem

noncomputable section

open MeasureTheory Set Filter ComplexConjugate
open scoped Topology BigOperators ENNReal FourierTransform SchwartzMap

/-- Squared pointwise norm of an actual L2 function is integrable. -/
theorem integrable_norm_sq_of_memLp_complex {f : ℝ → ℂ} (hf : MemLp f 2) :
    Integrable (fun x => ‖f x‖ ^ 2) := by
  have hg : Integrable (fun x => ‖(hf.toLp : Lp ℂ 2 volume) x‖ ^ 2) := by
    convert (L2.integrable_inner (hf.toLp) (hf.toLp)).re using 1
    ext x
    exact norm_sq_eq_re_inner (𝕜 := ℂ) _
  apply hg.congr
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx]

/-- Actual L2 energy equals the squared norm of its associated Hilbert class. -/
theorem integral_norm_sq_eq_toLp_norm_sq_complex {f : ℝ → ℂ} (hf : MemLp f 2) :
    (∫ x : ℝ, ‖f x‖ ^ 2) = ‖hf.toLp‖ ^ 2 := by
  have h := lintegral_norm_sq_eq_ofReal_toLp_norm_sq hf
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_norm_sq_of_memLp_complex hf)
    (Eventually.of_forall (fun x => sq_nonneg _))] at h
  exact (ENNReal.ofReal_eq_ofReal_iff
    (integral_nonneg (fun x => sq_nonneg _)) (sq_nonneg _)).mp h

/-- Separated point sampling on the whole line follows from the proved
finite local Sobolev estimate and genuine global L2 energies. -/
theorem sum_norm_sq_le_globalSobolev
    {ι : Type*} [Fintype ι] (x : ι → ℝ) (f f' : ℝ → ℂ)
    (hf : ∀ t, HasDerivAt f (f' t) t) (hf' : Continuous f')
    (hL2 : MemLp f 2) (hL2' : MemLp f' 2) {d : ℝ} (hd : 0 < d)
    (hsep : ∀ i j, i ≠ j → d ≤ |x i - x j|) :
    (∑ i, ‖f (x i)‖ ^ 2) ≤
      2 * d⁻¹ * ‖hL2.toLp‖ ^ 2 + d * ‖hL2'.toLp‖ ^ 2 := by
  obtain ⟨lo, hlo⟩ := (Set.finite_range x).bddBelow
  obtain ⟨hi, hhi⟩ := (Set.finite_range x).bddAbove
  have h := sum_norm_sq_le_localSobolev x f f' hf hf' hd hsep
    (fun i => hlo (Set.mem_range_self i)) (fun i => hhi (Set.mem_range_self i))
  apply h.trans
  rw [← integral_norm_sq_eq_toLp_norm_sq_complex hL2,
    ← integral_norm_sq_eq_toLp_norm_sq_complex hL2']
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left
      (setIntegral_le_integral (integrable_norm_sq_of_memLp_complex hL2)
        (Eventually.of_forall (fun t => sq_nonneg _))) (by positivity)
  · exact mul_le_mul_of_nonneg_left
      (setIntegral_le_integral (integrable_norm_sq_of_memLp_complex hL2')
        (Eventually.of_forall (fun t => sq_nonneg _))) hd.le

/-- Hermite–Genocchi averaging preserves a common bound on the sum of
squared virtual-node data. All virtual nodes remain in their original
hulls, including when nodes collapse. -/
theorem sum_norm_hermiteGenocchiIntegral_sq_le
    {n : ℕ} (nodes : Fin n → ℕ → ℝ) (order : ℕ)
    (g : ℝ → ℂ) (hg : Continuous g) (L U : Fin n → ℝ)
    (hnodes : ∀ i j, j ≤ order → nodes i j ∈ Icc (L i) (U i))
    {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ x : Fin n → ℝ, (∀ i, x i ∈ Icc (L i) (U i)) →
      (∑ i, ‖g (x i)‖ ^ 2) ≤ B) :
    (∑ i, ‖hermiteGenocchiIntegral (nodes i) order g‖ ^ 2) ≤ B := by
  let v : Fin n → ℂ := fun i => hermiteGenocchiIntegral (nodes i) order g
  have hsynth (c : Fin n → ℂ) : ‖∑ i, c i • v i‖ ^ 2 ≤ B * ∑ i, ‖c i‖ ^ 2 := by
    have h := integral_hermiteGenocchi_synthesis_sq_le nodes order
      (fun _ s _ => g s) c (fun _ => hg.comp continuous_fst) L U hnodes
      (lo := 0) (hi := 1) (B := B * ∑ i, ‖c i‖ ^ 2) (by
        intro x hx
        have hnorm : ‖∑ i, c i * g (x i)‖ ≤ ∑ i, ‖c i‖ * ‖g (x i)‖ := by
          simpa only [norm_mul] using norm_sum_le Finset.univ (fun i => c i * g (x i))
        have hsq := (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg (fun _ _ => by positivity))).mpr hnorm
        have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => ‖c i‖) (fun i => ‖g (x i)‖)
        have hfinal := hsq.trans (hcs.trans
          (mul_le_mul_of_nonneg_left (hbound x hx) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))))
        simpa only [integral_const, measureReal_restrict_apply_univ,
          Real.volume_real_Icc_of_le (by norm_num : (0 : ℝ) ≤ 1), sub_zero,
          smul_eq_mul, one_mul, mul_comm B] using hfinal)
    simpa [v, smul_eq_mul] using h
  have h := finite_analysis_bound_of_synthesis_bound v hB hsynth (1 : ℂ)
  simpa [RCLike.inner_apply] using h

/-- Fixed-order grouped sampling of a genuine Sobolev function uses only
its derivatives of orders j and j+1. Repeated nodes are allowed; the constant
comes from separated virtual nodes, never from an internal divided difference. -/
theorem sum_norm_analyticDividedDifference_sq_le_globalSobolev
    {n : ℕ} (nodes : Fin n → ℕ → ℝ) (order : ℕ) (L U : Fin n → ℝ)
    (hnodes : ∀ i j, j ≤ order → nodes i j ∈ Icc (L i) (U i))
    {d : ℝ} (hd : 0 < d)
    (hsep : ∀ i j, i ≠ j → ∀ x ∈ Icc (L i) (U i), ∀ y ∈ Icc (L j) (U j), d ≤ |x - y|)
    {f : ℝ → ℂ} (hf : ContDiff ℝ (order + 1) f)
    (hL2 : MemLp (iteratedDeriv order f) 2) (hL2' : MemLp (iteratedDeriv (order + 1) f) 2) :
    (∑ i, ‖analyticDividedDifference (nodes i) order f‖ ^ 2) ≤
      2 * d⁻¹ * ‖hL2.toLp‖ ^ 2 + d * ‖hL2'.toLp‖ ^ 2 := by
  have hsmall : ContDiff ℝ order f := hf.of_le (by exact_mod_cast Nat.le_succ order)
  simp_rw [analyticDividedDifference_eq_hermiteGenocchi _ _ hsmall]
  apply sum_norm_hermiteGenocchiIntegral_sq_le nodes order _
    (hsmall.continuous_iteratedDeriv' order) L U hnodes (by positivity)
  intro x hx
  apply sum_norm_sq_le_globalSobolev x _ _ ?_
    (hf.continuous_iteratedDeriv' (order + 1)) hL2 hL2' hd
    (fun i j hij => hsep i j hij (x i) (hx i) (x j) (hx j))
  intro t
  rw [iteratedDeriv_succ]
  exact (hf.differentiable_iteratedDeriv order (by exact_mod_cast Nat.lt_succ_self order) t).hasDerivAt

/-- All actual prefixes in finitely many groups satisfy a genuine Sobolev
sampling bound. Different group sizes are handled by exact prefix agreement
and nonnegative zero-free padding of the node sequence inside its own hull. -/
theorem finite_grouped_sobolev_sampling_upper
    {n q : ℕ} (r : Fin n → ℕ) (hrpos : ∀ i, 0 < r i) (hrq : ∀ i, r i ≤ q)
    (nodes : (i : Fin n) → Fin (r i) → ℝ) (L U : Fin n → ℝ)
    (hnodes : ∀ i j, nodes i j ∈ Icc (L i) (U i))
    {d : ℝ} (hd : 0 < d)
    (hsep : ∀ i j, i ≠ j → ∀ x ∈ Icc (L i) (U i), ∀ y ∈ Icc (L j) (U j), d ≤ |x - y|)
    {f : ℝ → ℂ} (hf : ContDiff ℝ q f)
    (hL2 : ∀ j ≤ q, MemLp (iteratedDeriv j f) 2) :
    (∑ i, ∑ j : Fin (r i),
      ‖analyticDividedDifference (finiteNodeSequence (nodes i)) j f‖ ^ 2) ≤
      ∑ j : Fin q, (2 * d⁻¹ * ‖(hL2 j j.isLt.le).toLp‖ ^ 2 +
        d * ‖(hL2 (j + 1) (by omega)).toLp‖ ^ 2) := by
  let N : Fin n → ℕ → ℝ := fun i k =>
    if h : k < r i then nodes i ⟨k, h⟩ else nodes i ⟨0, hrpos i⟩
  have hN (i : Fin n) (k : ℕ) : N i k ∈ Icc (L i) (U i) := by
    dsimp [N]
    split <;> apply hnodes
  have hprefix (i : Fin n) (j : Fin (r i)) :
      analyticDividedDifference (N i) j f =
        analyticDividedDifference (finiteNodeSequence (nodes i)) j f := by
    apply analyticDividedDifference_congr_nodes
    intro k hk
    have hkr : k < r i := hk.trans_lt j.isLt
    simp [N, finiteNodeSequence, hkr]
  calc
    _ = ∑ i, ∑ j : Fin (r i), ‖analyticDividedDifference (N i) j f‖ ^ 2 := by
      simp_rw [hprefix]
    _ ≤ ∑ i, ∑ j : Fin q, ‖analyticDividedDifference (N i) j f‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        _ = ∑ j ∈ Finset.range (r i), ‖analyticDividedDifference (N i) j f‖ ^ 2 :=
          Fin.sum_univ_eq_sum_range _ (r i)
        _ ≤ ∑ j ∈ Finset.range q, ‖analyticDividedDifference (N i) j f‖ ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (hrq i))
            (fun _ _ _ => sq_nonneg _)
        _ = _ := (Fin.sum_univ_eq_sum_range _ q).symm
    _ = ∑ j : Fin q, ∑ i, ‖analyticDividedDifference (N i) j f‖ ^ 2 := Finset.sum_comm
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro j hj
      exact sum_norm_analyticDividedDifference_sq_le_globalSobolev N j L U
        (fun i k _ => hN i k) hd hsep (hf.of_le (by exact_mod_cast Nat.succ_le_iff.mpr j.isLt))
        (hL2 j j.isLt.le) (hL2 (j + 1) (by omega))

/-- Actual canonical grouped samples of a C^q function with its first q
derivatives in L2 are square summable. This upper estimate applies to the
high-pass tail, without a band-limitation assumption. -/
theorem canonical_grouped_sobolev_sampling_upper
    (S : LocallyFiniteCarrier) {q : ℕ} {d : ℝ}
    (horder : BoundedClusterOrder S d q) (hd : 0 < d)
    {f : ℝ → ℂ} (hf : ContDiff ℝ q f)
    (hL2 : ∀ j ≤ q, MemLp (iteratedDeriv j f) 2) :
    Summable (fun C : CanonicalClusterIndex S d => ∑ j : Fin (horder.clusterSize C),
      ‖analyticDividedDifference (finiteNodeSequence (horder.realClusterNode C)) j f‖ ^ 2) ∧
    (∑' C : CanonicalClusterIndex S d, ∑ j : Fin (horder.clusterSize C),
      ‖analyticDividedDifference (finiteNodeSequence (horder.realClusterNode C)) j f‖ ^ 2) ≤
      ∑ j : Fin q, (2 * d⁻¹ * ‖(hL2 j j.isLt.le).toLp‖ ^ 2 +
        d * ‖(hL2 (j + 1) (by omega)).toLp‖ ^ 2) := by
  classical
  let e : CanonicalClusterIndex S d → ℝ := fun C => ∑ j : Fin (horder.clusterSize C),
    ‖analyticDividedDifference (finiteNodeSequence (horder.realClusterNode C)) j f‖ ^ 2
  have he (C) : 0 ≤ e C := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hfinite (s : Finset (CanonicalClusterIndex S d)) :
      ∑ C ∈ s, e C ≤ ∑ j : Fin q, (2 * d⁻¹ * ‖(hL2 j j.isLt.le).toLp‖ ^ 2 +
        d * ‖(hL2 (j + 1) (by omega)).toLp‖ ^ 2) := by
    let E := (Fintype.equivFin s).symm
    let groups : Fin (Fintype.card s) ↪ CanonicalClusterIndex S d :=
      ⟨fun i => (E i).val, Subtype.val_injective.comp E.injective⟩
    calc
      _ = ∑ C : s, e C.val := (Finset.sum_coe_sort s e).symm
      _ = ∑ i : Fin (Fintype.card s), e (groups i) := (E.sum_comp (fun C : s => e C.val)).symm
      _ ≤ _ := finite_grouped_sobolev_sampling_upper
        (fun i => horder.clusterSize (groups i)) (fun i => horder.clusterSize_pos (groups i))
        (fun i => horder.clusterSize_le (groups i)) (fun i => horder.realClusterNode (groups i))
        (fun i => horder.clusterLower (groups i)) (fun i => horder.clusterUpper (groups i))
        (fun i => horder.realClusterNode_mem_hull (groups i)) hd
        (fun i j hij x hx y hy => horder.cluster_hulls_separated hd
          (groups.injective.ne hij) hx hy) hf hL2
  exact ⟨summable_of_sum_le he hfinite, Real.tsum_le_of_sum_le he hfinite⟩

/-- A common bound on the first q Sobolev derivative norms gives an explicit
canonical sampling constant depending only on q and the inter-hull gap. -/
theorem canonical_grouped_sobolev_sampling_upper_of_derivative_bound
    (S : LocallyFiniteCarrier) {q : ℕ} {d : ℝ}
    (horder : BoundedClusterOrder S d q) (hd : 0 < d)
    {f : ℝ → ℂ} (hf : ContDiff ℝ q f)
    (hL2 : ∀ j ≤ q, MemLp (iteratedDeriv j f) 2)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ j (hj : j ≤ q), ‖(hL2 j hj).toLp‖ ≤ M) :
    (∑' C : CanonicalClusterIndex S d, ∑ j : Fin (horder.clusterSize C),
      ‖analyticDividedDifference (finiteNodeSequence (horder.realClusterNode C)) j f‖ ^ 2) ≤
        (q : ℝ) * (2 * d⁻¹ + d) * M ^ 2 := by
  apply (canonical_grouped_sobolev_sampling_upper S horder hd hf hL2).2.trans
  calc
    _ ≤ ∑ _j : Fin q, (2 * d⁻¹ + d) * M ^ 2 := by
      apply Finset.sum_le_sum
      intro j hj
      have hj₁ := (sq_le_sq₀ (norm_nonneg _) hM).mpr (hbound j j.isLt.le)
      have hj₂ := (sq_le_sq₀ (norm_nonneg _) hM).mpr (hbound (j + 1) (by omega))
      have h₁ := mul_le_mul_of_nonneg_left hj₁ (by positivity : 0 ≤ 2 * d⁻¹)
      have h₂ := mul_le_mul_of_nonneg_left hj₂ hd.le
      nlinarith
    _ = _ := by simp [mul_assoc]

/-- Finite actual Newton data of two functions are negatives when their
point values cancel. This identity uses distinct nodes, not a gap estimate. -/
theorem analyticDividedDifference_eq_neg_of_values_add_eq_zero
    {n : ℕ} (nodes : Fin n → ℝ) (hinj : Function.Injective nodes)
    (f g : ℝ → ℂ) (hzero : ∀ i, f (nodes i) + g (nodes i) = 0) (j : Fin n) :
    analyticDividedDifference (finiteNodeSequence nodes) j f =
      -analyticDividedDifference (finiteNodeSequence nodes) j g := by
  rw [analyticDividedDifference_eq_dividedDifferences nodes hinj,
    analyticDividedDifference_eq_dividedDifferences nodes hinj,
    dividedDifferences_eq_groupedNewtonWeights, dividedDifferences_eq_groupedNewtonWeights,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [eq_neg_of_add_eq_zero_left (hzero i), mul_neg]

/-- The actual Fourier integral of L1∩L2 data is L2 with precisely its
original norm, as a consequence of the proved integral/L2 Fourier bridge. -/
theorem memLp_fourier_norm_eq_of_integrable {G : ℝ → ℂ} (hG : Integrable G)
    (hG2 : MemLp G 2) :
    ∃ hF : MemLp (𝓕 G) 2, ‖hF.toLp‖ = ‖hG2.toLp‖ := by
  have hae := fourierIntegral_ae_eq_L2 hG hG2
  have hF : MemLp (𝓕 G) 2 := (memLp_congr_ae hae).mpr (Lp.memLp _)
  refine ⟨hF, ?_⟩
  have heq : hF.toLp = (𝓕 hG2.toLp : Lp ℂ 2 volume) :=
    Lp.ext (hF.coeFn_toLp.trans hae)
  rw [heq, Lp.norm_fourier_eq]

/-- A sharp high-pass factor at any j≤q≤k is bounded using the single
fixed-order factor Ω^q. This is the only common-order relaxation. -/
theorem inv_pow_sub_le_fixed_order_factor
    {Ω : ℝ} (hΩ : 1 ≤ Ω) {j q k : ℕ} (hjq : j ≤ q) (hqk : q ≤ k) :
    (Ω ^ (k - j))⁻¹ ≤ Ω ^ q * (Ω ^ k)⁻¹ := by
  have hΩpos : 0 < Ω := lt_of_lt_of_le zero_lt_one hΩ
  have hscale : Ω ^ k = Ω ^ (k - j) * Ω ^ j := by
    rw [← pow_add, Nat.sub_add_cancel (hjq.trans hqk)]
  have heq : (Ω ^ (k - j))⁻¹ = Ω ^ j * (Ω ^ k)⁻¹ := by
    rw [hscale, mul_inv]
    field_simp
  rw [heq]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact pow_le_pow_right₀ hΩ hjq

/-- The low/high frequency partition splits the exact squared L2 norm.
Its pointwise supports are disjoint, so no extraneous triangle factor is lost. -/
theorem norm_sq_low_high_frequency_split
    (r : ℝ) {G : ℝ → ℂ} (hG : MemLp G 2)
    (hlo : MemLp (lowFrequencyBand r G) 2) (hhi : MemLp (highFrequencyBand r G) 2) :
    ‖hG.toLp‖ ^ 2 = ‖hlo.toLp‖ ^ 2 + ‖hhi.toLp‖ ^ 2 := by
  rw [← integral_norm_sq_eq_toLp_norm_sq_complex hG,
    ← integral_norm_sq_eq_toLp_norm_sq_complex hlo,
    ← integral_norm_sq_eq_toLp_norm_sq_complex hhi,
    ← integral_add (integrable_norm_sq_of_memLp_complex hlo)
      (integrable_norm_sq_of_memLp_complex hhi)]
  apply integral_congr_ae
  filter_upwards [] with t
  by_cases ht : t ∈ Icc (-r) r <;> simp [lowFrequencyBand, highFrequencyBand, ht]

/-- Actual order-uniform spectral estimate on the Schwartz Fourier core.
For the whole block-count class, a single positive constant works for every
k≥q. Its geometric decay is Ω^(-2k); neither the constant nor the grouping
is chosen after k. The input zeros are actual point values on the carrier. -/
theorem spectralGap_of_groupedZeros_schwartzFourier
    {q N : ℕ} {d B₀ Ω Ω' : ℝ} (hd : 0 < d) (hΩ : 1 ≤ Ω)
    (hΩΩ' : Ω < Ω') (hgap : Ω' / Real.pi < (N : ℝ) / B₀) :
    ∃ C > 0, ∀ (Λ : TwoSidedCarrier) (_hcluster : BoundedClusterOrder Λ.toLocallyFinite d q),
      (∀ t R, 0 < R → (N : ℝ) * ((⌊2 * R / B₀⌋ : ℝ) - 2) ≤
        ((Λ.toLocallyFinite.carrier ∩ Ioo (t - R) (t + R)).ncard : ℝ)) →
      ∀ (G : SchwartzMap ℝ ℂ),
      (∀ t ∈ Λ.toLocallyFinite.carrier, (𝓕 (G : ℝ → ℂ)) t = 0) →
      ∀ k : ℕ, q ≤ k →
      (∫ t : ℝ, ‖(𝓕 (G : ℝ → ℂ)) t‖ ^ 2) ≤
        C * (Ω ^ (2 * k))⁻¹ * ∫ t : ℝ, ‖iteratedDeriv k (𝓕 (G : ℝ → ℂ)) t‖ ^ 2 := by
  have hΩpos : 0 < Ω := lt_of_lt_of_le zero_lt_one hΩ
  obtain ⟨A, _B, hA, _hB, hsampling⟩ := groupedPaleyWiener_sampling_function
    (q := q) hd hΩpos.le hΩΩ' hgap
  let C₀ : ℝ := (q : ℝ) * (2 * d⁻¹ + d)
  have hC₀ : 0 ≤ C₀ := by dsimp [C₀]; positivity
  let C : ℝ := 1 + A⁻¹ * C₀ * Ω ^ (2 * q)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro Λ hcluster hblock G hzero k hqk
  let r := Ω / (2 * Real.pi)
  have hr : 0 < r := by dsimp [r]; positivity
  have hscale : 2 * Real.pi * r = Ω := by dsimp [r]; field_simp
  let G₀ := lowFrequencyBand r (G : ℝ → ℂ)
  let G₁ := highFrequencyBand r (G : ℝ → ℂ)
  have hG₀ : MemLp G₀ 2 := (G.memLp 2).indicator measurableSet_Icc
  have hG₁ : MemLp G₁ 2 := (G.memLp 2).indicator measurableSet_Icc.compl
  obtain ⟨hF, hFnorm⟩ := memLp_fourier_norm_eq_of_integrable G.integrable (G.memLp 2)
  obtain ⟨hJ₀, hK, htail₀⟩ := exists_highFrequencyBand_fourier_derivative_bound
    G hr (j := 0) (k := k) (Nat.zero_le k)
  simp only [iteratedDeriv_zero, Nat.sub_zero, hscale] at hJ₀ htail₀
  obtain ⟨hF₁, hF₁norm⟩ := memLp_fourier_norm_eq_of_integrable
    (G.integrable.indicator measurableSet_Icc.compl) hG₁
  have htail (j : ℕ) (hj : j ≤ q) :
      ∃ hJ : MemLp (iteratedDeriv j (𝓕 G₁)) 2,
        ‖hJ.toLp‖ ≤ Ω ^ q * (Ω ^ k)⁻¹ * ‖hK.toLp‖ := by
    obtain ⟨hJ, hK', hbound⟩ := exists_highFrequencyBand_fourier_derivative_bound
      G hr (hj.trans hqk)
    rw [hscale] at hbound
    refine ⟨hJ, hbound.trans ?_⟩
    exact mul_le_mul_of_nonneg_right (inv_pow_sub_le_fixed_order_factor hΩ hj hqk)
      (norm_nonneg _)
  let hD (j : ℕ) (hj : j ≤ q) : MemLp (iteratedDeriv j (𝓕 G₁)) 2 :=
    Classical.choose (htail j hj)
  have hDbound (j : ℕ) (hj : j ≤ q) :
      ‖(hD j hj).toLp‖ ≤ Ω ^ q * (Ω ^ k)⁻¹ * ‖hK.toLp‖ :=
    Classical.choose_spec (htail j hj)
  have hsmooth : ContDiff ℝ q (𝓕 G₁) :=
    (contDiff_fourier_highFrequencyBand G r).of_le (by simp)
  have henergy := canonical_grouped_sobolev_sampling_upper_of_derivative_bound
    Λ.toLocallyFinite hcluster hd hsmooth hD (by positivity) hDbound
  have hlowSupport : ∀ᵐ t : ℝ,
      t ∉ Icc (-Ω / (2 * Real.pi)) (Ω / (2 * Real.pi)) → G₀ t = 0 := by
    filter_upwards [] with t ht
    exact indicator_of_notMem (by simpa only [r, neg_div] using ht) _
  have hlow := (hsampling Λ hcluster hblock G₀ hG₀ hlowSupport).2.1
  have hdata (C : CanonicalClusterIndex Λ.toLocallyFinite d) (j : Fin (hcluster.clusterSize C)) :
      analyticDividedDifference (finiteNodeSequence (hcluster.realClusterNode C)) j (𝓕 G₀) =
        -analyticDividedDifference (finiteNodeSequence (hcluster.realClusterNode C)) j (𝓕 G₁) := by
    apply analyticDividedDifference_eq_neg_of_values_add_eq_zero _
      (hcluster.realClusterNode_strictMono C).injective
    intro i
    have hsplit := congrFun (fourier_lowFrequencyBand_add_highFrequencyBand G.integrable r)
      (hcluster.realClusterNode C i)
    exact hsplit.trans (hzero _ (hcluster.realClusterNode_mem C i))
  simp_rw [hdata, norm_neg] at hlow
  have hlowBound : ‖hG₀.toLp‖ ^ 2 ≤
      A⁻¹ * (C₀ * (Ω ^ q * (Ω ^ k)⁻¹ * ‖hK.toLp‖) ^ 2) := by
    rw [← div_eq_inv_mul]
    apply (le_div_iff₀ hA).mpr
    have hlow' : ‖hG₀.toLp‖ ^ 2 * A ≤
        ∑' C : CanonicalClusterIndex Λ.toLocallyFinite d, ∑ j : Fin (hcluster.clusterSize C),
          ‖analyticDividedDifference (finiteNodeSequence (hcluster.realClusterNode C)) j (𝓕 G₁)‖ ^ 2 := by
      simpa only [mul_comm A] using hlow
    exact hlow'.trans henergy
  have hhighBound : ‖hG₁.toLp‖ ^ 2 ≤ ((Ω ^ k)⁻¹ * ‖hK.toLp‖) ^ 2 := by
    have hn : ‖hG₁.toLp‖ = ‖hJ₀.toLp‖ := hF₁norm.symm
    rw [hn]
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr htail₀
  rw [integral_norm_sq_eq_toLp_norm_sq_complex hF,
    integral_norm_sq_eq_toLp_norm_sq_complex hK, hFnorm,
    norm_sq_low_high_frequency_split r (G.memLp 2) hG₀ hG₁]
  apply (add_le_add hlowBound hhighBound).trans_eq
  dsimp [C]
  rw [show Ω ^ (2 * q) = (Ω ^ q) ^ 2 by rw [mul_comm 2 q, pow_mul],
    show Ω ^ (2 * k) = (Ω ^ k) ^ 2 by rw [mul_comm 2 k, pow_mul], ← inv_pow]
  ring

/-- The actual spectral estimate for any Schwartz function vanishing on
the carrier. Fourier inversion changes no point values or derivative orders. -/
theorem spectralGap_of_groupedZeros_schwartz
    {q N : ℕ} {d B₀ Ω Ω' : ℝ} (hd : 0 < d) (hΩ : 1 ≤ Ω)
    (hΩΩ' : Ω < Ω') (hgap : Ω' / Real.pi < (N : ℝ) / B₀) :
    ∃ C > 0, ∀ (Λ : TwoSidedCarrier) (_hcluster : BoundedClusterOrder Λ.toLocallyFinite d q),
      (∀ t R, 0 < R → (N : ℝ) * ((⌊2 * R / B₀⌋ : ℝ) - 2) ≤
        ((Λ.toLocallyFinite.carrier ∩ Ioo (t - R) (t + R)).ncard : ℝ)) →
      ∀ (f : SchwartzMap ℝ ℂ), (∀ t ∈ Λ.toLocallyFinite.carrier, f t = 0) →
      ∀ k : ℕ, q ≤ k →
      (∫ t : ℝ, ‖f t‖ ^ 2) ≤
        C * (Ω ^ (2 * k))⁻¹ * ∫ t : ℝ, ‖iteratedDeriv k (f : ℝ → ℂ) t‖ ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := spectralGap_of_groupedZeros_schwartzFourier
    (q := q) hd hΩ hΩΩ' hgap
  refine ⟨C, hC, ?_⟩
  intro Λ hcluster hblock f hzero k hqk
  have heq : (𝓕 ((𝓕⁻ f : SchwartzMap ℝ ℂ) : ℝ → ℂ) : ℝ → ℂ) = f := by
    rw [← SchwartzMap.fourier_coe, FourierTransform.fourier_fourierInv_eq]
  simpa only [heq] using hbound Λ hcluster hblock (𝓕⁻ f)
    (by simpa only [heq] using hzero) k hqk

/-- A single cofinal derivative-order threshold gives a strict π-scaled
gap for every carrier in the block-count class and every vanishing Schwartz
function. The threshold precedes the carrier and function, and all later
orders are covered, so in particular one common even order can be selected. -/
theorem eventual_spectralGap_of_groupedZeros_schwartz
    {q N : ℕ} {d B₀ Ω Ω' : ℝ} (hd : 0 < d) (hπΩ : Real.pi < Ω)
    (hΩΩ' : Ω < Ω') (hgap : Ω' / Real.pi < (N : ℝ) / B₀) :
    ∃ k₀ : ℕ, q ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
      ∀ (Λ : TwoSidedCarrier) (_hcluster : BoundedClusterOrder Λ.toLocallyFinite d q),
      (∀ t R, 0 < R → (N : ℝ) * ((⌊2 * R / B₀⌋ : ℝ) - 2) ≤
        ((Λ.toLocallyFinite.carrier ∩ Ioo (t - R) (t + R)).ncard : ℝ)) →
      ∀ (f : SchwartzMap ℝ ℂ), (∀ t ∈ Λ.toLocallyFinite.carrier, f t = 0) →
      Real.pi ^ (2 * k) * (∫ t : ℝ, ‖f t‖ ^ 2) ≤
        (1 / 2 : ℝ) * ∫ t : ℝ, ‖iteratedDeriv k (f : ℝ → ℂ) t‖ ^ 2 := by
  have hΩ : 1 ≤ Ω := by linarith [Real.two_le_pi]
  have hΩpos : 0 < Ω := Real.pi_pos.trans hπΩ
  obtain ⟨C, _hC, hbound⟩ := spectralGap_of_groupedZeros_schwartz
    (q := q) hd hΩ hΩΩ' hgap
  have hratio : 0 ≤ Real.pi / Ω := div_nonneg Real.pi_pos.le hΩpos.le
  have hratio₁ : Real.pi / Ω < 1 := (div_lt_one hΩpos).mpr hπΩ
  have hratio₂ : (Real.pi / Ω) ^ 2 < 1 := by nlinarith
  have htend : Tendsto (fun k : ℕ => C * ((Real.pi / Ω) ^ 2) ^ k) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds.mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one (sq_nonneg _) hratio₂))
  obtain ⟨K, hK⟩ := eventually_atTop.mp
    (htend.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)))
  refine ⟨max q K, le_max_left _ _, ?_⟩
  intro k hk Λ hcluster hblock f hzero
  have hqk : q ≤ k := (le_max_left q K).trans hk
  have hKk : K ≤ k := (le_max_right q K).trans hk
  calc
    _ ≤ Real.pi ^ (2 * k) * (C * (Ω ^ (2 * k))⁻¹ *
        ∫ t : ℝ, ‖iteratedDeriv k (f : ℝ → ℂ) t‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (hbound Λ hcluster hblock f hzero k hqk) (by positivity)
    _ = (C * ((Real.pi / Ω) ^ 2) ^ k) *
        ∫ t : ℝ, ‖iteratedDeriv k (f : ℝ → ℂ) t‖ ^ 2 := by
      rw [← pow_mul, div_pow]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (hK k hKk).le
      (integral_nonneg (fun _ => sq_nonneg _))

end

end MeyerGeneralProblem
