module

public import MeyerGeneralProblem.Sampling.GroupedSpectralGap

@[expose] public section

/-!
# Grouped spectral estimates for Fourier-Sobolev data

Weighted L2 frequency data have integrable moments below their Sobolev
order. This supplies actual continuous Fourier representatives and the
finite derivative tower required by the gap-free grouped sampling estimate.
No zero-preserving Schwartz approximation is used.
-/

namespace MeyerGeneralProblem

noncomputable section

-- The upgraded elaborator expands large measure-space expressions in these bounds.
set_option maxHeartbeats 4000000

open MeasureTheory Set Filter
open scoped FourierTransform Topology BigOperators ENNReal

/-- The elementary decay weight used to turn weighted L2 data into L1
moments belongs to L2 on the whole real line. -/
theorem memLp_inverse_one_add_abs :
    MemLp (fun t : ℝ => (1 + |t|)⁻¹) 2 := by
  apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
  have h : Integrable (fun t : ℝ => (1 + ‖t‖) ^ (-2 : ℝ)) :=
    integrable_one_add_norm (by norm_num)
  convert h using 1
  ext t
  rw [show (-2 : ℝ) = -(2 : ℕ) by norm_num, Real.rpow_neg, Real.rpow_natCast]
  · simp [Real.norm_eq_abs, inv_pow]
  · positivity

/-- One spare Sobolev derivative dominates the L2 moment multiplier,
uniformly over both the compact central region and the frequency tails. -/
theorem weighted_moment_norm_le_fourierSobolev
    (G : ℝ → ℂ) {j k : ℕ} (hjk : j + 1 ≤ k) (t : ℝ) :
    (1 + |t|) * |t| ^ j * ‖G t‖ ≤
      2 * (‖G t‖ + ‖fourierDerivativeData k G t‖) := by
  rw [norm_fourierDerivativeData]
  have ht : 0 ≤ |t| := abs_nonneg t
  have hG : 0 ≤ ‖G t‖ := norm_nonneg _
  have hπ : 1 ≤ 2 * Real.pi := by linarith [Real.two_le_pi]
  by_cases hsmall : |t| ≤ 1
  · have hp : |t| ^ j ≤ 1 := pow_le_one₀ ht hsmall
    have hprod : (1 + |t|) * |t| ^ j ≤ 2 := by nlinarith [pow_nonneg ht j]
    have hh := mul_le_mul_of_nonneg_right hprod hG
    nlinarith [mul_nonneg (pow_nonneg (by positivity : 0 ≤ 2 * Real.pi * |t|) k) hG]
  · have hlarge : 1 ≤ |t| := le_of_lt (lt_of_not_ge hsmall)
    have hp : |t| ^ (j + 1) ≤ |t| ^ k := pow_le_pow_right₀ hlarge hjk
    have hbase : |t| ≤ 2 * Real.pi * |t| := by nlinarith
    have hpow : |t| ^ k ≤ (2 * Real.pi * |t|) ^ k := by gcongr
    have hprod : (1 + |t|) * |t| ^ j ≤ 2 * (2 * Real.pi * |t|) ^ k := by
      rw [pow_succ] at hp
      nlinarith [mul_nonneg (pow_nonneg ht j) (sub_nonneg.mpr hlarge)]
    nlinarith [mul_le_mul_of_nonneg_right hprod hG]

/-- Actual Fourier-Sobolev L2 data have every real moment strictly below
their Sobolev order in L1. The spare order is explicit, not a smoothness
or integrability certificate supplied by the caller. -/
theorem integrable_real_moment_of_fourierSobolev
    {G : ℝ → ℂ} (hG : MemLp G 2) {k : ℕ}
    (hK : MemLp (fourierDerivativeData k G) 2) {j : ℕ} (hjk : j + 1 ≤ k) :
    Integrable (fun t : ℝ => t ^ j • G t) := by
  let H : ℝ → ℝ := fun t => (1 + |t|) * |t| ^ j * ‖G t‖
  have hm : AEStronglyMeasurable H volume :=
    (show Continuous (fun t : ℝ => (1 + |t|) * |t| ^ j) by fun_prop).aestronglyMeasurable.mul
      hG.aestronglyMeasurable.norm
  have hH : MemLp H 2 := (hG.norm.add hK.norm).of_le_mul hm (Eventually.of_forall (fun t => by
    simpa only [H, Real.norm_eq_abs, Pi.add_apply,
      abs_of_nonneg (by positivity : 0 ≤ (1 + |t|) * |t| ^ j * ‖G t‖),
      abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))] using
      weighted_moment_norm_le_fourierSobolev G hjk t))
  have hint := hH.integrable_mul memLp_inverse_one_add_abs
  apply hint.mono' ((by fun_prop : Continuous (fun t : ℝ => t ^ j)).aestronglyMeasurable.smul
    hG.aestronglyMeasurable)
  filter_upwards [] with t
  change ‖t ^ j • G t‖ ≤ H t * (1 + |t|)⁻¹
  rw [norm_smul, Real.norm_eq_abs, abs_pow]
  dsimp [H]
  have hp : 0 < 1 + |t| := by positivity
  field_simp
  exact le_rfl

/-- A finite tower of integrable moments already suffices for the exact
classical derivative formula up to that order. -/
theorem iteratedDeriv_fourier_of_integrable_moments_le
    {G : ℝ → ℂ} {q : ℕ}
    (hG : ∀ j : ℕ, j ≤ q → Integrable (fun t : ℝ => t ^ j • G t))
    {j : ℕ} (hj : j ≤ q) :
    iteratedDeriv j (𝓕 G) = (𝓕 (fourierDerivativeData j G) : ℝ → ℂ) := by
  change iteratedDeriv j (𝓕 G) =
    𝓕 (fun t : ℝ => (-2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) ^ j * G t)
  simpa only [smul_eq_mul] using Real.iteratedDeriv_fourier (N := (q : ℕ∞))
    (fun n hn => hG n (by exact_mod_cast hn)) (by exact_mod_cast hj)

/-- A finite integrable moment tower produces actual C^q Fourier data. -/
theorem contDiff_fourier_of_integrable_moments_le
    {G : ℝ → ℂ} {q : ℕ}
    (hG : ∀ j : ℕ, j ≤ q → Integrable (fun t : ℝ => t ^ j • G t)) :
    ContDiff ℝ q (𝓕 G) := by
  apply Real.contDiff_fourier (N := (q : ℕ∞))
  intro j hj
  convert (hG j (by exact_mod_cast hj)).norm using 1
  ext t
  simp [norm_pow]

/-- The actual derivative norm equals the exact frequency multiplier norm
whenever the required finite moment tower is integrable. -/
theorem memLp_iteratedDeriv_fourier_of_integrable_moments_le
    {G : ℝ → ℂ} {q : ℕ}
    (hG : ∀ j : ℕ, j ≤ q → Integrable (fun t : ℝ => t ^ j • G t))
    {j : ℕ} (hj : j ≤ q) (hM : MemLp (fourierDerivativeData j G) 2) :
    ∃ hD : MemLp (iteratedDeriv j (𝓕 G)) 2, ‖hD.toLp‖ = ‖hM.toLp‖ := by
  have hae : iteratedDeriv j (𝓕 G) =ᵐ[volume] (𝓕 hM.toLp : Lp ℂ 2 volume) := by
    rw [iteratedDeriv_fourier_of_integrable_moments_le hG hj]
    exact fourierIntegral_ae_eq_L2 (integrable_fourierDerivativeData_of_moment j (hG j hj)) hM
  have hD : MemLp (iteratedDeriv j (𝓕 G)) 2 := (memLp_congr_ae hae).mpr (Lp.memLp _)
  refine ⟨hD, ?_⟩
  have hc : hD.toLp = (𝓕 hM.toLp : Lp ℂ 2 volume) := Lp.ext (hD.coeFn_toLp.trans hae)
  rw [hc, Lp.norm_fourier_eq]

/-- Genuine H^k frequency data give a continuous finite derivative tower
for the high-pass Fourier integral whenever q+1≤k. -/
theorem contDiff_fourier_highFrequencyBand_of_fourierSobolev
    {G : ℝ → ℂ} (hG : MemLp G 2) {k q : ℕ}
    (hK : MemLp (fourierDerivativeData k G) 2) (hqk : q + 1 ≤ k) (r : ℝ) :
    ContDiff ℝ q (𝓕 (highFrequencyBand r G)) :=
  contDiff_fourier_of_integrable_moments_le (fun j hj =>
    integrable_real_moment_highFrequencyBand r j
      (integrable_real_moment_of_fourierSobolev hG hK (by omega)))

/-- Actual high-pass derivative norms for Fourier-Sobolev data have the
sharp bandwidth factor, without a Schwartz or classical k-th derivative
assumption. Only the requested j-th derivative needs its spare moment. -/
theorem exists_highFrequencyBand_derivative_bound_of_fourierSobolev
    {G : ℝ → ℂ} (hG : MemLp G 2) {k : ℕ}
    (hK : MemLp (fourierDerivativeData k G) 2) {r : ℝ} (hr : 0 < r)
    {j : ℕ} (hjk : j + 1 ≤ k) :
    ∃ hJ : MemLp (iteratedDeriv j (𝓕 (highFrequencyBand r G))) 2,
      ‖hJ.toLp‖ ≤ ((2 * Real.pi * r) ^ (k - j))⁻¹ * ‖hK.toLp‖ := by
  obtain ⟨hM, hbound⟩ := memLp_fourierDerivativeData_highFrequencyBand hr
    hG.aestronglyMeasurable (by omega : j ≤ k) hK
  obtain ⟨hJ, hnorm⟩ := memLp_iteratedDeriv_fourier_of_integrable_moments_le
    (q := j) (fun n hn => integrable_real_moment_highFrequencyBand r n
      (integrable_real_moment_of_fourierSobolev hG hK (by omega))) le_rfl hM
  exact ⟨hJ, by rw [hnorm]; exact hbound⟩

/-- The actual spectral estimate extends beyond the Schwartz core to
arbitrary Fourier-Sobolev data. The derivative energy is the genuine k-th
frequency multiplier norm. A single constant works for the whole geometric
class and all k≥q+1, and the zeros refer to the actual continuous Fourier
integral, not an arbitrary representative of an L2 equivalence class. -/
theorem spectralGap_of_groupedZeros_fourierSobolev
    {q N : ℕ} {d B₀ Ω Ω' : ℝ} (hd : 0 < d) (hΩ : 1 ≤ Ω)
    (hΩΩ' : Ω < Ω') (hgap : Ω' / Real.pi < (N : ℝ) / B₀) :
    ∃ C > 0, ∀ (Λ : TwoSidedCarrier) (_hcluster : BoundedClusterOrder Λ.toLocallyFinite d q),
      (∀ t R, 0 < R → (N : ℝ) * ((⌊2 * R / B₀⌋ : ℝ) - 2) ≤
        ((Λ.toLocallyFinite.carrier ∩ Ioo (t - R) (t + R)).ncard : ℝ)) →
      ∀ (G : ℝ → ℂ) (_hG : MemLp G 2) (k : ℕ), q + 1 ≤ k →
      ∀ (hK : MemLp (fourierDerivativeData k G) 2),
      (∀ t ∈ Λ.toLocallyFinite.carrier, (𝓕 G : ℝ → ℂ) t = 0) →
      (∫ t : ℝ, ‖(𝓕 G) t‖ ^ 2) ≤ C * (Ω ^ (2 * k))⁻¹ * ‖hK.toLp‖ ^ 2 := by
  have hΩpos : 0 < Ω := lt_of_lt_of_le zero_lt_one hΩ
  obtain ⟨A, _B, hA, _hB, hsampling⟩ := groupedPaleyWiener_sampling_function
    (q := q) hd hΩpos.le hΩΩ' hgap
  let C₀ : ℝ := (q : ℝ) * (2 * d⁻¹ + d)
  have hC₀ : 0 ≤ C₀ := by dsimp [C₀]; positivity
  let C : ℝ := 1 + A⁻¹ * C₀ * Ω ^ (2 * q)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro Λ hcluster hblock G hG k hqk hK hzero
  have hGint : Integrable G := by
    simpa only [pow_zero, one_smul] using
      integrable_real_moment_of_fourierSobolev hG hK (j := 0) (by omega)
  let r := Ω / (2 * Real.pi)
  have hr : 0 < r := by dsimp [r]; positivity
  have hscale : 2 * Real.pi * r = Ω := by dsimp [r]; field_simp
  let G₀ := lowFrequencyBand r G
  let G₁ := highFrequencyBand r G
  have hG₀ : MemLp G₀ 2 := hG.indicator measurableSet_Icc
  have hG₁ : MemLp G₁ 2 := hG.indicator measurableSet_Icc.compl
  obtain ⟨hF, hFnorm⟩ := memLp_fourier_norm_eq_of_integrable hGint hG
  obtain ⟨hJ₀, htail₀⟩ := exists_highFrequencyBand_derivative_bound_of_fourierSobolev
    hG hK hr (j := 0) (by omega)
  simp only [iteratedDeriv_zero, Nat.sub_zero, hscale] at hJ₀ htail₀
  obtain ⟨hF₁, hF₁norm⟩ := memLp_fourier_norm_eq_of_integrable
    (hGint.indicator measurableSet_Icc.compl) hG₁
  have htail (j : ℕ) (hj : j ≤ q) :
      ∃ hJ : MemLp (iteratedDeriv j (𝓕 G₁)) 2,
        ‖hJ.toLp‖ ≤ Ω ^ q * (Ω ^ k)⁻¹ * ‖hK.toLp‖ := by
    obtain ⟨hJ, hbound⟩ := exists_highFrequencyBand_derivative_bound_of_fourierSobolev
      hG hK hr (j := j) (by omega)
    rw [hscale] at hbound
    refine ⟨hJ, hbound.trans ?_⟩
    exact mul_le_mul_of_nonneg_right
      (inv_pow_sub_le_fixed_order_factor hΩ hj (by omega)) (norm_nonneg _)
  let hD (j : ℕ) (hj : j ≤ q) : MemLp (iteratedDeriv j (𝓕 G₁)) 2 :=
    Classical.choose (htail j hj)
  have hDbound (j : ℕ) (hj : j ≤ q) :
      ‖(hD j hj).toLp‖ ≤ Ω ^ q * (Ω ^ k)⁻¹ * ‖hK.toLp‖ :=
    Classical.choose_spec (htail j hj)
  have hsmooth : ContDiff ℝ q (𝓕 G₁) :=
    contDiff_fourier_highFrequencyBand_of_fourierSobolev hG hK hqk r
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
    have hsplit := congrFun (fourier_lowFrequencyBand_add_highFrequencyBand hGint r)
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
  rw [integral_norm_sq_eq_toLp_norm_sq_complex hF, hFnorm,
    norm_sq_low_high_frequency_split r hG hG₀ hG₁]
  apply (add_le_add hlowBound hhighBound).trans_eq
  dsimp [C]
  rw [show Ω ^ (2 * q) = (Ω ^ q) ^ 2 by rw [mul_comm 2 q, pow_mul],
    show Ω ^ (2 * k) = (Ω ^ k) ^ 2 by rw [mul_comm 2 k, pow_mul], ← inv_pow]
  ring

/-- One cofinal order threshold gives a strict π-scaled gap for every
member of the geometric class and every vanishing Fourier-Sobolev datum.
In particular, one common even Sobolev order can be chosen for the class. -/
theorem eventual_spectralGap_of_groupedZeros_fourierSobolev
    {q N : ℕ} {d B₀ Ω Ω' : ℝ} (hd : 0 < d) (hπΩ : Real.pi < Ω)
    (hΩΩ' : Ω < Ω') (hgap : Ω' / Real.pi < (N : ℝ) / B₀) :
    ∃ k₀ : ℕ, q + 1 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
      ∀ (Λ : TwoSidedCarrier) (_hcluster : BoundedClusterOrder Λ.toLocallyFinite d q),
      (∀ t R, 0 < R → (N : ℝ) * ((⌊2 * R / B₀⌋ : ℝ) - 2) ≤
        ((Λ.toLocallyFinite.carrier ∩ Ioo (t - R) (t + R)).ncard : ℝ)) →
      ∀ (G : ℝ → ℂ) (_hG : MemLp G 2) (hK : MemLp (fourierDerivativeData k G) 2),
      (∀ t ∈ Λ.toLocallyFinite.carrier, (𝓕 G : ℝ → ℂ) t = 0) →
      Real.pi ^ (2 * k) * (∫ t : ℝ, ‖(𝓕 G) t‖ ^ 2) ≤ (1 / 2 : ℝ) * ‖hK.toLp‖ ^ 2 := by
  have hΩ : 1 ≤ Ω := by linarith [Real.two_le_pi]
  have hΩpos : 0 < Ω := Real.pi_pos.trans hπΩ
  obtain ⟨C, _hC, hbound⟩ := spectralGap_of_groupedZeros_fourierSobolev
    (q := q) hd hΩ hΩΩ' hgap
  have hratio : 0 ≤ Real.pi / Ω := div_nonneg Real.pi_pos.le hΩpos.le
  have hratio₁ : Real.pi / Ω < 1 := (div_lt_one hΩpos).mpr hπΩ
  have hratio₂ : (Real.pi / Ω) ^ 2 < 1 := by nlinarith
  have htend : Tendsto (fun k : ℕ => C * ((Real.pi / Ω) ^ 2) ^ k) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds.mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one (sq_nonneg _) hratio₂))
  obtain ⟨K, hK⟩ := eventually_atTop.mp
    (htend.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)))
  refine ⟨max (q + 1) K, le_max_left _ _, ?_⟩
  intro k hk Λ hcluster hblock G hG hM hzero
  have hqk : q + 1 ≤ k := (le_max_left (q + 1) K).trans hk
  have hKk : K ≤ k := (le_max_right (q + 1) K).trans hk
  calc
    _ ≤ Real.pi ^ (2 * k) * (C * (Ω ^ (2 * k))⁻¹ * ‖hM.toLp‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (hbound Λ hcluster hblock G hG k hqk hM hzero) (by positivity)
    _ = (C * ((Real.pi / Ω) ^ 2) ^ k) * ‖hM.toLp‖ ^ 2 := by
      rw [← pow_mul, div_pow]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (hK k hKk).le (sq_nonneg _)

/-- A continuous L2 function in the frequency-defined H^k domain, k≥1,
equals the actual Fourier integral of its inverse L2 Fourier transform at
every point. Thus its carrier zeros are genuine pointwise data. -/
theorem fourierIntegral_inverse_L2_eq_of_fourierSobolev
    {f : ℝ → ℂ} (hf : Continuous f) (hF : MemLp f 2) {k : ℕ} (hk : 1 ≤ k)
    (hK : MemLp (fourierDerivativeData k ((𝓕⁻ hF.toLp : Lp ℂ 2 volume) : ℝ → ℂ)) 2) :
    (𝓕 ((𝓕⁻ hF.toLp : Lp ℂ 2 volume) : ℝ → ℂ) : ℝ → ℂ) = f := by
  let G : Lp ℂ 2 volume := 𝓕⁻ hF.toLp
  have hint : Integrable (G : ℝ → ℂ) := by
    simpa only [pow_zero, one_smul] using
      integrable_real_moment_of_fourierSobolev (Lp.memLp G) hK (j := 0) hk
  have hcont : Continuous (𝓕 (G : ℝ → ℂ) : ℝ → ℂ) :=
    (contDiff_fourier_of_integrable_moments_le (q := 0) (fun j hj => by
      have : j = 0 := by omega
      simpa only [this, pow_zero, one_smul] using hint)).continuous
  have heq : (Lp.memLp G).toLp = G := Lp.ext (Lp.memLp G).coeFn_toLp
  have hae := fourierIntegral_ae_eq_L2 hint (Lp.memLp G)
  rw [heq] at hae
  have hinv : (𝓕 G : Lp ℂ 2 volume) = hF.toLp := FourierTransform.fourier_fourierInv_eq _
  rw [hinv] at hae
  exact (hcont.ae_eq_iff_eq volume hf).mp (hae.trans hF.coeFn_toLp)

/-- The spectral estimate on actual continuous functions with arbitrary
frequency-defined H^k regularity. No Schwartz extension or pointwise
k-th derivative is required; the right side is the exact Sobolev multiplier
energy of the inverse L2 Fourier transform. -/
theorem spectralGap_of_groupedZeros_continuousFourierSobolev
    {q N : ℕ} {d B₀ Ω Ω' : ℝ} (hd : 0 < d) (hΩ : 1 ≤ Ω)
    (hΩΩ' : Ω < Ω') (hgap : Ω' / Real.pi < (N : ℝ) / B₀) :
    ∃ C > 0, ∀ (Λ : TwoSidedCarrier) (_hcluster : BoundedClusterOrder Λ.toLocallyFinite d q),
      (∀ t R, 0 < R → (N : ℝ) * ((⌊2 * R / B₀⌋ : ℝ) - 2) ≤
        ((Λ.toLocallyFinite.carrier ∩ Ioo (t - R) (t + R)).ncard : ℝ)) →
      ∀ (f : ℝ → ℂ) (_hf : Continuous f) (hF : MemLp f 2) (k : ℕ), q + 1 ≤ k →
      ∀ (hK : MemLp (fourierDerivativeData k ((𝓕⁻ hF.toLp : Lp ℂ 2 volume) : ℝ → ℂ)) 2),
      (∀ t ∈ Λ.toLocallyFinite.carrier, f t = 0) →
      (∫ t : ℝ, ‖f t‖ ^ 2) ≤ C * (Ω ^ (2 * k))⁻¹ * ‖hK.toLp‖ ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := spectralGap_of_groupedZeros_fourierSobolev
    (q := q) hd hΩ hΩΩ' hgap
  refine ⟨C, hC, ?_⟩
  intro Λ hcluster hblock f hf hF k hqk hK hzero
  have heq := fourierIntegral_inverse_L2_eq_of_fourierSobolev hf hF (by omega : 1 ≤ k) hK
  simpa only [heq] using hbound Λ hcluster hblock _
    (Lp.memLp (𝓕⁻ hF.toLp : Lp ℂ 2 volume)) k hqk hK (by simpa only [heq] using hzero)

/-- The common cofinal strict gap also holds for actual continuous
frequency-defined Sobolev functions, with the threshold chosen before the
carrier, function, and its Sobolev-domain witness. -/
theorem eventual_spectralGap_of_groupedZeros_continuousFourierSobolev
    {q N : ℕ} {d B₀ Ω Ω' : ℝ} (hd : 0 < d) (hπΩ : Real.pi < Ω)
    (hΩΩ' : Ω < Ω') (hgap : Ω' / Real.pi < (N : ℝ) / B₀) :
    ∃ k₀ : ℕ, q + 1 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
      ∀ (Λ : TwoSidedCarrier) (_hcluster : BoundedClusterOrder Λ.toLocallyFinite d q),
      (∀ t R, 0 < R → (N : ℝ) * ((⌊2 * R / B₀⌋ : ℝ) - 2) ≤
        ((Λ.toLocallyFinite.carrier ∩ Ioo (t - R) (t + R)).ncard : ℝ)) →
      ∀ (f : ℝ → ℂ) (_hf : Continuous f) (hF : MemLp f 2),
      ∀ (hK : MemLp (fourierDerivativeData k ((𝓕⁻ hF.toLp : Lp ℂ 2 volume) : ℝ → ℂ)) 2),
      (∀ t ∈ Λ.toLocallyFinite.carrier, f t = 0) →
      Real.pi ^ (2 * k) * (∫ t : ℝ, ‖f t‖ ^ 2) ≤ (1 / 2 : ℝ) * ‖hK.toLp‖ ^ 2 := by
  obtain ⟨k₀, hqk₀, hbound⟩ := eventual_spectralGap_of_groupedZeros_fourierSobolev
    (q := q) hd hπΩ hΩΩ' hgap
  refine ⟨k₀, hqk₀, ?_⟩
  intro k hk Λ hcluster hblock f hf hF hK hzero
  have heq := fourierIntegral_inverse_L2_eq_of_fourierSobolev hf hF (by omega : 1 ≤ k) hK
  simpa only [heq] using hbound k hk Λ hcluster hblock _
    (Lp.memLp (𝓕⁻ hF.toLp : Lp ℂ 2 volume)) hK (by simpa only [heq] using hzero)

end

end MeyerGeneralProblem
