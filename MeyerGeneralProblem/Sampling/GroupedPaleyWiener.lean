module

public import MeyerGeneralProblem.Sampling.GroupedBernsteinSampling
public import MeyerGeneralProblem.Sampling.BernsteinLocalizer
public import MeyerGeneralProblem.Carrier.CanonicalSourceBlocks
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import all Mathlib.Analysis.SpecialFunctions.JapaneseBracket

@[expose] public section

/-!
# Genuine grouped Paley–Wiener localization and lower sampling

The source localization uses full-prefix divided differences of the product
of a function and a narrow-band localizer. Here the Leibniz identity is proved
for arbitrary functions on distinct nodes by their actual Newton interpolants;
the analytic HG estimate then bounds its localizer factors without inverse gaps.
The proved narrow-band entire localizer and class-uniform Bernstein sup estimate
give a genuine squared lower sampling inequality on the real line. Tonelli and
the exact canonical-cluster repetition identity retain potentially infinite
energies without an unproved summability assumption. Identification with arbitrary
Paley–Wiener representatives and the spectral-gap conclusion are separate steps.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set Filter Polynomial
open MeasureTheory
open scoped Topology BigOperators FourierTransform ENNReal

/-- Actual divided-difference Leibniz law at distinct nodes, for arbitrary
functions. Both factors are replaced only by interpolants with exactly their
values on the whole prefix, so no regularity or polynomial premise is hidden. -/
theorem analyticDividedDifference_leibniz_of_distinct
    (nodes : ℕ → ℝ) (order : ℕ)
    (hdistinct : ∀ i ≤ order, ∀ j ≤ order, i ≠ j → nodes i ≠ nodes j)
    (f g : ℝ → ℂ) :
    analyticDividedDifference nodes order (fun x => f x * g x) =
      ∑ k ∈ Finset.range (order + 1),
        analyticDividedDifference nodes k f *
          analyticDividedDifference (fun i => nodes (i + k)) (order - k) g := by
  let z : Fin (order + 1) → ℂ := fun i => (nodes i : ℂ)
  have hz : Function.Injective z := by
    intro i j hij
    apply Fin.ext
    by_contra h
    exact hdistinct i (by omega) j (by omega) h (Complex.ofReal_injective hij)
  let p := newtonInterpolantFromValues z hz (fun i => f (nodes i))
  let r := newtonInterpolantFromValues z hz (fun i => g (nodes i))
  have hp (j : ℕ) (hj : j ≤ order) : p.eval (nodes j : ℂ) = f (nodes j) :=
    eval_newtonInterpolantFromValues_at_node z hz (fun i => f (nodes i)) ⟨j, by omega⟩
  have hr (j : ℕ) (hj : j ≤ order) : r.eval (nodes j : ℂ) = g (nodes j) :=
    eval_newtonInterpolantFromValues_at_node z hz (fun i => g (nodes i)) ⟨j, by omega⟩
  have htransfer (u : ℝ → ℂ) (v : ℂ[X])
      (hv : ∀ j ≤ order, v.eval (nodes j : ℂ) = u (nodes j))
      (start len : ℕ) (hlen : start + len ≤ order) :
      analyticDividedDifference (fun i => nodes (i + start)) len u =
        polynomialDividedDifference (fun i => (nodes (i + start) : ℂ)) len v := by
    rw [← analyticDividedDifference_polynomial_eval]
    apply analyticDividedDifference_congr_values_of_distinct
    · intro i hi j hj hij
      exact hdistinct (i + start) (by omega) (j + start) (by omega) (by omega)
    · intro j hj
      exact (hv (j + start) (by omega)).symm
  have hproduct := htransfer (fun x => f x * g x) (p * r) (by
    intro j hj
    rw [Polynomial.eval_mul, hp j hj, hr j hj]) 0 order (by omega)
  simp only [Nat.add_zero] at hproduct
  rw [hproduct, dividedDifference_leibniz]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ order := by have := Finset.mem_range.mp hk; omega
  congr 1
  · simpa only [Nat.add_zero] using (htransfer f p hp 0 k (by omega)).symm
  · exact (htransfer g r hr k (order - k) (by omega)).symm

/-- A smooth localizer whose derivatives up to the prefix order are bounded
on the actual node hull controls product data by the original full prefix.
The bound uses no minimum node gap and retains the actual functions. -/
theorem norm_analyticDividedDifference_mul_le_of_derivative_bound
    (nodes : ℕ → ℝ) (order : ℕ)
    (hdistinct : ∀ i ≤ order, ∀ j ≤ order, i ≠ j → nodes i ≠ nodes j)
    (f : ℝ → ℂ) {g : ℝ → ℂ} (hg : ContDiff ℝ order g)
    {L U M : ℝ} (hM : 0 ≤ M)
    (hnodes : ∀ j ≤ order, nodes j ∈ Icc L U)
    (hbound : ∀ j ≤ order, ∀ x ∈ Icc L U, ‖iteratedDeriv j g x‖ ≤ M) :
    ‖analyticDividedDifference nodes order (fun x => f x * g x)‖ ≤
      M * ∑ k ∈ Finset.range (order + 1), ‖analyticDividedDifference nodes k f‖ := by
  rw [analyticDividedDifference_leibniz_of_distinct nodes order hdistinct f g]
  calc
    _ ≤ ∑ k ∈ Finset.range (order + 1),
        ‖analyticDividedDifference nodes k f *
          analyticDividedDifference (fun i => nodes (i + k)) (order - k) g‖ :=
      norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range (order + 1), ‖analyticDividedDifference nodes k f‖ * M := by
      apply Finset.sum_le_sum
      intro k hk
      have hk' : k ≤ order := by have := Finset.mem_range.mp hk; omega
      rw [norm_mul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      have ht := norm_analyticDividedDifference_le_of_contDiff
        (fun i => nodes (i + k)) (order - k)
        (hg.of_le (by exact_mod_cast Nat.sub_le order k))
        (fun j hj => hnodes (j + k) (by omega))
        (hbound (order - k) (Nat.sub_le order k))
      exact ht.trans (div_le_self hM (by
        exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos (order - k))))
    _ = _ := by rw [← Finset.sum_mul, mul_comm]

/-- Quadratic decay on a bounded hull can be recentered at its actual anchor
with a diameter-only constant. -/
theorem quadratic_decay_recenter {C D x y c : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hy : |y - c| ≤ D) :
    C / (1 + |y - x|) ^ 2 ≤ C * (1 + D) ^ 2 / (1 + |x - c|) ^ 2 := by
  have ht : |x - c| ≤ |y - x| + D := by
    have h := abs_add_le (x - y) (y - c)
    rw [sub_add_sub_cancel, abs_sub_comm x y] at h
    linarith
  have hweight : 1 + |x - c| ≤ (1 + D) * (1 + |y - x|) := by
    have hcross := mul_nonneg hD (abs_nonneg (y - x))
    nlinarith
  have hsq := (sq_le_sq₀ (by positivity) (by positivity)).mpr hweight
  rw [mul_pow] at hsq
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hsq hC]

/-- Actual localized prefix data are bounded by the full original group data
and a quadratic translate weight. Neither the constant nor the proof uses
an inverse internal gap. -/
theorem norm_grouped_prefix_mul_localizer_le
    {n q : ℕ} (nodes : Fin n → ℝ) (hinjective : Function.Injective nodes)
    (hnq : n ≤ q) (j : Fin n) (f : ℝ → ℂ) {K : ℝ → ℂ}
    (hK : ContDiff ℝ q K) {C D c : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hdecay : ∀ k ≤ q, ∀ t, ‖iteratedDeriv k K t‖ ≤ C / (1 + |t|) ^ 2)
    (hnodes : ∀ i, |nodes i - c| ≤ D) (x : ℝ) :
    ‖analyticDividedDifference (finiteNodeSequence nodes) j (fun y => f y * K (y - x))‖ ≤
      (C * (1 + D) ^ 2 / (1 + |x - c|) ^ 2) *
        ∑ i : Fin n, ‖analyticDividedDifference (finiteNodeSequence nodes) i f‖ := by
  have hdistinct : ∀ a ≤ j.val, ∀ b ≤ j.val, a ≠ b →
      finiteNodeSequence nodes a ≠ finiteNodeSequence nodes b := by
    intro a ha b hb hab heq
    have han : a < n := ha.trans_lt j.isLt
    have hbn : b < n := hb.trans_lt j.isLt
    simp only [finiteNodeSequence, dite_eq_left han, dite_eq_left hbn] at heq
    exact hab (congrArg Fin.val (hinjective heq))
  have hM : 0 ≤ C * (1 + D) ^ 2 / (1 + |x - c|) ^ 2 := by positivity
  have hg : ContDiff ℝ j.val (fun y => K (y - x)) :=
    (hK.of_le (by exact_mod_cast j.isLt.le.trans hnq)).comp (by fun_prop)
  have h := norm_analyticDividedDifference_mul_le_of_derivative_bound
    (finiteNodeSequence nodes) j hdistinct f hg hM
    (L := c - D) (U := c + D) (by
      intro k hk
      have hkn : k < n := hk.trans_lt j.isLt
      simp only [finiteNodeSequence, dite_eq_left hkn]
      have hb := abs_le.mp (hnodes ⟨k, hkn⟩)
      exact ⟨by linarith [hb.1], by linarith [hb.2]⟩) (by
      intro k hk y hy
      rw [iteratedDeriv_comp_sub_const]
      exact (hdecay k (hk.trans (j.isLt.le.trans hnq)) (y - x)).trans
        (quadratic_decay_recenter hC hD (abs_le.mpr ⟨by linarith [hy.1],
          by linarith [hy.2]⟩)))
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ hM
  calc
    _ ≤ ∑ k ∈ Finset.range n, ‖analyticDividedDifference (finiteNodeSequence nodes) k f‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
        (fun _ _ _ => norm_nonneg _)
    _ = _ := (Fin.sum_univ_eq_sum_range _ n).symm

/-- A uniform adjacent-gap bound bounds every actual group relative to its
first node. This constant is independent of its position and internal gaps. -/
theorem IndexedSourceBlock.nodes_distance_first_le
    {b : ℤ → Bool} {anchor : ℤ} (P : IndexedSourceBlock b anchor)
    (Λ : TwoSidedCarrier) {q : ℕ} {H : ℝ} (_hH : 0 ≤ H) (hsize : P.size ≤ q)
    (hupper : ∀ j, Λ (j + 1) ≤ Λ j + H) (j : Fin P.size) :
    |Λ (P.index j) - Λ P.first| ≤ (q : ℝ) * H := by
  have hnat (n : ℕ) : Λ (P.first + n) ≤ Λ P.first + (n : ℝ) * H := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hu := hupper (P.first + n)
      have heq : P.first + (n + 1 : ℕ) = (P.first + n) + 1 := by omega
      rw [heq]
      push_cast
      linarith
  have hlo : Λ P.first ≤ Λ (P.index j) := Λ.strictMono.monotone (P.index_mem j).1
  have hhi : Λ (P.index j) ≤ Λ (P.first + q) :=
    Λ.strictMono.monotone (by have := (P.index_mem j).2; omega)
  rw [abs_of_nonneg (sub_nonneg.mpr hlo)]
  linarith [hnat q]

/-- Actual products add angular exponential types. The radial constants are
allowed to vary with epsilon, as in the retained Bernstein class. -/
theorem exponentialType_mul {F G : ℂ → ℂ} {τ σ : ℝ}
    (hF : ∀ ε > 0, ∃ C > 0, ∀ z, ‖F z‖ ≤ C * Real.exp ((τ + ε) * ‖z‖))
    (hG : ∀ ε > 0, ∃ C > 0, ∀ z, ‖G z‖ ≤ C * Real.exp ((σ + ε) * ‖z‖)) :
    ∀ ε > 0, ∃ C > 0, ∀ z, ‖F z * G z‖ ≤ C * Real.exp ((τ + σ + ε) * ‖z‖) := by
  intro ε hε
  obtain ⟨C, hC, hCF⟩ := hF (ε / 2) (half_pos hε)
  obtain ⟨D, hD, hDG⟩ := hG (ε / 2) (half_pos hε)
  refine ⟨C * D, mul_pos hC hD, ?_⟩
  intro z
  rw [norm_mul]
  calc
    _ ≤ (C * Real.exp ((τ + ε / 2) * ‖z‖)) *
        (D * Real.exp ((σ + ε / 2) * ‖z‖)) :=
      mul_le_mul (hCF z) (hDG z) (norm_nonneg _) (by positivity)
    _ = _ := by rw [show (τ + σ + ε) * ‖z‖ =
        (τ + ε / 2) * ‖z‖ + (σ + ε / 2) * ‖z‖ by ring, Real.exp_add]; ring

/-- A larger angular type bound follows by an actual monotone exponential
estimate, without changing the entire function. -/
theorem exponentialType_mono {F : ℂ → ℂ} {τ σ : ℝ} (hτσ : τ ≤ σ)
    (hF : ∀ ε > 0, ∃ C > 0, ∀ z, ‖F z‖ ≤ C * Real.exp ((τ + ε) * ‖z‖)) :
    ∀ ε > 0, ∃ C > 0, ∀ z, ‖F z‖ ≤ C * Real.exp ((σ + ε) * ‖z‖) := by
  intro ε hε
  obtain ⟨C, hC, hbound⟩ := hF ε hε
  exact ⟨C, hC, fun z => (hbound z).trans (by gcongr)⟩

/-- The integrable fourth-power translate weight arising after squaring the
quadratically decaying localized divided differences. -/
def bernsteinLocalizationWeight (c x : ℝ) : ℝ := (1 + |x - c|)⁻¹ ^ 4

/-- The localization weight is nonnegative at every point. -/
theorem bernsteinLocalizationWeight_nonneg (c x : ℝ) :
    0 ≤ bernsteinLocalizationWeight c x := by unfold bernsteinLocalizationWeight; positivity

/-- Every translated localization weight is continuous. -/
theorem continuous_bernsteinLocalizationWeight (c : ℝ) :
    Continuous (bernsteinLocalizationWeight c) := by
  unfold bernsteinLocalizationWeight
  apply Continuous.pow
  exact (continuous_const.add (continuous_id.sub continuous_const).abs).inv₀
    (fun x => ne_of_gt (show 0 < 1 + |x - c| by positivity))

/-- The localization weight has a finite genuine integral on the whole real
line, obtained from the proved Japanese-bracket integrability bound. -/
theorem integrable_bernsteinLocalizationWeight (c : ℝ) :
    Integrable (bernsteinLocalizationWeight c) := by
  have h : Integrable (fun x : ℝ => (1 + ‖x‖) ^ (-4 : ℝ)) :=
    integrable_one_add_norm (by norm_num)
  have hzero : Integrable (bernsteinLocalizationWeight 0) := by
    convert h using 1
    ext x
    rw [show (-4 : ℝ) = -(4 : ℕ) by norm_num, Real.rpow_neg, Real.rpow_natCast]
    · simp only [bernsteinLocalizationWeight, sub_zero, Real.norm_eq_abs, inv_pow]
    · positivity
  change Integrable (fun x : ℝ => (1 + |x - c|)⁻¹ ^ 4)
  simpa [bernsteinLocalizationWeight] using hzero.comp_sub_right c

/-- Every translated localization weight has exactly the same lower integral. -/
theorem lintegral_bernsteinLocalizationWeight (c : ℝ) :
    (∫⁻ x : ℝ, ENNReal.ofReal (bernsteinLocalizationWeight c x)) =
      ENNReal.ofReal (∫ x : ℝ, bernsteinLocalizationWeight 0 x) := by
  rw [ofReal_integral_eq_lintegral_ofReal (integrable_bernsteinLocalizationWeight 0)
    (Eventually.of_forall (bernsteinLocalizationWeight_nonneg 0))]
  simpa [bernsteinLocalizationWeight, sub_eq_add_neg] using
    lintegral_add_right_eq_self (μ := volume) (fun x : ℝ =>
      ENNReal.ofReal (bernsteinLocalizationWeight 0 x)) (-c)

/-- Tonelli integrates the actual weighted nonnegative sum, whether finite
or infinite. Thus no unproved summability is hidden in a real `tsum`. -/
theorem lintegral_tsum_bernsteinLocalizationWeight
    {ι : Type*} [Countable ι] (e : ι → ℝ≥0∞) (c : ι → ℝ) :
    (∫⁻ x : ℝ, ∑' i, e i * ENNReal.ofReal (bernsteinLocalizationWeight (c i) x)) =
      (∑' i, e i) * ENNReal.ofReal (∫ x : ℝ, bernsteinLocalizationWeight 0 x) := by
  rw [lintegral_tsum]
  · simp_rw [lintegral_const_mul _
      ((continuous_bernsteinLocalizationWeight _).measurable.ennreal_ofReal),
      lintegral_bernsteinLocalizationWeight]
    exact ENNReal.tsum_mul_right
  · intro i
    exact (measurable_const.mul
      ((continuous_bernsteinLocalizationWeight _).measurable.ennreal_ofReal)).aemeasurable

/-- An individual weighted nonnegative datum is bounded by the square root
of the actual extended sum of all squared weighted data, when that sum is finite. -/
theorem weighted_datum_le_sqrt_tsum
    {ι : Type*} (e : ι → ℝ) (c : ι → ℝ) (x : ℝ)
    (hfinite : (∑' i, ENNReal.ofReal (e i ^ 2) *
      ENNReal.ofReal (bernsteinLocalizationWeight (c i) x)) ≠ ⊤) (i : ι) :
    e i / (1 + |x - c i|) ^ 2 ≤ Real.sqrt
      (∑' i, ENNReal.ofReal (e i ^ 2) *
        ENNReal.ofReal (bernsteinLocalizationWeight (c i) x)).toReal := by
  apply Real.le_sqrt_of_sq_le
  have hterm := ENNReal.le_tsum (f := fun i => ENNReal.ofReal (e i ^ 2) *
    ENNReal.ofReal (bernsteinLocalizationWeight (c i) x)) i
  rw [← ENNReal.ofReal_mul (sq_nonneg _)] at hterm
  have h := (ENNReal.ofReal_le_iff_le_toReal hfinite).mp hterm
  apply le_trans _ h
  unfold bernsteinLocalizationWeight
  simp only [div_pow, inv_pow]
  norm_num [← pow_mul, div_eq_mul_inv]

/-- A translated localizer times a bounded entire function is still bounded
on the real axis. The bound uses the zeroth derivative decay estimate. -/
theorem bddAbove_range_norm_mul_localizer
    (F : ℂ → ℂ) (K : ℝ → ℂ) (E : ℂ → ℂ)
    (hreal : ∀ t : ℝ, E (t : ℂ) = K t)
    (hbounded : BddAbove (Set.range (fun t : ℝ => ‖F (t : ℂ)‖)))
    {C : ℝ} (hC : 0 ≤ C) (hK : ∀ t, ‖K t‖ ≤ C / (1 + |t|) ^ 2) (x : ℝ) :
    BddAbove (Set.range (fun t : ℝ => ‖F (t : ℂ) * E ((t : ℂ) - x)‖)) := by
  obtain ⟨M, hM⟩ := hbounded
  have hMnonneg : 0 ≤ M := (norm_nonneg _).trans (hM (Set.mem_range_self 0))
  refine ⟨M * C, ?_⟩
  rintro _ ⟨t, rfl⟩
  dsimp only
  rw [← Complex.ofReal_sub, hreal, norm_mul]
  have hKbound : ‖K (t - x)‖ ≤ C := (hK (t - x)).trans
    (div_le_self hC (by nlinarith [abs_nonneg (t - x)]))
  exact mul_le_mul (hM (Set.mem_range_self t)) hKbound (norm_nonneg _) hMnonneg

/-- Genuine class-uniform squared sampling for bounded entire functions.
The samples are the full-prefix data of the actual strict-gap source blocks.
Both sides use nonnegative integrals and sums, so no summability hypothesis or
convention on divergent real sums is concealed. The bandwidth enlargement is
strict and the constant is chosen before the carrier and the function. -/
theorem exists_uniform_clustered_bernstein_lintegral_bound
    {q : ℕ} {d Ω Ω' ρ r₀ : ℝ} (hd : 0 < d) (hΩ : 0 ≤ Ω)
    (hΩΩ' : Ω < Ω') (hρ : Ω' / Real.pi < ρ) (hr₀ : 0 < r₀) :
    ∃ A > 0, ∀ (Λ : TwoSidedCarrier), BoundedClusterOrder Λ.toLocallyFinite d q →
      (∀ t R, r₀ ≤ R → 2 * ρ * R ≤
        ((Λ.toLocallyFinite.carrier ∩ Ioo (t - R) (t + R)).ncard : ℝ)) →
      ∀ (P : ∀ anchor, IndexedSourceBlock (Λ.clusterBoundary d 0) anchor)
        (F : ℂ → ℂ), Differentiable ℂ F →
      (∀ ε > 0, ∃ C > 0, ∀ z, ‖F z‖ ≤ C * Real.exp ((Ω + ε) * ‖z‖)) →
      BddAbove (Set.range (fun x : ℝ => ‖F (x : ℂ)‖)) →
      (∫⁻ x : ℝ, ENNReal.ofReal (‖F (x : ℂ)‖ ^ 2)) ≤
        ENNReal.ofReal A * ∑' a : ℤ,
          ENNReal.ofReal (((P a).dataNorm Λ (fun x : ℝ => F (x : ℂ))) ^ 2) := by
  let α : ℝ := (Ω' - Ω) / 2
  have hα : 0 < α := by dsimp [α]; linarith
  obtain ⟨K, E, hE, hreal, hzero, _hradial, htypeE, hdecay⟩ :=
    exists_entire_schwartz_localizer hα
  obtain ⟨C, hC, hCbound⟩ := hdecay q
  have hΩ' : 0 ≤ Ω' := hΩ.trans hΩΩ'.le
  obtain ⟨S, hS, hsup⟩ := exists_uniform_clustered_bernstein_sup_bound
    (q := q) hd hΩ' hρ hr₀
  let D₀ : ℝ := (q : ℝ) * (2 * r₀)
  have hD₀ : 0 ≤ D₀ := by dsimp [D₀]; positivity
  let L : ℝ := C * (1 + D₀) ^ 2
  have hL : 0 < L := by dsimp [L]; positivity
  let Q : ℝ := (S * L) ^ 2
  have hQ : 0 < Q := by dsimp [Q]; positivity
  let I : ℝ := ∫ x : ℝ, bernsteinLocalizationWeight 0 x
  have hI : 0 ≤ I := integral_nonneg (bernsteinLocalizationWeight_nonneg 0)
  refine ⟨Q * (I + 1), by positivity, ?_⟩
  intro Λ hcluster hcounts P F hF htypeF hbounded
  let e : ℤ → ℝ := fun a => (P a).dataNorm Λ (fun x : ℝ => F (x : ℂ))
  let c : ℤ → ℝ := fun a => Λ (P a).first
  let T : ℝ → ℝ≥0∞ := fun x => ∑' a : ℤ,
    ENNReal.ofReal (e a ^ 2) * ENNReal.ofReal (bernsteinLocalizationWeight (c a) x)
  have he (a : ℤ) : 0 ≤ e a := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hsize (a : ℤ) : (P a).size ≤ q :=
    (P a).size_le_of_boundary_every_q_steps
      (Λ.clusterBoundary_every_q_steps hcluster 0)
  have hρpos : 0 < ρ := (div_nonneg hΩ' Real.pi_pos.le).trans_lt hρ
  have hupper := Λ.adjacent_gap_le_of_translated_count hρpos hr₀ hcounts
  have hpoint (x : ℝ) : ENNReal.ofReal (‖F (x : ℂ)‖ ^ 2) ≤
      ENNReal.ofReal Q * T x := by
    by_cases hfinite : T x = ⊤
    · rw [hfinite, ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr hQ))]
      exact le_top
    have hprefix (a : ℤ) (j : Fin (P a).size) :
        ‖analyticDividedDifference
          (finiteNodeSequence (fun i => Λ ((P a).index i))) j
          (fun y : ℝ => F (y : ℂ) * K (y - x))‖ ≤ L * Real.sqrt (T x).toReal := by
      have hinj : Function.Injective (fun i => Λ ((P a).index i)) :=
        Λ.strictMono.injective.comp (P a).index.injective
      have hb := norm_grouped_prefix_mul_localizer_le
        (fun i => Λ ((P a).index i)) hinj (hsize a) j (fun y : ℝ => F (y : ℂ))
        (K.smooth q) hC.le hD₀ hCbound
        ((P a).nodes_distance_first_le Λ (by positivity) (hsize a) hupper) x
      calc
        _ ≤ (L / (1 + |x - c a|) ^ 2) * e a := hb
        _ = L * (e a / (1 + |x - c a|) ^ 2) := by ring
        _ ≤ L * Real.sqrt (T x).toReal :=
          mul_le_mul_of_nonneg_left (weighted_datum_le_sqrt_tsum e c x hfinite a) hL.le
    let Fx : ℂ → ℂ := fun z => F z * E (z - (x : ℂ))
    have hFx : Differentiable ℂ Fx := by dsimp [Fx]; fun_prop
    have htypeTranslate : ∀ ε > 0, ∃ M > 0, ∀ z,
        ‖E (z - (x : ℂ))‖ ≤ M * Real.exp ((α + ε) * ‖z‖) := by
      simpa only [one_mul, Complex.ofReal_neg, sub_eq_add_neg] using
        exponentialType_const_mul_real_translate hα.le htypeE (-x) 1
    have htypeFx : ∀ ε > 0, ∃ M > 0, ∀ z,
        ‖Fx z‖ ≤ M * Real.exp ((Ω' + ε) * ‖z‖) :=
      exponentialType_mono (by dsimp [α]; linarith)
        (exponentialType_mul htypeF htypeTranslate)
    have hboundedFx : BddAbove (Set.range (fun t : ℝ => ‖Fx (t : ℂ)‖)) :=
      bddAbove_range_norm_mul_localizer F K E hreal hbounded hC.le
        (by simpa only [iteratedDeriv_zero] using hCbound 0 (Nat.zero_le q)) x
    have hFxreal (y : ℝ) : Fx (y : ℂ) = F (y : ℂ) * K (y - x) := by
      dsimp [Fx]
      rw [← Complex.ofReal_sub, hreal]
    have hx := hsup Λ hcluster hcounts P Fx hFx htypeFx hboundedFx
      (L * Real.sqrt (T x).toReal) (by positivity) (by
        intro a j
        simpa only [hFxreal] using hprefix a j) x
    rw [hFxreal, sub_self, hzero, mul_one] at hx
    have hsquare : ‖F (x : ℂ)‖ ^ 2 ≤ Q * (T x).toReal := by
      have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hx
      simpa only [Q, mul_pow, Real.sq_sqrt ENNReal.toReal_nonneg, mul_assoc] using hs
    calc
      _ ≤ ENNReal.ofReal (Q * (T x).toReal) := ENNReal.ofReal_le_ofReal hsquare
      _ = ENNReal.ofReal Q * T x := by
        rw [ENNReal.ofReal_mul hQ.le, ENNReal.ofReal_toReal hfinite]
  calc
    _ ≤ ∫⁻ x : ℝ, ENNReal.ofReal Q * T x := lintegral_mono hpoint
    _ = ENNReal.ofReal Q * ((∑' a : ℤ, ENNReal.ofReal (e a ^ 2)) *
        ENNReal.ofReal I) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      congr 1
      exact lintegral_tsum_bernsteinLocalizationWeight (fun a => ENNReal.ofReal (e a ^ 2)) c
    _ ≤ ENNReal.ofReal (Q * (I + 1)) * ∑' a : ℤ, ENNReal.ofReal (e a ^ 2) := by
      rw [ENNReal.ofReal_mul hQ.le]
      calc
        _ = (ENNReal.ofReal Q * ENNReal.ofReal I) *
            ∑' a : ℤ, ENNReal.ofReal (e a ^ 2) := by ac_rfl
        _ ≤ _ := by gcongr; linarith

/-- The actual integer-anchor energy is bounded by the canonical cluster
energy with precisely the two finite `q` losses: within-group Cauchy–Schwarz
and the proved number of anchors in that group. No carrier choice or data
summability is assumed. -/
theorem indexedSourceBlock_energy_le_canonical
    (Λ : TwoSidedCarrier) {d : ℝ} {q : ℕ}
    (hcluster : BoundedClusterOrder Λ.toLocallyFinite d q)
    (P : ∀ a, IndexedSourceBlock (Λ.clusterBoundary d 0) a) (f : ℝ → ℂ) :
    (∑' a : ℤ, ENNReal.ofReal (((P a).dataNorm Λ f) ^ 2)) ≤
      (q : ℝ≥0∞) ^ 2 * ∑' C : CanonicalClusterIndex Λ.toLocallyFinite d,
        ENNReal.ofReal (∑ j : Fin (hcluster.clusterSize C),
          ‖analyticDividedDifference (finiteNodeSequence (hcluster.realClusterNode C)) j f‖ ^ 2) := by
  let e : CanonicalClusterIndex Λ.toLocallyFinite d → ℝ≥0∞ := fun C =>
    ENNReal.ofReal (∑ j : Fin (hcluster.clusterSize C),
      ‖analyticDividedDifference (finiteNodeSequence (hcluster.realClusterNode C)) j f‖ ^ 2)
  calc
    _ ≤ ∑' a : ℤ, (q : ℝ≥0∞) * e (Λ.anchorClass d a) := by
      apply ENNReal.tsum_le_tsum
      intro a
      have h := ENNReal.ofReal_le_ofReal ((P a).dataNorm_sq_le_canonical_energy hcluster f)
      simpa only [ENNReal.ofReal_mul (Nat.cast_nonneg q), ENNReal.ofReal_natCast] using h
    _ = (q : ℝ≥0∞) * ∑' a : ℤ, e (Λ.anchorClass d a) := ENNReal.tsum_mul_left
    _ ≤ (q : ℝ≥0∞) * ((q : ℝ≥0∞) * ∑' C, e C) :=
      mul_le_mul_right (Λ.tsum_anchorClass_le hcluster e) _
    _ = _ := by rw [pow_two, mul_assoc]

/-- Canonical grouped sampling for bounded entire functions, with a uniform
constant for the geometric class and no artificial source-block choice in
the conclusion. Every datum is its actual analytic divided difference. -/
theorem exists_uniform_canonical_bernstein_lintegral_bound
    {q : ℕ} {d Ω Ω' ρ r₀ : ℝ} (hd : 0 < d) (hΩ : 0 ≤ Ω)
    (hΩΩ' : Ω < Ω') (hρ : Ω' / Real.pi < ρ) (hr₀ : 0 < r₀) :
    ∃ A > 0, ∀ (Λ : TwoSidedCarrier)
      (hcluster : BoundedClusterOrder Λ.toLocallyFinite d q),
      (∀ t R, r₀ ≤ R → 2 * ρ * R ≤
        ((Λ.toLocallyFinite.carrier ∩ Ioo (t - R) (t + R)).ncard : ℝ)) →
      ∀ (F : ℂ → ℂ), Differentiable ℂ F →
      (∀ ε > 0, ∃ C > 0, ∀ z, ‖F z‖ ≤ C * Real.exp ((Ω + ε) * ‖z‖)) →
      BddAbove (Set.range (fun x : ℝ => ‖F (x : ℂ)‖)) →
      (∫⁻ x : ℝ, ENNReal.ofReal (‖F (x : ℂ)‖ ^ 2)) ≤
        ENNReal.ofReal A * ∑' C : CanonicalClusterIndex Λ.toLocallyFinite d,
          ENNReal.ofReal (∑ j : Fin (hcluster.clusterSize C),
            ‖analyticDividedDifference (finiteNodeSequence (hcluster.realClusterNode C)) j
              (fun x : ℝ => F (x : ℂ))‖ ^ 2) := by
  obtain ⟨A, hA, hbound⟩ := exists_uniform_clustered_bernstein_lintegral_bound
    (q := q) hd hΩ hΩΩ' hρ hr₀
  refine ⟨A * ((q : ℝ) ^ 2 + 1), by positivity, ?_⟩
  intro Λ hcluster hcounts F hF htype hbounded
  let P : ∀ a, IndexedSourceBlock (Λ.clusterBoundary d 0) a := fun a =>
    Classical.choose (exists_indexedSourceBlock_of_boundary_every_q_steps
      (Λ.clusterBoundary_every_q_steps hcluster 0) a)
  have h := (hbound Λ hcluster hcounts P F hF htype hbounded).trans
    (mul_le_mul_right (indexedSourceBlock_energy_le_canonical Λ hcluster P
      (fun x : ℝ => F (x : ℂ))) (ENNReal.ofReal A))
  apply h.trans
  rw [ENNReal.ofReal_mul hA.le, ← mul_assoc]
  apply mul_le_mul_left
  apply mul_le_mul_right
  rw [← ENNReal.ofReal_natCast q, ← ENNReal.ofReal_pow (Nat.cast_nonneg q)]
  exact ENNReal.ofReal_le_ofReal (by linarith)

/-- The retained block-count class gives genuine grouped squared sampling
on the whole real line. The strict margin `Ω < Ω' < π N / B` is preserved;
there is no minimum internal gap, assumed lower bound, or cardinality-dependent
constant. Finiteness of the sample sum is not needed for the valid inequality. -/
theorem exists_uniform_canonical_bernstein_lintegral_bound_of_block_count
    {q N : ℕ} {d B Ω Ω' : ℝ} (hd : 0 < d) (hΩ : 0 ≤ Ω)
    (hΩΩ' : Ω < Ω') (hgap : Ω' / Real.pi < (N : ℝ) / B) :
    ∃ A > 0, ∀ (Λ : TwoSidedCarrier)
      (hcluster : BoundedClusterOrder Λ.toLocallyFinite d q),
      (∀ t R, 0 < R → (N : ℝ) * ((⌊2 * R / B⌋ : ℝ) - 2) ≤
        ((Λ.toLocallyFinite.carrier ∩ Ioo (t - R) (t + R)).ncard : ℝ)) →
      ∀ (F : ℂ → ℂ), Differentiable ℂ F →
      (∀ ε > 0, ∃ C > 0, ∀ z, ‖F z‖ ≤ C * Real.exp ((Ω + ε) * ‖z‖)) →
      BddAbove (Set.range (fun x : ℝ => ‖F (x : ℂ)‖)) →
      (∫⁻ x : ℝ, ENNReal.ofReal (‖F (x : ℂ)‖ ^ 2)) ≤
        ENNReal.ofReal A * ∑' C : CanonicalClusterIndex Λ.toLocallyFinite d,
          ENNReal.ofReal (∑ j : Fin (hcluster.clusterSize C),
            ‖analyticDividedDifference (finiteNodeSequence (hcluster.realClusterNode C)) j
              (fun x : ℝ => F (x : ℂ))‖ ^ 2) := by
  obtain ⟨ρ, hρlow, hρhigh⟩ := exists_between hgap
  obtain ⟨r₀, hr₀, hcount⟩ := uniform_translated_radial_count_of_block_count N hρhigh
  obtain ⟨A, hA, hbound⟩ := exists_uniform_canonical_bernstein_lintegral_bound
    (q := q) hd hΩ hΩΩ' hρlow hr₀
  exact ⟨A, hA, fun Λ hcluster hblock => hbound Λ hcluster (hcount Λ hblock)⟩

end

end MeyerGeneralProblem
