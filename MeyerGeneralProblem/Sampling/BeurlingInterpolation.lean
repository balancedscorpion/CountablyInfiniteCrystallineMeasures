module

public import MeyerGeneralProblem.Sampling.BeurlingWindow
public import MeyerGeneralProblem.Sampling.FourierRectangle
public import Mathlib.Data.Finset.Sort
import all Mathlib.Data.Finset.Sort
public import Mathlib.Order.Interval.Finset.Fin
import all Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Data.Nat.ModEq
import all Mathlib.Data.Nat.ModEq
public import Mathlib.Analysis.Convex.Integral
import all Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.Mul
import all Mathlib.Analysis.Convex.Mul

@[expose] public section

/-!
# Sharp-density geometry and Haraux frequency augmentation

The actual upper uniform Beurling density gives a uniform finite partition
into separated families.  The sum of the legal Ingham half-widths is strictly
less than the requested half-width.  All constants and the number of colours
are independent of the finite subfamily.

The actual averaged-shift operator is identified with its sinc multiplier,
controlled by Jensen and Fubini, and used to prove uniform one-frequency
augmentation.  This is the geometric and local analytic part of the elementary
Ingham--Beurling route.  It does not infer a lower Riesz inequality for a union
from the lower inequalities of its parts: that implication still needs the
support-controlled biorthogonal convolution and smoothing argument.
-/

namespace MeyerGeneralProblem

open MeasureTheory

noncomputable section

/-- A strict upper density bound supplies a fixed-length window cap whose
count-to-length ratio retains the same strict threshold. -/
theorem exists_uniform_windowCap_of_upperDensity_lt
    (S : LocallyFiniteCarrier) {c : ℝ} (hc : 0 < c)
    (hS : upperUniformBeurlingDensity S < ENNReal.ofReal c) :
    ∃ N : ℕ, 0 < N ∧ ∃ L : ℝ, 0 < L ∧ (N : ℝ) < c * L ∧
      ∀ x : ℝ, windowCount S x L ≤ N := by
  obtain ⟨ε, hε, L₀, hL₀, hbound⟩ :=
    (uniformUpperDensityLT_iff_upperUniformBeurlingDensity_lt S hc.le).2 hS
  let L : ℝ := max L₀ (3 / ε)
  have hL : 0 < L := hL₀.trans_le (le_max_left _ _)
  have hr : 0 ≤ c - ε := by
    have hb := hbound L₀ le_rfl 0
    have hn : (0 : ℝ) ≤ windowCount S 0 L₀ := Nat.cast_nonneg _
    nlinarith
  have hεL : 3 ≤ ε * L := by
    have h := le_max_right L₀ (3 / ε)
    have h' := (div_le_iff₀ hε).1 h
    nlinarith
  let N : ℕ := ⌈(c - ε) * L⌉₊ + 1
  refine ⟨N, Nat.succ_pos _, L, hL, ?_, ?_⟩
  · have hceil := Nat.ceil_lt_add_one (mul_nonneg hr hL.le)
    dsimp [N]
    push_cast
    nlinarith
  · intro x
    have hcount := (hbound L (le_max_left _ _) x).trans (Nat.le_ceil _)
    have hnat : windowCount S x L ≤ ⌈(c - ε) * L⌉₊ := by exact_mod_cast hcount
    exact hnat.trans (Nat.le_succ _)

/-- At most `N` points per half-open window of length `L` forces an `N`-step
gap of at least `L` in every finite increasing subfamily. -/
theorem ordered_gap_of_uniform_windowCap
    {S : LocallyFiniteCarrier} {N : ℕ} {L : ℝ}
    (hcap : ∀ x : ℝ, windowCount S x L ≤ N)
    {n : ℕ} (f : Fin n → ℝ) (hf : StrictMono f)
    (hmem : ∀ i, f i ∈ S.carrier) {i j : Fin n}
    (hij : i < j) (hN : N ≤ j.val - i.val) :
    L ≤ f j - f i := by
  classical
  by_contra hnot
  have hshort : f j < f i + L := by linarith
  let F : Finset ℝ := (Finset.Icc i j).image f
  have hsub : (F : Set ℝ) ⊆ S.carrier ∩ Set.Ico (f i) (f i + L) := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hx
    rcases Finset.mem_Icc.1 hk with ⟨hik, hkj⟩
    exact ⟨hmem k, hf.monotone hik, (hf.monotone hkj).trans_lt hshort⟩
  have hcard : F.card = j.val + 1 - i.val := by
    rw [Finset.card_image_of_injective _ hf.injective]
    exact Fin.card_Icc i j
  have hle : F.card ≤ windowCount S (f i) L := by
    simpa [windowCount] using Set.ncard_le_ncard hsub (S.finite_window (f i) L)
  have := hle.trans (hcap (f i))
  rw [hcard] at this
  have hi : i.val < j.val := hij
  omega

/-- Every finite subcarrier of a uniformly capped carrier admits an `N`-colour
partition whose distinct same-colour points are separated by `L`. -/
theorem exists_finite_colouring_of_uniform_windowCap
    {S : LocallyFiniteCarrier} {N : ℕ} (hN : 0 < N) {L : ℝ}
    (hcap : ∀ x : ℝ, windowCount S x L ≤ N)
    (F : Finset ℝ) (hF : ∀ x ∈ F, x ∈ S.carrier) :
    ∃ colour : F → Fin N, ∀ x y : F, colour x = colour y → x ≠ y →
      L ≤ |(x : ℝ) - y| := by
  classical
  let order : Fin F.card ≃o F := F.orderIsoOfFin rfl
  let colour : F → Fin N := fun x => ⟨(order.symm x).val % N, Nat.mod_lt _ hN⟩
  have hforward (x y : F) (hxy : x < y) (hcol : colour x = colour y) :
      L ≤ (y : ℝ) - x := by
    have hij : order.symm x < order.symm y := order.symm.strictMono hxy
    have hmod : (order.symm x).val ≡ (order.symm y).val [MOD N] :=
      congrArg Fin.val hcol
    have hstep : N ≤ (order.symm y).val - (order.symm x).val :=
      Nat.le_of_dvd (Nat.sub_pos_of_lt hij) hmod.dvd'
    have h := ordered_gap_of_uniform_windowCap hcap
      (F.orderEmbOfFin rfl) (F.orderEmbOfFin rfl).strictMono
      (fun i => hF _ (F.orderEmbOfFin_mem rfl i)) hij hstep
    simpa only [← Finset.coe_orderIsoOfFin_apply, order, OrderIso.apply_symm_apply] using h
  refine ⟨colour, fun x y hcol hxy => ?_⟩
  rcases lt_or_gt_of_ne hxy with hlt | hgt
  · have hlt' : (x : ℝ) < y := hlt
    rw [abs_sub_comm, abs_of_pos (sub_pos.mpr hlt')]
    exact hforward x y hlt hcol
  · have hgt' : (y : ℝ) < x := hgt
    rw [abs_of_pos (sub_pos.mpr hgt')]
    exact hforward y x hgt hcol.symm

/-- Sharp-density finite partition certificate: each colour has a genuine
proved Ingham lower bound on `[-b,b]`, and the total half-width `N*b` is
strictly less than `a`.  This does not claim a lower bound for their union. -/
theorem exists_finite_ingham_partition_of_upperDensity_lt
    (S : LocallyFiniteCarrier) {a : ℝ} (ha : 0 < a)
    (hS : upperUniformBeurlingDensity S < ENNReal.ofReal (2 * a)) :
    ∃ N : ℕ, 0 < N ∧ ∃ L b A : ℝ,
      0 < L ∧ 0 < b ∧ 0 < A ∧ (N : ℝ) * b < a ∧
      ∀ (F : Finset ℝ), (∀ x ∈ F, x ∈ S.carrier) →
        ∃ colour : F → Fin N, ∀ k : Fin N,
          HasFourierWindowLowerBound
            (fun x : {x : F // colour x = k} => (x.val : ℝ)) b A := by
  obtain ⟨N, hN, L, hL, hratio, hcap⟩ :=
    exists_uniform_windowCap_of_upperDensity_lt S (by positivity : 0 < 2 * a) hS
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hbudget : 1 / (2 * L) < a / N := by
    apply (div_lt_div_iff₀ (by positivity) hNr).2
    nlinarith
  obtain ⟨b, hblo, hbhi⟩ := exists_between hbudget
  have hb : 0 < b := (by positivity : (0 : ℝ) < 1 / (2 * L)).trans hblo
  have hgap : 1 < 2 * b * L := by
    have h := (div_lt_iff₀ (by positivity : 0 < 2 * L)).1 hblo
    nlinarith
  refine ⟨N, hN, L, b, cosineInghamFloorFactor b L, hL, hb,
    cosineInghamFloorFactor_pos hb hgap, ?_, ?_⟩
  · have h := (lt_div_iff₀ hNr).1 hbhi
    nlinarith
  · intro F hF
    obtain ⟨colour, hcolour⟩ := exists_finite_colouring_of_uniform_windowCap hN hcap F hF
    refine ⟨colour, fun k => ?_⟩
    apply hasFourierWindowLowerBound_of_cosineIngham _ hb hgap
    intro x y hxy
    exact hcolour x.val y.val (x.property.trans y.property.symm)
      (fun heq => hxy (Subtype.ext heq))

/-- Away from its zero argument the real sinc function is strictly below
one, which makes the averaged-shift frequency-removal multiplier positive. -/
theorem sinc_lt_one_of_ne_zero {t : ℝ} (ht : t ≠ 0) : Real.sinc t < 1 := by
  rcases lt_or_gt_of_ne ht with hneg | hpos
  · rw [← Real.sinc_neg t, Real.sinc_of_ne_zero (neg_ne_zero.mpr ht)]
    exact (div_lt_one (neg_pos.mpr hneg)).2 (Real.sin_lt (neg_pos.mpr hneg))
  · rw [Real.sinc_of_ne_zero ht]
    exact (div_lt_one hpos).2 (Real.sin_lt hpos)

/-- Positive separation gives a uniform positive lower bound for the sinc
defect, including frequencies arbitrarily far from the removed frequency. -/
theorem exists_pos_le_one_sub_sinc_of_abs_ge {d : ℝ} (hd : 0 < d) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ t : ℝ, d ≤ |t| → κ ≤ 1 - Real.sinc t := by
  obtain ⟨κ, hκ, hcompact⟩ := isCompact_Icc.exists_forall_le'
    (f := fun t : ℝ => 1 - Real.sinc t)
    ((continuous_const.sub Real.continuous_sinc).continuousOn)
    (a := 0) (fun t (ht : t ∈ Set.Icc d 2) =>
      sub_pos.mpr (sinc_lt_one_of_ne_zero (hd.trans_le ht.1).ne'))
  refine ⟨min κ (1 / 2), lt_min hκ (by norm_num), fun t ht => ?_⟩
  have ht0 : t ≠ 0 := by
    intro heq
    simp only [heq, abs_zero] at ht
    linarith
  by_cases hsmall : |t| ≤ 2
  · have hsinc : Real.sinc |t| = Real.sinc t := by
      rcases le_or_gt 0 t with hpos | hneg
      · rw [abs_of_nonneg hpos]
      · rw [abs_of_neg hneg, Real.sinc_neg]
    have h := hcompact |t| ⟨ht, hsmall⟩
    rw [hsinc] at h
    exact (min_le_left _ _).trans h
  · have hlarge : 2 ≤ |t| := le_of_lt (lt_of_not_ge hsmall)
    have hinv : |t|⁻¹ ≤ (1 / 2 : ℝ) := by
      simpa only [one_div] using inv_anti₀ (by norm_num : (0 : ℝ) < 2) hlarge
    have h := (Real.sinc_le_inv_abs ht0).trans hinv
    exact (min_le_right _ _).trans (by linarith)

/-- The real coefficient multiplier of Haraux's averaged-shift removal of
the frequency `ω`, with averaging over the actual interval `[-r,r]`. -/
def harauxMultiplier (r ω t : ℝ) : ℝ :=
  1 - Real.sinc (2 * Real.pi * (t - ω) * r)

/-- The selected frequency is exactly removed, not merely attenuated. -/
@[simp]
theorem harauxMultiplier_self (r ω : ℝ) : harauxMultiplier r ω ω = 0 := by
  simp [harauxMultiplier]

/-- Under positive separation from the selected frequency, the actual
averaged-shift multiplier has a uniform positive lower bound. -/
theorem exists_pos_le_harauxMultiplier {r d : ℝ} (hr : 0 < r) (hd : 0 < d) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ ω t : ℝ, d ≤ |t - ω| → κ ≤ harauxMultiplier r ω t := by
  obtain ⟨κ, hκ, hbound⟩ :=
    exists_pos_le_one_sub_sinc_of_abs_ge
      (d := 2 * Real.pi * d * r) (by positivity)
  refine ⟨κ, hκ, fun ω t ht => hbound _ ?_⟩
  simp only [abs_mul, abs_of_pos hr, abs_of_pos Real.pi_pos, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  nlinarith [mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ 2 * Real.pi * r)]

/-- Actual averaged-shift frequency removal on a complex-valued function. -/
def harauxFrequencyRemoval (r ω : ℝ) (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  f t - (2 * r : ℂ)⁻¹ *
    ∫ u : ℝ in Set.Icc (-r) r, gramPhase (-ω) u * f (t + u)

/-- Applying the actual averaged-shift operator to a finite exponential
polynomial multiplies each coefficient by its explicit sinc defect. -/
theorem harauxFrequencyRemoval_gramFourierPolynomial
    {n : ℕ} (s : Fin n → ℝ) (c : Fin n → ℂ)
    {r : ℝ} (hr : 0 < r) (ω t : ℝ) :
    harauxFrequencyRemoval r ω (gramFourierPolynomial s c) t =
      gramFourierPolynomial s (fun i => (harauxMultiplier r ω (s i) : ℂ) * c i) t := by
  have hpoint (u : ℝ) :
      gramPhase (-ω) u * gramFourierPolynomial s c (t + u) =
        ∑ i, (c i * gramPhase (s i) t) * gramPhase (s i - ω) u := by
    simp only [gramFourierPolynomial, Finset.mul_sum, gramPhase_add_right,
      sub_eq_add_neg, gramPhase_add]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hint (i : Fin n) : IntegrableOn
      (fun u : ℝ => (c i * gramPhase (s i) t) * gramPhase (s i - ω) u)
      (Set.Icc (-r) r) := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    unfold gramPhase
    fun_prop
  unfold harauxFrequencyRemoval
  simp_rw [hpoint]
  rw [integral_finsetSum _ (fun i hi => hint i)]
  simp_rw [integral_const_mul]
  change gramFourierPolynomial s c t - (2 * r : ℂ)⁻¹ *
    (∑ i, (c i * gramPhase (s i) t) * inghamWindowKernel r (s i - ω)) = _
  simp_rw [inghamWindowKernel_eq_sinc hr.le]
  unfold gramFourierPolynomial
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  unfold harauxMultiplier
  push_cast
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  field_simp [hrC]

private theorem norm_interval_average_sq_le {r : ℝ} (hr : 0 < r)
    (f : ℝ → ℂ) (hf : Continuous f) :
    ‖(2 * r : ℂ)⁻¹ * ∫ u : ℝ in Set.Icc (-r) r, f u‖ ^ 2 ≤
      (2 * r)⁻¹ * ∫ u : ℝ in Set.Icc (-r) r, ‖f u‖ ^ 2 := by
  have hconv : ConvexOn ℝ Set.univ (fun z : ℂ => ‖z‖ ^ 2) :=
    convexOn_univ_norm.pow (fun _ _ => norm_nonneg _) 2
  have hzero : volume (Set.Icc (-r) r) ≠ 0 := by
    rw [Real.volume_Icc, ne_eq, ENNReal.ofReal_eq_zero]
    linarith
  have htop : volume (Set.Icc (-r) r) ≠ ⊤ := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have hj := hconv.map_set_average_le (by fun_prop) isClosed_univ hzero htop
    (Filter.Eventually.of_forall (fun u => Set.mem_univ (f u)))
    (hf.continuousOn.integrableOn_compact isCompact_Icc)
    ((hf.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc)
  simp only [setAverage_eq, Real.volume_real_Icc_of_le (by linarith : -r ≤ r),
    sub_neg_eq_add, ← two_mul, Complex.real_smul, Complex.ofReal_inv,
    Complex.ofReal_mul, Complex.ofReal_ofNat, smul_eq_mul] at hj
  exact hj

/-- Jensen's inequality gives the pointwise energy estimate for the actual
averaged-shift frequency-removal operator. -/
theorem norm_harauxFrequencyRemoval_sq_le
    {r : ℝ} (hr : 0 < r) (ω : ℝ) (f : ℝ → ℂ) (hf : Continuous f) (t : ℝ) :
    ‖harauxFrequencyRemoval r ω f t‖ ^ 2 ≤ 2 * ‖f t‖ ^ 2 +
      2 * (2 * r)⁻¹ * ∫ u : ℝ in Set.Icc (-r) r, ‖f (t + u)‖ ^ 2 := by
  let z : ℂ := (2 * r : ℂ)⁻¹ *
    ∫ u : ℝ in Set.Icc (-r) r, gramPhase (-ω) u * f (t + u)
  have hz : ‖z‖ ^ 2 ≤
      (2 * r)⁻¹ * ∫ u : ℝ in Set.Icc (-r) r, ‖f (t + u)‖ ^ 2 := by
    have h := norm_interval_average_sq_le hr
      (fun u => gramPhase (-ω) u * f (t + u)) (by unfold gramPhase; fun_prop)
    simpa only [z, Complex.norm_mul, norm_gramPhase, one_mul] using h
  have hnorm := norm_sub_le (f t) z
  have hsquare := (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hnorm
  change ‖f t - z‖ ^ 2 ≤ _
  nlinarith [sq_nonneg (‖f t‖ - ‖z‖)]

private theorem integral_shifted_norm_sq_le {b r : ℝ}
    (hb : 0 ≤ b) (_hr : 0 ≤ r) (f : ℝ → ℂ) (hf : Continuous f)
    {u : ℝ} (hu : u ∈ Set.Icc (-r) r) :
    (∫ t : ℝ in Set.Icc (-b) b, ‖f (t + u)‖ ^ 2) ≤
      ∫ t : ℝ in Set.Icc (-(b + r)) (b + r), ‖f t‖ ^ 2 := by
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -b ≤ b),
    intervalIntegral.integral_comp_add_right (fun t : ℝ => ‖f t‖ ^ 2) u,
    intervalIntegral.integral_of_le (by linarith : -b + u ≤ b + u),
    ← integral_Icc_eq_integral_Ioc]
  apply setIntegral_mono_set ((hf.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc)
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
  apply Filter.Eventually.of_forall
  intro t ht
  constructor <;> linarith [ht.1, ht.2, hu.1, hu.2]

/-- The energy of the averaged-shift removal on `[-b,b]` is at most four
times the original energy on `[-(b+r),b+r]`.  The bound does not depend on
the number or the values of the frequencies. -/
theorem integral_harauxFrequencyRemoval_sq_le
    {n : ℕ} (s : Fin n → ℝ) (c : Fin n → ℂ)
    {b r : ℝ} (hb : 0 ≤ b) (hr : 0 < r) (ω : ℝ) :
    (∫ t : ℝ in Set.Icc (-b) b,
      ‖harauxFrequencyRemoval r ω (gramFourierPolynomial s c) t‖ ^ 2) ≤
      4 * ∫ t : ℝ in Set.Icc (-(b + r)) (b + r),
        ‖gramFourierPolynomial s c t‖ ^ 2 := by
  let f := gramFourierPolynomial s c
  have hf : Continuous f := by unfold f gramFourierPolynomial gramPhase; fun_prop
  have hrem : Continuous (harauxFrequencyRemoval r ω f) := by
    have heq : harauxFrequencyRemoval r ω f =
        gramFourierPolynomial s (fun i => (harauxMultiplier r ω (s i) : ℂ) * c i) :=
      funext (harauxFrequencyRemoval_gramFourierPolynomial s c hr ω)
    rw [heq]
    unfold gramFourierPolynomial gramPhase
    fun_prop
  have hprod : Integrable (fun p : ℝ × ℝ => ‖f (p.1 + p.2)‖ ^ 2)
      ((volume.restrict (Set.Icc (-b) b)).prod (volume.restrict (Set.Icc (-r) r))) := by
    rw [Measure.prod_restrict]
    apply ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    exact ((hf.comp (continuous_fst.add continuous_snd)).norm.pow 2).continuousOn
  let E : ℝ := ∫ t : ℝ in Set.Icc (-(b + r)) (b + r), ‖f t‖ ^ 2
  have hbase : (∫ t : ℝ in Set.Icc (-b) b, ‖f t‖ ^ 2) ≤ E := by
    simpa only [add_zero] using integral_shifted_norm_sq_le hb hr.le f hf
      (u := 0) (by constructor <;> linarith)
  have hdouble :
      (∫ t : ℝ in Set.Icc (-b) b, ∫ u : ℝ in Set.Icc (-r) r,
        ‖f (t + u)‖ ^ 2) ≤ (2 * r) * E := by
    rw [integral_integral_swap hprod]
    calc
      _ ≤ ∫ _u : ℝ in Set.Icc (-r) r, E := by
        apply setIntegral_mono_on hprod.integral_prod_right (integrable_const _) measurableSet_Icc
        intro u hu
        exact integral_shifted_norm_sq_le hb hr.le f hf hu
      _ = (2 * r) * E := by
        rw [setIntegral_const, Real.volume_real_Icc_of_le (by linarith : -r ≤ r)]
        simp only [smul_eq_mul]
        ring
  have hbound :
      (∫ t : ℝ in Set.Icc (-b) b, ‖harauxFrequencyRemoval r ω f t‖ ^ 2) ≤
        2 * (∫ t : ℝ in Set.Icc (-b) b, ‖f t‖ ^ 2) +
          2 * (2 * r)⁻¹ * (∫ t : ℝ in Set.Icc (-b) b,
            ∫ u : ℝ in Set.Icc (-r) r, ‖f (t + u)‖ ^ 2) := by
    calc
      _ ≤ ∫ t : ℝ in Set.Icc (-b) b,
          2 * ‖f t‖ ^ 2 + 2 * (2 * r)⁻¹ *
            ∫ u : ℝ in Set.Icc (-r) r, ‖f (t + u)‖ ^ 2 := by
        apply integral_mono ((hrem.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc)
          (((hf.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc).const_mul 2 |>.add
            (hprod.integral_prod_left.const_mul _))
        intro t
        exact norm_harauxFrequencyRemoval_sq_le hr ω f hf t
      _ = _ := by
        rw [integral_add (f := fun t : ℝ => 2 * ‖f t‖ ^ 2)
          (g := fun t : ℝ => 2 * (2 * r)⁻¹ *
            ∫ u : ℝ in Set.Icc (-r) r, ‖f (t + u)‖ ^ 2)
          (((hf.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc).const_mul 2)
          (hprod.integral_prod_left.const_mul (2 * (2 * r)⁻¹)),
          integral_const_mul, integral_const_mul]
  have hmul := mul_le_mul_of_nonneg_left hdouble
    (by positivity : 0 ≤ 2 * (2 * r)⁻¹)
  have hcancel : 2 * (2 * r)⁻¹ * ((2 * r) * E) = 2 * E := by
    field_simp
  change _ ≤ 4 * E
  rw [hcancel] at hmul
  linarith

/-- Uniform finite Haraux augmentation.  Adding one frequency separated by
`d` preserves a lower inequality after any positive enlargement `r` of the
window.  The new constant depends only on `b,r,d,A,B`, not on the finite
family, its cardinality, or the added frequency.  The supplied lower and
upper bounds are actual exponential integral inequalities. -/
theorem exists_uniform_finite_lowerBound_insert_frequency
    {b r d A B : ℝ} (hb : 0 < b) (hr : 0 < r) (hd : 0 < d)
    (hA : 0 < A) (hB : 0 ≤ B) :
    ∃ A' : ℝ, 0 < A' ∧ ∀ (n : ℕ) (s : Fin n → ℝ) (ω : ℝ),
      (∀ i, d ≤ |s i - ω|) →
      (∀ c : Fin n → ℂ, A * ∑ i, ‖c i‖ ^ 2 ≤
        ∫ t : ℝ in Set.Icc (-b) b, ‖gramFourierPolynomial s c t‖ ^ 2) →
      (∀ c : Fin n → ℂ,
        (∫ t : ℝ in Set.Icc (-(b + r)) (b + r), ‖gramFourierPolynomial s c t‖ ^ 2) ≤
          B * ∑ i, ‖c i‖ ^ 2) →
      ∀ (c₀ : ℂ) (c : Fin n → ℂ),
        A' * (‖c₀‖ ^ 2 + ∑ i, ‖c i‖ ^ 2) ≤
          ∫ t : ℝ in Set.Icc (-(b + r)) (b + r),
            ‖c₀ * gramPhase ω t + gramFourierPolynomial s c t‖ ^ 2 := by
  obtain ⟨κ, hκ, hmult⟩ := exists_pos_le_harauxMultiplier hr hd
  let P := A * κ ^ 2
  let V := 2 * (b + r)
  let D := 4 * V + 2 * P + 8 * B
  have hP : 0 < P := mul_pos hA (sq_pos_of_pos hκ)
  have hV : 0 < V := by dsimp [V]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨V * P / D, div_pos (mul_pos hV hP) hD, ?_⟩
  intro n s ω hsep hlower hupper c₀ c
  let f : ℝ → ℂ := fun t => c₀ * gramPhase ω t + gramFourierPolynomial s c t
  let E : ℝ := ∫ t : ℝ in Set.Icc (-(b + r)) (b + r), ‖f t‖ ^ 2
  let Q : ℝ := ∑ i, ‖c i‖ ^ 2
  have hf : Continuous f := by unfold f gramFourierPolynomial gramPhase; fun_prop
  have hpoly (t : ℝ) :
      gramFourierPolynomial (Fin.cases ω s) (Fin.cases c₀ c) t = f t := by
    simp only [gramFourierPolynomial, Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ, f]
  have hremoved (t : ℝ) : harauxFrequencyRemoval r ω f t =
      gramFourierPolynomial s (fun i => (harauxMultiplier r ω (s i) : ℂ) * c i) t := by
    have heq : f = gramFourierPolynomial (Fin.cases ω s) (Fin.cases c₀ c) :=
      (funext hpoly).symm
    rw [heq, harauxFrequencyRemoval_gramFourierPolynomial _ _ hr]
    simp only [gramFourierPolynomial, Fin.sum_univ_succ, Fin.cases_zero,
      Fin.cases_succ, harauxMultiplier_self, Complex.ofReal_zero, zero_mul, zero_add]
  have hcoeff : κ ^ 2 * Q ≤
      ∑ i, ‖(harauxMultiplier r ω (s i) : ℂ) * c i‖ ^ 2 := by
    rw [show κ ^ 2 * Q = ∑ i, κ ^ 2 * ‖c i‖ ^ 2 by rw [Finset.mul_sum]]
    apply Finset.sum_le_sum
    intro i hi
    have hm := hmult ω (s i) (hsep i)
    rw [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    exact mul_le_mul_of_nonneg_right
      ((sq_le_sq₀ hκ.le (hκ.le.trans hm)).2 hm) (sq_nonneg _)
  have htail : P * Q ≤ 4 * E := by
    calc
      _ ≤ A * ∑ i, ‖(harauxMultiplier r ω (s i) : ℂ) * c i‖ ^ 2 := by
        dsimp [P]
        nlinarith [mul_le_mul_of_nonneg_left hcoeff hA.le]
      _ ≤ ∫ t : ℝ in Set.Icc (-b) b, ‖harauxFrequencyRemoval r ω f t‖ ^ 2 := by
        simpa only [hremoved] using hlower
          (fun i => (harauxMultiplier r ω (s i) : ℂ) * c i)
      _ ≤ 4 * E := by
        have h := integral_harauxFrequencyRemoval_sq_le
          (Fin.cases ω s) (Fin.cases c₀ c) hb.le hr ω
        simpa only [hpoly, (funext hpoly)] using h
  have hconstant : V * ‖c₀‖ ^ 2 ≤ 2 * E + 2 * B * Q := by
    have hpoint (t : ℝ) : ‖c₀‖ ^ 2 ≤
        2 * ‖f t‖ ^ 2 + 2 * ‖gramFourierPolynomial s c t‖ ^ 2 := by
      have hnorm : ‖c₀‖ ≤ ‖f t‖ + ‖gramFourierPolynomial s c t‖ := by
        have h := norm_sub_le (f t) (gramFourierPolynomial s c t)
        simpa only [f, add_sub_cancel_right, Complex.norm_mul, norm_gramPhase, mul_one] using h
      have hsquare := (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hnorm
      nlinarith [sq_nonneg (‖f t‖ - ‖gramFourierPolynomial s c t‖)]
    have hcf : Continuous (gramFourierPolynomial s c) := by
      unfold gramFourierPolynomial gramPhase
      fun_prop
    have hint := integral_mono (μ := volume.restrict (Set.Icc (-(b + r)) (b + r)))
      (integrable_const (‖c₀‖ ^ 2))
      ((((hf.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc).const_mul 2).add
        (((hcf.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc).const_mul 2)) hpoint
    simp only [Pi.add_apply, Pi.pow_apply] at hint
    rw [integral_add (f := fun t : ℝ => 2 * ‖f t‖ ^ 2)
      (g := fun t : ℝ => 2 * ‖gramFourierPolynomial s c t‖ ^ 2)
      (((hf.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc).const_mul 2)
      (((hcf.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc).const_mul 2),
      integral_const_mul, integral_const_mul, setIntegral_const,
      Real.volume_real_Icc_of_le (by linarith : -(b + r) ≤ b + r)] at hint
    simp only [smul_eq_mul] at hint
    have hu := hupper c
    change _ ≤ B * Q at hu
    change V * ‖c₀‖ ^ 2 ≤ 2 * E + 2 * B * Q
    dsimp [V, E] at *
    nlinarith
  have htailV := mul_le_mul_of_nonneg_left htail hV.le
  have htailB := mul_le_mul_of_nonneg_left htail (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hB)
  have hconstantP := mul_le_mul_of_nonneg_left hconstant hP.le
  change (V * P / D) * (‖c₀‖ ^ 2 + Q) ≤ E
  rw [div_mul_eq_mul_div, div_le_iff₀ hD]
  dsimp [D]
  nlinarith

/-- A separated finite family satisfying the exact cosine-Ingham threshold
can be augmented by any one frequency at positive distance `d`.  Both input
inequalities of the generic augmentation lemma are discharged here by the
proved Ingham and upper-large-sieve theorems. -/
theorem exists_uniform_finite_cosineIngham_insert_frequency
    {b r L d : ℝ} (hb : 0 < b) (hr : 0 < r) (hL : 0 < L) (hd : 0 < d)
    (hgap : 1 < 2 * b * L) :
    ∃ A' : ℝ, 0 < A' ∧ ∀ (n : ℕ) (s : Fin n → ℝ),
      PairwiseFrequencySeparated s L → ∀ ω : ℝ,
      (∀ i, d ≤ |s i - ω|) → ∀ (c₀ : ℂ) (c : Fin n → ℂ),
        A' * (‖c₀‖ ^ 2 + ∑ i, ‖c i‖ ^ 2) ≤
          ∫ t : ℝ in Set.Icc (-(b + r)) (b + r),
            ‖c₀ * gramPhase ω t + gramFourierPolynomial s c t‖ ^ 2 := by
  let B := fourierIntervalLargeSieveConstant * (2 * (b + r) + L⁻¹)
  have hB : 0 ≤ B := mul_nonneg fourierIntervalLargeSieveConstant_pos.le (by positivity)
  obtain ⟨A', hA', hbound⟩ := exists_uniform_finite_lowerBound_insert_frequency
    hb hr hd (cosineInghamFloorFactor_pos hb hgap) hB
  refine ⟨A', hA', fun n s hsep ω hω => hbound n s ω hω ?_ ?_⟩
  · exact finite_cosineIngham hb hgap s hsep
  · intro c
    have h := integral_norm_sq_le_interval_largeSieve hL
      (by linarith : -(b + r) ≤ b + r) s hsep c
    convert h using 1
    dsimp [B]
    congr 2
    ring

end

end MeyerGeneralProblem
