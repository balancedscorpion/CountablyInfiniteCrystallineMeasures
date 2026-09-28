module

public import MeyerGeneralProblem.Cardinal.Adaptive.CatalogueNonresonance
public import MeyerGeneralProblem.Cardinal.Adaptive.SectorSeparation
public import Mathlib.Analysis.SpecificLimits.Normed
import all Mathlib.Analysis.SpecificLimits.Normed

@[expose] public section

/-!
# Quantitative separation of actual reciprocal sectors

The fixed-atom comparison has a linear small-ball rate, including the dependent
forward/reciprocal pair at one coordinate. No independence between those two
labels is asserted. Actual atom counts are used for the global separation law.
-/

namespace MeyerGeneralProblem.Adaptive
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal

/-- Pairwise scalar distance bounds control actual Lebesgue measure. -/
theorem volume_le_of_pairwise_abs_le (S : Set ℝ) (D : ℝ)
    (h : ∀ x ∈ S, ∀ y ∈ S, |x-y| ≤ D) : volume S ≤ ENNReal.ofReal D := by
  apply Real.volume_le_diam S |>.trans
  apply Metric.ediam_le
  intro x hx y hy
  rw [edist_dist, Real.dist_eq]
  exact ENNReal.ofReal_le_ofReal (h x hx y hy)

/-- Both actual scalar maps have inverse Lipschitz constant at most four on [1,2]. -/
theorem scaleFactor_inverse_lipschitz (σ : ReciprocalSign) {x y : ℝ}
    (hx : x ∈ Icc 1 2) (hy : y ∈ Icc 1 2) :
    |x-y| ≤ 4*|scaleFactor σ x-scaleFactor σ y| := by
  cases σ with
  | forward => change |x-y| ≤ 4*|x-y|; nlinarith [abs_nonneg (x-y)]
  | reciprocal =>
    change |x-y| ≤ 4*|x⁻¹-y⁻¹|
    have hx0 : x ≠ 0 := by linarith [hx.1]
    have hy0 : y ≠ 0 := by linarith [hy.1]
    have heq : (x⁻¹-y⁻¹)*(x*y) = -(x-y) := by field_simp; ring
    have habs := congrArg abs heq
    rw [abs_mul, abs_neg, abs_of_nonneg (by nlinarith [hx.1, hy.1] : 0 ≤ x*y)] at habs
    have hxy : x*y ≤ 4 := by nlinarith [hx.1, hy.1, hx.2, hy.2]
    nlinarith [abs_nonneg (x⁻¹-y⁻¹)]

/-- Linear one-coordinate small-ball estimate, with its actual atom normalization. -/
theorem scaleFactor_atom_sublevel_le (σ : ReciprocalSign) (a b A u : ℝ)
    (hA : 0 < A) (ha : A ≤ |a|) (_hu : 0 < u) :
    scaleLaw {x | |scaleFactor σ x*a-b| < u} ≤ ENNReal.ofReal (8*u/A) := by
  unfold scaleLaw
  rw [Measure.restrict_apply₀, Set.inter_comm]
  · apply volume_le_of_pairwise_abs_le
    intro x hx y hy
    have hlip := scaleFactor_inverse_lipschitz σ hx.1 hy.1
    have htri := abs_sub (scaleFactor σ x*a-b) (scaleFactor σ y*a-b)
    have heq : (scaleFactor σ x*a-b)-(scaleFactor σ y*a-b) =
        (scaleFactor σ x-scaleFactor σ y)*a := by ring
    rw [heq, abs_mul] at htri
    apply (le_div_iff₀ hA).mpr
    have hbase : |scaleFactor σ x-scaleFactor σ y| *A ≤
        |scaleFactor σ x-scaleFactor σ y| *|a| := mul_le_mul_of_nonneg_left ha (abs_nonneg _)
    have hmul := mul_le_mul_of_nonneg_right hlip hA.le
    have hx2 : |scaleFactor σ x*a-b| < u := hx.2
    have hy2 : |scaleFactor σ y*a-b| < u := hy.2
    nlinarith
  · exact (measurableSet_lt (continuous_abs.measurable.comp
      (((measurable_scaleFactor σ).mul_const a).sub_const b)) measurable_const).nullMeasurableSet

/-- Genuine two-coordinate comparison probability, by conditioning under the actual product law. -/
theorem product_atom_sublevel_le (σ τ : ReciprocalSign) (a b A u : ℝ)
    (hA : 0 < A) (ha : A ≤ |a|) (hu : 0 < u) :
    (scaleLaw.prod scaleLaw) {z : ℝ × ℝ | |scaleFactor σ z.1*a-scaleFactor τ z.2*b| < u} ≤
      ENNReal.ofReal (8*u/A) := by
  have hm : MeasurableSet {z : ℝ × ℝ | |scaleFactor σ z.1*a-scaleFactor τ z.2*b| < u} :=
    measurableSet_lt (continuous_abs.measurable.comp
      ((((measurable_scaleFactor σ).comp measurable_fst).mul_const a).sub
        (((measurable_scaleFactor τ).comp measurable_snd).mul_const b))) measurable_const
  rw [Measure.prod_apply_symm hm]
  calc
    _ ≤ ∫⁻ _y, ENNReal.ofReal (8*u/A) ∂scaleLaw := by
      apply lintegral_mono
      intro y
      exact scaleFactor_atom_sublevel_le σ a (scaleFactor τ y*b) A u hA ha hu
    _ = _ := by simp

/-- Same-sign reciprocal pairs have a quantitative monotone difference on positive scales. -/
theorem reciprocal_pair_difference {a b x y : ℝ} (hab : 0 ≤ a*b)
    (hx : 0 < x) (hy : 0 < y) :
    |a| *|x-y| ≤ |(x*a-x⁻¹*b)-(y*a-y⁻¹*b)| := by
  have heq : (x*a-x⁻¹*b)-(y*a-y⁻¹*b) = (x-y)*(a+b/(x*y)) := by
    field_simp
    ring
  rw [heq, abs_mul]
  have hcoeff : |a| ≤ |a+b/(x*y)| := by
    by_cases ha : a = 0
    · simp [ha]
    · by_cases hap : 0 < a
      · have hb : 0 ≤ b := by nlinarith
        have hdiv : 0 ≤ b/(x*y) := by positivity
        rw [abs_of_pos hap, abs_of_nonneg (by positivity)]
        linarith
      · have han : a < 0 := lt_of_le_of_ne (le_of_not_gt hap) ha
        have hb : b ≤ 0 := by nlinarith
        have hdiv : b/(x*y) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hb (by positivity)
        rw [abs_of_neg han, abs_of_nonpos (by linarith)]
        linarith
  nlinarith [mul_le_mul_of_nonneg_right hcoeff (abs_nonneg (x-y))]

/-- Opposite-sign base atoms cannot approach one another through positive reciprocal scales. -/
theorem reciprocal_pair_opposite_sign {a b x : ℝ} (hab : a*b < 0) (hx : 1 ≤ x) :
    |a| ≤ |x*a-x⁻¹*b| := by
  have hxpos : 0 < x := by linarith
  by_cases hap : 0 ≤ a
  · have ha : 0 < a := lt_of_le_of_ne hap (by intro h; rw [← h, zero_mul] at hab; exact lt_irrefl _ hab)
    have hb : b < 0 := by nlinarith
    have hdiv : x⁻¹*b ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hxpos.le) hb.le
    rw [abs_of_pos ha, abs_of_nonneg (by nlinarith)]
    nlinarith
  · have ha : a < 0 := lt_of_not_ge hap
    have hb : 0 < b := by nlinarith
    have hdiv : 0 ≤ x⁻¹*b := mul_nonneg (inv_nonneg.mpr hxpos.le) hb.le
    rw [abs_of_neg ha, abs_of_nonpos (by nlinarith)]
    nlinarith

/-- Linear small-ball estimate for the dependent forward/reciprocal pair at one coordinate. -/
theorem same_coordinate_atom_sublevel_le (a b A u : ℝ) (hA : 0 < A)
    (ha : A ≤ |a|) (hu : 0 < u) :
    scaleLaw {x | |x*a-x⁻¹*b| < u} ≤ ENNReal.ofReal (8*u/A) := by
  by_cases hab : 0 ≤ a*b
  · unfold scaleLaw
    rw [Measure.restrict_apply₀, Set.inter_comm]
    · apply volume_le_of_pairwise_abs_le
      intro x hx y hy
      have hlip := reciprocal_pair_difference (x := x) (y := y) hab (by linarith [hx.1.1]) (by linarith [hy.1.1])
      have htri := abs_sub (x*a-x⁻¹*b) (y*a-y⁻¹*b)
      have hx2 : |x*a-x⁻¹*b| < u := hx.2
      have hy2 : |y*a-y⁻¹*b| < u := hy.2
      have hmul := mul_le_mul_of_nonneg_right ha (abs_nonneg (x-y))
      apply (le_div_iff₀ hA).mpr
      nlinarith
    · exact (measurableSet_lt (continuous_abs.measurable.comp
        ((measurable_id.mul_const a).sub (measurable_inv.mul_const b))) measurable_const).nullMeasurableSet
  · by_cases huA : u ≤ A
    · have hzero : scaleLaw {x | |x*a-x⁻¹*b| < u} = 0 := by
        apply measure_eq_zero_iff_ae_notMem.mpr
        filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
        intro hsmall
        have hlow := reciprocal_pair_opposite_sign (lt_of_not_ge hab) hx.1
        have hs : |x*a-x⁻¹*b| < u := hsmall
        linarith
      rw [hzero]
      exact bot_le
    · calc
        _ ≤ scaleLaw Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
        _ ≤ ENNReal.ofReal (8*u/A) := by
          apply ENNReal.one_le_ofReal.mpr
          apply (le_div_iff₀ hA).mpr
          linarith

/-- Dependent-pair probability transferred through the exact one-coordinate marginal. -/
theorem same_coordinate_product_sublevel_le (i : ℕ+) (a b u : ℝ)
    (ha : 1 ≤ |a|) (hu : 0 < u) :
    scaleProbability {s | |s i*a-(s i)⁻¹*b| < u} ≤ ENNReal.ofReal (8*u) := by
  have hm : MeasurableSet {x : ℝ | |x*a-x⁻¹*b| < u} :=
    measurableSet_lt (continuous_abs.measurable.comp
      ((measurable_id.mul_const a).sub (measurable_inv.mul_const b))) measurable_const
  have hmap := Measure.map_apply (μ := scaleProbability) (measurable_pi_apply i) hm
  rw [scaleProbability_map_eval] at hmap
  change scaleProbability ((fun s => s i) ⁻¹' {x : ℝ | |x*a-x⁻¹*b| < u}) ≤ _
  rw [← hmap]
  simpa using same_coordinate_atom_sublevel_le a b 1 u (by norm_num) ha hu

/-- Different coordinate comparison transferred through the exact independent product marginal. -/
theorem distinct_coordinate_product_sublevel_le {i j : ℕ+} (hij : i ≠ j)
    (σ τ : ReciprocalSign) (a b u : ℝ) (ha : 1 ≤ |a|) (hu : 0 < u) :
    scaleProbability {s | |scaleFactor σ (s i)*a-scaleFactor τ (s j)*b| < u} ≤
      ENNReal.ofReal (8*u) := by
  have hm : MeasurableSet {z : ℝ × ℝ | |scaleFactor σ z.1*a-scaleFactor τ z.2*b| < u} :=
    measurableSet_lt (continuous_abs.measurable.comp
      ((((measurable_scaleFactor σ).comp measurable_fst).mul_const a).sub
        (((measurable_scaleFactor τ).comp measurable_snd).mul_const b))) measurable_const
  have hmap := Measure.map_apply (μ := scaleProbability)
    ((measurable_pi_apply i).prodMk (measurable_pi_apply j)) hm
  rw [scaleProbability_map_eval_pair hij] at hmap
  change scaleProbability ((fun s => (s i, s j)) ⁻¹'
    {z : ℝ × ℝ | |scaleFactor σ z.1*a-scaleFactor τ z.2*b| < u}) ≤ _
  rw [← hmap]
  simpa using product_atom_sublevel_le σ τ a b 1 u (by norm_num) ha hu

/-- Uniform actual fixed-atom small-ball estimate across all different reciprocal labels. -/
theorem label_atom_sublevel_le (c d : Label) (hcd : c ≠ d) (a b u : ℝ)
    (ha : 1 ≤ |a|) (hb : 1 ≤ |b|) (hu : 0 < u) :
    scaleProbability {s | |labelScale s c*a-labelScale s d*b| < u} ≤ ENNReal.ofReal (8*u) := by
  by_cases hij : c.1 = d.1
  · rcases c with ⟨i, σ⟩
    rcases d with ⟨j, τ⟩
    dsimp at hij
    subst j
    cases σ <;> cases τ
    · exact (hcd rfl).elim
    · exact same_coordinate_product_sublevel_le i a b u ha hu
    · simpa only [labelScale, abs_sub_comm] using same_coordinate_product_sublevel_le i b a u hb hu
    · exact (hcd rfl).elim
  · simpa only [labelScale_eq_scaleFactor] using
      distinct_coordinate_product_sublevel_le hij c.2 d.2 a b u ha hu

/-- The literal finite-catalogue descriptor of one scheduled sector atom. -/
abbrev SectorAtomDescriptor := ℕ × ReciprocalSign × ℕ × Bool × ℤ

/-- The positive block and reciprocal orientation named by an atom descriptor. -/
def sectorAtomLabel (o : SectorAtomDescriptor) : Label := (⟨max o.1 1, by omega⟩, o.2.1)
/-- The unscaled actual block atom represented by the descriptor. -/
def sectorAtomBase (R : ℕ+ → ℕ) (o : SectorAtomDescriptor) : ℝ :=
  blockCatalogueAtom (sectorAtomLabel o).1 (R (sectorAtomLabel o).1) o.2.2

/-- The positive-index and scheduled-cell conditions for an actual atom descriptor. -/
def sectorAtomValid (R : ℕ+ → ℕ) (o : SectorAtomDescriptor) : Prop :=
  1 ≤ o.1 ∧ 1 ≤ o.2.2.1 ∧
    cellThreshold (R (sectorAtomLabel o).1) ⟨max o.2.2.1 1, by omega⟩ ≤ o.2.2.2.2.natAbs

/-- The actual gap schedule forces every eligible base atom a uniform distance from zero. -/
theorem sectorAtomBase_abs_ge_one (R : ℕ+ → ℕ) (hR : ∀ i : ℕ+, 2^(i : ℕ) ≤ R i)
    (o : SectorAtomDescriptor) (ho : sectorAtomValid R o) : 1 ≤ |sectorAtomBase R o| := by
  have hi := (sectorAtomLabel o).1.pos
  have htwo : 2 ≤ R (sectorAtomLabel o).1 := by
    have hpow : 2^1 ≤ 2^((sectorAtomLabel o).1 : ℕ) := Nat.pow_le_pow_right (by decide) hi
    exact hpow.trans (hR _)
  have hmem : sectorAtomBase R o ∈ blockSet (sectorAtomLabel o).1 (R (sectorAtomLabel o).1) :=
    ⟨⟨max o.2.2.1 1, by omega⟩, o.2.2.2.1, o.2.2.2.2, ho.2.2, rfl⟩
  have hgap := blockSet_central_gap hi (by omega : 1 ≤ R (sectorAtomLabel o).1) hmem
  have hcast : (2 : ℝ) ≤ R (sectorAtomLabel o).1 := by exact_mod_cast htwo
  linarith

/-- The actual pair event includes only valid atoms and genuinely different labels. -/
def sectorPairBadEvent (R : ℕ+ → ℕ) (o p : SectorAtomDescriptor) (u : ℝ) : Set (ℕ+ → ℝ) :=
  {s | sectorAtomValid R o ∧ sectorAtomValid R p ∧ sectorAtomLabel o ≠ sectorAtomLabel p ∧
    |originCatalogueValue R s o-originCatalogueValue R s p| < u}

theorem sectorPairBadEvent_measure_le (R : ℕ+ → ℕ) (hR : ∀ i : ℕ+, 2^(i : ℕ) ≤ R i)
    (o p : SectorAtomDescriptor) (u : ℝ) (hu : 0 < u) :
    scaleProbability (sectorPairBadEvent R o p u) ≤ ENNReal.ofReal (8*u) := by
  by_cases hvalid : sectorAtomValid R o ∧ sectorAtomValid R p ∧ sectorAtomLabel o ≠ sectorAtomLabel p
  · apply (measure_mono (show sectorPairBadEvent R o p u ⊆
      {s | |labelScale s (sectorAtomLabel o)*sectorAtomBase R o-
        labelScale s (sectorAtomLabel p)*sectorAtomBase R p| < u} from fun _ hs => hs.2.2.2)).trans
    exact label_atom_sublevel_le _ _ hvalid.2.2 _ _ u
      (sectorAtomBase_abs_ge_one R hR o hvalid.1) (sectorAtomBase_abs_ge_one R hR p hvalid.2.1) hu
  · have heq : sectorPairBadEvent R o p u = ∅ := by ext s; simp [sectorPairBadEvent]; tauto
    simp only [heq, measure_empty]
    exact bot_le

/-- A deterministic window pair catalogue containing every actual bounded pair. -/
def windowSectorBadEvent (R : ℕ+ → ℕ) (r u : ℝ) : Set (ℕ+ → ℝ) :=
  ⋃ o ∈ originCatalogueLabels r, ⋃ p ∈ originCatalogueLabels r, sectorPairBadEvent R o p u

theorem windowSectorBadEvent_measure_le (R : ℕ+ → ℕ) (hR : ∀ i : ℕ+, 2^(i : ℕ) ≤ R i)
    (r u : ℝ) (hu : 0 < u) :
    scaleProbability (windowSectorBadEvent R r u) ≤ (originCatalogueLabels r).card^2 * ENNReal.ofReal (8*u) := by
  calc
    _ ≤ ∑ o ∈ originCatalogueLabels r, scaleProbability (⋃ p ∈ originCatalogueLabels r,
        sectorPairBadEvent R o p u) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _o ∈ originCatalogueLabels r, ((originCatalogueLabels r).card * ENNReal.ofReal (8*u)) := by
      apply Finset.sum_le_sum
      intro o ho
      calc
        _ ≤ ∑ p ∈ originCatalogueLabels r, scaleProbability (sectorPairBadEvent R o p u) :=
          measure_biUnion_finset_le _ _
        _ ≤ ∑ _p ∈ originCatalogueLabels r, ENNReal.ofReal (8*u) :=
          Finset.sum_le_sum (fun p _ => sectorPairBadEvent_measure_le R hR o p u hu)
        _ = _ := by simp
    _ = _ := by simp; ring

/-- Retain the logarithmic block factor explicitly at dyadic radii. -/
theorem originCatalogue_dyadic_card_le (n : ℕ) :
    (originCatalogueLabels ((2 : ℝ)^n)).card ≤ 168*(n+2)*(2^n)^2 := by
  have hp : 1 ≤ (2 : ℕ)^n := one_le_pow₀ (by decide)
  have hceil : ⌈2*(2 : ℝ)^n+1⌉₊ = 2*(2^n : ℕ)+1 := by
    have heq : 2*(2 : ℝ)^n+1 = ((2*(2^n : ℕ)+1 : ℕ) : ℝ) := by push_cast; rfl
    rw [heq, Nat.ceil_natCast]
  have hN : ⌈2*(2 : ℝ)^n+1/2⌉₊ ≤ 3*(2^n : ℕ) := by
    apply Nat.ceil_le.mpr
    have hp' : (1 : ℝ) ≤ 2^n := one_le_pow₀ (by norm_num)
    push_cast
    linarith
  have hlog : Nat.log 2 (2*(2^n : ℕ)+1) ≤ n+2 := by
    apply le_of_lt
    apply Nat.log_lt_of_lt_pow (by omega)
    rw [pow_add]
    norm_num
    omega
  rw [originCatalogueLabels_card, hceil]
  calc
    _ ≤ 8*(n+2)*(3*(2^n : ℕ))*(7*(2^n : ℕ)) := by gcongr; omega
    _ = 168*(n+2)*(2^n)^2 := by ring

/-- The dyadic union uses the actual quadratic atom count and the source power six. -/
def globalSectorBadEvent (R : ℕ+ → ℕ) (t : ℝ) : Set (ℕ+ → ℝ) :=
  ⋃ n : ℕ, windowSectorBadEvent R ((2 : ℝ)^n) (t/((2 : ℝ)^n)^6)

private theorem summable_sector_weights :
    Summable (fun n : ℕ => ((n : ℝ)+2)^2*(1/4 : ℝ)^n) := by
  have h0 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 0 (r := 1/4) (by norm_num)
  have h1 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 (r := 1/4) (by norm_num)
  have h2 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 2 (r := 1/4) (by norm_num)
  apply (h2.add ((h1.mul_left 4).add (h0.mul_left 4))).congr
  intro n
  ring

/-- A finite deterministic constant, independent of the gap schedule. -/
def sectorSeparationConstant : ℝ :=
  225792 * ∑' n : ℕ, ((n : ℝ)+2)^2*(1/4 : ℝ)^n

theorem sectorSeparationConstant_nonneg : 0 ≤ sectorSeparationConstant := by
  unfold sectorSeparationConstant
  positivity

theorem dyadicSectorBadEvent_measure_le (R : ℕ+ → ℕ)
    (hR : ∀ i : ℕ+, 2^(i : ℕ) ≤ R i) (n : ℕ) (t : ℝ) (ht : 0 < t) :
    scaleProbability (windowSectorBadEvent R ((2 : ℝ)^n) (t/((2 : ℝ)^n)^6)) ≤
      ENNReal.ofReal (225792*t*((n : ℝ)+2)^2*(1/4 : ℝ)^n) := by
  have hc : ((originCatalogueLabels ((2 : ℝ)^n)).card : ℝ) ≤
      168*((n : ℝ)+2)*((2 : ℝ)^n)^2 := by exact_mod_cast originCatalogue_dyadic_card_le n
  calc
    _ ≤ ((originCatalogueLabels ((2 : ℝ)^n)).card : ℝ≥0∞)^2 *
        ENNReal.ofReal (8*(t/((2 : ℝ)^n)^6)) :=
      windowSectorBadEvent_measure_le R hR _ _ (by positivity)
    _ = ENNReal.ofReal (((originCatalogueLabels ((2 : ℝ)^n)).card : ℝ)^2 *
        (8*(t/((2 : ℝ)^n)^6))) := by
      simp only [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ ((originCatalogueLabels ((2 : ℝ)^n)).card : ℝ)^2),
        ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ ((originCatalogueLabels ((2 : ℝ)^n)).card : ℝ)), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal ((168*((n : ℝ)+2)*((2 : ℝ)^n)^2)^2 *
        (8*(t/((2 : ℝ)^n)^6))) := by gcongr
    _ = _ := by
      congr 1
      have hpow : (1/4 : ℝ)^n = (((2 : ℝ)^n)^2)⁻¹ := by
        calc
          _ = (((2 : ℝ)^2)⁻¹)^n := by norm_num
          _ = _ := by rw [← inv_pow, ← pow_mul, Nat.mul_comm 2 n, pow_mul]; simp [inv_pow]
      rw [hpow]
      field_simp
      ring

theorem globalSectorBadEvent_measure_le (R : ℕ+ → ℕ)
    (hR : ∀ i : ℕ+, 2^(i : ℕ) ≤ R i) (t : ℝ) (ht : 0 < t) :
    scaleProbability (globalSectorBadEvent R t) ≤ ENNReal.ofReal (sectorSeparationConstant*t) := by
  calc
    _ ≤ ∑' n : ℕ, scaleProbability (windowSectorBadEvent R ((2 : ℝ)^n) (t/((2 : ℝ)^n)^6)) :=
      measure_iUnion_le _
    _ ≤ ∑' n : ℕ, ENNReal.ofReal (225792*t*((n : ℝ)+2)^2*(1/4 : ℝ)^n) :=
      ENNReal.tsum_le_tsum (fun n => dyadicSectorBadEvent_measure_le R hR n t ht)
    _ = ENNReal.ofReal (∑' n : ℕ, 225792*t*(((n : ℝ)+2)^2*(1/4 : ℝ)^n)) := by
      simp_rw [mul_assoc]
      simpa only [mul_assoc] using (ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
        (summable_sector_weights.mul_left (225792*t))).symm
    _ = _ := by rw [tsum_mul_left]; unfold sectorSeparationConstant; congr 1; ring

/-- Almost every scale sequence avoids every window collision at some positive threshold. -/
theorem ae_exists_globalSector_threshold (R : ℕ+ → ℕ)
    (hR : ∀ i : ℕ+, 2^(i : ℕ) ≤ R i) :
    ∀ᵐ s ∂scaleProbability, ∃ t : ℝ, 0 < t ∧ s ∉ globalSectorBadEvent R t := by
  apply ae_iff.mpr
  apply le_antisymm ?_ bot_le
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  have hK := sectorSeparationConstant_nonneg
  have he : (0 : ℝ) < ε := hε
  let t : ℝ := (ε : ℝ)/(sectorSeparationConstant+1)
  have ht : 0 < t := by dsimp [t]; positivity
  have hsub : {s | ¬ ∃ t : ℝ, 0 < t ∧ s ∉ globalSectorBadEvent R t} ⊆
      globalSectorBadEvent R t := by
    intro s hs
    by_contra hn
    exact hs ⟨t, ht, hn⟩
  calc
    _ ≤ scaleProbability (globalSectorBadEvent R t) := measure_mono hsub
    _ ≤ ENNReal.ofReal (sectorSeparationConstant*t) := globalSectorBadEvent_measure_le R hR t ht
    _ ≤ ENNReal.ofReal (ε : ℝ) := by
      apply ENNReal.ofReal_le_ofReal
      dsimp [t]
      rw [← mul_div_assoc]
      apply (div_le_iff₀ (by positivity : 0 < sectorSeparationConstant+1)).mpr
      nlinarith
    _ = 0+(ε : ℝ≥0∞) := by simp

/-- Every positive radius has a dyadic upper approximation with controlled overshoot. -/
theorem exists_dyadic_radius (a : ℝ) (ha : 1 ≤ a) :
    ∃ n : ℕ, a ≤ (2 : ℝ)^n ∧ (2 : ℝ)^n ≤ 4*a := by
  let N : ℕ := ⌈a⌉₊
  have hN : N ≠ 0 := by
    have hceil := Nat.le_ceil a
    change a ≤ (N : ℝ) at hceil
    intro hz
    rw [hz, Nat.cast_zero] at hceil
    linarith
  refine ⟨Nat.log 2 N+1, ?_, ?_⟩
  · apply (Nat.le_ceil a).trans
    exact_mod_cast (Nat.lt_pow_succ_log_self (by decide : 1 < 2) N).le
  · have hp : (2 : ℝ)^(Nat.log 2 N) ≤ N := by exact_mod_cast Nat.pow_log_le_self 2 hN
    have hceil : (N : ℝ) < a+1 := Nat.ceil_lt_add_one (by linarith)
    rw [pow_succ]
    nlinarith

/-- The literal descriptor of an actual atom is valid and has the original label and value. -/
theorem sectorAtom_actual_descriptor (R : ℕ+ → ℕ) (s : ℕ+ → ℝ)
    (b : Label) (j : ℕ+) (positive : Bool) (n : ℤ)
    (hcell : cellThreshold (R b.1) j ≤ n.natAbs) :
    let o : SectorAtomDescriptor := (b.1.val, b.2, j.val, positive, n)
    sectorAtomValid R o ∧ sectorAtomLabel o = b ∧
      originCatalogueValue R s o = labelScale s b*((n : ℝ)+signedPhase positive (blockPhase b.1 (R b.1) j)) := by
  dsimp only
  have hi : (⟨max b.1.val 1, by omega⟩ : ℕ+) = b.1 := Subtype.ext (max_eq_left b.1.pos)
  have hj : (⟨max j.val 1, by omega⟩ : ℕ+) = j := Subtype.ext (max_eq_left j.pos)
  simp only [sectorAtomValid, sectorAtomLabel, originCatalogueValue, blockCatalogueAtom, hi, hj,
    Prod.eta]
  exact ⟨⟨b.1.pos, j.pos, hcell⟩, trivial, trivial⟩

/-- Every actual close pair of different labels is present in its finite window event. -/
theorem actual_pair_mem_windowSectorBadEvent (R : ℕ+ → ℕ) (s : ℕ+ → ℝ)
    (hR : ∀ i : ℕ+, 2^(i : ℕ) ≤ R i) (hs : ∀ i, s i ∈ Icc (1 : ℝ) 2)
    (b d : Label) (hbd : b ≠ d) {x y r u : ℝ}
    (hx : x ∈ sectorSet R s b) (hy : y ∈ sectorSet R s d)
    (hxr : |x| ≤ r) (hyr : |y| ≤ r) (hclose : |x-y| < u) :
    s ∈ windowSectorBadEvent R r u := by
  obtain ⟨a, ⟨j, positive, n, hcell, rfl⟩, rfl⟩ := hx
  obtain ⟨a', ⟨j', positive', n', hcell', rfl⟩, rfl⟩ := hy
  have ho := actual_origin_descriptor_mem R s hR hs b j positive n hcell r hxr
  have hp := actual_origin_descriptor_mem R s hR hs d j' positive' n' hcell' r hyr
  have hod := sectorAtom_actual_descriptor R s b j positive n hcell
  have hpd := sectorAtom_actual_descriptor R s d j' positive' n' hcell'
  simp only [windowSectorBadEvent, mem_iUnion]
  refine ⟨(b.1.val, b.2, j.val, positive, n), ho,
    (d.1.val, d.2, j'.val, positive', n'), hp, hod.1, hpd.1, ?_, ?_⟩
  · simpa only [hod.2.1, hpd.2.1] using hbd
  · simpa only [hod.2.2, hpd.2.2] using hclose

/-- Actual power-six cross-label separation, with one positive constant for all atoms. -/
theorem actual_sector_separation_of_global_threshold (R : ℕ+ → ℕ) (s : ℕ+ → ℝ)
    (hR : ∀ i : ℕ+, 2^(i : ℕ) ≤ R i) (hs : ∀ i, s i ∈ Icc (1 : ℝ) 2)
    (t : ℝ) (ht : 0 < t) (hgood : s ∉ globalSectorBadEvent R t) :
    ∀ b d : Label, b ≠ d → ∀ x ∈ sectorSet R s b, ∀ y ∈ sectorSet R s d,
      (t/4096)/(1+|x|+|y|)^6 ≤ |x-y| := by
  intro b d hbd x hx y hy
  have ha : 1 ≤ 1+|x|+|y| := by linarith [abs_nonneg x, abs_nonneg y]
  obtain ⟨n, hn, hn'⟩ := exists_dyadic_radius (1+|x|+|y|) ha
  have hxr : |x| ≤ (2 : ℝ)^n := by linarith [abs_nonneg y]
  have hyr : |y| ≤ (2 : ℝ)^n := by linarith [abs_nonneg x]
  have hsep : t/((2 : ℝ)^n)^6 ≤ |x-y| := by
    by_contra hlt
    exact hgood (mem_iUnion.mpr ⟨n, actual_pair_mem_windowSectorBadEvent R s hR hs b d hbd
      hx hy hxr hyr (lt_of_not_ge hlt)⟩)
  apply le_trans ?_ hsep
  have hp : ((2 : ℝ)^n)^6 ≤ (4*(1+|x|+|y|))^6 := pow_le_pow_left₀ (by positivity) hn' 6
  have heq : (t/4096)/(1+|x|+|y|)^6 = t/(4*(1+|x|+|y|))^6 := by
    rw [mul_pow, div_div]
    norm_num
  rw [heq]
  exact div_le_div_of_nonneg_left ht.le (by positivity) hp

/-- For every deterministic exponential gap schedule, the actual reciprocal product law
almost surely gives a positive global power-six separation constant for different labels. -/
theorem ae_actual_sectors_power_six_separated (R : ℕ+ → ℕ)
    (hR : ∀ i : ℕ+, 2^(i : ℕ) ≤ R i) :
    ∀ᵐ s ∂scaleProbability, ∃ c : ℝ, 0 < c ∧
      ∀ b d : Label, b ≠ d → ∀ x ∈ sectorSet R s b, ∀ y ∈ sectorSet R s d,
        c/(1+|x|+|y|)^6 ≤ |x-y| := by
  filter_upwards [ae_all_scales_mem, ae_exists_globalSector_threshold R hR] with s hs ht
  obtain ⟨t, ht, hgood⟩ := ht
  exact ⟨t/4096, by positivity, actual_sector_separation_of_global_threshold R s hR hs t ht hgood⟩

end
end MeyerGeneralProblem.Adaptive
