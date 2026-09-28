module

public import MeyerGeneralProblem.Cardinal.Adaptive.SectorSeparation
public import MeyerGeneralProblem.Cardinal.Adaptive.CatalogueNonresonance
public import Mathlib.Topology.MetricSpace.HausdorffDistance
import all Mathlib.Topology.MetricSpace.HausdorffDistance

@[expose] public section

/-!
# Finite-window separation of the actual periodic closures

The seams remain present in every closed set. Compactness, actual almost-sure
periodic disjointness, and continuity of probability give a deterministic gap
with any prescribed positive failure budget.
-/

namespace MeyerGeneralProblem.Adaptive
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal

/-- Physical periodic sets are genuinely closed at every admissible scale. -/
theorem physicalPeriodicSet_isClosed (R : ℕ+ → ℕ) (s : ℕ+ → ℝ)
    (hR : ∀ i, 1 ≤ R i) (hs : ∀ i, s i ∈ Icc (1 : ℝ) 2) (b : Label) :
    IsClosed (physicalPeriodicSet R s b) := by
  have hb : labelScale s b ≠ 0 := by
    have h := labelScale_mem_Icc s hs b
    linarith [h.1]
  exact (Homeomorph.mulLeft₀ (labelScale s b)⁻¹ (inv_ne_zero hb)).isClosedMap _
    (periodicPhaseSet_isClosed b.1.pos (hR b.1))

/-- A finite family of disjoint closed real sets has one common positive gap on any window. -/
theorem finite_closed_family_window_gap {ι : Type*} (F : Finset ι) (C : ι → Set ℝ)
    (hC : ∀ b ∈ F, IsClosed (C b))
    (hdis : ∀ b ∈ F, ∀ d ∈ F, b ≠ d → Disjoint (C b) (C d)) (r : ℝ) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ b ∈ F, ∀ d ∈ F, b ≠ d →
      ∀ x ∈ C b, ∀ y ∈ C d, |x| ≤ r → |y| ≤ r → γ ≤ |x-y| := by
  classical
  let K : Set (ℝ × ℝ) := ⋃ b ∈ F, ⋃ d ∈ F, ⋃ _ : b ≠ d,
    (C b ∩ Icc (-r) r) ×ˢ (C d ∩ Icc (-r) r)
  have hK : IsCompact K := by
    apply F.isCompact_biUnion
    intro b hb
    apply F.isCompact_biUnion
    intro d hd
    apply isCompact_iUnion
    intro _
    exact (isCompact_Icc.inter_left (hC b hb)).prod (isCompact_Icc.inter_left (hC d hd))
  have hpos : ∀ z ∈ K, 0 < |z.1-z.2| := by
    intro z hz
    simp only [K, mem_iUnion] at hz
    obtain ⟨b, hb, d, hd, hbd, hz⟩ := hz
    apply abs_pos.mpr
    intro heq
    exact Set.disjoint_left.mp (hdis b hb d hd hbd) hz.1.1 (sub_eq_zero.mp heq ▸ hz.2.1)
  rcases K.eq_empty_or_nonempty with hempty | hne
  · refine ⟨1, by norm_num, ?_⟩
    intro b hb d hd hbd x hx y hy hxr hyr
    have hz : (x,y) ∈ K := by
      simp only [K, mem_iUnion]
      exact ⟨b,hb,d,hd,hbd,⟨hx,abs_le.mp hxr⟩,⟨hy,abs_le.mp hyr⟩⟩
    simp only [hempty, mem_empty_iff_false] at hz
  · have hc : Continuous (fun z : ℝ × ℝ => |z.1-z.2|) := by fun_prop
    obtain ⟨z, hz, hmin⟩ := hK.exists_isMinOn hne hc.continuousOn
    refine ⟨|z.1-z.2|, hpos z hz, ?_⟩
    intro b hb d hd hbd x hx y hy hxr hyr
    apply hmin (a := (x,y))
    simp only [K, mem_iUnion]
    exact ⟨b,hb,d,hd,hbd,⟨hx,abs_le.mp hxr⟩,⟨hy,abs_le.mp hyr⟩⟩

/-- Actual finite periodic closures almost surely have a positive common window gap. -/
theorem ae_finite_physical_closure_gap (R : ℕ+ → ℕ) (hR : ∀ i, 1 ≤ R i)
    (F : Finset Label) (r : ℝ) :
    ∀ᵐ s ∂scaleProbability, ∃ γ : ℝ, 0 < γ ∧ ∀ b ∈ F, ∀ d ∈ F, b ≠ d →
      ∀ x ∈ physicalPeriodicSet R s b, ∀ y ∈ physicalPeriodicSet R s d,
        |x| ≤ r → |y| ≤ r → γ ≤ |x-y| := by
  filter_upwards [ae_all_scales_mem, ae_physical_periodic_sets_disjoint R hR] with s hs hdis
  exact finite_closed_family_window_gap F (physicalPeriodicSet R s)
    (fun b _ => physicalPeriodicSet_isClosed R s hR hs b) (fun b _ d _ => hdis b d) r

/-- A countable encoding of the actual finite-window collision event, including seams. -/
def finitePeriodicCloseEvent (R : ℕ+ → ℕ) (F : Finset Label) (r γ : ℝ) : Set (ℕ+ → ℝ) :=
  ⋃ b ∈ F, ⋃ d ∈ F, ⋃ _ : b ≠ d,
    ⋃ a : periodicPhaseSet b.1 (R b.1), ⋃ z : periodicPhaseSet d.1 (R d.1),
      {s | |(labelScale s b)⁻¹*(a : ℝ)| ≤ r ∧ |(labelScale s d)⁻¹*(z : ℝ)| ≤ r ∧
        |(labelScale s b)⁻¹*(a : ℝ)-(labelScale s d)⁻¹*(z : ℝ)| < γ}

/-- Countability of the complete periodic phase sets gives measurable collision events. -/
theorem finitePeriodicCloseEvent_measurable (R : ℕ+ → ℕ) (F : Finset Label) (r γ : ℝ) :
    MeasurableSet (finitePeriodicCloseEvent R F r γ) := by
  let (b : Label) : Countable (periodicPhaseSet b.1 (R b.1)) :=
    (periodicPhaseSet_countable b.1 (R b.1)).to_subtype
  apply F.measurableSet_biUnion
  intro b _
  apply F.measurableSet_biUnion
  intro d _
  apply MeasurableSet.iUnion
  intro _
  apply MeasurableSet.iUnion
  intro a
  apply MeasurableSet.iUnion
  intro z
  have hb : Measurable (fun s : ℕ+ → ℝ => (labelScale s b)⁻¹*(a : ℝ)) := by
    simp only [labelScale_eq_scaleFactor]
    exact (((measurable_scaleFactor b.2).comp (measurable_pi_apply b.1)).inv).mul_const _
  have hd : Measurable (fun s : ℕ+ → ℝ => (labelScale s d)⁻¹*(z : ℝ)) := by
    simp only [labelScale_eq_scaleFactor]
    exact (((measurable_scaleFactor d.2).comp (measurable_pi_apply d.1)).inv).mul_const _
  exact (measurableSet_le (continuous_abs.measurable.comp hb) measurable_const).inter
    ((measurableSet_le (continuous_abs.measurable.comp hd) measurable_const).inter (measurableSet_lt (continuous_abs.measurable.comp (hb.sub hd)) measurable_const))

/-- The countable event is exactly the original physical-set collision statement. -/
theorem mem_finitePeriodicCloseEvent_iff (R : ℕ+ → ℕ) (F : Finset Label) (r γ : ℝ) (s : ℕ+ → ℝ) :
    s ∈ finitePeriodicCloseEvent R F r γ ↔
    ∃ b ∈ F, ∃ d ∈ F, b ≠ d ∧ ∃ x ∈ physicalPeriodicSet R s b,
      ∃ y ∈ physicalPeriodicSet R s d, |x| ≤ r ∧ |y| ≤ r ∧ |x-y| < γ := by
  simp only [finitePeriodicCloseEvent, mem_iUnion, mem_ofPred_eq]
  constructor
  · rintro ⟨b,hb,d,hd,hbd,a,z,ha,hz,hclose⟩
    exact ⟨b,hb,d,hd,hbd,_,⟨a,a.property,rfl⟩,_,⟨z,z.property,rfl⟩,ha,hz,hclose⟩
  · rintro ⟨b,hb,d,hd,hbd,x,⟨a,ha,rfl⟩,y,⟨z,hz,rfl⟩,hax,hzy,hclose⟩
    exact ⟨b,hb,d,hd,hbd,⟨a,ha⟩,⟨z,hz⟩,hax,hzy,hclose⟩

/-- Enlarging the proximity threshold enlarges the bad event. -/
theorem finitePeriodicCloseEvent_mono (R : ℕ+ → ℕ) (F : Finset Label) (r : ℝ) :
    Monotone (finitePeriodicCloseEvent R F r) := by
  intro γ δ h s hs
  rw [mem_finitePeriodicCloseEvent_iff] at hs ⊢
  obtain ⟨b,hb,d,hd,hbd,x,hx,y,hy,hxr,hyr,hclose⟩ := hs
  exact ⟨b,hb,d,hd,hbd,x,hx,y,hy,hxr,hyr,hclose.trans_le h⟩

/-- Compact separation makes the decreasing countable collision intersection null. -/
theorem finitePeriodicCloseEvent_iInter_null (R : ℕ+ → ℕ) (hR : ∀ i, 1 ≤ R i)
    (F : Finset Label) (r : ℝ) :
    scaleProbability (⋂ n : ℕ, finitePeriodicCloseEvent R F r (1/(n+1 : ℝ))) = 0 := by
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [ae_finite_physical_closure_gap R hR F r] with s hs
  obtain ⟨γ,hγ,hsep⟩ := hs
  obtain ⟨n,hn⟩ := exists_nat_one_div_lt hγ
  intro hmem
  have he := mem_iInter.mp hmem n
  rw [mem_finitePeriodicCloseEvent_iff] at he
  obtain ⟨b,hb,d,hd,hbd,x,hx,y,hy,hxr,hyr,hclose⟩ := he
  exact (hclose.trans hn).not_ge (hsep b hb d hd hbd x hx y hy hxr hyr)

/-- A deterministic positive phase gap meets any positive failure budget. -/
theorem exists_finite_closure_gap_failure_bound (R : ℕ+ → ℕ) (hR : ∀ i, 1 ≤ R i)
    (F : Finset Label) (r ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ δ ∧
      scaleProbability (finitePeriodicCloseEvent R F r γ) ≤ ENNReal.ofReal ε := by
  have hmono : Antitone (fun n : ℕ => finitePeriodicCloseEvent R F r (1/(n+1 : ℝ))) := by
    intro n m hnm
    apply finitePeriodicCloseEvent_mono
    have hm : (n : ℝ)+1 ≤ (m : ℝ)+1 := by exact_mod_cast Nat.add_le_add_right hnm 1
    exact one_div_le_one_div_of_le (by positivity) hm
  have hlim := tendsto_measure_iInter_atTop (μ := scaleProbability)
    (fun n : ℕ => (finitePeriodicCloseEvent_measurable R F r (1/(n+1 : ℝ))).nullMeasurableSet)
    hmono ⟨0, measure_ne_top _ _⟩
  rw [finitePeriodicCloseEvent_iInter_null R hR F r] at hlim
  have hevent := hlim.eventually (Iio_mem_nhds (ENNReal.ofReal_pos.mpr hε))
  obtain ⟨n,hn⟩ := hevent.exists
  refine ⟨min δ (1/(n+1 : ℝ)), lt_min hδ (by positivity), min_le_left _ _, ?_⟩
  apply (measure_mono (finitePeriodicCloseEvent_mono R F r (min_le_right _ _))).trans
  exact hn.le

/-- Exactly the first M reciprocal labels. -/
def finitePrefixLabels (M : ℕ) : Finset Label :=
  Finset.univ.image (fun b : Fin M × ReciprocalSign => (prefixScaleIndex b.1, b.2))

/-- An innocuous deterministic extension used only to choose a prefix-dependent constant. -/
def prefixGapExtension {M : ℕ} (R₀ : Fin M → ℕ) (i : ℕ+) : ℕ :=
  if h : i.val ≤ M then R₀ ⟨i.val-1, by have := i.pos; omega⟩ else 1

@[simp] theorem prefixGapExtension_apply {M : ℕ} (R₀ : Fin M → ℕ) (i : Fin M) :
    prefixGapExtension R₀ (prefixScaleIndex i) = R₀ i := by
  unfold prefixGapExtension
  have h : (prefixScaleIndex i).val ≤ M := by change i.val+1 ≤ M; omega
  rw [dite_eq_left h]
  congr 1

/-- Outside the measurable bad event, every actual listed pair obeys the selected gap. -/
theorem not_mem_finitePeriodicCloseEvent_iff (R : ℕ+ → ℕ) (F : Finset Label)
    (r γ : ℝ) (s : ℕ+ → ℝ) :
    s ∉ finitePeriodicCloseEvent R F r γ ↔
      ∀ b ∈ F, ∀ d ∈ F, b ≠ d → ∀ x ∈ physicalPeriodicSet R s b,
        ∀ y ∈ physicalPeriodicSet R s d, |x| ≤ r → |y| ≤ r → γ ≤ |x-y| := by
  rw [mem_finitePeriodicCloseEvent_iff]
  push Not
  rfl

/-- A sufficiently small test piece meets at most one of the listed closures. -/
theorem small_piece_meets_at_most_one_closure (R : ℕ+ → ℕ) (F : Finset Label)
    (r γ : ℝ) (s : ℕ+ → ℝ) (hgood : s ∉ finitePeriodicCloseEvent R F r γ)
    (U : Set ℝ) (hwindow : ∀ x ∈ U, |x| ≤ r)
    (hsmall : ∀ x ∈ U, ∀ y ∈ U, |x-y| < γ) :
    ∀ b ∈ F, ∀ d ∈ F, (U ∩ physicalPeriodicSet R s b).Nonempty →
      (U ∩ physicalPeriodicSet R s d).Nonempty → b = d := by
  intro b hb d hd ⟨x,hx,hxb⟩ ⟨y,hy,hyd⟩
  by_contra hbd
  exact (hsmall x hx y hy).not_ge
    ((not_mem_finitePeriodicCloseEvent_iff R F r γ s).mp hgood b hb d hd hbd
      x hxb y hyd (hwindow x hx) (hwindow y hy))

/-- The collision event depends solely on the gaps of the listed labels. -/
theorem finitePeriodicCloseEvent_congr (R R' : ℕ+ → ℕ) (F : Finset Label) (r γ : ℝ)
    (h : ∀ b ∈ F, R b.1 = R' b.1) :
    finitePeriodicCloseEvent R F r γ = finitePeriodicCloseEvent R' F r γ := by
  ext s
  simp only [finitePeriodicCloseEvent, mem_iUnion, mem_ofPred_eq]
  constructor
  · rintro ⟨b,hb,d,hd,hbd,a,z,ha,hz,hclose⟩
    refine ⟨b,hb,d,hd,hbd,⟨a, ?_⟩,⟨z, ?_⟩,ha,hz,hclose⟩
    · simpa only [← h b hb] using a.property
    · simpa only [← h d hd] using z.property
  · rintro ⟨b,hb,d,hd,hbd,a,z,ha,hz,hclose⟩
    refine ⟨b,hb,d,hd,hbd,⟨a, ?_⟩,⟨z, ?_⟩,ha,hz,hclose⟩
    · simpa only [h b hb] using a.property
    · simpa only [h d hd] using z.property

/-- The deterministic gap is chosen before any future gap, uniformly over all completions. -/
theorem exists_prefix_closure_gap_failure_bound (M : ℕ) (R₀ : Fin M → ℕ)
    (hR₀ : ∀ i, 1 ≤ R₀ i) (r ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ δ ∧ ∀ R : ℕ+ → ℕ,
      (∀ i, R (prefixScaleIndex i) = R₀ i) →
      scaleProbability (finitePeriodicCloseEvent R (finitePrefixLabels M) r γ) ≤ ENNReal.ofReal ε := by
  have hR : ∀ i, 1 ≤ prefixGapExtension R₀ i := by
    intro i
    unfold prefixGapExtension
    split_ifs
    · exact hR₀ _
    · exact le_rfl
  obtain ⟨γ,hγ,hγδ,hbound⟩ := exists_finite_closure_gap_failure_bound
    (prefixGapExtension R₀) hR (finitePrefixLabels M) r ε δ hε hδ
  refine ⟨γ,hγ,hγδ,?_⟩
  intro R hprefix
  rw [finitePeriodicCloseEvent_congr R (prefixGapExtension R₀) (finitePrefixLabels M) r γ]
  · exact hbound
  · intro b hb
    obtain ⟨⟨i,σ⟩,_,rfl⟩ := Finset.mem_image.mp hb
    simp only [prefixGapExtension_apply, hprefix]

/-- Accepted finite-stage window, cap and geometric failure budget. -/
theorem exists_stage_closure_gap (M : ℕ) (hM : 0 < M) (R₀ : Fin M → ℕ)
    (hR₀ : ∀ i, 1 ≤ R₀ i) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1/(M : ℝ) ∧ ∀ R : ℕ+ → ℕ,
      (∀ i, R (prefixScaleIndex i) = R₀ i) →
      scaleProbability (finitePeriodicCloseEvent R (finitePrefixLabels M) ((M : ℝ)+2) γ) ≤
        ENNReal.ofReal ((2 : ℝ)^(-(M+4 : ℤ))) := by
  apply exists_prefix_closure_gap_failure_bound M R₀ hR₀
  · positivity
  · positivity

end
end MeyerGeneralProblem.Adaptive
