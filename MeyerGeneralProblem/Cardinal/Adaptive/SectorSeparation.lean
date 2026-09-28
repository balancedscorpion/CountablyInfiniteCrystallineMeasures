module

public import MeyerGeneralProblem.Cardinal.Adaptive.ScaleProbability
public import MeyerGeneralProblem.Cardinal.Adaptive.PhaseClosure

@[expose] public section

/-!
# Almost-sure disjointness of actual reciprocal sectors and periodic closures

Distinct coordinates are handled by their actual product marginal and null
singleton fibres. The two reciprocal labels at one coordinate are dependent:
their collision equation reduces to a square equation on the positive scale
interval and has at most one solution. Countable intersections of full-measure
events need no independence assumption.
-/

namespace MeyerGeneralProblem.Adaptive

noncomputable section

open MeasureTheory Set Filter

/-- A collision between two distinct-coordinate scaled atoms has null product measure. -/
theorem product_atom_collision_null (σ τ : ReciprocalSign) (a b : ℝ) (hb : b ≠ 0) :
    (scaleLaw.prod scaleLaw) {q : ℝ × ℝ | scaleFactor σ q.1 * a = scaleFactor τ q.2 * b} = 0 := by
  apply Measure.measure_prod_null_of_ae_null
  · exact measurableSet_eq_fun ((measurable_scaleFactor σ).comp measurable_fst |>.mul_const a)
      ((measurable_scaleFactor τ).comp measurable_snd |>.mul_const b)
  · apply Eventually.of_forall
    intro x
    apply Set.Subsingleton.measure_zero
    intro y hy z hz
    apply scaleFactor_mul_injective τ hb
    exact hy.symm.trans hz

/-- Distinct actual coordinates almost surely avoid each fixed reciprocal atom collision. -/
theorem ae_distinct_coordinate_atom_ne {i j : ℕ+} (hij : i ≠ j)
    (σ τ : ReciprocalSign) (a b : ℝ) (hb : b ≠ 0) :
    ∀ᵐ s ∂scaleProbability, scaleFactor σ (s i) * a ≠ scaleFactor τ (s j) * b := by
  have hp : ∀ᵐ q ∂scaleLaw.prod scaleLaw,
      scaleFactor σ q.1 * a ≠ scaleFactor τ q.2 * b := by
    rw [ae_iff]
    simpa only [not_not] using product_atom_collision_null σ τ a b hb
  have hpmap : ∀ᵐ q ∂scaleProbability.map (fun s => (s i, s j)),
      scaleFactor σ q.1 * a ≠ scaleFactor τ q.2 * b := by
    rwa [scaleProbability_map_eval_pair hij]
  exact ae_of_ae_map ((measurable_pi_apply i).prodMk (measurable_pi_apply j)).aemeasurable hpmap

/-- On the actual positive scale interval, a same-coordinate reciprocal collision has at most one root. -/
theorem same_coordinate_collision_subsingleton (a b : ℝ) (ha : a ≠ 0) :
    {x : ℝ | x ∈ Icc 1 2 ∧ x * a = x⁻¹ * b}.Subsingleton := by
  intro x hx y hy
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx.1.1
  have hypos : 0 < y := lt_of_lt_of_le zero_lt_one hy.1.1
  have hx2 : x ^ 2 * a = b := by
    have h := congrArg (fun t : ℝ => x * t) hx.2
    rw [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hxpos.ne', one_mul] at h
    nlinarith [h]
  have hy2 : y ^ 2 * a = b := by
    have h := congrArg (fun t : ℝ => y * t) hy.2
    rw [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hypos.ne', one_mul] at h
    nlinarith [h]
  have hsq : x ^ 2 = y ^ 2 := mul_right_cancel₀ ha (hx2.trans hy2.symm)
  exact (sq_eq_sq₀ hxpos.le hypos.le).mp hsq

/-- The dependent forward/reciprocal pair also avoids every fixed nonzero-atom collision. -/
theorem ae_same_coordinate_atom_ne (i : ℕ+) (a b : ℝ) (ha : a ≠ 0) :
    ∀ᵐ s ∂scaleProbability, s i * a ≠ (s i)⁻¹ * b := by
  have hnull : ∀ᵐ x ∂scaleLaw, x ∉ {x : ℝ | x ∈ Icc 1 2 ∧ x * a = x⁻¹ * b} := by
    rw [ae_iff]
    simpa [and_assoc] using (same_coordinate_collision_subsingleton a b ha).measure_zero scaleLaw
  refine ae_scale_coordinate i (p := fun x => x * a ≠ x⁻¹ * b) ?_
  filter_upwards [hnull, ae_restrict_mem measurableSet_Icc] with x hx hmem
  intro heq
  exact hx ⟨hmem, heq⟩

/-- Every pair of different reciprocal labels almost surely avoids each fixed nonzero-atom collision. -/
theorem ae_label_atom_ne (c d : Label) (hcd : c ≠ d) (a b : ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    ∀ᵐ s ∂scaleProbability, labelScale s c * a ≠ labelScale s d * b := by
  by_cases hidx : c.1 = d.1
  · rcases c with ⟨i, σ⟩
    rcases d with ⟨j, τ⟩
    dsimp at hidx
    subst j
    cases σ <;> cases τ
    · exact (hcd rfl).elim
    · exact ae_same_coordinate_atom_ne i a b ha
    · exact (ae_same_coordinate_atom_ne i b a hb).mono fun _ h => h.symm
    · exact (hcd rfl).elim
  · simpa only [labelScale_eq_scaleFactor] using
      ae_distinct_coordinate_atom_ne hidx c.2 d.2 a b hb

/-- Countable nonzero atom families have almost surely pairwise disjoint reciprocal sectors. -/
theorem ae_scaled_countable_sets_disjoint (A : ℕ+ → Set ℝ)
    (hcount : ∀ i, (A i).Countable) (hzero : ∀ i, (0 : ℝ) ∉ A i) :
    ∀ᵐ s ∂scaleProbability, ∀ c d : Label, c ≠ d →
      Disjoint ((fun x => labelScale s c * x) '' A c.1)
        ((fun x => labelScale s d * x) '' A d.1) := by
  let (i : ℕ+) : Countable (A i) := (hcount i).to_subtype
  have hpair : ∀ c d : Label, ∀ a : A c.1, ∀ b : A d.1,
      ∀ᵐ s ∂scaleProbability, c ≠ d →
        labelScale s c * (a : ℝ) ≠ labelScale s d * (b : ℝ) := by
    intro c d a b
    by_cases hcd : c = d
    · exact Eventually.of_forall fun _ h => (h hcd).elim
    · have ha : (a : ℝ) ≠ 0 := fun h => hzero c.1 (h ▸ a.property)
      have hb : (b : ℝ) ≠ 0 := fun h => hzero d.1 (h ▸ b.property)
      exact (ae_label_atom_ne c d hcd a b ha hb).mono fun _ h _ => h
  have hall : ∀ᵐ s ∂scaleProbability, ∀ c d : Label, ∀ a : A c.1, ∀ b : A d.1,
      c ≠ d → labelScale s c * (a : ℝ) ≠ labelScale s d * (b : ℝ) := by
    exact ae_all_iff.mpr fun c => ae_all_iff.mpr fun d =>
      ae_all_iff.mpr fun a => ae_all_iff.mpr fun b => hpair c d a b
  filter_upwards [hall] with s hs
  intro c d hcd
  apply Set.disjoint_left.mpr
  rintro x ⟨a, ha, rfl⟩ ⟨b, hb, heq⟩
  exact hs c d ⟨a, ha⟩ ⟨b, hb⟩ hcd heq.symm

/-- All full periodic reciprocal sectors, including seams, are almost surely pairwise disjoint. -/
theorem ae_periodic_sectors_disjoint (R : ℕ+ → ℕ) (hR : ∀ i, 1 ≤ R i) :
    ∀ᵐ s ∂scaleProbability, ∀ c d : Label, c ≠ d →
      Disjoint ((fun x => labelScale s c * x) '' periodicPhaseSet c.1 (R c.1))
        ((fun x => labelScale s d * x) '' periodicPhaseSet d.1 (R d.1)) :=
  ae_scaled_countable_sets_disjoint (fun i => periodicPhaseSet i (R i))
    (fun i => periodicPhaseSet_countable i (R i))
    (fun i => zero_not_mem_periodicPhaseSet i.pos (hR i))

/-- Literal actual atom sectors inherit almost-sure pairwise disjointness. -/
theorem ae_actual_sectors_disjoint (R : ℕ+ → ℕ) (hR : ∀ i, 1 ≤ R i) :
    ∀ᵐ s ∂scaleProbability, ∀ c d : Label, c ≠ d →
      Disjoint (sectorSet R s c) (sectorSet R s d) := by
  filter_upwards [ae_periodic_sectors_disjoint R hR] with s hs
  intro c d hcd
  exact (hs c d hcd).mono
    (Set.image_mono (blockSet_subset_periodicPhaseSet _ _))
    (Set.image_mono (blockSet_subset_periodicPhaseSet _ _))

/-- The physical reciprocal orientation has the same almost-sure periodic disjointness. -/
theorem ae_physical_periodic_sets_disjoint (R : ℕ+ → ℕ) (hR : ∀ i, 1 ≤ R i) :
    ∀ᵐ s ∂scaleProbability, ∀ c d : Label, c ≠ d →
      Disjoint (physicalPeriodicSet R s c) (physicalPeriodicSet R s d) := by
  filter_upwards [ae_periodic_sectors_disjoint R hR] with s hs
  intro c d hcd
  have hflip : (c.1, c.2.flip) ≠ (d.1, d.2.flip) := by
    intro h
    apply hcd
    have h' := congrArg (fun b : Label => (b.1, b.2.flip)) h
    simpa only [ReciprocalSign.flip_flip, Prod.eta] using h'
  simpa only [physicalPeriodicSet, labelScale_flip] using hs (c.1, c.2.flip) (d.1, d.2.flip) hflip

/-- All positive integer gap choices still form one countable nonzero phase family. -/
def allGapPeriodicSet (i : ℕ+) : Set ℝ := ⋃ R : ℕ+, periodicPhaseSet i R

/-- The countable union over admissible integer gaps remains countable. -/
theorem allGapPeriodicSet_countable (i : ℕ+) : (allGapPeriodicSet i).Countable :=
  Set.countable_iUnion fun R : ℕ+ => periodicPhaseSet_countable i R

/-- Taking all admissible gap choices does not introduce the zero phase. -/
theorem zero_not_mem_allGapPeriodicSet (i : ℕ+) : (0 : ℝ) ∉ allGapPeriodicSet i := by
  intro hx
  obtain ⟨R, hR⟩ := mem_iUnion.mp hx
  exact zero_not_mem_periodicPhaseSet i.pos R.pos hR

/-- One full-measure scale event separates all integer gap choices simultaneously. -/
theorem ae_all_gap_periodic_sectors_disjoint :
    ∀ᵐ s ∂scaleProbability, ∀ c d : Label, c ≠ d →
      ∀ Rc Rd : ℕ, 1 ≤ Rc → 1 ≤ Rd →
      Disjoint ((fun x => labelScale s c * x) '' periodicPhaseSet c.1 Rc)
        ((fun x => labelScale s d * x) '' periodicPhaseSet d.1 Rd) := by
  filter_upwards [ae_scaled_countable_sets_disjoint allGapPeriodicSet
    allGapPeriodicSet_countable zero_not_mem_allGapPeriodicSet] with s hs
  intro c d hcd Rc Rd hRc hRd
  exact (hs c d hcd).mono
    (Set.image_mono (Set.subset_iUnion (fun R : ℕ+ => periodicPhaseSet c.1 R) ⟨Rc, hRc⟩))
    (Set.image_mono (Set.subset_iUnion (fun R : ℕ+ => periodicPhaseSet d.1 R) ⟨Rd, hRd⟩))

/-- Future adaptive choices of integer gaps inherit the same disjointness event. -/
theorem ae_adaptive_gap_periodic_sectors_disjoint
    (R : (ℕ+ → ℝ) → ℕ+ → ℕ) (hR : ∀ s i, 1 ≤ R s i) :
    ∀ᵐ s ∂scaleProbability, ∀ c d : Label, c ≠ d →
      Disjoint ((fun x => labelScale s c * x) '' periodicPhaseSet c.1 (R s c.1))
        ((fun x => labelScale s d * x) '' periodicPhaseSet d.1 (R s d.1)) := by
  filter_upwards [ae_all_gap_periodic_sectors_disjoint] with s hs
  intro c d hcd
  exact hs c d hcd (R s c.1) (R s d.1) (hR s c.1) (hR s d.1)

/-- There are actual full scale sequences obeying every integer-gap disjointness condition. -/
theorem exists_scales_all_gap_periodic_disjoint :
    ∃ s : ℕ+ → ℝ, (∀ i, s i ∈ Icc (1 : ℝ) 2) ∧
      ∀ c d : Label, c ≠ d → ∀ Rc Rd : ℕ, 1 ≤ Rc → 1 ≤ Rd →
      Disjoint ((fun x => labelScale s c * x) '' periodicPhaseSet c.1 Rc)
        ((fun x => labelScale s d * x) '' periodicPhaseSet d.1 Rd) :=
  (ae_all_scales_mem.and ae_all_gap_periodic_sectors_disjoint).exists

end
end MeyerGeneralProblem.Adaptive
