module

public import MeyerGeneralProblem.Cardinal.Adaptive.PhaseGeometry
public import Mathlib.Topology.LocallyFinite
import all Mathlib.Topology.LocallyFinite
public import Mathlib.Topology.Algebra.Module.Cardinality
import all Mathlib.Topology.Algebra.Module.Cardinality
public import Mathlib.Topology.GDelta.Basic
import all Mathlib.Topology.GDelta.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
import all Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-!
# The actual phase closure and its periodic translates

The rapid tail converges to the half-cell seam. Adding both signs of the
seam gives a compact signed phase set; its integer translates form a locally
finite family of closed sets. Countability is used only after closedness has
been proved, to establish nowhere density.
-/

namespace MeyerGeneralProblem.Adaptive

noncomputable section

open Filter Set
open scoped Topology

/-- Enumerate all positive phases without omitting the finite matched head. -/
def positivePhaseSequence (P R : ℕ) (n : ℕ) : ℝ :=
  blockPhase P R ⟨n+1, Nat.succ_pos n⟩

/-- The full rapid distance tends to zero for every positive order and gap. -/
theorem rapidDistance_tendsto_zero {P R : ℕ} (hP : 1 ≤ P) (hR : 1 ≤ R) :
    Tendsto (rapidDistance P R) atTop (𝓝 0) := by
  have hp := tendsto_pow_atTop_atTop_of_one_lt (rapidBase_one_lt hP)
  have he := Real.tendsto_exp_atBot.comp
    (hp.const_mul_atTop_of_neg (neg_lt_zero.mpr (rapidDecay_pos hP hR)))
  change Tendsto (fun n => (1 / 16 : ℝ) *
    Real.exp (-(rapidDecay P R) * rapidBase P ^ n)) atTop (𝓝 0)
  simpa only [Function.comp_def, mul_zero] using he.const_mul (1 / 16 : ℝ)

/-- The complete sequence has only the original positive seam as a limit. -/
theorem positivePhaseSequence_tendsto {P R : ℕ} (hP : 1 ≤ P) (hR : 1 ≤ R) :
    Tendsto (positivePhaseSequence P R) atTop (𝓝 (1 / 2)) := by
  have hi : Tendsto (fun n : ℕ => (n+1) - headLength R) atTop atTop :=
    (tendsto_sub_atTop_nat (headLength R)).comp (tendsto_add_atTop_nat 1)
  have h := (rapidDistance_tendsto_zero hP hR).comp hi
  have ht : Tendsto (fun n : ℕ => 1 / 2 - rapidDistance P R ((n+1)-headLength R))
      atTop (𝓝 (1 / 2)) := by simpa using h.const_sub (1 / 2 : ℝ)
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (headLength R)] with n hn
  change 1 / 2 - rapidDistance P R (n+1-headLength R) =
    if n+1 ≤ headLength R then
      (2 * ((n+1 : ℕ) : ℝ) - 1) / (4 * (headLength R : ℝ))
    else 1 / 2 - rapidDistance P R (n+1-headLength R)
  rw [ite_eq_right (by omega)]

/-- The real signed phase closure needs both endpoint signs before periodization. -/
def signedPhaseClosure (P R : ℕ) : Set ℝ :=
  phaseSet P R ∪ {1 / 2, -(1 / 2)}

/-- The signed closure is the union of two convergent sequences with their limits. -/
theorem signedPhaseClosure_eq_insert_ranges (P R : ℕ) :
    signedPhaseClosure P R =
      insert (1 / 2) (range (positivePhaseSequence P R)) ∪
        insert (-(1 / 2)) (range (fun n => -positivePhaseSequence P R n)) := by
  ext x
  constructor
  · rintro (⟨j, positive, rfl⟩ | hx)
    · have hj : (⟨(j : ℕ)-1+1, by have := j.pos; omega⟩ : ℕ+) = j := by
        apply Subtype.ext
        change (j : ℕ)-1+1 = (j : ℕ)
        have := j.pos
        omega
      cases positive with
      | false =>
          refine Or.inr (Or.inr ⟨(j : ℕ)-1, ?_⟩)
          simp only [positivePhaseSequence, hj, signedPhase, Bool.false_eq_true, ite_false]
      | true =>
          refine Or.inl (Or.inr ⟨(j : ℕ)-1, ?_⟩)
          simp only [positivePhaseSequence, hj, signedPhase, ite_true]
    · rcases hx with hx | hx
      · exact Or.inl (Or.inl hx)
      · exact Or.inr (Or.inl hx)
  · rintro ((hx | ⟨n, rfl⟩) | (hx | ⟨n, rfl⟩))
    · exact Or.inr (Or.inl hx)
    · exact Or.inl ⟨⟨n+1, Nat.succ_pos n⟩, true, rfl⟩
    · exact Or.inr (Or.inr hx)
    · exact Or.inl ⟨⟨n+1, Nat.succ_pos n⟩, false, rfl⟩

/-- Compactness is supplied by the actual rapid-tail convergence. -/
theorem signedPhaseClosure_isCompact {P R : ℕ} (hP : 1 ≤ P) (hR : 1 ≤ R) :
    IsCompact (signedPhaseClosure P R) := by
  rw [signedPhaseClosure_eq_insert_ranges]
  exact (positivePhaseSequence_tendsto hP hR).isCompact_insert_range.union
    (by simpa using (positivePhaseSequence_tendsto hP hR).neg.isCompact_insert_range)

/-- All closed signed phases lie in the closed half-cell. -/
theorem signedPhaseClosure_subset_Icc {P R : ℕ} (hP : 1 ≤ P) (hR : 1 ≤ R) :
    signedPhaseClosure P R ⊆ Icc (-(1 / 2) : ℝ) (1 / 2) := by
  rintro x (⟨j, positive, rfl⟩ | hx)
  · have h := abs_lt.mp (abs_signedPhase_lt_half hP hR j positive)
    constructor <;> linarith
  · rcases hx with rfl | hx
    · norm_num
    · rcases hx with rfl
      norm_num

/-- The advertised signed phase set is exactly the topological closure. -/
theorem closure_phaseSet {P R : ℕ} (hP : 1 ≤ P) (hR : 1 ≤ R) :
    closure (phaseSet P R) = signedPhaseClosure P R := by
  apply le_antisymm
  · apply closure_minimal (fun _ hx => Or.inl hx)
    exact (signedPhaseClosure_isCompact hP hR).isClosed
  · rintro x (hx | hx)
    · exact subset_closure hx
    · rcases hx with rfl | hx
      · apply mem_closure_of_tendsto (positivePhaseSequence_tendsto hP hR)
        exact Eventually.of_forall fun n => ⟨⟨n+1, Nat.succ_pos n⟩, true, rfl⟩
      · rcases hx with rfl
        apply mem_closure_of_tendsto ((positivePhaseSequence_tendsto hP hR).neg)
        exact Eventually.of_forall fun n => ⟨⟨n+1, Nat.succ_pos n⟩, false, rfl⟩

/-- Integer translates of the compact signed closure recover the explicit periodic set. -/
theorem periodicPhaseSet_eq_iUnion_signedClosure (P R : ℕ) :
    periodicPhaseSet P R = ⋃ n : ℤ,
      (fun β : ℝ => (n : ℝ) + β) '' signedPhaseClosure P R := by
  ext x
  constructor
  · rintro ⟨n, β, hβ, rfl⟩
    refine mem_iUnion.mpr ⟨n, β, ?_, rfl⟩
    rcases hβ with hβ | rfl
    · exact Or.inl hβ
    · exact Or.inr (Or.inl rfl)
  · intro hx
    obtain ⟨n, β, hβ, rfl⟩ := mem_iUnion.mp hx
    rcases hβ with hβ | hβ
    · exact ⟨n, β, Or.inl hβ, rfl⟩
    · rcases hβ with rfl | hβ
      · exact ⟨n, 1/2, Or.inr rfl, rfl⟩
      · rcases hβ with rfl
        refine ⟨n-1, 1/2, Or.inr rfl, ?_⟩
        push_cast
        ring

/-- Only finitely many translated compact half-cells meet any small neighbourhood. -/
theorem signedPhaseClosure_translates_locallyFinite {P R : ℕ}
    (hP : 1 ≤ P) (hR : 1 ≤ R) :
    LocallyFinite (fun n : ℤ =>
      (fun β : ℝ => (n : ℝ) + β) '' signedPhaseClosure P R) := by
  intro x
  obtain ⟨N : ℕ, hN⟩ := exists_nat_gt (|x| + 2)
  refine ⟨Ioo (x-1) (x+1), Ioo_mem_nhds (by linarith) (by linarith), ?_⟩
  apply (Set.finite_Icc (-(N : ℤ)) (N : ℤ)).subset
  rintro n ⟨y, ⟨β, hβ, rfl⟩, hylo, hyhi⟩
  obtain ⟨hβlo, hβhi⟩ := signedPhaseClosure_subset_Icc hP hR hβ
  have hxlo := neg_abs_le x
  have hxhi := le_abs_self x
  have hlo : -(N : ℝ) ≤ n := by linarith
  have hhi : (n : ℝ) ≤ N := by linarith
  constructor
  · exact_mod_cast hlo
  · exact_mod_cast hhi

/-- The complete periodic phase set is closed, not locally finite at its seams. -/
theorem periodicPhaseSet_isClosed {P R : ℕ} (hP : 1 ≤ P) (hR : 1 ≤ R) :
    IsClosed (periodicPhaseSet P R) := by
  rw [periodicPhaseSet_eq_iUnion_signedClosure]
  apply (signedPhaseClosure_translates_locallyFinite hP hR).isClosed_iUnion
  intro n
  exact ((signedPhaseClosure_isCompact hP hR).image
    (continuous_const.add continuous_id)).isClosed

/-- Closedness together with countability gives nowhere density. -/
theorem periodicPhaseSet_isNowhereDense {P R : ℕ} (hP : 1 ≤ P) (hR : 1 ≤ R) :
    IsNowhereDense (periodicPhaseSet P R) := by
  rw [(periodicPhaseSet_isClosed hP hR).isNowhereDense_iff]
  exact interior_eq_empty_iff_dense_compl.mpr ((periodicPhaseSet_countable P R).dense_compl ℝ)

/-- No isolated signed phase or seam is the zero phase. -/
theorem zero_not_mem_signedPhaseClosure {P R : ℕ} (hP : 1 ≤ P) (hR : 1 ≤ R) :
    (0 : ℝ) ∉ signedPhaseClosure P R := by
  rintro (⟨j, positive, hzero⟩ | hzero)
  · have hp := (blockPhase_mem_Ioo hP hR j).1
    cases positive <;> simp only [signedPhase, Bool.false_eq_true, ite_false, ite_true] at hzero
    all_goals linarith
  · norm_num at hzero

/-- Periodization adds no integer phase; in particular zero remains excluded. -/
theorem zero_not_mem_periodicPhaseSet {P R : ℕ} (hP : 1 ≤ P) (hR : 1 ≤ R) :
    (0 : ℝ) ∉ periodicPhaseSet P R := by
  rw [periodicPhaseSet_eq_iUnion_signedClosure]
  intro hzero
  obtain ⟨n, β, hβ, heq⟩ := mem_iUnion.mp hzero
  obtain ⟨hlo, hhi⟩ := signedPhaseClosure_subset_Icc hP hR hβ
  have hnlo : (-1 : ℝ) < n := by linarith
  have hnhi : (n : ℝ) < 1 := by linarith
  have hnlo' : (-1 : ℤ) < n := by exact_mod_cast hnlo
  have hnhi' : n < 1 := by exact_mod_cast hnhi
  have hn : n = 0 := by omega
  have hβzero : β = 0 := by simpa [hn] using heq
  exact zero_not_mem_signedPhaseClosure hP hR (hβzero ▸ hβ)

/-- Deleting a point other than the limit from a convergent sequence preserves compactness. -/
theorem compact_insert_range_sdiff_singleton {f : ℕ → ℝ} {l x : ℝ}
    (ht : Tendsto f atTop (𝓝 l)) (hx : x ≠ l) :
    IsCompact ((insert l (range f)) \ {x}) := by
  classical
  let g : ℕ → ℝ := fun n => if f n = x then l else f n
  have hg : Tendsto g atTop (𝓝 l) := by
    apply ht.congr'
    filter_upwards [ht.eventually_ne hx.symm] with n hn
    simp only [g, hn, ite_false]
  have heq : insert l (range g) = (insert l (range f)) \ {x} := by
    ext y
    constructor
    · rintro (rfl | ⟨n, rfl⟩)
      · exact ⟨Or.inl rfl, hx.symm⟩
      · by_cases hn : f n = x
        · simp only [g, hn, ite_true]
          exact ⟨Or.inl rfl, hx.symm⟩
        · simp only [g, hn, ite_false]
          exact ⟨Or.inr ⟨n, rfl⟩, hn⟩
    · rintro ⟨hy, hyx⟩
      rcases hy with rfl | ⟨n, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨n, by simp only [g, show f n ≠ x from hyx, ite_false]⟩
  rw [← heq]
  exact hg.isCompact_insert_range

/-- Away from the two seams, removal of a signed phase leaves a compact set. -/
theorem signedPhaseClosure_sdiff_singleton_isCompact {P R : ℕ}
    (hP : 1 ≤ P) (hR : 1 ≤ R) {x : ℝ}
    (hpos : x ≠ 1 / 2) (hneg : x ≠ -(1 / 2)) :
    IsCompact (signedPhaseClosure P R \ {x}) := by
  rw [signedPhaseClosure_eq_insert_ranges, union_sdiff_distrib]
  exact (compact_insert_range_sdiff_singleton (positivePhaseSequence_tendsto hP hR) hpos).union
    (compact_insert_range_sdiff_singleton (positivePhaseSequence_tendsto hP hR).neg hneg)

/-- Deleting a non-seam point from the periodic closure leaves a closed set. -/
theorem periodicPhaseSet_sdiff_singleton_isClosed {P R : ℕ}
    (hP : 1 ≤ P) (hR : 1 ≤ R) {x : ℝ}
    (hseam : ∀ n : ℤ, x ≠ (n : ℝ) + 1 / 2) :
    IsClosed (periodicPhaseSet P R \ {x}) := by
  rw [periodicPhaseSet_eq_iUnion_signedClosure, iUnion_sdiff]
  apply ((signedPhaseClosure_translates_locallyFinite hP hR).subset
    (fun _ => sdiff_subset)).isClosed_iUnion
  intro n
  have hpos : x - (n : ℝ) ≠ 1 / 2 := by
    intro h
    exact hseam n (by linarith)
  have hneg : x - (n : ℝ) ≠ -(1 / 2) := by
    intro h
    apply hseam (n-1)
    push_cast
    linarith
  have heq : ((fun β : ℝ => (n : ℝ) + β) '' signedPhaseClosure P R) \ {x} =
      (fun β : ℝ => (n : ℝ) + β) '' (signedPhaseClosure P R \ {x - n}) := by
    ext y
    constructor
    · rintro ⟨⟨β, hβ, rfl⟩, hne⟩
      refine ⟨β, ⟨hβ, ?_⟩, rfl⟩
      intro h
      apply hne
      change (n : ℝ) + β = x
      change β = x - (n : ℝ) at h
      linarith
    · rintro ⟨β, ⟨hβ, hne⟩, rfl⟩
      refine ⟨⟨β, hβ, rfl⟩, ?_⟩
      intro h
      apply hne
      change β = x - (n : ℝ)
      change (n : ℝ) + β = x at h
      linarith
  rw [heq]
  exact ((signedPhaseClosure_sdiff_singleton_isCompact hP hR hpos hneg).image
    (continuous_const.add continuous_id)).isClosed

/-- Every periodic phase away from the half-integer seam is isolated in the complete closure. -/
theorem periodicPhaseSet_point_isolated {P R : ℕ} (hP : 1 ≤ P) (hR : 1 ≤ R)
    {x : ℝ} (hx : x ∈ periodicPhaseSet P R)
    (hseam : ∀ n : ℤ, x ≠ (n : ℝ) + 1 / 2) :
    ∃ U : Set ℝ, IsOpen U ∧ U ∩ periodicPhaseSet P R = {x} := by
  refine ⟨(periodicPhaseSet P R \ {x})ᶜ,
    (periodicPhaseSet_sdiff_singleton_isClosed hP hR hseam).isOpen_compl, ?_⟩
  ext y
  constructor
  · rintro ⟨hy, hyS⟩
    by_contra hyx
    exact hy ⟨hyS, hyx⟩
  · rintro rfl
    exact ⟨fun h => h.2 rfl, hx⟩

/-- Every half-integer seam is in the periodic phase set by its explicit formula. -/
theorem halfInteger_mem_periodicPhaseSet (P R : ℕ) (n : ℤ) :
    (n : ℝ) + 1 / 2 ∈ periodicPhaseSet P R :=
  ⟨n, 1 / 2, Or.inr rfl, rfl⟩

/-- No half-integer seam has accidentally entered the actual atom set. -/
theorem halfInteger_not_mem_blockSet {P R : ℕ} (hP : 1 ≤ P) (hR : 1 ≤ R) (n : ℤ) :
    (n : ℝ) + 1 / 2 ∉ blockSet P R := by
  rintro ⟨j, positive, m, _, heq⟩
  obtain ⟨hlo, hhi⟩ := abs_lt.mp (abs_signedPhase_lt_half hP hR j positive)
  have hmlo : (n : ℝ) < m := by linarith
  have hmhi : (m : ℝ) < (n : ℝ) + 1 := by linarith
  have hmlo' : n < m := by exact_mod_cast hmlo
  have hmhi' : m < n + 1 := by exact_mod_cast hmhi
  omega

/-- Every seam is a genuine accumulation point, not an isolated extra point. -/
theorem halfInteger_mem_closure_without_self {P R : ℕ}
    (hP : 1 ≤ P) (hR : 1 ≤ R) (n : ℤ) :
    (n : ℝ) + 1 / 2 ∈ closure (periodicPhaseSet P R \ {(n : ℝ) + 1 / 2}) := by
  apply mem_closure_of_tendsto ((positivePhaseSequence_tendsto hP hR).const_add (n : ℝ))
  apply Eventually.of_forall
  intro k
  refine ⟨⟨n, positivePhaseSequence P R k,
    Or.inl ⟨⟨k+1, Nat.succ_pos k⟩, true, rfl⟩, rfl⟩, ?_⟩
  intro heq
  have hphase := (blockPhase_mem_Ioo hP hR ⟨k+1, Nat.succ_pos k⟩).2
  change (n : ℝ) + blockPhase P R ⟨k+1, Nat.succ_pos k⟩ = (n : ℝ) + 1 / 2 at heq
  linarith

end
end MeyerGeneralProblem.Adaptive
