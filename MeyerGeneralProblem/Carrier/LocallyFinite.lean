module

public import MeyerGeneralProblem.Carrier.TwoSided
public import Mathlib.Topology.DiscreteSubset
import all Mathlib.Topology.DiscreteSubset

@[expose] public section

/-!
# Extensional locally finite carriers

This file provides the carrier interface used when no preferred enumeration is
part of the data.  Local finiteness is expressed on closed bounded intervals;
the resulting carrier is countable, closed, and discrete.
-/

namespace MeyerGeneralProblem

/-- A subset of the real line having finite intersection with every closed
bounded interval. -/
structure LocallyFiniteCarrier where
  /-- The underlying extensional carrier. -/
  carrier : Set ℝ
  /-- Every bounded closed interval contains only finitely many carrier points. -/
  finite_inter_Icc : ∀ a b : ℝ, (carrier ∩ Set.Icc a b).Finite

namespace LocallyFiniteCarrier

@[ext]
theorem ext {S T : LocallyFiniteCarrier} (h : S.carrier = T.carrier) : S = T := by
  cases S
  cases T
  cases h
  rfl

variable (S : LocallyFiniteCarrier)

/-- The type of points of an extensional carrier. -/
def subtype := S.carrier

theorem finite_inter_Ico (a b : ℝ) :
    (S.carrier ∩ Set.Ico a b).Finite :=
  (S.finite_inter_Icc a b).subset fun _ hx ↦ ⟨hx.1, Set.Ico_subset_Icc_self hx.2⟩

theorem finite_inter_Ioo (a b : ℝ) :
    (S.carrier ∩ Set.Ioo a b).Finite :=
  (S.finite_inter_Icc a b).subset fun _ hx ↦ ⟨hx.1, Set.Ioo_subset_Icc_self hx.2⟩

/-- A subcarrier of a locally finite carrier is locally finite. -/
def restrict (T : Set ℝ) (hT : T ⊆ S.carrier) : LocallyFiniteCarrier where
  carrier := T
  finite_inter_Icc a b :=
    (S.finite_inter_Icc a b).subset fun _ hx ↦ ⟨hT hx.1, hx.2⟩

@[simp]
theorem restrict_carrier (T : Set ℝ) (hT : T ⊆ S.carrier) :
    (S.restrict T hT).carrier = T := rfl

/-- Every locally finite carrier on the real line is countable. -/
theorem countable_carrier : S.carrier.Countable := by
  refine (Set.countable_iUnion fun n : ℕ ↦
    (S.finite_inter_Icc (-(n : ℝ)) n).countable).mono ?_
  intro x hx
  obtain ⟨n : ℕ, hn : |x| < n⟩ := exists_nat_gt |x|
  refine Set.mem_iUnion.mpr ⟨n, hx, ?_⟩
  exact ⟨(abs_lt.mp hn).1.le, (abs_lt.mp hn).2.le⟩

/-- The subtype of carrier points is countable. -/
instance countable_subtype : Countable S.subtype :=
  S.countable_carrier.to_subtype

/-- Local finiteness gives an open neighbourhood isolating every carrier node. -/
theorem point_isolated {x : ℝ} (hx : x ∈ S.carrier) :
    ∃ U : Set ℝ, IsOpen U ∧ U ∩ S.carrier = {x} := by
  let F : Set ℝ := S.carrier ∩ Set.Icc (x - 1) (x + 1)
  have hF : F.Finite := S.finite_inter_Icc (x - 1) (x + 1)
  have hxF : x ∈ F := by
    refine ⟨hx, ?_⟩
    constructor <;> linarith
  obtain ⟨U, hUopen, hUF⟩ :=
    isDiscrete_iff_forall_mem_exists_isOpen.mp hF.isDiscrete x hxF
  refine ⟨U ∩ Set.Ioo (x - 1) (x + 1), hUopen.inter isOpen_Ioo, ?_⟩
  ext y
  constructor
  · rintro ⟨⟨hyU, hylo, hyhi⟩, hyS⟩
    have hyF : y ∈ F := ⟨hyS, hylo.le, hyhi.le⟩
    have : y ∈ U ∩ F := ⟨hyU, hyF⟩
    simpa [hUF] using this
  · intro hy
    have hyx : y = x := Set.mem_singleton_iff.mp hy
    subst y
    have hxU : x ∈ U := by
      have : x ∈ U ∩ F := hUF.symm ▸ Set.mem_singleton x
      exact this.1
    exact ⟨⟨hxU, by constructor <;> linarith⟩, hx⟩

/-- The carrier is a discrete subset of the real line. -/
theorem carrier_isDiscrete : IsDiscrete S.carrier :=
  isDiscrete_iff_forall_mem_exists_isOpen.mpr fun _ hx ↦ S.point_isolated hx

/-- Every carrier node admits a positive ball meeting the carrier only there. -/
theorem exists_isolationRadius {x : ℝ} (hx : x ∈ S.carrier) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball x r ∩ S.carrier = {x} :=
  Metric.exists_ball_inter_eq_singleton_of_mem_discrete S.carrier_isDiscrete hx

/-- A locally finite subset of the real line is closed. -/
theorem carrier_isClosed : IsClosed S.carrier := by
  rw [← isOpen_compl_iff]
  apply isOpen_iff_forall_mem_open.mpr
  intro x hx
  let F : Set ℝ := S.carrier ∩ Set.Icc (x - 1) (x + 1)
  have hF : F.Finite := S.finite_inter_Icc (x - 1) (x + 1)
  refine ⟨Set.Ioo (x - 1) (x + 1) \ F, ?_, ?_, ?_⟩
  · intro y hy
    exact fun hyS ↦ hy.2 ⟨hyS, hy.1.1.le, hy.1.2.le⟩
  · exact isOpen_Ioo.sdiff hF.isClosed
  · refine ⟨⟨by linarith, by linarith⟩, ?_⟩
    exact fun hxF ↦ hx hxF.1

end LocallyFiniteCarrier

namespace TwoSidedCarrier

/-- The ordered two-sided carrier viewed extensionally. -/
def toLocallyFinite (Λ : TwoSidedCarrier) : LocallyFiniteCarrier where
  carrier := Set.range Λ
  finite_inter_Icc := Λ.finite_carrier_inter_Icc

@[simp]
theorem toLocallyFinite_carrier (Λ : TwoSidedCarrier) :
    Λ.toLocallyFinite.carrier = Set.range Λ := rfl

end TwoSidedCarrier

end MeyerGeneralProblem
