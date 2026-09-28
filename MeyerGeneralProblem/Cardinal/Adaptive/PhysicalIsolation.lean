module

public import MeyerGeneralProblem.Cardinal.Adaptive.IsolatedMassRecovery
public import MeyerGeneralProblem.Cardinal.Adaptive.LatticeJetDifferences

@[expose] public section

/-! # Isolated physical phases and the actual seam carrier -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open Set
open scoped Topology

/-- Every physical periodic closure point outside its actual seam lattice has
a positive isolation neighborhood in the whole closure. -/
theorem physicalPeriodicSet_isolation_radius (R : ℕ+ → ℕ) (s : ℕ+ → ℝ)
    (hR : ∀ i, 1 ≤ R i) (hs : ∀ i, s i ∈ Icc (1:ℝ) 2) (b : Label) (a : ℝ)
    (ha : a ∈ physicalPeriodicSet R s b)
    (hseam : ∀ n : ℤ, a ≠ ((n:ℝ)+1/2)/(labelScale s b)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ physicalPeriodicSet R s b, |x-a| < δ → x=a := by
  obtain ⟨z,hz,rfl⟩ := ha
  have ht := labelScale_pos s hs b
  let H := Homeomorph.mulLeft₀ (labelScale s b)⁻¹ (inv_ne_zero ht.ne')
  have hzseam : ∀ n : ℤ, z ≠ (n:ℝ)+1/2 := by
    intro n hn
    apply hseam n
    rw [hn]
    dsimp only
    ring
  have hclosed := H.isClosedMap _ (periodicPhaseSet_sdiff_singleton_isClosed b.1.pos (hR b.1) hzseam)
  have hnot : H z ∉ H '' (periodicPhaseSet b.1 (R b.1) \ {z}) := by
    rintro ⟨w,hw,he⟩
    exact hw.2 (H.injective he)
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp (hclosed.isOpen_compl.mem_nhds hnot)
  refine ⟨δ,hδ,?_⟩
  intro x hx hdist
  by_contra hne
  apply hball (show x ∈ Metric.ball (H z) δ by change dist x ((labelScale s b)⁻¹*z) < δ; simpa only [Real.dist_eq] using hdist)
  obtain ⟨w,hw,rfl⟩ := hx
  refine ⟨w,⟨hw,?_⟩,rfl⟩
  intro he
  exact hne (congrArg H he)

/-- The actual carrier augmented by one seam lattice is still locally finite.
This retains all possible seam jets until their separate coefficient argument. -/
def carrierWithSeams (L : LocallyFiniteCarrier) (t : ℝ) (ht : 0 < t) : LocallyFiniteCarrier where
  carrier := L.carrier ∪ (halfPeriodLatticeCarrier t ht).carrier
  finite_inter_Icc a b := by
    rw [Set.union_inter_distrib_right]
    exact (L.finite_inter_Icc a b).union ((halfPeriodLatticeCarrier t ht).finite_inter_Icc a b)

/-- Actual physical sectors are contained in their whole periodic closures. -/
theorem physicalSectorSet_subset_periodic (R : ℕ+ → ℕ) (s : ℕ+ → ℝ) (b : Label) :
    physicalSectorSet R s b ⊆ physicalPeriodicSet R s b :=
  Set.image_mono (blockSet_subset_periodicPhaseSet _ _)

/-- A physical closure meets the complete actual carrier precisely in its own
physical sector, because the full closures of different labels are disjoint. -/
theorem carrierSet_inter_physicalPeriodicSet (R : ℕ+ → ℕ) (s : ℕ+ → ℝ)
    (hdis : ∀ b d : Label, b ≠ d → Disjoint (physicalPeriodicSet R s b) (physicalPeriodicSet R s d))
    (b : Label) : carrierSet R s ∩ physicalPeriodicSet R s b = physicalSectorSet R s b := by
  ext x
  constructor
  · rintro ⟨hx,hxb⟩
    obtain ⟨d,hxd⟩ := Set.mem_iUnion.mp hx
    have hxflip : x ∈ physicalSectorSet R s (d.1,d.2.flip) := by
      simpa only [physicalSectorSet_eq_flipped,ReciprocalSign.flip_flip,Prod.eta] using hxd
    have hdf : (d.1,d.2.flip)=b := by
      by_contra hn
      exact Set.disjoint_left.mp (hdis _ _ hn) (physicalSectorSet_subset_periodic R s _ hxflip) hxb
    simpa only [hdf] using hxflip
  · intro hx
    refine ⟨?_,physicalSectorSet_subset_periodic R s b hx⟩
    exact Set.mem_iUnion.mpr ⟨(b.1,b.2.flip),by simpa only [physicalSectorSet_eq_flipped] using hx⟩

end
end MeyerGeneralProblem.Adaptive
