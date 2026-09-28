module

public import MeyerGeneralProblem.Cardinal.Adaptive.CriticalBlockComparison
public import MeyerGeneralProblem.Cardinal.Adaptive.CriticalForwardMap

@[expose] public section

/-! # Exact whole high-gap block equivalence with its literal rapid tail -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section

/-- The actual reindexed rapid phases are strictly interior. -/
theorem rapidTailPhase_inside (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) (j : ℕ+) :
    0 < rapidTailPhase P R j ∧ rapidTailPhase P R j < 1/2 := by
  rw [←criticalTailPhases_block_head]
  exact blockPhase_mem_Ioo hP hR _

/-- The complete rapid critical carrier equals the reindexed block carrier exactly. -/
theorem criticalPhaseTailCarrier_block_head_eq (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) :
    criticalPhaseTailCarrier (blockPhase P R) (blockPhase_mem_Ioo hP hR) (headLength R) 0=
      criticalPhaseTailCarrier (rapidTailPhase P R) (rapidTailPhase_inside P R hP hR) 0 0 := by
  apply LocallyFiniteCarrier.ext
  change criticalPhaseTailSet _ _ _=criticalPhaseTailSet _ _ _
  simp only [criticalPhaseTailSet,criticalTailPhases_block_head,criticalTailPhases_zero]

/-- The whole actual gapped block source, before any native-order restriction. -/
def actualBlockCompleteSource (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) :
    Submodule ℂ (TemperedDistribution ℝ ℂ) :=
  pairedAtomicSource (blockCarrier P R hP hR) (blockCarrier P R hP hR)

/-- The whole literal rapid critical source, with its own original cell schedule. -/
def actualRapidCompleteSource (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) :
    Submodule ℂ (TemperedDistribution ℝ ℂ) :=
  criticalCompleteSource (rapidTailPhase P R) (rapidTailPhase P R)
    (rapidTailPhase_inside P R hP hR) (rapidTailPhase_inside P R hP hR) 0

/-- Literal original native layer of the complete rapid source. -/
def actualRapidNativeSource (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) (p : ℕ) :
    Submodule ℂ (TemperedDistribution ℝ ℂ) :=
  actualRapidCompleteSource P R hP hR ⊓ originalNativeDistributionSpace p

/-- Exact source equivalence from the actual gapped block to its whole rapid tail.
Both finite surgeries are constructed and the infinite carrier is retained. -/
def actualBlockRapidEquiv (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) :
    actualBlockCompleteSource P R hP hR ≃ₗ[ℂ] actualRapidCompleteSource P R hP hR := by
  have he := criticalCompleteHeadEquiv (blockPhase P R) (blockPhase P R)
    (blockPhase_injective hP hR) (blockPhase_mem_Ioo hP hR)
    (blockPhase_injective hP hR) (blockPhase_mem_Ioo hP hR) (headLength R) (headLength_pos hR)
  unfold criticalCompleteSource at he
  rw [criticalPhaseTailCarrier_block_zero P R hP hR,criticalPhaseTailCarrier_block_head_eq P R hP hR] at he
  exact (concreteBlockHoleExchange P R hP hR).symm.trans he

/-- Complete total ranks agree by an actual whole-source equivalence. -/
theorem actualBlockRapid_rank_eq (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) :
    Module.rank ℂ (actualBlockCompleteSource P R hP hR)=
      Module.rank ℂ (actualRapidCompleteSource P R hP hR) :=
  (actualBlockRapidEquiv P R hP hR).rank_eq

/-- The complete low-order block source injects at the same original order into its rapid tail. -/
theorem actualBlockNative_rank_le_rapid (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R)
    (p : ℕ) (hp : 1 ≤ p) :
    Module.rank ℂ (actualBlockNativeSource P R hP hR p) ≤
      Module.rank ℂ (actualRapidNativeSource P R hP hR p) := by
  have he := (criticalBlockNativeSourceEquiv P R hP hR p hp).rank_eq
  have hh := (criticalNativeSource_rank_sandwich_all (blockPhase P R) (blockPhase P R)
    (blockPhase_injective hP hR) (blockPhase_mem_Ioo hP hR)
    (blockPhase_injective hP hR) (blockPhase_mem_Ioo hP hR) (headLength R) p).1
  rw [←he]
  unfold criticalOriginalNativeSource at hh
  rw [criticalPhaseTailCarrier_block_head_eq P R hP hR] at hh
  exact hh

/-- The complete rapid layer enters the actual high-gap block with exactly two original orders. -/
theorem actualRapidNative_rank_le_block (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) (p : ℕ) :
    Module.rank ℂ (actualRapidNativeSource P R hP hR p) ≤
      Module.rank ℂ (actualBlockNativeSource P R hP hR (p+2)) := by
  have hh := criticalBlockTail_rank_le_actualBlock P R hP hR (headLength R) p
  unfold criticalOriginalNativeSource at hh
  rw [criticalPhaseTailCarrier_block_head_eq P R hP hR] at hh
  exact hh

end
end MeyerGeneralProblem.Adaptive
