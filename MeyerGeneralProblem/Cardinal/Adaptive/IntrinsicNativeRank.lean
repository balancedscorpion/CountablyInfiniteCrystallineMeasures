module

public import MeyerGeneralProblem.Cardinal.Adaptive.ActualHoleExchange
public import MeyerGeneralProblem.Hermite.DistributionCoherence

/-! The local atomic interface needed by exhaustive finite synthesis. -/
@[expose] public section
noncomputable section
namespace MeyerGeneralProblem.Adaptive

/-- The complete paired vanishing-ideal source equals the intrinsic distributional
Meyer space, using the proved local atomic representation in both directions. -/
theorem pairedAtomicSource_eq_distributionalMeyerSpace (S : LocallyFiniteCarrier) :
    pairedAtomicSource S S=DistributionalMeyerSpace S := by
  ext T
  rw [mem_pairedAtomicSource,mem_distributionalMeyerSpace_iff,
    atomicOnCarrier_iff_hasLocallyAtomicAction,atomicOnCarrier_iff_hasLocallyAtomicAction]

end MeyerGeneralProblem.Adaptive
