module

public import MeyerGeneralProblem.Distribution.CompactSchwartzDensity

@[expose] public section

/-!
# The complete distributional Meyer space

The distributional space is defined by its intrinsic local meaning: both a
tempered distribution and its distributional Fourier transform have locally
finite atomic formulas on the prescribed carrier.
-/

open scoped FourierTransform SchwartzMap

namespace MeyerGeneralProblem

noncomputable section

/-- The distributional Fourier transform as a complex-linear map. -/
def temperedFourierLinearMap :
    TemperedDistribution ℝ ℂ →ₗ[ℂ] TemperedDistribution ℝ ℂ where
  toFun := FourierTransform.fourier
  map_add' := FourierTransform.fourier_add
  map_smul' := FourierTransform.fourier_smul

@[simp]
theorem temperedFourierLinearMap_apply (T : TemperedDistribution ℝ ℂ) :
    temperedFourierLinearMap T = FourierTransform.fourier T :=
  rfl

/-- Tempered distributions which are locally atomic on `S`, and whose
distributional Fourier transforms are locally atomic on `S`. -/
def DistributionalMeyerSpace (S : LocallyFiniteCarrier) :
    Submodule ℂ (TemperedDistribution ℝ ℂ) where
  carrier := {T |
    HasLocallyAtomicAction S T ∧
      HasLocallyAtomicAction S (FourierTransform.fourier T)}
  zero_mem' := by
    constructor
    · exact atomicOnCarrier_hasLocallyAtomicAction S 0 (by
        intro f hf
        simp)
    · exact atomicOnCarrier_hasLocallyAtomicAction S 0 (by
        intro f hf
        simp)
  add_mem' := by
    intro T U hT hU
    constructor
    · rw [← atomicOnCarrier_iff_hasLocallyAtomicAction]
      intro f hf
      change T f + U f = 0
      rw [(hasLocallyAtomicAction_atomicOnCarrier S T hT.1) f hf,
        (hasLocallyAtomicAction_atomicOnCarrier S U hU.1) f hf,
        add_zero]
    · rw [← atomicOnCarrier_iff_hasLocallyAtomicAction]
      simpa only [FourierTransform.fourier_add] using
        (show AtomicOnCarrier S
            (FourierTransform.fourier T + FourierTransform.fourier U) by
          intro f hf
          change FourierTransform.fourier T f +
            FourierTransform.fourier U f = 0
          rw [(hasLocallyAtomicAction_atomicOnCarrier S
              (FourierTransform.fourier T) hT.2) f hf,
            (hasLocallyAtomicAction_atomicOnCarrier S
              (FourierTransform.fourier U) hU.2) f hf,
            add_zero])
  smul_mem' := by
    intro c T hT
    constructor
    · rw [← atomicOnCarrier_iff_hasLocallyAtomicAction]
      intro f hf
      change c * T f = 0
      rw [(hasLocallyAtomicAction_atomicOnCarrier S T hT.1) f hf,
        mul_zero]
    · rw [← atomicOnCarrier_iff_hasLocallyAtomicAction]
      simpa only [FourierTransform.fourier_smul] using
        (show AtomicOnCarrier S
            (c • FourierTransform.fourier T) by
          intro f hf
          change c * FourierTransform.fourier T f = 0
          rw [(hasLocallyAtomicAction_atomicOnCarrier S
              (FourierTransform.fourier T) hT.2) f hf,
            mul_zero])

@[simp]
theorem mem_distributionalMeyerSpace_iff
    (S : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ) :
    T ∈ DistributionalMeyerSpace S ↔
      HasLocallyAtomicAction S T ∧
        HasLocallyAtomicAction S (FourierTransform.fourier T) :=
  Iff.rfl

end

end MeyerGeneralProblem
