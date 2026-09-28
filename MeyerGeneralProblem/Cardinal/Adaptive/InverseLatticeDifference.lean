module

public import MeyerGeneralProblem.Cardinal.Adaptive.LatticeJetDifferences

@[expose] public section

/-! Exact inverse-Fourier finite differences from native seam support. -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open Set
open scoped FourierTransform

/-- Inverse Fourier turns negative character modulation into positive translation,
including every iterate of the character-plus-one operator. -/
theorem fourierInv_antiperiodicModulation_iter (P : ℝ) (n : ℕ) (U : TemperedDistribution ℝ ℂ) :
    𝓕⁻ ((antiperiodicModulation (-P) : TemperedDistribution ℝ ℂ → TemperedDistribution ℝ ℂ)^[n] U) =
      (antiperiodicDifference P : TemperedDistribution ℝ ℂ → TemperedDistribution ℝ ℂ)^[n] (𝓕⁻ U) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply',Function.iterate_succ_apply']
      change 𝓕⁻ (combDistributionModulation (-P)
          ((antiperiodicModulation (-P) : TemperedDistribution ℝ ℂ → TemperedDistribution ℝ ℂ)^[n] U) +
          (antiperiodicModulation (-P) : TemperedDistribution ℝ ℂ → TemperedDistribution ℝ ℂ)^[n] U) =
        combDistributionTranslation P
          ((antiperiodicDifference P : TemperedDistribution ℝ ℂ → TemperedDistribution ℝ ℂ)^[n] (𝓕⁻ U)) +
          (antiperiodicDifference P : TemperedDistribution ℝ ℂ → TemperedDistribution ℝ ℂ)^[n] (𝓕⁻ U)
      rw [FourierTransform.fourierInv_add,fourierInv_combDistributionModulation,neg_neg,ih]

/-- Ordinary native support on negative-character zeros yields a whole inverse-Fourier difference law. -/
theorem supportedOn_fourierInv_antiperiodicDifference_eq_zero (S : LocallyFiniteCarrier) (q : ℕ)
    (T : HermiteScale (-(q:ℤ)))
    (hT : DistributionSupportedOn S.carrier (hermiteScaleDistribution q T)) (P : ℝ)
    (hzero : ∀ a ∈ S.carrier, combModulationCharacter (-P) a+1 = 0) :
    (antiperiodicDifference P : TemperedDistribution ℝ ℂ → TemperedDistribution ℝ ℂ)^[2*q+1]
      (𝓕⁻ (hermiteScaleDistribution q T)) = 0 := by
  have h : (antiperiodicModulation (-P) : TemperedDistribution ℝ ℂ → TemperedDistribution ℝ ℂ)^[2*q+1]
      (hermiteScaleDistribution q T) = 0 := by
    apply distributions_eq_of_compact_test_eq
    intro f hf
    rw [antiperiodicModulation_iter_apply]
    exact supportedOn_antiperiodicTest_annihilates S q T hT (-P) hzero f hf
  rw [← fourierInv_antiperiodicModulation_iter,h,FourierTransform.fourierInv_zero]

/-- The negative character is also minus one on the same actual seam lattice. -/
theorem combModulationCharacter_neg_halfPeriod (P : ℝ) (hP : P ≠ 0) (n : ℤ) :
    combModulationCharacter (-P) (((n:ℝ)+1/2)/P) = -1 := by
  have he : ((n:ℝ)+1/2)/P = ((((-n-1:ℤ):ℝ)+1/2)/(-P)) := by
    push_cast
    field_simp
    ring
  rw [he,combModulationCharacter_halfPeriod (-P) (neg_ne_zero.mpr hP)]

/-- Native support on t times the half-integers gives the positive reciprocal
antidifference law after inverse Fourier, with exact order 2q+1. -/
theorem scaledHalfInteger_support_fourierInv_finite_difference (t : ℝ) (ht : 0 < t) (q : ℕ)
    (T : HermiteScale (-(q:ℤ)))
    (hT : DistributionSupportedOn (Set.range (fun n : ℤ => t*((n:ℝ)+1/2)))
      (hermiteScaleDistribution q T)) :
    ((combDistributionTranslation t⁻¹ + ContinuousLinearMap.id ℂ (TemperedDistribution ℝ ℂ)) :
      TemperedDistribution ℝ ℂ → TemperedDistribution ℝ ℂ)^[2*q+1]
      (𝓕⁻ (hermiteScaleDistribution q T)) = 0 := by
  have he : (halfPeriodLatticeCarrier t⁻¹ (inv_pos.mpr ht)).carrier =
      Set.range (fun n : ℤ => t*((n:ℝ)+1/2)) := by
    change Set.range (fun n : ℤ => ((n:ℝ)+1/2)/t⁻¹) = _
    congr 1
    funext n
    simp only [div_inv_eq_mul,mul_comm]
  apply supportedOn_fourierInv_antiperiodicDifference_eq_zero
    (halfPeriodLatticeCarrier t⁻¹ (inv_pos.mpr ht)) q T (he.symm ▸ hT) t⁻¹
  rintro a ⟨n,rfl⟩
  rw [combModulationCharacter_neg_halfPeriod t⁻¹ (inv_ne_zero ht.ne')]
  ring

end
end MeyerGeneralProblem.Adaptive
