module

public import MeyerGeneralProblem.Cardinal.Adaptive.ConstructedAlgebraicBasis
public import Mathlib.Basic.Denumerable

/-! Proof of the exact statement in Challenge.lean by the extracted exhaustive
reciprocal-source synthesis theorem. This module does not import Challenge. -/

@[expose] public section
noncomputable section
namespace CountablyInfiniteCrystallineMeasures

/-- Local finiteness: every bounded closed interval meets Λ in a finite set. -/
def LocallyFinite (Λ : Set ℝ) : Prop :=
  ∀ a b : ℝ, (Λ ∩ Set.Icc a b).Finite

/-- The compact-test action of a locally finite complex atomic measure on Λ.
Coefficients are independent of the test. The finite sum includes all points
where the test is nonzero; zero coefficients are allowed. -/
def LocallyAtomic (Λ : Set ℝ) (T : TemperedDistribution ℝ ℂ) : Prop :=
  ∃ a : Λ → ℂ, ∀ f : SchwartzMap ℝ ℂ, HasCompactSupport f →
    ∃ E : Finset Λ,
      (∀ x : Λ, x ∉ E → f x = 0) ∧ T f = ∑ x ∈ E, a x * f x

/-- Tempered distributions annihilating every Schwartz function vanishing on Λ.
For locally finite Λ this is equivalent to the local atomic formula above. -/
def atomicSpace (Λ : Set ℝ) : Submodule ℂ (TemperedDistribution ℝ ℂ) where
  carrier := {T | ∀ f : SchwartzMap ℝ ℂ, (∀ x ∈ Λ, f x = 0) → T f = 0}
  zero_mem' := by intro f _; rfl
  add_mem' := by intro T U hT hU f hf; change T f + U f = 0; rw [hT f hf, hU f hf, add_zero]
  smul_mem' := by intro c T hT f hf; change c * T f = 0; rw [hT f hf, mul_zero]

/-- The usual distributional Fourier transform, as a complex linear map. -/
def fourierLinearMap :
    TemperedDistribution ℝ ℂ →ₗ[ℂ] TemperedDistribution ℝ ℂ where
  toFun := FourierTransform.fourier
  map_add' := FourierTransform.fourier_add
  map_smul' := FourierTransform.fourier_smul

/-- The full atomic tempered space with physical and Fourier supports in Λ.
The theorem explicitly identifies membership with both local atomic formulas. -/
def meyerSpace (Λ : Set ℝ) : Submodule ℂ (TemperedDistribution ℝ ℂ) :=
  atomicSpace Λ ⊓ (atomicSpace Λ).comap fourierLinearMap

open MeyerGeneralProblem MeyerGeneralProblem.Adaptive

private theorem space_eq (S : LocallyFiniteCarrier) :
    meyerSpace S.carrier = DistributionalMeyerSpace S := by
  ext T
  change (AtomicOnCarrier S T ∧ AtomicOnCarrier S (FourierTransform.fourier T)) ↔ _
  rw [atomicOnCarrier_iff_hasLocallyAtomicAction, atomicOnCarrier_iff_hasLocallyAtomicAction]
  rfl

private theorem local_iff (S : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ) :
    LocallyAtomic S.carrier T ↔ HasLocallyAtomicAction S T := Iff.rfl

/-- The exhaustive countably infinite cardinal claim, with all witnesses constructed. -/
theorem exhaustiveCardinalClaim :
    ∃ Λ : Set ℝ, LocallyFinite Λ ∧
      Module.rank ℂ (meyerSpace Λ) = Cardinal.aleph0 ∧
      (∀ T : TemperedDistribution ℝ ℂ,
        T ∈ meyerSpace Λ ↔ LocallyAtomic Λ T ∧
          LocallyAtomic Λ (FourierTransform.fourier T)) ∧
      ∃ g : ℕ → TemperedDistribution ℝ ℂ,
        ∀ T : TemperedDistribution ℝ ℂ,
          (LocallyAtomic Λ T ∧ LocallyAtomic Λ (FourierTransform.fourier T)) ↔
            ∃! c : ℕ →₀ ℂ, Finsupp.linearCombination ℂ g c = T := by
  classical
  let : Nonempty ReciprocalSign := ⟨.forward⟩
  let e : ℕ ≃ Label := Classical.choice inferInstance
  let g : ℕ → TemperedDistribution ℝ ℂ := constructedGenerator ∘ e
  have hli : LinearIndependent ℂ g := constructedGenerator_linearIndependent.comp e e.injective
  have hrange : Set.range g = Set.range constructedGenerator := by
    exact e.surjective.range_comp constructedGenerator
  have hspan : Submodule.span ℂ (Set.range g) = DistributionalMeyerSpace constructedCarrier := by
    rw [hrange, constructedGenerator_span_eq_meyer]
  refine ⟨constructedCarrier.carrier, constructedCarrier.finite_inter_Icc, ?_, ?_, g, ?_⟩
  · rw [space_eq]
    exact constructedMeyerRank_eq_aleph0_via_synthesis
  · intro T
    rw [space_eq]
    exact Iff.rfl
  · intro T
    change (T ∈ DistributionalMeyerSpace constructedCarrier) ↔ _
    rw [← hspan]
    constructor
    · intro hT
      obtain ⟨c, hc⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).mp hT
      refine ⟨c, hc, ?_⟩
      intro d hd
      exact hli.finsuppLinearCombination_injective (hd.trans hc.symm)
    · rintro ⟨c, hc, _⟩
      rw [← hc]
      rw [← Finsupp.range_linearCombination]
      exact ⟨c, rfl⟩

end CountablyInfiniteCrystallineMeasures
