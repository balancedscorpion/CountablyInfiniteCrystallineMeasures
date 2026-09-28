module

public import Mathlib.Analysis.Distribution.TemperedDistribution
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# A complete crystalline-measure space of countably infinite Hamel dimension

There exists a locally finite set Λ in the real line for which the **entire**
space of tempered distributions locally given by atomic measures on Λ, whose
Fourier transforms have the same property, has complex Hamel dimension ℵ₀.
Every such distribution has a unique finite expansion in one countable family.
Fourier transformation uses the kernel exp(-2πixξ).

Local atomicity is stated on compactly supported Schwartz tests, so derivatives
of point masses are excluded. Temperedness means continuity on Schwartz space;
no additional polynomial bound on the total variation is imposed. Support and
spectrum are contained in Λ, and need not equal Λ. The carrier is existentially
constructed; this is not a classification of arbitrary carriers.

The single `sorry` is the intentional Comparator statement placeholder.
-/

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

/-- One locally finite carrier has complete Hamel dimension ℵ₀. A single
countable family gives a unique finite expansion of every admissible source,
and every finite expansion is admissible. No supplied source, rank bound,
construction certificate, or exhaustion hypothesis is assumed. -/
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
  sorry

end CountablyInfiniteCrystallineMeasures
