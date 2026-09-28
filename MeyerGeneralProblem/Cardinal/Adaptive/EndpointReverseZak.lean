module

public import MeyerGeneralProblem.Cardinal.Adaptive.EndpointDeletedSource
public import MeyerGeneralProblem.Cardinal.Adaptive.GaugedReverseZak

@[expose] public section

/-! Actual complete endpoint sources paired with the literal reverse Zak chart. -/

noncomputable section
open scoped BigOperators

namespace MeyerGeneralProblem.Adaptive

/-- The entire Poisson source acts by an actual reverse Zak value; the full
infinite comb is retained and no finite coefficient certificate is assumed. -/
theorem wholePoissonSource_reverseZak (a b : ℝ) (f : SchwartzMap ℝ ℂ) :
    wholePoissonSource a b f = reverseZakChart f a b := by
  rw [wholePoissonSource_apply]
  unfold reverseZakChart reverseZakJet
  simp only [pow_zero,one_mul,iteratedDeriv_zero]
  apply tsum_congr
  intro n
  have he : criticalCharacter n b = Complex.exp (reverseZakFrequency n*b) := by
    unfold criticalCharacter reverseZakFrequency
    push_cast
    rfl
  rw [he,mul_comm]

/-- Exact finite sum of actual chart values for the complete synthesized
endpoint source, with the endpoint included once by its existing index type. -/
theorem endpointPoissonSynthesis_reverseZak {k : ℕ} (α β : Fin k → ℝ)
    (c : EndpointMatrix k) (f : SchwartzMap ℝ ℂ) :
    endpointPoissonSynthesis α β c f =
      ∑ a, ∑ b, c a b*reverseZakChart f (endpointPhase α a) (endpointPhase β b) := by
  change (∑ a, ∑ b, c a b • wholePoissonSource (endpointPhase α a) (endpointPhase β b)) f = _
  simp only [sum_apply,smul_apply,smul_eq_mul,wholePoissonSource_reverseZak]

/-- The root's actual normalized endpoint source has the same exact pairing;
its canonical matrix is substituted, not posited as a certificate. -/
theorem normalizedEndpointSource_reverseZak {k : ℕ} (α β : Fin k → ℝ)
    (ha : Function.Injective α) (hb : Function.Injective β)
    (hia : ∀ i, 0 < α i ∧ α i < 1/2) (hib : ∀ i, 0 < β i ∧ β i < 1/2)
    (f : SchwartzMap ℝ ℂ) :
    normalizedEndpointSource α β ha hb hia hib f =
      ∑ a, ∑ b, normalizedEndpointMatrix α β ha hb hia hib a b *
        reverseZakChart f (endpointPhase α a) (endpointPhase β b) :=
  endpointPoissonSynthesis_reverseZak α β _ f

/-- Exact fixed-gauge form of the same whole source pairing. The compensating
matrix factor is displayed explicitly, so the gauge cannot alter the source. -/
theorem endpointPoissonSynthesis_gaugedReverseZak {k : ℕ} (α β : Fin k → ℝ)
    (c : EndpointMatrix k) (f : SchwartzMap ℝ ℂ) :
    endpointPoissonSynthesis α β c f =
      ∑ a, ∑ b, (c a b / fixedZakGauge (endpointPhase α a) (endpointPhase β b))*
        gaugedReverseZakChart f (endpointPhase α a) (endpointPhase β b) := by
  rw [endpointPoissonSynthesis_reverseZak]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  have hn : fixedZakGauge (endpointPhase α a) (endpointPhase β b) ≠ 0 := by
    intro hz
    have hh := fixedZakGauge_norm (endpointPhase α a) (endpointPhase β b)
    rw [hz,norm_zero] at hh
    exact zero_ne_one hh
  rw [gaugedReverseZakChart,← mul_assoc,div_mul_cancel₀ _ hn]

end MeyerGeneralProblem.Adaptive
