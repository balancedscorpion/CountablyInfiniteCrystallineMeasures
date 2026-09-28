module

public import MeyerGeneralProblem.Cardinal.Adaptive.EndpointReflection

@[expose] public section

/-! # Exact Fourier normalization of the complete finite endpoint line -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open scoped FourierTransform BigOperators

theorem endpointCharacter_flip {k : ℕ} (α : Fin k → ℝ) (a : EndpointPhaseIndex k) (n : ℤ) :
    criticalCharacter (-n) (endpointPhase α a)=criticalCharacter n (endpointPhase α (endpointFlip a)) := by
  cases a with
  | none =>
    simp only [endpointPhase,endpointFlip,criticalCharacter,Complex.ofReal_div,Complex.ofReal_one,
      Complex.ofReal_ofNat,Int.cast_neg]
    rw [show 2*(Real.pi : ℂ)*Complex.I*(-(n : ℂ))*(1/2) =
      2*(Real.pi : ℂ)*Complex.I*(n : ℂ)*(1/2)+((-n : ℤ) : ℂ)*(2*Real.pi*Complex.I) by push_cast; ring,
      Complex.exp_add,Complex.exp_int_mul_two_pi_mul_I,mul_one]
  | some a =>
    rcases a with ⟨i,u⟩
    cases u <;> simp [endpointPhase,endpointFlip,criticalSignedPhase,criticalCharacter] <;>
      congr 1 <;> ring

/-- Fourier preserves the entire Poisson basis with its negative phase gauge,
including the endpoint's integer-equivalent negative representative. -/
theorem fourier_endpointPoissonBasis {k : ℕ} (α β : Fin k → ℝ)
    (a b : EndpointPhaseIndex k) :
    𝓕 (wholePoissonSource (endpointPhase α a) (endpointPhase β b)) =
      endpointGauge (endpointPhase α a) (endpointPhase β b) •
        wholePoissonSource (endpointPhase β b) (endpointPhase α (endpointFlip a)) := by
  ext f
  rw [fourier_wholePoissonSource_apply,smul_apply,smul_eq_mul,wholePoissonSource_apply,← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [endpointGauge_modulation,endpointCharacter_flip]
  ring

/-- Whole Fourier action on finite coefficients, including reflection and the exact gauge. -/
def endpointFourierMatrix {k : ℕ} (α β : Fin k → ℝ) (c : EndpointMatrix k) : EndpointMatrix k :=
  fun a b => endpointGauge (endpointPhase α (endpointFlip b)) (endpointPhase β a)*c (endpointFlip b) a

theorem fourier_endpointPoissonSynthesis {k : ℕ} (α β : Fin k → ℝ) (c : EndpointMatrix k) :
    𝓕 (endpointPoissonSynthesis α β c)=endpointPoissonSynthesis β α (endpointFourierMatrix α β c) := by
  change temperedFourierLinearMap (∑ a,∑ b,c a b •wholePoissonSource _ _) = _
  simp only [map_sum,map_smul,temperedFourierLinearMap_apply,fourier_endpointPoissonBasis,smul_smul]
  change _ = ∑ b,∑ a, endpointFourierMatrix α β c b a •wholePoissonSource _ _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  let e : EndpointPhaseIndex k ≃ EndpointPhaseIndex k :=
    ⟨endpointFlip,endpointFlip,endpointFlip_involutive,endpointFlip_involutive⟩
  apply Fintype.sum_equiv e
  intro a
  simp [e,endpointFourierMatrix,mul_comm]

theorem endpointGauge_corner : endpointGauge (1/2) (1/2) = -Complex.I := by
  unfold endpointGauge
  have he : -((2*Real.pi*(1/2)*(1/2) : ℝ) : ℂ)*Complex.I = -((Real.pi : ℂ)/2*Complex.I) := by
    push_cast
    ring
  rw [he,Complex.exp_neg,Complex.exp_pi_div_two_mul_I]
  simp

theorem endpointFourierMatrix_corner {k : ℕ} (α β : Fin k → ℝ) (c : EndpointMatrix k) :
    endpointFourierMatrix α β c none none = -Complex.I*c none none := by
  simp only [endpointFourierMatrix,endpointFlip,endpointPhase,endpointGauge_corner]

/-- Reflection preserves the entire value-only deleted carrier record. -/
theorem endpointDeleted_atomic_fourier_sq {k : ℕ} (α : Fin k → ℝ)
    (T : TemperedDistribution ℝ ℂ) (hT : AtomicOnCarrier (endpointDeletedCarrier α) T) :
    AtomicOnCarrier (endpointDeletedCarrier α) (𝓕 (𝓕 T)) := by
  rw [fourier_sq_eq_reflection]
  intro f hf
  rw [temperedReflectionCLM_apply]
  apply hT
  intro x hx
  rw [schwartzReflectionCLM_apply]
  exact hf _ (endpointDeletedCarrier_neg α hx)

/-- For identical heads the actual complete normalized source has Fourier
eigenvalue `-i`, fixed by its single endpoint corner and the whole-source gauge. -/
theorem normalizedEndpointSource_fourier {k : ℕ} (α : Fin k → ℝ)
    (ha : Function.Injective α) (hi : ∀ i, 0 < α i ∧ α i < 1/2) :
    𝓕 (normalizedEndpointSource α α ha ha hi hi) =
      -Complex.I • normalizedEndpointSource α α ha ha hi hi := by
  let c := normalizedEndpointMatrix α α ha ha hi hi
  let T := normalizedEndpointSource α α ha ha hi hi
  have hT := normalizedEndpointSource_atomic_records α α ha ha hi hi
  have hFT := endpointDeleted_atomic_fourier_sq α T hT.1
  have he : 𝓕 T=endpointPoissonSynthesis α α (endpointFourierMatrix α α c) :=
    fourier_endpointPoissonSynthesis α α c
  have hobs := endpointDeleted_poisson_observation α α ha ha hi hi
    (endpointFourierMatrix α α c) (he ▸ hT.2) (he ▸ hFT)
  have hc := endpointMatrix_eq_corner_smul α α ha ha hi hi (endpointFourierMatrix α α c) hobs
  have hcorner : endpointFourierMatrix α α c none none = -Complex.I := by
    rw [endpointFourierMatrix_corner]
    dsimp [c]
    rw [normalizedEndpointMatrix_corner,mul_one]
  rw [hcorner] at hc
  change 𝓕 T = _
  rw [he,hc,map_smul]
  rfl

end
end MeyerGeneralProblem.Adaptive
