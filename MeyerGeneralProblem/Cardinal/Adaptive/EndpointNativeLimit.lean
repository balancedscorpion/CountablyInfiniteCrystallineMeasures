module

public import MeyerGeneralProblem.Cardinal.Adaptive.EndpointCarrierLimit
public import MeyerGeneralProblem.Cardinal.Adaptive.EndpointFourierEigen

@[expose] public section

/-! # Original-native endpoint approximants and their nonzero limit

The exact finite sources and both carrier limits are constructed here. The
remaining analytic inputs are stated explicitly: a uniform original native
bound and one fixed nonzero Schwartz observation after scalar normalization.
-/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open scoped FourierTransform

/-- The actual complete finite endpoint source on the first `k` phases. -/
def endpointApproximation (α : ℕ+ → ℝ) (ha : Function.Injective α)
    (hi : ∀ j, 0 < α j ∧ α j < 1/2) (k : ℕ) : TemperedDistribution ℝ ℂ :=
  normalizedEndpointSource (endpointPhasePrefix α k) (endpointPhasePrefix α k)
    (endpointPhasePrefix_injective α ha k) (endpointPhasePrefix_injective α ha k)
    (endpointPhasePrefix_interior α hi k) (endpointPhasePrefix_interior α hi k)

theorem endpointApproximation_native (α : ℕ+ → ℝ) (ha : Function.Injective α)
    (hi : ∀ j, 0 < α j ∧ α j < 1/2) (k p : ℕ) (hp : 1 ≤ p) :
    ∃ U : HermiteScale (-(p : ℤ)), hermiteScaleDistribution p U=endpointApproximation α ha hi k :=
  originalNativeDistributionSpace_mono hp (normalizedEndpointSource_native_one _ _ _ _ _ _)

/-- A genuine original-native representative of the whole endpoint approximation. -/
def endpointNativeApproximation (α : ℕ+ → ℝ) (ha : Function.Injective α)
    (hi : ∀ j, 0 < α j ∧ α j < 1/2) (p : ℕ) (hp : 1 ≤ p) (k : ℕ) :
    HermiteScale (-(p : ℤ)) := (endpointApproximation_native α ha hi k p hp).choose

theorem endpointNativeApproximation_realizes (α : ℕ+ → ℝ) (ha : Function.Injective α)
    (hi : ∀ j, 0 < α j ∧ α j < 1/2) (p : ℕ) (hp : 1 ≤ p) (k : ℕ) :
    hermiteScaleDistribution p (endpointNativeApproximation α ha hi p hp k)=endpointApproximation α ha hi k :=
  (endpointApproximation_native α ha hi k p hp).choose_spec

/-- Uniform original-norm bounds and a fixed nonzero Schwartz normalization
of the constructed finite sources yield a genuine nonzero critical source.
All value-only carrier records and the Fourier eigenvalue are proved here. -/
theorem endpointNativeLimit_of_uniform_bound (α : ℕ+ → ℝ) (ha : Function.Injective α)
    (hi : ∀ j, 0 < α j ∧ α j < 1/2) (p : ℕ) (hp : 1 ≤ p)
    (z : ℕ → ℂ) (B : ℝ)
    (hB : ∀ k, ‖z k • endpointNativeApproximation α ha hi p hp k‖ ≤ B)
    (f₀ : SchwartzMap ℝ ℂ) (c : ℂ) (hc : c ≠ 0)
    (hobs : ∀ k, z k * endpointApproximation α ha hi k f₀=c) :
    ∃ U : HermiteScale (-(p : ℤ)), ‖U‖ ≤ B ∧ U ≠ 0 ∧
      AtomicOnCarrier (criticalPhaseTailCarrier α hi 0 0) (hermiteScaleDistribution p U) ∧
      AtomicOnCarrier (criticalPhaseTailCarrier α hi 0 0) (𝓕 (hermiteScaleDistribution p U)) ∧
      hermiteScaleDistribution p U f₀=c ∧
      𝓕 (hermiteScaleDistribution p U)= -Complex.I • hermiteScaleDistribution p U := by
  have hreal (k : ℕ) : hermiteScaleDistribution p (z k • endpointNativeApproximation α ha hi p hp k)=
      z k • endpointApproximation α ha hi k := by
    change hermiteScaleDistributionCLM p (z k • endpointNativeApproximation α ha hi p hp k)=_
    rw [map_smul,hermiteScaleDistributionCLM_apply,endpointNativeApproximation_realizes]
  apply exists_native_atomic_limit p _ B hB
    (fun k => endpointDeletedCarrier (endpointPhasePrefix α k))
    (fun k => endpointDeletedCarrier (endpointPhasePrefix α k))
    (criticalPhaseTailCarrier α hi 0 0) (criticalPhaseTailCarrier α hi 0 0)
    (endpointDeletedCarrier_eventually_locally_equal α ha hi)
    (endpointDeletedCarrier_eventually_locally_equal α ha hi)
  · intro k
    rw [hreal]
    intro f hf
    change z k * endpointApproximation α ha hi k f=0
    dsimp only [endpointApproximation]
    rw [(normalizedEndpointSource_atomic_records _ _ _ _ _ _).1 f hf,mul_zero]
  · intro k
    rw [hreal,FourierTransform.fourier_smul]
    intro f hf
    change z k * 𝓕 (endpointApproximation α ha hi k) f=0
    dsimp only [endpointApproximation]
    rw [(normalizedEndpointSource_atomic_records _ _ _ _ _ _).2 f hf,mul_zero]
  · exact hc
  · intro k
    rw [hreal]
    exact hobs k
  · intro k
    rw [hreal,FourierTransform.fourier_smul]
    change z k • 𝓕 (normalizedEndpointSource _ _ _ _ _ _)=_
    rw [normalizedEndpointSource_fourier]
    exact smul_comm _ _ _

end
end MeyerGeneralProblem.Adaptive
