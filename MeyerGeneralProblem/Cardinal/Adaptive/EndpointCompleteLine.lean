module

public import MeyerGeneralProblem.Cardinal.Adaptive.EndpointSourceExhaustion

@[expose] public section

/-! # The complete finite endpoint source is one line -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open scoped FourierTransform BigOperators

/-- Actual deleted records force all finite observations except the unique
corner to vanish for the uniquely recovered whole Poisson coefficients. -/
theorem endpointDeleted_poisson_observation {k : ℕ} (α β : Fin k → ℝ)
    (ha : Function.Injective α) (hb : Function.Injective β)
    (hia : ∀ i, 0 < α i ∧ α i < 1/2) (hib : ∀ i, 0 < β i ∧ β i < 1/2)
    (c : EndpointMatrix k)
    (hT : AtomicOnCarrier (endpointDeletedCarrier α) (endpointPoissonSynthesis α β c))
    (hFT : AtomicOnCarrier (endpointDeletedCarrier β) (𝓕 (endpointPoissonSynthesis α β c))) :
    endpointObservation α β c=(0,0,0,c none none) := by
  have hA := ((atomicOn_deleteCarrier_iff _ _ _).mp hT).2
  have hB := ((atomicOn_deleteCarrier_iff _ _ _).mp hFT).2
  have hzA (h : EndpointHoleIndex k) :
      endpointPoissonSynthesis α β c
        ((endpointCosetCarrier α).isolationSchwartz (endpointHolePoint α h))=0 :=
    hA _ ⟨h,rfl⟩
  have hzB (h : EndpointHoleIndex k) :
      𝓕 (endpointPoissonSynthesis α β c)
        ((endpointCosetCarrier β).isolationSchwartz (endpointHolePoint β h))=0 :=
    hB _ ⟨h,rfl⟩
  apply Prod.ext
  · funext h
    cases h with
    | inl h =>
      change endpointRow β c (some (h.1,h.2.1)) (triangularHoleCell h)=0
      rw [← endpointCoefficient_synthesis α β ha hia]
      exact hzA (.inl h)
    | inr h =>
      change endpointFourierRow α β c (some (h.1,h.2.1)) (triangularHoleCell h)=0
      rw [← endpointCoefficient_fourier_synthesis α β hb hib]
      exact hzB (.inl h)
  · apply Prod.ext
    · funext n
      change endpointRow β c none (-(k : ℤ)+(n : ℕ))=0
      rw [← endpointCoefficient_synthesis α β ha hia]
      exact hzA (.inr n)
    · apply Prod.ext
      · funext n
        change endpointFourierRow α β c none (-(k : ℤ)+(n : ℕ))=0
        rw [← endpointCoefficient_fourier_synthesis α β hb hib]
        exact hzB (.inr n)
      · rfl

/-- Every whole tempered distribution with the exact two deleted endpoint
records lies on the constructed line; no native order or representation is assumed. -/
theorem endpointDeletedSource_exists_smul {k : ℕ} (α β : Fin k → ℝ)
    (ha : Function.Injective α) (hb : Function.Injective β)
    (hia : ∀ i, 0 < α i ∧ α i < 1/2) (hib : ∀ i, 0 < β i ∧ β i < 1/2)
    (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier (endpointDeletedCarrier α) T)
    (hFT : AtomicOnCarrier (endpointDeletedCarrier β) (𝓕 T)) :
    ∃ z : ℂ, T=z • normalizedEndpointSource α β ha hb hia hib := by
  have hA := ((atomicOn_deleteCarrier_iff _ _ _).mp hT).1
  have hB := ((atomicOn_deleteCarrier_iff _ _ _).mp hFT).1
  obtain ⟨c,hc,_⟩ := endpointSource_existsUnique_poisson α β ha hb hia hib T hA hB
  have hobs := endpointDeleted_poisson_observation α β ha hb hia hib c (hc.symm ▸ hT) (hc.symm ▸ hFT)
  have he := endpointMatrix_eq_corner_smul α β ha hb hia hib c hobs
  refine ⟨c none none,?_⟩
  calc
    T = endpointPoissonSynthesis α β c := hc.symm
    _ = endpointPoissonSynthesis α β (c none none • normalizedEndpointMatrix α β ha hb hia hib) := congrArg _ he
    _ = _ := map_smul _ _ _

/-- Equality with a genuine nonzero line is a theorem about the full two-sided
source submodule, including every distribution at either accumulation seam. -/
theorem endpointDeletedSource_eq_span {k : ℕ} (α β : Fin k → ℝ)
    (ha : Function.Injective α) (hb : Function.Injective β)
    (hia : ∀ i, 0 < α i ∧ α i < 1/2) (hib : ∀ i, 0 < β i ∧ β i < 1/2) :
    pairedAtomicSource (endpointDeletedCarrier α) (endpointDeletedCarrier β) =
      Submodule.span ℂ {normalizedEndpointSource α β ha hb hia hib} := by
  apply le_antisymm
  · intro T hT
    obtain ⟨z,hz⟩ := endpointDeletedSource_exists_smul α β ha hb hia hib T hT.1 hT.2
    rw [hz]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  · apply Submodule.span_le.mpr
    intro T hT
    rcases Set.mem_singleton_iff.mp hT with rfl
    exact normalizedEndpointSource_atomic_records α β ha hb hia hib

/-- Full source dimension is one; finite dimensionality is established by the
actual span equality before evaluating the dimension. -/
theorem endpointDeletedSource_finrank {k : ℕ} (α β : Fin k → ℝ)
    (ha : Function.Injective α) (hb : Function.Injective β)
    (hia : ∀ i, 0 < α i ∧ α i < 1/2) (hib : ∀ i, 0 < β i ∧ β i < 1/2) :
    Module.finrank ℂ (pairedAtomicSource (endpointDeletedCarrier α) (endpointDeletedCarrier β))=1 := by
  rw [endpointDeletedSource_eq_span α β ha hb hia hib]
  exact finrank_span_singleton (normalizedEndpointSource_ne_zero α β ha hb hia hib)

end
end MeyerGeneralProblem.Adaptive
