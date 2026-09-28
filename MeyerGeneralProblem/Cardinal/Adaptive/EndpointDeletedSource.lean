module

public import MeyerGeneralProblem.Cardinal.Adaptive.EndpointPoissonSource

@[expose] public section

/-! # Actual normalized finite endpoint source on its deleted carriers -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open scoped FourierTransform BigOperators

/-- Interior triangular-hole indices and the single endpoint hole list. -/
abbrev EndpointHoleIndex (k : ℕ) := TriangularHoleIndex k ⊕ Fin (2*k)

/-- The actual carrier point removed by a finite endpoint hole index. -/
def endpointHolePoint {k : ℕ} (α : Fin k → ℝ) :
    EndpointHoleIndex k → (endpointCosetCarrier α).subtype
  | .inl h => endpointPoint α (some (h.1,h.2.1)) (triangularHoleCell h)
  | .inr n => endpointPoint α none (-(k : ℤ)+(n : ℕ))

/-- Exactly the actual interior triangular holes and the single endpoint's
`-k,...,k-1` holes. -/
def endpointHoleSet {k : ℕ} (α : Fin k → ℝ) : Set ℝ :=
  Set.range (fun h => (endpointHolePoint α h : ℝ))

/-- The complete finite coset carrier after removing exactly the prescribed holes. -/
def endpointDeletedCarrier {k : ℕ} (α : Fin k → ℝ) : LocallyFiniteCarrier :=
  deleteCarrier (endpointCosetCarrier α) (endpointHoleSet α)

/-- Whole canonical endpoint distribution, normalized at its coefficient corner. -/
def normalizedEndpointSource {k : ℕ} (α β : Fin k → ℝ)
    (ha : Function.Injective α) (hb : Function.Injective β)
    (hia : ∀ i, 0 < α i ∧ α i < 1/2) (hib : ∀ i, 0 < β i ∧ β i < 1/2) :
    TemperedDistribution ℝ ℂ :=
  endpointPoissonSynthesis α β (normalizedEndpointMatrix α β ha hb hia hib)

theorem normalizedEndpointSource_physical_holes {k : ℕ} (α β : Fin k → ℝ)
    (ha : Function.Injective α) (hb : Function.Injective β)
    (hia : ∀ i, 0 < α i ∧ α i < 1/2) (hib : ∀ i, 0 < β i ∧ β i < 1/2)
    (h : EndpointHoleIndex k) :
    normalizedEndpointSource α β ha hb hia hib
      ((endpointCosetCarrier α).isolationSchwartz (endpointHolePoint α h)) = 0 := by
  have hz := normalizedEndpointMatrix_observation α β ha hb hia hib
  cases h with
  | inl h =>
    have he := congrFun (congrArg (fun q => q.1) hz) (.inl h)
    change endpointRow β (normalizedEndpointMatrix α β ha hb hia hib)
      (some (h.1,h.2.1)) (triangularHoleCell h)=0 at he
    exact (endpointCoefficient_synthesis α β ha hia _ _ _).trans he
  | inr n =>
    have he := congrFun (congrArg (fun q => q.2.1) hz) n
    exact (endpointCoefficient_synthesis α β ha hia _ _ _).trans he

theorem normalizedEndpointSource_spectral_holes {k : ℕ} (α β : Fin k → ℝ)
    (ha : Function.Injective α) (hb : Function.Injective β)
    (hia : ∀ i, 0 < α i ∧ α i < 1/2) (hib : ∀ i, 0 < β i ∧ β i < 1/2)
    (h : EndpointHoleIndex k) :
    𝓕 (normalizedEndpointSource α β ha hb hia hib)
      ((endpointCosetCarrier β).isolationSchwartz (endpointHolePoint β h)) = 0 := by
  have hz := normalizedEndpointMatrix_observation α β ha hb hia hib
  cases h with
  | inl h =>
    have he := congrFun (congrArg (fun q => q.1) hz) (.inr h)
    change endpointFourierRow α β (normalizedEndpointMatrix α β ha hb hia hib)
      (some (h.1,h.2.1)) (triangularHoleCell h)=0 at he
    exact (endpointCoefficient_fourier_synthesis α β hb hib _ _ _).trans he
  | inr n =>
    have he := congrFun (congrArg (fun q => q.2.2.1) hz) n
    exact (endpointCoefficient_fourier_synthesis α β hb hib _ _ _).trans he

/-- Both complete value-only deleted carrier records follow from the actual
whole Poisson formulas and the constructed square inverse. -/
theorem normalizedEndpointSource_atomic_records {k : ℕ} (α β : Fin k → ℝ)
    (ha : Function.Injective α) (hb : Function.Injective β)
    (hia : ∀ i, 0 < α i ∧ α i < 1/2) (hib : ∀ i, 0 < β i ∧ β i < 1/2) :
    AtomicOnCarrier (endpointDeletedCarrier α) (normalizedEndpointSource α β ha hb hia hib) ∧
    AtomicOnCarrier (endpointDeletedCarrier β) (𝓕 (normalizedEndpointSource α β ha hb hia hib)) := by
  have hbase := endpointPoissonSynthesis_atomic α β (normalizedEndpointMatrix α β ha hb hia hib)
  constructor
  · apply (atomicOn_deleteCarrier_iff _ _ _).mpr
    refine ⟨hbase.1,?_⟩
    intro x hx
    obtain ⟨h,hh⟩ := hx
    have he : x=endpointHolePoint α h := Subtype.ext hh.symm
    rw [he]
    exact normalizedEndpointSource_physical_holes α β ha hb hia hib h
  · apply (atomicOn_deleteCarrier_iff _ _ _).mpr
    refine ⟨hbase.2,?_⟩
    intro x hx
    obtain ⟨h,hh⟩ := hx
    have he : x=endpointHolePoint β h := Subtype.ext hh.symm
    rw [he]
    exact normalizedEndpointSource_spectral_holes α β ha hb hia hib h

/-- The normalized source is genuinely nonzero, including when the head is empty. -/
theorem normalizedEndpointSource_ne_zero {k : ℕ} (α β : Fin k → ℝ)
    (ha : Function.Injective α) (hb : Function.Injective β)
    (hia : ∀ i, 0 < α i ∧ α i < 1/2) (hib : ∀ i, 0 < β i ∧ β i < 1/2) :
    normalizedEndpointSource α β ha hb hia hib ≠ 0 := by
  intro hz
  have hc : normalizedEndpointMatrix α β ha hb hia hib = 0 :=
    endpointPoissonSynthesis_injective α β ha hb hia hib (hz.trans (map_zero _).symm)
  have he := normalizedEndpointMatrix_corner α β ha hb hia hib
  rw [hc] at he
  exact zero_ne_one he

/-- Each whole endpoint source is represented in the original first Hermite layer. -/
theorem normalizedEndpointSource_native_one {k : ℕ} (α β : Fin k → ℝ)
    (ha : Function.Injective α) (hb : Function.Injective β)
    (hia : ∀ i, 0 < α i ∧ α i < 1/2) (hib : ∀ i, 0 < β i ∧ β i < 1/2) :
    normalizedEndpointSource α β ha hb hia hib ∈ originalNativeDistributionSpace 1 :=
  endpointPoissonSynthesis_native_one α β _

end
end MeyerGeneralProblem.Adaptive
