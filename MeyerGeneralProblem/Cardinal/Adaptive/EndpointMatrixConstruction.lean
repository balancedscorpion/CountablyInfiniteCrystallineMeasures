module

public import MeyerGeneralProblem.Cardinal.Adaptive.EndpointMatrixKernel

@[expose] public section

/-! # Constructed normalized finite endpoint coefficient matrix -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open scoped FourierTransform BigOperators

/-- Interior triangular holes, the two endpoint hole lists, and the single corner. -/
abbrev EndpointObservations (k : ℕ) :=
  TriangularHoleCoordinates k × (Fin (2*k) → ℂ) × (Fin (2*k) → ℂ) × ℂ

/-- The full square observation map consists of literal physical and Fourier samples. -/
def endpointObservation {k : ℕ} (α β : Fin k → ℝ) :
    EndpointMatrix k →ₗ[ℂ] EndpointObservations k where
  toFun c := (Sum.elim
    (fun h => endpointRow β c (some (h.1,h.2.1)) (triangularHoleCell h))
    (fun h => endpointFourierRow α β c (some (h.1,h.2.1)) (triangularHoleCell h)),
    (fun n => endpointRow β c none (-(k : ℤ)+(n : ℕ))),
    (fun n => endpointFourierRow α β c none (-(k : ℤ)+(n : ℕ))),c none none)
  map_add' c d := by
    apply Prod.ext
    · funext h; cases h <;> simp [endpointRow,endpointFourierRow,mul_add,Finset.sum_add_distrib]
    · apply Prod.ext
      · funext n; simp [endpointRow,mul_add,Finset.sum_add_distrib]
      · apply Prod.ext
        · funext n; simp [endpointFourierRow,mul_add,Finset.sum_add_distrib]
        · rfl
  map_smul' a c := by
    apply Prod.ext
    · funext h; cases h <;> simp [endpointRow,endpointFourierRow,Finset.mul_sum,mul_comm,mul_left_comm,mul_assoc,mul_add]
    · apply Prod.ext
      · funext n; simp [endpointRow,Finset.mul_sum,mul_comm,mul_left_comm,mul_assoc,mul_add]
      · apply Prod.ext
        · funext n; simp [endpointFourierRow,Finset.mul_sum,mul_comm,mul_left_comm,mul_assoc,mul_add]
        · rfl

theorem endpointObservation_injective {k : ℕ} (α β : Fin k → ℝ)
    (ha : Function.Injective α) (hb : Function.Injective β)
    (hia : ∀ i, 0 < α i ∧ α i < 1/2) (hib : ∀ i, 0 < β i ∧ β i < 1/2) :
    Function.Injective (endpointObservation α β) := by
  rw [← LinearMap.ker_eq_bot,Submodule.eq_bot_iff]
  intro c hc
  have hz : endpointObservation α β c = 0 := hc
  apply endpointMatrix_kernel α β ha hb hia hib c
  · exact congrArg (fun q => q.2.2.2) hz
  · intro n; exact congrFun (congrArg (fun q => q.2.1) hz) n
  · intro n; exact congrFun (congrArg (fun q => q.2.2.1) hz) n
  · intro i u n hn
    obtain ⟨h,hi,hu,hn'⟩ := triangularHoleCell_surjective i u n hn
    have he := congrFun (congrArg (fun q => q.1) hz) (.inl h)
    change endpointRow β c (some (h.1,h.2.1)) (triangularHoleCell h)=0 at he
    simpa only [hi,hu,hn'] using he
  · intro j v n hn
    obtain ⟨h,hj,hv,hn'⟩ := triangularHoleCell_surjective j v n hn
    have he := congrFun (congrArg (fun q => q.1) hz) (.inr h)
    change endpointFourierRow α β c (some (h.1,h.2.1)) (triangularHoleCell h)=0 at he
    simpa only [hj,hv,hn'] using he

/-- The actual endpoint square matrix has a constructed inverse for every
finite size, including zero interior phases. -/
def endpointObservationEquiv {k : ℕ} (α β : Fin k → ℝ)
    (ha : Function.Injective α) (hb : Function.Injective β)
    (hia : ∀ i, 0 < α i ∧ α i < 1/2) (hib : ∀ i, 0 < β i ∧ β i < 1/2) :
    EndpointMatrix k ≃ₗ[ℂ] EndpointObservations k :=
  LinearEquiv.ofInjectiveOfFinrankEq (endpointObservation α β)
    (endpointObservation_injective α β ha hb hia hib) (by
      have hd : Module.finrank ℂ (TriangularHoleCoordinates k) = 4*k^2 := by
        rw [Module.finrank_pi,Fintype.card_sum,triangularHoleIndex_card]
        ring
      simp only [EndpointObservations,Module.finrank_prod,hd]
      simp [EndpointMatrix,EndpointPhaseIndex,Module.finrank_pi_fintype]
      ring)

/-- Canonical normalized endpoint coefficient matrix with every prescribed hole zero. -/
def normalizedEndpointMatrix {k : ℕ} (α β : Fin k → ℝ)
    (ha : Function.Injective α) (hb : Function.Injective β)
    (hia : ∀ i, 0 < α i ∧ α i < 1/2) (hib : ∀ i, 0 < β i ∧ β i < 1/2) : EndpointMatrix k :=
  (endpointObservationEquiv α β ha hb hia hib).symm (0,0,0,1)

theorem normalizedEndpointMatrix_observation {k : ℕ} (α β : Fin k → ℝ)
    (ha : Function.Injective α) (hb : Function.Injective β)
    (hia : ∀ i, 0 < α i ∧ α i < 1/2) (hib : ∀ i, 0 < β i ∧ β i < 1/2) :
    endpointObservation α β (normalizedEndpointMatrix α β ha hb hia hib) = (0,0,0,1) :=
  (endpointObservationEquiv α β ha hb hia hib).apply_symm_apply _

theorem normalizedEndpointMatrix_corner {k : ℕ} (α β : Fin k → ℝ)
    (ha : Function.Injective α) (hb : Function.Injective β)
    (hia : ∀ i, 0 < α i ∧ α i < 1/2) (hib : ∀ i, 0 < β i ∧ β i < 1/2) :
    normalizedEndpointMatrix α β ha hb hia hib none none = 1 :=
  congrArg (fun q => q.2.2.2) (normalizedEndpointMatrix_observation α β ha hb hia hib)

/-- Every coefficient matrix with the prescribed actual holes is a scalar
multiple of the constructed endpoint matrix, with scalar its unique corner. -/
theorem endpointMatrix_eq_corner_smul {k : ℕ} (α β : Fin k → ℝ)
    (ha : Function.Injective α) (hb : Function.Injective β)
    (hia : ∀ i, 0 < α i ∧ α i < 1/2) (hib : ∀ i, 0 < β i ∧ β i < 1/2)
    (c : EndpointMatrix k) (h : endpointObservation α β c = (0,0,0,c none none)) :
    c = c none none • normalizedEndpointMatrix α β ha hb hia hib := by
  apply endpointObservation_injective α β ha hb hia hib
  rw [map_smul,normalizedEndpointMatrix_observation,h]
  simp

end
end MeyerGeneralProblem.Adaptive
