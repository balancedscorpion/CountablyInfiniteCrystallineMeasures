module

public import MeyerGeneralProblem.Cardinal.Adaptive.EndpointCompleteLine

@[expose] public section

/-! # Reflection preserves the exact single-endpoint deleted carrier -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open scoped FourierTransform BigOperators

/-- Reflection of signed phases, fixing the unique endpoint coset. -/
def endpointFlip {k : ℕ} : EndpointPhaseIndex k → EndpointPhaseIndex k
  | none => none
  | some (i,u) => some (i,!u)

@[simp] theorem endpointFlip_involutive {k : ℕ} (a : EndpointPhaseIndex k) :
    endpointFlip (endpointFlip a)=a := by
  cases a with
  | none => rfl
  | some a => rcases a with ⟨i,u⟩; simp [endpointFlip]

/-- Reflection of integer cells, retaining the endpoint shift by minus one. -/
def endpointReflectedCell {k : ℕ} : EndpointPhaseIndex k → ℤ → ℤ
  | none,n => -n-1
  | some _,n => -n

theorem endpointPoint_reflect {k : ℕ} (α : Fin k → ℝ) (a : EndpointPhaseIndex k) (n : ℤ) :
    (endpointPoint α (endpointFlip a) (endpointReflectedCell a n) : ℝ) =
      -(endpointPoint α a n : ℝ) := by
  cases a with
  | none => simp [endpointPoint,endpointPhase,endpointFlip,endpointReflectedCell]; ring
  | some a =>
    rcases a with ⟨i,u⟩
    cases u <;> simp [endpointPoint,endpointPhase,endpointFlip,endpointReflectedCell,criticalSignedPhase] <;> ring

/-- The exact permutation of retained hole indices induced by reflection. -/
def endpointHoleReflection {k : ℕ} : EndpointHoleIndex k → EndpointHoleIndex k
  | .inl ⟨i,u,r⟩ => .inl ⟨i,!u,r.rev⟩
  | .inr r => .inr r.rev

theorem endpointHolePoint_reflect {k : ℕ} (α : Fin k → ℝ) (h : EndpointHoleIndex k) :
    (endpointHolePoint α (endpointHoleReflection h) : ℝ) = -(endpointHolePoint α h : ℝ) := by
  cases h with
  | inl h =>
    rcases h with ⟨i,u,r⟩
    have hr := r.isLt
    have he : ((r.rev.val : ℕ) : ℤ)-(i.val : ℤ) = -((r.val : ℤ)-(i.val : ℤ)) := by
      simp only [Fin.val_rev]
      omega
    change endpointPhase α (some (i,!u))+(((r.rev.val : ℕ) : ℤ)-(i.val : ℤ) : ℤ) =
      -(endpointPhase α (some (i,u))+((r.val : ℤ)-(i.val : ℤ) : ℤ))
    rw [he]
    cases u <;> simp [endpointPhase,criticalSignedPhase] <;> ring
  | inr r =>
    have hr := r.isLt
    have he : -(k : ℤ)+(r.rev.val : ℕ) = -(-(k : ℤ)+(r.val : ℕ))-1 := by
      simp only [Fin.val_rev]
      omega
    change (1/2 : ℝ)+(-(k : ℤ)+(r.rev.val : ℕ) : ℤ) =
      -((1/2 : ℝ)+(-(k : ℤ)+(r.val : ℕ) : ℤ))
    rw [he]
    push_cast
    ring

theorem endpointCosetCarrier_neg {k : ℕ} (α : Fin k → ℝ) {x : ℝ}
    (hx : x ∈ (endpointCosetCarrier α).carrier) : -x ∈ (endpointCosetCarrier α).carrier := by
  obtain ⟨a,n,rfl⟩ := hx
  exact ⟨endpointFlip a,endpointReflectedCell a n,endpointPoint_reflect α a n⟩

theorem endpointHoleSet_neg {k : ℕ} (α : Fin k → ℝ) {x : ℝ}
    (hx : x ∈ endpointHoleSet α) : -x ∈ endpointHoleSet α := by
  obtain ⟨h,rfl⟩ := hx
  exact ⟨endpointHoleReflection h,endpointHolePoint_reflect α h⟩

/-- Reflection keeps the complete endpoint carrier and exactly the retained
holes; the endpoint cell shifts by `-n-1`, not `-n`. -/
theorem endpointDeletedCarrier_neg {k : ℕ} (α : Fin k → ℝ) {x : ℝ}
    (hx : x ∈ (endpointDeletedCarrier α).carrier) : -x ∈ (endpointDeletedCarrier α).carrier := by
  refine ⟨endpointCosetCarrier_neg α hx.1,?_⟩
  intro hh
  have he := endpointHoleSet_neg α hh
  exact hx.2 (by simpa only [neg_neg] using he)

end
end MeyerGeneralProblem.Adaptive
