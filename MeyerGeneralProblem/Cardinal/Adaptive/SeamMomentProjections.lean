module

public import MeyerGeneralProblem.Cardinal.Adaptive.MomentHilbertEmbedding

@[expose] public section

/-! # Literal full-array seam projections and diagonal coordinate isometries -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Both Newton levels and both parity bits are retained in the actual index. -/
abbrev SeamMomentIndex := (ℕ × Bool) × (ℕ × Bool)
/-- The complete square-summable Newton array, including both infinite arms. -/
abbrev SeamMomentArray := MomentHilbert SeamMomentIndex

/-- The diagonal index of a specified parity pair. -/
def seamDiagonalIndex (e f : Bool) (n : ℕ) : SeamMomentIndex := ((n,e),(n,f))

theorem seamDiagonalIndex_injective (e f : Bool) : Function.Injective (seamDiagonalIndex e f) := by
  intro m n h
  exact congrArg (fun p : SeamMomentIndex => p.1.1) h

/-- Actual extraction of an entire parity diagonal. -/
def seamDiagonalReading (e f : Bool) : SeamMomentArray →L[ℂ] SeamSequence :=
  momentPullback (seamDiagonalIndex e f) (seamDiagonalIndex_injective e f)
/-- Actual insertion of an entire parity diagonal, zero on its complement. -/
def seamDiagonalEmbedding (e f : Bool) : SeamSequence →L[ℂ] SeamMomentArray :=
  momentEmbedding (seamDiagonalIndex e f) (seamDiagonalIndex_injective e f)

@[simp] theorem seamDiagonalReading_apply (e f : Bool) (u : SeamMomentArray) (n : ℕ) :
    seamDiagonalReading e f u n=u ((n,e),(n,f)) := rfl

@[simp] theorem seamDiagonalEmbedding_apply (e f : Bool) (u : SeamSequence) (p : SeamMomentIndex) :
    seamDiagonalEmbedding e f u p=
      if p.1.1=p.2.1 ∧ p.1.2=e ∧ p.2.2=f then u p.1.1 else 0 := by
  rcases p with ⟨⟨i,a⟩,j,b⟩
  by_cases h : i=j ∧ a=e ∧ b=f
  · simp only [h.1,h.2.1,h.2.2]
    simp only [seamDiagonalEmbedding]
    change momentEmbedding (seamDiagonalIndex e f) (seamDiagonalIndex_injective e f) u
      (seamDiagonalIndex e f j)=_
    rw [momentEmbedding_at]
    simp
  · have ho : ((i,a),(j,b)) ∉ Set.range (seamDiagonalIndex e f) := by
      rintro ⟨n,hn⟩
      apply h
      cases hn
      exact ⟨rfl,rfl,rfl⟩
    change momentEmbedding (seamDiagonalIndex e f) (seamDiagonalIndex_injective e f) u _=_
    rw [momentEmbedding_off _ _ _ _ ho]
    simp only [h,ite_false]

theorem seamDiagonalReading_norm_le_one (e f : Bool) : ‖seamDiagonalReading e f‖ ≤ 1 :=
  momentPullback_norm_le_one _ _

theorem seamDiagonalEmbedding_norm (e f : Bool) (u : SeamSequence) :
    ‖seamDiagonalEmbedding e f u‖=‖u‖ := momentEmbedding_norm _ _ _

theorem seamDiagonalEmbedding_norm_le_one (e f : Bool) : ‖seamDiagonalEmbedding e f‖ ≤ 1 :=
  momentEmbedding_norm_le_one _ _

@[simp] theorem seamDiagonalReading_embedding (e f : Bool) (u : SeamSequence) :
    seamDiagonalReading e f (seamDiagonalEmbedding e f u)=u := momentPullback_embedding _ _ _

/-- The 00 diagonal defining the leading domain. -/
def seamDIndices : Set SeamMomentIndex := {p | p.1.1=p.2.1 ∧ p.1.2=false ∧ p.2.2=false}
/-- The complete strict upper triangle plus the 01 diagonal. -/
def seamCIndices : Set SeamMomentIndex :=
  {p | p.1.1 < p.2.1 ∨ (p.1.1=p.2.1 ∧ p.1.2=false ∧ p.2.2=true)}
/-- The 11 diagonal defining the leading target. -/
def seamGIndices : Set SeamMomentIndex := {p | p.1.1=p.2.1 ∧ p.1.2=true ∧ p.2.2=true}
/-- Every coordinate in either infinite arm above level h. -/
def seamArmIndices (h : ℕ) : Set SeamMomentIndex := {p | h ≤ max p.1.1 p.2.1}
/-- The simultaneous two-level tail quadrant. -/
def seamQuadrantIndices (h : ℕ) : Set SeamMomentIndex := {p | h ≤ p.1.1 ∧ h ≤ p.2.1}

/-- Full coordinate projection onto the domain diagonal. -/
def seamDProjection : SeamMomentArray →L[ℂ] SeamMomentArray := momentProjection seamDIndices
/-- Full coordinate projection onto the complementary triangle. -/
def seamCProjection : SeamMomentArray →L[ℂ] SeamMomentArray := momentProjection seamCIndices
/-- Full coordinate projection onto the target diagonal. -/
def seamGProjection : SeamMomentArray →L[ℂ] SeamMomentArray := momentProjection seamGIndices
/-- Full domain flag D ⊕ C. -/
def seamPProjection : SeamMomentArray →L[ℂ] SeamMomentArray := momentProjection (seamDIndices ∪ seamCIndices)
/-- Full target flag C ⊕ G. -/
def seamQProjection : SeamMomentArray →L[ℂ] SeamMomentArray := momentProjection (seamCIndices ∪ seamGIndices)
/-- The actual maximum-index tail, retaining both off-diagonal arms. -/
def seamArmProjection (h : ℕ) : SeamMomentArray →L[ℂ] SeamMomentArray := momentProjection (seamArmIndices h)
/-- The actual simultaneous quadrant tail. -/
def seamQuadrantProjection (h : ℕ) : SeamMomentArray →L[ℂ] SeamMomentArray := momentProjection (seamQuadrantIndices h)

theorem seamCProjection_norm_le_one : ‖seamCProjection‖ ≤ 1 := momentProjection_norm_le_one _
theorem seamArmProjection_norm_le_one (h : ℕ) : ‖seamArmProjection h‖ ≤ 1 := momentProjection_norm_le_one _
theorem seamQuadrantProjection_norm_le_one (h : ℕ) : ‖seamQuadrantProjection h‖ ≤ 1 := momentProjection_norm_le_one _

@[simp] theorem seamCProjection_idempotent (u : SeamMomentArray) : seamCProjection (seamCProjection u)=seamCProjection u :=
  momentProjection_idempotent _ _
@[simp] theorem seamArmProjection_idempotent (h : ℕ) (u : SeamMomentArray) :
    seamArmProjection h (seamArmProjection h u)=seamArmProjection h u := momentProjection_idempotent _ _

theorem seamArmProjection_commute_C (h : ℕ) (u : SeamMomentArray) :
    seamArmProjection h (seamCProjection u)=seamCProjection (seamArmProjection h u) := by
  unfold seamArmProjection seamCProjection
  rw [momentProjection_inter,momentProjection_inter,Set.inter_comm]

theorem seamDProjection_eq_diagonal (u : SeamMomentArray) :
    seamDProjection u=seamDiagonalEmbedding false false (seamDiagonalReading false false u) := by
  ext p
  simp only [seamDProjection,momentProjection_apply,seamDiagonalEmbedding_apply,seamDiagonalReading_apply,seamDIndices,Set.mem_setOf_eq]
  split_ifs with h
  · rcases p with ⟨⟨i,e⟩,j,f⟩
    dsimp at h ⊢
    rcases h with ⟨rfl,rfl,rfl⟩
    rfl
  · rfl

theorem seamGProjection_eq_diagonal (u : SeamMomentArray) :
    seamGProjection u=seamDiagonalEmbedding true true (seamDiagonalReading true true u) := by
  ext p
  simp only [seamGProjection,momentProjection_apply,seamDiagonalEmbedding_apply,seamDiagonalReading_apply,seamGIndices,Set.mem_setOf_eq]
  split_ifs with h
  · rcases p with ⟨⟨i,e⟩,j,f⟩
    dsimp at h ⊢
    rcases h with ⟨rfl,rfl,rfl⟩
    rfl
  · rfl

/-- The full complementary feedback estimate specialized to the actual
maximum-index arm projection on the entire moment Hilbert space. -/
theorem seamArm_full_complement_bound (h : ℕ) (B : SeamMomentArray →L[ℂ] SeamMomentArray)
    (htri : ∀ x, seamArmProjection h (B x)=seamArmProjection h (B (seamArmProjection h x)))
    (δ : ℝ) (hδ : δ < 1) (hB : ‖B-ContinuousLinearMap.id ℂ SeamMomentArray‖ ≤ δ)
    (y c : SeamMomentArray) (heq : y+B c=0) :
    ‖seamArmProjection h c‖ ≤ (1-δ)⁻¹*‖seamArmProjection h y‖ :=
  projectedComplement_bound _ B (seamArmProjection_norm_le_one h)
    (seamArmProjection_idempotent h) htri δ hδ hB y c heq

end
end MeyerGeneralProblem.Adaptive
