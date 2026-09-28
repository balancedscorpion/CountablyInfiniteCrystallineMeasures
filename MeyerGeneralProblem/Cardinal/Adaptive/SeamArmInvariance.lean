module

public import MeyerGeneralProblem.Cardinal.Adaptive.OperatorCornerInvariance
public import MeyerGeneralProblem.Cardinal.Adaptive.SeamSchurAssembly

@[expose] public section

/-! # The entire seam equation preserves both maximum-index arms -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Two actual coordinate projections preserve each other's complete input corner. -/
theorem momentProjection_corner {ι : Type*} (s t : Set ι) :
    OperatorCornerInvariant (momentProjection s) (momentProjection t) := by
  unfold OperatorCornerInvariant
  ext u p
  change momentProjection s (momentProjection t u) p=
    momentProjection s (momentProjection t (momentProjection s u)) p
  simp only [momentProjection_apply]
  split_ifs <;> rfl

theorem seamArmProjection_mul_self (h : ℕ) : seamArmProjection h*seamArmProjection h=seamArmProjection h := by
  ext u p
  exact congrArg (fun v : SeamMomentArray => v p) (seamArmProjection_idempotent h u)

/-- Every actual sine row retains the complete union of both high-index arms. -/
theorem seamSineRow_arm_invariant (h : ℕ) (κ R : ℂ) (a : ℕ → ℂ) (K : ℝ)
    (hK : 0 ≤ K) (ha : ∀ i, ‖a i‖ ≤ K) :
    OperatorCornerInvariant (seamArmProjection h) (seamSineRow κ R a K hK ha) := by
  unfold OperatorCornerInvariant
  ext u p
  rcases p with ⟨⟨i,e⟩,j,f⟩
  change seamArmProjection h (seamSineRow κ R a K hK ha u) ((i,e),(j,f))=
    seamArmProjection h (seamSineRow κ R a K hK ha (seamArmProjection h u)) ((i,e),(j,f))
  simp only [seamArmProjection,momentProjection_apply,seamArmIndices,Set.mem_setOf_eq]
  by_cases hh : h ≤ max i j
  · have hn : h ≤ max (i+1) j := hh.trans (max_le_max (Nat.le_succ _) le_rfl)
    simp only [hh,ite_true,seamSineRow_apply,momentProjection_apply,seamArmIndices,Set.mem_setOf_eq]
    cases e <;> simp [hh,hn]
  · simp [hh]

/-- Every actual sine column retains both arms, including the off-diagonal one. -/
theorem seamSineColumn_arm_invariant (h : ℕ) (κ R : ℂ) (a : ℕ → ℂ) (K : ℝ)
    (hK : 0 ≤ K) (ha : ∀ i, ‖a i‖ ≤ K) :
    OperatorCornerInvariant (seamArmProjection h) (seamSineColumn κ R a K hK ha) := by
  unfold OperatorCornerInvariant
  ext u p
  rcases p with ⟨⟨i,e⟩,j,f⟩
  change seamArmProjection h (seamSineColumn κ R a K hK ha u) ((i,e),(j,f))=
    seamArmProjection h (seamSineColumn κ R a K hK ha (seamArmProjection h u)) ((i,e),(j,f))
  simp only [seamArmProjection,momentProjection_apply,seamArmIndices,Set.mem_setOf_eq]
  by_cases hh : h ≤ max i j
  · have hn : h ≤ max i (j+1) := hh.trans (max_le_max le_rfl (Nat.le_succ _))
    simp only [hh,ite_true,seamSineColumn_apply,momentProjection_apply,seamArmIndices,Set.mem_setOf_eq]
    cases f <;> simp [hh,hn]
  · simp [hh]

/-- The entire arcsine coordinate inherits full arm invariance, including all higher terms. -/
theorem seamCoordinate_arm_invariant (h : ℕ) (S : SeamMomentArray →L[ℂ] SeamMomentArray)
    (hS : OperatorCornerInvariant (seamArmProjection h) S) (hn : ‖S*S‖ < 1) :
    OperatorCornerInvariant (seamArmProjection h) (seamCoordinateOperator S) :=
  (hS.mul ((hS.mul hS).series (seamArmProjection_mul_self h) (seamArmProjection_norm_le_one h)
    _ scalarArcsineCoefficient_cast_norm hn)).smul _

/-- Complete full-gauge invariance on both infinite arms. -/
theorem seamGauge_arm_invariant (h : ℕ) (a b : ℕ → ℂ)
    (ha : ∀ i, ‖a i‖ ≤ (1/4096 : ℝ)^2) (hb : ∀ i, ‖b i‖ ≤ (1/4096 : ℝ)^2) :
    OperatorCornerInvariant (seamArmProjection h) (seamGaugeOperator
      (seamSineRow (1/64) (1/4096) a ((1/4096)^2) (by positivity) ha)
      (seamSineColumn (1/64) (1/4096) b ((1/4096)^2) (by positivity) hb)) := by
  have hx := seamCoordinate_arm_invariant h _ (seamSineRow_arm_invariant h _ _ _ _ _ _)
    ((seamSineRow_square_norm a ha).trans_lt (by norm_num))
  have hy := seamCoordinate_arm_invariant h _ (seamSineColumn_arm_invariant h _ _ _ _ _ _)
    ((seamSineColumn_square_norm b hb).trans_lt (by norm_num))
  exact ((hx.mul hy).smul _).exp (seamArmProjection_mul_self h) (seamArmProjection_norm_le_one h)
    ((seamGaugeGenerator_norm _ _ (seamSineRow_constant_bound _ _) (seamSineRow_square_norm _ _)
      (seamSineColumn_constant_bound _ _) (seamSineColumn_square_norm _ _)).trans_lt (by norm_num))

theorem seamPhysicalGraph_arm_invariant (h : ℕ) (t : ℕ → ℂ)
    (ht : ∀ i, ‖t i‖ ≤ (1/4096 : ℝ)^3) :
    OperatorCornerInvariant (seamArmProjection h) (seamPhysicalGraph t ht) := by
  unfold OperatorCornerInvariant
  ext u p
  change seamArmProjection h (seamPhysicalGraph t ht u) p=
    seamArmProjection h (seamPhysicalGraph t ht (seamArmProjection h u)) p
  simp only [seamArmProjection,momentProjection_apply,seamArmIndices,Set.mem_setOf_eq,
    seamPhysicalGraph_apply,seamParityExchange]
  split_ifs <;> simp_all

theorem seamSpectralGraph_arm_invariant (h : ℕ) (t : ℕ → ℂ)
    (ht : ∀ i, ‖t i‖ ≤ (1/4096 : ℝ)^3) :
    OperatorCornerInvariant (seamArmProjection h) (seamSpectralGraph t ht) := by
  unfold OperatorCornerInvariant
  ext u p
  change seamArmProjection h (seamSpectralGraph t ht u) p=
    seamArmProjection h (seamSpectralGraph t ht (seamArmProjection h u)) p
  simp only [seamArmProjection,momentProjection_apply,seamArmIndices,Set.mem_setOf_eq,
    seamSpectralGraph_apply,seamParityExchange]
  split_ifs <;> simp_all

/-- Actual graph corrections preserve both arms through the complete gauge. -/
theorem seamFullOperator_arm_invariant (h : ℕ) (a b ta tb : ℕ → ℂ)
    (ha : ∀ i, ‖a i‖ ≤ (1/4096 : ℝ)^2) (hb : ∀ i, ‖b i‖ ≤ (1/4096 : ℝ)^2)
    (hta : ∀ i, ‖ta i‖ ≤ (1/4096 : ℝ)^3) (htb : ∀ i, ‖tb i‖ ≤ (1/4096 : ℝ)^3) :
    OperatorCornerInvariant (seamArmProjection h) (seamFullOperator a b ta tb ha hb hta htb) :=
  (((momentProjection_corner _ _).sub (seamSpectralGraph_arm_invariant h tb htb)).mul
    (seamGauge_arm_invariant h a b ha hb)).mul
      ((OperatorCornerInvariant.one _ (seamArmProjection_mul_self h)).add
        (seamPhysicalGraph_arm_invariant h ta hta))

/-- The actual whole complementary block preserves both arms before its inverse is estimated. -/
theorem seamSchurB_arm_invariant (h : ℕ) (F : SeamMomentArray →L[ℂ] SeamMomentArray)
    (hF : OperatorCornerInvariant (seamArmProjection h) F) :
    OperatorCornerInvariant (seamArmProjection h) (seamSchurB F) :=
  (OperatorCornerInvariant.one _ (seamArmProjection_mul_self h)).add
    (((momentProjection_corner _ _).mul (hF.sub (momentProjection_corner _ _))).mul
      (momentProjection_corner _ _))

end
end MeyerGeneralProblem.Adaptive
