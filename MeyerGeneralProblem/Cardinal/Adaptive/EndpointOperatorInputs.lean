module

public import MeyerGeneralProblem.Cardinal.Adaptive.EndpointFiniteSource
public import MeyerGeneralProblem.Cardinal.Adaptive.ShrinkingNewtonDerivatives

@[expose] public section

/-! Literal finite rapid phase inputs for the complete Newton operators. -/
noncomputable section
namespace MeyerGeneralProblem.Adaptive

/-- The actual finite next-phase sequence, including its zero seam tail. -/
def endpointOperatorDistance (P R k n : ℕ) : ℝ :=
  endpointPaddedDistance P R k ⟨n+1,by omega⟩

/-- The actual cosine node in the complete Newton row and column operators. -/
def endpointOperatorNode (P R k n : ℕ) : ℂ :=
  (1-Real.cos (2*Real.pi*endpointOperatorDistance P R k n) : ℝ)

/-- The actual tangent coefficient in both finite source flag graphs. -/
def endpointOperatorTangent (P R k n : ℕ) : ℂ :=
  (Real.tan (Real.pi*endpointOperatorDistance P R k n) : ℝ)

/-- Zero padding preserves the uniform small rapid phase bound. -/
theorem endpointOperatorDistance_bounds {P R : ℕ} (hP : 1 ≤ P) (hR : 1 ≤ R) (k n : ℕ) :
    0 ≤ endpointOperatorDistance P R k n ∧
      endpointOperatorDistance P R k n ≤ 1/(2:ℝ)^68 := by
  unfold endpointOperatorDistance endpointPaddedDistance
  split_ifs
  · exact ⟨(rapidDistance_bounds hP hR _).1.le,rapidDistance_le_small_constant hP hR _⟩
  · constructor <;> norm_num

/-- The literal cosine node retains its quadratic smallness including the seam. -/
theorem endpointOperatorNode_quadratic {P R : ℕ} (hP : 1 ≤ P) (hR : 1 ≤ R) (k n : ℕ) :
    ‖endpointOperatorNode P R k n‖ ≤ 32*(endpointOperatorDistance P R k n)^2 := by
  have ht := endpointOperatorDistance_bounds hP hR k n
  have hz := shrinkingNewton_cos_factor_le (endpointOperatorDistance P R k n) 0 ht.1
    (ht.2.trans (by norm_num)) (by simpa using ht.1)
  simpa only [endpointOperatorNode,Complex.norm_real,Real.norm_eq_abs,mul_zero,Real.cos_zero,
    abs_sub_comm] using hz

/-- The actual cosine inputs satisfy the fixed R-squared operator bound. -/
theorem endpointOperatorNode_norm {P R : ℕ} (hP : 1 ≤ P) (hR : 1 ≤ R) (k n : ℕ) :
    ‖endpointOperatorNode P R k n‖ ≤ (1/4096 : ℝ)^2 := by
  have ht := endpointOperatorDistance_bounds hP hR k n
  have hs := sq_le_sq₀ ht.1 (by positivity) |>.mpr ht.2
  exact (endpointOperatorNode_quadratic hP hR k n).trans
    ((mul_le_mul_of_nonneg_left hs (by norm_num)).trans (by norm_num))

/-- The actual tangent input is bounded linearly in its own phase. -/
theorem endpointOperatorTangent_linear {P R : ℕ} (hP : 1 ≤ P) (hR : 1 ≤ R) (k n : ℕ) :
    ‖endpointOperatorTangent P R k n‖ ≤ 8*endpointOperatorDistance P R k n := by
  have ht := endpointOperatorDistance_bounds hP hR k n
  have hh : endpointOperatorDistance P R k n ≤ 1/16 := ht.2.trans (by norm_num)
  have hn : 0 ≤ Real.tan (Real.pi*endpointOperatorDistance P R k n) :=
    Real.tan_nonneg_of_nonneg_of_le_pi_div_two (mul_nonneg Real.pi_pos.le ht.1) (by nlinarith [Real.pi_pos])
  simpa only [endpointOperatorTangent,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hn] using
    tan_phase_le_eight_mul _ ht.1 hh

/-- The actual tangent graph inputs satisfy the fixed R-cubed bound. -/
theorem endpointOperatorTangent_norm {P R : ℕ} (hP : 1 ≤ P) (hR : 1 ≤ R) (k n : ℕ) :
    ‖endpointOperatorTangent P R k n‖ ≤ (1/4096 : ℝ)^3 := by
  have ht := endpointOperatorDistance_bounds hP hR k n
  exact (endpointOperatorTangent_linear hP hR k n).trans
    ((mul_le_mul_of_nonneg_left ht.2 (by norm_num)).trans (by norm_num))

/-- Both graph tangents and the node are controlled by the actual next phase. -/
theorem endpointOperator_weight_linear {P R : ℕ} (hP : 1 ≤ P) (hR : 1 ≤ R) (k n : ℕ) :
    ‖endpointOperatorTangent P R k n‖+‖endpointOperatorTangent P R k n‖+
      ‖endpointOperatorNode P R k n‖ ≤ 128*endpointOperatorDistance P R k n := by
  have ht := endpointOperatorDistance_bounds hP hR k n
  have hsmall : endpointOperatorDistance P R k n ≤ 1 := ht.2.trans (by norm_num)
  have hsq : (endpointOperatorDistance P R k n)^2 ≤ endpointOperatorDistance P R k n := by nlinarith
  have htan := endpointOperatorTangent_linear hP hR k n
  have hnode := endpointOperatorNode_quadratic hP hR k n
  nlinarith

end MeyerGeneralProblem.Adaptive
