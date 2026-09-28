module

public import MeyerGeneralProblem.Cardinal.Adaptive.BoundedOperatorSeries

@[expose] public section

/-! # Whole-operator intertwining through every power-series term -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- Continuous left composition on the complete operator space. -/
def operatorComposeLeft (U : E →L[ℂ] F) : (E →L[ℂ] E) →L[ℂ] (E →L[ℂ] F) :=
  LinearMap.mkContinuous
    { toFun := fun A => U.comp A
      map_add' A B := by ext x; simp
      map_smul' z A := by ext x; simp } ‖U‖ (fun A => U.opNorm_comp_le A)

/-- Continuous right composition on the complete operator space. -/
def operatorComposeRight (U : E →L[ℂ] F) : (F →L[ℂ] F) →L[ℂ] (E →L[ℂ] F) :=
  LinearMap.mkContinuous
    { toFun := fun A => A.comp U
      map_add' A B := by ext x; simp
      map_smul' z A := by ext x; simp } ‖U‖ (fun A => by
        change ‖A.comp U‖ ≤ ‖U‖*‖A‖
        simpa only [mul_comm] using A.opNorm_comp_le U)

theorem operator_intertwine_pow (U : E →L[ℂ] F) (X : E →L[ℂ] E) (Y : F →L[ℂ] F)
    (h : U.comp X=Y.comp U) (n : ℕ) : U.comp (X^n)=(Y^n).comp U := by
  induction n with
  | zero => ext x; rfl
  | succ n ih =>
    rw [pow_succ',pow_succ',ContinuousLinearMap.mul_def,ContinuousLinearMap.mul_def,
      ← ContinuousLinearMap.comp_assoc,h,ContinuousLinearMap.comp_assoc,ih,← ContinuousLinearMap.comp_assoc]

/-- A bounded intertwiner passes through the entire norm-convergent series.
This applies to axis exchange, tail shifts and invariant coordinate arms. -/
theorem boundedOperatorSeries_intertwine [NontrivialTopology E] [NontrivialTopology F]
    (c : ℕ → ℂ) (hc : ∀ n, ‖c n‖ ≤ 1)
    (U : E →L[ℂ] F) (X : E →L[ℂ] E) (Y : F →L[ℂ] F)
    (hX : ‖X‖ < 1) (hY : ‖Y‖ < 1) (h : U.comp X=Y.comp U) :
    U.comp (boundedOperatorSeries c X)=(boundedOperatorSeries c Y).comp U := by
  have hleft := (operatorComposeLeft U).hasSum (boundedOperatorSeries_hasSum c hc X hX)
  have hright := (operatorComposeRight U).hasSum (boundedOperatorSeries_hasSum c hc Y hY)
  have he : (fun n => operatorComposeLeft U (c n •X^n))=
      (fun n => operatorComposeRight U (c n •Y^n)) := by
    funext n
    change U.comp (c n •X^n)=(c n •Y^n).comp U
    rw [ContinuousLinearMap.comp_smul,ContinuousLinearMap.smul_comp,operator_intertwine_pow U X Y h n]
  rw [he] at hleft
  exact hleft.unique hright

end
end MeyerGeneralProblem.Adaptive
