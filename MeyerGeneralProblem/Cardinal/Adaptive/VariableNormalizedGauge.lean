module

public import MeyerGeneralProblem.Cardinal.Adaptive.VariableTangentWeights

@[expose] public section

/-! Bounded normalization of the actual full diagonal gauge row. -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section

/-- The actual positive leading diagonal, as a bounded map; no inverse is defined. -/
def variableSourceDenominatorMap (P R Q S : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R)
    (hQ : 1 ≤ Q) (hS : 1 ≤ S) : SeamSequence →L[ℂ] SeamSequence :=
  momentDiagonal (fun i => (variableSourceRowDenominator P R Q S i : ℂ))
    (8*shrinkingNewtonSourceKappa^2) (by positivity) (fun i => by
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (variableSourceRowDenominator_pos P R Q S hP hR hQ hS i)]
      exact variableSourceRowDenominator_le P R Q S hP hR hQ hS i)

/-- The inverse-row coefficient is constructed only after multiplying by both
actual phase weights, yielding a bounded diagonal on the entire sequence space. -/
def variableNormalizedGaugeDiagonal (P R Q S : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R)
    (hQ : 1 ≤ Q) (hS : 1 ≤ S) : SeamSequence →L[ℂ] SeamSequence :=
  momentDiagonal (fun i => (variableNormalizedGaugeWeight P R Q S i : ℂ))
    (shrinkingNewtonSourceKappa^6/6) (by positivity) (fun i => by
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg
        (variableNormalizedGaugeWeight_bounds P R Q S hP hR hQ hS i).1]
      exact (variableNormalizedGaugeWeight_bounds P R Q S hP hR hQ hS i).2)

/-- The genuine bounded normalized complete gauge row. -/
def variableNormalizedGaugeRow (P R Q S : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R)
    (hQ : 1 ≤ Q) (hS : 1 ≤ S) : SeamMomentArray →L[ℂ] SeamSequence :=
  (variableNormalizedGaugeDiagonal P R Q S hP hR hQ hS).comp
    ((seamDiagonalReading true true).comp (variableGaugeRowFactor P R Q S hP hR hQ hS))

/-- Both retained weights give the sharper rho bound after legitimate normalization. -/
theorem variableNormalizedGaugeRow_norm_le (P R Q S : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R)
    (hQ : 1 ≤ Q) (hS : 1 ≤ S) :
    ‖variableNormalizedGaugeRow P R Q S hP hR hQ hS‖ ≤ 100*shrinkingNewtonSourceKappa^4/6 := by
  have hD : ‖variableNormalizedGaugeDiagonal P R Q S hP hR hQ hS‖ ≤ shrinkingNewtonSourceKappa^6/6 :=
    momentDiagonal_norm_le _ _ _ _
  have hG : ‖(seamDiagonalReading true true).comp (variableGaugeRowFactor P R Q S hP hR hQ hS)‖ ≤
      100*shrinkingNewtonSourceKappa⁻¹^2 := by
    apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
    exact (mul_le_mul (seamDiagonalReading_norm_le_one true true)
      (variableGaugeRowFactor_norm_le P R Q S hP hR hQ hS) (norm_nonneg _) zero_le_one).trans (by simp)
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  have h := mul_le_mul hD hG (norm_nonneg _) (by positivity : 0 ≤ shrinkingNewtonSourceKappa^6/6)
  exact h.trans (by norm_num [shrinkingNewtonSourceKappa])

/-- The constructed normalized row realizes the complete diagonal gauge
identity on every full array; cancellation is justified coefficient by coefficient. -/
theorem variableNormalizedGaugeRow_realizes (P R Q S : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R)
    (hQ : 1 ≤ Q) (hS : 1 ≤ S) :
    (variableSourceDenominatorMap P R Q S hP hR hQ hS).comp
      (variableNormalizedGaugeRow P R Q S hP hR hQ hS) =
    (seamDiagonalReading true true).comp (variableGaugeOperator P R Q S hP hR hQ hS-1) := by
  ext u n
  have hg := congrArg (fun A : SeamMomentArray →L[ℂ] SeamMomentArray => A u ((n,true),(n,true)))
    (variableGaugeOperator_row_factor P R Q S hP hR hQ hS)
  change ((momentProjection (seamRowParity true) * momentProjection {p : SeamMomentIndex | p.2.2=true})
    ((variableGaugeOperator P R Q S hP hR hQ hS-1) u)) ((n,true),(n,true)) = _ at hg
  simp only [ContinuousLinearMap.mul_apply,momentProjection_apply,seamRowParity,Set.mem_setOf_eq,ite_true,
    variableNewtonRowWeight_apply,variableNewtonColumnWeight_apply] at hg
  change (variableSourceRowDenominator P R Q S n : ℂ) *
    ((variableNormalizedGaugeWeight P R Q S n : ℂ)*
      (variableGaugeRowFactor P R Q S hP hR hQ hS u) ((n,true),(n,true))) =
    ((variableGaugeOperator P R Q S hP hR hQ hS-1) u) ((n,true),(n,true))
  rw [←mul_assoc,←Complex.ofReal_mul,variableNormalizedGaugeWeight_cancellation P R Q S hP hR hQ hS n,
    Complex.ofReal_mul,mul_assoc]
  exact hg.symm

/-- The positive leading diagonal is injective despite its unbounded inverse. -/
theorem variableSourceDenominatorMap_injective (P R Q S : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R)
    (hQ : 1 ≤ Q) (hS : 1 ≤ S) : Function.Injective (variableSourceDenominatorMap P R Q S hP hR hQ hS) := by
  intro u v h
  ext n
  have hn := congrArg (fun w : SeamSequence => w n) h
  change (variableSourceRowDenominator P R Q S n : ℂ)*u n =
    (variableSourceRowDenominator P R Q S n : ℂ)*v n at hn
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (ne_of_gt
    (variableSourceRowDenominator_pos P R Q S hP hR hQ hS n))) hn

end
end MeyerGeneralProblem.Adaptive
