module

public import MeyerGeneralProblem.Cardinal.Adaptive.VariableGraphCorrections
public import MeyerGeneralProblem.Cardinal.Adaptive.VariableNormalizedGauge

@[expose] public section

/-! The bounded normalized remainder of the complete signed graph equation. -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section

/-- The actual spectral leading coefficient in the complete graph equation. -/
def variableSpectralLeadingDiagonal (Q S : ℕ) (hQ : 1 ≤ Q) (hS : 1 ≤ S) :
    SeamSequence →L[ℂ] SeamSequence :=
  momentDiagonal (fun i => ((variableSourceTangent Q S i/shrinkingNewtonSourceKappa^2 : ℝ):ℂ))
    (4*shrinkingNewtonSourceKappa^2) (by positivity) (fun i => by
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (div_pos (variableSourceTangent_pos Q S hQ hS i)
        (sq_pos_of_pos shrinkingNewtonSourceKappa_pos))]
      apply (div_le_iff₀ (sq_pos_of_pos shrinkingNewtonSourceKappa_pos)).2
      calc
        _ ≤ 4*shrinkingNewtonSourceKappa^4 := variableSourceTangent_le Q S hQ hS i
        _ = _ := by ring)

/-- The bounded spectral share of the whole positive leading diagonal. -/
def variableSpectralRatioDiagonal (P R Q S : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R)
    (hQ : 1 ≤ Q) (hS : 1 ≤ S) : SeamSequence →L[ℂ] SeamSequence :=
  momentDiagonal (fun i => ((variableSourceTangent Q S i /
    (variableSourceTangent P R i+variableSourceTangent Q S i):ℝ):ℂ)) 1 zero_le_one (fun i => by
      have he := variableNewton_source_phase_bound P R hP hR (i+1)
      have hd := variableNewton_source_phase_bound Q S hQ hS (i+1)
      have h := tangent_div_tangent_sum_mem_unit _ _ he.1 hd.1
        (he.2.trans (by norm_num [shrinkingNewtonSourceKappa]))
        (hd.2.trans (by norm_num [shrinkingNewtonSourceKappa]))
      rw [Complex.norm_real,Real.norm_eq_abs]
      change |Real.tan (Real.pi*rapidDistance Q S (i+1))/(Real.tan (Real.pi*rapidDistance P R (i+1))+Real.tan (Real.pi*rapidDistance Q S (i+1)))| ≤ 1
      rw [abs_of_nonneg h.1]
      exact h.2)

theorem variableSpectralRatioDiagonal_realizes (P R Q S : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R)
    (hQ : 1 ≤ Q) (hS : 1 ≤ S) :
    (variableSourceDenominatorMap P R Q S hP hR hQ hS).comp
      (variableSpectralRatioDiagonal P R Q S hP hR hQ hS)=variableSpectralLeadingDiagonal Q S hQ hS := by
  ext u n
  change (variableSourceRowDenominator P R Q S n : ℂ) *
    (((variableSourceTangent Q S n/(variableSourceTangent P R n+variableSourceTangent Q S n):ℝ):ℂ)*u n) =
    (((variableSourceTangent Q S n/shrinkingNewtonSourceKappa^2:ℝ):ℂ)*u n)
  rw [←mul_assoc,←Complex.ofReal_mul]
  congr 2
  have hs : variableSourceTangent P R n+variableSourceTangent Q S n ≠ 0 := ne_of_gt
    (add_pos (variableSourceTangent_pos P R hP hR n) (variableSourceTangent_pos Q S hQ hS n))
  unfold variableSourceRowDenominator
  field_simp [hs]

/-- The literal complete graph row remainder, retaining the spectral feedback term. -/
def variableGraphRowRemainder (P R Q S : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R)
    (hQ : 1 ≤ Q) (hS : 1 ≤ S) : SeamMomentArray →L[ℂ] SeamSequence :=
  (((seamDiagonalReading true true).comp (variableGaugeOperator P R Q S hP hR hQ hS-1))-
    Complex.I • ((variableSpectralLeadingDiagonal Q S hQ hS).comp
      ((seamDiagonalReading false false).comp (variableGaugeOperator P R Q S hP hR hQ hS-1)))).comp
    (1+variablePhysicalSourceGraph P R hP hR)

/-- The normalized complete remainder is constructed from bounded weighted
ratios and the full gauge, without defining the bare inverse leading diagonal. -/
def variableNormalizedGraphRemainder (P R Q S : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R)
    (hQ : 1 ≤ Q) (hS : 1 ≤ S) : SeamMomentArray →L[ℂ] SeamSequence :=
  (variableNormalizedGaugeRow P R Q S hP hR hQ hS-
    Complex.I • ((variableSpectralRatioDiagonal P R Q S hP hR hQ hS).comp
      ((seamDiagonalReading false false).comp (variableGaugeOperator P R Q S hP hR hQ hS-1)))).comp
    (1+variablePhysicalSourceGraph P R hP hR)

/-- The constructed normalized map realizes the entire graph row remainder. -/
theorem variableNormalizedGraphRemainder_realizes (P R Q S : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R)
    (hQ : 1 ≤ Q) (hS : 1 ≤ S) :
    (variableSourceDenominatorMap P R Q S hP hR hQ hS).comp
      (variableNormalizedGraphRemainder P R Q S hP hR hQ hS)=
      variableGraphRowRemainder P R Q S hP hR hQ hS := by
  unfold variableNormalizedGraphRemainder variableGraphRowRemainder
  rw [←ContinuousLinearMap.comp_assoc,ContinuousLinearMap.comp_sub,ContinuousLinearMap.comp_smul,
    variableNormalizedGaugeRow_realizes,←ContinuousLinearMap.comp_assoc,variableSpectralRatioDiagonal_realizes]

/-- The complete normalized remainder obeys the retained source constant,
including every exponential term and the whole physical graph correction. -/
theorem variableNormalizedGraphRemainder_norm_le (P R Q S : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R)
    (hQ : 1 ≤ Q) (hS : 1 ≤ S) :
    ‖variableNormalizedGraphRemainder P R Q S hP hR hQ hS‖ ≤ 128*shrinkingNewtonSourceKappa^2 := by
  have hD : ‖variableSpectralRatioDiagonal P R Q S hP hR hQ hS‖ ≤ 1 := momentDiagonal_norm_le _ _ _ _
  have hE := variableGaugeOperator_close P R Q S hP hR hQ hS
  have hG := variableNormalizedGaugeRow_norm_le P R Q S hP hR hQ hS
  have hA : ‖1+variablePhysicalSourceGraph P R hP hR‖ ≤ 1+4*shrinkingNewtonSourceKappa^2 := by
    apply (norm_add_le _ _).trans
    rw [norm_one]
    exact add_le_add le_rfl (variablePhysicalGraph_norm _ _)
  have hF : ‖(seamDiagonalReading false false).comp (variableGaugeOperator P R Q S hP hR hQ hS-1)‖ ≤
      9*shrinkingNewtonSourceKappa^2 := by
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul (seamDiagonalReading_norm_le_one false false) hE (norm_nonneg _) zero_le_one).trans (by simp))
  have hB : ‖(variableSpectralRatioDiagonal P R Q S hP hR hQ hS).comp
      ((seamDiagonalReading false false).comp (variableGaugeOperator P R Q S hP hR hQ hS-1))‖ ≤
      9*shrinkingNewtonSourceKappa^2 :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul hD hF (norm_nonneg _) zero_le_one).trans (by simp))
  unfold variableNormalizedGraphRemainder
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  have hn : ‖variableNormalizedGaugeRow P R Q S hP hR hQ hS-
      Complex.I • ((variableSpectralRatioDiagonal P R Q S hP hR hQ hS).comp
        ((seamDiagonalReading false false).comp (variableGaugeOperator P R Q S hP hR hQ hS-1)))‖ ≤
      100*shrinkingNewtonSourceKappa^4/6+9*shrinkingNewtonSourceKappa^2 := by
    apply (norm_sub_le _ _).trans
    rw [norm_smul,Complex.norm_I,one_mul]
    exact add_le_add hG hB
  exact (mul_le_mul hn hA (norm_nonneg _) (by positivity)).trans (by norm_num [shrinkingNewtonSourceKappa])

/-- Exact diagonal row of the complete signed graph operator, with both
leading tangent contributions and the full retained remainder. -/
theorem variableFullSourceOperator_diagonal_row (P R Q S : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R)
    (hQ : 1 ≤ Q) (hS : 1 ≤ S) (u : SeamMomentArray) :
    seamDiagonalReading true true (variableFullSourceOperator P R Q S hP hR hQ hS u) =
    seamDiagonalReading true true u - Complex.I •
      variableSourceDenominatorMap P R Q S hP hR hQ hS (seamDiagonalReading false false u) +
      variableGraphRowRemainder P R Q S hP hR hQ hS u := by
  let E := variableGaugeOperator P R Q S hP hR hQ hS
  let A := variablePhysicalSourceGraph P R hP hR
  let B := variableSpectralSourceGraph Q S hQ hS
  let v := u+A u
  let w := (E-1) v
  have hEv : E v=v+w := by simp [w]
  ext n
  change (seamQProjection (E v)-B (E v)) ((n,true),(n,true)) = _
  simp only [lp.coeFn_sub,Pi.sub_apply,seamQProjection,momentProjection_apply,seamGIndices,seamCIndices,
    Set.mem_union,Set.mem_setOf_eq,and_self,or_true,ite_true]
  change (E v) ((n,true),(n,true)) - (B (E v)) ((n,true),(n,true)) =
    u ((n,true),(n,true))-Complex.I*((variableSourceRowDenominator P R Q S n:ℂ)*u ((n,false),(n,false)))+
      (w ((n,true),(n,true))-Complex.I*(((variableSourceTangent Q S n/shrinkingNewtonSourceKappa^2:ℝ):ℂ)*w ((n,false),(n,false))))
  have hv11 : v ((n,true),(n,true)) = u ((n,true),(n,true))+
      (-Complex.I*(variableSourceTangent P R n:ℂ)/(shrinkingNewtonSourceKappa:ℂ)^2)*u ((n,false),(n,false)) := by
    simp [v,A,variablePhysicalSourceGraph,variablePhysicalGraph_apply,variablePhysicalGraphCoefficient,seamParityExchange]
  have hv00 : v ((n,false),(n,false))=u ((n,false),(n,false)) := by
    simp [v,A,variablePhysicalSourceGraph,variablePhysicalGraph_apply,variablePhysicalGraphCoefficient]
  have hB (z : SeamMomentArray) : B z ((n,true),(n,true))=
      (Complex.I*(variableSourceTangent Q S n:ℂ)/(shrinkingNewtonSourceKappa:ℂ)^2)*z ((n,false),(n,false)) := by
    simp [B,variableSpectralSourceGraph,variableSpectralGraph_apply,variableSpectralGraphCoefficient,seamParityExchange]
  rw [hB,hEv]
  simp only [lp.coeFn_add,Pi.add_apply,hv11,hv00]
  unfold variableSourceRowDenominator
  push_cast
  ring

end
end MeyerGeneralProblem.Adaptive
