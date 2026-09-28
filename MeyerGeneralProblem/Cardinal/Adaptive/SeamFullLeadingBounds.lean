module

public import MeyerGeneralProblem.Cardinal.Adaptive.SeamLeadingCompression

@[expose] public section

/-! # Quantitative leading compression of the actual full corrected gauge -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section

theorem seamSchurH_norm (F : SeamMomentArray →L[ℂ] SeamMomentArray) : ‖seamSchurH F‖ ≤ ‖F‖ := by
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  calc
    _ ≤ 1*(‖F‖*1) := by
      apply mul_le_mul (seamDiagonalReading_norm_le_one true true) _ (norm_nonneg _) zero_le_one
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (seamDiagonalEmbedding_norm_le_one false false) (norm_nonneg _))
    _ = _ := by ring

theorem seamSchurH_one : seamSchurH 1=0 := by
  ext u n
  change seamDiagonalEmbedding false false u ((n,true),(n,true))=0
  simp

theorem seamSchurH_Q_mul (F : SeamMomentArray →L[ℂ] SeamMomentArray) :
    seamSchurH (seamQProjection*F)=seamSchurH F := by
  ext u n
  change seamQProjection (F (seamDiagonalEmbedding false false u)) ((n,true),(n,true))=_
  simp only [seamQProjection,momentProjection_apply,seamCIndices,seamGIndices,Set.mem_union,Set.mem_setOf_eq,lt_self_iff_false,false_or,true_and,eq_self,ite_true]
  rfl

/-- The complete graph correction contributes at most 3R² to the leading compression. -/
theorem seamFullOperator_graph_compression_bound (a b ta tb : ℕ → ℂ)
    (ha : ∀ i, ‖a i‖ ≤ (1/4096 : ℝ)^2) (hb : ∀ i, ‖b i‖ ≤ (1/4096 : ℝ)^2)
    (hta : ∀ i, ‖ta i‖ ≤ (1/4096 : ℝ)^3) (htb : ∀ i, ‖tb i‖ ≤ (1/4096 : ℝ)^3) :
    ‖seamSchurH (seamFullOperator a b ta tb ha hb hta htb)-seamSchurH
      (seamGaugeOperator (seamSineRow (1/64) (1/4096) a ((1/4096)^2) (by positivity) ha)
        (seamSineColumn (1/64) (1/4096) b ((1/4096)^2) (by positivity) hb))‖ ≤ 3*(1/4096 : ℝ)^2 := by
  let E := seamGaugeOperator (seamSineRow (1/64) (1/4096) a ((1/4096)^2) (by positivity) ha)
    (seamSineColumn (1/64) (1/4096) b ((1/4096)^2) (by positivity) hb)
  have hn : ‖E‖ ≤ 1+9*(1/4096 : ℝ) := by
    have h := norm_le_norm_sub_add E 1
    rw [norm_one] at h
    have he : ‖E-1‖ ≤ 9*(1/4096 : ℝ) := seamGaugeOperator_actual_close a b ha hb
    linarith
  change ‖seamSchurH (seamFullOperator a b ta tb ha hb hta htb)-seamSchurH E‖ ≤ _
  rw [←seamSchurH_Q_mul E,←seamSchurH_sub]
  apply (seamSchurH_norm _).trans
  exact fullGraphOperator_seam_correction _ E _ _ (momentProjection_norm_le_one _) hn
    (seamPhysicalGraph_norm ta hta) (seamSpectralGraph_norm tb htb)

/-- The complete exponential remainder contributes at most 65R² after exact compression. -/
theorem seamGaugeOperator_compression_remainder (a b : ℕ → ℂ)
    (ha : ∀ i, ‖a i‖ ≤ (1/4096 : ℝ)^2) (hb : ∀ i, ‖b i‖ ≤ (1/4096 : ℝ)^2) :
    ‖seamSchurH
      (seamGaugeOperator (seamSineRow (1/64) (1/4096) a ((1/4096)^2) (by positivity) ha)
        (seamSineColumn (1/64) (1/4096) b ((1/4096)^2) (by positivity) hb))-
      seamSchurH
      (seamGaugeGenerator (seamSineRow (1/64) (1/4096) a ((1/4096)^2) (by positivity) ha)
        (seamSineColumn (1/64) (1/4096) b ((1/4096)^2) (by positivity) hb))‖ ≤ 65*(1/4096 : ℝ)^2 := by
  let Z := seamGaugeGenerator (seamSineRow (1/64) (1/4096) a ((1/4096)^2) (by positivity) ha)
    (seamSineColumn (1/64) (1/4096) b ((1/4096)^2) (by positivity) hb)
  have he : seamSchurH (NormedSpace.exp Z)-seamSchurH Z=seamSchurH (NormedSpace.exp Z-1-Z) := by
    rw [seamSchurH_sub,seamSchurH_sub,seamSchurH_one,sub_zero]
  change ‖seamSchurH (NormedSpace.exp Z)-seamSchurH Z‖ ≤ _
  rw [he]
  apply (seamSchurH_norm _).trans
  exact fullExponential_seam_quadratic Z (seamGaugeGenerator_norm _ _
    (seamSineRow_constant_bound a ha) (seamSineRow_square_norm a ha)
    (seamSineColumn_constant_bound b hb) (seamSineColumn_square_norm b hb))

/-- The actual full corrected operator has the required 100R² leading error, with no block premise. -/
theorem seamFullOperator_leading_bound (a b ta tb : ℕ → ℂ)
    (ha : ∀ i, ‖a i‖ ≤ (1/4096 : ℝ)^2) (hb : ∀ i, ‖b i‖ ≤ (1/4096 : ℝ)^2)
    (hta : ∀ i, ‖ta i‖ ≤ (1/4096 : ℝ)^3) (htb : ∀ i, ‖tb i‖ ≤ (1/4096 : ℝ)^3) :
    ‖seamSchurH (seamFullOperator a b ta tb ha hb hta htb)-seamLeadingCoefficient •seamBackwardShift‖ ≤ 100*(1/4096 : ℝ)^2 := by
  let E := seamGaugeOperator (seamSineRow (1/64) (1/4096) a ((1/4096)^2) (by positivity) ha)
    (seamSineColumn (1/64) (1/4096) b ((1/4096)^2) (by positivity) hb)
  let Z := seamGaugeGenerator (seamSineRow (1/64) (1/4096) a ((1/4096)^2) (by positivity) ha)
    (seamSineColumn (1/64) (1/4096) b ((1/4096)^2) (by positivity) hb)
  have h1 := seamFullOperator_graph_compression_bound a b ta tb ha hb hta htb
  have h2 := seamGaugeOperator_compression_remainder a b ha hb
  have h3 := seamGaugeGenerator_leading_compression a b ha hb
  have h4 := norm_sub_le_norm_sub_add_norm_sub (seamSchurH (seamFullOperator a b ta tb ha hb hta htb))
    (seamSchurH E) (seamLeadingCoefficient •seamBackwardShift)
  have h5 := norm_sub_le_norm_sub_add_norm_sub (seamSchurH E) (seamSchurH Z) (seamLeadingCoefficient •seamBackwardShift)
  dsimp only [E,Z] at h4 h5
  linarith

end
end MeyerGeneralProblem.Adaptive
