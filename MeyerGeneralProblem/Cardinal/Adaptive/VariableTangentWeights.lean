module

public import MeyerGeneralProblem.Cardinal.Adaptive.VariableGaugeFactor

@[expose] public section

/-! Actual positive tangent ratios for the bounded corrected row composition. -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section

/-- The source phases have tangent at most four times their distance. -/
theorem tan_phase_le_four_mul (t : ℝ) (ht : 0 ≤ t) (hu : t ≤ 1/16) :
    Real.tan (Real.pi*t) ≤ 4*t := by
  have hs := sine_phase_bounds t ht hu
  have hsn : 0 ≤ Real.sin (Real.pi*t) := by linarith [hs.1]
  have hc : 0 ≤ Real.cos (Real.pi*t) := Real.cos_nonneg_of_mem_Icc
    ⟨by nlinarith [Real.pi_pos],by nlinarith [Real.pi_pos]⟩
  have hc4 : 4/5 ≤ Real.cos (Real.pi*t) := by
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi*t)]
  have hsin : Real.sin (Real.pi*t) ≤ (16/5)*t := by
    apply (Real.sin_le (mul_nonneg Real.pi_pos.le ht)).trans
    nlinarith [Real.pi_lt_d2]
  rw [Real.tan_eq_sin_div_cos]
  apply (div_le_iff₀ (by linarith : 0 < Real.cos (Real.pi*t))).2
  nlinarith [mul_nonneg ht (sub_nonneg.mpr hc4)]

/-- The actual tangent denominator is strictly positive and at least three
 times its positive phase distance. -/
theorem three_mul_phase_le_tan (t : ℝ) (ht : 0 < t) (hu : t ≤ 1/16) :
    3*t ≤ Real.tan (Real.pi*t) := by
  have h := Real.le_tan (mul_nonneg Real.pi_pos.le ht.le)
    (by nlinarith [Real.pi_pos] : Real.pi*t < Real.pi/2)
  nlinarith [Real.pi_gt_three]

/-- The ratio used after both corrected next-level weights is uniformly small. -/
theorem phase_product_div_tangent_sum_le (ε δ ρ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (heρ : ε ≤ ρ) (hdρ : δ ≤ ρ) (hr : ρ ≤ 1/16) :
    ε*δ/(Real.tan (Real.pi*ε)+Real.tan (Real.pi*δ)) ≤ ρ/6 := by
  have he := three_mul_phase_le_tan ε hε (heρ.trans hr)
  have hd := three_mul_phase_le_tan δ hδ (hdρ.trans hr)
  have ht : 0 < Real.tan (Real.pi*ε)+Real.tan (Real.pi*δ) := by linarith
  apply (div_le_iff₀ ht).2
  have h1 := mul_le_mul_of_nonneg_right heρ hδ.le
  have h2 := mul_le_mul_of_nonneg_right hdρ hε.le
  have h3 := mul_le_mul_of_nonneg_left (add_le_add he hd) (hε.le.trans heρ)
  nlinarith

/-- The spectral share of the actual positive denominator is at most one. -/
theorem tangent_div_tangent_sum_mem_unit (ε δ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (he : ε ≤ 1/16) (hd : δ ≤ 1/16) :
    0 ≤ Real.tan (Real.pi*δ)/(Real.tan (Real.pi*ε)+Real.tan (Real.pi*δ)) ∧
      Real.tan (Real.pi*δ)/(Real.tan (Real.pi*ε)+Real.tan (Real.pi*δ)) ≤ 1 := by
  have hte := three_mul_phase_le_tan ε hε he
  have htd := three_mul_phase_le_tan δ hδ hd
  have ht : 0 < Real.tan (Real.pi*ε)+Real.tan (Real.pi*δ) := by linarith
  constructor
  · exact div_nonneg (by linarith) ht.le
  · apply (div_le_one ht).2
    linarith

/-- The literal next-level source tangent coefficient. -/
def variableSourceTangent (P R : ℕ) (i : ℕ) : ℝ :=
  Real.tan (Real.pi * rapidDistance P R (i+1))

theorem variableSourceTangent_pos (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) (i : ℕ) :
    0 < variableSourceTangent P R i := by
  have he := variableNewton_source_phase_bound P R hP hR (i+1)
  have h := three_mul_phase_le_tan _ he.1
    (he.2.trans (by norm_num [shrinkingNewtonSourceKappa]))
  exact lt_of_lt_of_le (mul_pos (by norm_num : (0:ℝ)<3) he.1) h

theorem variableSourceTangent_le (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) (i : ℕ) :
    variableSourceTangent P R i ≤ 4*shrinkingNewtonSourceKappa^4 := by
  have he := variableNewton_source_phase_bound P R hP hR (i+1)
  exact (tan_phase_le_four_mul _ he.1.le
    (he.2.trans (by norm_num [shrinkingNewtonSourceKappa]))).trans
      (mul_le_mul_of_nonneg_left he.2 (by norm_num))

/-- The actual inverse-row composition coefficient, already multiplied by
both next-level phase weights; no inverse diagonal is constructed. -/
def variableNormalizedGaugeWeight (P R Q S : ℕ) (i : ℕ) : ℝ :=
  shrinkingNewtonSourceKappa^2 * (rapidDistance P R (i+1)*rapidDistance Q S (i+1)/
    (variableSourceTangent P R i+variableSourceTangent Q S i))

theorem variableNormalizedGaugeWeight_bounds (P R Q S : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R)
    (hQ : 1 ≤ Q) (hS : 1 ≤ S) (i : ℕ) :
    0 ≤ variableNormalizedGaugeWeight P R Q S i ∧
      variableNormalizedGaugeWeight P R Q S i ≤ shrinkingNewtonSourceKappa^6/6 := by
  have he := variableNewton_source_phase_bound P R hP hR (i+1)
  have hd := variableNewton_source_phase_bound Q S hQ hS (i+1)
  have hp := variableSourceTangent_pos P R hP hR i
  have hq := variableSourceTangent_pos Q S hQ hS i
  constructor
  · unfold variableNormalizedGaugeWeight
    exact mul_nonneg (sq_nonneg _) (div_nonneg (mul_nonneg he.1.le hd.1.le) (by linarith))
  · have h := phase_product_div_tangent_sum_le _ _ _ he.1 hd.1 he.2 hd.2
      (by norm_num [shrinkingNewtonSourceKappa])
    have hh := mul_le_mul_of_nonneg_left h (sq_nonneg shrinkingNewtonSourceKappa)
    calc
      _ ≤ shrinkingNewtonSourceKappa^2 * (shrinkingNewtonSourceKappa^4/6) := hh
      _ = _ := by ring

/-- The actual positive diagonal of the signed leading equation. -/
def variableSourceRowDenominator (P R Q S : ℕ) (i : ℕ) : ℝ :=
  (variableSourceTangent P R i+variableSourceTangent Q S i)/shrinkingNewtonSourceKappa^2

theorem variableSourceRowDenominator_pos (P R Q S : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R)
    (hQ : 1 ≤ Q) (hS : 1 ≤ S) (i : ℕ) : 0 < variableSourceRowDenominator P R Q S i := by
  exact div_pos (add_pos (variableSourceTangent_pos P R hP hR i)
    (variableSourceTangent_pos Q S hQ hS i)) (sq_pos_of_pos shrinkingNewtonSourceKappa_pos)

theorem variableSourceRowDenominator_le (P R Q S : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R)
    (hQ : 1 ≤ Q) (hS : 1 ≤ S) (i : ℕ) :
    variableSourceRowDenominator P R Q S i ≤ 8*shrinkingNewtonSourceKappa^2 := by
  unfold variableSourceRowDenominator
  apply (div_le_iff₀ (sq_pos_of_pos shrinkingNewtonSourceKappa_pos)).2
  have h := add_le_add (variableSourceTangent_le P R hP hR i) (variableSourceTangent_le Q S hQ hS i)
  convert h using 1 <;> ring

theorem variableNormalizedGaugeWeight_cancellation (P R Q S : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R)
    (hQ : 1 ≤ Q) (hS : 1 ≤ S) (i : ℕ) :
    variableSourceRowDenominator P R Q S i * variableNormalizedGaugeWeight P R Q S i =
      rapidDistance P R (i+1)*rapidDistance Q S (i+1) := by
  have hs : variableSourceTangent P R i+variableSourceTangent Q S i ≠ 0 :=
    ne_of_gt (add_pos (variableSourceTangent_pos P R hP hR i) (variableSourceTangent_pos Q S hQ hS i))
  unfold variableSourceRowDenominator variableNormalizedGaugeWeight
  field_simp [hs,ne_of_gt shrinkingNewtonSourceKappa_pos]

end
end MeyerGeneralProblem.Adaptive
