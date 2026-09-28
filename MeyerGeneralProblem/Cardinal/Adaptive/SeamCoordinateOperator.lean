module

public import MeyerGeneralProblem.Cardinal.Adaptive.SeamSineOperator
public import MeyerGeneralProblem.Cardinal.Adaptive.FullExponentialBounds
public import MeyerGeneralProblem.Cardinal.Adaptive.ScalarArcsineSeries
public import Mathlib.Analysis.Real.Pi.Bounds
import all Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section

/-! # Full arcsine coordinate operators and the complete bounded seam gauge -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section

/-- Compatibility of scalar and composition actions on the operator space. -/
instance seamOperator_isScalarTower :
    IsScalarTower ℂ (SeamMomentArray →L[ℂ] SeamMomentArray) (SeamMomentArray →L[ℂ] SeamMomentArray) := by
  constructor
  intro c A B
  change (c • A) * B = c • (A * B)
  exact ContinuousLinearMap.smul_comp c A B

/-- Complex scalars commute with the composition action. -/
instance seamOperator_smulCommClass :
    SMulCommClass ℂ (SeamMomentArray →L[ℂ] SeamMomentArray) (SeamMomentArray →L[ℂ] SeamMomentArray) := by
  constructor
  intro c A B
  change c • (A * B) = A * (c • B)
  exact (ContinuousLinearMap.comp_smul A c B).symm

/-- Scalar multiplication commutes with operator multiplication on the left. -/
theorem seamOperator_smul_mul (c : ℂ) (A B : SeamMomentArray →L[ℂ] SeamMomentArray) :
    (c • A) * B = c • (A * B) := ContinuousLinearMap.smul_comp c A B

/-- Scalar multiplication commutes with operator multiplication on the right. -/
theorem seamOperator_mul_smul (c : ℂ) (A B : SeamMomentArray →L[ℂ] SeamMomentArray) :
    A * (c • B) = c • (A * B) := ContinuousLinearMap.comp_smul A c B

/-- The actual array contains the nonzero diagonal first vector. -/
instance seamMomentArray_nontrivial : Nontrivial SeamMomentArray := by
  refine ⟨⟨seamDiagonalEmbedding false false seamFirstVector,0,?_⟩⟩
  intro he
  have hn := seamDiagonalEmbedding_norm false false seamFirstVector
  rw [he,norm_zero,seamFirstVector_norm] at hn
  exact zero_ne_one hn


/-- The actual full central-binomial operator series h(C). -/
def seamArcsineFactor (C : SeamMomentArray →L[ℂ] SeamMomentArray) : SeamMomentArray →L[ℂ] SeamMomentArray :=
  boundedOperatorSeries (fun n => (scalarArcsineCoefficient n : ℂ)) C

theorem scalarArcsineCoefficient_cast_norm (n : ℕ) : ‖(scalarArcsineCoefficient n : ℂ)‖ ≤ 1 := by
  rw [scalarArcsineCoefficient_complex]
  exact scalarArcsineCoefficient_complex_norm_le_one n

theorem seamArcsineFactor_hasSum (C : SeamMomentArray →L[ℂ] SeamMomentArray) (hC : ‖C‖ < 1) :
    HasSum (fun n => (scalarArcsineCoefficient n : ℂ) •C^n) (seamArcsineFactor C) :=
  boundedOperatorSeries_hasSum _ scalarArcsineCoefficient_cast_norm C hC

theorem seamArcsineFactor_norm (C : SeamMomentArray →L[ℂ] SeamMomentArray)
    (hC : ‖C‖ ≤ 5*(1/4096 : ℝ)) : ‖seamArcsineFactor C‖ ≤ (1-5*(1/4096 : ℝ))⁻¹ := by
  apply (boundedOperatorSeries_norm_le _ scalarArcsineCoefficient_cast_norm C (by linarith)).trans
  exact inv_anti₀ (by norm_num) (by linarith)

/-- The full arcsine factor differs from identity by at most 6R. -/
theorem seamArcsineFactor_close (C : SeamMomentArray →L[ℂ] SeamMomentArray)
    (hC : ‖C‖ ≤ 5*(1/4096 : ℝ)) : ‖seamArcsineFactor C-1‖ ≤ 6*(1/4096 : ℝ) := by
  apply (boundedOperatorSeries_sub_one_bound _ scalarArcsineCoefficient_cast_norm
    (by simp [scalarArcsineCoefficient_zero]) C (by linarith)).trans
  apply (div_le_iff₀ (by linarith : 0 < 1-‖C‖)).mpr
  linarith

/-- Exact source normalization of the coordinate operator, with no square-root choice. -/
def seamCoordinateOperator (S : SeamMomentArray →L[ℂ] SeamMomentArray) : SeamMomentArray →L[ℂ] SeamMomentArray :=
  (2*(Real.pi : ℂ))⁻¹ •(S*seamArcsineFactor (S*S))

theorem seamCoordinateOperator_norm (S : SeamMomentArray →L[ℂ] SeamMomentArray)
    (hS : ‖S‖ ≤ 3*(1/64 : ℝ)) (hSS : ‖S*S‖ ≤ 5*(1/4096 : ℝ)) :
    ‖seamCoordinateOperator S‖ ≤ (1/64 : ℝ) := by
  have hp : ‖(2*(Real.pi : ℂ))⁻¹‖ ≤ (1/6 : ℝ) := by
    rw [norm_inv,norm_mul]
    norm_num only [Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
    rw [one_div]
    exact inv_anti₀ (by norm_num) (by nlinarith [Real.pi_gt_three])
  rw [seamCoordinateOperator,norm_smul]
  calc
    _ ≤ ‖(2*(Real.pi : ℂ))⁻¹‖*(‖S‖*‖seamArcsineFactor (S*S)‖) :=
      mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg _)
    _ ≤ (1/6 : ℝ)*((3*(1/64 : ℝ))*(1-5*(1/4096 : ℝ))⁻¹) := by
      gcongr
      exact seamArcsineFactor_norm (S*S) hSS
    _ ≤ _ := by norm_num

/-- The true sine square satisfies the stronger 5R bound. -/
theorem seamSineRow_square_norm (a : ℕ → ℂ) (ha : ∀ i, ‖a i‖ ≤ (1/4096 : ℝ)^2) :
    let S := seamSineRow (1/64) (1/4096) a ((1/4096)^2) (by positivity) ha
    ‖S*S‖ ≤ 5*(1/4096 : ℝ) := by
  dsimp only
  change ‖(seamSineRow (1/64) (1/4096) a ((1/4096)^2) (by positivity) ha).comp
    (seamSineRow (1/64) (1/4096) a ((1/4096)^2) (by positivity) ha)‖ ≤ _
  rw [seamSineRow_square _ _ (by norm_num)]
  have hJ := seamNewtonRow_norm_le (1/4096) a ((1/4096)^2) (by positivity) ha
  norm_num only [norm_div,norm_one,Complex.norm_ofNat] at hJ
  have hI : ‖(2 : ℂ) •ContinuousLinearMap.id ℂ SeamMomentArray-
      seamNewtonRow (1/4096) a ((1/4096)^2) (by positivity) ha‖ ≤ 2+((1/4096)+(1/4096)^2 : ℝ) := by
    apply (norm_sub_le _ _).trans
    rw [norm_smul]
    norm_num only [Complex.norm_ofNat,ContinuousLinearMap.norm_id,mul_one]
    linarith
  calc
    _ ≤ ‖seamNewtonRow (1/4096) a ((1/4096)^2) (by positivity) ha‖*
      ‖(2 : ℂ) •ContinuousLinearMap.id ℂ SeamMomentArray-seamNewtonRow (1/4096) a ((1/4096)^2) (by positivity) ha‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ((1/4096)+(1/4096)^2 : ℝ)*(2+((1/4096)+(1/4096)^2 : ℝ)) := by
      apply mul_le_mul _ hI (norm_nonneg _) (by positivity)
      convert hJ using 1 <;> first | rfl | norm_num
    _ ≤ _ := by norm_num

/-- Conjugation by the literal axis exchange is contractive in operator norm. -/
theorem seamTranspose_conjugate_norm (A : SeamMomentArray →L[ℂ] SeamMomentArray) :
    ‖seamTranspose.comp (A.comp seamTranspose)‖ ≤ ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro u
  change ‖seamTranspose (A (seamTranspose u))‖ ≤ _
  calc
    _ ≤ ‖A (seamTranspose u)‖ := seamTranspose_norm_apply _
    _ ≤ ‖A‖*‖seamTranspose u‖ := A.le_opNorm _
    _ ≤ _ := mul_le_mul_of_nonneg_left (seamTranspose_norm_apply _) (norm_nonneg _)

theorem seamSineColumn_square_norm (b : ℕ → ℂ) (hb : ∀ i, ‖b i‖ ≤ (1/4096 : ℝ)^2) :
    let S := seamSineColumn (1/64) (1/4096) b ((1/4096)^2) (by positivity) hb
    ‖S*S‖ ≤ 5*(1/4096 : ℝ) := by
  let A := seamSineRow (1/64) (1/4096) b ((1/4096)^2) (by positivity) hb
  have he : (seamSineColumn (1/64) (1/4096) b ((1/4096)^2) (by positivity) hb)*
      (seamSineColumn (1/64) (1/4096) b ((1/4096)^2) (by positivity) hb)=
      seamTranspose.comp ((A*A).comp seamTranspose) := by
    ext u p
    change seamTranspose (A (seamTranspose (seamTranspose (A (seamTranspose u))))) p=
      seamTranspose (A (A (seamTranspose u))) p
    rw [seamTranspose_involutive]
  dsimp only
  rw [he]
  exact (seamTranspose_conjugate_norm (A*A)).trans (seamSineRow_square_norm b hb)

/-- The complete quadratic gauge generator constructed from both actual coordinate operators. -/
def seamGaugeGenerator (S T : SeamMomentArray →L[ℂ] SeamMomentArray) : SeamMomentArray →L[ℂ] SeamMomentArray :=
  (-2*(Real.pi : ℂ)*Complex.I) •(seamCoordinateOperator S*seamCoordinateOperator T)

/-- The full gauge is the entire Banach-algebra exponential. -/
def seamGaugeOperator (S T : SeamMomentArray →L[ℂ] SeamMomentArray) : SeamMomentArray →L[ℂ] SeamMomentArray :=
  NormedSpace.exp (seamGaugeGenerator S T)

theorem seamGaugeGenerator_norm (S T : SeamMomentArray →L[ℂ] SeamMomentArray)
    (hS : ‖S‖ ≤ 3*(1/64 : ℝ)) (hSS : ‖S*S‖ ≤ 5*(1/4096 : ℝ))
    (hT : ‖T‖ ≤ 3*(1/64 : ℝ)) (hTT : ‖T*T‖ ≤ 5*(1/4096 : ℝ)) :
    ‖seamGaugeGenerator S T‖ ≤ 8*(1/4096 : ℝ) := by
  have hp : ‖-2*(Real.pi : ℂ)*Complex.I‖ ≤ 8 := by
    simp only [norm_mul,norm_neg,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos,Complex.norm_I,mul_one]
    linarith [Real.pi_lt_four]
  rw [seamGaugeGenerator,norm_smul]
  calc
    _ ≤ ‖-2*(Real.pi : ℂ)*Complex.I‖*(‖seamCoordinateOperator S‖*‖seamCoordinateOperator T‖) :=
      mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg _)
    _ ≤ 8*((1/64 : ℝ)*(1/64 : ℝ)) := by
      gcongr
      · exact seamCoordinateOperator_norm S hS hSS
      · exact seamCoordinateOperator_norm T hT hTT
    _ = _ := by norm_num

/-- The actual full gauge on both arbitrary small phase node sequences is
within 9R of identity in the original operator norm. -/
theorem seamGaugeOperator_actual_close (a b : ℕ → ℂ)
    (ha : ∀ i, ‖a i‖ ≤ (1/4096 : ℝ)^2) (hb : ∀ i, ‖b i‖ ≤ (1/4096 : ℝ)^2) :
    ‖seamGaugeOperator
      (seamSineRow (1/64) (1/4096) a ((1/4096)^2) (by positivity) ha)
      (seamSineColumn (1/64) (1/4096) b ((1/4096)^2) (by positivity) hb)-1‖ ≤ 9*(1/4096 : ℝ) :=
  fullExponential_seam_close _ (seamGaugeGenerator_norm _ _
    (seamSineRow_constant_bound a ha) (seamSineRow_square_norm a ha)
    (seamSineColumn_constant_bound b hb) (seamSineColumn_square_norm b hb))

end
end MeyerGeneralProblem.Adaptive
