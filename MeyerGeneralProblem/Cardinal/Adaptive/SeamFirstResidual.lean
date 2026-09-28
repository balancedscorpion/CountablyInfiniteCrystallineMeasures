module

public import MeyerGeneralProblem.Cardinal.Adaptive.SeamSchurAssembly
public import MeyerGeneralProblem.Cardinal.Adaptive.SeamLowerCoordinate
public import MeyerGeneralProblem.Cardinal.Adaptive.FullExponentialResidual

@[expose] public section

/-! # The complete gauge residual retains the first actual phase -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The original limiting 00 corner in the complete moment Hilbert space. -/
def seamFirstArray : SeamMomentArray := seamDiagonalEmbedding false false seamFirstVector

theorem seamFirstArray_norm : ‖seamFirstArray‖=1 := by
  rw [seamFirstArray,seamDiagonalEmbedding_norm,seamFirstVector_norm]

@[simp] theorem seamFirstArray_apply (p : SeamMomentIndex) :
    seamFirstArray p=if p=((0,false),(0,false)) then 1 else 0 := by
  rcases p with ⟨⟨i,e⟩,j,f⟩
  simp only [seamFirstArray,seamDiagonalEmbedding_apply,seamFirstVector,lp.single_apply]
  split_ifs <;> simp_all

/-- The complete spectral sine on the first corner retains the actual first node. -/
theorem seamSineColumn_first (b : ℕ → ℂ) (hb : ∀ i, ‖b i‖ ≤ (1/4096 : ℝ)^2) :
    seamSineColumn (1/64) (1/4096) b ((1/4096)^2) (by positivity) hb seamFirstArray=
      ((1/64 : ℂ)⁻¹*b 0) •seamDiagonalEmbedding false true seamFirstVector := by
  ext p
  rcases p with ⟨⟨i,e⟩,j,f⟩
  simp only [seamSineColumn_apply,seamFirstArray_apply,seamDiagonalEmbedding_apply,
    lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,seamFirstVector,lp.single_apply]
  cases e <;> cases f <;> by_cases hi : i=0 <;> by_cases hj : j=0 <;> simp_all [eq_comm]

/-- The physical graph correction on the first corner contains only its actual first tangent. -/
theorem seamPhysicalGraph_first (t : ℕ → ℂ) (ht : ∀ i, ‖t i‖ ≤ (1/4096 : ℝ)^3) :
    seamPhysicalGraph t ht seamFirstArray=
      (-Complex.I*t 0/(1/4096 : ℂ)) •seamDiagonalEmbedding true true seamFirstVector := by
  ext p
  rcases p with ⟨⟨i,e⟩,j,f⟩
  simp only [seamPhysicalGraph_apply,seamPhysicalGraphCoefficient,seamParityExchange,
    seamFirstArray_apply,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,
    seamDiagonalEmbedding_apply,seamFirstVector,lp.single_apply]
  cases e <;> cases f <;> by_cases hi : i=0 <;> by_cases hj : j=0 <;> simp_all [eq_comm]

/-- The spectral graph residual likewise retains its actual first tangent. -/
theorem seamSpectralGraph_first (t : ℕ → ℂ) (ht : ∀ i, ‖t i‖ ≤ (1/4096 : ℝ)^3) :
    seamSpectralGraph t ht seamFirstArray=
      (Complex.I*t 0/(1/4096 : ℂ)) •seamDiagonalEmbedding true true seamFirstVector := by
  ext p
  rcases p with ⟨⟨i,e⟩,j,f⟩
  simp only [seamSpectralGraph_apply,seamSpectralGraphCoefficient,seamParityExchange,
    seamFirstArray_apply,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,
    seamDiagonalEmbedding_apply,seamFirstVector,lp.single_apply]
  cases e <;> cases f <;> by_cases hi : i=0 <;> by_cases hj : j=0 <;> simp_all [eq_comm]

/-- The whole coordinate on a vector is controlled by its actual sine residual. -/
theorem seamCoordinate_apply_sine_bound (S : SeamMomentArray →L[ℂ] SeamMomentArray)
    (hSS : ‖S*S‖ ≤ 5*(1/4096 : ℝ)) (u : SeamMomentArray) :
    ‖seamCoordinateOperator S u‖ ≤ ‖S u‖ := by
  have hc : Commute (S*S) S := by change (S*S)*S=S*(S*S); exact mul_assoc _ _ _
  have hh := (seamArcsineFactor_commute _ _ hc).eq
  have he : seamCoordinateOperator S u=(2*(Real.pi : ℂ))⁻¹ •(seamArcsineFactor (S*S) (S u)) := by
    change ((2*(Real.pi : ℂ))⁻¹ •(S*seamArcsineFactor (S*S))) u=_
    rw [←hh]
    rfl
  have hp : ‖(2*(Real.pi : ℂ))⁻¹‖ ≤ (1/6 : ℝ) := by
    rw [norm_inv,norm_mul]
    norm_num only [Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
    rw [one_div]
    exact inv_anti₀ (by norm_num) (by nlinarith [Real.pi_gt_three])
  rw [he,norm_smul]
  calc
    _ ≤ ‖(2*(Real.pi : ℂ))⁻¹‖*(‖seamArcsineFactor (S*S)‖*‖S u‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
    _ ≤ (1/6 : ℝ)*((1-5*(1/4096 : ℝ))⁻¹*‖S u‖) := by
      gcongr
      exact seamArcsineFactor_norm _ hSS
    _ ≤ _ := by nlinarith [norm_nonneg (S u)]

/-- All generator terms on the first corner retain the first spectral node. -/
theorem seamGaugeGenerator_first_bound (a b : ℕ → ℂ)
    (ha : ∀ i, ‖a i‖ ≤ (1/4096 : ℝ)^2) (hb : ∀ i, ‖b i‖ ≤ (1/4096 : ℝ)^2) :
    ‖seamGaugeGenerator
      (seamSineRow (1/64) (1/4096) a ((1/4096)^2) (by positivity) ha)
      (seamSineColumn (1/64) (1/4096) b ((1/4096)^2) (by positivity) hb) seamFirstArray‖ ≤ 8*‖b 0‖ := by
  let S := seamSineRow (1/64) (1/4096) a ((1/4096)^2) (by positivity) ha
  let T := seamSineColumn (1/64) (1/4096) b ((1/4096)^2) (by positivity) hb
  have hp : ‖-2*(Real.pi : ℂ)*Complex.I‖ ≤ 8 := by
    simp only [norm_mul,norm_neg,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos,Complex.norm_I,mul_one]
    linarith [Real.pi_lt_four]
  have hx : ‖seamCoordinateOperator S‖ ≤ (1/64 : ℝ) :=
    seamCoordinateOperator_norm _ (seamSineRow_constant_bound a ha) (seamSineRow_square_norm a ha)
  have hy : ‖seamCoordinateOperator T seamFirstArray‖ ≤ 64*‖b 0‖ := by
    apply (seamCoordinate_apply_sine_bound T (seamSineColumn_square_norm b hb) _).trans
    dsimp only [T]
    rw [seamSineColumn_first,norm_smul,seamDiagonalEmbedding_norm,seamFirstVector_norm,mul_one,norm_mul]
    norm_num
  change ‖(-2*(Real.pi : ℂ)*Complex.I) •(seamCoordinateOperator S (seamCoordinateOperator T seamFirstArray))‖ ≤ _
  rw [norm_smul]
  calc
    _ ≤ ‖-2*(Real.pi : ℂ)*Complex.I‖*(‖seamCoordinateOperator S‖*‖seamCoordinateOperator T seamFirstArray‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
    _ ≤ 8*((1/64 : ℝ)*(64*‖b 0‖)) := by gcongr
    _ = _ := by ring

/-- The entire gauge residual at the corner tends to zero with the first actual node. -/
theorem seamGaugeOperator_first_bound (a b : ℕ → ℂ)
    (ha : ∀ i, ‖a i‖ ≤ (1/4096 : ℝ)^2) (hb : ∀ i, ‖b i‖ ≤ (1/4096 : ℝ)^2) :
    ‖seamGaugeOperator
      (seamSineRow (1/64) (1/4096) a ((1/4096)^2) (by positivity) ha)
      (seamSineColumn (1/64) (1/4096) b ((1/4096)^2) (by positivity) hb) seamFirstArray-seamFirstArray‖ ≤ 16*‖b 0‖ := by
  let Z := seamGaugeGenerator
    (seamSineRow (1/64) (1/4096) a ((1/4096)^2) (by positivity) ha)
    (seamSineColumn (1/64) (1/4096) b ((1/4096)^2) (by positivity) hb)
  have hZ : ‖Z‖ ≤ 8*(1/4096 : ℝ) := seamGaugeGenerator_norm _ _
    (seamSineRow_constant_bound a ha) (seamSineRow_square_norm a ha)
    (seamSineColumn_constant_bound b hb) (seamSineColumn_square_norm b hb)
  apply (fullExponential_apply_sub_self_bound Z (hZ.trans_lt (by norm_num)) _).trans
  have hi : (1-‖Z‖)⁻¹ ≤ 2 := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ (by linarith : 0 < 1-‖Z‖)).mpr
    linarith
  calc
    _ ≤ 2*(8*‖b 0‖) := mul_le_mul hi (seamGaugeGenerator_first_bound a b ha hb) (norm_nonneg _) (by norm_num)
    _ = _ := by ring

/-- Full graph residual bound retaining the actual vector residuals of all three corrections. -/
theorem fullGraphOperator_apply_residual_bound (Q E CA CB : SeamMomentArray →L[ℂ] SeamMomentArray)
    (hQ : ‖Q‖ ≤ 1) (hE : ‖E‖ ≤ 2) (hCB : ‖CB‖ ≤ 1)
    (x : SeamMomentArray) (hx : Q x=0) :
    ‖fullGraphOperator Q E CA CB x‖ ≤ 2*‖E x-x‖+4*‖CA x‖+‖CB x‖ := by
  have hn : ‖Q-CB‖ ≤ 2 := (norm_sub_le _ _).trans (by linarith)
  have he : fullGraphOperator Q E CA CB x=
      (Q-CB) (E x-x)+(Q-CB) (E (CA x))-CB x := by
    change (Q-CB) (E (x+CA x))=_
    simp only [map_add,map_sub,sub_apply,hx]
    abel
  rw [he]
  calc
    _ ≤ (‖(Q-CB) (E x-x)‖+‖(Q-CB) (E (CA x))‖)+‖CB x‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (‖Q-CB‖*‖E x-x‖+‖Q-CB‖*(‖E‖*‖CA x‖))+‖CB x‖ := by
      gcongr
      · exact ContinuousLinearMap.le_opNorm _ _
      · exact (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_left (E.le_opNorm _) (norm_nonneg _))
    _ ≤ (2*‖E x-x‖+2*(2*‖CA x‖))+‖CB x‖ := by gcongr
    _ = _ := by ring

/-- The complete graph-corrected first residual retains only the first actual node and tangents. -/
theorem seamFullOperator_first_bound (a b ta tb : ℕ → ℂ)
    (ha : ∀ i, ‖a i‖ ≤ (1/4096 : ℝ)^2) (hb : ∀ i, ‖b i‖ ≤ (1/4096 : ℝ)^2)
    (hta : ∀ i, ‖ta i‖ ≤ (1/4096 : ℝ)^3) (htb : ∀ i, ‖tb i‖ ≤ (1/4096 : ℝ)^3) :
    ‖seamFullOperator a b ta tb ha hb hta htb seamFirstArray‖ ≤
      32768*(‖ta 0‖+‖tb 0‖+‖b 0‖) := by
  let E := seamGaugeOperator
    (seamSineRow (1/64) (1/4096) a ((1/4096)^2) (by positivity) ha)
    (seamSineColumn (1/64) (1/4096) b ((1/4096)^2) (by positivity) hb)
  have hE : ‖E‖ ≤ 2 := by
    have hn := norm_le_norm_sub_add E 1
    have he := seamGaugeOperator_actual_close a b ha hb
    rw [norm_one] at hn
    dsimp only [E] at hn ⊢
    linarith
  have hca : ‖seamPhysicalGraph ta hta seamFirstArray‖=4096*‖ta 0‖ := by
    rw [seamPhysicalGraph_first,norm_smul,seamDiagonalEmbedding_norm,seamFirstVector_norm,mul_one]
    simp [norm_div,norm_mul,mul_comm]
  have hcb : ‖seamSpectralGraph tb htb seamFirstArray‖=4096*‖tb 0‖ := by
    rw [seamSpectralGraph_first,norm_smul,seamDiagonalEmbedding_norm,seamFirstVector_norm,mul_one]
    simp [norm_div,norm_mul,mul_comm]
  apply (fullGraphOperator_apply_residual_bound _ E _ _ (momentProjection_norm_le_one _) hE
    ((seamSpectralGraph_norm tb htb).trans (by norm_num)) seamFirstArray (seamQProjection_D _)).trans
  rw [hca,hcb]
  have he := seamGaugeOperator_first_bound a b ha hb
  change ‖E seamFirstArray-seamFirstArray‖ ≤ _ at he
  nlinarith [norm_nonneg (ta 0),norm_nonneg (tb 0),norm_nonneg (b 0)]

end
end MeyerGeneralProblem.Adaptive
