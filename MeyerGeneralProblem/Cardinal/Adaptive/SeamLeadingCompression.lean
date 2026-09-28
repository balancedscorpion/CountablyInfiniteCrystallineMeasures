module

public import MeyerGeneralProblem.Cardinal.Adaptive.SeamLowerCoordinate
public import MeyerGeneralProblem.Cardinal.Adaptive.SeamCoordinateIntertwining
public import MeyerGeneralProblem.Cardinal.Adaptive.SeamSchurAssembly

@[expose] public section

/-! Exact whole-series leading diagonal compression and its quantitative error. -/
noncomputable section
set_option maxHeartbeats 400000
namespace MeyerGeneralProblem.Adaptive

/-- The full spectral parity projection, without restricting either level. -/
def seamColumnParityProjection (e : Bool) : SeamMomentArray →L[ℂ] SeamMomentArray :=
  momentProjection {p | p.2.2=e}

/-- Literal action of spectral parity projection. -/
theorem seamColumnParityProjection_apply (e : Bool) (u : SeamMomentArray) (p : SeamMomentIndex) :
    seamColumnParityProjection e u p=if p.2.2=e then u p else 0 := by
  simp only [seamColumnParityProjection,momentProjection_apply,Set.mem_ofPred_eq]

/-- Physical coordinate series preserve the other parity bit on the entire array. -/
theorem seamCoordinateRow_columnParity (a : ℕ → ℂ) (ha : ∀ i, ‖a i‖ ≤ (1/4096 : ℝ)^2) (e : Bool) :
    (seamColumnParityProjection e).comp
      (seamCoordinateOperator (seamSineRow (1/64) (1/4096) a ((1/4096)^2) (by positivity) ha))=
    (seamCoordinateOperator (seamSineRow (1/64) (1/4096) a ((1/4096)^2) (by positivity) ha)).comp
      (seamColumnParityProjection e) := by
  apply seamCoordinateOperator_intertwine
  · exact (seamSineRow_square_norm a ha).trans_lt (by norm_num)
  · exact (seamSineRow_square_norm a ha).trans_lt (by norm_num)
  · ext u p
    rcases p with ⟨⟨i,b⟩,j,f⟩
    simp only [ContinuousLinearMap.comp_apply]
    simp only [seamColumnParityProjection_apply,seamSineRow_apply]
    by_cases he : f=e <;> cases b <;> simp [he]

/-- Spectral coordinate series preserve the physical parity bit on the entire array. -/
theorem seamCoordinateColumn_rowParity (b : ℕ → ℂ) (hb : ∀ i, ‖b i‖ ≤ (1/4096 : ℝ)^2) (e : Bool) :
    (momentProjection (seamRowParity e)).comp
      (seamCoordinateOperator (seamSineColumn (1/64) (1/4096) b ((1/4096)^2) (by positivity) hb))=
    (seamCoordinateOperator (seamSineColumn (1/64) (1/4096) b ((1/4096)^2) (by positivity) hb)).comp
      (momentProjection (seamRowParity e)) := by
  apply seamCoordinateOperator_intertwine
  · exact (seamSineColumn_square_norm b hb).trans_lt (by norm_num)
  · exact (seamSineColumn_square_norm b hb).trans_lt (by norm_num)
  · ext u p
    rcases p with ⟨⟨i,a⟩,j,f⟩
    simp only [ContinuousLinearMap.comp_apply]
    simp only [momentProjection_apply,seamRowParity,seamSineColumn_apply,Set.mem_ofPred_eq]
    by_cases he : a=e <;> cases f <;> simp [he]

/-- The actual column lower block is exactly the axis conjugate of the full row lower block. -/
theorem seamCoordinateColumn_lower (b : ℕ → ℂ) (hb : ∀ i, ‖b i‖ ≤ (1/4096 : ℝ)^2) :
    seamColumnParityProjection true*
      seamCoordinateOperator (seamSineColumn (1/64) (1/4096) b ((1/4096)^2) (by positivity) hb)*
        seamColumnParityProjection false =
    seamTranspose.comp ((seamLowerCoordinate (seamSineRow (1/64) (1/4096) b ((1/4096)^2) (by positivity) hb)).comp seamTranspose) := by
  rw [seamCoordinateOperator_column]
  ext u p
  simp only [mul_apply_eq_comp,ContinuousLinearMap.comp_apply]
  have he : seamTranspose (seamColumnParityProjection false u)=
      momentProjection (seamRowParity false) (seamTranspose u) := by
    ext q
    simp [seamTranspose_apply,seamColumnParityProjection_apply,momentProjection_apply,seamRowParity]
  rw [he]
  simp only [seamLowerCoordinate,mul_apply_eq_comp,seamColumnParityProjection_apply,
    seamTranspose_apply,momentProjection_apply,seamRowParity,Set.mem_ofPred_eq]

private theorem compression_lower_blocks (A B : SeamMomentArray →L[ℂ] SeamMomentArray)
    (hA : (seamColumnParityProjection true).comp A=A.comp (seamColumnParityProjection true))
    (hB : (momentProjection (seamRowParity false)).comp B=B.comp (momentProjection (seamRowParity false))) :
    seamSchurH (A*B)=seamSchurH
      ((momentProjection (seamRowParity true)*A*momentProjection (seamRowParity false))*
        (seamColumnParityProjection true*B*seamColumnParityProjection false)) := by
  ext u n
  have hc : seamColumnParityProjection false (seamDiagonalEmbedding false false u)=
      seamDiagonalEmbedding false false u := by
    ext p
    simp only [seamColumnParityProjection_apply,seamDiagonalEmbedding_apply]
    split_ifs <;> simp_all
  have hr : momentProjection (seamRowParity false) (seamDiagonalEmbedding false false u)=
      seamDiagonalEmbedding false false u := by
    ext p
    simp only [momentProjection_apply,seamRowParity,seamDiagonalEmbedding_apply,Set.mem_ofPred_eq]
    split_ifs <;> simp_all
  have hp (v : SeamMomentArray) : momentProjection (seamRowParity false) (seamColumnParityProjection true v)=
      seamColumnParityProjection true (momentProjection (seamRowParity false) v) := by
    ext p
    simp only [momentProjection_apply,seamRowParity,seamColumnParityProjection_apply,Set.mem_ofPred_eq]
    split_ifs <;> rfl
  have ha (v : SeamMomentArray) : A (seamColumnParityProjection true v)=seamColumnParityProjection true (A v) :=
    (congrArg (fun U : SeamMomentArray →L[ℂ] SeamMomentArray => U v) hA).symm
  have hb (v : SeamMomentArray) : momentProjection (seamRowParity false) (B v)=B (momentProjection (seamRowParity false) v) :=
    congrArg (fun U : SeamMomentArray →L[ℂ] SeamMomentArray => U v) hB
  change (A (B (seamDiagonalEmbedding false false u))) ((n,true),(n,true))=
    momentProjection (seamRowParity true) (A (momentProjection (seamRowParity false)
      (seamColumnParityProjection true (B (seamColumnParityProjection false (seamDiagonalEmbedding false false u)))))) ((n,true),(n,true))
  rw [hc,hp,hb,hr,ha]
  simp [momentProjection_apply,seamRowParity,seamColumnParityProjection_apply]

/-- Exact compression of the full coordinate tensor to its two lower parity blocks. -/
theorem seamCoordinateTensor_lower_compression (a b : ℕ → ℂ)
    (ha : ∀ i, ‖a i‖ ≤ (1/4096 : ℝ)^2) (hb : ∀ i, ‖b i‖ ≤ (1/4096 : ℝ)^2) :
    seamSchurH (seamCoordinateOperator (seamSineRow (1/64) (1/4096) a ((1/4096)^2) (by positivity) ha)*
      seamCoordinateOperator (seamSineColumn (1/64) (1/4096) b ((1/4096)^2) (by positivity) hb))=
    seamSchurH (seamLowerCoordinate (seamSineRow (1/64) (1/4096) a ((1/4096)^2) (by positivity) ha)*
      seamTranspose.comp ((seamLowerCoordinate (seamSineRow (1/64) (1/4096) b ((1/4096)^2) (by positivity) hb)).comp seamTranspose)) := by
  rw [compression_lower_blocks _ _ (seamCoordinateRow_columnParity a ha true)
    (seamCoordinateColumn_rowParity b hb false),seamCoordinateColumn_lower]
  rfl

/-- The actual diagonal compression is a contraction on whole bounded operators. -/
theorem seamSchurH_norm_le (F : SeamMomentArray →L[ℂ] SeamMomentArray) : ‖seamSchurH F‖ ≤ ‖F‖ := by
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  have hi := seamDiagonalEmbedding_norm_le_one false false
  have ho := seamDiagonalReading_norm_le_one true true
  have hc := F.opNorm_comp_le (seamDiagonalEmbedding false false)
  have hh : ‖F.comp (seamDiagonalEmbedding false false)‖ ≤ ‖F‖ := by
    exact hc.trans (by nlinarith [norm_nonneg F])
  exact (mul_le_mul ho hh (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

/-- Difference commutes with the genuine full diagonal compression. -/
theorem seamSchurH_sub (F G : SeamMomentArray →L[ℂ] SeamMomentArray) :
    seamSchurH (F-G)=seamSchurH F-seamSchurH G := by
  ext u n
  simp [seamSchurH]

/-- Scalar multiplication commutes with the genuine full diagonal compression. -/
theorem seamSchurH_smul (z : ℂ) (F : SeamMomentArray →L[ℂ] SeamMomentArray) :
    seamSchurH (z •F)=z •seamSchurH F := by
  ext u n
  simp [seamSchurH]

/-- Axis conjugation preserves the complete lower-block replacement error bound. -/
theorem seamLowerColumn_constant_error (b : ℕ → ℂ) (hb : ∀ i, ‖b i‖ ≤ (1/4096 : ℝ)^2) :
    ‖seamTranspose.comp ((seamLowerCoordinate (seamSineRow (1/64) (1/4096) b ((1/4096)^2) (by positivity) hb)).comp seamTranspose)-
      seamTranspose.comp ((seamLeadingLower (1/64) (1/4096) b ((1/4096)^2) (by positivity) hb).comp seamTranspose)‖ ≤
      2*(1/4096 : ℝ)*(1/64 : ℝ) := by
  rw [←ContinuousLinearMap.comp_sub,←ContinuousLinearMap.sub_comp]
  exact (seamTranspose_conjugate_norm _).trans (seamLowerCoordinate_constant_error b hb)

/-- The product of both actual lower coordinate blocks is close to the product
of both true leading blocks, uniformly on the entire array. -/
theorem seamLowerTensor_constant_error (a b : ℕ → ℂ)
    (ha : ∀ i, ‖a i‖ ≤ (1/4096 : ℝ)^2) (hb : ∀ i, ‖b i‖ ≤ (1/4096 : ℝ)^2) :
    let A := seamLowerCoordinate (seamSineRow (1/64) (1/4096) a ((1/4096)^2) (by positivity) ha)
    let B := seamTranspose.comp ((seamLowerCoordinate (seamSineRow (1/64) (1/4096) b ((1/4096)^2) (by positivity) hb)).comp seamTranspose)
    let Y := seamLeadingLower (1/64) (1/4096) a ((1/4096)^2) (by positivity) ha
    let V := seamTranspose.comp ((seamLeadingLower (1/64) (1/4096) b ((1/4096)^2) (by positivity) hb).comp seamTranspose)
    ‖A*B-Y*V‖ ≤ (5/3 : ℝ)*(1/4096 : ℝ)^2 := by
  dsimp only
  let A := seamLowerCoordinate (seamSineRow (1/64) (1/4096) a ((1/4096)^2) (by positivity) ha)
  let B := seamTranspose.comp ((seamLowerCoordinate (seamSineRow (1/64) (1/4096) b ((1/4096)^2) (by positivity) hb)).comp seamTranspose)
  let Y := seamLeadingLower (1/64) (1/4096) a ((1/4096)^2) (by positivity) ha
  let V := seamTranspose.comp ((seamLeadingLower (1/64) (1/4096) b ((1/4096)^2) (by positivity) hb).comp seamTranspose)
  change ‖A*B-Y*V‖ ≤ _
  have he : A*B-Y*V=(A-Y)*B+Y*(B-V) := by
    rw [sub_mul, mul_sub]
    abel
  have hA : ‖A-Y‖ ≤ 2*(1/4096 : ℝ)*(1/64 : ℝ) := seamLowerCoordinate_constant_error a ha
  have hB : ‖B‖ ≤ (1/64 : ℝ)/2 :=
    (seamTranspose_conjugate_norm _).trans (seamLowerCoordinate_constant_norm b hb)
  have hY : ‖Y‖ ≤ (1/64 : ℝ)/3 := seamLeadingLower_constant_norm a ha
  have hV : ‖B-V‖ ≤ 2*(1/4096 : ℝ)*(1/64 : ℝ) := seamLowerColumn_constant_error b hb
  rw [he]
  calc
    _ ≤ ‖A-Y‖*‖B‖+‖Y‖*‖B-V‖ := (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
    _ ≤ (2*(1/4096 : ℝ)*(1/64 : ℝ))*((1/64 : ℝ)/2)+((1/64 : ℝ)/3)*(2*(1/4096 : ℝ)*(1/64 : ℝ)) := by gcongr
    _ = _ := by norm_num

/-- The complete leading tensor has its exact diagonal shift and diagonal product;
both mixed single shifts vanish by actual diagonal insertion. -/
theorem seamLeadingTensor_compression_apply (a b : ℕ → ℂ)
    (ha : ∀ i, ‖a i‖ ≤ (1/4096 : ℝ)^2) (hb : ∀ i, ‖b i‖ ≤ (1/4096 : ℝ)^2)
    (u : SeamSequence) (n : ℕ) :
    seamSchurH (seamLeadingLower (1/64) (1/4096) a ((1/4096)^2) (by positivity) ha*
      seamTranspose.comp ((seamLeadingLower (1/64) (1/4096) b ((1/4096)^2) (by positivity) hb).comp seamTranspose)) u n=
      ((2*(Real.pi:ℂ))⁻¹*64)^2*((1/4096:ℂ)^2*u (n+1)+a n*b n*u n) := by
  simp only [seamSchurH,ContinuousLinearMap.comp_apply,mul_apply_eq_comp,seamDiagonalReading_apply,
    seamLeadingLower,_root_.smul_apply,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,
    seamTranspose_apply,seamSineLower_apply,ite_true,seamDiagonalEmbedding_apply]
  simp only [and_self,ite_true,Nat.add_eq_left,one_ne_zero,false_and,ite_false,
    show ¬n=n+1 by omega,mul_zero,add_zero,zero_add]
  norm_num
  ring

/-- Norm of the full diagonal-product remainder in the leading gauge compression. -/
theorem seamLeadingTensor_gauge_error (a b : ℕ → ℂ)
    (ha : ∀ i, ‖a i‖ ≤ (1/4096 : ℝ)^2) (hb : ∀ i, ‖b i‖ ≤ (1/4096 : ℝ)^2) :
    ‖seamSchurH ((-2*(Real.pi:ℂ)*Complex.I) •
      (seamLeadingLower (1/64) (1/4096) a ((1/4096)^2) (by positivity) ha*
        seamTranspose.comp ((seamLeadingLower (1/64) (1/4096) b ((1/4096)^2) (by positivity) hb).comp seamTranspose)))-
      seamLeadingCoefficient •seamBackwardShift‖ ≤ (1/4096 : ℝ)^2 := by
  let d : ℂ := -Complex.I*4096/(2*(Real.pi:ℂ))
  have hab (i : ℕ) : ‖a i*b i‖ ≤ (1/4096 : ℝ)^4 := by
    rw [norm_mul]
    exact (mul_le_mul (ha i) (hb i) (norm_nonneg _) (by positivity)).trans_eq (by ring)
  let M : SeamSequence →L[ℂ] SeamSequence := momentDiagonal (fun i => a i*b i) ((1/4096)^4) (by positivity) hab
  have he : seamSchurH ((-2*(Real.pi:ℂ)*Complex.I) •
      (seamLeadingLower (1/64) (1/4096) a ((1/4096)^2) (by positivity) ha*
        seamTranspose.comp ((seamLeadingLower (1/64) (1/4096) b ((1/4096)^2) (by positivity) hb).comp seamTranspose)))-
      seamLeadingCoefficient •seamBackwardShift=d •M := by
    rw [seamSchurH_smul]
    ext u n
    dsimp only [M]
    simp only [_root_.sub_apply,_root_.smul_apply,lp.coeFn_sub,Pi.sub_apply,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,
      seamLeadingTensor_compression_apply,seamBackwardShift_apply,momentDiagonal_apply]
    dsimp only [d,seamLeadingCoefficient]
    have hp : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp
    ring
  have hd : ‖d‖ ≤ 4096 := by
    dsimp only [d]
    rw [norm_div,norm_mul,norm_neg,Complex.norm_I,norm_mul]
    norm_num only [Complex.norm_ofNat,one_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [Real.pi_gt_three]
  rw [he,norm_smul]
  have hm : ‖M‖ ≤ (1/4096 : ℝ)^4 := momentDiagonal_norm_le _ _ _ _
  exact (mul_le_mul hd hm (norm_nonneg _) (by norm_num)).trans (by norm_num)

/-- The literal full quadratic gauge generator has the accepted leading diagonal
shift with error at most 17R². Both coordinate series and both infinite arms remain. -/
theorem seamGaugeGenerator_leading_compression (a b : ℕ → ℂ)
    (ha : ∀ i, ‖a i‖ ≤ (1/4096 : ℝ)^2) (hb : ∀ i, ‖b i‖ ≤ (1/4096 : ℝ)^2) :
    ‖seamSchurH (seamGaugeGenerator
      (seamSineRow (1/64) (1/4096) a ((1/4096)^2) (by positivity) ha)
      (seamSineColumn (1/64) (1/4096) b ((1/4096)^2) (by positivity) hb))-
      seamLeadingCoefficient •seamBackwardShift‖ ≤ 17*(1/4096 : ℝ)^2 := by
  let A := seamLowerCoordinate (seamSineRow (1/64) (1/4096) a ((1/4096)^2) (by positivity) ha)
  let B := seamTranspose.comp ((seamLowerCoordinate (seamSineRow (1/64) (1/4096) b ((1/4096)^2) (by positivity) hb)).comp seamTranspose)
  let Y := seamLeadingLower (1/64) (1/4096) a ((1/4096)^2) (by positivity) ha
  let V := seamTranspose.comp ((seamLeadingLower (1/64) (1/4096) b ((1/4096)^2) (by positivity) hb).comp seamTranspose)
  let z : ℂ := -2*(Real.pi:ℂ)*Complex.I
  let Z := seamGaugeGenerator (seamSineRow (1/64) (1/4096) a ((1/4096)^2) (by positivity) ha)
    (seamSineColumn (1/64) (1/4096) b ((1/4096)^2) (by positivity) hb)
  have he : seamSchurH Z=seamSchurH (z •(A*B)) := by
    dsimp only [Z,seamGaugeGenerator]
    rw [seamSchurH_smul,seamCoordinateTensor_lower_compression]
    exact (seamSchurH_smul z (A*B)).symm
  have hz : ‖z‖ ≤ 8 := by
    dsimp only [z]
    simp only [norm_mul,norm_neg,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos Real.pi_pos,Complex.norm_I,mul_one]
    linarith [Real.pi_lt_four]
  have herr : ‖seamSchurH Z-seamSchurH (z •(Y*V))‖ ≤ 14*(1/4096 : ℝ)^2 := by
    rw [he,←seamSchurH_sub]
    have hx : z • (A*B) - z • (Y*V) = z • (A*B-Y*V) := by
      ext u p
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.mul_apply, lp.coeFn_sub, lp.coeFn_smul,
        Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_sub]
    rw [hx]
    apply (seamSchurH_norm_le _).trans
    rw [norm_smul]
    have ht : ‖A*B-Y*V‖ ≤ (5/3:ℝ)*(1/4096:ℝ)^2 := seamLowerTensor_constant_error a b ha hb
    exact (mul_le_mul hz ht (norm_nonneg _) (by norm_num)).trans (by norm_num)
  have hlead : ‖seamSchurH (z •(Y*V))-seamLeadingCoefficient •seamBackwardShift‖ ≤ (1/4096:ℝ)^2 :=
    seamLeadingTensor_gauge_error a b ha hb
  change ‖seamSchurH Z-seamLeadingCoefficient •seamBackwardShift‖ ≤ _
  exact (norm_sub_le_norm_sub_add_norm_sub _ (seamSchurH (z •(Y*V))) _).trans
    ((add_le_add herr hlead).trans (by norm_num))

end MeyerGeneralProblem.Adaptive
