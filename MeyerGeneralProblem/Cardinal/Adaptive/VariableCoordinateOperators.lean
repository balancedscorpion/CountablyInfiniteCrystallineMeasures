module

public import MeyerGeneralProblem.Cardinal.Adaptive.VariableSineOperators
public import MeyerGeneralProblem.Cardinal.Adaptive.FullExponentialBounds
public import MeyerGeneralProblem.Cardinal.Adaptive.SeamCoordinateOperator

@[expose] public section

/-! Complete inverse-sine coordinate operators at the variable source weights. -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section

/-- The entire inverse-sine factor evaluated at the actual Newton kernel. -/
def variableCoordinateFactor (ε : ℕ → ℝ) (ρ : ℝ) (hρ : ρ ≤ 1/2)
    (hε : ∀ i, 0 < ε i ∧ ε i ≤ ρ) : SeamMomentArray →L[ℂ] SeamMomentArray :=
  boundedOperatorSeries (fun n => (scalarArcsineCoefficient n : ℂ))
    ((variableNewtonRow ε ρ hρ hε).comp
      ((2:ℂ) • ContinuousLinearMap.id ℂ SeamMomentArray-variableNewtonRow ε ρ hρ hε))

/-- The complete inverse-sine factor has norm at most two throughout the small-radius range. -/
theorem variableCoordinateFactor_norm_le (ε : ℕ → ℝ) (ρ : ℝ) (hρ : ρ ≤ 1/2)
    (hsmall : ρ ≤ 1/32) (hε : ∀ i, 0 < ε i ∧ ε i ≤ ρ) :
    ‖variableCoordinateFactor ε ρ hρ hε‖ ≤ 2 := by
  have hK := variableNewtonRow_kernel_norm_le ε ρ hρ hsmall hε
  have hc (n : ℕ) : ‖(scalarArcsineCoefficient n : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (scalarArcsineCoefficient_nonneg n)]
    exact scalarArcsineCoefficient_le_one n
  have hn := boundedOperatorSeries_norm_le _ hc _ (lt_of_le_of_lt hK (by linarith))
  refine hn.trans ?_
  rw [inv_eq_one_div]
  apply (div_le_iff₀ (by linarith : 0 < 1-‖(variableNewtonRow ε ρ hρ hε).comp
      ((2:ℂ) • ContinuousLinearMap.id ℂ SeamMomentArray-variableNewtonRow ε ρ hρ hε)‖)).2
  linarith

/-- Physical coordinate multiplication obtained from the entire inverse-sine series. -/
def variableCoordinateRow (κ : ℂ) (ε : ℕ → ℝ) (ρ : ℝ) (hρ : ρ ≤ 1/2)
    (hε : ∀ i, 0 < ε i ∧ ε i ≤ ρ) : SeamMomentArray →L[ℂ] SeamMomentArray :=
  ((2*(Real.pi:ℂ))⁻¹) • ((variableSineRow κ ε ρ hρ hε).comp
    (variableCoordinateFactor ε ρ hρ hε))

/-- The full physical coordinate operator at the retained variable source parameters. -/
def variableCoordinateSourceRow (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) :
    SeamMomentArray →L[ℂ] SeamMomentArray :=
  variableCoordinateRow shrinkingNewtonSourceKappa (rapidDistance P R) (shrinkingNewtonSourceKappa^4)
    (by norm_num [shrinkingNewtonSourceKappa]) (variableNewton_source_phase_bound P R hP hR)

/-- The complete coordinate norm retains the source's small parameter. -/
theorem variableCoordinateSourceRow_norm_le (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) :
    ‖variableCoordinateSourceRow P R hP hR‖ ≤ shrinkingNewtonSourceKappa := by
  have hF := variableCoordinateFactor_norm_le (rapidDistance P R) (shrinkingNewtonSourceKappa^4)
    (by norm_num [shrinkingNewtonSourceKappa]) (by norm_num [shrinkingNewtonSourceKappa])
    (variableNewton_source_phase_bound P R hP hR)
  have hS := variableSineSourceRow_norm_le P R hP hR
  unfold variableCoordinateSourceRow variableCoordinateRow
  rw [norm_smul]
  have he : ‖(2*(Real.pi:ℂ))⁻¹‖ = (2*Real.pi)⁻¹ := by
    rw [norm_inv,norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  rw [he]
  calc
    _ ≤ (2*Real.pi)⁻¹ * (3*shrinkingNewtonSourceKappa*2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul hS hF (norm_nonneg _) (by positivity [shrinkingNewtonSourceKappa_pos]))
    _ ≤ _ := by
      apply (inv_mul_le_iff₀ (by positivity : 0 < 2*Real.pi)).2
      have hp := Real.pi_gt_three
      nlinarith [shrinkingNewtonSourceKappa_pos]

/-- The spectral coordinate is exact conjugation by the full axis exchange. -/
def variableCoordinateSourceColumn (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) :
    SeamMomentArray →L[ℂ] SeamMomentArray :=
  seamTranspose.comp ((variableCoordinateSourceRow P R hP hR).comp seamTranspose)

/-- The spectral coordinate has the same source norm. -/
theorem variableCoordinateSourceColumn_norm_le (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) :
    ‖variableCoordinateSourceColumn P R hP hR‖ ≤ shrinkingNewtonSourceKappa := by
  apply le_trans (ContinuousLinearMap.opNorm_comp_le _ _)
  calc
    _ ≤ 1 * (‖variableCoordinateSourceRow P R hP hR‖ * 1) := by
      apply mul_le_mul seamTranspose_norm_le_one _ (norm_nonneg _) zero_le_one
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left seamTranspose_norm_le_one (norm_nonneg _))
    _ ≤ _ := by simpa using variableCoordinateSourceRow_norm_le P R hP hR

/-- The complete quadratic gauge generator, at the actual two rapid phase scales. -/
def variableGaugeGenerator (P R Q S : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R)
    (hQ : 1 ≤ Q) (hS : 1 ≤ S) : SeamMomentArray →L[ℂ] SeamMomentArray :=
  (-2*(Real.pi:ℂ)*Complex.I) • ((variableCoordinateSourceRow P R hP hR).comp
    (variableCoordinateSourceColumn Q S hQ hS))

/-- The actual gauge retains every power of the genuine bounded generator. -/
def variableGaugeOperator (P R Q S : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R)
    (hQ : 1 ≤ Q) (hS : 1 ≤ S) : SeamMomentArray →L[ℂ] SeamMomentArray :=
  NormedSpace.exp (variableGaugeGenerator P R Q S hP hR hQ hS)

theorem variableGaugeGenerator_norm_le (P R Q S : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R)
    (hQ : 1 ≤ Q) (hS : 1 ≤ S) :
    ‖variableGaugeGenerator P R Q S hP hR hQ hS‖ ≤ 8*shrinkingNewtonSourceKappa^2 := by
  have hp : ‖-2*(Real.pi:ℂ)*Complex.I‖ ≤ 8 := by
    simp only [norm_mul,norm_neg,Complex.norm_ofNat,Complex.norm_real,
      Real.norm_eq_abs,abs_of_pos Real.pi_pos,Complex.norm_I,mul_one]
    linarith [Real.pi_lt_four]
  rw [variableGaugeGenerator,norm_smul]
  calc
    _ ≤ 8 * (shrinkingNewtonSourceKappa*shrinkingNewtonSourceKappa) := by
      apply mul_le_mul hp _ (norm_nonneg _) (by norm_num)
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul (variableCoordinateSourceRow_norm_le P R hP hR)
          (variableCoordinateSourceColumn_norm_le Q S hQ hS) (norm_nonneg _) shrinkingNewtonSourceKappa_pos.le)
    _ = _ := by ring

/-- The complete gauge differs from identity by at most nine times sqrt(rho). -/
theorem variableGaugeOperator_close (P R Q S : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R)
    (hQ : 1 ≤ Q) (hS : 1 ≤ S) :
    ‖variableGaugeOperator P R Q S hP hR hQ hS-1‖ ≤ 9*shrinkingNewtonSourceKappa^2 := by
  have hn := variableGaugeGenerator_norm_le P R Q S hP hR hQ hS
  have hs : ‖variableGaugeGenerator P R Q S hP hR hQ hS‖ < 1 := by
    have hh : 8*shrinkingNewtonSourceKappa^2 < 1 := by norm_num [shrinkingNewtonSourceKappa]
    exact hn.trans_lt hh
  apply (fullExponential_sub_one_bound _ hs).trans
  apply (div_le_iff₀ (sub_pos.mpr hs)).2
  norm_num [shrinkingNewtonSourceKappa] at hn ⊢
  linarith

/-- Bounded core of the lower coordinate block, before its actual next-level weight. -/
def variableCoordinateLowerCore (ε : ℕ → ℝ) (ρ : ℝ) (hρ : ρ ≤ 1/2)
    (hε : ∀ i, 0 < ε i ∧ ε i ≤ ρ) : SeamMomentArray →L[ℂ] SeamMomentArray :=
  (2*(Real.pi:ℂ))⁻¹ • ((variableNewtonRowCore ε ρ hρ hε).comp
    ((seamRowFlip.comp (momentProjection (seamRowParity false))).comp
      (variableCoordinateFactor ε ρ hρ hε)))

/-- The lower coordinate contribution factors through the actual phase diagonal.
The remaining core is a genuine bounded operator on the full Hilbert space. -/
theorem variableCoordinate_lower_factor (κ : ℂ) (ε : ℕ → ℝ) (ρ : ℝ) (hρ : ρ ≤ 1/2)
    (hε : ∀ i, 0 < ε i ∧ ε i ≤ ρ) :
    (2*(Real.pi:ℂ))⁻¹ • ((variableSineLower κ ε ρ hρ hε).comp
      (variableCoordinateFactor ε ρ hρ hε)) =
    κ⁻¹ • ((variableNewtonRowWeight ε ρ hε).comp (variableCoordinateLowerCore ε ρ hρ hε)) := by
  ext u p
  simp only [variableSineLower,variableNewtonRow,variableCoordinateLowerCore,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.smul_apply,map_smul,lp.coeFn_smul,
    Pi.smul_apply,smul_eq_mul]
  ring

/-- The lower coordinate core is contractive, independently of the small weights. -/
theorem variableCoordinateLowerCore_norm_le (ε : ℕ → ℝ) (ρ : ℝ) (hρ : ρ ≤ 1/2)
    (hsmall : ρ ≤ 1/32) (hε : ∀ i, 0 < ε i ∧ ε i ≤ ρ) :
    ‖variableCoordinateLowerCore ε ρ hρ hε‖ ≤ 1 := by
  have hB : ‖variableNewtonRowCore ε ρ hρ hε‖ ≤ 2 :=
    (variableNewtonRowCore_norm_le ε ρ hρ hε).trans (by linarith)
  have hF := variableCoordinateFactor_norm_le ε ρ hρ hsmall hε
  have hflip : ‖seamRowFlip.comp (momentProjection (seamRowParity false))‖ ≤ 1 := by
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (by nlinarith [seamRowFlip_norm_le_one,momentProjection_norm_le_one (seamRowParity false),
        norm_nonneg seamRowFlip,norm_nonneg (momentProjection (seamRowParity false))])
  have hin : ‖(seamRowFlip.comp (momentProjection (seamRowParity false))).comp
      (variableCoordinateFactor ε ρ hρ hε)‖ ≤ 2 :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans (by nlinarith [norm_nonneg (variableCoordinateFactor ε ρ hρ hε)])
  have hp : ‖(2*(Real.pi:ℂ))⁻¹‖ ≤ 1/6 := by
    rw [norm_inv,norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
    rw [one_div]
    exact inv_anti₀ (by norm_num) (by nlinarith [Real.pi_gt_three])
  rw [variableCoordinateLowerCore,norm_smul]
  calc
    _ ≤ (1/6:ℝ)*(2*2) := mul_le_mul hp
      ((ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul hB hin (norm_nonneg _) (by norm_num)))
      (norm_nonneg _) (by norm_num)
    _ ≤ 1 := by norm_num

/-- The complete series commutes with the actual sine operator, because its
argument is exactly that operator's square. -/
theorem variableCoordinateFactor_commute (κ : ℂ) (hκ : κ ≠ 0) (ε : ℕ → ℝ) (ρ : ℝ)
    (hρ : ρ ≤ 1/2) (hε : ∀ i, 0 < ε i ∧ ε i ≤ ρ) :
    Commute (variableSineRow κ ε ρ hρ hε) (variableCoordinateFactor ε ρ hρ hε) := by
  unfold variableCoordinateFactor boundedOperatorSeries
  apply Commute.tsum_right
  intro n
  apply Commute.smul_right
  apply Commute.pow_right
  rw [← variableSineRow_square κ hκ]
  change Commute (variableSineRow κ ε ρ hρ hε)
    ((variableSineRow κ ε ρ hρ hε)*(variableSineRow κ ε ρ hρ hε))
  exact (Commute.refl (variableSineRow κ ε ρ hρ hε)).mul_right
    (Commute.refl (variableSineRow κ ε ρ hρ hε))

/-- Bounded square core, retaining the phase diagonal before every even power. -/
def variableCoordinateSquareCore (ε : ℕ → ℝ) (ρ : ℝ) (hρ : ρ ≤ 1/2)
    (hε : ∀ i, 0 < ε i ∧ ε i ≤ ρ) : SeamMomentArray →L[ℂ] SeamMomentArray :=
  ((2*(Real.pi:ℂ))⁻¹)^2 • ((variableNewtonRowCore ε ρ hρ hε) *
    ((2:ℂ) • ContinuousLinearMap.id ℂ SeamMomentArray-variableNewtonRow ε ρ hρ hε) *
    (variableCoordinateFactor ε ρ hρ hε)^2)

/-- Exact factorization of the full coordinate square by the actual next-level
phase diagonal; the right-hand side never contains an inverse diagonal. -/
theorem variableCoordinate_square_factor (κ : ℂ) (hκ : κ ≠ 0) (ε : ℕ → ℝ) (ρ : ℝ)
    (hρ : ρ ≤ 1/2) (hε : ∀ i, 0 < ε i ∧ ε i ≤ ρ) :
    (variableCoordinateRow κ ε ρ hρ hε)^2 =
    (variableNewtonRowWeight ε ρ hε) * (variableCoordinateSquareCore ε ρ hρ hε) := by
  have hc := variableCoordinateFactor_commute κ hκ ε ρ hρ hε
  have hs : variableSineRow κ ε ρ hρ hε * variableSineRow κ ε ρ hρ hε =
      variableNewtonRow ε ρ hρ hε *
        ((2:ℂ) • ContinuousLinearMap.id ℂ SeamMomentArray-variableNewtonRow ε ρ hρ hε) :=
    variableSineRow_square κ hκ ε ρ hρ hε
  unfold variableCoordinateRow variableCoordinateSquareCore
  change (((2*(Real.pi:ℂ))⁻¹) • (variableSineRow κ ε ρ hρ hε *
    variableCoordinateFactor ε ρ hρ hε))^2 = _
  rw [smul_pow, hc.mul_pow, pow_two (variableSineRow κ ε ρ hρ hε), hs]
  simp only [variableNewtonRow, mul_smul_comm, mul_assoc]
  rfl

/-- The complete square core is contractive on the original full array Hilbert space. -/
theorem variableCoordinateSquareCore_norm_le (ε : ℕ → ℝ) (ρ : ℝ) (hρ : ρ ≤ 1/2)
    (hsmall : ρ ≤ 1/32) (hε : ∀ i, 0 < ε i ∧ ε i ≤ ρ) :
    ‖variableCoordinateSquareCore ε ρ hρ hε‖ ≤ 1 := by
  have hB : ‖variableNewtonRowCore ε ρ hρ hε‖ ≤ 2 :=
    (variableNewtonRowCore_norm_le ε ρ hρ hε).trans (by linarith)
  have hJ := variableNewtonRow_norm_le_two_radius ε ρ hρ hsmall hε
  have hA : ‖(2:ℂ) • ContinuousLinearMap.id ℂ SeamMomentArray-variableNewtonRow ε ρ hρ hε‖ ≤ 3 := by
    apply (norm_sub_le _ _).trans
    rw [norm_smul,Complex.norm_ofNat,ContinuousLinearMap.norm_id]
    linarith
  have hF := variableCoordinateFactor_norm_le ε ρ hρ hsmall hε
  have hp : ‖(2*(Real.pi:ℂ))⁻¹‖ ≤ 1/6 := by
    rw [norm_inv,norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos,one_div]
    exact inv_anti₀ (by norm_num) (by nlinarith [Real.pi_gt_three])
  rw [variableCoordinateSquareCore,norm_smul,norm_pow]
  calc
    _ ≤ (1/6:ℝ)^2 * ((2*3)*2^2) := by
      apply mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hp 2) _ (norm_nonneg _) (by positivity)
      apply (norm_mul_le _ _).trans
      apply mul_le_mul ((norm_mul_le _ _).trans (mul_le_mul hB hA (norm_nonneg _) (by norm_num)))
        ((norm_pow_le _ 2).trans (pow_le_pow_left₀ (norm_nonneg _) hF 2)) (norm_nonneg _) (by norm_num)
    _ ≤ 1 := by norm_num

/-- Every coefficient and every operator power occurs in the native norm limit. -/
theorem variableCoordinateFactor_hasSum (ε : ℕ → ℝ) (ρ : ℝ) (hρ : ρ ≤ 1/2)
    (hsmall : ρ ≤ 1/32) (hε : ∀ i, 0 < ε i ∧ ε i ≤ ρ) :
    HasSum (fun n => (scalarArcsineCoefficient n : ℂ) •
      ((variableNewtonRow ε ρ hρ hε).comp
        ((2:ℂ) • ContinuousLinearMap.id ℂ SeamMomentArray-variableNewtonRow ε ρ hρ hε))^n)
      (variableCoordinateFactor ε ρ hρ hε) := by
  apply boundedOperatorSeries_hasSum _ scalarArcsineCoefficient_cast_norm
  exact (variableNewtonRow_kernel_norm_le ε ρ hρ hsmall hε).trans_lt (by linarith)

/-- The full physical coordinate square obeys the stronger rho bound. -/
theorem variableCoordinateSourceRow_square_norm_le (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) :
    ‖(variableCoordinateSourceRow P R hP hR)^2‖ ≤ shrinkingNewtonSourceKappa^4 := by
  unfold variableCoordinateSourceRow
  rw [variableCoordinate_square_factor _ (by norm_num [shrinkingNewtonSourceKappa])]
  apply (norm_mul_le _ _).trans
  have hw := variableNewtonRowWeight_norm_le (rapidDistance P R) (shrinkingNewtonSourceKappa^4)
    (variableNewton_source_phase_bound P R hP hR)
  have hc := variableCoordinateSquareCore_norm_le (rapidDistance P R) (shrinkingNewtonSourceKappa^4)
    (by norm_num [shrinkingNewtonSourceKappa]) (by norm_num [shrinkingNewtonSourceKappa])
    (variableNewton_source_phase_bound P R hP hR)
  exact (mul_le_mul hw hc (norm_nonneg _) (by positivity)).trans (by simp)

end
end MeyerGeneralProblem.Adaptive
