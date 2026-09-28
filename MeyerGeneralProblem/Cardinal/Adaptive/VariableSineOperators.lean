module

public import MeyerGeneralProblem.Cardinal.Adaptive.VariableNewtonOperators
public import MeyerGeneralProblem.Cardinal.Adaptive.SeamSineOperator

@[expose] public section

/-! Full variable-weight sine multiplication on the genuine moment Hilbert space. -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section

/-- The complete upper parity block κ(2−J), using the genuine odd input. -/
def variableSineUpper (κ : ℂ) (ε : ℕ → ℝ) (ρ : ℝ) (hρ : ρ ≤ 1/2)
    (hε : ∀ i, 0 < ε i ∧ ε i ≤ ρ) :
    SeamMomentArray →L[ℂ] SeamMomentArray :=
  κ •(((2 : ℂ) •ContinuousLinearMap.id ℂ SeamMomentArray-variableNewtonRow ε ρ hρ hε).comp
    (seamRowFlip.comp (momentProjection (seamRowParity true))))
/-- The complete lower parity block J/κ, using the genuine even input. -/
def variableSineLower (κ : ℂ) (ε : ℕ → ℝ) (ρ : ℝ) (hρ : ρ ≤ 1/2)
    (hε : ∀ i, 0 < ε i ∧ ε i ≤ ρ) :
    SeamMomentArray →L[ℂ] SeamMomentArray :=
  κ⁻¹ •((variableNewtonRow ε ρ hρ hε).comp
    (seamRowFlip.comp (momentProjection (seamRowParity false))))
/-- The full physical sine operator, retaining all levels and both parity blocks. -/
def variableSineRow (κ : ℂ) (ε : ℕ → ℝ) (ρ : ℝ) (hρ : ρ ≤ 1/2)
    (hε : ∀ i, 0 < ε i ∧ ε i ≤ ρ) :
    SeamMomentArray →L[ℂ] SeamMomentArray := variableSineUpper κ ε ρ hρ hε+variableSineLower κ ε ρ hρ hε

@[simp] theorem variableSineUpper_apply (κ : ℂ) (ε : ℕ → ℝ) (ρ : ℝ) (hρ : ρ ≤ 1/2)
    (hε : ∀ i, 0 < ε i ∧ ε i ≤ ρ) (u : SeamMomentArray) (i j : ℕ) (e f : Bool) :
    variableSineUpper κ ε ρ hρ hε u ((i,e),(j,f))=
      if e then 0 else κ*(2*u ((i,true),(j,f))-((ε (i+1):ℂ)*u ((i+1,true),(j,f))+criticalNewtonNode (ε (i+1))*u ((i,true),(j,f)))) := by
  change κ*(2*(seamRowFlip (momentProjection (seamRowParity true) u)) ((i,e),(j,f))-
    variableNewtonRow ε ρ hρ hε (seamRowFlip (momentProjection (seamRowParity true) u)) ((i,e),(j,f)))=_
  cases e <;> simp [variableNewtonRow_apply,seamRowShift_apply,seamRowFlip_apply,momentProjection_apply,seamRowParity]

@[simp] theorem variableSineLower_apply (κ : ℂ) (ε : ℕ → ℝ) (ρ : ℝ) (hρ : ρ ≤ 1/2)
    (hε : ∀ i, 0 < ε i ∧ ε i ≤ ρ) (u : SeamMomentArray) (i j : ℕ) (e f : Bool) :
    variableSineLower κ ε ρ hρ hε u ((i,e),(j,f))=
      if e then κ⁻¹*((ε (i+1):ℂ)*u ((i+1,false),(j,f))+criticalNewtonNode (ε (i+1))*u ((i,false),(j,f))) else 0 := by
  change κ⁻¹*variableNewtonRow ε ρ hρ hε (seamRowFlip (momentProjection (seamRowParity false) u)) ((i,e),(j,f))=_
  cases e <;> simp [variableNewtonRow_apply,seamRowShift_apply,seamRowFlip_apply,momentProjection_apply,seamRowParity]

@[simp] theorem variableSineRow_apply (κ : ℂ) (ε : ℕ → ℝ) (ρ : ℝ) (hρ : ρ ≤ 1/2)
    (hε : ∀ i, 0 < ε i ∧ ε i ≤ ρ) (u : SeamMomentArray) (i j : ℕ) (e f : Bool) :
    variableSineRow κ ε ρ hρ hε u ((i,e),(j,f))=
      if e then κ⁻¹*((ε (i+1):ℂ)*u ((i+1,false),(j,f))+criticalNewtonNode (ε (i+1))*u ((i,false),(j,f)))
      else κ*(2*u ((i,true),(j,f))-((ε (i+1):ℂ)*u ((i+1,true),(j,f))+criticalNewtonNode (ε (i+1))*u ((i,true),(j,f)))) := by
  change variableSineUpper κ ε ρ hρ hε u ((i,e),(j,f))+variableSineLower κ ε ρ hρ hε u ((i,e),(j,f))=_
  cases e <;> simp only [variableSineUpper_apply,variableSineLower_apply,Bool.false_eq_true,ite_false,ite_true,add_zero,zero_add]

private theorem variableRowFlip_norm_apply (u : SeamMomentArray) : ‖seamRowFlip u‖ ≤ ‖u‖ :=
  (seamRowFlip.le_opNorm u).trans (by nlinarith [seamRowFlip_norm_le_one,norm_nonneg u])

/-- A whole operator bound derived from the true Hilbert parity partition;
 the two disjoint blocks are not charged twice. -/
theorem variableSineRow_norm_le (κ : ℂ) (ε : ℕ → ℝ) (ρ : ℝ) (hρ : ρ ≤ 1/2)
    (hε : ∀ i, 0 < ε i ∧ ε i ≤ ρ) (M : ℝ) (hM : 0 ≤ M)
    (hupper : ‖κ‖*(2+ρ*(1+32*ρ)) ≤ M) (hlower : ‖κ⁻¹‖*(ρ*(1+32*ρ)) ≤ M) :
    ‖variableSineRow κ ε ρ hρ hε‖ ≤ M := by
  have hρ0 : 0 ≤ ρ := (hε 0).1.le.trans (hε 0).2
  have hJ := variableNewtonRow_norm_le ε ρ hρ hε
  have hUp (u : SeamMomentArray) : ‖((2 : ℂ) •ContinuousLinearMap.id ℂ SeamMomentArray-variableNewtonRow ε ρ hρ hε) u‖ ≤
      (2+ρ*(1+32*ρ))*‖u‖ := by
    change ‖(2 : ℂ) •u-variableNewtonRow ε ρ hρ hε u‖ ≤ _
    calc
      _ ≤ ‖(2 : ℂ) •u‖+‖variableNewtonRow ε ρ hρ hε u‖ := norm_sub_le _ _
      _ ≤ (2+ρ*(1+32*ρ))*‖u‖ := by
        rw [norm_smul]
        norm_num only [Complex.norm_ofNat]
        have hj := (variableNewtonRow ε ρ hρ hε).le_opNorm u
        have hh := mul_le_mul_of_nonneg_right hJ (norm_nonneg u)
        nlinarith
  apply moment_partition_operator_bound (seamRowParity true) _ _ M hM
  · intro u
    change ‖κ •(((2 : ℂ) •ContinuousLinearMap.id ℂ SeamMomentArray-variableNewtonRow ε ρ hρ hε)
      (seamRowFlip (momentProjection (seamRowParity true) u)))‖ ≤ _
    rw [norm_smul]
    calc
      _ ≤ ‖κ‖*((2+ρ*(1+32*ρ))*‖seamRowFlip (momentProjection (seamRowParity true) u)‖) :=
        mul_le_mul_of_nonneg_left (hUp _) (norm_nonneg _)
      _ ≤ ‖κ‖*((2+ρ*(1+32*ρ))*‖momentProjection (seamRowParity true) u‖) := by
        gcongr
        exact variableRowFlip_norm_apply _
      _ ≤ _ := by nlinarith [norm_nonneg (momentProjection (seamRowParity true) u)]
  · intro u
    have hs : (seamRowParity true)ᶜ=seamRowParity false := by
      ext p
      simp [seamRowParity]
    rw [hs]
    change ‖κ⁻¹ •(variableNewtonRow ε ρ hρ hε (seamRowFlip (momentProjection (seamRowParity false) u)))‖ ≤ _
    rw [norm_smul]
    calc
      _ ≤ ‖κ⁻¹‖*(‖variableNewtonRow ε ρ hρ hε‖*‖seamRowFlip (momentProjection (seamRowParity false) u)‖) :=
        mul_le_mul_of_nonneg_left ((variableNewtonRow ε ρ hρ hε).le_opNorm _) (norm_nonneg _)
      _ ≤ ‖κ⁻¹‖*((ρ*(1+32*ρ))*‖momentProjection (seamRowParity false) u‖) := by
        gcongr
        exact variableRowFlip_norm_apply _
      _ ≤ _ := by nlinarith [norm_nonneg (momentProjection (seamRowParity false) u)]
  · rintro u ⟨⟨i,e⟩,j,f⟩
    cases e <;> simp only [variableSineUpper_apply,variableSineLower_apply,Bool.false_eq_true,ite_false,ite_true,or_true,true_or]

/-- The exact full sine square is J(2−J) on both parity sectors. -/
theorem variableSineRow_square (κ : ℂ) (hκ : κ ≠ 0) (ε : ℕ → ℝ) (ρ : ℝ) (hρ : ρ ≤ 1/2)
    (hε : ∀ i, 0 < ε i ∧ ε i ≤ ρ) :
    (variableSineRow κ ε ρ hρ hε).comp (variableSineRow κ ε ρ hρ hε)=
      (variableNewtonRow ε ρ hρ hε).comp
        ((2 : ℂ) •ContinuousLinearMap.id ℂ SeamMomentArray-variableNewtonRow ε ρ hρ hε) := by
  ext u p
  rcases p with ⟨⟨i,e⟩,j,f⟩
  simp only [ContinuousLinearMap.comp_apply,variableNewtonRow_apply,seamRowShift_apply,
    ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply,
    lp.coeFn_sub,lp.coeFn_smul,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
  cases e <;> simp only [variableSineRow_apply,Bool.false_eq_true,ite_false,ite_true] <;>
    field_simp [hκ] <;> ring


/-- The entire spectral sine operator obtained by exact axis exchange. -/
def variableSineColumn (κ : ℂ) (ε : ℕ → ℝ) (ρ : ℝ) (hρ : ρ ≤ 1/2)
    (hε : ∀ i, 0 < ε i ∧ ε i ≤ ρ) :
    SeamMomentArray →L[ℂ] SeamMomentArray :=
  seamTranspose.comp ((variableSineRow κ ε ρ hρ hε).comp seamTranspose)

@[simp] theorem variableSineColumn_apply (κ : ℂ) (ε : ℕ → ℝ) (ρ : ℝ) (hρ : ρ ≤ 1/2)
    (hε : ∀ i, 0 < ε i ∧ ε i ≤ ρ) (u : SeamMomentArray) (i j : ℕ) (e f : Bool) :
    variableSineColumn κ ε ρ hρ hε u ((i,e),(j,f))=
      if f then κ⁻¹*((ε (j+1):ℂ)*u ((i,e),(j+1,false))+criticalNewtonNode (ε (j+1))*u ((i,e),(j,false)))
      else κ*(2*u ((i,e),(j,true))-((ε (j+1):ℂ)*u ((i,e),(j+1,true))+criticalNewtonNode (ε (j+1))*u ((i,e),(j,true)))) := by
  change variableSineRow κ ε ρ hρ hε (seamTranspose u) ((j,f),(i,e))=_
  rw [variableSineRow_apply]
  rfl

theorem variableSineColumn_norm_le_row (κ : ℂ) (ε : ℕ → ℝ) (ρ : ℝ) (hρ : ρ ≤ 1/2)
    (hε : ∀ i, 0 < ε i ∧ ε i ≤ ρ) :
    ‖variableSineColumn κ ε ρ hρ hε‖ ≤ ‖variableSineRow κ ε ρ hρ hε‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro u
  change ‖seamTranspose (variableSineRow κ ε ρ hρ hε (seamTranspose u))‖ ≤ _
  calc
    _ ≤ ‖variableSineRow κ ε ρ hρ hε (seamTranspose u)‖ := seamTranspose_norm_apply _
    _ ≤ ‖variableSineRow κ ε ρ hρ hε‖*‖seamTranspose u‖ := (variableSineRow κ ε ρ hρ hε).le_opNorm _
    _ ≤ _ := mul_le_mul_of_nonneg_left (seamTranspose_norm_apply _) (norm_nonneg _)



/-- The physical variable-weight sine at the retained source parameters. -/
def variableSineSourceRow (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) :
    SeamMomentArray →L[ℂ] SeamMomentArray :=
  variableSineRow shrinkingNewtonSourceKappa (rapidDistance P R) (shrinkingNewtonSourceKappa^4)
    (by norm_num [shrinkingNewtonSourceKappa]) (variableNewton_source_phase_bound P R hP hR)

/-- The spectral variable-weight sine at the same retained source parameters. -/
def variableSineSourceColumn (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) :
    SeamMomentArray →L[ℂ] SeamMomentArray :=
  variableSineColumn shrinkingNewtonSourceKappa (rapidDistance P R) (shrinkingNewtonSourceKappa^4)
    (by norm_num [shrinkingNewtonSourceKappa]) (variableNewton_source_phase_bound P R hP hR)

/-- The genuine parity partition gives the full source sine norm at most 3 kappa. -/
theorem variableSineSourceRow_norm_le (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) :
    ‖variableSineSourceRow P R hP hR‖ ≤ 3*shrinkingNewtonSourceKappa := by
  apply variableSineRow_norm_le
  · norm_num [shrinkingNewtonSourceKappa]
  · norm_num [shrinkingNewtonSourceKappa]
  · norm_num [shrinkingNewtonSourceKappa]

/-- The spectral source sine obeys the same complete Hilbert-space bound. -/
theorem variableSineSourceColumn_norm_le (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) :
    ‖variableSineSourceColumn P R hP hR‖ ≤ 3*shrinkingNewtonSourceKappa :=
  (variableSineColumn_norm_le_row _ _ _ _ _).trans (variableSineSourceRow_norm_le P R hP hR)

/-- The complete small Newton kernel J(2−J) has norm at most five times
rho; this is the operator argument of the convergent inverse-sine series. -/
theorem variableNewtonRow_kernel_norm_le (ε : ℕ → ℝ) (ρ : ℝ)
    (hρ : ρ ≤ 1/2) (hsmall : ρ ≤ 1/32) (hε : ∀ i, 0 < ε i ∧ ε i ≤ ρ) :
    ‖(variableNewtonRow ε ρ hρ hε).comp
      ((2:ℂ) • ContinuousLinearMap.id ℂ SeamMomentArray-variableNewtonRow ε ρ hρ hε)‖ ≤ 5*ρ := by
  have hρ0 : 0 ≤ ρ := (hε 0).1.le.trans (hε 0).2
  have hJ := variableNewtonRow_norm_le_two_radius ε ρ hρ hsmall hε
  have hb (u : SeamMomentArray) : ‖variableNewtonRow ε ρ hρ hε u‖ ≤ 2*ρ*‖u‖ :=
    ((variableNewtonRow ε ρ hρ hε).le_opNorm u).trans
      (mul_le_mul_of_nonneg_right hJ (norm_nonneg _))
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  change ‖variableNewtonRow ε ρ hρ hε ((2:ℂ) • u-variableNewtonRow ε ρ hρ hε u)‖ ≤ _
  calc
    _ ≤ 2*ρ*‖(2:ℂ) • u-variableNewtonRow ε ρ hρ hε u‖ := hb _
    _ ≤ 2*ρ*(‖(2:ℂ) •u‖+‖variableNewtonRow ε ρ hρ hε u‖) := by
      gcongr; exact norm_sub_le _ _
    _ ≤ 2*ρ*(2*‖u‖+2*ρ*‖u‖) := by
      rw [norm_smul]; norm_num only [Complex.norm_ofNat]
      gcongr; exact hb u
    _ ≤ 5*ρ*‖u‖ := by
      have hh : 2*ρ*(2+2*ρ) ≤ 5*ρ := by nlinarith [mul_nonneg hρ0 (show 0 ≤ 1-4*ρ by linarith)]
      nlinarith [mul_le_mul_of_nonneg_right hh (norm_nonneg u)]

end
end MeyerGeneralProblem.Adaptive
