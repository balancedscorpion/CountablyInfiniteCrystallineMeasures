module

public import MeyerGeneralProblem.Cardinal.Adaptive.SeamNewtonOperators
public import MeyerGeneralProblem.Cardinal.Adaptive.HalfNewtonGaugeMembership

@[expose] public section

/-! Actual variable-weight Newton operators on the complete square-summable array. -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open scoped FourierTransform

/-- The actual Newton node is quadratically small in its positive phase distance. -/
theorem variableNewtonNode_norm_bound (t : ℝ) (ht : 0 ≤ t) (hh : t ≤ 1/2) :
    ‖criticalNewtonNode t‖ ≤ 32*t^2 := by
  have h := shrinkingNewton_cos_factor_le t 0 ht hh (by simpa using ht)
  simpa only [criticalNewtonNode,mul_zero,Real.cos_zero,Complex.norm_real,
    Real.norm_eq_abs,abs_sub_comm] using h

/-- Dividing the node by its own positive phase remains bounded; this is a
bounded diagonal coefficient, not a stand-alone inverse diagonal operator. -/
theorem variableNewtonNode_ratio_bound (t : ℝ) (ht : 0 < t) (hh : t ≤ 1/2) :
    ‖criticalNewtonNode t/(t:ℂ)‖ ≤ 32*t := by
  rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ht]
  apply (div_le_iff₀ ht).mpr
  have h := variableNewtonNode_norm_bound t ht.le hh
  nlinarith


/-- Actual next-level phase multiplication in the row coordinate. -/
def variableNewtonRowWeight (ε : ℕ → ℝ) (ρ : ℝ)
    (hε : ∀ i, 0 < ε i ∧ ε i ≤ ρ) : SeamMomentArray →L[ℂ] SeamMomentArray :=
  momentDiagonal (fun p : SeamMomentIndex => (ε (p.1.1+1):ℂ)) ρ ((hε 0).1.le.trans (hε 0).2)
    (fun p => by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (hε _).1]; exact (hε _).2)

/-- The bounded core of the full variable-weight row Newton operator. -/
def variableNewtonRowCore (ε : ℕ → ℝ) (ρ : ℝ)
    (hρ : ρ ≤ 1/2) (hε : ∀ i, 0 < ε i ∧ ε i ≤ ρ) : SeamMomentArray →L[ℂ] SeamMomentArray :=
  seamRowShift+momentDiagonal
    (fun p : SeamMomentIndex => criticalNewtonNode (ε (p.1.1+1))/(ε (p.1.1+1):ℂ))
    (32*ρ) (mul_nonneg (by norm_num) ((hε 0).1.le.trans (hε 0).2))
    (fun p : SeamMomentIndex => (variableNewtonNode_ratio_bound (ε (p.1.1+1))
      (hε (p.1.1+1)).1 ((hε (p.1.1+1)).2.trans hρ)).trans
      (mul_le_mul_of_nonneg_left (hε (p.1.1+1)).2 (by norm_num)))

/-- The full actual variable-weight row Newton operator, with its bounded row factor retained. -/
def variableNewtonRow (ε : ℕ → ℝ) (ρ : ℝ)
    (hρ : ρ ≤ 1/2) (hε : ∀ i, 0 < ε i ∧ ε i ≤ ρ) : SeamMomentArray →L[ℂ] SeamMomentArray :=
  (variableNewtonRowWeight ε ρ hε).comp (variableNewtonRowCore ε ρ hρ hε)

@[simp] theorem variableNewtonRowWeight_apply (ε : ℕ → ℝ) (ρ : ℝ)
    (hε : ∀ i, 0 < ε i ∧ ε i ≤ ρ) (u : SeamMomentArray) (p : SeamMomentIndex) :
    variableNewtonRowWeight ε ρ hε u p=(ε (p.1.1+1):ℂ)*u p := rfl

@[simp] theorem variableNewtonRowCore_apply (ε : ℕ → ℝ) (ρ : ℝ)
    (hρ : ρ ≤ 1/2) (hε : ∀ i, 0 < ε i ∧ ε i ≤ ρ) (u : SeamMomentArray) (p : SeamMomentIndex) :
    variableNewtonRowCore ε ρ hρ hε u p=seamRowShift u p+
      (criticalNewtonNode (ε (p.1.1+1))/(ε (p.1.1+1):ℂ))*u p := rfl

/-- The exact coordinate law uses epsilon at level i+1, including the first row. -/
theorem variableNewtonRow_apply (ε : ℕ → ℝ) (ρ : ℝ)
    (hρ : ρ ≤ 1/2) (hε : ∀ i, 0 < ε i ∧ ε i ≤ ρ) (u : SeamMomentArray) (p : SeamMomentIndex) :
    variableNewtonRow ε ρ hρ hε u p=(ε (p.1.1+1):ℂ)*seamRowShift u p+
      criticalNewtonNode (ε (p.1.1+1))*u p := by
  change (ε (p.1.1+1):ℂ)*(seamRowShift u p+
    (criticalNewtonNode (ε (p.1.1+1))/(ε (p.1.1+1):ℂ))*u p)=_
  have hne : (ε (p.1.1+1):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (hε _).1)
  field_simp

/-- The full bounded core is a small perturbation of the actual backward shift. -/
theorem variableNewtonRowCore_norm_le (ε : ℕ → ℝ) (ρ : ℝ)
    (hρ : ρ ≤ 1/2) (hε : ∀ i, 0 < ε i ∧ ε i ≤ ρ) :
    ‖variableNewtonRowCore ε ρ hρ hε‖ ≤ 1+32*ρ :=
  (norm_add_le _ _).trans (add_le_add seamRowShift_norm_le_one (momentDiagonal_norm_le _ _ _ _))

/-- Its genuine diagonal factor has the original phase upper bound. -/
theorem variableNewtonRowWeight_norm_le (ε : ℕ → ℝ) (ρ : ℝ)
    (hε : ∀ i, 0 < ε i ∧ ε i ≤ ρ) : ‖variableNewtonRowWeight ε ρ hε‖ ≤ ρ :=
  momentDiagonal_norm_le _ _ _ _

/-- The norm estimate keeps the complete factorization and no inverse phase diagonal. -/
theorem variableNewtonRow_norm_le (ε : ℕ → ℝ) (ρ : ℝ)
    (hρ : ρ ≤ 1/2) (hε : ∀ i, 0 < ε i ∧ ε i ≤ ρ) :
    ‖variableNewtonRow ε ρ hρ hε‖ ≤ ρ*(1+32*ρ) :=
  (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul (variableNewtonRowWeight_norm_le ε ρ hε)
      (variableNewtonRowCore_norm_le ε ρ hρ hε) (norm_nonneg _) ((hε 0).1.le.trans (hε 0).2))


/-- Actual next-level phase multiplication in the column coordinate. -/
def variableNewtonColumnWeight (ε : ℕ → ℝ) (ρ : ℝ)
    (hε : ∀ i, 0 < ε i ∧ ε i ≤ ρ) : SeamMomentArray →L[ℂ] SeamMomentArray :=
  momentDiagonal (fun p : SeamMomentIndex => (ε (p.2.1+1):ℂ)) ρ ((hε 0).1.le.trans (hε 0).2)
    (fun p => by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (hε _).1]; exact (hε _).2)

/-- The bounded core of the full variable-weight column Newton operator. -/
def variableNewtonColumnCore (ε : ℕ → ℝ) (ρ : ℝ)
    (hρ : ρ ≤ 1/2) (hε : ∀ i, 0 < ε i ∧ ε i ≤ ρ) : SeamMomentArray →L[ℂ] SeamMomentArray :=
  seamColumnShift+momentDiagonal
    (fun p : SeamMomentIndex => criticalNewtonNode (ε (p.2.1+1))/(ε (p.2.1+1):ℂ))
    (32*ρ) (mul_nonneg (by norm_num) ((hε 0).1.le.trans (hε 0).2))
    (fun p : SeamMomentIndex => (variableNewtonNode_ratio_bound (ε (p.2.1+1))
      (hε (p.2.1+1)).1 ((hε (p.2.1+1)).2.trans hρ)).trans
      (mul_le_mul_of_nonneg_left (hε (p.2.1+1)).2 (by norm_num)))

/-- The full actual variable-weight column Newton operator, with its bounded row factor retained. -/
def variableNewtonColumn (ε : ℕ → ℝ) (ρ : ℝ)
    (hρ : ρ ≤ 1/2) (hε : ∀ i, 0 < ε i ∧ ε i ≤ ρ) : SeamMomentArray →L[ℂ] SeamMomentArray :=
  (variableNewtonColumnWeight ε ρ hε).comp (variableNewtonColumnCore ε ρ hρ hε)

@[simp] theorem variableNewtonColumnWeight_apply (ε : ℕ → ℝ) (ρ : ℝ)
    (hε : ∀ i, 0 < ε i ∧ ε i ≤ ρ) (u : SeamMomentArray) (p : SeamMomentIndex) :
    variableNewtonColumnWeight ε ρ hε u p=(ε (p.2.1+1):ℂ)*u p := rfl

@[simp] theorem variableNewtonColumnCore_apply (ε : ℕ → ℝ) (ρ : ℝ)
    (hρ : ρ ≤ 1/2) (hε : ∀ i, 0 < ε i ∧ ε i ≤ ρ) (u : SeamMomentArray) (p : SeamMomentIndex) :
    variableNewtonColumnCore ε ρ hρ hε u p=seamColumnShift u p+
      (criticalNewtonNode (ε (p.2.1+1))/(ε (p.2.1+1):ℂ))*u p := rfl

/-- The exact coordinate law uses epsilon at level i+1, including the first row. -/
theorem variableNewtonColumn_apply (ε : ℕ → ℝ) (ρ : ℝ)
    (hρ : ρ ≤ 1/2) (hε : ∀ i, 0 < ε i ∧ ε i ≤ ρ) (u : SeamMomentArray) (p : SeamMomentIndex) :
    variableNewtonColumn ε ρ hρ hε u p=(ε (p.2.1+1):ℂ)*seamColumnShift u p+
      criticalNewtonNode (ε (p.2.1+1))*u p := by
  change (ε (p.2.1+1):ℂ)*(seamColumnShift u p+
    (criticalNewtonNode (ε (p.2.1+1))/(ε (p.2.1+1):ℂ))*u p)=_
  have hne : (ε (p.2.1+1):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (hε _).1)
  field_simp

/-- The full bounded core is a small perturbation of the actual backward shift. -/
theorem variableNewtonColumnCore_norm_le (ε : ℕ → ℝ) (ρ : ℝ)
    (hρ : ρ ≤ 1/2) (hε : ∀ i, 0 < ε i ∧ ε i ≤ ρ) :
    ‖variableNewtonColumnCore ε ρ hρ hε‖ ≤ 1+32*ρ :=
  (norm_add_le _ _).trans (add_le_add seamColumnShift_norm_le_one (momentDiagonal_norm_le _ _ _ _))

/-- Its genuine diagonal factor has the original phase upper bound. -/
theorem variableNewtonColumnWeight_norm_le (ε : ℕ → ℝ) (ρ : ℝ)
    (hε : ∀ i, 0 < ε i ∧ ε i ≤ ρ) : ‖variableNewtonColumnWeight ε ρ hε‖ ≤ ρ :=
  momentDiagonal_norm_le _ _ _ _

/-- The norm estimate keeps the complete factorization and no inverse phase diagonal. -/
theorem variableNewtonColumn_norm_le (ε : ℕ → ℝ) (ρ : ℝ)
    (hρ : ρ ≤ 1/2) (hε : ∀ i, 0 < ε i ∧ ε i ≤ ρ) :
    ‖variableNewtonColumn ε ρ hρ hε‖ ≤ ρ*(1+32*ρ) :=
  (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul (variableNewtonColumnWeight_norm_le ε ρ hε)
      (variableNewtonColumnCore_norm_le ε ρ hρ hε) (norm_nonneg _) ((hε 0).1.le.trans (hε 0).2))


/-- The two actual variable-weight Newton multiplications commute on the whole
array because they act in independent row and column coordinates. -/
theorem variableNewton_row_column_commute (ε δ : ℕ → ℝ) (ρ σ : ℝ)
    (hρ : ρ ≤ 1/2) (hσ : σ ≤ 1/2)
    (hε : ∀ i, 0 < ε i ∧ ε i ≤ ρ) (hδ : ∀ i, 0 < δ i ∧ δ i ≤ σ) :
    (variableNewtonRow ε ρ hρ hε).comp (variableNewtonColumn δ σ hσ hδ)=
      (variableNewtonColumn δ σ hσ hδ).comp (variableNewtonRow ε ρ hρ hε) := by
  ext u p
  simp only [ContinuousLinearMap.comp_apply,variableNewtonRow_apply,variableNewtonColumn_apply,
    seamRowShift_apply,seamColumnShift_apply]
  ring

/-- Compression of the complete product has the corrected next-level numerator
in its backward shift, retaining the full remaining diagonal term. -/
theorem variableNewton_diagonal_compression (ε δ : ℕ → ℝ) (ρ σ : ℝ)
    (hρ : ρ ≤ 1/2) (hσ : σ ≤ 1/2)
    (hε : ∀ i, 0 < ε i ∧ ε i ≤ ρ) (hδ : ∀ i, 0 < δ i ∧ δ i ≤ σ)
    (e f : Bool) (u : SeamSequence) (n : ℕ) :
    seamDiagonalReading e f (variableNewtonRow ε ρ hρ hε
      (variableNewtonColumn δ σ hσ hδ (seamDiagonalEmbedding e f u))) n=
      (ε (n+1):ℂ)*(δ (n+1):ℂ)*u (n+1)+
        criticalNewtonNode (ε (n+1))*criticalNewtonNode (δ (n+1))*u n := by
  simp only [seamDiagonalReading_apply,variableNewtonRow_apply,variableNewtonColumn_apply,
    seamRowShift_apply,seamColumnShift_apply,seamDiagonalEmbedding_apply]
  simp only [and_self,ite_true,Nat.add_eq_left,one_ne_zero,false_and,ite_false,mul_zero,add_zero]
  have hn : ¬n=n+1 := by omega
  simp only [hn,false_and,ite_false,mul_zero,zero_add]
  ring

/-- The actual rapid tail meets the source's precise radius rho=10^-12,
including the zeroth entry and hence every next-level weight. -/
theorem variableNewton_source_phase_bound (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) (i : ℕ) :
    0 < rapidDistance P R i ∧ rapidDistance P R i ≤ shrinkingNewtonSourceKappa^4 := by
  constructor
  · unfold rapidDistance; positivity
  · rw [shrinkingNewtonSourceKappa_fourth]
    exact (rapidDistance_le_small_constant hP hR i).trans (by norm_num)


/-- The actual variable-weight row Newton multiplier is at most twice
its radius on the small source parameter range. -/
theorem variableNewtonRow_norm_le_two_radius (ε : ℕ → ℝ) (ρ : ℝ)
    (hρ : ρ ≤ 1/2) (hsmall : ρ ≤ 1/32) (hε : ∀ i, 0 < ε i ∧ ε i ≤ ρ) :
    ‖variableNewtonRow ε ρ hρ hε‖ ≤ 2*ρ := by
  have hp : 0 ≤ ρ := (hε 0).1.le.trans (hε 0).2
  apply (variableNewtonRow_norm_le ε ρ hρ hε).trans
  nlinarith [mul_nonneg hp (show 0 ≤ 1-32*ρ by linarith)]

/-- The concrete original rapid tail's complete variable-weight row operator. -/
def variableNewtonSourceRow (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) :
    SeamMomentArray →L[ℂ] SeamMomentArray :=
  variableNewtonRow (rapidDistance P R) (shrinkingNewtonSourceKappa^4)
    (by norm_num [shrinkingNewtonSourceKappa]) (variableNewton_source_phase_bound P R hP hR)

/-- The original rapid tail operator satisfies the precise source-scale bound. -/
theorem variableNewtonSourceRow_norm_le (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) :
    ‖variableNewtonSourceRow P R hP hR‖ ≤ 2*shrinkingNewtonSourceKappa^4 :=
  variableNewtonRow_norm_le_two_radius _ _ _ (by norm_num [shrinkingNewtonSourceKappa]) _


/-- The actual variable-weight column Newton multiplier is at most twice
its radius on the small source parameter range. -/
theorem variableNewtonColumn_norm_le_two_radius (ε : ℕ → ℝ) (ρ : ℝ)
    (hρ : ρ ≤ 1/2) (hsmall : ρ ≤ 1/32) (hε : ∀ i, 0 < ε i ∧ ε i ≤ ρ) :
    ‖variableNewtonColumn ε ρ hρ hε‖ ≤ 2*ρ := by
  have hp : 0 ≤ ρ := (hε 0).1.le.trans (hε 0).2
  apply (variableNewtonColumn_norm_le ε ρ hρ hε).trans
  nlinarith [mul_nonneg hp (show 0 ≤ 1-32*ρ by linarith)]

/-- The concrete original rapid tail's complete variable-weight column operator. -/
def variableNewtonSourceColumn (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) :
    SeamMomentArray →L[ℂ] SeamMomentArray :=
  variableNewtonColumn (rapidDistance P R) (shrinkingNewtonSourceKappa^4)
    (by norm_num [shrinkingNewtonSourceKappa]) (variableNewton_source_phase_bound P R hP hR)

/-- The original rapid tail operator satisfies the precise source-scale bound. -/
theorem variableNewtonSourceColumn_norm_le (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) :
    ‖variableNewtonSourceColumn P R hP hR‖ ≤ 2*shrinkingNewtonSourceKappa^4 :=
  variableNewtonColumn_norm_le_two_radius _ _ _ (by norm_num [shrinkingNewtonSourceKappa]) _


/-- The actual rapid-source variable-weight matrix as a genuine complete lp vector. -/
def sourceShrinkingNewtonArray (P R p : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) (hp : p ≤ P)
    (T : HermiteScale (-(p:ℤ)))
    (hT : AtomicOnCarrier ((criticalPhaseTailCarrier (shrinkingRapidPhase P R)
      (shrinkingRapidPhase_mem P R hP hR) 0 0).translate (-1/2)) (hermiteScaleDistribution p T))
    (hFT : AtomicOnCarrier ((criticalPhaseTailCarrier (shrinkingRapidPhase P R)
      (shrinkingRapidPhase_mem P R hP hR) 0 0).translate (-1/2)) (𝓕 (hermiteScaleDistribution p T))) :
    SeamMomentArray :=
  ⟨fun z => shrinkingNewtonMomentWithScale shrinkingNewtonSourceKappa
      (rapidDistance P R) (rapidDistance P R) (hermiteScaleDistribution p T) z.1.1 z.1.2 z.2.1 z.2.2,
    memℓp_gen (by simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
      summable_sq_sourceNewtonMatrix_actual P R p hP hR hp T hT hFT)⟩

/-- Every entry is the exact whole-source normalized reading, including both infinite arms. -/
theorem sourceShrinkingNewtonArray_apply (P R p : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) (hp : p ≤ P)
    (T : HermiteScale (-(p:ℤ)))
    (hT : AtomicOnCarrier ((criticalPhaseTailCarrier (shrinkingRapidPhase P R)
      (shrinkingRapidPhase_mem P R hP hR) 0 0).translate (-1/2)) (hermiteScaleDistribution p T))
    (hFT : AtomicOnCarrier ((criticalPhaseTailCarrier (shrinkingRapidPhase P R)
      (shrinkingRapidPhase_mem P R hP hR) 0 0).translate (-1/2)) (𝓕 (hermiteScaleDistribution p T)))
    (z : SeamMomentIndex) : sourceShrinkingNewtonArray P R p hP hR hp T hT hFT z=
      shrinkingNewtonMomentWithScale shrinkingNewtonSourceKappa
        (rapidDistance P R) (rapidDistance P R) (hermiteScaleDistribution p T) z.1.1 z.1.2 z.2.1 z.2.2 := rfl


/-- The actual gauged rapid-source variable-weight matrix as a genuine complete lp vector. -/
def sourceShrinkingGaugeNewtonArray (P R p : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) (hp : p ≤ P)
    (T : HermiteScale (-(p:ℤ)))
    (hT : AtomicOnCarrier ((criticalPhaseTailCarrier (shrinkingRapidPhase P R)
      (shrinkingRapidPhase_mem P R hP hR) 0 0).translate (-1/2)) (hermiteScaleDistribution p T))
    (hFT : AtomicOnCarrier ((criticalPhaseTailCarrier (shrinkingRapidPhase P R)
      (shrinkingRapidPhase_mem P R hP hR) 0 0).translate (-1/2)) (𝓕 (hermiteScaleDistribution p T))) :
    SeamMomentArray :=
  ⟨fun z => shrinkingNewtonGaugeMomentWithScale shrinkingNewtonSourceKappa
      (rapidDistance P R) (rapidDistance P R) (hermiteScaleDistribution p T) z.1.1 z.1.2 z.2.1 z.2.2,
    memℓp_gen (by simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
      summable_sq_sourceGaugeNewtonMatrix_actual P R p hP hR hp T hT hFT)⟩

/-- Every entry is the exact whole-source normalized reading, including both infinite arms. -/
theorem sourceShrinkingGaugeNewtonArray_apply (P R p : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) (hp : p ≤ P)
    (T : HermiteScale (-(p:ℤ)))
    (hT : AtomicOnCarrier ((criticalPhaseTailCarrier (shrinkingRapidPhase P R)
      (shrinkingRapidPhase_mem P R hP hR) 0 0).translate (-1/2)) (hermiteScaleDistribution p T))
    (hFT : AtomicOnCarrier ((criticalPhaseTailCarrier (shrinkingRapidPhase P R)
      (shrinkingRapidPhase_mem P R hP hR) 0 0).translate (-1/2)) (𝓕 (hermiteScaleDistribution p T)))
    (z : SeamMomentIndex) : sourceShrinkingGaugeNewtonArray P R p hP hR hp T hT hFT z=
      shrinkingNewtonGaugeMomentWithScale shrinkingNewtonSourceKappa
        (rapidDistance P R) (rapidDistance P R) (hermiteScaleDistribution p T) z.1.1 z.1.2 z.2.1 z.2.2 := rfl

end
end MeyerGeneralProblem.Adaptive
