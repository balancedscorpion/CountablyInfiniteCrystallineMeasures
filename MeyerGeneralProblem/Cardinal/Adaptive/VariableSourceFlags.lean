module

public import MeyerGeneralProblem.Cardinal.Adaptive.VariableSourceGauge

@[expose] public section

/-! Literal source flags and diagonal equations at the variable normalization. -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open scoped FourierTransform

/-- Variable normalization removes no actual coordinate. -/
theorem variableNewtonNormalization_ne_zero (κ : ℝ) (hκ : κ ≠ 0) (ε δ : ℕ → ℝ)
    (hε : ∀ i, 0 < ε i) (hδ : ∀ i, 0 < δ i) (i j : ℕ) (e f : Bool) :
    variableNewtonNormalization κ ε δ i e j f ≠ 0 := by
  apply inv_ne_zero
  apply mul_ne_zero
  · exact pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hκ)
  · exact Complex.ofReal_ne_zero.mpr (ne_of_gt (mul_pos
      (shrinkingNewtonWeight_strictly_pos ε hε i) (shrinkingNewtonWeight_strictly_pos δ hδ j)))

/-- The genuine rotated Fourier reading with the original variable weights. -/
def variableFourierMoment (κ : ℝ) (ε δ : ℕ → ℝ) (T : TemperedDistribution ℝ ℂ)
    (i : ℕ) (e : Bool) (j : ℕ) (f : Bool) : ℂ :=
  variableNewtonNormalization κ ε δ i e j f * halfNewtonFourierBilinear T
    (halfNewtonTest (fun l => ε l) i e) (halfNewtonTest (fun l => δ l) j f)

/-- Exact reflection and transposition preserve the variable product normalization. -/
theorem variableFourierMoment_eq_transposed (κ : ℝ) (ε δ : ℕ → ℝ)
    (T : TemperedDistribution ℝ ℂ) (i : ℕ) (e : Bool) (j : ℕ) (f : Bool) :
    variableFourierMoment κ ε δ T i e j f=
      halfNewtonParitySign e * shrinkingNewtonMomentWithScale κ δ ε (halfWeylFourierCompanion T) j f i e := by
  rw [variableFourierMoment,shrinkingNewtonMomentWithScale_normalization]
  unfold halfNewtonFourierBilinear halfNewtonCoordinate
  rw [halfNewtonTest_reflection,halfNewtonBilinear_smul_second,variableNewtonNormalization_swap]
  ring

/-- The rapid original phases stay above one quarter, including the first phase. -/
theorem variableSourcePhase_ge_quarter (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) (l : ℕ+) :
    1/4 ≤ shrinkingRapidPhase P R l := by
  have h := variableSourcePhase_chart_bound P R hP hR l
  have hh := le_abs_self (1/2-shrinkingRapidPhase P R l)
  linarith

/-- The complete physical upper flag is inherited by every variable normalization. -/
theorem variableMoment_upper_flag (P R Q S : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R)
    (hQ : 1 ≤ Q) (hS : 1 ≤ S) (κ : ℝ) (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier ((criticalPhaseTailCarrier (shrinkingRapidPhase P R)
      (shrinkingRapidPhase_mem P R hP hR) 0 0).translate (-1/2)) T)
    (hFT : AtomicOnCarrier ((criticalPhaseTailCarrier (shrinkingRapidPhase Q S)
      (shrinkingRapidPhase_mem Q S hQ hS) 0 0).translate (-1/2)) (𝓕 T))
    (i j : ℕ) (e f : Bool) (hij : j < i) :
    shrinkingNewtonMomentWithScale κ (rapidDistance P R) (rapidDistance Q S) T i e j f=0 := by
  have h := halfNewtonCoordinate_upper_flag _ _ (shrinkingRapidPhase_mem P R hP hR)
    (shrinkingRapidPhase_mem Q S hQ hS) (variableSourcePhase_ge_quarter Q S hQ hS) T hT hFT i j e f hij
  simp only [shrinkingRapidPhase,sub_sub_cancel] at h
  rw [shrinkingNewtonMomentWithScale_normalization,h,mul_zero]

/-- Both exact physical diagonal signs survive the variable normalization;
parity 11 has the required kappa-squared denominator. -/
theorem variableMoment_diagonal_relations (P R Q S : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R)
    (hQ : 1 ≤ Q) (hS : 1 ≤ S) (κ : ℝ) (hκ : κ ≠ 0) (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier ((criticalPhaseTailCarrier (shrinkingRapidPhase P R)
      (shrinkingRapidPhase_mem P R hP hR) 0 0).translate (-1/2)) T)
    (hFT : AtomicOnCarrier ((criticalPhaseTailCarrier (shrinkingRapidPhase Q S)
      (shrinkingRapidPhase_mem Q S hQ hS) 0 0).translate (-1/2)) (𝓕 T)) (i : ℕ) :
    shrinkingNewtonMomentWithScale κ (rapidDistance P R) (rapidDistance Q S) T i true i false=
      Complex.I*(variableSourceTangent P R i:ℂ)*
        shrinkingNewtonMomentWithScale κ (rapidDistance P R) (rapidDistance Q S) T i false i true ∧
    shrinkingNewtonMomentWithScale κ (rapidDistance P R) (rapidDistance Q S) T i true i true=
      (-Complex.I*(variableSourceTangent P R i:ℂ)/(κ:ℂ)^2)*
        shrinkingNewtonMomentWithScale κ (rapidDistance P R) (rapidDistance Q S) T i false i false := by
  obtain ⟨hp,hn⟩ := halfNewtonCoordinate_diagonal_relations _ _ (shrinkingRapidPhase_mem P R hP hR)
    (shrinkingRapidPhase_mem Q S hQ hS) (variableSourcePhase_ge_quarter Q S hQ hS) T hT hFT i
  simp only [shrinkingRapidPhase,sub_sub_cancel,PNat.mk_coe] at hp hn
  simp only [shrinkingNewtonMomentWithScale_normalization,hp,hn,variableNewtonNormalization,
    Bool.toNat_true,Bool.toNat_false,variableSourceTangent]
  constructor
  · ring
  · have hc : (κ:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hκ
    simp only [one_add_one_eq_two,zero_add,pow_zero,one_mul,mul_inv_rev]
    field_simp <;> ring

/-- The complete actual Fourier companion has the opposite variable-weight flag. -/
theorem variableFourierMoment_lower_flag (P R Q S : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R)
    (hQ : 1 ≤ Q) (hS : 1 ≤ S) (κ : ℝ) (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier (criticalPhaseTailCarrier (shrinkingRapidPhase P R)
      (shrinkingRapidPhase_mem P R hP hR) 0 0) T)
    (hFT : AtomicOnCarrier (criticalPhaseTailCarrier (shrinkingRapidPhase Q S)
      (shrinkingRapidPhase_mem Q S hQ hS) 0 0) (𝓕 T))
    (i j : ℕ) (e f : Bool) (hij : i < j) :
    variableFourierMoment κ (rapidDistance P R) (rapidDistance Q S) T i e j f=0 := by
  obtain ⟨hp,hq⟩ := halfWeylFourierCompanion_atomic_records _ _ (shrinkingRapidPhase_mem P R hP hR)
    (shrinkingRapidPhase_mem Q S hQ hS) T hT hFT
  rw [variableFourierMoment_eq_transposed,
    variableMoment_upper_flag Q S P R hQ hS hP hR κ _ hp hq j i f e hij,mul_zero]

/-- The actual Fourier companion has both reversed imaginary signs, at exactly
 the source's variable kappa normalization. -/
theorem variableFourierMoment_diagonal_relations (P R Q S : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R)
    (hQ : 1 ≤ Q) (hS : 1 ≤ S) (κ : ℝ) (hκ : κ ≠ 0) (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier (criticalPhaseTailCarrier (shrinkingRapidPhase P R)
      (shrinkingRapidPhase_mem P R hP hR) 0 0) T)
    (hFT : AtomicOnCarrier (criticalPhaseTailCarrier (shrinkingRapidPhase Q S)
      (shrinkingRapidPhase_mem Q S hQ hS) 0 0) (𝓕 T)) (i : ℕ) :
    variableFourierMoment κ (rapidDistance P R) (rapidDistance Q S) T i false i true=
      -Complex.I*(variableSourceTangent Q S i:ℂ)*variableFourierMoment κ (rapidDistance P R) (rapidDistance Q S) T i true i false ∧
    variableFourierMoment κ (rapidDistance P R) (rapidDistance Q S) T i true i true=
      (Complex.I*(variableSourceTangent Q S i:ℂ)/(κ:ℂ)^2)*variableFourierMoment κ (rapidDistance P R) (rapidDistance Q S) T i false i false := by
  obtain ⟨hp,hq⟩ := halfWeylFourierCompanion_atomic_records _ _ (shrinkingRapidPhase_mem P R hP hR)
    (shrinkingRapidPhase_mem Q S hQ hS) T hT hFT
  obtain ⟨hc,hd⟩ := variableMoment_diagonal_relations Q S P R hQ hS hP hR κ hκ _ hp hq i
  simp only [variableFourierMoment_eq_transposed,halfNewtonParitySign,
    ite_true,Bool.false_eq_true,ite_false,one_mul,neg_one_mul]
  rw [hc,hd]
  constructor <;> ring

/-- The full analytic gauge reading is the actual Fourier companion reading,
with no change to either variable weight or the parity scale. -/
theorem variableGaugeMoment_eq_FourierMoment (P R Q S : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R)
    (hQ : 1 ≤ Q) (hS : 1 ≤ S) (κ : ℝ) (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier (criticalPhaseTailCarrier (shrinkingRapidPhase P R)
      (shrinkingRapidPhase_mem P R hP hR) 0 0) T)
    (hFT : AtomicOnCarrier (criticalPhaseTailCarrier (shrinkingRapidPhase Q S)
      (shrinkingRapidPhase_mem Q S hQ hS) 0 0) (𝓕 T)) (i j : ℕ) (e f : Bool) :
    shrinkingNewtonGaugeMomentWithScale κ (rapidDistance P R) (rapidDistance Q S)
      (halfWeylDistributionCLM T) i e j f =
      variableFourierMoment κ (rapidDistance P R) (rapidDistance Q S) T i e j f := by
  rw [shrinkingNewtonGaugeMomentWithScale_normalization,variableFourierMoment]
  congr 1
  apply halfNewtonGaugeBilinear_eq_FourierBilinear_central _ _
    (shrinkingRapidPhase_mem P R hP hR) (shrinkingRapidPhase_mem Q S hQ hS)
    (variableSourcePhase_ge_quarter P R hP hR) (variableSourcePhase_ge_quarter Q S hQ hS) T hT hFT
  · intro x hx; rw [halfNewtonTest_apply,zakCentralCutoff_zero x hx,zero_mul]
  · intro x hx; rw [halfNewtonTest_apply,zakCentralCutoff_zero x hx,zero_mul]

end
end MeyerGeneralProblem.Adaptive
