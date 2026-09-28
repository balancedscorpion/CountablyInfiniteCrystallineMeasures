module

public import MeyerGeneralProblem.Cardinal.Adaptive.ActualGaugeAction
public import MeyerGeneralProblem.Cardinal.Adaptive.ActualConstantNewtonArray

@[expose] public section

/-! # The complete gauge on the literal physical and Fourier source arrays -/
open scoped ContDiff
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open Set
open scoped FourierTransform

theorem fixedNewtonChart_compact :
    HasCompactSupport (fun x : ℝ => (shrinkingTailCutoff (1/8192) (1/4096) x : ℂ)) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc : IsCompact (Icc (-(1/4096 : ℝ)) (1/4096)))
  intro x hx
  have h : |x| < (1/4096 : ℝ) := lt_of_not_ge (fun h => hx (by
    dsimp only
    rw [shrinkingTailCutoff_zero _ _ x (by norm_num) h,Complex.ofReal_zero]))
  exact ⟨(abs_lt.mp h).1.le,(abs_lt.mp h).2.le⟩

/-- The actual fixed smooth chart used by constant-normalized source moments. -/
def fixedNewtonChart : SchwartzMap ℝ ℂ :=
  fixedNewtonChart_compact.toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp (shrinkingTailCutoff_smooth (1/8192) (1/4096)))

/-- The fixed chart has its literal shrinking cutoff value. -/
theorem fixedNewtonChart_apply (x : ℝ) :
    fixedNewtonChart x=(shrinkingTailCutoff (1/8192) (1/4096) x : ℂ) := rfl

/-- The fixed chart preserves every actual phase in its inner cell exactly. -/
theorem fixedNewtonChart_one (x : ℝ) (hx : |x| ≤ 1/8192) : fixedNewtonChart x=1 := by
  rw [fixedNewtonChart_apply,shrinkingTailCutoff_one _ _ x (by norm_num) hx,Complex.ofReal_one]

/-- The fixed chart is supported in the strict coordinate-inversion cell. -/
theorem fixedNewtonChart_zero (x : ℝ) (hx : 1/4096 ≤ |x|) : fixedNewtonChart x=0 := by
  rw [fixedNewtonChart_apply,shrinkingTailCutoff_zero _ _ x (by norm_num) hx,Complex.ofReal_zero]

/-- Actual chart multiplication agrees as a whole Schwartz function with the
fixed shrinking Newton test; this includes its seam value and all derivatives. -/
theorem fixedNewtonChart_product (ε : ℕ+ → ℝ) (i : ℕ) (e : Bool) :
    schwartzChartProduct fixedNewtonChart (halfNewtonTest ε i e)=
      shrinkingNewtonTest ε i e (1/8192) (1/4096) (by norm_num) := by
  ext x
  rw [schwartzChartProduct_apply,fixedNewtonChart_apply,halfNewtonTest_apply,shrinkingNewtonTest_apply]
  by_cases hx : 1/4096 ≤ |x|
  · rw [shrinkingTailCutoff_zero _ _ x (by norm_num) hx,Complex.ofReal_zero,zero_mul,zero_mul]
  · rw [zakCentralCutoff_one x (by linarith [lt_of_not_ge hx]),one_mul]

/-- The true compact-chart source reading is exactly the previously bounded
fixed-cutoff Newton moment, including zero-padded finite phases. -/
theorem chartNewtonReading_fixed (ε δ : ℕ → ℝ) (T : TemperedDistribution ℝ ℂ)
    (i j : ℕ) (e f : Bool) :
    chartNewtonReading halfNewtonNormalization (fun l => ε l) (fun l => δ l) T
      fixedNewtonChart fixedNewtonChart i e j f=
    fixedChartNewtonMoment (1/4096) (1/64) (1/8192) (1/4096) (by norm_num) ε δ T i e j f := by
  simp only [chartNewtonReading,fixedNewtonChart_product,fixedChartNewtonMoment,halfNewtonNormalization,
    Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat]

/-- The complete bounded gauge acts on the actual paired source moments.
Localization is proved from both whole atomic records, not supplied as a gauge certificate. -/
theorem seamGauge_actualMoment_action (α β : ℕ+ → ℝ)
    (hia : ∀ j, 0 < α j ∧ α j < 1/2) (hib : ∀ j, 0 < β j ∧ β j < 1/2)
    (ha : ∀ j, |1/2-α j| ≤ 1/8192) (hb : ∀ j, |1/2-β j| ≤ 1/8192)
    (haN : ∀ i, ‖criticalNewtonNode (1/2-α ⟨i+1,by omega⟩)‖ ≤ (1/4096:ℝ)^2)
    (hbN : ∀ i, ‖criticalNewtonNode (1/2-β ⟨i+1,by omega⟩)‖ ≤ (1/4096:ℝ)^2)
    (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier ((criticalPhaseTailCarrier α hia 0 0).translate (-1/2)) T)
    (hFT : AtomicOnCarrier ((criticalPhaseTailCarrier β hib 0 0).translate (-1/2)) (𝓕 T))
    (u : SeamMomentArray)
    (hu : ∀ i e j f, u ((i,e),(j,f))=halfNewtonMoment (fun l => 1/2-α l) (fun l => 1/2-β l) T i e j f)
    (i j : ℕ) (e f : Bool) :
    NormedSpace.exp (seamGaugeGenerator
      (seamSineRow (1/64) (1/4096) (fun n => criticalNewtonNode (1/2-α ⟨n+1,by omega⟩)) ((1/4096)^2) (by positivity) haN)
      (seamSineColumn (1/64) (1/4096) (fun n => criticalNewtonNode (1/2-β ⟨n+1,by omega⟩)) ((1/4096)^2) (by positivity) hbN))
        u ((i,e),(j,f))=
    halfNewtonNormalization i e j f*halfNewtonGaugeBilinear T
      (halfNewtonTest (fun l => 1/2-α l) i e) (halfNewtonTest (fun l => 1/2-β l) j f) := by
  have hc : ∀ i e j f, u ((i,e),(j,f))=chartNewtonReading halfNewtonNormalization
      (fun l => 1/2-α l) (fun l => 1/2-β l) T fixedNewtonChart fixedNewtonChart i e j f := by
    intro i e j f
    rw [hu]
    have hh := chartNewtonReading_fixed (phaseNatDistance α) (phaseNatDistance β) T i j e f
    simp only [phaseNatDistance_coe] at hh
    rw [hh,fixedChartNewtonMoment_eq_actual α β hia hib ha hb T hT hFT]
  have hh := seamGauge_chart_action (fun l => 1/2-α l) (fun l => 1/2-β l)
    ((1/4096)^2) ((1/4096)^2) (by positivity) (by positivity) haN hbN T
    fixedNewtonChart fixedNewtonChart (1/4096) (by norm_num) (by norm_num)
    fixedNewtonChart_zero fixedNewtonChart_zero u hc
    ((seamSineRow_square_norm _ haN).trans_lt (by norm_num))
    ((seamSineRow_square_norm _ hbN).trans_lt (by norm_num)) i j e f
  simp only [fixedNewtonChart_product] at hh
  rw [halfNewtonGaugeBilinear_shrinking_tests α β hia hib T hT hFT i j e f
    (1/8192) (1/4096) (1/8192) (1/4096) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun l => (ha l).trans (by norm_num)) (fun l => (hb l).trans (by norm_num))
    (fun l _ => ha l) (fun l _ => hb l)] at hh
  exact hh

/-- The full bounded gauge sends the complete original physical array to its
complete Fourier companion. Both arrays are the constructed actual ℓ² vectors. -/
theorem seamGauge_actualArrays (α β : ℕ+ → ℝ)
    (hia : ∀ j, 0 < α j ∧ α j < 1/2) (hib : ∀ j, 0 < β j ∧ β j < 1/2)
    (ha : ∀ j, |1/2-α j| ≤ 1/8192) (hb : ∀ j, |1/2-β j| ≤ 1/8192)
    (haN : ∀ i, ‖criticalNewtonNode (1/2-α ⟨i+1,by omega⟩)‖ ≤ (1/4096:ℝ)^2)
    (hbN : ∀ i, ‖criticalNewtonNode (1/2-β ⟨i+1,by omega⟩)‖ ≤ (1/4096:ℝ)^2)
    (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier (criticalPhaseTailCarrier α hia 0 0) T)
    (hFT : AtomicOnCarrier (criticalPhaseTailCarrier β hib 0 0) (𝓕 T)) :
    let hp := halfWeylDistribution_atomic_records α β hia hib T hT hFT
    NormedSpace.exp (seamGaugeGenerator
      (seamSineRow (1/64) (1/4096) (fun n => criticalNewtonNode (1/2-α ⟨n+1,by omega⟩)) ((1/4096)^2) (by positivity) haN)
      (seamSineColumn (1/64) (1/4096) (fun n => criticalNewtonNode (1/2-β ⟨n+1,by omega⟩)) ((1/4096)^2) (by positivity) hbN))
        (actualConstantNewtonArray α β hia hib ha hb (halfWeylDistributionCLM T) hp.1 hp.2)=
      actualConstantFourierArray α β hia hib ha hb T hT hFT := by
  dsimp only
  ext z
  rcases z with ⟨⟨i,e⟩,⟨j,f⟩⟩
  rw [seamGauge_actualMoment_action α β hia hib ha hb haN hbN
    (halfWeylDistributionCLM T)
    (halfWeylDistribution_atomic_records α β hia hib T hT hFT).1
    (halfWeylDistribution_atomic_records α β hia hib T hT hFT).2
    _ (fun i e j f => rfl) i j e f]
  exact (actualConstantFourierArray_gauge α β hia hib ha hb T hT hFT i j e f).symm

end
end MeyerGeneralProblem.Adaptive
