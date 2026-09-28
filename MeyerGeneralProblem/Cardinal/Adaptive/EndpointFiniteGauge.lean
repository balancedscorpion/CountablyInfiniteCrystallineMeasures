module

public import MeyerGeneralProblem.Cardinal.Adaptive.EndpointOperatorInputs
public import MeyerGeneralProblem.Cardinal.Adaptive.ActualSourceGauge

@[expose] public section

/-! The complete bounded gauge on actual finite endpoint sources, including zero padding. -/
noncomputable section
namespace MeyerGeneralProblem.Adaptive

/-- The fixed chart reflects evenly as an actual Schwartz function. -/
theorem fixedNewtonChart_reflection : schwartzReflectionCLM fixedNewtonChart=fixedNewtonChart := by
  ext x
  simp only [schwartzReflectionCLM_apply,fixedNewtonChart_apply,shrinkingTailCutoff]
  congr 1
  rw [show -x+(1/4096:ℝ)=1/4096-x by ring,sub_neg_eq_add,add_comm (1/4096:ℝ) x,mul_comm]

/-- Fixed-chart multiplication preserves the exact signed Newton reflection. -/
theorem fixedNewtonChart_test_reflection (ε : ℕ+ → ℝ) (i : ℕ) (e : Bool) :
    schwartzReflectionCLM (schwartzChartProduct fixedNewtonChart (halfNewtonTest ε i e))=
      halfNewtonParitySign e •schwartzChartProduct fixedNewtonChart (halfNewtonTest ε i e) := by
  ext x
  have hc := congrArg (fun f : SchwartzMap ℝ ℂ => f x) fixedNewtonChart_reflection
  have ht := congrArg (fun f : SchwartzMap ℝ ℂ => f x) (halfNewtonTest_reflection ε i e)
  simp only [schwartzReflectionCLM_apply] at hc
  simp only [schwartzReflectionCLM_apply,_root_.smul_apply,smul_eq_mul] at ht
  simp only [schwartzReflectionCLM_apply,schwartzChartProduct_apply,_root_.smul_apply,smul_eq_mul,hc,ht]
  ring

/-- The actual finite physical chart reading agrees with the complete moment, at all indices. -/
theorem endpointFinite_chart_reading (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) (k i j : ℕ) (e f : Bool) :
    chartNewtonReading halfNewtonNormalization (endpointPaddedDistance P R k) (endpointPaddedDistance P R k)
      (halfWeylDistributionCLM (endpointFiniteSource P R hP hR k)) fixedNewtonChart fixedNewtonChart i e j f=
      endpointFinitePhysicalArray P R hP hR k ((i,e),(j,f)) := by
  unfold chartNewtonReading
  rw [fixedNewtonChart_product,fixedNewtonChart_product]
  change halfNewtonNormalization i e j f*halfNewtonBilinear
    (halfWeylDistributionCLM (endpointPoissonSynthesis _ _ _)) _ _= _
  rw [halfNewtonBilinear_endpoint_fixed_cutoff _ _ _ _ _ i j e f _ _ (by norm_num)
    (by norm_num) (by norm_num) (endpointCenteredPhase_rapid_fixedRadius hP hR k)
      (endpointCenteredPhase_rapid_fixedRadius hP hR k)]
  rfl

/-- The compact-chart Fourier reading is the genuine finite companion moment. -/
theorem endpointFinite_fourier_chart_reading (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) (k i j : ℕ) (e f : Bool) :
    halfNewtonNormalization i e j f*halfNewtonFourierBilinear (endpointFiniteSource P R hP hR k)
      (schwartzChartProduct fixedNewtonChart (halfNewtonTest (endpointPaddedDistance P R k) i e))
      (schwartzChartProduct fixedNewtonChart (halfNewtonTest (endpointPaddedDistance P R k) j f))=
      endpointFiniteFourierArray P R hP hR k ((i,e),(j,f)) := by
  rw [endpointFiniteFourierArray_eq]
  unfold halfNewtonFourierBilinear
  rw [endpointFiniteSource_companion,fixedNewtonChart_test_reflection]
  unfold halfNewtonBilinear
  rw [map_smul,zakTensorAction_smul_right]
  have hh := endpointFinite_chart_reading P R hP hR k j i f e
  unfold chartNewtonReading halfNewtonBilinear at hh
  rw [←hh]
  unfold halfNewtonNormalization
  rw [Nat.add_comm i j,Nat.add_comm e.toNat f.toNat]
  ring

/-- The literal full exponential gauge sends the actual finite physical vector to
its actual Fourier vector. No positivity is required for the zero-padded tail. -/
theorem endpointFiniteGauge_action (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) (k : ℕ) :
    seamGaugeOperator
      (seamSineRow (1/64) (1/4096) (endpointOperatorNode P R k) ((1/4096)^2) (by positivity)
        (endpointOperatorNode_norm hP hR k))
      (seamSineColumn (1/64) (1/4096) (endpointOperatorNode P R k) ((1/4096)^2) (by positivity)
        (endpointOperatorNode_norm hP hR k)) (endpointFinitePhysicalVector P R hP hR k)=
      endpointFiniteFourierVector P R hP hR k := by
  ext z
  rcases z with ⟨⟨i,e⟩,⟨j,f⟩⟩
  have hc : ∀ i e j f, endpointFinitePhysicalVector P R hP hR k ((i,e),(j,f))=
      chartNewtonReading halfNewtonNormalization (endpointPaddedDistance P R k) (endpointPaddedDistance P R k)
      (halfWeylDistributionCLM (endpointFiniteSource P R hP hR k)) fixedNewtonChart fixedNewtonChart i e j f := by
    intro i e j f
    exact (endpointFinite_chart_reading P R hP hR k i j e f).symm
  have hh := seamGauge_chart_action (endpointPaddedDistance P R k) (endpointPaddedDistance P R k)
    ((1/4096)^2) ((1/4096)^2) (by positivity) (by positivity)
    (endpointOperatorNode_norm hP hR k) (endpointOperatorNode_norm hP hR k)
    (halfWeylDistributionCLM (endpointFiniteSource P R hP hR k)) fixedNewtonChart fixedNewtonChart
    (1/4096) (by norm_num) (by norm_num) fixedNewtonChart_zero fixedNewtonChart_zero
    (endpointFinitePhysicalVector P R hP hR k) hc
    ((seamSineRow_square_norm _ (endpointOperatorNode_norm hP hR k)).trans_lt (by norm_num))
    ((seamSineRow_square_norm _ (endpointOperatorNode_norm hP hR k)).trans_lt (by norm_num)) i j e f
  rw [halfNewtonGaugeBilinear_eq_FourierBilinear _ _ _ (1/4096) (by norm_num)
    (fun x hx => by rw [schwartzChartProduct_apply,fixedNewtonChart_zero x hx,zero_mul])
    (fun x hx => by rw [schwartzChartProduct_apply,fixedNewtonChart_zero x hx,zero_mul]),
    endpointFinite_fourier_chart_reading] at hh
  exact hh

end MeyerGeneralProblem.Adaptive
