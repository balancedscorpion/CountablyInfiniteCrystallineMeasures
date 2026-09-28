module

public import MeyerGeneralProblem.Cardinal.Adaptive.VariableActualGaugeAction
public import MeyerGeneralProblem.Cardinal.Adaptive.ActualSourceGauge

@[expose] public section

/-! The complete variable gauge on the literal rapid-source Newton arrays. -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open scoped FourierTransform

/-- Every rapid phase is contained in the fixed coordinate chart, with the source constants. -/
theorem variableSourcePhase_chart_bound (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) (l : ℕ+) :
    |1/2-shrinkingRapidPhase P R l| ≤ 1/8192 := by
  simp only [shrinkingRapidPhase,sub_sub_cancel,abs_of_pos ((variableNewton_source_phase_bound P R hP hR l).1)]
  exact (variableNewton_source_phase_bound P R hP hR l).2.trans (by norm_num [shrinkingNewtonSourceKappa])

/-- The genuine entire variable gauge sends actual physical moments to their full analytic gauge.
Both chart replacements follow from the two whole atomic records. -/
theorem variableGauge_actualMoment_action (P R Q S : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R)
    (hQ : 1 ≤ Q) (hS : 1 ≤ S) (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier ((criticalPhaseTailCarrier (shrinkingRapidPhase P R)
      (shrinkingRapidPhase_mem P R hP hR) 0 0).translate (-1/2)) T)
    (hFT : AtomicOnCarrier ((criticalPhaseTailCarrier (shrinkingRapidPhase Q S)
      (shrinkingRapidPhase_mem Q S hQ hS) 0 0).translate (-1/2)) (𝓕 T))
    (u : SeamMomentArray)
    (hu : ∀ i e j f, u ((i,e),(j,f))=shrinkingNewtonMomentWithScale shrinkingNewtonSourceKappa
      (rapidDistance P R) (rapidDistance Q S) T i e j f) (i j : ℕ) (e f : Bool) :
    variableGaugeOperator P R Q S hP hR hQ hS u ((i,e),(j,f))=
      shrinkingNewtonGaugeMomentWithScale shrinkingNewtonSourceKappa
        (rapidDistance P R) (rapidDistance Q S) T i e j f := by
  have ha := variableSourcePhase_chart_bound P R hP hR
  have hb := variableSourcePhase_chart_bound Q S hQ hS
  have hreplace (i j : ℕ) (e f : Bool) := halfNewtonBilinear_shrinking_tests
    (shrinkingRapidPhase P R) (shrinkingRapidPhase Q S)
    (shrinkingRapidPhase_mem P R hP hR) (shrinkingRapidPhase_mem Q S hQ hS) T hT hFT i j e f
    (1/8192) (1/4096) (1/8192) (1/4096) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun l => (ha l).trans (by norm_num)) (fun l => (hb l).trans (by norm_num))
    (fun l _ => ha l) (fun l _ => hb l)
  simp only [shrinkingRapidPhase,sub_sub_cancel] at hreplace
  have hc : ∀ i e j f, u ((i,e),(j,f))=chartNewtonReading
      (variableNewtonNormalization shrinkingNewtonSourceKappa (rapidDistance P R) (rapidDistance Q S))
      (fun l => rapidDistance P R l) (fun l => rapidDistance Q S l) T fixedNewtonChart fixedNewtonChart i e j f := by
    intro i e j f
    rw [hu,shrinkingNewtonMomentWithScale_normalization]
    simp only [chartNewtonReading,fixedNewtonChart_product,hreplace,halfNewtonCoordinate]
  have hh := variableGauge_chart_action P R Q S hP hR hQ hS T
    fixedNewtonChart fixedNewtonChart (1/4096) (by norm_num) (by norm_num)
    fixedNewtonChart_zero fixedNewtonChart_zero u hc i j e f
  have hg := halfNewtonGaugeBilinear_shrinking_tests
    (shrinkingRapidPhase P R) (shrinkingRapidPhase Q S)
    (shrinkingRapidPhase_mem P R hP hR) (shrinkingRapidPhase_mem Q S hQ hS) T hT hFT i j e f
    (1/8192) (1/4096) (1/8192) (1/4096) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun l => (ha l).trans (by norm_num)) (fun l => (hb l).trans (by norm_num))
    (fun l _ => ha l) (fun l _ => hb l)
  simp only [shrinkingRapidPhase,sub_sub_cancel] at hg
  simpa only [fixedNewtonChart_product,hg,shrinkingNewtonGaugeMomentWithScale_normalization] using hh

/-- At every original native order p≤P, the full bounded gauge carries the constructed
complete variable-weight lp source array to the constructed complete gauged array. -/
theorem variableGauge_actualArrays (P R p : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) (hp : p ≤ P)
    (T : HermiteScale (-(p:ℤ)))
    (hT : AtomicOnCarrier ((criticalPhaseTailCarrier (shrinkingRapidPhase P R)
      (shrinkingRapidPhase_mem P R hP hR) 0 0).translate (-1/2)) (hermiteScaleDistribution p T))
    (hFT : AtomicOnCarrier ((criticalPhaseTailCarrier (shrinkingRapidPhase P R)
      (shrinkingRapidPhase_mem P R hP hR) 0 0).translate (-1/2)) (𝓕 (hermiteScaleDistribution p T))) :
    variableGaugeOperator P R P R hP hR hP hR (sourceShrinkingNewtonArray P R p hP hR hp T hT hFT)=
      sourceShrinkingGaugeNewtonArray P R p hP hR hp T hT hFT := by
  ext z
  rcases z with ⟨⟨i,e⟩,⟨j,f⟩⟩
  exact variableGauge_actualMoment_action P R P R hP hR hP hR (hermiteScaleDistribution p T)
    hT hFT _ (fun _ _ _ _ => rfl) i j e f

end
end MeyerGeneralProblem.Adaptive
