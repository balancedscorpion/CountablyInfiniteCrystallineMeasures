module

public import MeyerGeneralProblem.Cardinal.Adaptive.VariableMomentNormalization
public import MeyerGeneralProblem.Cardinal.Adaptive.ActualGaugeAction

@[expose] public section

/-! The entire variable coordinate and gauge operators act on actual whole-source slices. -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section

/-- Literal coordinate multiplication in a continuous physical slice, with
arbitrary actual variable weights and all inverse-sine terms retained. -/
theorem variableCoordinateRow_chart_slice_action (κ : ℝ) (hκ : κ ≠ 0) (ε δ : ℕ → ℝ) (ρ : ℝ)
    (hρ : ρ ≤ 1/2) (hsmall : ρ ≤ 1/32) (hε : ∀ i, 0 < ε i ∧ ε i ≤ ρ)
    (φ : SchwartzMap ℝ ℂ) (b : ℝ) (hb : 0 < b) (hb' : b < 1/8)
    (hφ : ∀ x, b ≤ |x| → φ x=0) (V : ℕ → Bool → TemperedDistribution ℝ ℂ) (u : SeamMomentArray)
    (hu : ∀ i e j f, u ((i,e),(j,f))=variableNewtonNormalization κ ε δ i e j f*
      V j f (schwartzChartProduct φ (halfNewtonTest (fun l => ε l) i e))) (i j : ℕ) (e f : Bool) :
    variableCoordinateRow κ ε ρ hρ hε u ((i,e),(j,f))=
      variableNewtonNormalization κ ε δ i e j f * V j f
        (schwartzChartProduct (mixedSchwartz 1 0 φ) (halfNewtonTest (fun l => ε l) i e)) := by
  have hk : (κ:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hκ
  rw [variableCoordinateRow_eq_seamCoordinate _ hk]
  have hs : ‖variableSineRow κ ε ρ hρ hε * variableSineRow κ ε ρ hρ hε‖ < 1 := by
    change ‖(variableSineRow κ ε ρ hρ hε).comp (variableSineRow κ ε ρ hρ hε)‖ < 1
    rw [variableSineRow_square _ hk]
    exact (variableNewtonRow_kernel_norm_le ε ρ hρ hsmall hε).trans_lt (by linarith)
  apply actualCoordinate_chart_slice_action (variableNewtonNormalization κ ε δ) (fun l => ε l)
    (variableSineRow κ ε ρ hρ hε) hs ?_ φ b hb hb' hφ V u hu i j e f
  intro U w hw i e j f
  simpa only [compactSinePower_one_halfNewtonTest] using
    variableSineRow_slice_action κ hκ ε δ ρ hρ hε U w hw i j e f

/-- The actual spectral coordinate action follows by exact axis exchange,
including the full variable normalization and every continuous slice. -/
theorem variableCoordinateSourceColumn_chart_slice_action (Q S : ℕ) (hQ : 1 ≤ Q) (hS : 1 ≤ S)
    (ε : ℕ → ℝ) (φ : SchwartzMap ℝ ℂ) (b : ℝ) (hb : 0 < b) (hb' : b < 1/8)
    (hφ : ∀ x, b ≤ |x| → φ x=0) (V : ℕ → Bool → TemperedDistribution ℝ ℂ) (u : SeamMomentArray)
    (hu : ∀ i e j f, u ((i,e),(j,f))=variableNewtonNormalization shrinkingNewtonSourceKappa ε (rapidDistance Q S) i e j f*
      V i e (schwartzChartProduct φ (halfNewtonTest (fun l => rapidDistance Q S l) j f)))
    (i j : ℕ) (e f : Bool) :
    variableCoordinateSourceColumn Q S hQ hS u ((i,e),(j,f))=
      variableNewtonNormalization shrinkingNewtonSourceKappa ε (rapidDistance Q S) i e j f * V i e
        (schwartzChartProduct (mixedSchwartz 1 0 φ) (halfNewtonTest (fun l => rapidDistance Q S l) j f)) := by
  have hv : ∀ j f i e, seamTranspose u ((j,f),(i,e))=
      variableNewtonNormalization shrinkingNewtonSourceKappa (rapidDistance Q S) ε j f i e*
      V i e (schwartzChartProduct φ (halfNewtonTest (fun l => rapidDistance Q S l) j f)) := by
    intro j f i e
    simpa only [seamTranspose_apply,variableNewtonNormalization_swap] using hu i e j f
  have h := variableCoordinateRow_chart_slice_action shrinkingNewtonSourceKappa
    (ne_of_gt shrinkingNewtonSourceKappa_pos) (rapidDistance Q S) ε (shrinkingNewtonSourceKappa^4)
    (by norm_num [shrinkingNewtonSourceKappa]) (by norm_num [shrinkingNewtonSourceKappa])
    (variableNewton_source_phase_bound Q S hQ hS) φ b hb hb' hφ V (seamTranspose u) hv j i f e
  change variableCoordinateSourceRow Q S hQ hS (seamTranspose u) ((j,f),(i,e))=
    variableNewtonNormalization shrinkingNewtonSourceKappa ε (rapidDistance Q S) i e j f*_
  simpa only [variableCoordinateSourceRow,variableNewtonNormalization_swap] using h

/-- The entire physical variable coordinate acts on the actual characteristic-adjusted Zak pairing. -/
theorem variableCoordinateSourceRow_chart_bilinear_action (P R Q S : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R)
    (T : TemperedDistribution ℝ ℂ) (φ ψ : SchwartzMap ℝ ℂ) (b : ℝ) (hb : 0 < b) (hb' : b < 1/8)
    (hφ : ∀ x, b ≤ |x| → φ x=0) (u : SeamMomentArray)
    (hu : ∀ i e j f, u ((i,e),(j,f))=chartNewtonReading
      (variableNewtonNormalization shrinkingNewtonSourceKappa (rapidDistance P R) (rapidDistance Q S))
      (fun l => rapidDistance P R l) (fun l => rapidDistance Q S l) T φ ψ i e j f)
    (i j : ℕ) (e f : Bool) :
    variableCoordinateSourceRow P R hP hR u ((i,e),(j,f))=chartNewtonReading
      (variableNewtonNormalization shrinkingNewtonSourceKappa (rapidDistance P R) (rapidDistance Q S))
      (fun l => rapidDistance P R l) (fun l => rapidDistance Q S l) T (mixedSchwartz 1 0 φ) ψ i e j f := by
  let V (j : ℕ) (f : Bool) : TemperedDistribution ℝ ℂ :=
    (zakPhysicalSlice T (combSchwartzModulation (-1/2)
      (schwartzChartProduct ψ (halfNewtonTest (fun l => rapidDistance Q S l) j f)))).comp
      (combSchwartzModulation (1/2))
  exact variableCoordinateRow_chart_slice_action shrinkingNewtonSourceKappa
    (ne_of_gt shrinkingNewtonSourceKappa_pos) (rapidDistance P R) (rapidDistance Q S) (shrinkingNewtonSourceKappa^4)
    (by norm_num [shrinkingNewtonSourceKappa]) (by norm_num [shrinkingNewtonSourceKappa])
    (variableNewton_source_phase_bound P R hP hR) φ b hb hb' hφ V u hu i j e f

/-- The entire spectral variable coordinate acts on the second actual Zak factor. -/
theorem variableCoordinateSourceColumn_chart_bilinear_action (P R Q S : ℕ) (hQ : 1 ≤ Q) (hS : 1 ≤ S)
    (T : TemperedDistribution ℝ ℂ) (φ ψ : SchwartzMap ℝ ℂ) (b : ℝ) (hb : 0 < b) (hb' : b < 1/8)
    (hψ : ∀ x, b ≤ |x| → ψ x=0) (u : SeamMomentArray)
    (hu : ∀ i e j f, u ((i,e),(j,f))=chartNewtonReading
      (variableNewtonNormalization shrinkingNewtonSourceKappa (rapidDistance P R) (rapidDistance Q S))
      (fun l => rapidDistance P R l) (fun l => rapidDistance Q S l) T φ ψ i e j f)
    (i j : ℕ) (e f : Bool) :
    variableCoordinateSourceColumn Q S hQ hS u ((i,e),(j,f))=chartNewtonReading
      (variableNewtonNormalization shrinkingNewtonSourceKappa (rapidDistance P R) (rapidDistance Q S))
      (fun l => rapidDistance P R l) (fun l => rapidDistance Q S l) T φ (mixedSchwartz 1 0 ψ) i e j f := by
  let V (i : ℕ) (e : Bool) : TemperedDistribution ℝ ℂ :=
    (zakTensorSlice T (combSchwartzModulation (1/2)
      (schwartzChartProduct φ (halfNewtonTest (fun l => rapidDistance P R l) i e)))).comp
      (combSchwartzModulation (-1/2))
  have hv : ∀ i e j f, u ((i,e),(j,f))=
      variableNewtonNormalization shrinkingNewtonSourceKappa (rapidDistance P R) (rapidDistance Q S) i e j f*
      V i e (schwartzChartProduct ψ (halfNewtonTest (fun l => rapidDistance Q S l) j f)) := by
    intro i e j f
    change _=variableNewtonNormalization shrinkingNewtonSourceKappa (rapidDistance P R) (rapidDistance Q S) i e j f *
      zakTensorSlice T (combSchwartzModulation (1/2) (schwartzChartProduct φ (halfNewtonTest (fun l => rapidDistance P R l) i e)))
        (combSchwartzModulation (-1/2) (schwartzChartProduct ψ (halfNewtonTest (fun l => rapidDistance Q S l) j f)))
    simpa only [chartNewtonReading,zakTensorSlice_apply,halfNewtonBilinear] using hu i e j f
  have h := variableCoordinateSourceColumn_chart_slice_action Q S hQ hS (rapidDistance P R)
    ψ b hb hb' hψ V u hv i j e f
  change _=variableNewtonNormalization shrinkingNewtonSourceKappa (rapidDistance P R) (rapidDistance Q S) i e j f *
    zakTensorSlice T (combSchwartzModulation (1/2) (schwartzChartProduct φ (halfNewtonTest (fun l => rapidDistance P R l) i e)))
      (combSchwartzModulation (-1/2) (schwartzChartProduct (mixedSchwartz 1 0 ψ) (halfNewtonTest (fun l => rapidDistance Q S l) j f))) at h
  simpa only [chartNewtonReading,zakTensorSlice_apply,halfNewtonBilinear] using h

/-- The genuine entire variable gauge acts on complete compact chart readings. -/
theorem variableGauge_chart_action (P R Q S : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) (hQ : 1 ≤ Q) (hS : 1 ≤ S)
    (T : TemperedDistribution ℝ ℂ) (φ ψ : SchwartzMap ℝ ℂ) (b : ℝ) (hb : 0 < b) (hb' : b < 1/8)
    (hφ : ∀ x, b ≤ |x| → φ x=0) (hψ : ∀ x, b ≤ |x| → ψ x=0) (u : SeamMomentArray)
    (hu : ∀ i e j f, u ((i,e),(j,f))=chartNewtonReading
      (variableNewtonNormalization shrinkingNewtonSourceKappa (rapidDistance P R) (rapidDistance Q S))
      (fun l => rapidDistance P R l) (fun l => rapidDistance Q S l) T φ ψ i e j f)
    (i j : ℕ) (e f : Bool) :
    variableGaugeOperator P R Q S hP hR hQ hS u ((i,e),(j,f))=
      variableNewtonNormalization shrinkingNewtonSourceKappa (rapidDistance P R) (rapidDistance Q S) i e j f*
      halfNewtonGaugeBilinear T (schwartzChartProduct φ (halfNewtonTest (fun l => rapidDistance P R l) i e))
        (schwartzChartProduct ψ (halfNewtonTest (fun l => rapidDistance Q S l) j f)) := by
  exact actualGaugeAction_of_coordinates _ _ _ T _ _ b (hb'.trans (by norm_num))
    (fun φ ψ hφ u hu i e j f => variableCoordinateSourceRow_chart_bilinear_action P R Q S hP hR T φ ψ b hb hb' hφ u hu i j e f)
    (fun φ ψ hψ u hu i e j f => variableCoordinateSourceColumn_chart_bilinear_action P R Q S hQ hS T φ ψ b hb hb' hψ u hu i j e f)
    φ ψ hφ hψ u hu i j e f

end
end MeyerGeneralProblem.Adaptive
