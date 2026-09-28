module

public import MeyerGeneralProblem.Cardinal.Adaptive.VariableSourceFlags

@[expose] public section

/-! Exclusion in the original native order for the complete rapid critical source. -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open scoped FourierTransform

/-- The complete rapid critical source has no nonzero vector in original H_-p
when p≤P. The proof constructs both actual variable-weight arrays, derives their
full gauge and signed flags from both original atomic records, applies the bounded
whole-operator estimate, and recovers the whole source by coordinate faithfulness. -/
theorem rapidNativeSource_eq_zero (P R p : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) (hp : p ≤ P)
    (T : HermiteScale (-(p:ℤ)))
    (hT : AtomicOnCarrier (criticalPhaseTailCarrier (shrinkingRapidPhase P R)
      (shrinkingRapidPhase_mem P R hP hR) 0 0) (hermiteScaleDistribution p T))
    (hFT : AtomicOnCarrier (criticalPhaseTailCarrier (shrinkingRapidPhase P R)
      (shrinkingRapidPhase_mem P R hP hR) 0 0) (𝓕 (hermiteScaleDistribution p T))) : T=0 := by
  let W := halfWeylNativeCLM p T
  have hW : hermiteScaleDistribution p W=halfWeylDistributionCLM (hermiteScaleDistribution p T) :=
    halfWeylNativeCLM_realizes p T
  obtain ⟨hw,hfw⟩ := halfWeylDistribution_atomic_records _ _
    (shrinkingRapidPhase_mem P R hP hR) (shrinkingRapidPhase_mem P R hP hR)
    (hermiteScaleDistribution p T) hT hFT
  rw [←hW] at hw hfw
  let u := sourceShrinkingNewtonArray P R p hP hR hp W hw hfw
  let v := sourceShrinkingGaugeNewtonArray P R p hP hR hp W hw hfw
  have hu (i : ℕ) (e : Bool) (j : ℕ) (f : Bool) : u ((i,e),(j,f))=
      shrinkingNewtonMomentWithScale shrinkingNewtonSourceKappa (rapidDistance P R) (rapidDistance P R)
        (hermiteScaleDistribution p W) i e j f := rfl
  have hv (i : ℕ) (e : Bool) (j : ℕ) (f : Bool) : v ((i,e),(j,f))=
      variableFourierMoment shrinkingNewtonSourceKappa (rapidDistance P R) (rapidDistance P R)
        (hermiteScaleDistribution p T) i e j f := by
    change shrinkingNewtonGaugeMomentWithScale _ _ _ _ _ _ _ _=_
    rw [hW,variableGaugeMoment_eq_FourierMoment P R P R hP hR hP hR _ _ hT hFT]
  have huf : ∀ i j e f, j < i → u ((i,e),(j,f))=0 := by
    intro i j e f hij
    rw [hu]
    exact variableMoment_upper_flag P R P R hP hR hP hR _ _ hw hfw i j e f hij
  have hud : ∀ i, u ((i,true),(i,false))=Complex.I*(variableSourceTangent P R i:ℂ)*u ((i,false),(i,true)) ∧
      u ((i,true),(i,true))=(-Complex.I*(variableSourceTangent P R i:ℂ)/(shrinkingNewtonSourceKappa:ℂ)^2)*u ((i,false),(i,false)) := by
    intro i
    simp only [hu]
    exact variableMoment_diagonal_relations P R P R hP hR hP hR _
      (ne_of_gt shrinkingNewtonSourceKappa_pos) _ hw hfw i
  have hvf : ∀ i j e f, i < j → v ((i,e),(j,f))=0 := by
    intro i j e f hij
    rw [hv]
    exact variableFourierMoment_lower_flag P R P R hP hR hP hR _ _ hT hFT i j e f hij
  have hvd : ∀ i, v ((i,false),(i,true))=-Complex.I*(variableSourceTangent P R i:ℂ)*v ((i,true),(i,false)) ∧
      v ((i,true),(i,true))=(Complex.I*(variableSourceTangent P R i:ℂ)/(shrinkingNewtonSourceKappa:ℂ)^2)*v ((i,false),(i,false)) := by
    intro i
    simp only [hv]
    exact variableFourierMoment_diagonal_relations P R P R hP hR hP hR _
      (ne_of_gt shrinkingNewtonSourceKappa_pos) _ hT hFT i
  have hE : variableGaugeOperator P R P R hP hR hP hR u=v :=
    variableGauge_actualArrays P R p hP hR hp W hw hfw
  have hz := (variableSignedArrays_zero P R P R hP hR hP hR u v huf hud hvf hvd hE).1
  have hcoords : ∀ i e j f, halfNewtonCoordinate (fun l => rapidDistance P R l)
      (fun l => rapidDistance P R l) (hermiteScaleDistribution p W) i e j f=0 := by
    intro i e j f
    have hh : u ((i,e),(j,f))=0 := by rw [hz]; rfl
    rw [hu,shrinkingNewtonMomentWithScale_normalization] at hh
    exact (mul_eq_zero.mp hh).resolve_left (variableNewtonNormalization_ne_zero _
      (ne_of_gt shrinkingNewtonSourceKappa_pos) _ _
      (fun n => (variableNewton_source_phase_bound P R hP hR n).1)
      (fun n => (variableNewton_source_phase_bound P R hP hR n).1) i j e f)
  have hzero := halfNewtonCoordinates_faithful _ _ _ _
    (shrinkingRapidPhase_mem P R hP hR) (shrinkingRapidPhase_mem P R hP hR)
    (variableSourcePhase_ge_quarter P R hP hR) (variableSourcePhase_ge_quarter P R hP hR)
    (hermiteScaleDistribution p W) hw hfw hcoords
  rw [hW] at hzero
  have htzero : hermiteScaleDistribution p T=0 := halfWeylDistribution_injective (by simpa only [map_zero] using hzero)
  apply hermiteScaleDistribution_injective p
  simpa only [← hermiteScaleDistributionCLM_apply,map_zero] using htzero

end
end MeyerGeneralProblem.Adaptive
