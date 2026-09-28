module

public import MeyerGeneralProblem.Cardinal.Adaptive.EndpointLiteralMoments
public import MeyerGeneralProblem.Cardinal.Adaptive.ShrinkingNewtonTests

@[expose] public section

/-! Fixed-cutoff Newton readings of actual finite endpoint sources, including the seam. -/
noncomputable section
open scoped BigOperators
namespace MeyerGeneralProblem.Adaptive

/-- The complete finite endpoint source has its literal two-variable central reading. -/
theorem halfNewtonBilinear_recentered_endpoint {k : ℕ} (α β : Fin k → ℝ) (c : EndpointMatrix k)
    (ha : ∀ a, |endpointCenteredPhase (fun i => 1/2-α i) a| < 1/2)
    (hb : ∀ b, |endpointCenteredPhase (fun i => 1/2-β i) b| < 1/2)
    (f g : SchwartzMap ℝ ℂ) (hf : ∀ x, 1/2 ≤ |x| → f x=0)
    (hg : ∀ x, 1/2 ≤ |x| → g x=0) :
    halfNewtonBilinear (halfWeylDistributionCLM (endpointPoissonSynthesis α β c)) f g =
      ∑ a, ∑ b, (c a b*endpointCenterFactor α β a b)*
        (combModulationCharacter (1/2) (endpointCenteredPhase (fun i => 1/2-α i) a)*
          combModulationCharacter (-1/2) (endpointCenteredPhase (fun i => 1/2-β i) b))*
        (f (endpointCenteredPhase (fun i => 1/2-α i) a)*
          g (endpointCenteredPhase (fun i => 1/2-β i) b)) := by
  rw [halfNewtonBilinear,← zakSchwartzTranspose_realizes,halfWeyl_endpointPoissonSynthesis]
  simp only [_root_.sum_apply,_root_.smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [zakSchwartzTranspose_realizes]
  change (c a b*endpointCenterFactor α β a b)*halfNewtonBilinear _ f g = _
  rw [halfNewtonBilinear_wholePoisson_central _ _ (ha a) (hb b) f g hf hg]
  ring

/-- A fixed small cutoff reads the same actual finite Newton coordinate whenever
it contains every finite representative, including the single zero seam. -/
theorem halfNewtonBilinear_endpoint_fixed_cutoff {k : ℕ} (α β : Fin k → ℝ) (c : EndpointMatrix k)
    (ε δ : ℕ+ → ℝ) (i j : ℕ) (e d : Bool) (a b : ℝ) (hab : a < b)
    (hb : b ≤ 1/2) (ha : a ≤ 1/4)
    (hα : ∀ u, |endpointCenteredPhase (fun i => 1/2-α i) u| ≤ a)
    (hβ : ∀ v, |endpointCenteredPhase (fun i => 1/2-β i) v| ≤ a) :
    halfNewtonBilinear (halfWeylDistributionCLM (endpointPoissonSynthesis α β c))
      (shrinkingNewtonTest ε i e a b hab) (shrinkingNewtonTest δ j d a b hab) =
      halfNewtonCoordinate ε δ (halfWeylDistributionCLM (endpointPoissonSynthesis α β c)) i e j d := by
  have hα' u : |endpointCenteredPhase (fun i => 1/2-α i) u| < 1/2 := by linarith [hα u]
  have hβ' v : |endpointCenteredPhase (fun i => 1/2-β i) v| < 1/2 := by linarith [hβ v]
  unfold halfNewtonCoordinate
  rw [halfNewtonBilinear_recentered_endpoint α β c hα' hβ' _ _
    (fun x hx => shrinkingNewtonTest_zero ε i e a b hab x (hb.trans hx))
    (fun x hx => shrinkingNewtonTest_zero δ j d a b hab x (hb.trans hx)),
    halfNewtonBilinear_recentered_endpoint α β c hα' hβ' _ _
      (halfNewtonTest_central_zero ε i e) (halfNewtonTest_central_zero δ j d)]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  rw [shrinkingNewtonTest_apply,shrinkingNewtonTest_apply,
    shrinkingTailCutoff_one a b _ hab (hα u),shrinkingTailCutoff_one a b _ hab (hβ v),
    halfNewtonTest_apply,halfNewtonTest_apply,
    zakCentralCutoff_one _ ((hα u).trans ha),zakCentralCutoff_one _ ((hβ v).trans ha)]
  simp only [Complex.ofReal_one,one_mul]

/-- Every actual rapid finite representative fits in the fixed inner radius R/2,
where the accepted coordinate normalization has R=1/4096. -/
theorem endpointCenteredPhase_rapid_fixedRadius {P R : ℕ} (hP : 1 ≤ P) (hR : 1 ≤ R)
    (k : ℕ) (a : EndpointPhaseIndex k) :
    |endpointCenteredPhase (fun i => 1/2-rapidEndpointPhaseData P R k i) a| ≤ 1/8192 := by
  cases a with
  | none => norm_num [endpointCenteredPhase]
  | some a =>
      obtain ⟨i,e⟩ := a
      have hp := (rapidDistance_bounds hP hR (i.val+1)).1
      have hh := rapidDistance_le_small_constant hP hR (i.val+1)
      have he : 1/2-rapidEndpointPhaseData P R k i=rapidDistance P R (i.val+1) := by
        unfold rapidEndpointPhaseData
        ring
      cases e <;> simp only [endpointCenteredPhase,he,Bool.false_eq_true,ite_false,
        ite_true,abs_neg,abs_of_pos hp] <;> exact hh.trans (by norm_num)

/-- Literal fixed-cutoff equality for every actual finite rapid source and every
Newton index, including the zeroth seam and both signed parities. -/
theorem rapidEndpointSource_fixedCutoff_reading {P R : ℕ} (hP : 1 ≤ P) (hR : 1 ≤ R)
    (k : ℕ) (c : EndpointMatrix k) (i j : ℕ) (e d : Bool) :
    halfNewtonBilinear (halfWeylDistributionCLM (endpointPoissonSynthesis
      (rapidEndpointPhaseData P R k) (rapidEndpointPhaseData P R k) c))
      (shrinkingNewtonTest (fun r => rapidDistance P R r.val) i e (1/8192) (1/4096) (by norm_num))
      (shrinkingNewtonTest (fun r => rapidDistance P R r.val) j d (1/8192) (1/4096) (by norm_num)) =
      halfNewtonCoordinate (fun r => rapidDistance P R r.val) (fun r => rapidDistance P R r.val)
        (halfWeylDistributionCLM (endpointPoissonSynthesis
          (rapidEndpointPhaseData P R k) (rapidEndpointPhaseData P R k) c)) i e j d :=
  halfNewtonBilinear_endpoint_fixed_cutoff _ _ c _ _ i j e d _ _ (by norm_num)
    (by norm_num) (by norm_num) (endpointCenteredPhase_rapid_fixedRadius hP hR k)
      (endpointCenteredPhase_rapid_fixedRadius hP hR k)

end MeyerGeneralProblem.Adaptive
