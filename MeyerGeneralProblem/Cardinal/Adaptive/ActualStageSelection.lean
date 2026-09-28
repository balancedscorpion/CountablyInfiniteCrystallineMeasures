module

public import MeyerGeneralProblem.Cardinal.Adaptive.CatalogueEvents
public import MeyerGeneralProblem.Cardinal.Adaptive.PrefixGeometryParameters
public import MeyerGeneralProblem.Cardinal.Adaptive.StagePhaseParameters
public import MeyerGeneralProblem.Cardinal.Adaptive.StageTailAssembly
public import MeyerGeneralProblem.Cardinal.Adaptive.ReciprocalAnnihilatorProduct

@[expose] public section

/-! # Actual prefix-only selection of every finite-stage parameter -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open MeasureTheory
open scoped ContDiff

/-- The complete annihilator family for the actual positive prefix labels. -/
def stageAnnihilatorFunctions (M : ℕ+) (gaps : GapPrefix M.val)
    (hgaps : ∀ i, 1 ≤ gaps i) : Fin (M.val+M.val) → ℝ → ℂ :=
  reciprocalProductFunctions M.val (fun i => i.val+1) gaps (fun _ => Nat.succ_pos _) hgaps

/-- Every actual prefix annihilator is smooth. -/
theorem stageAnnihilatorFunctions_smooth (M : ℕ+) (gaps : GapPrefix M.val)
    (hgaps : ∀ i, 1 ≤ gaps i) (j : Fin (M.val+M.val)) :
    ContDiff ℝ ∞ (stageAnnihilatorFunctions M gaps hgaps j) :=
  reciprocalProductFunctions_smooth _ _ _ _ _ j

/-- Every actual prefix annihilator is one-periodic. -/
theorem stageAnnihilatorFunctions_periodic (M : ℕ+) (gaps : GapPrefix M.val)
    (hgaps : ∀ i, 1 ≤ gaps i) (j : Fin (M.val+M.val)) :
    Function.Periodic (stageAnnihilatorFunctions M gaps hgaps j) 1 :=
  reciprocalProductFunctions_periodic _ _ _ _ _ j

/-- Proved laws for the actual choices, kept separate from the parameter data.
All probability bounds hold for every later completion of the same prefix. -/
structure ActualStepLaws (ψ : SchwartzMap ℝ ℂ) (M : ℕ+) (gaps : GapPrefix M.val)
    (hgaps : ∀ i, 1 ≤ gaps i) (C : StepConstants M gaps) : Prop where
  /-- The actual full catalogue event has the prescribed probability bound. -/
  catalogue : ∀ R : ℕ+ → ℕ, (∀ i, R (prefixScaleIndex i) = gaps i) →
    scaleProbability (dyadicCatalogueBadEvent R M.val C.catalogueConstant) ≤
      ENNReal.ofReal ((2:ℝ)^(-(M.val+4:ℤ)))
  /-- Actual physical closures satisfy the prescribed probability bound. -/
  closures : ∀ R : ℕ+ → ℕ, (∀ i, R (prefixScaleIndex i) = gaps i) →
    scaleProbability (finitePeriodicCloseEvent R (finitePrefixLabels M.val)
      ((M:ℝ)+2) C.closureGap) ≤ ENNReal.ofReal ((2:ℝ)^(-(M.val+4:ℤ)))
  /-- Head gaps and closure separation jointly determine the partition radius. -/
  radius : C.pieceRadius = prefixPieceRadius M gaps C.closureGap
  /-- Every partition piece has compact support. -/
  compact : ∀ i, HasCompactSupport (C.partition i)
  /-- Every partition piece stays in the enlarged testing window. -/
  support : ∀ i, tsupport (C.partition i) ⊆ Set.Icc (-(M:ℝ)-1) ((M:ℝ)+1)
  /-- Every piece is narrower than the prescribed separation scale. -/
  diameter : ∀ i, ∀ x ∈ tsupport (C.partition i), ∀ y ∈ tsupport (C.partition i),
    |x-y| < C.pieceRadius
  /-- The partition sums to one on the whole test window. -/
  sum_one : ∀ x ∈ Set.Icc (-(M:ℝ)) (M:ℝ), ∑ i, C.partition i x = 1
  /-- The partition is real and nonnegative. -/
  nonnegative : ∀ i x, (C.partition i x).im = 0 ∧ 0 ≤ (C.partition i x).re
  /-- The total partition weight is globally at most one. -/
  sum_le : ∀ x, ∑ i, (C.partition i x).re ≤ 1
  /-- The entire translation interval lies past the stage window. -/
  start : (M:ℝ)+1 ≤ C.translationStart
  /-- Phase error stays below the physical partition scale. -/
  phase_radius : C.phaseTolerance ≤ C.pieceRadius/10
  /-- Phase error has the prescribed stage normalization. -/
  phase_stage : C.phaseTolerance ≤ 1/(M:ℝ)
  /-- Every permitted polynomial degree has its actual leading error paid. -/
  leading : ∀ p ≤ M.val, ∀ D ≤ 12*p,
    stageLeadingErrorConstant p D C.partitionSize (2*M.val) C.partition M (by positivity) /
      C.translationStart ≤ (2:ℝ)^(-(M.val:ℤ)) / stageCoefficientCount M.val
  /-- Every permitted native order has its actual phase error paid. -/
  phase : ∀ p ≤ M.val,
    stagePhaseErrorConstant p C.partitionSize (2*M.val) C.partition M ((M:ℝ)+4)
      (by positivity) (by positivity) * C.phaseTolerance ≤
      (2:ℝ)^(-(M.val:ℤ)) / stageCoefficientCount M.val
  /-- The bounded interval supplies the genuine torus net outside its small bad event. -/
  net : scaleProbability (prefixSegmentNetEvent M.val C.translationStart
      C.translationBound (C.phaseTolerance/4))ᶜ ≤ ENNReal.ofReal ((2:ℝ)^(-(M.val+4:ℤ)))
  /-- The full omitted Fourier series is small at the subsequently chosen probe radius. -/
  fourier_tail : CatalogueTailPaid M.val (M.val+M.val) C.catalogueExponent C.fourierCutoff
    (stageAnnihilatorFunctions M gaps hgaps) (stageAnnihilatorFunctions_smooth M gaps hgaps)
    ψ (2*(M:ℝ)+1) (C.catalogueConstant/(10*3^C.catalogueExponent)) ((2:ℝ)^(-(M.val:ℤ)))
    (by have := C.catalogueConstant_pos; positivity)
  /-- Budget A uses the full annihilator and the actual shrinking catalogue radius. -/
  catalogue_spatial : CatalogueSpatialPaid M.val (M.val+M.val) C.spatialCutoff
    (stageAnnihilatorFunctions M gaps hgaps) ψ (2*(M:ℝ)+1) C.catalogueRadius
    ((2:ℝ)^(-(M.val:ℤ))) C.catalogueRadius_pos
  /-- Budget B uses only the prescribed finite derivative class. -/
  translated_spatial : TranslatedTestSpatialPaid M.val C.partitionSize C.spatialCutoff
    C.partition (2*(M:ℝ)+1) C.translationBound ((2:ℝ)^(-(M.val:ℤ)))
  /-- Budget J uses the fixed closure-gap jet width. -/
  jet_spatial : JetSpatialPaid M.val C.spatialCutoff ψ (2*(M:ℝ)+1) C.jetRadius
    ((2:ℝ)^(-(M.val:ℤ))) C.jetRadius_pos

/-- Every finite positive gap prefix determines actual parameter data satisfying
all geometric, probability, phase and tail laws, before a scale tuple or source
is realized. This constructs the analytic inputs to the deterministic recursion. -/
theorem exists_actualStep (ψ : SchwartzMap ℝ ℂ) (M : ℕ+) (gaps : GapPrefix M.val)
    (hgaps : ∀ i, 1 ≤ gaps i) :
    ∃ C : StepConstants M gaps, ActualStepLaws ψ M gaps hgaps C := by
  obtain ⟨c,hc,hc1,hcat⟩ := exists_prefix_nonresonance_stage_bound M.val gaps hgaps
  obtain ⟨γ,hγ,hγM,hgap⟩ := exists_stage_closure_gap M.val M.pos gaps hgaps
  let ρ := prefixPieceRadius M gaps γ
  have hρ := prefixPieceRadius_spec M gaps hgaps γ hγ
  obtain ⟨J,ζ,hcompact,hsupport,hdiam,hsum,hnonneg,hsumle⟩ :=
    exists_finite_schwartz_partition (M:ℝ) ρ hρ.1
  obtain ⟨H₀,η,H,hH₀,hη,hηρ,hηM,hH,hlead,hphase,hnet⟩ :=
    exists_stage_phase_parameters_and_net M J ζ ρ hρ.1
  let β := 2*(M.val+1)*(2*M.val+6)
  let a := c/(10*3^β)
  have ha : 0 < a := by dsimp [a]; positivity
  have ha1 : a ≤ 1 := by
    apply (div_le_iff₀ (by positivity : (0:ℝ)<10*3^β)).mpr
    have hpow : (1:ℝ) ≤ 3^β := one_le_pow₀ (by norm_num)
    linarith
  let δJ := min (γ/10) (1/(M:ℝ))
  have hδJ : 0 < δJ := by dsimp [δJ]; positivity
  have hHnonneg : 0 ≤ H := (le_trans (le_trans (by positivity) hH₀) hH)
  obtain ⟨L,N,R,hML,_,_,hfourier,hA,hB,hJ⟩ := exists_stage_tail_choices M.val (M.val+M.val) J β 0
    (stageAnnihilatorFunctions M gaps hgaps) (stageAnnihilatorFunctions_smooth M gaps hgaps)
    (stageAnnihilatorFunctions_periodic M gaps hgaps) ψ ζ (2*(M:ℝ)+1) H a δJ
    ((2:ℝ)^(-(M.val:ℤ))) (by positivity) hHnonneg ha ha1 hδJ (by positivity)
  let C : StepConstants M gaps := {
    catalogueConstant := c, catalogueConstant_pos := hc, catalogueConstant_le_one := hc1
    closureGap := γ, closureGap_pos := hγ, closureGap_le := hγM
    pieceRadius := ρ, pieceRadius_pos := hρ.1, pieceRadius_lt_gap := hρ.2.1
    partitionSize := J, partition := ζ
    translationStart := H₀, translationStart_nonneg := le_trans (by positivity) hH₀
    phaseTolerance := η, phaseTolerance_pos := hη
    translationBound := H, translationStart_le := hH
    fourierCutoff := L, stage_le_cutoff := hML, spatialCutoff := N }
  refine ⟨C,⟨hcat,hgap,rfl,hcompact,hsupport,hdiam,hsum,hnonneg,hsumle,
    hH₀,hηρ,hηM,hlead,hphase,hnet,hfourier,?_,hB,hJ⟩⟩
  exact hA

/-- A single fixed template yields a prefix-only choice function with no source
or realized scale argument. -/
def actualStepSelection (ψ : SchwartzMap ℝ ℂ) : PrefixStepSelection :=
  fun M gaps hgaps => Classical.choose (exists_actualStep ψ M gaps hgaps)

/-- Every chosen stage satisfies the actual proved laws. -/
theorem actualStepSelection_laws (ψ : SchwartzMap ℝ ℂ) (M : ℕ+) (gaps : GapPrefix M.val)
    (hgaps : ∀ i, 1 ≤ gaps i) :
    ActualStepLaws ψ M gaps hgaps (actualStepSelection ψ M gaps hgaps) :=
  Classical.choose_spec (exists_actualStep ψ M gaps hgaps)

end
end MeyerGeneralProblem.Adaptive
