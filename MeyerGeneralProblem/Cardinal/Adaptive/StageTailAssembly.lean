module

public import MeyerGeneralProblem.Cardinal.Adaptive.CatalogueTailBudget
public import MeyerGeneralProblem.Cardinal.Adaptive.JetTailBudget
public import MeyerGeneralProblem.Cardinal.Adaptive.TranslatedTestTailBudget

@[expose] public section

/-! # Simultaneous finite-stage choices for the three analytic tail budgets -/

namespace MeyerGeneralProblem.Adaptive
noncomputable section
open scoped ContDiff FourierTransform

/-- The exact omitted-series budget at a fixed stage and cutoff. -/
def CatalogueTailPaid (M q β L : ℕ) (g : Fin q → ℝ → ℂ)
    (hg : ∀ j, ContDiff ℝ ∞ (g j)) (ψ : SchwartzMap ℝ ℂ)
    (H a ε : ℝ) (ha : 0 < a) : Prop :=
  ∀ p ≤ M, ∀ s : Fin q → ℝ, (∀ j, |s j| ≤ 2) →
    ∀ y : ℝ, |y| ≤ H → ∀ T : HermiteScale (-(p:ℤ)),
    ‖hermiteScaleDistribution p
      (fourierTranslationTail q p (fun j => periodicCoefficient (g j) (hg j)) s L T)
      (shrinkingBump ψ y (polynomialIsolationRadius a β L)
        (polynomialIsolationRadius_pos ha β L))‖ ≤ ε*‖T‖

/-- Budget A on the actual complete family of Fourier-transformed catalogue bumps. -/
def CatalogueSpatialPaid (M q N : ℕ) (g : Fin q → ℝ → ℂ)
    (ψ : SchwartzMap ℝ ℂ) (H δ ε : ℝ) (hδ : 0 < δ) : Prop :=
  ∀ p ≤ M, ∀ inverse : Bool, ∀ y : ℝ, |y| ≤ H →
    ∀ s : Fin q → ℝ, (∀ j, |s j| ≤ 2) →
    let f := if inverse then 𝓕⁻ (shrinkingBump ψ y δ hδ) else 𝓕 (shrinkingBump ψ y δ hδ)
    ‖schwartzToHermiteScale p (SchwartzMap.smulLeftCLM ℂ (fun x => ∏ j, g j (s j*x))
      (f-compactSchwartzApproximation N f))‖ < ε

/-- Budget B for precisely the fixed-Kp compact test class and finite partition. -/
def TranslatedTestSpatialPaid (M J N : ℕ) (ζ : Fin J → SchwartzMap ℝ ℂ)
    (H S ε : ℝ) : Prop :=
  ∀ p ≤ M, ∀ j : Fin J, ∀ f : SchwartzMap ℝ ℂ,
    tsupport f ⊆ Set.Icc (-H) H →
    (∀ r ≤ testOrder p, ∀ x, ‖iteratedDeriv r (f : ℝ → ℂ) x‖ ≤ 1) →
    ∀ h : ℝ, |h| ≤ S → ∀ inverse : Bool,
    let v := combSchwartzTranslation h (SchwartzMap.smulLeftCLM ℂ (ζ j) f)
    let F := if inverse then 𝓕⁻ v else 𝓕 v
    ‖schwartzToHermiteScale (6*p) (F-compactSchwartzApproximation N F)‖ < ε/(1+(J:ℝ))

/-- Budget J on the actual normalized jet probes with fixed positive width. -/
def JetSpatialPaid (M N : ℕ) (ψ : SchwartzMap ℝ ℂ)
    (H δ ε : ℝ) (hδ : 0 < δ) : Prop :=
  ∀ p ≤ M, ∀ r ≤ 12*p, ∀ inverse : Bool, ∀ y : ℝ, |y| ≤ H →
    let f := if inverse then 𝓕⁻ (localJetProbe ψ δ hδ r y)
      else 𝓕 (localJetProbe ψ δ hδ r y)
    ‖schwartzToHermiteScale (6*p) (f-compactSchwartzApproximation N f)‖ < ε

/-- All analytic choices are made from already fixed finite-stage data. The
Fourier cutoff comes before its shrinking radius and the spatial cutoff;
one sufficiently large next gap then pays A, B and J for every p≤M. -/
theorem exists_stage_tail_choices (M q J β floor : ℕ) (g : Fin q → ℝ → ℂ)
    (hg : ∀ j, ContDiff ℝ ∞ (g j)) (hp : ∀ j, Function.Periodic (g j) 1)
    (ψ : SchwartzMap ℝ ℂ) (ζ : Fin J → SchwartzMap ℝ ℂ)
    (H S a δJ ε : ℝ) (hH : 0 ≤ H) (hS : 0 ≤ S)
    (ha : 0 < a) (ha1 : a ≤ 1) (hδJ : 0 < δJ) (hε : 0 < ε) :
    ∃ L N R : ℕ, M ≤ L ∧ floor ≤ R ∧ 6*(N+1) ≤ R ∧
      CatalogueTailPaid M q β L g hg ψ H a ε ha ∧
      CatalogueSpatialPaid M q N g ψ H (polynomialIsolationRadius a β L) ε
        (polynomialIsolationRadius_pos ha β L) ∧
      TranslatedTestSpatialPaid M J N ζ H S ε ∧ JetSpatialPaid M N ψ H δJ ε hδJ := by
  obtain ⟨L,hML,hL⟩ := exists_periodic_catalogue_cutoff M q β g hg ψ H a ε hH ha ha1 hε
  have hA := exists_catalogue_spatial_budget M q g hg hp ψ H
    (polynomialIsolationRadius a β L) ε hH (polynomialIsolationRadius_pos ha β L) hε
  obtain ⟨NA,hNA⟩ := hA
  obtain ⟨NB,hNB⟩ := exists_fixed_regularity_translated_budget M J ζ H S ε hH hS hε
  obtain ⟨NJ,hNJ⟩ := exists_local_jet_spatial_budget M ψ δJ H ε hδJ hH hε
  let N := max NA (max NB NJ)
  let R := max floor (6*(N+1))
  refine ⟨L,N,R,hML,le_max_left _ _,le_max_right _ _,hL L le_rfl,?_,?_,?_⟩
  · exact hNA N (le_max_left _ _)
  · exact hNB N ((le_max_left NB NJ).trans (le_max_right NA _))
  · exact hNJ N ((le_max_right NB NJ).trans (le_max_right NA _))

end
end MeyerGeneralProblem.Adaptive
