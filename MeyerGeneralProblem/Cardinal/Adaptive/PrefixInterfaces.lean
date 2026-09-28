module

public import MeyerGeneralProblem.Cardinal.Adaptive.Definitions
public import MeyerGeneralProblem.Cardinal.Adaptive.PrefixRecursion
public import MeyerGeneralProblem.Cardinal.Adaptive.RankArithmetic
public import MeyerGeneralProblem.Distribution.CompactSchwartzDensity

@[expose] public section

/-!
# Data selected from a finite deterministic gap prefix

These data record the order of finite-stage choices. They do not assert good
events, partition identities, tail estimates, source classifications or the
existence of a completed carrier. Those are separate proved obligations. A
selection function is given only the positive stage and its earlier gaps.
-/

namespace MeyerGeneralProblem.Adaptive
noncomputable section

/-- Finite-stage choices indexed by the already fixed positive gap prefix.
The next gap and all realized scale coordinates are deliberately absent. -/
structure StepConstants (M : ℕ+) (gaps : GapPrefix M.val) where
  /-- Prefix-only coefficient in the catalogue nonresonance estimate. -/
  catalogueConstant : ℝ
  /-- Positivity of the catalogue coefficient. -/
  catalogueConstant_pos : 0 < catalogueConstant
  /-- Normalization compatible with the quantitative catalogue estimate. -/
  catalogueConstant_le_one : catalogueConstant ≤ 1
  /-- Separation threshold for the finite list of physical periodic closures. -/
  closureGap : ℝ
  /-- Positive closure separation threshold. -/
  closureGap_pos : 0 < closureGap
  /-- Stage normalization for the closure separation threshold. -/
  closureGap_le : closureGap ≤ 1/(M.val:ℝ)
  /-- Positive radius used for local single-closure pieces and head gaps. -/
  pieceRadius : ℝ
  /-- Positive partition scale. -/
  pieceRadius_pos : 0 < pieceRadius
  /-- Pieces are chosen smaller than the closure separation scale. -/
  pieceRadius_lt_gap : pieceRadius < closureGap
  /-- Number of compact smooth partition functions. -/
  partitionSize : ℕ
  /-- Actual Schwartz partition functions; their support and sum laws are separate obligations. -/
  partition : Fin partitionSize → SchwartzMap ℝ ℂ
  /-- Beginning of the forward interval used for the finite torus net. -/
  translationStart : ℝ
  /-- Nonnegative beginning of the translation search. -/
  translationStart_nonneg : 0 ≤ translationStart
  /-- Accuracy requested of the physical phase approximation. -/
  phaseTolerance : ℝ
  /-- Positive phase approximation tolerance. -/
  phaseTolerance_pos : 0 < phaseTolerance
  /-- End of the bounded translation interval, selected before any scale realization. -/
  translationBound : ℝ
  /-- The translation interval contains its prescribed beginning. -/
  translationStart_le : translationStart ≤ translationBound
  /-- Fourier truncation chosen before the catalogue probe radius. -/
  fourierCutoff : ℕ
  /-- The cutoff covers the stage index. -/
  stage_le_cutoff : M.val ≤ fourierCutoff
  /-- Common spatial cutoff paying A, B and J at all orders through M. -/
  spatialCutoff : ℕ

/-- Exact polynomial exponent used in the catalogue isolation estimate. -/
def StepConstants.catalogueExponent {M : ℕ+} {gaps : GapPrefix M.val}
    (_C : StepConstants M gaps) : ℕ := 2*(M.val+1)*(2*M.val+6)

/-- A source-compatible catalogue radius, fixed after the Fourier cutoff. -/
def StepConstants.catalogueRadius {M : ℕ+} {gaps : GapPrefix M.val}
    (C : StepConstants M gaps) : ℝ :=
  (C.catalogueConstant/(10*3^C.catalogueExponent)) /
    (1+(C.fourierCutoff:ℝ))^C.catalogueExponent

/-- Local jet radius is fixed before choosing the next gap. -/
def StepConstants.jetRadius {M : ℕ+} {gaps : GapPrefix M.val}
    (C : StepConstants M gaps) : ℝ := min (C.closureGap/10) (1/(M.val:ℝ))

/-- A selection function has no next-gap, scale-sequence, native-order or source argument. -/
abbrev PrefixStepSelection := ∀ (M : ℕ+) (gaps : GapPrefix M.val),
  (∀ i, 1 ≤ gaps i) → StepConstants M gaps

/-- The next gap must cover the analytic cutoff as well as all source growth demands. -/
def StepConstants.nextGapLowerBound {M : ℕ+} {gaps : GapPrefix M.val}
    (C : StepConstants M gaps) (previous : ℕ) : ℕ :=
  max (nextGapFloor (M.val-1) previous C.translationBound) (6*(C.spatialCutoff+1))

/-- Every chosen catalogue radius is strictly positive. -/
theorem StepConstants.catalogueRadius_pos {M : ℕ+} {gaps : GapPrefix M.val}
    (C : StepConstants M gaps) : 0 < C.catalogueRadius := by
  unfold StepConstants.catalogueRadius
  have := C.catalogueConstant_pos
  positivity

/-- The local jet width is positive, including the first stage. -/
theorem StepConstants.jetRadius_pos {M : ℕ+} {gaps : GapPrefix M.val}
    (C : StepConstants M gaps) : 0 < C.jetRadius := by
  unfold StepConstants.jetRadius
  apply lt_min
  · exact div_pos C.closureGap_pos (by norm_num)
  · exact div_pos zero_lt_one (by exact_mod_cast M.pos)

/-- The next-gap floor enforces all three deterministic growth demands and
covers the already chosen analytic cutoff. -/
theorem StepConstants.nextGapLowerBound_spec {M : ℕ+} {gaps : GapPrefix M.val}
    (C : StepConstants M gaps) (previous R : ℕ) (hR : C.nextGapLowerBound previous ≤ R) :
    2^(M.val+1) ≤ R ∧ 2*previous ≤ R ∧
      6*(C.translationBound+(M.val:ℝ)+2) ≤ (R:ℝ) ∧ 6*(C.spatialCutoff+1) ≤ R := by
  have h := max_le_iff.mp hR
  obtain ⟨h1,h2,h3⟩ := nextGapFloor_spec (M.val-1) previous R C.translationBound h.1
  have hm : M.val-1+1 = M.val := by have := M.pos; omega
  have hm' : M.val-1+2 = M.val+1 := by omega
  refine ⟨by simpa only [hm'] using h1,h2,?_,h.2⟩
  have hmr : ((M.val-1:ℕ):ℝ)+1 = (M.val:ℝ) := by exact_mod_cast hm
  simpa only [hmr] using h3

/-- Finite-prefix extensionality excludes dependence on a later completion. -/
theorem prefixStepSelection_ext (chooseStep : PrefixStepSelection) (M : ℕ+)
    (R S : ℕ → ℕ) (h : ∀ i < M.val, R i = S i)
    (hR : ∀ i : Fin M.val, 1 ≤ R i) (hS : ∀ i : Fin M.val, 1 ≤ S i) :
    HEq (chooseStep M (fun i => R i) hR) (chooseStep M (fun i => S i) hS) := by
  have he : (fun i : Fin M.val => R i) = (fun i : Fin M.val => S i) := funext fun i => h i i.isLt
  have hp : (⟨(fun i : Fin M.val => R i),hR⟩ : {g : GapPrefix M.val // ∀ i, 1 ≤ g i}) =
      ⟨(fun i : Fin M.val => S i),hS⟩ := Subtype.ext he
  have hpack := congrArg (fun g : {g : GapPrefix M.val // ∀ i, 1 ≤ g i} =>
    (⟨g.val,chooseStep M g.val g.property⟩ : Sigma (StepConstants M))) hp
  exact (Sigma.mk.inj_iff.mp hpack).2

end
end MeyerGeneralProblem.Adaptive
