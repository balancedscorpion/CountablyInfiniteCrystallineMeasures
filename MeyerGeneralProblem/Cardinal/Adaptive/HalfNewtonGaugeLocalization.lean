module

public import MeyerGeneralProblem.Cardinal.Adaptive.HalfNewtonGaugeIdentity
public import MeyerGeneralProblem.Cardinal.Adaptive.HalfNewtonGaugeMembership

@[expose] public section

/-! # Exact inner-chart transfer of the analytic half-seam gauge -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open scoped FourierTransform

/-- A smaller fixed cutoff leaves every quarter-cell phase unchanged and has
its entire support strictly inside the half-cell. -/
def zakInnerBump : ContDiffBump (0 : ℝ) where
  rIn := 1/4
  rOut := 3/8
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- Genuine compact Schwartz realization of the smaller fixed cutoff. -/
def zakInnerCutoff : SchwartzMap ℝ ℂ :=
  (zakInnerBump.hasCompactSupport.comp_left (show ((0 : ℝ) : ℂ)=0 by rfl)).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp zakInnerBump.contDiff)

/-- The smaller cutoff is exactly one on the complete phase quarter-cell. -/
theorem zakInnerCutoff_one (x : ℝ) (hx : |x| ≤ 1/4) : zakInnerCutoff x=1 := by
  change (zakInnerBump x : ℂ)=1
  rw [zakInnerBump.one_of_mem_closedBall]
  · norm_num
  · simpa only [Metric.mem_closedBall,Real.dist_eq,sub_zero,zakInnerBump] using hx

/-- The smaller cutoff vanishes outside radius three eighths. -/
theorem zakInnerCutoff_zero (x : ℝ) (hx : 3/8 ≤ |x|) : zakInnerCutoff x=0 := by
  change (zakInnerBump x : ℂ)=0
  rw [zakInnerBump.zero_of_le_dist]
  · norm_num
  · simpa only [Real.dist_eq,sub_zero,zakInnerBump] using hx

/-- Actual multiplication by the smaller fixed Schwartz cutoff. -/
def zakInnerLocalize (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.smulLeftCLM ℂ (zakInnerCutoff : ℝ → ℂ) f

/-- Localization preserves all quarter-cell values exactly. -/
theorem zakInnerLocalize_eq (f : SchwartzMap ℝ ℂ) (x : ℝ) (hx : |x| ≤ 1/4) :
    zakInnerLocalize f x=f x := by
  rw [zakInnerLocalize,SchwartzMap.smulLeftCLM_apply_apply zakInnerCutoff.hasTemperateGrowth,
    zakInnerCutoff_one x hx,one_smul]

/-- Every localized test has the strict half-cell support required by the
native Taylor series estimate. -/
theorem zakInnerLocalize_zero (f : SchwartzMap ℝ ℂ) (x : ℝ) (hx : 3/8 ≤ |x|) :
    zakInnerLocalize f x=0 := by
  rw [zakInnerLocalize,SchwartzMap.smulLeftCLM_apply_apply zakInnerCutoff.hasTemperateGrowth,
    zakInnerCutoff_zero x hx,zero_smul]

/-- The complete Fourier companion pairing permits independent replacement
of both central tests by their actual signed phase values. -/
theorem halfNewtonFourierBilinear_eq_of_phase_values (α β : ℕ+ → ℝ)
    (hia : ∀ j, 0 < α j ∧ α j < 1/2) (hib : ∀ j, 0 < β j ∧ β j < 1/2)
    (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier (criticalPhaseTailCarrier α hia 0 0) T)
    (hFT : AtomicOnCarrier (criticalPhaseTailCarrier β hib 0 0) (𝓕 T))
    (f f' g g' : SchwartzMap ℝ ℂ)
    (hf : ∀ x : ℝ, 1/2 ≤ |x| → f x=0) (hf' : ∀ x : ℝ, 1/2 ≤ |x| → f' x=0)
    (hg : ∀ x : ℝ, 1/2 ≤ |x| → g x=0) (hg' : ∀ x : ℝ, 1/2 ≤ |x| → g' x=0)
    (he : ∀ j, f (1/2-α j)=f' (1/2-α j) ∧ f (-(1/2-α j))=f' (-(1/2-α j)))
    (he' : ∀ j, g (1/2-β j)=g' (1/2-β j) ∧ g (-(1/2-β j))=g' (-(1/2-β j))) :
    halfNewtonFourierBilinear T f g=halfNewtonFourierBilinear T f' g' := by
  obtain ⟨hp,hq⟩ := halfWeylFourierCompanion_atomic_records α β hia hib T hT hFT
  unfold halfNewtonFourierBilinear
  apply halfNewtonBilinear_eq_of_phase_values β α hib hia (halfWeylFourierCompanion T) hp hq
    g g' (schwartzReflectionCLM f) (schwartzReflectionCLM f') hg hg'
  · intro x hx
    rw [schwartzReflectionCLM_apply]
    exact hf (-x) (by simpa only [abs_neg] using hx)
  · intro x hx
    rw [schwartzReflectionCLM_apply]
    exact hf' (-x) (by simpa only [abs_neg] using hx)
  · exact he'
  · intro j
    simpa only [schwartzReflectionCLM_apply,neg_neg] using (he j).symm

/-- Exact phase replacement extends the complete analytic gauge identity to
all central tests of the original paired source. -/
theorem halfNewtonGaugeBilinear_eq_FourierBilinear_central (α β : ℕ+ → ℝ)
    (hia : ∀ j, 0 < α j ∧ α j < 1/2) (hib : ∀ j, 0 < β j ∧ β j < 1/2)
    (ha : ∀ j, 1/4 ≤ α j) (hb : ∀ j, 1/4 ≤ β j)
    (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier (criticalPhaseTailCarrier α hia 0 0) T)
    (hFT : AtomicOnCarrier (criticalPhaseTailCarrier β hib 0 0) (𝓕 T))
    (f g : SchwartzMap ℝ ℂ)
    (hf : ∀ x : ℝ, 1/2 ≤ |x| → f x=0) (hg : ∀ x : ℝ, 1/2 ≤ |x| → g x=0) :
    halfNewtonGaugeBilinear (halfWeylDistributionCLM T) f g=
      halfNewtonFourierBilinear T f g := by
  have hs (u : SchwartzMap ℝ ℂ) : ∀ x : ℝ, 1/2 ≤ |x| → zakInnerLocalize u x=0 := by
    intro x hx
    exact zakInnerLocalize_zero u x (by linarith)
  have hv (γ : ℕ+ → ℝ) (hi : ∀ j, 0 < γ j ∧ γ j < 1/2)
      (hh : ∀ j, 1/4 ≤ γ j) (u : SchwartzMap ℝ ℂ) :
      ∀ j, u (1/2-γ j)=zakInnerLocalize u (1/2-γ j) ∧
        u (-(1/2-γ j))=zakInnerLocalize u (-(1/2-γ j)) := by
    intro j
    have hq : |1/2-γ j| ≤ 1/4 := by
      rw [abs_of_pos (by linarith [(hi j).2])]
      linarith [hh j]
    exact ⟨(zakInnerLocalize_eq u _ hq).symm,
      (zakInnerLocalize_eq u _ (by simpa only [abs_neg] using hq)).symm⟩
  obtain ⟨hp,hq⟩ := halfWeylDistribution_atomic_records α β hia hib T hT hFT
  calc
    _ = halfNewtonGaugeBilinear (halfWeylDistributionCLM T) (zakInnerLocalize f) (zakInnerLocalize g) :=
      halfNewtonGaugeBilinear_eq_of_phase_values α β hia hib _ hp hq f _ g _
        hf (hs f) hg (hs g) (hv α hia ha f) (hv β hib hb g)
    _ = halfNewtonFourierBilinear T (zakInnerLocalize f) (zakInnerLocalize g) :=
      halfNewtonGaugeBilinear_eq_FourierBilinear T _ _ (3/8) (by norm_num)
        (zakInnerLocalize_zero f) (zakInnerLocalize_zero g)
    _ = halfNewtonFourierBilinear T f g :=
      (halfNewtonFourierBilinear_eq_of_phase_values α β hia hib T hT hFT f _ g _
        hf (hs f) hg (hs g) (hv α hia ha f) (hv β hib hb g)).symm

/-- The complete fixed-normalized Newton gauge array equals the actual
Fourier moment array, including both parity factors. -/
theorem halfNewtonGaugeMoment_eq_FourierMoment (α β : ℕ+ → ℝ)
    (hia : ∀ j, 0 < α j ∧ α j < 1/2) (hib : ∀ j, 0 < β j ∧ β j < 1/2)
    (ha : ∀ j, 1/4 ≤ α j) (hb : ∀ j, 1/4 ≤ β j)
    (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier (criticalPhaseTailCarrier α hia 0 0) T)
    (hFT : AtomicOnCarrier (criticalPhaseTailCarrier β hib 0 0) (𝓕 T))
    (i j : ℕ) (e f : Bool) :
    (((1/4096 : ℂ)^(i+j)*(1/64 : ℂ)^(e.toNat+f.toNat))⁻¹)*
      halfNewtonGaugeBilinear (halfWeylDistributionCLM T)
        (halfNewtonTest (fun l => 1/2-α l) i e) (halfNewtonTest (fun l => 1/2-β l) j f)=
      halfNewtonFourierMoment (fun l => 1/2-α l) (fun l => 1/2-β l) T i e j f := by
  unfold halfNewtonFourierMoment
  rw [halfNewtonGaugeBilinear_eq_FourierBilinear_central α β hia hib ha hb T hT hFT]
  all_goals intro x hx; rw [halfNewtonTest_apply,zakCentralCutoff_zero x hx,zero_mul]

end
end MeyerGeneralProblem.Adaptive
