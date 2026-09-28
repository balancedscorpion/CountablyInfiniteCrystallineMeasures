module

public import MeyerGeneralProblem.Cardinal.Adaptive.HalfNewtonCoordinates

@[expose] public section

/-! # Exact shrinking-chart replacement for whole half-seam Newton readings -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open scoped FourierTransform

private theorem central_integer_translate_zero (g : SchwartzMap ℝ ℂ)
    (hg : ∀ x : ℝ, 1/2 ≤ |x| → g x=0) (a : ℝ) (ha : |a| < 1/2)
    (hga : g a=0) (n : ℤ) : g ((n : ℝ)+a)=0 := by
  by_cases hn : n=0
  · simpa only [hn,Int.cast_zero,zero_add] using hga
  · apply hg
    have hnabs : (1 : ℝ) ≤ |(n : ℝ)| := by
      by_cases hp : 0 ≤ n
      · have h : (1 : ℤ) ≤ n := by omega
        have hr : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
        rw [abs_of_nonneg (by positivity)]
        exact hr
      · have h : n ≤ (-1 : ℤ) := by omega
        have hr : (n : ℝ) ≤ -1 := by exact_mod_cast h
        rw [abs_of_nonpos (by linarith)]
        linarith
    have h := abs_add_le ((n : ℝ)+a) (-a)
    simp only [add_neg_cancel_right,abs_neg] at h
    linarith

/-- Vanishing on all signed spectral phases annihilates the whole physical
Zak slice, with both infinite critical threshold branches retained. -/
theorem zakPhysicalSlice_halfWeyl_central_zero (β : ℕ+ → ℝ)
    (hib : ∀ j, 0 < β j ∧ β j < 1/2) (T : TemperedDistribution ℝ ℂ)
    (hFT : AtomicOnCarrier ((criticalPhaseTailCarrier β hib 0 0).translate (-1/2)) (𝓕 T))
    (g : SchwartzMap ℝ ℂ) (hg : ∀ x : ℝ, 1/2 ≤ |x| → g x=0)
    (hphase : ∀ j, g (1/2-β j)=0 ∧ g (-(1/2-β j))=0) :
    zakPhysicalSlice T g=0 := by
  apply zakPhysicalSlice_zero_of_spectral_vanishing _ T hFT g
  intro m x hx
  rw [halfWeylCriticalSet_eq_translate] at hx
  rcases hx with ⟨j,n,hn,rfl⟩|⟨j,n,hn,rfl⟩
  · have ha : |-(1/2-β j)| < 1/2 := by
      rw [abs_neg,abs_of_pos (by linarith [(hib j).2])]
      linarith [(hib j).1]
    have he : (n : ℝ)-(1/2-β j)+(m : ℝ)=((n+m : ℤ) : ℝ)+(-(1/2-β j)) := by
      push_cast
      ring
    rw [he]
    exact central_integer_translate_zero g hg _ ha (hphase j).2 (n+m)
  · have ha : |1/2-β j| < 1/2 := by
      rw [abs_of_pos (by linarith [(hib j).2])]
      linarith [(hib j).1]
    have he : (n : ℝ)+(1/2-β j)+(m : ℝ)=((n+m : ℤ) : ℝ)+(1/2-β j) := by
      push_cast
      ring
    rw [he]
    exact central_integer_translate_zero g hg _ ha (hphase j).1 (n+m)

/-- Equal values on every signed physical phase give identical whole readings. -/
theorem zakTensorAction_eq_of_physical_phases (α : ℕ+ → ℝ)
    (hia : ∀ j, 0 < α j ∧ α j < 1/2) (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier ((criticalPhaseTailCarrier α hia 0 0).translate (-1/2)) T)
    (f f' g : SchwartzMap ℝ ℂ)
    (hf : ∀ x : ℝ, 1/2 ≤ |x| → f x=0) (hf' : ∀ x : ℝ, 1/2 ≤ |x| → f' x=0)
    (he : ∀ j, f (1/2-α j)=f' (1/2-α j) ∧ f (-(1/2-α j))=f' (-(1/2-α j))) :
    zakTensorAction T f g=zakTensorAction T f' g := by
  have hz := zakTensorSlice_halfWeyl_central_zero α hia T hT (f-f')
    (by intro x hx; simp only [_root_.sub_apply,hf x hx,hf' x hx,sub_self])
    (by intro j; simp only [_root_.sub_apply,(he j).1,(he j).2,sub_self,and_self])
  have hz' := congrArg (fun U : TemperedDistribution ℝ ℂ => U g) hz
  rw [zakTensorSlice_apply,_root_.zero_apply,← zakPhysicalSlice_apply] at hz'
  rw [map_sub] at hz'
  simpa only [zakPhysicalSlice_apply,zakTensorSlice_apply] using sub_eq_zero.mp hz'

/-- Equal values on every signed spectral phase give identical whole readings. -/
theorem zakTensorAction_eq_of_spectral_phases (β : ℕ+ → ℝ)
    (hib : ∀ j, 0 < β j ∧ β j < 1/2) (T : TemperedDistribution ℝ ℂ)
    (hFT : AtomicOnCarrier ((criticalPhaseTailCarrier β hib 0 0).translate (-1/2)) (𝓕 T))
    (f g g' : SchwartzMap ℝ ℂ)
    (hg : ∀ x : ℝ, 1/2 ≤ |x| → g x=0) (hg' : ∀ x : ℝ, 1/2 ≤ |x| → g' x=0)
    (he : ∀ j, g (1/2-β j)=g' (1/2-β j) ∧ g (-(1/2-β j))=g' (-(1/2-β j))) :
    zakTensorAction T f g=zakTensorAction T f g' := by
  have hz := zakPhysicalSlice_halfWeyl_central_zero β hib T hFT (g-g')
    (by intro x hx; simp only [_root_.sub_apply,hg x hx,hg' x hx,sub_self])
    (by intro j; simp only [_root_.sub_apply,(he j).1,(he j).2,sub_self,and_self])
  have hz' := congrArg (fun U : TemperedDistribution ℝ ℂ => U f) hz
  rw [zakPhysicalSlice_apply,_root_.zero_apply,← zakTensorSlice_apply] at hz'
  rw [map_sub] at hz'
  simpa only [zakPhysicalSlice_apply,zakTensorSlice_apply] using sub_eq_zero.mp hz'

/-- Exact independent replacement in both characteristic-adjusted variables,
using actual atomic records rather than a supplied moment or jet certificate. -/
theorem halfNewtonBilinear_eq_of_phase_values (α β : ℕ+ → ℝ)
    (hia : ∀ j, 0 < α j ∧ α j < 1/2) (hib : ∀ j, 0 < β j ∧ β j < 1/2)
    (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier ((criticalPhaseTailCarrier α hia 0 0).translate (-1/2)) T)
    (hFT : AtomicOnCarrier ((criticalPhaseTailCarrier β hib 0 0).translate (-1/2)) (𝓕 T))
    (f f' g g' : SchwartzMap ℝ ℂ)
    (hf : ∀ x : ℝ, 1/2 ≤ |x| → f x=0) (hf' : ∀ x : ℝ, 1/2 ≤ |x| → f' x=0)
    (hg : ∀ x : ℝ, 1/2 ≤ |x| → g x=0) (hg' : ∀ x : ℝ, 1/2 ≤ |x| → g' x=0)
    (he : ∀ j, f (1/2-α j)=f' (1/2-α j) ∧ f (-(1/2-α j))=f' (-(1/2-α j)))
    (he' : ∀ j, g (1/2-β j)=g' (1/2-β j) ∧ g (-(1/2-β j))=g' (-(1/2-β j))) :
    halfNewtonBilinear T f g=halfNewtonBilinear T f' g' := by
  have hmod (a : ℝ) (u : SchwartzMap ℝ ℂ) (hu : ∀ x : ℝ, 1/2 ≤ |x| → u x=0) :
      ∀ x : ℝ, 1/2 ≤ |x| → combSchwartzModulation a u x=0 := by
    intro x hx
    rw [combSchwartzModulation_apply,hu x hx,mul_zero]
  unfold halfNewtonBilinear
  calc
    _ = zakTensorAction T (combSchwartzModulation (1/2) f') (combSchwartzModulation (-1/2) g) := by
      apply zakTensorAction_eq_of_physical_phases α hia T hT _ _ _
        (hmod _ _ hf) (hmod _ _ hf')
      intro j
      simp only [combSchwartzModulation_apply,(he j).1,(he j).2,and_self]
    _ = _ := by
      apply zakTensorAction_eq_of_spectral_phases β hib T hFT _ _ _
        (hmod _ _ hg) (hmod _ _ hg')
      intro j
      simp only [combSchwartzModulation_apply,(he' j).1,(he' j).2,and_self]

end
end MeyerGeneralProblem.Adaptive
