module

public import MeyerGeneralProblem.Cardinal.Adaptive.ShrinkingNewtonCutoffs
public import MeyerGeneralProblem.Cardinal.Adaptive.HalfNewtonLocalization

@[expose] public section

/-! Genuine shrinking Newton Schwartz tests and exact whole-source replacement. -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open Set
open scoped ContDiff FourierTransform

/-- The literal Newton product is the real cosine-difference product used in its derivative estimates. -/
theorem halfNewtonProduct_cosine_product (ε : ℕ → ℝ) (i : ℕ) (x : ℝ) :
    halfNewtonProduct (fun j => ε j) i x =
      ((∏ l ∈ Finset.range i, (Real.cos (2*Real.pi*ε (l+1))-
        Real.cos (2*Real.pi*x)) : ℝ) : ℂ) := by
  simp only [halfNewtonProduct,Complex.ofReal_prod]
  apply Finset.prod_congr rfl
  intro l hl
  simp only [criticalNewtonNode,Complex.ofReal_sub,Complex.ofReal_one]
  change (1-(Real.cos (2*Real.pi*x):ℂ))-(1-(Real.cos (2*Real.pi*ε (l+1)):ℂ)) = _
  ring

theorem shrinkingNewtonTest_compact (ε : ℕ+ → ℝ) (i : ℕ) (e : Bool)
    (a b : ℝ) (hab : a < b) :
    HasCompactSupport (fun x => (shrinkingTailCutoff a b x : ℂ)*halfNewtonFunction ε i e x) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc : IsCompact (Icc (-b) b))
  intro x hx
  have h : |x| < b := lt_of_not_ge (fun h => hx (by
    dsimp only
    rw [shrinkingTailCutoff_zero a b x hab h,Complex.ofReal_zero,zero_mul]))
  exact ⟨(abs_lt.mp h).1.le,(abs_lt.mp h).2.le⟩

/-- Actual shrinking cutoff times the original Newton function, as a genuine Schwartz test. -/
def shrinkingNewtonTest (ε : ℕ+ → ℝ) (i : ℕ) (e : Bool) (a b : ℝ)
    (hab : a < b) : SchwartzMap ℝ ℂ :=
  (shrinkingNewtonTest_compact ε i e a b hab).toSchwartzMap
    ((Complex.ofRealCLM.contDiff.comp (shrinkingTailCutoff_smooth a b)).mul
      (halfNewtonFunction_contDiff ε i e))

/-- Pointwise formula for the actual shrinking Schwartz representative. -/
theorem shrinkingNewtonTest_apply (ε : ℕ+ → ℝ) (i : ℕ) (e : Bool) (a b : ℝ)
    (hab : a < b) (x : ℝ) : shrinkingNewtonTest ε i e a b hab x =
      (shrinkingTailCutoff a b x : ℂ)*halfNewtonFunction ε i e x := rfl

/-- The complete shrinking test vanishes beyond its outer radius. -/
theorem shrinkingNewtonTest_zero (ε : ℕ+ → ℝ) (i : ℕ) (e : Bool) (a b : ℝ)
    (hab : a < b) (x : ℝ) (hx : b ≤ |x|) : shrinkingNewtonTest ε i e a b hab x=0 := by
  rw [shrinkingNewtonTest_apply,shrinkingTailCutoff_zero a b x hab hx,Complex.ofReal_zero,zero_mul]

/-- Every head node, on either sign arm, is annihilated by its actual Newton factor. -/
theorem halfNewtonProduct_zero_at_head (ε : ℕ+ → ℝ) (i : ℕ) (j : ℕ+)
    (hj : (j:ℕ) ≤ i) (x : ℝ) (hx : x=ε j ∨ x= -ε j) :
    halfNewtonProduct ε i x=0 := by
  unfold halfNewtonProduct
  apply Finset.prod_eq_zero (Finset.mem_range.mpr (show (j:ℕ)-1 < i by have := j.pos; omega))
  have he : (⟨(j:ℕ)-1+1,by omega⟩ : ℕ+)=j := by
    apply Subtype.ext
    change (j:ℕ)-1+1=(j:ℕ)
    have := j.pos
    omega
  rw [he]
  rcases hx with rfl | rfl
  · simp
  · simp [criticalNewtonNode,Real.cos_neg,mul_neg]

/-- Tail phases survive the shrinking cutoff and preceding phases vanish by exact Newton factors. -/
theorem shrinkingNewtonTest_eq_fixed_at_phases (ε : ℕ+ → ℝ) (i : ℕ) (e : Bool)
    (a b : ℝ) (hab : a < b) (hsmall : ∀ j, |ε j| ≤ 1/4)
    (htail : ∀ j : ℕ+, i < (j:ℕ) → |ε j| ≤ a) (j : ℕ+) (x : ℝ)
    (hx : x=ε j ∨ x= -ε j) :
    shrinkingNewtonTest ε i e a b hab x=halfNewtonTest ε i e x := by
  rw [shrinkingNewtonTest_apply,halfNewtonTest_apply]
  by_cases hj : (j:ℕ) ≤ i
  · have hz := halfNewtonProduct_zero_at_head ε i j hj x hx
    simp only [halfNewtonFunction,hz,mul_zero]
  · have ha : |x| ≤ a := by rcases hx with rfl | rfl <;> simpa using htail j (by omega)
    have hs : |x| ≤ 1/4 := by rcases hx with rfl | rfl <;> simpa using hsmall j
    rw [shrinkingTailCutoff_one a b x hab ha,zakCentralCutoff_one x hs,Complex.ofReal_one]

/-- The whole characteristic-adjusted source reading survives replacement by actual shrinking tests. -/
theorem halfNewtonBilinear_shrinking_tests (α β : ℕ+ → ℝ)
    (hia : ∀ j, 0 < α j ∧ α j < 1/2) (hib : ∀ j, 0 < β j ∧ β j < 1/2)
    (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier ((criticalPhaseTailCarrier α hia 0 0).translate (-1/2)) T)
    (hFT : AtomicOnCarrier ((criticalPhaseTailCarrier β hib 0 0).translate (-1/2)) (𝓕 T))
    (i j : ℕ) (e f : Bool) (a b c d : ℝ) (hab : a < b) (hcd : c < d)
    (hb : b < 1/2) (hd : d < 1/2)
    (ha : ∀ l, |1/2-α l| ≤ 1/4) (hc : ∀ l, |1/2-β l| ≤ 1/4)
    (hat : ∀ l : ℕ+, i < (l:ℕ) → |1/2-α l| ≤ a)
    (hct : ∀ l : ℕ+, j < (l:ℕ) → |1/2-β l| ≤ c) :
    halfNewtonBilinear T
      (shrinkingNewtonTest (fun l => 1/2-α l) i e a b hab)
      (shrinkingNewtonTest (fun l => 1/2-β l) j f c d hcd) =
    halfNewtonBilinear T (halfNewtonTest (fun l => 1/2-α l) i e)
      (halfNewtonTest (fun l => 1/2-β l) j f) := by
  apply halfNewtonBilinear_eq_of_phase_values α β hia hib T hT hFT
  · intro x hx; exact shrinkingNewtonTest_zero _ _ _ _ _ _ _ (hb.le.trans hx)
  · intro x hx; rw [halfNewtonTest_apply,zakCentralCutoff_zero x hx,zero_mul]
  · intro x hx; exact shrinkingNewtonTest_zero _ _ _ _ _ _ _ (hd.le.trans hx)
  · intro x hx; rw [halfNewtonTest_apply,zakCentralCutoff_zero x hx,zero_mul]
  · intro l
    exact ⟨shrinkingNewtonTest_eq_fixed_at_phases _ _ _ _ _ hab ha hat l _ (Or.inl rfl),
      shrinkingNewtonTest_eq_fixed_at_phases _ _ _ _ _ hab ha hat l _ (Or.inr rfl)⟩
  · intro l
    exact ⟨shrinkingNewtonTest_eq_fixed_at_phases _ _ _ _ _ hcd hc hct l _ (Or.inl rfl),
      shrinkingNewtonTest_eq_fixed_at_phases _ _ _ _ _ hcd hc hct l _ (Or.inr rfl)⟩

end
end MeyerGeneralProblem.Adaptive
