module

public import MeyerGeneralProblem.Cardinal.Adaptive.ZakTensorTests

@[expose] public section

/-! # The actual Schwartz-to-distribution Zak transpose family -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open scoped FourierTransform

/-- The complete Zak action is continuous in the physical Schwartz test, with
the second test fixed; continuity is proved from the original native norm. -/
def zakPhysicalSlice (T : TemperedDistribution ℝ ℂ) (g : SchwartzMap ℝ ℂ) :
    TemperedDistribution ℝ ℂ :=
  SchwartzMap.mkCLMtoNormedSpace (fun f => zakTensorAction T f g)
    (fun f h => zakTensorAction_add_left T f h g)
    (fun a f => by rw [zakTensorAction_smul_left]; rfl)
    (by
      obtain ⟨p,u,hu⟩ := exists_hermiteScale_representation T
      obtain ⟨C,hC,hbound⟩ := zakTensorAction_native_bound p
      let q : Seminorm ℂ (SchwartzMap ℝ ℂ) :=
        (normSeminorm ℂ (HermiteScale (p : ℤ))).comp (schwartzToHermiteScale p).toLinearMap
      have hq : Continuous q := continuous_norm.comp (schwartzToHermiteScale p).continuous
      obtain ⟨s,B,hB,hseminorm⟩ := Seminorm.bound_of_continuous
        (schwartz_withSeminorms ℂ ℝ ℂ) q hq
      let G : ℝ := (Finset.Iic (2*p+2,0)).sup (schwartzSeminormFamily ℂ ℝ ℂ) (𝓕 g)
      have hG : 0 ≤ G := apply_nonneg _ _
      refine ⟨s,C*‖u‖*(B : ℝ)*G,by positivity,?_⟩
      intro f
      have h := hbound u f g
      rw [hermiteScaleDistributionCLM_apply,hu] at h
      have hb : ‖schwartzToHermiteScale p f‖ ≤ (B : ℝ)*s.sup (schwartzSeminormFamily ℂ ℝ ℂ) f :=
        hseminorm f
      calc
        _ ≤ C*‖u‖*‖schwartzToHermiteScale p f‖*G := h
        _ ≤ C*‖u‖*((B : ℝ)*s.sup (schwartzSeminormFamily ℂ ℝ ℂ) f)*G :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb (by positivity)) hG
        _ = _ := by ring)

/-- Evaluation of the physical slice is exactly the same whole Zak action. -/
theorem zakPhysicalSlice_apply (T : TemperedDistribution ℝ ℂ) (f g : SchwartzMap ℝ ℂ) :
    zakPhysicalSlice T g f=zakTensorAction T f g := rfl

/-- The actual transpose family maps a physical Schwartz test continuously to
its complete tempered frequency distribution. No two-variable kernel theorem
or Newton representation is assumed in this construction. -/
def zakDistributionFamily (T : TemperedDistribution ℝ ℂ) :
    SchwartzMap ℝ ℂ →L[ℂ] TemperedDistribution ℝ ℂ where
  toFun := zakTensorSlice T
  map_add' f h := by
    ext g
    simp only [zakTensorSlice_apply,_root_.add_apply,zakTensorAction_add_left]
  map_smul' a f := by
    ext g
    simp only [zakTensorSlice_apply,_root_.smul_apply,smul_eq_mul,zakTensorAction_smul_left,RingHom.id_apply]
  cont := PointwiseConvergenceCLM.continuous_of_continuous_eval fun g => by
    have he : (fun f => zakTensorSlice T f g)=fun f => zakPhysicalSlice T g f := by
      funext f
      rw [zakTensorSlice_apply,zakPhysicalSlice_apply]
    rw [he]
    exact (zakPhysicalSlice T g).continuous

/-- Evaluation of the continuous transpose family retains the defining series. -/
theorem zakDistributionFamily_apply (T : TemperedDistribution ℝ ℂ) (f g : SchwartzMap ℝ ℂ) :
    zakDistributionFamily T f g=zakTensorAction T f g := zakTensorSlice_apply T f g

/-- The continuous transpose family is faithful on all original sources. -/
theorem zakDistributionFamily_injective : Function.Injective zakDistributionFamily := by
  intro T U h
  ext f
  have he := congrArg (fun Z : SchwartzMap ℝ ℂ →L[ℂ] TemperedDistribution ℝ ℂ =>
    Z f (zakFrequencyProbe 0)) h
  simpa only [zakDistributionFamily_apply,zakTensorAction_frequency_zero] using he

/-- Source addition is preserved by the actual transpose family. -/
theorem zakDistributionFamily_add (T U : TemperedDistribution ℝ ℂ) :
    zakDistributionFamily (T+U)=zakDistributionFamily T+zakDistributionFamily U := by
  ext f g
  simp only [zakDistributionFamily_apply,_root_.add_apply,
    zakTensorAction_add_source]

/-- Source complex homogeneity is preserved by the actual transpose family. -/
theorem zakDistributionFamily_smul (a : ℂ) (T : TemperedDistribution ℝ ℂ) :
    zakDistributionFamily (a •T)=a •zakDistributionFamily T := by
  ext f g
  simp only [zakDistributionFamily_apply,_root_.smul_apply,
    smul_eq_mul,zakTensorAction_smul_source]

/-- A faithful complex linear embedding of the entire original tempered source
space into actual continuous Schwartz-to-distribution transpose families. -/
def zakDistributionFamilyLM : TemperedDistribution ℝ ℂ →ₗ[ℂ]
    (SchwartzMap ℝ ℂ →L[ℂ] TemperedDistribution ℝ ℂ) where
  toFun := zakDistributionFamily
  map_add' := zakDistributionFamily_add
  map_smul' a T := by simpa only [RingHom.id_apply] using zakDistributionFamily_smul a T

/-- The original source embedding is injective without an atomicity premise. -/
theorem zakDistributionFamilyLM_injective : Function.Injective zakDistributionFamilyLM :=
  zakDistributionFamily_injective


private theorem central_test_integer_phase_zero (f : SchwartzMap ℝ ℂ)
    (hf : ∀ x : ℝ, 1/2 ≤ |x| → f x=0) (a : ℝ) (ha : |a| < 1/2) (hfa : f a=0)
    (n : ℤ) : f ((n : ℝ)+a)=0 := by
  by_cases hn : n=0
  · simpa only [hn,Int.cast_zero,zero_add] using hfa
  · apply hf
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
    have habs := abs_add_le ((n : ℝ)+a) (-a)
    simp only [add_neg_cancel_right,abs_neg] at habs
    linarith

/-- In the central chart, vanishing on the actual signed half-endpoint phases
annihilates the complete Zak frequency distribution. Infinite phase clusters
and their accumulation are retained in this whole-source assertion. -/
theorem zakTensorSlice_halfWeyl_central_zero (α : ℕ+ → ℝ)
    (hia : ∀ j, 0 < α j ∧ α j < 1/2)
    (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier ((criticalPhaseTailCarrier α hia 0 0).translate (-1/2)) T)
    (f : SchwartzMap ℝ ℂ) (hf : ∀ x : ℝ, 1/2 ≤ |x| → f x=0)
    (hphase : ∀ j, f (1/2-α j)=0 ∧ f (-(1/2-α j))=0) :
    zakTensorSlice T f=0 := by
  apply zakTensorSlice_zero_of_translated_vanishing _ T hT f
  intro m x hx
  rw [halfWeylCriticalSet_eq_translate] at hx
  rcases hx with ⟨j,n,hn,rfl⟩|⟨j,n,hn,rfl⟩
  · have ha : |-(1/2-α j)| < 1/2 := by
      rw [abs_neg,abs_of_pos (by linarith [(hia j).2])]
      linarith [(hia j).1]
    have he : (n : ℝ)-(1/2-α j)-(m : ℝ)=((n-m : ℤ) : ℝ)+(-(1/2-α j)) := by
      push_cast
      ring
    rw [he]
    exact central_test_integer_phase_zero f hf (-(1/2-α j)) ha (hphase j).2 (n-m)
  · have ha : |1/2-α j| < 1/2 := by
      rw [abs_of_pos (by linarith [(hia j).2])]
      linarith [(hia j).1]
    have he : (n : ℝ)+(1/2-α j)-(m : ℝ)=((n-m : ℤ) : ℝ)+(1/2-α j) := by
      push_cast
      ring
    rw [he]
    exact central_test_integer_phase_zero f hf (1/2-α j) ha (hphase j).1 (n-m)

end
end MeyerGeneralProblem.Adaptive
