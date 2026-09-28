module

public import MeyerGeneralProblem.Cardinal.Adaptive.HalfNewtonSpan

@[expose] public section

/-! # Actual compact Newton tests and complete coordinate extraction -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open scoped FourierTransform ContDiff

/-- Every actual half-integer Newton scalar is globally smooth. -/
theorem halfNewtonFunction_contDiff (ε : ℕ+ → ℝ) (i : ℕ) (e : Bool) :
    ContDiff ℝ ∞ (halfNewtonFunction ε i e) := by
  have hd : ContDiff ℝ ∞ (halfNewtonProduct ε i) := by
    unfold halfNewtonProduct
    have hz := criticalNewtonNode_contDiff
    fun_prop
  have hc : ContDiff ℝ ∞ (fun x : ℝ => (Real.cos (Real.pi*x) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp ((contDiff_const.mul contDiff_id).cos)
  have hs : ContDiff ℝ ∞ (fun x : ℝ => (Real.sin (Real.pi*x) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp ((contDiff_const.mul contDiff_id).sin)
  cases e
  · exact hc.mul hd
  · exact hs.mul hd

theorem halfNewtonTest_compact (ε : ℕ+ → ℝ) (i : ℕ) (e : Bool) :
    HasCompactSupport (fun x => zakCentralCutoff x*halfNewtonFunction ε i e x) := by
  have hc : HasCompactSupport (zakCentralCutoff : ℝ → ℂ) := by
    change HasCompactSupport (fun x => (zakCentralBump x : ℂ))
    exact zakCentralBump.hasCompactSupport.comp_left (show ((0 : ℝ) : ℂ)=0 by rfl)
  exact hc.mul_right

/-- The actual compact Schwartz test of the prescribed Newton parity function. -/
def halfNewtonTest (ε : ℕ+ → ℝ) (i : ℕ) (e : Bool) : SchwartzMap ℝ ℂ :=
  (halfNewtonTest_compact ε i e).toSchwartzMap
    ((zakCentralCutoff.smooth ⊤).mul (halfNewtonFunction_contDiff ε i e))

/-- Pointwise identification with the fixed genuine central cutoff. -/
theorem halfNewtonTest_apply (ε : ℕ+ → ℝ) (i : ℕ) (e : Bool) (x : ℝ) :
    halfNewtonTest ε i e x=zakCentralCutoff x*halfNewtonFunction ε i e x := rfl

/-- Finite span of the genuine compact Newton Schwartz tests. -/
def halfNewtonTestSpan (ε : ℕ+ → ℝ) : Submodule ℂ (SchwartzMap ℝ ℂ) :=
  Submodule.span ℂ (Set.range (fun p : ℕ × Bool => halfNewtonTest ε p.1 p.2))

/-- Scalar Newton-span membership lifts to actual Schwartz test membership,
with the same pointwise cutoff, by finite linear operations only. -/
theorem halfNewtonSpan_lift_test (ε : ℕ+ → ℝ) {f : ℝ → ℂ} (hf : f ∈ halfNewtonSpan ε) :
    ∃ u : SchwartzMap ℝ ℂ, u ∈ halfNewtonTestSpan ε ∧ ∀ x, u x=zakCentralCutoff x*f x := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨⟨i,e⟩,rfl⟩ := hf
      exact ⟨halfNewtonTest ε i e,Submodule.subset_span ⟨(i,e),rfl⟩,halfNewtonTest_apply ε i e⟩
  | zero => exact ⟨0,(halfNewtonTestSpan ε).zero_mem,fun x => by simp⟩
  | add f g _ _ hf hg =>
      obtain ⟨u,hu,heu⟩ := hf
      obtain ⟨v,hv,hev⟩ := hg
      refine ⟨u+v,(halfNewtonTestSpan ε).add_mem hu hv,?_⟩
      intro x
      simp only [_root_.add_apply,Pi.add_apply,heu,hev,mul_add]
  | smul a f _ hf =>
      obtain ⟨u,hu,heu⟩ := hf
      refine ⟨a •u,(halfNewtonTestSpan ε).smul_mem a hu,?_⟩
      intro x
      simp only [_root_.smul_apply,Pi.smul_apply,smul_eq_mul,heu]
      ring

/-- Every compact half-integer Fourier probe is a finite linear combination
of the actual Newton Schwartz tests, on both frequency arms. -/
theorem halfNewtonTestSpan_half_character (ε : ℕ+ → ℝ) (n : ℤ) :
    combSchwartzModulation ((n : ℝ)+1/2) zakCentralCutoff ∈ halfNewtonTestSpan ε := by
  obtain ⟨u,hu,heu⟩ := halfNewtonSpan_lift_test ε (halfNewtonSpan_all_half_characters ε n)
  have he : u=combSchwartzModulation ((n : ℝ)+1/2) zakCentralCutoff := by
    ext x
    rw [heu,combSchwartzModulation_apply,mul_comm]
  rwa [he] at hu

/-- The literal characteristic-adjusted Zak bilinear action, retaining both
opposite half modulations from the accepted source. -/
def halfNewtonBilinear (T : TemperedDistribution ℝ ℂ) (f g : SchwartzMap ℝ ℂ) : ℂ :=
  zakTensorAction T (combSchwartzModulation (1/2) f) (combSchwartzModulation (-1/2) g)

private theorem halfNewtonBilinear_add_left (T : TemperedDistribution ℝ ℂ)
    (f h g : SchwartzMap ℝ ℂ) :
    halfNewtonBilinear T (f+h) g=halfNewtonBilinear T f g+halfNewtonBilinear T h g := by
  simp only [halfNewtonBilinear,map_add,zakTensorAction_add_left]

private theorem halfNewtonBilinear_add_right (T : TemperedDistribution ℝ ℂ)
    (f g h : SchwartzMap ℝ ℂ) :
    halfNewtonBilinear T f (g+h)=halfNewtonBilinear T f g+halfNewtonBilinear T f h := by
  simp only [halfNewtonBilinear,map_add,zakTensorAction_add_right]

private theorem halfNewtonBilinear_smul_left (T : TemperedDistribution ℝ ℂ)
    (a : ℂ) (f g : SchwartzMap ℝ ℂ) :
    halfNewtonBilinear T (a •f) g=a*halfNewtonBilinear T f g := by
  simp only [halfNewtonBilinear,map_smul,zakTensorAction_smul_left]

private theorem halfNewtonBilinear_smul_right (T : TemperedDistribution ℝ ℂ)
    (a : ℂ) (f g : SchwartzMap ℝ ℂ) :
    halfNewtonBilinear T f (a •g)=a*halfNewtonBilinear T f g := by
  simp only [halfNewtonBilinear,map_smul,zakTensorAction_smul_right]

/-- The unnormalized complete Newton coordinate is an actual whole-source
evaluation on the constructed compact Schwartz tests. -/
def halfNewtonCoordinate (ε δ : ℕ+ → ℝ) (T : TemperedDistribution ℝ ℂ)
    (i : ℕ) (e : Bool) (j : ℕ) (f : Bool) : ℂ :=
  halfNewtonBilinear T (halfNewtonTest ε i e) (halfNewtonTest δ j f)

/-- Vanishing of all actual Newton coordinates extends to their complete
finite spans in both test variables, using true bilinearity. -/
theorem halfNewtonCoordinate_zero_spans (ε δ : ℕ+ → ℝ) (T : TemperedDistribution ℝ ℂ)
    (hz : ∀ i e j f, halfNewtonCoordinate ε δ T i e j f=0)
    {u v : SchwartzMap ℝ ℂ} (hu : u ∈ halfNewtonTestSpan ε) (hv : v ∈ halfNewtonTestSpan δ) :
    halfNewtonBilinear T u v=0 := by
  have hrow (i : ℕ) (e : Bool) : halfNewtonBilinear T (halfNewtonTest ε i e) v=0 := by
    induction hv using Submodule.span_induction with
    | mem v hv =>
        obtain ⟨⟨j,f⟩,rfl⟩ := hv
        exact hz i e j f
    | zero => simp [halfNewtonBilinear,zakTensorAction]
    | add g h _ _ hg hh => rw [halfNewtonBilinear_add_right,hg,hh,add_zero]
    | smul a g _ hg => rw [halfNewtonBilinear_smul_right,hg,mul_zero]
  induction hu using Submodule.span_induction with
  | mem u hu =>
      obtain ⟨⟨i,e⟩,rfl⟩ := hu
      exact hrow i e
  | zero => simp [halfNewtonBilinear,zakTensorAction]
  | add f h _ _ hf hh => rw [halfNewtonBilinear_add_left,hf,hh,add_zero]
  | smul a f _ hf => rw [halfNewtonBilinear_smul_left,hf,mul_zero]


private theorem modulation_add_test (a b : ℝ) (f : SchwartzMap ℝ ℂ) :
    combSchwartzModulation a (combSchwartzModulation b f)=combSchwartzModulation (a+b) f := by
  ext x
  simp only [combSchwartzModulation_apply,combModulationCharacter,add_mul,
    AddChar.map_add_eq_mul,Circle.coe_mul,mul_assoc]

/-- The two characteristic half shifts turn the complete half-frequency probes
into the actual integer Fourier coordinates, with both source signs retained. -/
theorem halfNewtonBilinear_half_probes (T : TemperedDistribution ℝ ℂ) (m n : ℤ) :
    halfNewtonBilinear T
      (combSchwartzModulation (((m-1 : ℤ) : ℝ)+1/2) zakCentralCutoff)
      (combSchwartzModulation ((n : ℝ)+1/2) zakCentralCutoff)=
        zakCompactFourierCoordinates T m n := by
  unfold halfNewtonBilinear
  rw [modulation_add_test,modulation_add_test]
  have hm : (1/2 : ℝ)+(((m-1 : ℤ) : ℝ)+1/2)=(m : ℝ) := by push_cast; ring
  have hn : (-1/2 : ℝ)+((n : ℝ)+1/2)=(n : ℝ) := by ring
  rw [hm,hn]
  rfl

/-- The complete actual Newton coordinate array is faithful on the entire
paired recentered critical source. Accumulation jets are retained through the
proved full Fourier-array extraction, without a moment representation premise. -/
theorem halfNewtonCoordinates_faithful (ε δ α β : ℕ+ → ℝ)
    (hia : ∀ j, 0 < α j ∧ α j < 1/2) (hib : ∀ j, 0 < β j ∧ β j < 1/2)
    (hsmallA : ∀ j, 1/4 ≤ α j) (hsmallB : ∀ j, 1/4 ≤ β j)
    (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier ((criticalPhaseTailCarrier α hia 0 0).translate (-1/2)) T)
    (hFT : AtomicOnCarrier ((criticalPhaseTailCarrier β hib 0 0).translate (-1/2)) (𝓕 T))
    (hz : ∀ i e j f, halfNewtonCoordinate ε δ T i e j f=0) : T=0 := by
  apply zakCompactFourierCoordinates_faithful α β hia hib hsmallA hsmallB T hT hFT
  intro m n
  have h := halfNewtonCoordinate_zero_spans ε δ T hz
    (halfNewtonTestSpan_half_character ε (m-1)) (halfNewtonTestSpan_half_character δ n)
  rwa [halfNewtonBilinear_half_probes] at h

/-- The exact source normalization R^(-i-j)κ^(-e-f), with R=1/4096 and
κ=1/64, applied to the constructed whole compact Newton coordinate. -/
def halfNewtonMoment (ε δ : ℕ+ → ℝ) (T : TemperedDistribution ℝ ℂ)
    (i : ℕ) (e : Bool) (j : ℕ) (f : Bool) : ℂ :=
  (((1/4096 : ℂ)^(i+j)*(1/64 : ℂ)^(e.toNat+f.toNat))⁻¹)*
    halfNewtonCoordinate ε δ T i e j f

/-- The prescribed normalization is nowhere zero, so no coordinate is lost. -/
theorem halfNewtonMoment_eq_zero_iff (ε δ : ℕ+ → ℝ) (T : TemperedDistribution ℝ ℂ)
    (i : ℕ) (e : Bool) (j : ℕ) (f : Bool) :
    halfNewtonMoment ε δ T i e j f=0 ↔ halfNewtonCoordinate ε δ T i e j f=0 := by
  unfold halfNewtonMoment
  rw [mul_eq_zero]
  have h : (((1/4096 : ℂ)^(i+j)*(1/64 : ℂ)^(e.toNat+f.toNat))⁻¹) ≠ 0 := by
    apply inv_ne_zero
    apply mul_ne_zero <;> apply pow_ne_zero <;> norm_num
  exact or_iff_right h

/-- Complete normalized half-seam moments are faithfully extracted from the
actual original paired critical source using its exact recentered phases. -/
theorem halfNewtonMoments_original_faithful (α β : ℕ+ → ℝ)
    (hia : ∀ j, 0 < α j ∧ α j < 1/2) (hib : ∀ j, 0 < β j ∧ β j < 1/2)
    (hsmallA : ∀ j, 1/4 ≤ α j) (hsmallB : ∀ j, 1/4 ≤ β j)
    (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier (criticalPhaseTailCarrier α hia 0 0) T)
    (hFT : AtomicOnCarrier (criticalPhaseTailCarrier β hib 0 0) (𝓕 T))
    (hz : ∀ i e j f, halfNewtonMoment (fun l => 1/2-α l) (fun l => 1/2-β l)
      (halfWeylDistributionCLM T) i e j f=0) : T=0 := by
  have hw := halfWeylDistribution_atomic_records α β hia hib T hT hFT
  have he := halfNewtonCoordinates_faithful (fun l => 1/2-α l) (fun l => 1/2-β l)
    α β hia hib hsmallA hsmallB (halfWeylDistributionCLM T) hw.1 hw.2
    (fun i e j f => (halfNewtonMoment_eq_zero_iff _ _ _ i e j f).mp (hz i e j f))
  apply halfWeylDistribution_injective
  simpa only [map_zero] using he

end
end MeyerGeneralProblem.Adaptive
