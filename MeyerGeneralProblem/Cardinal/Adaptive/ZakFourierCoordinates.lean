module

public import MeyerGeneralProblem.Cardinal.Adaptive.ZakCompactChart

@[expose] public section

/-! # Faithful compact Fourier coordinates of the entire Zak source -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open scoped FourierTransform

/-- The genuine central Schwartz Fourier probe at an integer frequency. -/
def zakChartFourierProbe (n : ℤ) : SchwartzMap ℝ ℂ :=
  combSchwartzModulation (n : ℝ) zakCentralCutoff

/-- Every Fourier probe is actually supported inside the central half-cell. -/
theorem zakChartFourierProbe_zero (n : ℤ) (x : ℝ) (hx : 1/2 ≤ |x|) :
    zakChartFourierProbe n x=0 := by
  rw [zakChartFourierProbe,combSchwartzModulation_apply,zakCentralCutoff_zero x hx,mul_zero]

/-- The canonical compact representative is the strong sum of the actual
Fourier probes in every original positive native order. -/
theorem zakCentralFrequencyTest_hasSum (p : ℕ) (g : SchwartzMap ℝ ℂ) :
    HasSum (fun n : ℤ => (𝓕 g) (n : ℝ) • schwartzToHermiteScale p (zakChartFourierProbe n))
      (schwartzToHermiteScale p (zakCentralFrequencyTest g)) := by
  have hu (x : ℝ) : zakCentralFrequencyTest g x=∑' n : ℤ,
      (𝓕 g) (n : ℝ)*combSchwartzModulation (n : ℝ) zakCentralCutoff x := by
    rw [zakCentralFrequencyTest,SchwartzMap.smulLeftCLM_apply_apply
      (zakPeriodizedTestFunction_temperate g),smul_eq_mul]
    unfold zakPeriodizedTestFunction
    rw [← tsum_mul_right]
    apply tsum_congr
    intro n
    rw [combSchwartzModulation_apply]
    ring
  have ht := hasSum_native_modulated_tests p (fun n : ℤ => (𝓕 g) (n : ℝ)) (fun n : ℤ => (n : ℝ))
    (by simpa only using summable_weighted_schwartz_int_samples (𝓕 g) (2*p))
    zakCentralCutoff (zakCentralFrequencyTest g) hu
  exact ht

/-- Fourier probes determine every canonical compact test against an arbitrary
original tempered functional, including all derivative jets. -/
theorem zakChartFourierProbe_complete (U : TemperedDistribution ℝ ℂ)
    (hU : ∀ n : ℤ, U (zakChartFourierProbe n)=0) (g : SchwartzMap ℝ ℂ) :
    U (zakCentralFrequencyTest g)=0 := by
  obtain ⟨p,u,hu⟩ := exists_hermiteScale_representation U
  have h := (hermiteScalePairingLeftCLM p u).hasSum (zakCentralFrequencyTest_hasSum p g)
  simp only [map_smul,smul_eq_mul,hermiteScalePairingLeftCLM_apply,
    ← hermiteScaleDistribution_apply,hu,hU,mul_zero] at h
  simpa only [tsum_zero] using h.tsum_eq.symm

/-- A central test has only its zeroth translate at any quarter-cell point. -/
theorem zakPeriodizedTestFunction_eq_of_central (f : SchwartzMap ℝ ℂ)
    (hf : ∀ x : ℝ, 1/2 ≤ |x| → f x=0) (a : ℝ) (ha : |a| ≤ 1/4) :
    zakPeriodizedTestFunction f a=f a := by
  rw [zakPeriodizedTestFunction_eq_tsum,tsum_eq_single (0 : ℤ)]
  · simp only [Int.cast_zero,add_zero]
  · intro n hn
    apply hf
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
    have h := abs_add_le (a+(n : ℝ)) (-a)
    rw [add_right_comm,add_neg_cancel,zero_add,abs_neg] at h
    linarith

/-- The canonical compact representative agrees with the original central test
on every physical phase in the fixed quarter-cell. -/
theorem zakCentralFrequencyTest_eq_of_central (f : SchwartzMap ℝ ℂ)
    (hf : ∀ x : ℝ, 1/2 ≤ |x| → f x=0) (a : ℝ) (ha : |a| ≤ 1/4) :
    zakCentralFrequencyTest f a=f a := by
  rw [zakCentralFrequencyTest,SchwartzMap.smulLeftCLM_apply_apply
    (zakPeriodizedTestFunction_temperate f),zakCentralCutoff_one a ha,smul_eq_mul,mul_one,
    zakPeriodizedTestFunction_eq_of_central f hf a ha]

/-- The actual physical half-Weyl source permits the same canonical compact
replacement in the physical test variable. -/
theorem zakTensorSlice_eq_central_physical (α : ℕ+ → ℝ)
    (hia : ∀ j, 0 < α j ∧ α j < 1/2) (hsmall : ∀ j, 1/4 ≤ α j)
    (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier ((criticalPhaseTailCarrier α hia 0 0).translate (-1/2)) T)
    (f : SchwartzMap ℝ ℂ) (hf : ∀ x : ℝ, 1/2 ≤ |x| → f x=0) :
    zakTensorSlice T (zakCentralFrequencyTest f)=zakTensorSlice T f := by
  have hphase (j : ℕ+) : |1/2-α j| ≤ 1/4 := by
    rw [abs_of_pos (by linarith [(hia j).2])]
    linarith [hsmall j]
  have he := zakTensorSlice_halfWeyl_central_zero α hia T hT (zakCentralFrequencyTest f-f)
    (by intro x hx; simp only [_root_.sub_apply,zakCentralFrequencyTest_zero f x hx,hf x hx,sub_self])
    (by
      intro j
      constructor
      · simp only [_root_.sub_apply,zakCentralFrequencyTest_eq_of_central f hf _ (hphase j),sub_self]
      · have ha : |-(1/2-α j)| ≤ 1/4 := by simpa only [abs_neg] using hphase j
        simp only [_root_.sub_apply,zakCentralFrequencyTest_eq_of_central f hf _ ha,sub_self])
  ext g
  have hz := congrArg (fun U : TemperedDistribution ℝ ℂ => U g) he
  rw [zakTensorSlice_apply] at hz
  have hadd := zakTensorAction_add_left T (zakCentralFrequencyTest f-f) f g
  rw [sub_add_cancel] at hadd
  rw [hz] at hadd
  simpa only [_root_.zero_apply,zero_add,zakTensorSlice_apply] using hadd

/-- Complete compact Fourier coordinates are actual evaluations of the whole
source family, with no supplied array representation. -/
def zakCompactFourierCoordinates (T : TemperedDistribution ℝ ℂ) (m n : ℤ) : ℂ :=
  zakTensorAction T (zakChartFourierProbe m) (zakChartFourierProbe n)

/-- The entire paired half-Weyl source is faithfully determined by its complete
double Fourier coordinate array in the compact chart. -/
theorem zakCompactFourierCoordinates_faithful (α β : ℕ+ → ℝ)
    (hia : ∀ j, 0 < α j ∧ α j < 1/2) (hib : ∀ j, 0 < β j ∧ β j < 1/2)
    (hsmallA : ∀ j, 1/4 ≤ α j) (hsmallB : ∀ j, 1/4 ≤ β j)
    (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier ((criticalPhaseTailCarrier α hia 0 0).translate (-1/2)) T)
    (hFT : AtomicOnCarrier ((criticalPhaseTailCarrier β hib 0 0).translate (-1/2)) (𝓕 T))
    (hz : ∀ m n : ℤ, zakCompactFourierCoordinates T m n=0) : T=0 := by
  apply zakCentralChart_faithful _ _ T hT hFT (halfWeylCarrier_cell α hia)
    (halfWeylCarrier_quarter β hib hsmallB)
  intro f g hf hg
  have hrow (m : ℤ) : zakTensorAction T (zakChartFourierProbe m) g=0 := by
    have he := zakChartFourierProbe_complete (zakTensorSlice T (zakChartFourierProbe m))
      (fun n => by simpa only [zakTensorSlice_apply,zakCompactFourierCoordinates] using hz m n) g
    have hl := congrArg (fun U : TemperedDistribution ℝ ℂ => U (zakChartFourierProbe m))
      (zakPhysicalSlice_eq_central _ T hFT (halfWeylCarrier_quarter β hib hsmallB) g)
    rw [zakTensorSlice_apply] at he
    rw [zakPhysicalSlice_apply,zakPhysicalSlice_apply] at hl
    rwa [hl] at he
  have hc := zakChartFourierProbe_complete (zakPhysicalSlice T g)
    (fun m => by simpa only [zakPhysicalSlice_apply] using hrow m) f
  have hl := congrArg (fun U : TemperedDistribution ℝ ℂ => U g)
    (zakTensorSlice_eq_central_physical α hia hsmallA T hT f hf)
  rw [zakPhysicalSlice_apply] at hc
  rw [zakTensorSlice_apply,zakTensorSlice_apply] at hl
  rwa [hl] at hc


/-- The complete compact Fourier array of the genuine half-Weyl image is a
faithful coordinate extraction from the original paired critical source. -/
theorem halfWeylCompactFourierCoordinates_faithful (α β : ℕ+ → ℝ)
    (hia : ∀ j, 0 < α j ∧ α j < 1/2) (hib : ∀ j, 0 < β j ∧ β j < 1/2)
    (hsmallA : ∀ j, 1/4 ≤ α j) (hsmallB : ∀ j, 1/4 ≤ β j)
    (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier (criticalPhaseTailCarrier α hia 0 0) T)
    (hFT : AtomicOnCarrier (criticalPhaseTailCarrier β hib 0 0) (𝓕 T))
    (hz : ∀ m n : ℤ, zakCompactFourierCoordinates (halfWeylDistributionCLM T) m n=0) : T=0 := by
  have hw := halfWeylDistribution_atomic_records α β hia hib T hT hFT
  have he := zakCompactFourierCoordinates_faithful α β hia hib hsmallA hsmallB
    (halfWeylDistributionCLM T) hw.1 hw.2 hz
  apply halfWeylDistribution_injective
  simpa only [map_zero] using he

end
end MeyerGeneralProblem.Adaptive
