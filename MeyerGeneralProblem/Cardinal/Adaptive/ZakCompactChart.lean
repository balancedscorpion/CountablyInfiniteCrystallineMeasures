module

public import MeyerGeneralProblem.Cardinal.Adaptive.ZakPeriodization

@[expose] public section

/-! # Faithful central-chart restriction of the actual whole paired source -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open scoped FourierTransform

/-- A fixed central bump equals one on the quarter-cell and vanishes outside
the half-cell; its radii are independent of every phase sequence. -/
def zakCentralBump : ContDiffBump (0 : ℝ) where
  rIn := 1/4
  rOut := 1/2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- The genuine compact Schwartz version of the central chart cutoff. -/
def zakCentralCutoff : SchwartzMap ℝ ℂ :=
  (zakCentralBump.hasCompactSupport.comp_left (show ((0 : ℝ) : ℂ)=0 by rfl)).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp zakCentralBump.contDiff)

/-- Exact value one on every point in the fixed inner quarter-cell. -/
theorem zakCentralCutoff_one (x : ℝ) (hx : |x| ≤ 1/4) : zakCentralCutoff x=1 := by
  change (zakCentralBump x : ℂ)=1
  rw [zakCentralBump.one_of_mem_closedBall]
  · norm_num
  · simpa only [Metric.mem_closedBall,Real.dist_eq,sub_zero,zakCentralBump] using hx

/-- Exact vanishing outside the open central half-cell. -/
theorem zakCentralCutoff_zero (x : ℝ) (hx : 1/2 ≤ |x|) : zakCentralCutoff x=0 := by
  change (zakCentralBump x : ℂ)=0
  rw [zakCentralBump.zero_of_le_dist]
  · norm_num
  · simpa only [Real.dist_eq,sub_zero,zakCentralBump] using hx

/-- Canonical compact representative of the complete periodization of any
Schwartz test, on all spectral phases in the quarter-cell. -/
def zakCentralFrequencyTest (g : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.smulLeftCLM ℂ (zakPeriodizedTestFunction g) zakCentralCutoff

/-- The canonical representative is genuinely zero outside the central chart. -/
theorem zakCentralFrequencyTest_zero (g : SchwartzMap ℝ ℂ) (x : ℝ) (hx : 1/2 ≤ |x|) :
    zakCentralFrequencyTest g x=0 := by
  rw [zakCentralFrequencyTest,SchwartzMap.smulLeftCLM_apply_apply
    (zakPeriodizedTestFunction_temperate g),zakCentralCutoff_zero x hx,smul_zero]

private theorem integer_offset_large (n : ℤ) (hn : n ≠ 0) (a : ℝ) (ha : |a| ≤ 1/4) :
    1/2 ≤ |a+(n : ℝ)| := by
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

/-- The complete compact periodization agrees exactly with the original
periodization at every integer translate of the quarter-cell. -/
theorem zakCentralFrequencyTest_periodization (g : SchwartzMap ℝ ℂ)
    (a : ℝ) (ha : |a| ≤ 1/4) (n : ℤ) :
    zakPeriodizedTestFunction (zakCentralFrequencyTest g) (a+(n : ℝ))=
      zakPeriodizedTestFunction g (a+(n : ℝ)) := by
  have hp (h : SchwartzMap ℝ ℂ) :
      zakPeriodizedTestFunction h (a+(n : ℝ))=zakPeriodizedTestFunction h a := by
    simpa only [mul_one] using (zakPeriodizedTestFunction_periodic h).int_mul n a
  rw [hp,hp,zakPeriodizedTestFunction_eq_tsum]
  rw [tsum_eq_single (0 : ℤ)]
  · simp only [Int.cast_zero,add_zero]
    rw [zakCentralFrequencyTest,SchwartzMap.smulLeftCLM_apply_apply
      (zakPeriodizedTestFunction_temperate g),zakCentralCutoff_one a ha,smul_eq_mul,mul_one]
  · intro m hm
    exact zakCentralFrequencyTest_zero g _ (integer_offset_large m hm a ha)

/-- If the two complete periodizations agree on the actual Fourier carrier,
the genuine physical Zak slices agree. This permits chart localization without
assuming phasewise tempering or omitting accumulation terms. -/
theorem zakPhysicalSlice_eq_of_periodization_eq (S : LocallyFiniteCarrier)
    (T : TemperedDistribution ℝ ℂ) (hT : AtomicOnCarrier S (𝓕 T))
    (g h : SchwartzMap ℝ ℂ)
    (hgh : ∀ x ∈ S.carrier, zakPeriodizedTestFunction g x=zakPeriodizedTestFunction h x) :
    zakPhysicalSlice T g=zakPhysicalSlice T h := by
  have he : 𝓕 (zakPhysicalSlice T g)=𝓕 (zakPhysicalSlice T h) := by
    rw [fourier_zakPhysicalSlice,fourier_zakPhysicalSlice]
    ext f
    rw [TemperedDistribution.smulLeftCLM_apply_apply,TemperedDistribution.smulLeftCLM_apply_apply]
    apply sub_eq_zero.mp
    rw [← map_sub]
    apply hT
    intro x hx
    simp only [_root_.sub_apply,SchwartzMap.smulLeftCLM_apply_apply
      (zakPeriodizedTestFunction_temperate g),SchwartzMap.smulLeftCLM_apply_apply
      (zakPeriodizedTestFunction_temperate h),hgh x hx,sub_self]
  have hi := congrArg (fun U : TemperedDistribution ℝ ℂ => 𝓕⁻ U) he
  simpa only [FourierTransform.fourierInv_fourier_eq] using hi

/-- Actual paired sources whose Fourier atoms lie in translated quarter-cells
are exactly determined by the canonical compact frequency representative. -/
theorem zakPhysicalSlice_eq_central (S : LocallyFiniteCarrier)
    (T : TemperedDistribution ℝ ℂ) (hT : AtomicOnCarrier S (𝓕 T))
    (hS : ∀ x ∈ S.carrier, ∃ (a : ℝ) (n : ℤ), |a| ≤ 1/4 ∧ x=a+(n : ℝ))
    (g : SchwartzMap ℝ ℂ) :
    zakPhysicalSlice T (zakCentralFrequencyTest g)=zakPhysicalSlice T g := by
  apply zakPhysicalSlice_eq_of_periodization_eq S T hT
  intro x hx
  obtain ⟨a,n,ha,rfl⟩ := hS x hx
  exact zakCentralFrequencyTest_periodization g a ha n


/-- Central physical and frequency tests faithfully retain the entire paired
source. The proof uses exact compact frequency localization, true Fourier
probes, and the complete whole-carrier atomic uniqueness theorem. -/
theorem zakCentralChart_faithful (S R : LocallyFiniteCarrier)
    (T : TemperedDistribution ℝ ℂ) (hT : AtomicOnCarrier S T) (hFT : AtomicOnCarrier R (𝓕 T))
    (hcell : ∀ z : S.subtype, ∃ n : ℤ, |(z : ℝ)-(n : ℝ)|<1/2)
    (hR : ∀ x ∈ R.carrier, ∃ (a : ℝ) (n : ℤ), |a| ≤ 1/4 ∧ x=a+(n : ℝ))
    (hz : ∀ (f g : SchwartzMap ℝ ℂ),
      (∀ x : ℝ, 1/2 ≤ |x| → f x=0) →
      (∀ x : ℝ, 1/2 ≤ |x| → g x=0) → zakTensorAction T f g=0) : T=0 := by
  apply atomicOnCarrier_eq_zero_of_cell_tests S T hT hcell
  intro f hf n
  have ha (g : SchwartzMap ℝ ℂ) : zakTensorAction T f g=0 := by
    have he := congrArg (fun U : TemperedDistribution ℝ ℂ => U f)
      (zakPhysicalSlice_eq_central R T hFT hR g)
    rw [zakPhysicalSlice_apply,zakPhysicalSlice_apply] at he
    rw [← he]
    exact hz f (zakCentralFrequencyTest g) hf (zakCentralFrequencyTest_zero g)
  have he := ha (zakFrequencyProbe (-n))
  rw [zakTensorAction_frequency_probe] at he
  simpa only [Int.cast_neg,neg_neg] using he

/-- Every actual recentered critical atom belongs strictly to one central
integer chart, with both original asymmetric threshold branches retained. -/
theorem halfWeylCarrier_cell (α : ℕ+ → ℝ) (hia : ∀ j, 0 < α j ∧ α j < 1/2) :
    ∀ z : ((criticalPhaseTailCarrier α hia 0 0).translate (-1/2)).subtype,
      ∃ n : ℤ, |(z : ℝ)-(n : ℝ)|<1/2 := by
  intro z
  have hz : (z : ℝ) ∈ ((criticalPhaseTailCarrier α hia 0 0).translate (-1/2)).carrier := z.property
  rw [halfWeylCriticalSet_eq_translate] at hz
  rcases hz with ⟨j,n,hn,hz⟩|⟨j,n,hn,hz⟩
  · refine ⟨n,?_⟩
    rw [hz]
    have he : (n : ℝ)-(1/2-α j)-(n : ℝ)=-(1/2-α j) := by ring
    rw [he,abs_neg,abs_of_pos (by linarith [(hia j).2])]
    linarith [(hia j).1]
  · refine ⟨n,?_⟩
    rw [hz,add_sub_cancel_left,abs_of_pos (by linarith [(hia j).2])]
    linarith [(hia j).1]

/-- The small half-endpoint premise gives the proved quarter-cell geometry
of the entire actual recentered critical carrier. -/
theorem halfWeylCarrier_quarter (α : ℕ+ → ℝ) (hia : ∀ j, 0 < α j ∧ α j < 1/2)
    (hsmall : ∀ j, 1/4 ≤ α j) :
    ∀ x ∈ ((criticalPhaseTailCarrier α hia 0 0).translate (-1/2)).carrier,
      ∃ (a : ℝ) (n : ℤ), |a| ≤ 1/4 ∧ x=a+(n : ℝ) := by
  intro x hx
  rw [halfWeylCriticalSet_eq_translate] at hx
  rcases hx with ⟨j,n,hn,rfl⟩|⟨j,n,hn,rfl⟩
  · refine ⟨-(1/2-α j),n,?_,by ring⟩
    rw [abs_neg,abs_of_pos (by linarith [(hia j).2])]
    linarith [hsmall j]
  · refine ⟨1/2-α j,n,?_,by ring⟩
    rw [abs_of_pos (by linarith [(hia j).2])]
    linarith [hsmall j]

/-- On the actual original paired critical source, central-chart Zak tests
of the constructed half-Weyl image are faithful. No compact kernel or moment
representation is supplied as a premise. -/
theorem halfWeylZakCentralChart_faithful (α β : ℕ+ → ℝ)
    (hia : ∀ j, 0 < α j ∧ α j < 1/2) (hib : ∀ j, 0 < β j ∧ β j < 1/2)
    (hsmall : ∀ j, 1/4 ≤ β j) (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier (criticalPhaseTailCarrier α hia 0 0) T)
    (hFT : AtomicOnCarrier (criticalPhaseTailCarrier β hib 0 0) (𝓕 T))
    (hz : ∀ (f g : SchwartzMap ℝ ℂ),
      (∀ x : ℝ, 1/2 ≤ |x| → f x=0) →
      (∀ x : ℝ, 1/2 ≤ |x| → g x=0) → zakTensorAction (halfWeylDistributionCLM T) f g=0) : T=0 := by
  have hw := halfWeylDistribution_atomic_records α β hia hib T hT hFT
  have he := zakCentralChart_faithful _ _ (halfWeylDistributionCLM T) hw.1 hw.2
    (halfWeylCarrier_cell α hia) (halfWeylCarrier_quarter β hib hsmall) hz
  apply halfWeylDistribution_injective
  simpa only [map_zero] using he

end
end MeyerGeneralProblem.Adaptive
