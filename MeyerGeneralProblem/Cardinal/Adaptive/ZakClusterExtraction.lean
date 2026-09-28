module

public import MeyerGeneralProblem.Cardinal.Adaptive.HalfNewtonLocalization

@[expose] public section

/-! # Compact Fourier probes extract actual complete physical clusters -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open scoped FourierTransform

/-- Integer Fourier characters are invariant under every integer spatial shift. -/
theorem combModulationCharacter_int_translate (m n : ℤ) (a : ℝ) :
    combModulationCharacter (m : ℝ) (a+(n : ℝ))=combModulationCharacter (m : ℝ) a := by
  have he : combModulationCharacter (m : ℝ) (a+(n : ℝ))=
      combModulationCharacter (m : ℝ) a*combModulationCharacter (m : ℝ) (n : ℝ) := by
    simp only [combModulationCharacter_eq_exp]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [he,combModulationCharacter_int_int,mul_one]

/-- The full periodization of the compact Fourier probe equals its exact
integer character on every translated quarter-cell. -/
theorem zakChartFourierProbe_periodization (m n : ℤ) (a : ℝ) (ha : |a| ≤ 1/4) :
    zakPeriodizedTestFunction (zakChartFourierProbe m) (a+(n : ℝ))=
      combModulationCharacter (m : ℝ) (a+(n : ℝ)) := by
  have hp : zakPeriodizedTestFunction (zakChartFourierProbe m) (a+(n : ℝ))=
      zakPeriodizedTestFunction (zakChartFourierProbe m) a := by
    simpa only [mul_one] using
      (zakPeriodizedTestFunction_periodic (zakChartFourierProbe m)).int_mul n a
  rw [hp,zakPeriodizedTestFunction_eq_of_central _ (zakChartFourierProbe_zero m) a ha,
    zakChartFourierProbe,combSchwartzModulation_apply,zakCentralCutoff_one a ha,mul_one,
    combModulationCharacter_int_translate]

/-- A compact Fourier probe extracts exactly a whole translated original
source whenever the true Fourier carrier lies in translated quarter-cells.
This is a distribution identity, not an assumed coefficient reading. -/
theorem zakPhysicalSlice_chartFourierProbe (S : LocallyFiniteCarrier)
    (T : TemperedDistribution ℝ ℂ) (hFT : AtomicOnCarrier S (𝓕 T))
    (hS : ∀ x ∈ S.carrier, ∃ (a : ℝ) (n : ℤ), |a| ≤ 1/4 ∧ x=a+(n : ℝ))
    (m : ℤ) :
    zakPhysicalSlice T (zakChartFourierProbe m)=combDistributionTranslation (-(m : ℝ)) T := by
  have he : 𝓕 (zakPhysicalSlice T (zakChartFourierProbe m))=
      𝓕 (combDistributionTranslation (-(m : ℝ)) T) := by
    rw [fourier_zakPhysicalSlice,fourier_combDistributionTranslation,neg_neg]
    ext f
    rw [TemperedDistribution.smulLeftCLM_apply_apply,combDistributionModulation_apply]
    apply sub_eq_zero.mp
    rw [← map_sub]
    apply hFT
    intro x hx
    obtain ⟨a,n,ha,rfl⟩ := hS x hx
    simp only [_root_.sub_apply,SchwartzMap.smulLeftCLM_apply_apply
      (zakPeriodizedTestFunction_temperate _),smul_eq_mul,combSchwartzModulation_apply,
      zakChartFourierProbe_periodization m n a ha,sub_self]
  have hi := congrArg (fun U : TemperedDistribution ℝ ℂ => 𝓕⁻ U) he
  simpa only [FourierTransform.fourierInv_fourier_eq] using hi

/-- Exact signed integer-cluster extraction for every physical Schwartz test,
from the complete actual half-Weyl Fourier carrier. -/
theorem zakTensorAction_chartFourierProbe (β : ℕ+ → ℝ)
    (hib : ∀ j, 0 < β j ∧ β j < 1/2) (hsmall : ∀ j, 1/4 ≤ β j)
    (T : TemperedDistribution ℝ ℂ)
    (hFT : AtomicOnCarrier ((criticalPhaseTailCarrier β hib 0 0).translate (-1/2)) (𝓕 T))
    (f : SchwartzMap ℝ ℂ) (m : ℤ) :
    zakTensorAction T f (zakChartFourierProbe m)=T (combSchwartzTranslation (-(m : ℝ)) f) := by
  have he := congrArg (fun U : TemperedDistribution ℝ ℂ => U f)
    (zakPhysicalSlice_chartFourierProbe _ T hFT (halfWeylCarrier_quarter β hib hsmall) m)
  simpa only [zakPhysicalSlice_apply,combDistributionTranslation_apply] using he

private theorem central_test_other_cell (f : SchwartzMap ℝ ℂ)
    (hf : ∀ x : ℝ, 1/2 ≤ |x| → f x=0) (a : ℝ) (ha : |a| < 1/2)
    (n m : ℤ) (hn : n ≠ m) : f ((n : ℝ)+a-(m : ℝ))=0 := by
  apply hf
  have hd : n-m ≠ 0 := sub_ne_zero.mpr hn
  have hnabs : (1 : ℝ) ≤ |((n-m : ℤ) : ℝ)| := by
    by_cases hp : 0 ≤ n-m
    · have h : (1 : ℤ) ≤ n-m := by omega
      have hr : (1 : ℝ) ≤ ((n-m : ℤ) : ℝ) := by exact_mod_cast h
      rw [abs_of_nonneg (by positivity)]
      exact hr
    · have h : n-m ≤ (-1 : ℤ) := by omega
      have hr : ((n-m : ℤ) : ℝ) ≤ -1 := by exact_mod_cast h
      rw [abs_of_nonpos (by linarith)]
      linarith
  have h := abs_add_le ((n : ℝ)+a-(m : ℝ)) (-a)
  rw [show (n : ℝ)+a-(m : ℝ)+(-a)=((n-m : ℤ) : ℝ) by push_cast; ring,abs_neg] at h
  linarith

/-- The exact asymmetric critical cluster thresholds suffice for a translated
central test to annihilate the entire original source. Other clusters vanish
by support, not by dropping them from the distribution. -/
theorem halfWeylSource_cluster_zero (α : ℕ+ → ℝ)
    (hia : ∀ j, 0 < α j ∧ α j < 1/2) (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier ((criticalPhaseTailCarrier α hia 0 0).translate (-1/2)) T)
    (f : SchwartzMap ℝ ℂ) (hf : ∀ x : ℝ, 1/2 ≤ |x| → f x=0) (m : ℤ)
    (hminus : ∀ j : ℕ+, (j : ℕ) ≤ m.natAbs → f (-(1/2-α j))=0)
    (hplus : ∀ j : ℕ+, (j : ℕ) ≤ (m+1).natAbs → f (1/2-α j)=0) :
    T (combSchwartzTranslation (-(m : ℝ)) f)=0 := by
  apply hT
  intro x hx
  rw [halfWeylCriticalSet_eq_translate] at hx
  rcases hx with ⟨j,n,hn,rfl⟩|⟨j,n,hn,rfl⟩
  · rw [combSchwartzTranslation_apply]
    by_cases hnm : n=m
    · subst n
      rw [show -(m : ℝ)+((m : ℝ)-(1/2-α j))=-(1/2-α j) by ring]
      exact hminus j hn
    · have ha : |-(1/2-α j)| < 1/2 := by
        rw [abs_neg,abs_of_pos (by linarith [(hia j).2])]
        linarith [(hia j).1]
      convert central_test_other_cell f hf _ ha n m hnm using 1
      congr 1
      ring
  · rw [combSchwartzTranslation_apply]
    by_cases hnm : n=m
    · subst n
      rw [show -(m : ℝ)+((m : ℝ)+(1/2-α j))=1/2-α j by ring]
      exact hplus j hn
    · have ha : |1/2-α j| < 1/2 := by
        rw [abs_of_pos (by linarith [(hia j).2])]
        linarith [(hia j).1]
      convert central_test_other_cell f hf _ ha n m hnm using 1
      congr 1
      ring

/-- Every ordered Newton product kills its earlier positive phase nodes. -/
theorem halfNewtonProduct_phase_zero (ε : ℕ+ → ℝ) (i : ℕ) (j : ℕ+) (hj : (j : ℕ) ≤ i) :
    halfNewtonProduct ε i (ε j)=0 := by
  have hjpos : 0 < (j : ℕ) := j.property
  have hr : (j : ℕ)-1 ∈ Finset.range i := Finset.mem_range.mpr (by omega)
  have he : (j : ℕ)-1+1=(j : ℕ) := by omega
  unfold halfNewtonProduct
  apply Finset.prod_eq_zero hr
  have hp : (⟨(j : ℕ)-1+1,by omega⟩ : ℕ+)=j := Subtype.ext he
  rw [hp,sub_self]

/-- Every ordered Newton product kills the same earlier negative phase nodes. -/
theorem halfNewtonProduct_neg_phase_zero (ε : ℕ+ → ℝ) (i : ℕ) (j : ℕ+)
    (hj : (j : ℕ) ≤ i) : halfNewtonProduct ε i (-(ε j))=0 := by
  have he : criticalNewtonNode (-(ε j))=criticalNewtonNode (ε j) := by
    simp only [criticalNewtonNode,mul_neg,Real.cos_neg]
  simpa only [halfNewtonProduct,he] using halfNewtonProduct_phase_zero ε i j hj

/-- The actual characteristic-adjusted Newton row has zero reading on every
interior cluster, with the exact negative and positive threshold endpoints. -/
theorem halfNewtonRow_cluster_zero (α : ℕ+ → ℝ)
    (hia : ∀ j, 0 < α j ∧ α j < 1/2) (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier ((criticalPhaseTailCarrier α hia 0 0).translate (-1/2)) T)
    (i : ℕ) (e : Bool) (m : ℤ) (hm : m.natAbs ≤ i) (hm' : (m+1).natAbs ≤ i) :
    T (combSchwartzTranslation (-(m : ℝ))
      (combSchwartzModulation (1/2) (halfNewtonTest (fun j => 1/2-α j) i e)))=0 := by
  apply halfWeylSource_cluster_zero α hia T hT
  · intro x hx
    simp only [combSchwartzModulation_apply,halfNewtonTest_apply,zakCentralCutoff_zero x hx,zero_mul,mul_zero]
  · intro j hj
    simp only [combSchwartzModulation_apply,halfNewtonTest_apply,halfNewtonFunction,
      halfNewtonProduct_neg_phase_zero _ i j (hj.trans hm),mul_zero]
  · intro j hj
    simp only [combSchwartzModulation_apply,halfNewtonTest_apply,halfNewtonFunction,
      halfNewtonProduct_phase_zero _ i j (hj.trans hm'),mul_zero]

/-- The compact Fourier readings of a genuine Newton row vanish throughout
its exact interior band, by actual source extraction and physical support. -/
theorem halfNewtonRow_chartFourierProbe_zero (α β : ℕ+ → ℝ)
    (hia : ∀ j, 0 < α j ∧ α j < 1/2) (hib : ∀ j, 0 < β j ∧ β j < 1/2)
    (hsmall : ∀ j, 1/4 ≤ β j) (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier ((criticalPhaseTailCarrier α hia 0 0).translate (-1/2)) T)
    (hFT : AtomicOnCarrier ((criticalPhaseTailCarrier β hib 0 0).translate (-1/2)) (𝓕 T))
    (i : ℕ) (e : Bool) (m : ℤ) (hm : m.natAbs ≤ i) (hm' : (m+1).natAbs ≤ i) :
    zakTensorAction T (combSchwartzModulation (1/2) (halfNewtonTest (fun j => 1/2-α j) i e))
      (zakChartFourierProbe m)=0 := by
  rw [zakTensorAction_chartFourierProbe β hib hsmall T hFT]
  exact halfNewtonRow_cluster_zero α hia T hT i e m hm hm'

end
end MeyerGeneralProblem.Adaptive
