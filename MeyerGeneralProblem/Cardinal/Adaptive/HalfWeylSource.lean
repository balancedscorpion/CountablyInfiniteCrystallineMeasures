module

public import MeyerGeneralProblem.Cardinal.Adaptive.CriticalForwardMap

@[expose] public section

/-! # Actual half-Weyl source recentering for the full half-seam analysis -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open scoped FourierTransform

/-- The literal characteristic-preserving half-Weyl change of the whole source. -/
def halfWeylDistributionCLM : TemperedDistribution ℝ ℂ →L[ℂ] TemperedDistribution ℝ ℂ :=
  (combDistributionModulation (-1/2)).comp (combDistributionTranslation (-1/2))

/-- Its complete Fourier-side counterpart retains the opposite modulation sign. -/
def halfWeylSpectralCLM : TemperedDistribution ℝ ℂ →L[ℂ] TemperedDistribution ℝ ℂ :=
  (combDistributionTranslation (-1/2)).comp (combDistributionModulation (1/2))

private theorem fourier_modulation (a : ℝ) (T : TemperedDistribution ℝ ℂ) :
    𝓕 (combDistributionModulation a T)=combDistributionTranslation a (𝓕 T) := by
  ext f
  change T (combSchwartzModulation a (𝓕 f))=T (𝓕 (combSchwartzTranslation a f))
  change T (𝓕 (combSchwartzTranslation a (𝓕⁻ (𝓕 f))))=_
  rw [FourierTransform.fourierInv_fourier_eq]

/-- Exact Fourier covariance of the whole half-Weyl source map. -/
theorem fourier_halfWeylDistribution (T : TemperedDistribution ℝ ℂ) :
    𝓕 (halfWeylDistributionCLM T)=halfWeylSpectralCLM (𝓕 T) := by
  change 𝓕 (combDistributionModulation (-1/2) (combDistributionTranslation (-1/2) T))=_
  rw [fourier_modulation,fourier_combDistributionTranslation]
  norm_num [halfWeylSpectralCLM]

/-- The exact recentered critical carrier retains the asymmetric endpoint cells. -/
def halfWeylCriticalSet (ε : ℕ+ → ℝ) : Set ℝ :=
  {x | ∃ (j : ℕ+) (n : ℤ), (j : ℕ) ≤ n.natAbs ∧ x=(n : ℝ)-ε j} ∪
  {x | ∃ (j : ℕ+) (n : ℤ), (j : ℕ) ≤ (n+1).natAbs ∧ x=(n : ℝ)+ε j}

/-- Every atom and its original threshold transforms by the literal half shift.
The second branch has |n+1|, including the unequal cells zero and minus one. -/
theorem halfWeylCriticalSet_eq_translate (α : ℕ+ → ℝ)
    (hia : ∀ j, 0 < α j ∧ α j < 1/2) :
    ((criticalPhaseTailCarrier α hia 0 0).translate (-1/2)).carrier=
      halfWeylCriticalSet (fun j => 1/2-α j) := by
  ext x
  constructor
  · rintro ⟨y,⟨j,u,n,hn,rfl⟩,rfl⟩
    simp only [criticalTailPhases_zero] at *
    cases u with
    | true =>
        refine Or.inl ⟨j,n,by simpa using hn,?_⟩
        simp only [signedPhase,ite_true]
        ring
    | false =>
        refine Or.inr ⟨j,n-1,by simpa using hn,?_⟩
        simp only [signedPhase,Bool.false_eq_true,ite_false,Int.cast_sub,Int.cast_one]
        ring
  · rintro (⟨j,n,hn,rfl⟩|⟨j,n,hn,rfl⟩)
    · refine ⟨(n : ℝ)+signedPhase true (α j),⟨j,true,n,by simpa using hn,?_⟩,?_⟩
      · simp only [criticalTailPhases_zero]
      · simp only [signedPhase,ite_true]
        ring
    · refine ⟨((n+1 : ℤ) : ℝ)+signedPhase false (α j),⟨j,false,n+1,by simpa using hn,?_⟩,?_⟩
      · simp only [criticalTailPhases_zero]
      · simp only [signedPhase,Bool.false_eq_true,ite_false,Int.cast_add,Int.cast_one]
        ring

/-- Both complete source records are genuinely recentered; modulation changes
coefficients but removes no whole record or accumulation contribution. -/
theorem halfWeylDistribution_atomic_records (α β : ℕ+ → ℝ)
    (hia : ∀ j, 0 < α j ∧ α j < 1/2) (hib : ∀ j, 0 < β j ∧ β j < 1/2)
    (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier (criticalPhaseTailCarrier α hia 0 0) T)
    (hFT : AtomicOnCarrier (criticalPhaseTailCarrier β hib 0 0) (𝓕 T)) :
    AtomicOnCarrier ((criticalPhaseTailCarrier α hia 0 0).translate (-1/2))
      (halfWeylDistributionCLM T) ∧
    AtomicOnCarrier ((criticalPhaseTailCarrier β hib 0 0).translate (-1/2))
      (𝓕 (halfWeylDistributionCLM T)) := by
  constructor
  · exact atomicOnCarrier_combDistributionModulation _ _
      (atomicOnCarrier_combDistributionTranslation _ T hT (-1/2)) (-1/2)
  · rw [fourier_halfWeylDistribution]
    exact atomicOnCarrier_combDistributionTranslation _ _
      (atomicOnCarrier_combDistributionModulation _ (𝓕 T) hFT (1/2)) (-1/2)

/-- Actual original-native half-Weyl map at the same order. -/
def halfWeylNativeCLM (p : ℕ) :
    HermiteScale (-(p : ℤ)) →L[ℂ] HermiteScale (-(p : ℤ)) :=
  (nativeModulation p (-1/2)).comp (nativeTranslation p (-1/2))

/-- The native map agrees with the whole recentering on all Schwartz tests. -/
theorem halfWeylNativeCLM_realizes (p : ℕ) (T : HermiteScale (-(p : ℤ))) :
    hermiteScaleDistribution p (halfWeylNativeCLM p T)=
      halfWeylDistributionCLM (hermiteScaleDistribution p T) := by
  change hermiteScaleDistribution p (nativeModulation p (-1/2) (nativeTranslation p (-1/2) T))=_
  rw [nativeModulation_realizes,nativeTranslation_realizes]
  rfl

/-- The original native order is preserved by a genuine bounded operator. -/
theorem halfWeylNativeCLM_bound (p : ℕ) :
    ∃ C > 0, ∀ T : HermiteScale (-(p : ℤ)), ‖halfWeylNativeCLM p T‖ ≤ C*‖T‖ := by
  refine ⟨‖halfWeylNativeCLM p‖+1,by positivity,fun T => ?_⟩
  exact ((halfWeylNativeCLM p).le_opNorm T).trans
    (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))


private theorem distributionTranslation_cancel (a : ℝ) (T : TemperedDistribution ℝ ℂ) :
    combDistributionTranslation (-a) (combDistributionTranslation a T)=T := by
  ext f
  change T (combSchwartzTranslation a (combSchwartzTranslation (-a) f))=T f
  congr 1
  ext x
  simp only [combSchwartzTranslation_apply,neg_add_cancel_left]

private theorem distributionModulation_cancel (a : ℝ) (T : TemperedDistribution ℝ ℂ) :
    combDistributionModulation (-a) (combDistributionModulation a T)=T := by
  apply (FourierTransform.fourierEquiv ℂ (TemperedDistribution ℝ ℂ)).injective
  change 𝓕 (combDistributionModulation (-a) (combDistributionModulation a T))=𝓕 T
  rw [fourier_modulation,fourier_modulation,distributionTranslation_cancel]

/-- The actual inverse half-Weyl map, with translation and modulation reversed. -/
def halfWeylInverseDistributionCLM : TemperedDistribution ℝ ℂ →L[ℂ] TemperedDistribution ℝ ℂ :=
  (combDistributionTranslation (1/2)).comp (combDistributionModulation (1/2))

/-- Full invertibility prevents loss of any original source direction. -/
theorem halfWeylInverse_left (T : TemperedDistribution ℝ ℂ) :
    halfWeylInverseDistributionCLM (halfWeylDistributionCLM T)=T := by
  change combDistributionTranslation (1/2) (combDistributionModulation (1/2)
    (combDistributionModulation (-1/2) (combDistributionTranslation (-1/2) T)))=T
  rw [show (-1/2 : ℝ)=-(1/2) by ring]
  have hm := distributionModulation_cancel (-(1/2)) (combDistributionTranslation (-(1/2)) T)
  simp only [neg_neg] at hm
  rw [hm]
  simpa only [neg_neg] using distributionTranslation_cancel (-(1/2)) T

/-- The inverse is also a right inverse on the entire tempered space. -/
theorem halfWeylInverse_right (T : TemperedDistribution ℝ ℂ) :
    halfWeylDistributionCLM (halfWeylInverseDistributionCLM T)=T := by
  change combDistributionModulation (-1/2) (combDistributionTranslation (-1/2)
    (combDistributionTranslation (1/2) (combDistributionModulation (1/2) T)))=T
  rw [show (-1/2 : ℝ)=-(1/2) by ring,distributionTranslation_cancel,distributionModulation_cancel]

/-- Exact whole-source injectivity of the half-Weyl change. -/
theorem halfWeylDistribution_injective : Function.Injective halfWeylDistributionCLM := by
  intro T U h
  have hh := congrArg halfWeylInverseDistributionCLM h
  simpa only [halfWeylInverse_left] using hh

/-- The actual inverse recentering preserves the same original native order. -/
def halfWeylInverseNativeCLM (p : ℕ) :
    HermiteScale (-(p : ℤ)) →L[ℂ] HermiteScale (-(p : ℤ)) :=
  (nativeTranslation p (1/2)).comp (nativeModulation p (1/2))

/-- Equality of the whole inverse with its actual original-native realization. -/
theorem halfWeylInverseNativeCLM_realizes (p : ℕ) (T : HermiteScale (-(p : ℤ))) :
    hermiteScaleDistribution p (halfWeylInverseNativeCLM p T)=
      halfWeylInverseDistributionCLM (hermiteScaleDistribution p T) := by
  change hermiteScaleDistribution p (nativeTranslation p (1/2) (nativeModulation p (1/2) T))=_
  rw [nativeTranslation_realizes,nativeModulation_realizes]
  rfl

/-- Both directions of the half-Weyl coordinate change are bounded at the
same original order; this estimate precedes any compact Zak construction. -/
theorem halfWeylInverseNativeCLM_bound (p : ℕ) :
    ∃ C > 0, ∀ T : HermiteScale (-(p : ℤ)), ‖halfWeylInverseNativeCLM p T‖ ≤ C*‖T‖ := by
  refine ⟨‖halfWeylInverseNativeCLM p‖+1,by positivity,fun T => ?_⟩
  exact ((halfWeylInverseNativeCLM p).le_opNorm T).trans
    (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))

end
end MeyerGeneralProblem.Adaptive
