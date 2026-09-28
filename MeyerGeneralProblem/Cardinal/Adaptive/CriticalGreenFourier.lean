module

public import MeyerGeneralProblem.Cardinal.Adaptive.CriticalGreenSupport

@[expose] public section

/-! # The actual two-direction head inverse and its Fourier normalization -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open scoped FourierTransform BigOperators

/-- The accepted cosine head symbol is even with the actual normalization. -/
theorem criticalHeadTrigProduct_neg {k : ℕ} (α : Fin k → ℝ) (x : ℝ) :
    criticalHeadTrigProduct α (-x) = criticalHeadTrigProduct α x := by
  simp [criticalHeadTrigProduct,criticalNewtonNode,mul_neg,Real.cos_neg]

/-- The accepted head symbol is exactly one-periodic. -/
theorem criticalHeadTrigProduct_periodic {k : ℕ} (α : Fin k → ℝ) :
    Function.Periodic (criticalHeadTrigProduct α) 1 := by
  intro x
  simp only [criticalHeadTrigProduct,criticalNewtonNode]
  rw [show 2*Real.pi*(x+1)=2*Real.pi*x+2*Real.pi by ring,Real.cos_add_two_pi]

private theorem modulationCharacter_eq_critical (n : ℤ) (x : ℝ) :
    combModulationCharacter (n : ℝ) x = criticalCharacter n x := by
  rw [combModulationCharacter_eq_exp]
  simp only [criticalCharacter,Complex.ofReal_intCast]

/-- Fourier of the actual centered difference on tests is multiplication by
its exact cosine product, with both shifts and signs retained. -/
theorem criticalHeadDifference_fourier_apply {k : ℕ} (α : Fin k → ℝ)
    (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    𝓕 (criticalHeadDifferenceTestCLM α f) x = criticalHeadTrigProduct α x*𝓕 f x := by
  change (FourierTransform.fourierCLM ℂ (SchwartzMap ℝ ℂ))
    (criticalHeadDifferenceTestCLM α f) x = _
  simp only [criticalHeadDifferenceTestCLM,_root_.sum_apply,_root_.smul_apply,
    map_sum,map_smul,FourierTransform.fourierCLM_apply,smul_eq_mul,
    fourier_combSchwartzTranslation]
  simp only [← Int.cast_sub,modulationCharacter_eq_critical,← mul_assoc,← Finset.sum_mul,
    criticalHeadDifferenceCoeff_symbol]

/-- Evenness ensures the same multiplier for inverse Fourier normalization. -/
theorem criticalHeadDifference_fourierInv_apply {k : ℕ} (α : Fin k → ℝ)
    (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    𝓕⁻ (criticalHeadDifferenceTestCLM α f) x = criticalHeadTrigProduct α x*𝓕⁻ f x := by
  change 𝓕 (criticalHeadDifferenceTestCLM α f) (-x) = criticalHeadTrigProduct α x*𝓕 f (-x)
  rw [criticalHeadDifference_fourier_apply,criticalHeadTrigProduct_neg]

/-- The genuine Schwartz multiplier, constructed from the actual finite
head difference through Fourier conjugacy. -/
def criticalHeadMultiplierTestCLM {k : ℕ} (α : Fin k → ℝ) :
    SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
  (FourierTransform.fourierCLM ℂ (SchwartzMap ℝ ℂ)).comp
    ((criticalHeadDifferenceTestCLM α).comp
      (FourierTransform.fourierInvCLM ℂ (SchwartzMap ℝ ℂ)))

/-- The constructed multiplier acts pointwise by the accepted cosine product. -/
theorem criticalHeadMultiplierTestCLM_apply {k : ℕ} (α : Fin k → ℝ)
    (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    criticalHeadMultiplierTestCLM α f x = criticalHeadTrigProduct α x*f x := by
  change 𝓕 (criticalHeadDifferenceTestCLM α (𝓕⁻ f)) x = _
  rw [criticalHeadDifference_fourier_apply,FourierTransform.fourier_fourierInv_eq]

/-- Fourier intertwines actual multiplication with the centered difference. -/
theorem fourier_criticalHeadMultiplierTestCLM {k : ℕ} (α : Fin k → ℝ)
    (f : SchwartzMap ℝ ℂ) :
    𝓕 (criticalHeadMultiplierTestCLM α f) = criticalHeadDifferenceTestCLM α (𝓕 f) := by
  apply (FourierTransform.fourierEquiv ℂ (SchwartzMap ℝ ℂ)).symm.injective
  change 𝓕⁻ (𝓕 (criticalHeadMultiplierTestCLM α f)) = 𝓕⁻ (criticalHeadDifferenceTestCLM α (𝓕 f))
  rw [FourierTransform.fourierInv_fourier_eq]
  ext x
  rw [criticalHeadMultiplierTestCLM_apply,criticalHeadDifference_fourierInv_apply,
    FourierTransform.fourierInv_fourier_eq]

/-- The reverse test-space intertwining uses the exact even head symbol. -/
theorem criticalHeadMultiplierTestCLM_fourier {k : ℕ} (α : Fin k → ℝ)
    (f : SchwartzMap ℝ ℂ) :
    criticalHeadMultiplierTestCLM α (𝓕 f) = 𝓕 (criticalHeadDifferenceTestCLM α f) := by
  ext x
  rw [criticalHeadMultiplierTestCLM_apply,criticalHeadDifference_fourier_apply]

/-- Actual whole distribution multiplication by the head cosine product. -/
def criticalHeadMultiplierDistributionCLM {k : ℕ} (α : Fin k → ℝ) :
    TemperedDistribution ℝ ℂ →L[ℂ] TemperedDistribution ℝ ℂ :=
  PointwiseConvergenceCLM.precomp ℂ (criticalHeadMultiplierTestCLM α)

/-- Distribution Fourier turns actual head multiplication into the centered difference. -/
theorem fourier_criticalHeadMultiplierDistribution {k : ℕ} (α : Fin k → ℝ)
    (T : TemperedDistribution ℝ ℂ) :
    𝓕 (criticalHeadMultiplierDistributionCLM α T) = criticalHeadDifferenceDistributionCLM α (𝓕 T) := by
  ext f
  change T (criticalHeadMultiplierTestCLM α (𝓕 f)) = T (𝓕 (criticalHeadDifferenceTestCLM α f))
  rw [criticalHeadMultiplierTestCLM_fourier]

/-- Distribution Fourier turns the centered difference into actual multiplication. -/
theorem fourier_criticalHeadDifferenceDistribution {k : ℕ} (α : Fin k → ℝ)
    (T : TemperedDistribution ℝ ℂ) :
    𝓕 (criticalHeadDifferenceDistributionCLM α T) = criticalHeadMultiplierDistributionCLM α (𝓕 T) := by
  ext f
  change T (criticalHeadDifferenceTestCLM α (𝓕 f)) = T (𝓕 (criticalHeadMultiplierTestCLM α f))
  rw [fourier_criticalHeadMultiplierTestCLM]

private theorem integerGreenAction_head_multiplier {k : ℕ} (α : Fin k → ℝ)
    (w : ℤ → ℂ) (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    integerGreenAction w (criticalHeadMultiplierTestCLM α f) x =
      criticalHeadTrigProduct α x*integerGreenAction w f x := by
  have hp (t : ℤ) : criticalHeadTrigProduct α (x+(t : ℝ))=criticalHeadTrigProduct α x := by
    simpa using (criticalHeadTrigProduct_periodic α).int_mul t x
  simp only [integerGreenAction,criticalHeadMultiplierTestCLM_apply,hp]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  ring

/-- The actual Green inverse and every accepted periodic head multiplier commute. -/
theorem criticalGreenTestCLM_head_multiplier {k l : ℕ} (hk : 1 ≤ k)
    (α : Fin k → ℝ) (ha : Function.Injective α) (hi : ∀ i, 0 < α i ∧ α i < 1/2)
    (β : Fin l → ℝ) (f : SchwartzMap ℝ ℂ) :
    criticalGreenTestCLM α ha hi (criticalHeadMultiplierTestCLM β f) =
      criticalHeadMultiplierTestCLM β (criticalGreenTestCLM α ha hi f) := by
  ext x
  rw [criticalGreenTestCLM_bilateral hk,criticalHeadMultiplierTestCLM_apply,
    criticalGreenTestCLM_bilateral hk,integerGreenAction_head_multiplier,
    integerGreenAction_head_multiplier]
  ring

/-- Whole-distribution head multiplier commutation holds before any source restriction. -/
theorem criticalGreenDistribution_head_multiplier {k l : ℕ} (hk : 1 ≤ k)
    (α : Fin k → ℝ) (ha : Function.Injective α) (hi : ∀ i, 0 < α i ∧ α i < 1/2)
    (β : Fin l → ℝ) (T : TemperedDistribution ℝ ℂ) :
    criticalGreenDistributionCLM α ha hi (criticalHeadMultiplierDistributionCLM β T) =
      criticalHeadMultiplierDistributionCLM β (criticalGreenDistributionCLM α ha hi T) := by
  ext f
  change T (criticalHeadMultiplierTestCLM β (criticalGreenTestCLM α ha hi f)) =
    T (criticalGreenTestCLM α ha hi (criticalHeadMultiplierTestCLM β f))
  rw [criticalGreenTestCLM_head_multiplier hk]

/-- Actual inverse for head multiplication, defined by Fourier conjugation of
our complete Green difference inverse. -/
def criticalMultiplierInverseCLM {k : ℕ} (α : Fin k → ℝ)
    (ha : Function.Injective α) (hi : ∀ i, 0 < α i ∧ α i < 1/2) :
    TemperedDistribution ℝ ℂ →L[ℂ] TemperedDistribution ℝ ℂ :=
  (FourierTransform.fourierInvCLM ℂ (TemperedDistribution ℝ ℂ)).comp
    ((criticalGreenDistributionCLM α ha hi).comp
      (FourierTransform.fourierCLM ℂ (TemperedDistribution ℝ ℂ)))

/-- The conjugated operator retains exactly the complete transformed Green record. -/
theorem fourier_criticalMultiplierInverse {k : ℕ} (α : Fin k → ℝ)
    (ha : Function.Injective α) (hi : ∀ i, 0 < α i ∧ α i < 1/2)
    (T : TemperedDistribution ℝ ℂ) :
    𝓕 (criticalMultiplierInverseCLM α ha hi T) = criticalGreenDistributionCLM α ha hi (𝓕 T) :=
  FourierTransform.fourier_fourierInv_eq _

/-- The actual cosine-product inverse is a right inverse on all tempered distributions. -/
theorem criticalMultiplierInverse_rightInverse {k : ℕ} (hk : 1 ≤ k) (α : Fin k → ℝ)
    (ha : Function.Injective α) (hi : ∀ i, 0 < α i ∧ α i < 1/2)
    (T : TemperedDistribution ℝ ℂ) :
    criticalHeadMultiplierDistributionCLM α (criticalMultiplierInverseCLM α ha hi T) = T := by
  apply (FourierTransform.fourierEquiv ℂ (TemperedDistribution ℝ ℂ)).injective
  change 𝓕 (criticalHeadMultiplierDistributionCLM α (criticalMultiplierInverseCLM α ha hi T)) = 𝓕 T
  rw [fourier_criticalHeadMultiplierDistribution,fourier_criticalMultiplierInverse,
    criticalGreenDistribution_rightInverse hk]

/-- The Fourier-conjugate inverse commutes with the OTHER head difference,
without requiring or asserting commutation of the two Green inverses. -/
theorem criticalMultiplierInverse_commutes_difference {k l : ℕ} (hk : 1 ≤ k)
    (α : Fin k → ℝ) (ha : Function.Injective α) (hi : ∀ i, 0 < α i ∧ α i < 1/2)
    (β : Fin l → ℝ) (T : TemperedDistribution ℝ ℂ) :
    criticalMultiplierInverseCLM α ha hi (criticalHeadDifferenceDistributionCLM β T) =
      criticalHeadDifferenceDistributionCLM β (criticalMultiplierInverseCLM α ha hi T) := by
  apply (FourierTransform.fourierEquiv ℂ (TemperedDistribution ℝ ℂ)).injective
  change 𝓕 (criticalMultiplierInverseCLM α ha hi (criticalHeadDifferenceDistributionCLM β T)) =
    𝓕 (criticalHeadDifferenceDistributionCLM β (criticalMultiplierInverseCLM α ha hi T))
  rw [fourier_criticalMultiplierInverse,fourier_criticalHeadDifferenceDistribution,
    fourier_criticalHeadDifferenceDistribution,fourier_criticalMultiplierInverse,
    criticalGreenDistribution_head_multiplier hk]

/-- Whole preliminary inverse before the finite head-hole repair. -/
def criticalWholePreinverseCLM {k : ℕ} (α β : Fin k → ℝ)
    (ha : Function.Injective α) (hia : ∀ i, 0 < α i ∧ α i < 1/2)
    (hb : Function.Injective β) (hib : ∀ i, 0 < β i ∧ β i < 1/2) :
    TemperedDistribution ℝ ℂ →L[ℂ] TemperedDistribution ℝ ℂ :=
  (criticalMultiplierInverseCLM α ha hia).comp (criticalGreenDistributionCLM β hb hib)

/-- The complete physical equation retains every head contribution from the other inverse. -/
theorem criticalWholePreinverse_multiplier {k : ℕ} (hk : 1 ≤ k) (α β : Fin k → ℝ)
    (ha : Function.Injective α) (hia : ∀ i, 0 < α i ∧ α i < 1/2)
    (hb : Function.Injective β) (hib : ∀ i, 0 < β i ∧ β i < 1/2)
    (T : TemperedDistribution ℝ ℂ) :
    criticalHeadMultiplierDistributionCLM α (criticalWholePreinverseCLM α β ha hia hb hib T) =
      criticalGreenDistributionCLM β hb hib T :=
  criticalMultiplierInverse_rightInverse hk α ha hia _

/-- The complete Fourier-side equation follows from periodic commutation. -/
theorem criticalWholePreinverse_difference {k : ℕ} (hk : 1 ≤ k) (α β : Fin k → ℝ)
    (ha : Function.Injective α) (hia : ∀ i, 0 < α i ∧ α i < 1/2)
    (hb : Function.Injective β) (hib : ∀ i, 0 < β i ∧ β i < 1/2)
    (T : TemperedDistribution ℝ ℂ) :
    criticalHeadDifferenceDistributionCLM β (criticalWholePreinverseCLM α β ha hia hb hib T) =
      criticalMultiplierInverseCLM α ha hia T := by
  change criticalHeadDifferenceDistributionCLM β
    (criticalMultiplierInverseCLM α ha hia (criticalGreenDistributionCLM β hb hib T)) = _
  rw [← criticalMultiplierInverse_commutes_difference hk,
    criticalGreenDistribution_rightInverse hk]

/-- The preliminary whole inverse solves the exact two-direction head equation. -/
theorem criticalWholePreinverse_rightInverse {k : ℕ} (hk : 1 ≤ k) (α β : Fin k → ℝ)
    (ha : Function.Injective α) (hia : ∀ i, 0 < α i ∧ α i < 1/2)
    (hb : Function.Injective β) (hib : ∀ i, 0 < β i ∧ β i < 1/2)
    (T : TemperedDistribution ℝ ℂ) :
    criticalHeadMultiplierDistributionCLM α
      (criticalHeadDifferenceDistributionCLM β (criticalWholePreinverseCLM α β ha hia hb hib T)) = T := by
  rw [criticalWholePreinverse_difference hk,criticalMultiplierInverse_rightInverse hk]

/-- Inverse native Fourier represents the actual inverse distributional Fourier map. -/
theorem hermiteFourier_symm_represents {p : ℕ} (T : HermiteScale (-(p : ℤ))) :
    hermiteScaleDistribution p ((hermiteFourier (-(p : ℤ))).symm T) =
      𝓕⁻ (hermiteScaleDistribution p T) := by
  have h := hermiteFourier_represents_distributionalFourier p ((hermiteFourier (-(p : ℤ))).symm T)
  rw [LinearIsometryEquiv.apply_symm_apply] at h
  have h' := congrArg (fun U : TemperedDistribution ℝ ℂ => 𝓕⁻ U) h
  simpa only [FourierTransform.fourierInv_fourier_eq] using h'.symm

/-- Actual native Fourier-conjugate Green inverse with exactly one original-order loss. -/
def criticalMultiplierInverseNativeCLM {k : ℕ} (α : Fin k → ℝ)
    (ha : Function.Injective α) (hi : ∀ i, 0 < α i ∧ α i < 1/2) (p : ℕ) :
    HermiteScale (-(p : ℤ)) →L[ℂ] HermiteScale (-((p+1 : ℕ) : ℤ)) :=
  (hermiteFourier (-((p+1 : ℕ) : ℤ))).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((criticalGreenNativeCLM α ha hi p).comp
      (hermiteFourier (-(p : ℤ))).toContinuousLinearEquiv.toContinuousLinearMap)

/-- Native Fourier conjugation agrees with the complete distribution on every Schwartz test. -/
theorem criticalMultiplierInverseNativeCLM_realizes {k : ℕ} (α : Fin k → ℝ)
    (ha : Function.Injective α) (hi : ∀ i, 0 < α i ∧ α i < 1/2) (p : ℕ)
    (T : HermiteScale (-(p : ℤ))) :
    hermiteScaleDistribution (p+1) (criticalMultiplierInverseNativeCLM α ha hi p T) =
      criticalMultiplierInverseCLM α ha hi (hermiteScaleDistribution p T) := by
  change hermiteScaleDistribution (p+1)
    ((hermiteFourier (-((p+1 : ℕ) : ℤ))).symm
      (criticalGreenNativeCLM α ha hi p (hermiteFourier (-(p : ℤ)) T))) = _
  rw [hermiteFourier_symm_represents,criticalGreenNativeCLM_realizes,
    hermiteFourier_represents_distributionalFourier]
  rfl

/-- Constructed whole preliminary inverse costs two ORIGINAL native orders,
independently of the number of head factors. -/
def criticalWholePreinverseNativeCLM {k : ℕ} (α β : Fin k → ℝ)
    (ha : Function.Injective α) (hia : ∀ i, 0 < α i ∧ α i < 1/2)
    (hb : Function.Injective β) (hib : ∀ i, 0 < β i ∧ β i < 1/2) (p : ℕ) :
    HermiteScale (-(p : ℤ)) →L[ℂ] HermiteScale (-((p+2 : ℕ) : ℤ)) :=
  (criticalMultiplierInverseNativeCLM α ha hia (p+1)).comp (criticalGreenNativeCLM β hb hib p)

/-- The two-order native preinverse is the actual whole tempered construction. -/
theorem criticalWholePreinverseNativeCLM_realizes {k : ℕ} (α β : Fin k → ℝ)
    (ha : Function.Injective α) (hia : ∀ i, 0 < α i ∧ α i < 1/2)
    (hb : Function.Injective β) (hib : ∀ i, 0 < β i ∧ β i < 1/2) (p : ℕ)
    (T : HermiteScale (-(p : ℤ))) :
    hermiteScaleDistribution (p+2) (criticalWholePreinverseNativeCLM α β ha hia hb hib p T) =
      criticalWholePreinverseCLM α β ha hia hb hib (hermiteScaleDistribution p T) := by
  change hermiteScaleDistribution ((p+1)+1)
    (criticalMultiplierInverseNativeCLM α ha hia (p+1) (criticalGreenNativeCLM β hb hib p T)) = _
  rw [criticalMultiplierInverseNativeCLM_realizes,criticalGreenNativeCLM_realizes]
  rfl

/-- A finite norm bound depends only on p and the two heads, before choosing
any whole input or any infinite tails. No uniformity in head size is asserted. -/
theorem criticalWholePreinverseNativeCLM_bound {k : ℕ} (α β : Fin k → ℝ)
    (ha : Function.Injective α) (hia : ∀ i, 0 < α i ∧ α i < 1/2)
    (hb : Function.Injective β) (hib : ∀ i, 0 < β i ∧ β i < 1/2) (p : ℕ) :
    ∃ C > 0, ∀ T : HermiteScale (-(p : ℤ)),
      ‖criticalWholePreinverseNativeCLM α β ha hia hb hib p T‖ ≤ C*‖T‖ := by
  let U := criticalWholePreinverseNativeCLM α β ha hia hb hib p
  refine ⟨‖U‖+1,by positivity,fun T => ?_⟩
  exact (U.le_opNorm T).trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))

/-- The second whole equation restores every original FOURIER tail hole,
while retaining all homogeneous contributions of the first inverse. -/
theorem criticalWholePreinverse_fourier_difference_tail {k : ℕ} (hk : 1 ≤ k)
    (α β : Fin k → ℝ) (ha : Function.Injective α) (hia : ∀ i, 0 < α i ∧ α i < 1/2)
    (hb : Function.Injective β) (hib : ∀ i, 0 < β i ∧ β i < 1/2)
    (η : ℕ+ → ℝ) (hiη : ∀ j, 0 < η j ∧ η j < 1/2)
    (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier (criticalPhaseTailCarrier η hiη k 0) (𝓕 T)) :
    AtomicOnCarrier (criticalPhaseTailCarrier η hiη k k)
      (𝓕 (criticalHeadDifferenceDistributionCLM β (criticalWholePreinverseCLM α β ha hia hb hib T))) := by
  rw [criticalWholePreinverse_difference hk,fourier_criticalMultiplierInverse]
  exact criticalGreenDistribution_restores_tail α ha hia η hiη _ hT

/-- The first whole equation restores every original PHYSICAL tail hole. -/
theorem criticalWholePreinverse_multiplier_tail {k : ℕ} (hk : 1 ≤ k)
    (α β : Fin k → ℝ) (ha : Function.Injective α) (hia : ∀ i, 0 < α i ∧ α i < 1/2)
    (hb : Function.Injective β) (hib : ∀ i, 0 < β i ∧ β i < 1/2)
    (η : ℕ+ → ℝ) (hiη : ∀ j, 0 < η j ∧ η j < 1/2)
    (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier (criticalPhaseTailCarrier η hiη k 0) T) :
    AtomicOnCarrier (criticalPhaseTailCarrier η hiη k k)
      (criticalHeadMultiplierDistributionCLM α (criticalWholePreinverseCLM α β ha hia hb hib T)) := by
  rw [criticalWholePreinverse_multiplier hk]
  exact criticalGreenDistribution_restores_tail β hb hib η hiη _ hT

end
end MeyerGeneralProblem.Adaptive
