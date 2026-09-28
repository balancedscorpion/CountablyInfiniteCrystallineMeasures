module

public import MeyerGeneralProblem.Cardinal.Adaptive.CriticalPoissonRepair

@[expose] public section

/-! # Bounded whole finite-head repair with constants independent of the tails -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open scoped FourierTransform BigOperators

/-- Every whole Poisson source has a representation in each eligible original layer. -/
theorem wholePoissonSource_native (a b : ℝ) (p : ℕ) (hp : 1 ≤ p) :
    ∃ u : HermiteScale (-(p : ℤ)), hermiteScaleDistribution p u = wholePoissonSource a b :=
  originalNativeDistributionSpace_mono hp (wholePoissonSource_native_one a b)

/-- A fixed original native realization of the actual whole Poisson source. -/
def wholePoissonNative (a b : ℝ) (p : ℕ) (hp : 1 ≤ p) : HermiteScale (-(p : ℤ)) :=
  (wholePoissonSource_native a b p hp).choose

/-- The chosen native vector realizes the entire Poisson source, not just finite samples. -/
theorem wholePoissonNative_realizes (a b : ℝ) (p : ℕ) (hp : 1 ≤ p) :
    hermiteScaleDistribution p (wholePoissonNative a b p hp) = wholePoissonSource a b :=
  (wholePoissonSource_native a b p hp).choose_spec

def criticalPoissonNativeSynthesisLM {k : ℕ} (α β : Fin k → ℝ) (p : ℕ) (hp : 1 ≤ p) :
    (Fin k → Fin k → SignedMassBlock) →ₗ[ℂ] HermiteScale (-(p : ℤ)) where
  toFun c := ∑ I,∑ u,∑ J,∑ v,c I J u v •
    wholePoissonNative (criticalSignedPhase u (α I)) (criticalSignedPhase v (β J)) p hp
  map_add' c d := by simp only [Pi.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' a c := by simp [Finset.smul_sum,smul_smul]

/-- Actual finite-dimensional synthesis into the original native norm. -/
def criticalPoissonNativeSynthesis {k : ℕ} (α β : Fin k → ℝ) (p : ℕ) (hp : 1 ≤ p) :
    (Fin k → Fin k → SignedMassBlock) →L[ℂ] HermiteScale (-(p : ℤ)) :=
  (criticalPoissonNativeSynthesisLM α β p hp).toContinuousLinearMap

/-- Equality of the whole synthesized distributions follows from each actual basis realization. -/
theorem criticalPoissonNativeSynthesis_realizes {k : ℕ} (α β : Fin k → ℝ)
    (p : ℕ) (hp : 1 ≤ p) (c : Fin k → Fin k → SignedMassBlock) :
    hermiteScaleDistribution p (criticalPoissonNativeSynthesis α β p hp c) = criticalPoissonSynthesis α β c := by
  change hermiteScaleDistributionCLM p (∑ I,∑ u,∑ J,∑ v,c I J u v •wholePoissonNative _ _ p hp) = _
  simp only [map_sum,map_smul,hermiteScaleDistributionCLM_apply,wholePoissonNative_realizes]
  rfl

/-- Actual evaluation at a head point is continuous for the whole tempered distribution topology. -/
def criticalHeadCoefficientCLM {k : ℕ} (α : Fin k → ℝ) (S : LocallyFiniteCarrier)
    (hS : criticalHeadCosetSet α ⊆ S.carrier) (i : Fin k) (u : Bool) (n : ℤ) :
    TemperedDistribution ℝ ℂ →L[ℂ] ℂ :=
  PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ
    (S.isolationSchwartz ⟨criticalHeadPoint α i u n,hS (criticalHeadPoint_mem α i u n)⟩)

/-- Both actual finite lists define a continuous operator on whole distributions. -/
def criticalTriangularObservationCLM {k : ℕ} (α β : Fin k → ℝ)
    (S R : LocallyFiniteCarrier) (hS : criticalHeadCosetSet α ⊆ S.carrier)
    (hR : criticalHeadCosetSet β ⊆ R.carrier) :
    TemperedDistribution ℝ ℂ →L[ℂ] TriangularHoleCoordinates k :=
  ContinuousLinearMap.pi (Sum.elim
    (fun h => criticalHeadCoefficientCLM α S hS h.1 h.2.1 (triangularHoleCell h))
    (fun h => (criticalHeadCoefficientCLM β R hR h.1 h.2.1 (triangularHoleCell h)).comp
      (FourierTransform.fourierCLM ℂ (TemperedDistribution ℝ ℂ))))

/-- Continuous and algebraic observation interfaces agree on every whole input. -/
theorem criticalTriangularObservationCLM_apply {k : ℕ} (α β : Fin k → ℝ)
    (S R : LocallyFiniteCarrier) (hS : criticalHeadCosetSet α ⊆ S.carrier)
    (hR : criticalHeadCosetSet β ⊆ R.carrier) (T : TemperedDistribution ℝ ℂ) :
    criticalTriangularObservationCLM α β S R hS hR T = criticalTriangularObservation α β S R hS hR T := by
  ext h
  cases h <;> rfl

/-- Canonical inclusion of the full head set in its actual carrier. -/
theorem criticalHeadCosetCarrier_contains {k : ℕ} (α : Fin k → ℝ) :
    criticalHeadCosetSet α ⊆ (criticalHeadCosetCarrier α).carrier := fun _ h => h

/-- The native finite repair operator is constructed entirely from the two
finite heads and the original order. No infinite-tail carrier is an input. -/
def criticalPoissonNativeCorrection {k : ℕ} (α β : Fin k → ℝ)
    (ha : Function.Injective α) (hia : ∀ i, 0 < α i ∧ α i < 1/2)
    (hb : Function.Injective β) (hib : ∀ i, 0 < β i ∧ β i < 1/2) (p : ℕ) (hp : 1 ≤ p) :
    HermiteScale (-(p : ℤ)) →L[ℂ] HermiteScale (-(p : ℤ)) :=
  (criticalPoissonNativeSynthesis α β p hp).comp
    (((criticalTriangularSynthesisEquiv α β ha hia hb hib
      (criticalHeadCosetCarrier α) (criticalHeadCosetCarrier β) (criticalHeadCosetCarrier_contains α) (criticalHeadCosetCarrier_contains β)).symm.toLinearMap.toContinuousLinearMap).comp
      ((criticalTriangularObservationCLM α β (criticalHeadCosetCarrier α) (criticalHeadCosetCarrier β)
        (criticalHeadCosetCarrier_contains α) (criticalHeadCosetCarrier_contains β)).comp (hermiteScaleDistributionCLM p)))

/-- Native repair is exactly the actual whole Poisson correction at all tests. -/
theorem criticalPoissonNativeCorrection_realizes {k : ℕ} (α β : Fin k → ℝ)
    (ha : Function.Injective α) (hia : ∀ i, 0 < α i ∧ α i < 1/2)
    (hb : Function.Injective β) (hib : ∀ i, 0 < β i ∧ β i < 1/2) (p : ℕ) (hp : 1 ≤ p)
    (T : HermiteScale (-(p : ℤ))) :
    hermiteScaleDistribution p (criticalPoissonNativeCorrection α β ha hia hb hib p hp T) =
      criticalPoissonCorrection α β ha hia hb hib (criticalHeadCosetCarrier α) (criticalHeadCosetCarrier β)
        (criticalHeadCosetCarrier_contains α) (criticalHeadCosetCarrier_contains β) (hermiteScaleDistribution p T) := by
  simp only [criticalPoissonNativeCorrection,ContinuousLinearMap.comp_apply,
    criticalPoissonNativeSynthesis_realizes,hermiteScaleDistributionCLM_apply]
  rw [criticalTriangularObservationCLM_apply]
  rfl

/-- Complete repaired native operator with exactly two original orders of loss. -/
def criticalRepairedNativeCLM {k : ℕ} (α β : Fin k → ℝ)
    (ha : Function.Injective α) (hia : ∀ i, 0 < α i ∧ α i < 1/2)
    (hb : Function.Injective β) (hib : ∀ i, 0 < β i ∧ β i < 1/2) (p : ℕ) :
    HermiteScale (-(p : ℤ)) →L[ℂ] HermiteScale (-((p+2 : ℕ) : ℤ)) :=
  ((ContinuousLinearMap.id ℂ _)-criticalPoissonNativeCorrection α β ha hia hb hib (p+2) (by omega)).comp
    (criticalWholePreinverseNativeCLM α β ha hia hb hib p)

/-- Its finite operator bound is fixed before any tails or input are chosen. -/
theorem criticalRepairedNativeCLM_bound {k : ℕ} (α β : Fin k → ℝ)
    (ha : Function.Injective α) (hia : ∀ i, 0 < α i ∧ α i < 1/2)
    (hb : Function.Injective β) (hib : ∀ i, 0 < β i ∧ β i < 1/2) (p : ℕ) :
    ∃ C > 0, ∀ T : HermiteScale (-(p : ℤ)), ‖criticalRepairedNativeCLM α β ha hia hb hib p T‖ ≤ C*‖T‖ := by
  let U := criticalRepairedNativeCLM α β ha hia hb hib p
  refine ⟨‖U‖+1,by positivity,fun T => ?_⟩
  exact (U.le_opNorm T).trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))


/-- The repaired whole operator subtracts the uniquely determined actual
Poisson correction, using only the two finite heads. -/
def criticalRepairedDistributionLM {k : ℕ} (α β : Fin k → ℝ)
    (ha : Function.Injective α) (hia : ∀ i, 0 < α i ∧ α i < 1/2)
    (hb : Function.Injective β) (hib : ∀ i, 0 < β i ∧ β i < 1/2) :
    TemperedDistribution ℝ ℂ →ₗ[ℂ] TemperedDistribution ℝ ℂ :=
  (LinearMap.id-criticalPoissonCorrection α β ha hia hb hib
    (criticalHeadCosetCarrier α) (criticalHeadCosetCarrier β)
    (criticalHeadCosetCarrier_contains α) (criticalHeadCosetCarrier_contains β)).comp
      (criticalWholePreinverseCLM α β ha hia hb hib).toLinearMap

/-- The native repaired operator realizes the same whole distribution on every test. -/
theorem criticalRepairedNativeCLM_realizes {k : ℕ} (α β : Fin k → ℝ)
    (ha : Function.Injective α) (hia : ∀ i, 0 < α i ∧ α i < 1/2)
    (hb : Function.Injective β) (hib : ∀ i, 0 < β i ∧ β i < 1/2) (p : ℕ)
    (T : HermiteScale (-(p : ℤ))) :
    hermiteScaleDistribution (p+2) (criticalRepairedNativeCLM α β ha hia hb hib p T) =
      criticalRepairedDistributionLM α β ha hia hb hib (hermiteScaleDistribution p T) := by
  change hermiteScaleDistributionCLM (p+2)
    (criticalWholePreinverseNativeCLM α β ha hia hb hib p T-
      criticalPoissonNativeCorrection α β ha hia hb hib (p+2) _
        (criticalWholePreinverseNativeCLM α β ha hia hb hib p T)) = _
  rw [map_sub]
  simp only [hermiteScaleDistributionCLM_apply,criticalPoissonNativeCorrection_realizes,
    criticalWholePreinverseNativeCLM_realizes]
  rfl

/-- The whole correction is killed by the actual difference operator, so the
repaired operator remains a right inverse of the actual product. -/
theorem criticalRepairedDistribution_rightInverse {k : ℕ} (hk : 1 ≤ k) (α β : Fin k → ℝ)
    (ha : Function.Injective α) (hia : ∀ i, 0 < α i ∧ α i < 1/2)
    (hb : Function.Injective β) (hib : ∀ i, 0 < β i ∧ β i < 1/2)
    (T : TemperedDistribution ℝ ℂ) :
    criticalHeadMultiplierDistributionCLM α (criticalHeadDifferenceDistributionCLM β
      (criticalRepairedDistributionLM α β ha hia hb hib T)) = T := by
  change criticalHeadMultiplierDistributionCLM α (criticalHeadDifferenceDistributionCLM β
    (criticalWholePreinverseCLM α β ha hia hb hib T-criticalPoissonSynthesis α β _))=T
  rw [map_sub,criticalPoissonSynthesis_difference_zero,sub_zero]
  exact criticalWholePreinverse_rightInverse hk α β ha hia hb hib T

/-- The constructed inverse is injective on whole distributions. This uses
its proved right-inverse identity and does not assume uniqueness of preimages. -/
theorem criticalRepairedDistribution_injective {k : ℕ} (hk : 1 ≤ k) (α β : Fin k → ℝ)
    (ha : Function.Injective α) (hia : ∀ i, 0 < α i ∧ α i < 1/2)
    (hb : Function.Injective β) (hib : ∀ i, 0 < β i ∧ β i < 1/2) :
    Function.Injective (criticalRepairedDistributionLM α β ha hia hb hib) := by
  intro T U h
  have hh := congrArg (fun V => criticalHeadMultiplierDistributionCLM α
    (criticalHeadDifferenceDistributionCLM β V)) h
  simpa only [criticalRepairedDistribution_rightInverse hk] using hh

end
end MeyerGeneralProblem.Adaptive
