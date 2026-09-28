module

public import MeyerGeneralProblem.Cardinal.Adaptive.SinglePhaseSeam
public import MeyerGeneralProblem.Cardinal.Adaptive.InverseLatticeDifference
public import MeyerGeneralProblem.Cardinal.Adaptive.LocalMultiplierCancellation
public import MeyerGeneralProblem.Cardinal.Adaptive.AntiperiodicLift

@[expose] public section

/-! Actual local generalized antiperiodic difference and bounded-lift bridge. -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open Classical Set
open scoped Topology FourierTransform ContDiff

/-- The actual single-factor multiplier is smooth everywhere, including its flat zero set. -/
theorem singlePhaseMultiplier_smooth (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) (t : ℝ) :
    ContDiff ℝ ∞ (singlePhaseMultiplier P R hP hR t) :=
  (complexPhaseAnnihilator_smooth P R hP hR).comp (contDiff_const.mul contDiff_id)

/-- The physical multiplier period is exactly the reciprocal signed scale. -/
theorem singlePhaseMultiplier_periodic (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R)
    (t : ℝ) (ht : t ≠ 0) : Function.Periodic (singlePhaseMultiplier P R hP hR t) t⁻¹ := by
  intro x
  change complexPhaseAnnihilator P R hP hR (t*(x+t⁻¹)) =
    complexPhaseAnnihilator P R hP hR (t*x)
  rw [show t*(x+t⁻¹)=t*x+1 by rw [mul_add,mul_inv_cancel₀ ht]]
  exact complexPhaseAnnihilator_periodic P R hP hR (t*x)

/-- The actual flat multiplier is nonzero precisely where local cancellation is needed. -/
theorem singlePhaseMultiplier_ne_zero_off_physical (R : ℕ+ → ℕ) (hR : ∀ i, 1 ≤ R i)
    (s : ℕ+ → ℝ) (hs : ∀ i, s i ∈ Set.Icc 1 2) (b : Label) (x : ℝ)
    (hx : x ∉ physicalPeriodicSet R s b) :
    singlePhaseMultiplier b.1 (R b.1) b.1.pos (hR b.1) (labelScale s b) x ≠ 0 := by
  intro hz
  have hreal : phaseAnnihilator b.1 (R b.1) b.1.pos (hR b.1) (labelScale s b*x)=0 := by
    change (phaseAnnihilator b.1 (R b.1) b.1.pos (hR b.1) (labelScale s b*x) : ℂ) = 0 at hz
    exact Complex.ofReal_eq_zero.mp hz
  have hmem := ((phaseAnnihilator_spec b.1 (R b.1) b.1.pos (hR b.1)).2.2.2.1 _).mp hreal
  apply hx
  refine ⟨labelScale s b*x,hmem,?_⟩
  change (labelScale s b)⁻¹*(labelScale s b*x)=x
  rw [← mul_assoc,inv_mul_cancel₀ (labelScale_pos s hs b).ne',one_mul]

/-- The actual whole source piece has the source's local antidifference law
of degree exactly12p+1 off its physical periodic closure. The flat multiplier
is cancelled only on compact tests supported where it is nonzero. -/
theorem actualSourcePiece_local_antidifference (ψ : SchwartzMap ℝ ℂ)
    (hψone : ψ 0 = 1) (hψzero : ∀ x, 2 ≤ |x| → ψ x = 0)
    (σ : ℝ) (hσ : 0 < σ) (p : ℕ) (s : ℕ+ → ℝ) (hs : ActualGoodScale ψ s)
    (hsep : ∀ b d : Label, b ≠ d → ∀ x ∈ sectorSet (actualPositiveGaps ψ) s b,
      ∀ y ∈ sectorSet (actualPositiveGaps ψ) s d, σ/(1+|x|+|y|)^6 ≤ |x-y|)
    (A B : LocallyFiniteCarrier)
    (hA : A.carrier ⊆ carrierSet (actualPositiveGaps ψ) s)
    (hB : B.carrier ⊆ carrierSet (actualPositiveGaps ψ) s)
    (T : HermiteScale (-(p:ℤ))) (hT : AtomicOnCarrier A (hermiteScaleDistribution p T))
    (hFT : AtomicOnCarrier B (𝓕 (hermiteScaleDistribution p T))) (b : Label) :
    DistributionVanishesOn (physicalPeriodicSet (actualPositiveGaps ψ) s b)ᶜ
      ((distributionAntidifference (labelScale s b)⁻¹ : TemperedDistribution ℝ ℂ → TemperedDistribution ℝ ℂ)^[12*p+1]
        (hermiteScaleDistribution (6*p) (nativeSourcePiece σ hσ p (actualPositiveGaps ψ) s {b} T))) := by
  let R := actualPositiveGaps ψ
  let χ := singlePhaseMultiplier b.1 (R b.1) b.1.pos (actualPositiveGaps_pos ψ b.1) (labelScale s b)
  have hg := singlePhaseMultiplier_hasTemperateGrowth b.1 (R b.1) b.1.pos
    (actualPositiveGaps_pos ψ b.1) (labelScale s b)
  have hχ := singlePhaseMultiplier_smooth b.1 (R b.1) b.1.pos
    (actualPositiveGaps_pos ψ b.1) (labelScale s b)
  have hper := singlePhaseMultiplier_periodic b.1 (R b.1) b.1.pos
    (actualPositiveGaps_pos ψ b.1) (labelScale s b) (labelScale_pos s hs.1.1 b).ne'
  have hsupport := actualSinglePhase_supportedOn_seam ψ hψone hψzero σ hσ p s hs hsep A B hA hB T hT hFT b
  have he := scaledHalfInteger_support_fourierInv_finite_difference (labelScale s b)
    (labelScale_pos s hs.1.1 b) (6*p) _ hsupport
  rw [actualSinglePhaseSpectralNative,singlePhaseSpectralNative_realizes,
    FourierTransform.fourierInv_fourier_eq] at he
  have horder : 2*(6*p)+1=12*p+1 := by omega
  rw [horder] at he
  change (distributionAntidifference (labelScale s b)⁻¹ : TemperedDistribution ℝ ℂ → TemperedDistribution ℝ ℂ)^[12*p+1]
      (TemperedDistribution.smulLeftCLM ℂ χ
        (hermiteScaleDistribution (6*p) (nativeSourcePiece σ hσ p R s {b} T))) = 0 at he
  rw [periodicMultiplier_antidifference_iter χ hg (labelScale s b)⁻¹ hper] at he
  exact distributionVanishesOn_of_multiplier_zero _ χ hχ hg
    (fun x hx => singlePhaseMultiplier_ne_zero_off_physical R (actualPositiveGaps_pos ψ) s hs.1.1 b x hx)
    _ he

end
end MeyerGeneralProblem.Adaptive
