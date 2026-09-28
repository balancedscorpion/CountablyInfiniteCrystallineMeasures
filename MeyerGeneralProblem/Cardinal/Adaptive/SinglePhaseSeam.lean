module

public import MeyerGeneralProblem.Cardinal.Adaptive.SinglePhaseLocalization
public import MeyerGeneralProblem.Cardinal.Adaptive.ProfileConvolutionVanishing
public import MeyerGeneralProblem.Cardinal.Adaptive.DistributionLocality

@[expose] public section

/-! The complete single-factor source, retaining possible distributions on the seam. -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open Classical Set Filter
open scoped Topology FourierTransform ContDiff

/-- The actual single-block flat multiplier at its signed physical scale. -/
def singlePhaseMultiplier (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) (t : ℝ) (x : ℝ) : ℂ :=
  complexPhaseAnnihilator P R hP hR (t*x)

/-- Every actual single-block multiplier acts on the whole Schwartz space. -/
theorem singlePhaseMultiplier_hasTemperateGrowth (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) (t : ℝ) :
    (singlePhaseMultiplier P R hP hR t).HasTemperateGrowth :=
  (smooth_periodic_hasTemperateGrowth _ (complexPhaseAnnihilator_smooth P R hP hR)
    (complexPhaseAnnihilator_periodic P R hP hR)).comp
    ((Function.HasTemperateGrowth.const t).mul Function.HasTemperateGrowth.id')

/-- All actual scaled frequency moments are summable, at every original native order. -/
theorem singlePhase_frequency_moment (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) (t : ℝ) (q : ℕ) :
    Summable (fun l : ℤ => (1+|t*(l:ℝ)|)^(2*q)*‖phaseCoefficient P R hP hR l‖) := by
  apply Summable.of_nonneg_of_le (fun l => by positivity) _
    ((phaseCoefficient_all_moments P R hP hR (2*q)).mul_left ((1+|t|)^(2*q)))
  intro l
  have h : 1+|t*(l:ℝ)| ≤ (1+|t|)*(1+|(l:ℝ)|) := by
    rw [abs_mul]
    nlinarith [abs_nonneg t,abs_nonneg (l:ℝ)]
  calc
    _ ≤ ((1+|t|)*(1+|(l:ℝ)|))^(2*q)*‖phaseCoefficient P R hP hR l‖ := by gcongr
    _ = _ := by rw [mul_pow]; ring

/-- The complete Fourier expansion has the exact signed physical frequency. -/
theorem singlePhaseMultiplier_expansion (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) (t x : ℝ) :
    singlePhaseMultiplier P R hP hR t x =
      ∑' l : ℤ, phaseCoefficient P R hP hR l * combModulationCharacter (t*(l:ℝ)) x := by
  rw [singlePhaseMultiplier,periodicCoefficient_expansion _
    (complexPhaseAnnihilator_smooth P R hP hR) (complexPhaseAnnihilator_periodic P R hP hR)]
  apply tsum_congr
  intro l
  congr 1
  rw [fourier_coe_apply,combModulationCharacter_eq_exp]
  congr 1
  push_cast
  ring

/-- Native realization of the complete spectral single-factor source, with no order loss. -/
def singlePhaseSpectralNative (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) (t : ℝ) (q : ℕ)
    (T : HermiteScale (-(q:ℤ))) : HermiteScale (-(q:ℤ)) :=
  (∑' l : ℤ, phaseCoefficient P R hP hR l • nativeTranslation q (t*(l:ℝ)))
    (hermiteFourier (-(q:ℤ)) T)

/-- Every translation in the single-factor full series is retained as a whole distribution. -/
theorem singlePhase_spectral_hasSum (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) (t : ℝ) (q : ℕ)
    (T : HermiteScale (-(q:ℤ))) :
    HasSum (fun l : ℤ => phaseCoefficient P R hP hR l •
      combDistributionTranslation (t*(l:ℝ)) (𝓕 (hermiteScaleDistribution q T)))
      (𝓕 (TemperedDistribution.smulLeftCLM ℂ (singlePhaseMultiplier P R hP hR t)
        (hermiteScaleDistribution q T))) :=
  hasSum_fourier_multiplier_translations q _ _ (singlePhase_frequency_moment P R hP hR t q)
    _ (singlePhaseMultiplier_hasTemperateGrowth P R hP hR t)
    (singlePhaseMultiplier_expansion P R hP hR t) T

/-- The full multiplied source remains at the original native order, including every seam term. -/
theorem singlePhaseSpectralNative_realizes (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) (t : ℝ) (q : ℕ)
    (T : HermiteScale (-(q:ℤ))) :
    hermiteScaleDistribution q (singlePhaseSpectralNative P R hP hR t q T) =
      𝓕 (TemperedDistribution.smulLeftCLM ℂ (singlePhaseMultiplier P R hP hR t)
        (hermiteScaleDistribution q T)) := by
  rw [singlePhaseSpectralNative,native_translation_series_realizes q _ _
    (singlePhase_frequency_moment P R hP hR t q),hermiteFourier_represents_distributionalFourier]
  exact (singlePhase_spectral_hasSum P R hP hR t q T).tsum_eq


/-- The full single-factor pairing is the complete scalar translation sum. -/
theorem singlePhase_spectral_pairing (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) (t : ℝ) (q : ℕ)
    (T : HermiteScale (-(q:ℤ))) (f : SchwartzMap ℝ ℂ) :
    hermiteScaleDistribution q (singlePhaseSpectralNative P R hP hR t q T) f =
      ∑' l : ℤ, phaseCoefficient P R hP hR l *
        combDistributionTranslation (t*(l:ℝ)) (𝓕 (hermiteScaleDistribution q T)) f := by
  rw [singlePhaseSpectralNative_realizes]
  have h := (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ f).hasSum
    (singlePhase_spectral_hasSum P R hP hR t q T)
  simpa only [PointwiseConvergenceCLM.evalCLM_apply,_root_.smul_apply,smul_eq_mul] using! h.tsum_eq.symm

/-- The complete actual one-sector source after its actual annihilator, still in H_-(6p). -/
def actualSinglePhaseSpectralNative (σ : ℝ) (hσ : 0 < σ) (p : ℕ)
    (R : ℕ+ → ℕ) (hR : ∀ i, 1 ≤ R i) (s : ℕ+ → ℝ) (b : Label)
    (T : HermiteScale (-(p:ℤ))) : HermiteScale (-((6*p:ℕ):ℤ)) :=
  singlePhaseSpectralNative b.1 (R b.1) b.1.pos (hR b.1) (labelScale s b) (6*p)
    (nativeSourcePiece σ hσ p R s {b} T)

/-- Whole closure support follows from the complete translation series and
actual atomicity, without asserting atomicity at an accumulation seam. -/
theorem actualSinglePhase_test_zero_on_closure (σ : ℝ) (hσ : 0 < σ) (p : ℕ)
    (R : ℕ+ → ℕ) (hR : ∀ i, 1 ≤ R i) (s : ℕ+ → ℝ)
    (hsep : ∀ b d : Label, b ≠ d → ∀ x ∈ sectorSet R s b,
      ∀ y ∈ sectorSet R s d, σ/(1+|x|+|y|)^6 ≤ |x-y|)
    (B : LocallyFiniteCarrier) (hB : B.carrier ⊆ carrierSet R s)
    (T : HermiteScale (-(p:ℤ))) (hFT : AtomicOnCarrier B (𝓕 (hermiteScaleDistribution p T)))
    (b : Label) (f : SchwartzMap ℝ ℂ)
    (hf : ∀ y ∈ scaledPeriodicPhaseSet b.1 (R b.1) (labelScale s b), f y = 0) :
    hermiteScaleDistribution (6*p) (actualSinglePhaseSpectralNative σ hσ p R hR s b T) f = 0 := by
  rw [actualSinglePhaseSpectralNative,singlePhase_spectral_pairing]
  apply HasSum.tsum_eq
  apply hasSum_zero.congr_fun
  intro l
  suffices he : combDistributionTranslation (labelScale s b*(l:ℝ))
      (𝓕 (hermiteScaleDistribution (6*p) (nativeSourcePiece σ hσ p R s {b} T))) f = 0 by
    rw [he,mul_zero]
  rw [combDistributionTranslation_apply]
  apply nativeSourcePiece_spectral_atomic σ hσ p R s hsep B hB T hFT {b}
  intro x hx
  have hxsec : x ∈ sectorSet R s b := by
    obtain ⟨d,hd⟩ := mem_iUnion.mp hx.2
    obtain ⟨hdb,hxd⟩ := mem_iUnion.mp hd
    have he : d=b := mem_singleton_iff.mp hdb
    simpa only [he] using hxd
  rw [combSchwartzTranslation_apply]
  apply hf
  convert scaledPeriodicPhaseSet_add b.1 (R b.1) (labelScale s b) l
    (sectorSet_subset_scaled_periodic R s b hxsec) using 1; ring

/-- A vanishing complete phase convolution kills every test isolating that
phase in the full periodic closure. All omitted translations are present. -/
theorem actualSinglePhase_test_zero_at_phase (σ : ℝ) (hσ : 0 < σ) (p : ℕ)
    (R : ℕ+ → ℕ) (hR : ∀ i, 1 ≤ R i) (s : ℕ+ → ℝ)
    (hsep : ∀ b d : Label, b ≠ d → ∀ x ∈ sectorSet R s b,
      ∀ y ∈ sectorSet R s d, σ/(1+|x|+|y|)^6 ≤ |x-y|)
    (B : LocallyFiniteCarrier) (hB : B.carrier ⊆ carrierSet R s)
    (T : HermiteScale (-(p:ℤ))) (hFT : AtomicOnCarrier B (𝓕 (hermiteScaleDistribution p T)))
    (b : Label) (β γ : ℝ) (hγ : 0 < γ)
    (hisol : ∀ m : ℤ, ∀ y ∈ sectorSet R s b,
      y ≠ labelScale s b*((m:ℝ)+β) → 4*γ ≤ |y-labelScale s b*((m:ℝ)+β)|)
    (n : ℤ) (hzero : (∑' l : ℤ, phaseCoefficient b.1 (R b.1) b.1.pos (hR b.1) l *
      isolatedSourceCoefficient σ hσ p R s b β γ hγ T (n-l)) = 0)
    (f : SchwartzMap ℝ ℂ)
    (hf : ∀ y ∈ scaledPeriodicPhaseSet b.1 (R b.1) (labelScale s b),
      y ≠ labelScale s b*((n:ℝ)+β) → f y = 0) :
    hermiteScaleDistribution (6*p) (actualSinglePhaseSpectralNative σ hσ p R hR s b T) f = 0 := by
  rw [actualSinglePhaseSpectralNative,singlePhase_spectral_pairing]
  simp_rw [isolated_phase_translation_pairing σ hσ p R s hsep B hB T hFT b β γ hγ hisol n _ f hf]
  calc
    _ = f (labelScale s b*((n:ℝ)+β)) *
        ∑' l : ℤ, phaseCoefficient b.1 (R b.1) b.1.pos (hR b.1) l *
          isolatedSourceCoefficient σ hσ p R s b β γ hγ T (n-l) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro l
      ring
    _ = 0 := by rw [hzero,mul_zero]


/-- Scaling the complete periodic phase closure preserves closedness. -/
theorem scaledPeriodicPhaseSet_isClosed (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R)
    (t : ℝ) (ht : t ≠ 0) : IsClosed (scaledPeriodicPhaseSet P R t) :=
  (Homeomorph.mulLeft₀ t ht).isClosedMap _ (periodicPhaseSet_isClosed hP hR)

/-- Every scaled phase away from the actual half-integer seam is isolated in the whole closure. -/
theorem scaledPeriodicPhaseSet_point_isolated (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R)
    (t : ℝ) (ht : t ≠ 0) (x : ℝ) (hx : x ∈ scaledPeriodicPhaseSet P R t)
    (hseam : ∀ n : ℤ, x ≠ t*((n:ℝ)+1/2)) :
    ∃ O : Set ℝ, IsOpen O ∧ O ∩ scaledPeriodicPhaseSet P R t = {x} := by
  obtain ⟨z,hz,rfl⟩ := hx
  obtain ⟨V,hV,hVe⟩ := periodicPhaseSet_point_isolated hP hR hz
    (fun n he => hseam n (congrArg (fun z : ℝ => t*z) he))
  refine ⟨(fun y : ℝ => t⁻¹*y) ⁻¹' V,hV.preimage (continuous_const.mul continuous_id),?_⟩
  ext y
  constructor
  · rintro ⟨hyV,w,hw,rfl⟩
    have hwV : w ∈ V := by simpa only [mem_preimage,← mul_assoc,inv_mul_cancel₀ ht,one_mul] using hyV
    have he : w=z := mem_singleton_iff.mp (hVe ▸ ⟨hwV,hw⟩)
    exact congrArg (fun z : ℝ => t*z) he
  · rintro rfl
    refine ⟨?_,z,hz,rfl⟩
    have hzV := (show z ∈ V ∩ periodicPhaseSet P R from hVe.symm ▸ mem_singleton z).1
    simpa only [mem_preimage,← mul_assoc,inv_mul_cancel₀ ht,one_mul] using hzV

/-- The entire actual single-factor spectral source is supported on the seam.
All possible derivatives at seam points remain in the native distribution. -/
theorem actualSinglePhase_supportedOn_seam (ψ : SchwartzMap ℝ ℂ)
    (hψone : ψ 0 = 1) (hψzero : ∀ x, 2 ≤ |x| → ψ x = 0) (σ : ℝ) (hσ : 0 < σ) (p : ℕ)
    (s : ℕ+ → ℝ) (hs : ActualGoodScale ψ s)
    (hsep : ∀ b d : Label, b ≠ d →
      ∀ x ∈ sectorSet (actualPositiveGaps ψ) s b,
      ∀ y ∈ sectorSet (actualPositiveGaps ψ) s d,
        σ/(1+|x|+|y|)^6 ≤ |x-y|)
    (A B : LocallyFiniteCarrier)
    (hA : A.carrier ⊆ carrierSet (actualPositiveGaps ψ) s)
    (hB : B.carrier ⊆ carrierSet (actualPositiveGaps ψ) s)
    (T : HermiteScale (-(p:ℤ))) (hT : AtomicOnCarrier A (hermiteScaleDistribution p T))
    (hFT : AtomicOnCarrier B (𝓕 (hermiteScaleDistribution p T))) (b : Label) :
    DistributionSupportedOn (Set.range (fun n : ℤ => labelScale s b*((n:ℝ)+1/2)))
      (hermiteScaleDistribution (6*p)
        (actualSinglePhaseSpectralNative σ hσ p (actualPositiveGaps ψ)
          (actualPositiveGaps_pos ψ) s b T)) := by
  let R := actualPositiveGaps ψ
  have ht : labelScale s b ≠ 0 := (labelScale_pos s hs.1.1 b).ne'
  apply supportedOn_of_local_vanishing
  intro x hx
  have hseam : ∀ n : ℤ, x ≠ labelScale s b*((n:ℝ)+1/2) :=
    fun n he => hx ⟨n,he.symm⟩
  by_cases hxP : x ∈ scaledPeriodicPhaseSet b.1 (R b.1) (labelScale s b)
  · obtain ⟨O,hO,hOe⟩ := scaledPeriodicPhaseSet_point_isolated b.1 (R b.1) b.1.pos
      (actualPositiveGaps_pos ψ b.1) _ ht x hxP hseam
    have hxO : x ∈ O := (show x ∈ O ∩ scaledPeriodicPhaseSet b.1 (R b.1) (labelScale s b)
      from hOe.symm ▸ mem_singleton x).1
    obtain ⟨z,⟨n,β,hβ,rfl⟩,hxz⟩ := hxP
    have hβphase : β ∈ phaseSet b.1 (R b.1) := by
      rcases hβ with hβ | rfl
      · exact hβ
      · exact False.elim (hseam n hxz.symm)
    obtain ⟨γ,hγ,hisol,hzero⟩ := exists_profile_phase_convolution_zero ψ hψone hψzero σ hσ p s hs hsep b β hβphase
    refine ⟨O,hO,hxO,fun f hf hfO => ?_⟩
    apply actualSinglePhase_test_zero_at_phase σ hσ p R (actualPositiveGaps_pos ψ)
      s hsep B hB T hFT b β γ hγ hisol n (hzero A B hA hB T hT hFT n) f
    intro y hy hne
    by_contra hfy
    have hyO := hfO (subset_tsupport f hfy)
    have hyx : y=x := mem_singleton_iff.mp (hOe ▸ ⟨hyO,hy⟩)
    exact hne (hyx.trans hxz.symm)
  · refine ⟨(scaledPeriodicPhaseSet b.1 (R b.1) (labelScale s b))ᶜ,
      (scaledPeriodicPhaseSet_isClosed _ _ b.1.pos (actualPositiveGaps_pos ψ b.1) _ ht).isOpen_compl,
      hxP,fun f hf hfO => ?_⟩
    apply actualSinglePhase_test_zero_on_closure σ hσ p R (actualPositiveGaps_pos ψ)
      s hsep B hB T hFT b f
    intro y hy
    by_contra hfy
    exact hfO (subset_tsupport f hfy) hy

end
end MeyerGeneralProblem.Adaptive
