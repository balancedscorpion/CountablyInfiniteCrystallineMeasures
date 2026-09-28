module

public import MeyerGeneralProblem.Cardinal.Adaptive.SmoothSelectors
public import MeyerGeneralProblem.Cardinal.Adaptive.NativeDiscreteJets

@[expose] public section

/-! Exact finite whole-source splitting by actual spectral sectors. -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open MeasureTheory Set Filter Classical
open scoped Topology ContDiff FourierTransform

/-- The actual inverse Fourier realization of the inverse native isometry. -/
theorem hermiteFourier_symm_realizes (p : ℕ) (T : HermiteScale (-(p:ℤ))) :
    hermiteScaleDistribution p ((hermiteFourier (-(p:ℤ))).symm T) =
      𝓕⁻ (hermiteScaleDistribution p T) := by
  have h := hermiteFourier_represents_distributionalFourier p
    ((hermiteFourier (-(p:ℤ))).symm T)
  rw [LinearIsometryEquiv.apply_symm_apply] at h
  rw [h,FourierTransform.fourierInv_fourier_eq]

/-- Actual spectral restriction followed by inverse Fourier transform, as an original native CLM. -/
def nativeSourcePiece (σ : ℝ) (hσ : 0 < σ) (p : ℕ)
    (R : ℕ+ → ℕ) (s : ℕ+ → ℝ) (E : Set Label) :
    HermiteScale (-(p:ℤ)) →L[ℂ] HermiteScale (-((6*p:ℕ):ℤ)) :=
  ((hermiteFourier (-((6*p:ℕ):ℤ))).symm.toContinuousLinearEquiv.toContinuousLinearMap).comp
    ((nativeMultiplier p (6*p) (actualSectorSelector σ hσ R s E)).comp
      (hermiteFourier (-(p:ℤ))).toContinuousLinearEquiv.toContinuousLinearMap)

/-- The constructed native piece is the complete inverse Fourier transform of the actual selected source. -/
theorem nativeSourcePiece_realizes (σ : ℝ) (hσ : 0 < σ) (p : ℕ)
    (R : ℕ+ → ℕ) (s : ℕ+ → ℝ) (E : Set Label) (T : HermiteScale (-(p:ℤ))) :
    hermiteScaleDistribution (6*p) (nativeSourcePiece σ hσ p R s E T) =
      𝓕⁻ (TemperedDistribution.smulLeftCLM ℂ (actualSectorSelector σ hσ R s E)
        (𝓕 (hermiteScaleDistribution p T))) := by
  change hermiteScaleDistribution (6*p) ((hermiteFourier (-((6*p:ℕ):ℤ))).symm
    (nativeMultiplier p (6*p) (actualSectorSelector σ hσ R s E)
      (hermiteFourier (-(p:ℤ)) T))) = _
  rw [hermiteFourier_symm_realizes,actualSectorSelector_native_realizes,
    hermiteFourier_represents_distributionalFourier]

/-- One original norm constant controls all pieces and all future remainders, before E is chosen. -/
theorem exists_nativeSourcePiece_norm_bound (σ : ℝ) (hσ : 0 < σ) (p : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ (R : ℕ+ → ℕ) (s : ℕ+ → ℝ) (E : Set Label)
      (T : HermiteScale (-(p:ℤ))), ‖nativeSourcePiece σ hσ p R s E T‖ ≤ B*‖T‖ := by
  obtain ⟨B,hB,hbound⟩ := exists_actualSectorSelector_native_norm_bound σ hσ p
  refine ⟨B,hB,fun R s E T => ?_⟩
  change ‖(hermiteFourier (-((6*p:ℕ):ℤ))).symm
    (nativeMultiplier p (6*p) (actualSectorSelector σ hσ R s E)
      (hermiteFourier (-(p:ℤ)) T))‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  calc
    _ ≤ ‖nativeMultiplier p (6*p) (actualSectorSelector σ hσ R s E)‖ *
        ‖hermiteFourier (-(p:ℤ)) T‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ B*‖T‖ := by rw [LinearIsometryEquiv.norm_map]; exact mul_le_mul_of_nonneg_right (hbound R s E) (norm_nonneg _)

/-- The actual selector takes the exact membership value on every sector point. -/
theorem actualSectorSelector_on_sector (σ : ℝ) (hσ : 0 < σ)
    (R : ℕ+ → ℕ) (s : ℕ+ → ℝ)
    (hsep : ∀ b d : Label, b ≠ d → ∀ x ∈ sectorSet R s b,
      ∀ y ∈ sectorSet R s d, σ/(1+|x|+|y|)^6 ≤ |x-y|)
    (E : Set Label) (b : Label) (x : ℝ) (hx : x ∈ sectorSet R s b) :
    actualSectorSelector σ hσ R s E x = if b ∈ E then 1 else 0 := by
  classical
  by_cases hb : b ∈ E
  · rw [ite_eq_left hb]
    exact (actualSectorSelector_near_selected σ hσ R s E b hb x hx).eq_of_nhds
  · rw [ite_eq_right hb]
    exact (actualSectorSelector_near_excluded σ hσ R s hsep E b hb x hx).eq_of_nhds

/-- Finite singleton selectors plus the complementary selector form an exact partition on the carrier. -/
theorem actualSectorSelector_finset_partition (σ : ℝ) (hσ : 0 < σ)
    (R : ℕ+ → ℕ) (s : ℕ+ → ℝ)
    (hsep : ∀ b d : Label, b ≠ d → ∀ x ∈ sectorSet R s b,
      ∀ y ∈ sectorSet R s d, σ/(1+|x|+|y|)^6 ≤ |x-y|)
    (F : Finset Label) (x : ℝ) (hx : x ∈ carrierSet R s) :
    (∑ b ∈ F, actualSectorSelector σ hσ R s {b} x) +
      actualSectorSelector σ hσ R s (↑F : Set Label)ᶜ x = 1 := by
  classical
  obtain ⟨b,hb⟩ := mem_iUnion.mp hx
  rw [actualSectorSelector_on_sector σ hσ R s hsep _ b x hb]
  have he : (∑ d ∈ F, actualSectorSelector σ hσ R s {d} x) = if b ∈ F then 1 else 0 := by
    calc
      _ = ∑ d ∈ F, (if b=d then (1:ℂ) else 0) := Finset.sum_congr rfl (fun d hd => by
        rw [actualSectorSelector_on_sector σ hσ R s hsep _ b x hb]; simp only [Set.mem_singleton_iff])
      _ = _ := by simp
  rw [he]
  by_cases h : b ∈ F <;> simp [h]

/-- Atomic whole sources split into finitely many actual spectral restrictions and the original future restriction. -/
theorem actualSectorSelector_finite_atomic_split (σ : ℝ) (hσ : 0 < σ)
    (R : ℕ+ → ℕ) (s : ℕ+ → ℝ)
    (hsep : ∀ b d : Label, b ≠ d → ∀ x ∈ sectorSet R s b,
      ∀ y ∈ sectorSet R s d, σ/(1+|x|+|y|)^6 ≤ |x-y|)
    (L : LocallyFiniteCarrier) (hL : L.carrier ⊆ carrierSet R s)
    (U : TemperedDistribution ℝ ℂ) (hU : AtomicOnCarrier L U) (F : Finset Label) :
    (∑ b ∈ F, TemperedDistribution.smulLeftCLM ℂ (actualSectorSelector σ hσ R s {b}) U) +
      TemperedDistribution.smulLeftCLM ℂ (actualSectorSelector σ hσ R s (↑F : Set Label)ᶜ) U = U := by
  classical
  ext f
  simp only [_root_.add_apply,_root_.sum_apply,TemperedDistribution.smulLeftCLM_apply_apply]
  apply sub_eq_zero.mp
  rw [← map_sum,← map_add,← map_sub]
  apply hU
  intro x hx
  simp only [_root_.sub_apply,_root_.add_apply,_root_.sum_apply,
    SchwartzMap.smulLeftCLM_apply_apply (actualSectorSelector_hasTemperateGrowth σ hσ R s _),smul_eq_mul]
  rw [← Finset.sum_mul,← add_mul,actualSectorSelector_finset_partition σ hσ R s hsep F x (hL hx),one_mul,sub_self]

/-- The whole original source equals its finite selected pieces plus the unaltered future piece.
This asserts spectral restriction only, not physical support of any piece. -/
theorem nativeSourcePiece_finite_split (σ : ℝ) (hσ : 0 < σ) (p : ℕ)
    (R : ℕ+ → ℕ) (s : ℕ+ → ℝ)
    (hsep : ∀ b d : Label, b ≠ d → ∀ x ∈ sectorSet R s b,
      ∀ y ∈ sectorSet R s d, σ/(1+|x|+|y|)^6 ≤ |x-y|)
    (L : LocallyFiniteCarrier) (hL : L.carrier ⊆ carrierSet R s)
    (T : HermiteScale (-(p:ℤ)))
    (hT : AtomicOnCarrier L (𝓕 (hermiteScaleDistribution p T))) (F : Finset Label) :
    (∑ b ∈ F, hermiteScaleDistribution (6*p) (nativeSourcePiece σ hσ p R s {b} T)) +
      hermiteScaleDistribution (6*p) (nativeSourcePiece σ hσ p R s (↑F : Set Label)ᶜ T) =
        hermiteScaleDistribution p T := by
  simp only [nativeSourcePiece_realizes]
  have h := congrArg (FourierTransform.fourierInvCLM ℂ (TemperedDistribution ℝ ℂ))
    (actualSectorSelector_finite_atomic_split σ hσ R s hsep L hL _ hT F)
  simpa only [map_add,map_sum,FourierTransform.fourierInvCLM_apply,
    FourierTransform.fourierInv_fourier_eq] using! h


/-- The complete Fourier transform of a constructed piece is exactly its selected spectral source. -/
theorem fourier_nativeSourcePiece (σ : ℝ) (hσ : 0 < σ) (p : ℕ)
    (R : ℕ+ → ℕ) (s : ℕ+ → ℝ) (E : Set Label) (T : HermiteScale (-(p:ℤ))) :
    𝓕 (hermiteScaleDistribution (6*p) (nativeSourcePiece σ hσ p R s E T)) =
      TemperedDistribution.smulLeftCLM ℂ (actualSectorSelector σ hσ R s E)
        (𝓕 (hermiteScaleDistribution p T)) := by
  rw [nativeSourcePiece_realizes,FourierTransform.fourier_fourierInv_eq]

/-- The spectral record of each piece is value-only on the actual selected carrier. -/
theorem nativeSourcePiece_spectral_atomic (σ : ℝ) (hσ : 0 < σ) (p : ℕ)
    (R : ℕ+ → ℕ) (s : ℕ+ → ℝ)
    (hsep : ∀ b d : Label, b ≠ d → ∀ x ∈ sectorSet R s b,
      ∀ y ∈ sectorSet R s d, σ/(1+|x|+|y|)^6 ≤ |x-y|)
    (L : LocallyFiniteCarrier) (hL : L.carrier ⊆ carrierSet R s)
    (T : HermiteScale (-(p:ℤ)))
    (hT : AtomicOnCarrier L (𝓕 (hermiteScaleDistribution p T))) (E : Set Label) :
    AtomicOnCarrier (L.restrict (L.carrier ∩ selectedSectorUnion R s E) inter_subset_left)
      (𝓕 (hermiteScaleDistribution (6*p) (nativeSourcePiece σ hσ p R s E T))) := by
  rw [fourier_nativeSourcePiece]
  apply actualSectorSelector_atomic_restrict σ hσ R s hsep L _ _ hT E
  intro x hx
  obtain ⟨b,hb⟩ := mem_iUnion.mp (hL hx)
  exact mem_iUnion.mpr ⟨b,mem_iUnion.mpr ⟨mem_univ b,hb⟩⟩

/-- Future spectral sectors lie beyond the common central gap; no physical assertion is made. -/
theorem nativeSourcePiece_future_spectral_support (σ : ℝ) (hσ : 0 < σ) (p : ℕ)
    (R : ℕ+ → ℕ) (s : ℕ+ → ℝ)
    (hR : ∀ i, 1 ≤ R i) (hs : ∀ i, s i ∈ Icc (1:ℝ) 2)
    (hsep : ∀ b d : Label, b ≠ d → ∀ x ∈ sectorSet R s b,
      ∀ y ∈ sectorSet R s d, σ/(1+|x|+|y|)^6 ≤ |x-y|)
    (L : LocallyFiniteCarrier) (hL : L.carrier ⊆ carrierSet R s)
    (T : HermiteScale (-(p:ℤ)))
    (hT : AtomicOnCarrier L (𝓕 (hermiteScaleDistribution p T)))
    (F : Finset Label) (r : ℝ) (hr : 2 ≤ r)
    (hgap : ∀ b : Label, b ∉ F → r ≤ (R b.1:ℝ)) :
    DistributionSupportedOn {x : ℝ | r/3 < |x|}
      (𝓕 (hermiteScaleDistribution (6*p)
        (nativeSourcePiece σ hσ p R s (↑F : Set Label)ᶜ T))) := by
  have hat := nativeSourcePiece_spectral_atomic σ hσ p R s hsep L hL T hT (↑F : Set Label)ᶜ
  intro f hf hz
  apply hat
  intro x hx
  rcases hx with ⟨hxL,hxE⟩
  obtain ⟨b,hb⟩ := mem_iUnion.mp hxE
  obtain ⟨hbF,hb⟩ := mem_iUnion.mp hb
  have hbgap := sectorSet_central_gap R s hR hs b hb
  have hRbgap := hgap b hbF
  have hout : r/3 < |x| := by linarith
  exact (hz x hout).eq_of_nhds

/-- The actual adaptive carrier satisfies the exact finite whole-source decomposition. -/
theorem adaptive_nativeSourcePiece_finite_split (σ : ℝ) (hσ : 0 < σ) (p : ℕ)
    (R : ℕ+ → ℕ) (s : ℕ+ → ℝ)
    (hR : ∀ i : ℕ+, (i:ℕ) ≤ R i) (hs : ∀ i, s i ∈ Icc (1:ℝ) 2)
    (hsep : ∀ b d : Label, b ≠ d → ∀ x ∈ sectorSet R s b,
      ∀ y ∈ sectorSet R s d, σ/(1+|x|+|y|)^6 ≤ |x-y|)
    (T : HermiteScale (-(p:ℤ)))
    (hT : AtomicOnCarrier (adaptiveCarrier R s hR hs) (𝓕 (hermiteScaleDistribution p T)))
    (F : Finset Label) :
    (∑ b ∈ F, hermiteScaleDistribution (6*p) (nativeSourcePiece σ hσ p R s {b} T)) +
      hermiteScaleDistribution (6*p) (nativeSourcePiece σ hσ p R s (↑F : Set Label)ᶜ T) =
        hermiteScaleDistribution p T := by
  apply nativeSourcePiece_finite_split σ hσ p R s hsep (adaptiveCarrier R s hR hs) _ T hT F
  rw [adaptiveCarrier_carrier]

end
end MeyerGeneralProblem.Adaptive
