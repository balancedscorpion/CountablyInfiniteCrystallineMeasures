module

public import MeyerGeneralProblem.Cardinal.Adaptive.ActualAtomRecovery
public import MeyerGeneralProblem.Cardinal.Adaptive.CriticalBlockComparison

@[expose] public section

/-! # Exact native reduction of recovered reciprocal pieces to literal blocks -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open Set
open scoped FourierTransform
set_option maxHeartbeats 800000

/-- Whole atomicity is carried by the actual pushforward dilation. -/
theorem atomicOnCarrier_combDilation (S A : LocallyFiniteCarrier) (a : ℝ) (ha : a ≠ 0)
    (hSA : ∀ x ∈ S.carrier, a*x ∈ A.carrier) (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier S T) : AtomicOnCarrier A (combDistributionDilation a ha T) := by
  intro f hf
  apply hT
  intro x hx
  change combSchwartzDilation a ha f x = 0
  rw [combSchwartzDilation_apply]
  exact hf _ (hSA x hx)

/-- Dilation by t_b sends the exact paired physical and spectral sectors to the
same literal block A_i. The Fourier inverse Jacobian is retained. -/
theorem paired_sectors_dilate_to_block (R : ℕ+ → ℕ) (s : ℕ+ → ℝ)
    (hR : ∀ i, 1 ≤ R i) (hs : ∀ i, s i ∈ Icc (1:ℝ) 2) (b : Label)
    (T : TemperedDistribution ℝ ℂ)
    (hphysical : AtomicOnCarrier (sectorCarrier R s hR hs (b.1,b.2.flip)) T)
    (hspectral : AtomicOnCarrier (sectorCarrier R s hR hs b) (𝓕 T)) :
    combDistributionDilation (labelScale s b) (labelScale_pos s hs b).ne' T ∈
      pairedAtomicSource (blockCarrier b.1 (R b.1) b.1.pos (hR b.1))
        (blockCarrier b.1 (R b.1) b.1.pos (hR b.1)) := by
  have ht := (labelScale_pos s hs b).ne'
  constructor
  · apply atomicOnCarrier_combDilation _ _ _ ht _ T hphysical
    intro x hx
    change x ∈ sectorSet R s (b.1,b.2.flip) at hx
    rw [← physicalSectorSet_eq_flipped] at hx
    obtain ⟨y,hy,rfl⟩ := hx
    change labelScale s b*((labelScale s b)⁻¹*y) ∈ blockSet b.1 (R b.1)
    simpa only [mul_inv_cancel_left₀ ht] using hy
  · change AtomicOnCarrier (blockCarrier b.1 (R b.1) b.1.pos (hR b.1))
      (𝓕 (combDistributionDilation (labelScale s b) ht T))
    rw [fourier_combDistributionDilation]
    have h := atomicOnCarrier_combDilation (sectorCarrier R s hR hs b)
      (blockCarrier b.1 (R b.1) b.1.pos (hR b.1)) (labelScale s b)⁻¹ (inv_ne_zero ht) (by
      intro x hx
      obtain ⟨y,hy,rfl⟩ := hx
      change y ∈ blockSet b.1 (R b.1) at hy
      change (labelScale s b)⁻¹*(labelScale s b*y) ∈ blockSet b.1 (R b.1)
      simpa only [inv_mul_cancel_left₀ ht] using hy) (𝓕 T) hspectral
    intro f hf
    simp only [smul_apply,h f hf,smul_zero]

/-- The selected spectral piece is value-only on its full literal sector. -/
theorem actualSourcePiece_spectral_sector (σ : ℝ) (hσ : 0 < σ) (p : ℕ)
    (R : ℕ+ → ℕ) (s : ℕ+ → ℝ) (hR : ∀ i, 1 ≤ R i) (hs : ∀ i, s i ∈ Icc (1:ℝ) 2)
    (hsep : ∀ b d : Label, b ≠ d → ∀ x ∈ sectorSet R s b,
      ∀ y ∈ sectorSet R s d, σ/(1+|x|+|y|)^6 ≤ |x-y|)
    (L : LocallyFiniteCarrier) (hL : L.carrier ⊆ carrierSet R s)
    (T : HermiteScale (-(p:ℤ))) (hT : AtomicOnCarrier L (𝓕 (hermiteScaleDistribution p T)))
    (b : Label) : AtomicOnCarrier (sectorCarrier R s hR hs b)
      (𝓕 (hermiteScaleDistribution (6*p) (nativeSourcePiece σ hσ p R s {b} T))) := by
  have h := nativeSourcePiece_spectral_atomic σ hσ p R s hsep L hL T hT {b}
  intro f hf
  apply h f
  intro x hx
  apply hf x
  obtain ⟨d,hd⟩ := mem_iUnion.mp hx.2
  obtain ⟨hd,hx⟩ := mem_iUnion.mp hd
  have he : d=b := hd
  change x ∈ sectorSet R s b
  simpa only [he] using hx

/-- Actual same-order block reduction as an original native continuous linear map. -/
def nativeBlockPiece (σ : ℝ) (hσ : 0 < σ) (p : ℕ)
    (R : ℕ+ → ℕ) (s : ℕ+ → ℝ) (hs : ∀ i, s i ∈ Icc (1:ℝ) 2) (b : Label) :
    HermiteScale (-(p:ℤ)) →L[ℂ] HermiteScale (-((6*p:ℕ):ℤ)) :=
  (nativeDilation (6*p) (labelScale s b) (labelScale_mem_Icc s hs b)).comp
    (nativeSourcePiece σ hσ p R s {b})

/-- The recovered actual piece is an element of the COMPLETE original native
block source, not a supplied one-dimensional line or a finite approximation. -/
theorem nativeBlockPiece_mem_actualBlock (s : ℕ+ → ℝ)
    (hs : ActualGoodScale fixedProbeTemplate s) (σ : ℝ) (hσ : 0 < σ) (p : ℕ)
    (hsep : ∀ b d : Label, b ≠ d → ∀ x ∈ sectorSet constructedGaps s b,
      ∀ y ∈ sectorSet constructedGaps s d, σ/(1+|x|+|y|)^6 ≤ |x-y|)
    (L : LocallyFiniteCarrier) (hL : L.carrier ⊆ carrierSet constructedGaps s)
    (T : HermiteScale (-(p:ℤ))) (hTphys : AtomicOnCarrier L (hermiteScaleDistribution p T))
    (hTspec : AtomicOnCarrier L (𝓕 (hermiteScaleDistribution p T)))
    (hphysical : ∀ d, DistributionSupportedOn (physicalPeriodicSet constructedGaps s d)
      (hermiteScaleDistribution (6*p) (nativeSourcePiece σ hσ p constructedGaps s {d} T)))
    (b : Label) : hermiteScaleDistribution (6*p)
      (nativeBlockPiece σ hσ p constructedGaps s hs.1.1 b T) ∈
      actualBlockNativeSource b.1 (constructedGaps b.1) b.1.pos
        (actualPositiveGaps_pos fixedProbeTemplate b.1) (6*p) := by
  have he : hermiteScaleDistribution (6*p) (nativeBlockPiece σ hσ p constructedGaps s hs.1.1 b T) =
      combDistributionDilation (labelScale s b) (labelScale_pos s hs.1.1 b).ne'
        (hermiteScaleDistribution (6*p) (nativeSourcePiece σ hσ p constructedGaps s {b} T)) := by
    simp only [nativeBlockPiece,ContinuousLinearMap.comp_apply,nativeDilation_realizes]
  constructor
  · rw [he]
    exact paired_sectors_dilate_to_block constructedGaps s (actualPositiveGaps_pos fixedProbeTemplate)
      hs.1.1 b _ (actualSourcePiece_physical_atomic s hs σ hσ p hsep L hL T hTphys hTspec hphysical b)
      (actualSourcePiece_spectral_sector σ hσ p constructedGaps s
        (actualPositiveGaps_pos fixedProbeTemplate) hs.1.1 hsep L hL T hTspec b)
  · exact ⟨_,rfl⟩

/-- The inverse physical dilation recovers the entire original tempered source. -/
theorem combDistributionDilation_inv_cancel (a : ℝ) (ha : a ≠ 0)
    (T : TemperedDistribution ℝ ℂ) :
    combDistributionDilation a⁻¹ (inv_ne_zero ha) (combDistributionDilation a ha T) = T := by
  ext f
  simp only [combDistributionDilation_apply]
  congr 1
  ext x
  simp only [combSchwartzDilation_apply,inv_mul_cancel_left₀ ha]

/-- Actual whole distribution dilation is injective, including at original order zero. -/
theorem combDistributionDilation_injective (a : ℝ) (ha : a ≠ 0) :
    Function.Injective (combDistributionDilation a ha) := by
  intro T U he
  have h := congrArg (combDistributionDilation a⁻¹ (inv_ne_zero ha)) he
  simpa only [combDistributionDilation_inv_cancel] using h

/-- Same-order native dilation is faithful because its whole distributional realization is. -/
theorem nativeDilation_injective (q : ℕ) (a : ℝ) (ha : a ∈ Icc (1/2:ℝ) 2) :
    Function.Injective (nativeDilation q a ha) := by
  intro T U he
  apply hermiteScaleDistribution_injective q
  apply combDistributionDilation_injective a (by have := ha.1; linarith)
  simpa only [nativeDilation_realizes] using congrArg (hermiteScaleDistribution q) he

/-- A zero reduced block source means that the original complete reciprocal piece was zero. -/
theorem nativeBlockPiece_eq_zero_iff (σ : ℝ) (hσ : 0 < σ) (p : ℕ)
    (R : ℕ+ → ℕ) (s : ℕ+ → ℝ) (hs : ∀ i, s i ∈ Icc (1:ℝ) 2) (b : Label)
    (T : HermiteScale (-(p:ℤ))) :
    nativeBlockPiece σ hσ p R s hs b T = 0 ↔ nativeSourcePiece σ hσ p R s {b} T = 0 := by
  simp only [nativeBlockPiece,ContinuousLinearMap.comp_apply]
  exact map_eq_zero_iff _ (nativeDilation_injective (6*p) (labelScale s b) (labelScale_mem_Icc s hs b))

/-- One fixed original norm bound controls every literal block reduction at a
fixed input order, uniformly in scales, gap schedules and labels. -/
theorem exists_nativeBlockPiece_norm_bound (σ : ℝ) (hσ : 0 < σ) (p : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℕ+ → ℕ) (s : ℕ+ → ℝ)
      (hs : ∀ i, s i ∈ Icc (1:ℝ) 2) (b : Label) (T : HermiteScale (-(p:ℤ))),
      ‖nativeBlockPiece σ hσ p R s hs b T‖ ≤ C*‖T‖ := by
  obtain ⟨A,hA,ha⟩ := exists_nativeDilation_norm_bound (6*p)
  obtain ⟨B,hB,hb⟩ := exists_nativeSourcePiece_norm_bound σ hσ p
  refine ⟨A*B,mul_pos hA hB,fun R s hs b T => ?_⟩
  simp only [nativeBlockPiece,ContinuousLinearMap.comp_apply]
  calc
    _ ≤ ‖nativeDilation (6*p) (labelScale s b) (labelScale_mem_Icc s hs b)‖ *
        ‖nativeSourcePiece σ hσ p R s {b} T‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ A*(B*‖T‖) := mul_le_mul (ha _ _) (hb _ _ _ T) (norm_nonneg _) hA.le
    _ = _ := by ring

end
end MeyerGeneralProblem.Adaptive
