module

public import MeyerGeneralProblem.Cardinal.Adaptive.ActualConvolutionVanishing

@[expose] public section

/-! Whole translated spectral sources localized to one actual phase. -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open Classical Set Filter
open scoped Topology FourierTransform

/-- The complete periodic spectral phase closure at a positive physical scale. -/
def scaledPeriodicPhaseSet (P R : ℕ) (t : ℝ) : Set ℝ :=
  (fun x : ℝ => t*x) '' periodicPhaseSet P R

/-- Translating by an integer number of scaled periods preserves the full closure. -/
theorem scaledPeriodicPhaseSet_add (P R : ℕ) (t : ℝ) (l : ℤ) {x : ℝ}
    (hx : x ∈ scaledPeriodicPhaseSet P R t) : x+t*(l:ℝ) ∈ scaledPeriodicPhaseSet P R t := by
  obtain ⟨y,hy,rfl⟩ := hx
  refine ⟨y+(l:ℝ),(periodicPhaseSet_add_int_iff P R y l).mpr hy,?_⟩
  ring

/-- A genuine isolating phase probe has value exactly one at its center and
zero at every other actual source atom. -/
theorem isolated_phase_probe_value (R : ℕ+ → ℕ) (s : ℕ+ → ℝ) (b : Label)
    (β γ : ℝ) (hγ : 0 < γ)
    (hisol : ∀ m : ℤ, ∀ y ∈ sectorSet R s b,
      y ≠ labelScale s b*((m:ℝ)+β) → 4*γ ≤ |y-labelScale s b*((m:ℝ)+β)|)
    (m : ℤ) (x : ℝ) (hx : x ∈ sectorSet R s b) :
    localJetProbe compactSchwartzCutoff γ hγ 0 (labelScale s b*((m:ℝ)+β)) x =
      if x=labelScale s b*((m:ℝ)+β) then 1 else 0 := by
  by_cases he : x=labelScale s b*((m:ℝ)+β)
  · rw [ite_eq_left he,he,localJetProbe_apply,sub_self,zero_div]
    simp only [pow_zero,Nat.factorial_zero,Nat.cast_one,div_one,one_mul]
    exact compactSchwartzCutoff_eq_one (by norm_num)
  · rw [ite_eq_right he]
    apply localJetProbe_cutoff_zero
    have h := hisol m x hx he
    linarith

/-- A test with only one nonzero periodic-phase value reads exactly the
corresponding actual coefficient under every integer translation. -/
theorem isolated_phase_translation_pairing (σ : ℝ) (hσ : 0 < σ) (p : ℕ)
    (R : ℕ+ → ℕ) (s : ℕ+ → ℝ)
    (hsep : ∀ b d : Label, b ≠ d → ∀ x ∈ sectorSet R s b,
      ∀ y ∈ sectorSet R s d, σ/(1+|x|+|y|)^6 ≤ |x-y|)
    (B : LocallyFiniteCarrier) (hB : B.carrier ⊆ carrierSet R s)
    (T : HermiteScale (-(p:ℤ))) (hFT : AtomicOnCarrier B (𝓕 (hermiteScaleDistribution p T)))
    (b : Label) (β γ : ℝ) (hγ : 0 < γ)
    (hisol : ∀ m : ℤ, ∀ y ∈ sectorSet R s b,
      y ≠ labelScale s b*((m:ℝ)+β) → 4*γ ≤ |y-labelScale s b*((m:ℝ)+β)|)
    (n l : ℤ) (f : SchwartzMap ℝ ℂ)
    (hf : ∀ y ∈ scaledPeriodicPhaseSet b.1 (R b.1) (labelScale s b),
      y ≠ labelScale s b*((n:ℝ)+β) → f y = 0) :
    combDistributionTranslation (labelScale s b*(l:ℝ))
      (𝓕 (hermiteScaleDistribution (6*p) (nativeSourcePiece σ hσ p R s {b} T))) f =
      f (labelScale s b*((n:ℝ)+β)) * isolatedSourceCoefficient σ hσ p R s b β γ hγ T (n-l) := by
  let U := 𝓕 (hermiteScaleDistribution (6*p) (nativeSourcePiece σ hσ p R s {b} T))
  let A := B.restrict (B.carrier ∩ selectedSectorUnion R s {b}) inter_subset_left
  have hU : AtomicOnCarrier A U := nativeSourcePiece_spectral_atomic σ hσ p R s hsep B hB T hFT {b}
  rw [combDistributionTranslation_apply]
  change U (combSchwartzTranslation (labelScale s b*(l:ℝ)) f) =
    f (labelScale s b*((n:ℝ)+β)) • U
      (localJetProbe compactSchwartzCutoff γ hγ 0 (labelScale s b*((((n-l):ℤ):ℝ)+β)))
  rw [← map_smul]
  apply atomic_test_eq_of_eqOn A U hU
  intro x hx
  have hxsec : x ∈ sectorSet R s b := by
    obtain ⟨d,hd⟩ := mem_iUnion.mp hx.2
    obtain ⟨hdb,hxd⟩ := mem_iUnion.mp hd
    have he : d=b := mem_singleton_iff.mp hdb
    simpa only [he] using hxd
  rw [combSchwartzTranslation_apply,_root_.smul_apply,smul_eq_mul,
    isolated_phase_probe_value R s b β γ hγ hisol (n-l) x hxsec]
  have he : x+labelScale s b*(l:ℝ) = labelScale s b*((n:ℝ)+β) ↔
      x=labelScale s b*((((n-l):ℤ):ℝ)+β) := by push_cast; constructor <;> intro h <;> nlinarith [h]
  by_cases hxcenter : x=labelScale s b*((((n-l):ℤ):ℝ)+β)
  · rw [ite_eq_left hxcenter,mul_one]
    congr 1
    linarith [(he.mpr hxcenter)]
  · rw [ite_eq_right hxcenter,mul_zero]
    have hmem := scaledPeriodicPhaseSet_add b.1 (R b.1) (labelScale s b) l
      (sectorSet_subset_scaled_periodic R s b hxsec)
    apply hf _
    · convert hmem using 1; ring
    · intro hh
      apply hxcenter
      apply he.mp
      linarith [hh]

end
end MeyerGeneralProblem.Adaptive
