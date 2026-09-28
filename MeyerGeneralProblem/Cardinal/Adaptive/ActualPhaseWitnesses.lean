module

public import MeyerGeneralProblem.Cardinal.Adaptive.PrefixPhaseErrorBounds
public import MeyerGeneralProblem.Cardinal.Adaptive.ActualFutureTailBounds

@[expose] public section

/-! # Two phase choices at the actual deterministically selected stage

Piece centers are fixed once for both phase choices. Only the net witnesses
vary. Every support and gap condition is supplied by the constructed stage.
-/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open Set

/-- A support center when the test is nonzero, and zero for an empty support. -/
def testPieceCenter (g : SchwartzMap ℝ ℂ) : ℝ := by
  classical
  exact if h : (tsupport g).Nonempty then h.choose else 0

/-- Every nonempty test has its selected center in its support. -/
theorem testPieceCenter_mem (g : SchwartzMap ℝ ℂ) (h : (tsupport g).Nonempty) :
    testPieceCenter g ∈ tsupport g := by
  rw [testPieceCenter,dite_eq_left h]
  exact h.choose_spec

/-- Centers stay inside the original symmetric support bound, including empty pieces. -/
theorem testPieceCenter_abs_le (g : SchwartzMap ℝ ℂ) (S : ℝ) (hS : 0 ≤ S)
    (hg : tsupport g ⊆ Icc (-S) S) : |testPieceCenter g| ≤ S := by
  by_cases h : (tsupport g).Nonempty
  · exact abs_le.mpr (hg (testPieceCenter_mem g h))
  · simp only [testPieceCenter,dite_eq_right h,abs_zero]
    exact hS

/-- The same predetermined center works for either phase choice, even for empty pieces. -/
theorem exists_piece_center_avoiding_translation (M : ℕ) (R : ℕ+ → ℕ) (s : ℕ+ → ℝ)
    (hR : ∀ i, 1 ≤ R i) (hs : ∀ i, s i ∈ Icc (1:ℝ) 2)
    (target : Fin M × ReciprocalSign) (f g : SchwartzMap ℝ ℂ)
    (hsupport : tsupport g ⊆ tsupport f) (ρ η δ H₀ H₁ : ℝ) (hρ : 0 < ρ) (hη : 0 < η)
    (hηρ : η ≤ ρ/10) (hηδ : η ≤ δ)
    (hsmall : ∀ x ∈ tsupport g, ∀ y ∈ tsupport g, |x-y| < ρ)
    (hrho : ∀ i : Fin M, ρ < 1/(100*(headLength (R (prefixScaleIndex i)):ℝ)))
    (hmargin : ∀ x ∈ tsupport f, ∀ y : ℝ, |y-x| < δ →
      y ∉ physicalPeriodicSet R s (prefixScaleIndex target.1,target.2))
    (hnet : s ∈ prefixSegmentNetEvent M H₀ H₁ (η/4)) (flip : Bool) :
    ∃ h : ℝ, H₀ ≤ h ∧ h ≤ H₁ ∧ ∃ n : (Fin M × ReciprocalSign) → ℤ,
      (∀ b, |h-pieceTargetPhase s target (testPieceCenter g) flip b-
        (n b:ℝ)*(2/labelScale s (prefixScaleIndex b.1,b.2))| < η) ∧
      ∀ b : Fin M × ReciprocalSign,
        tsupport (combSchwartzTranslation h g) ⊆ (physicalPeriodicSet R s (prefixScaleIndex b.1,b.2))ᶜ := by
  classical
  by_cases hg : (tsupport g).Nonempty
  · exact exists_piece_avoiding_translation M R s hR hs target f g hsupport ρ η δ
      (testPieceCenter g) H₀ H₁ hρ hη hηρ hηδ hsmall (testPieceCenter_mem g hg) hrho hmargin hnet flip
  · obtain ⟨h,hh₀,hh₁,hphase⟩ := prefix_net_supplies_physical_phases M s hs H₀ H₁ η hη hnet
      (pieceTargetPhase s target (testPieceCenter g) flip)
    choose n hn using hphase
    refine ⟨h,hh₀,hh₁,n,hn,?_⟩
    intro b x hx
    exact (hg ⟨h+x,by simpa only [translated_test_tsupport,mem_preimage] using hx⟩).elim

/-- The actual finite-stage partition scale fits every head gap in its prefix. -/
theorem actualStage_pieceRadius_head_bound (ψ : SchwartzMap ℝ ℂ) (n : ℕ) (i : Fin (n+1)) :
    (actualStage ψ n).pieceRadius < 1/(100*(headLength (actualPositiveGaps ψ (prefixScaleIndex i)):ℝ)) := by
  rw [(actualStage_laws ψ n).radius,actualPositiveGaps_prefix]
  exact (prefixPieceRadius_spec ⟨n+1,Nat.succ_pos _⟩ (fun j => actualGaps ψ j.val)
    (fun j => actualGaps_pos ψ j.val) _ (actualStage ψ n).closureGap_pos).2.2.2 i

/-- Both complete finite families of long translations avoid all prefix closures.
The center is identical for the two choices, so the exact flip identity applies. -/
theorem exists_actualStage_avoiding_translations (ψ : SchwartzMap ℝ ℂ) (s : ℕ+ → ℝ)
    (hs : ActualGoodScale ψ s) (n : ℕ) (target : Fin (n+1) × ReciprocalSign)
    (f : SchwartzMap ℝ ℂ) (δ : ℝ) (hδ : (actualStage ψ n).phaseTolerance ≤ δ)
    (hmargin : ∀ x ∈ tsupport f, ∀ y : ℝ, |y-x| < δ →
      y ∉ physicalPeriodicSet (actualPositiveGaps ψ) s (prefixScaleIndex target.1,target.2)) :
    ∃ h : Bool → Fin (actualStage ψ n).partitionSize → ℝ,
      ∃ z : Bool → Fin (actualStage ψ n).partitionSize → (Fin (n+1) × ReciprocalSign) → ℤ,
      (∀ flip i, (actualStage ψ n).translationStart ≤ h flip i ∧
        h flip i ≤ (actualStage ψ n).translationBound) ∧
      (∀ flip i b, |h flip i-pieceTargetPhase s target
        (testPieceCenter (SchwartzMap.smulLeftCLM ℂ ((actualStage ψ n).partition i) f)) flip b-
        (z flip i b:ℝ)*(2/labelScale s (prefixScaleIndex b.1,b.2))| < (actualStage ψ n).phaseTolerance) ∧
      ∀ flip i (b : Fin (n+1) × ReciprocalSign), tsupport (combSchwartzTranslation (h flip i)
        (SchwartzMap.smulLeftCLM ℂ ((actualStage ψ n).partition i) f)) ⊆
        (physicalPeriodicSet (actualPositiveGaps ψ) s (prefixScaleIndex b.1,b.2))ᶜ := by
  classical
  have hex (flip : Bool) (i : Fin (actualStage ψ n).partitionSize) :=
    exists_piece_center_avoiding_translation (n+1) (actualPositiveGaps ψ) s (actualPositiveGaps_pos ψ)
      hs.1.1 target f (SchwartzMap.smulLeftCLM ℂ ((actualStage ψ n).partition i) f)
      (fun _ hx => (SchwartzMap.tsupport_smulLeftCLM_subset _ _ hx).1)
      (actualStage ψ n).pieceRadius (actualStage ψ n).phaseTolerance δ
      (actualStage ψ n).translationStart (actualStage ψ n).translationBound
      (actualStage ψ n).pieceRadius_pos (actualStage ψ n).phaseTolerance_pos
      (actualStage_laws ψ n).phase_radius hδ
      (fun x hx y hy => (actualStage_laws ψ n).diameter i x
        (SchwartzMap.tsupport_smulLeftCLM_subset _ _ hx).2 y (SchwartzMap.tsupport_smulLeftCLM_subset _ _ hy).2)
      (actualStage_pieceRadius_head_bound ψ n) hmargin (hs.net ψ s n) flip
  choose h hh₀ hh₁ z hz havoid using hex
  exact ⟨h,z,fun flip i => ⟨hh₀ flip i,hh₁ flip i⟩,hz,havoid⟩

/-- Flipping the reciprocal label places every actual sector in its physical closure. -/
theorem sectorSet_subset_flipped_physicalPeriodicSet (R : ℕ+ → ℕ) (s : ℕ+ → ℝ) (b : Label) :
    sectorSet R s b ⊆ physicalPeriodicSet R s (b.1,b.2.flip) := by
  rintro x ⟨y,hy,rfl⟩
  refine ⟨y,blockSet_subset_periodicPhaseSet b.1 (R b.1) hy,?_⟩
  simp only [labelScale_flip,inv_inv]

/-- The actual next-gap floor excludes every future carrier point from all translated
stage tests. Together with prefix avoidance, this excludes the whole actual carrier. -/
theorem actualStage_translated_test_avoids_carrier (ψ : SchwartzMap ℝ ℂ) (s : ℕ+ → ℝ)
    (hs : ActualGoodScale ψ s) (n : ℕ) (g : SchwartzMap ℝ ℂ)
    (hg : tsupport g ⊆ Icc (-(n+1:ℝ)) (n+1:ℝ)) (h : ℝ)
    (hh : |h| ≤ (actualStage ψ n).translationBound)
    (havoid : ∀ b : Fin (n+1) × ReciprocalSign, tsupport (combSchwartzTranslation h g) ⊆
      (physicalPeriodicSet (actualPositiveGaps ψ) s (prefixScaleIndex b.1,b.2))ᶜ) :
    tsupport (combSchwartzTranslation h g) ⊆ (carrierSet (actualPositiveGaps ψ) s)ᶜ := by
  intro x hx hxC
  obtain ⟨b,hb⟩ := mem_iUnion.mp hxC
  by_cases hbM : b.1.val ≤ n+1
  · let i : Fin (n+1) := ⟨b.1.val-1,by have := b.1.pos; omega⟩
    have hi : prefixScaleIndex i = b.1 := by
      apply Subtype.ext
      change b.1.val-1+1 = b.1.val
      have := b.1.pos
      omega
    apply havoid (i,b.2.flip) hx
    simpa only [hi] using sectorSet_subset_flipped_physicalPeriodicSet _ s b hb
  · have hfuture := actual_future_gap ψ n b (by
      simpa only [mem_finitePrefixLabels_iff] using hbM)
    have hgap := sectorSet_central_gap (actualPositiveGaps ψ) s (actualPositiveGaps_pos ψ) hs.1.1 b hb
    have hfloor := (actualGaps_step ψ n).2.2.1
    have hfutureR : (actualGaps ψ (n+1):ℝ) ≤ (actualPositiveGaps ψ b.1:ℝ) := by exact_mod_cast hfuture
    have hxg : h+x ∈ tsupport g := by simpa only [translated_test_tsupport,mem_preimage] using hx
    have hsmall : |h+x| ≤ (n+1:ℝ) := abs_le.mpr (hg hxg)
    have htri := abs_sub (h+x) h
    have hcancel : h+x-h=x := by ring
    rw [hcancel] at htri
    linarith

/-- The original atomic source vanishes on each actual translated stage test.
This uses its given physical atomicity, never physical support of a spectral piece. -/
theorem actualStage_original_pairing_eq_zero (ψ : SchwartzMap ℝ ℂ) (s : ℕ+ → ℝ)
    (hs : ActualGoodScale ψ s) (n : ℕ) (g : SchwartzMap ℝ ℂ)
    (hg : tsupport g ⊆ Icc (-(n+1:ℝ)) (n+1:ℝ)) (h : ℝ)
    (hh : |h| ≤ (actualStage ψ n).translationBound)
    (havoid : ∀ b : Fin (n+1) × ReciprocalSign, tsupport (combSchwartzTranslation h g) ⊆
      (physicalPeriodicSet (actualPositiveGaps ψ) s (prefixScaleIndex b.1,b.2))ᶜ)
    (L : LocallyFiniteCarrier) (hL : L.carrier ⊆ carrierSet (actualPositiveGaps ψ) s)
    (T : TemperedDistribution ℝ ℂ) (hT : AtomicOnCarrier L T) :
    combDistributionTranslation h T g = 0 := by
  apply hT
  intro x hx
  apply image_eq_zero_of_notMem_tsupport
  intro hxg
  exact actualStage_translated_test_avoids_carrier ψ s hs n g hg h hh havoid hxg (hL hx)

end
end MeyerGeneralProblem.Adaptive
