module

public import MeyerGeneralProblem.Cardinal.Adaptive.ActualPhaseErrorBounds
public import MeyerGeneralProblem.Cardinal.Adaptive.PeriodicDescent

@[expose] public section

/-! # Finite whole-source identities for the actual two-phase descent

Only a finite prefix is summed. Local polynomial agreement is supplied for each
whole source piece; neither a support assertion on a source piece nor convergence
of separate infinite coefficient series is assumed.
-/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open Set
open scoped FourierTransform

/-- The exact finite source identity turns the translated prefix polynomial sum
into minus the future pairing. Local lift remainders vanish on the actual avoided closures. -/
theorem actualStage_prefix_polynomial_pairing_eq_neg_future (ψ : SchwartzMap ℝ ℂ)
    (s : ℕ+ → ℝ) (hs : ActualGoodScale ψ s) (n D : ℕ)
    (V : (Fin (n+1) × ReciprocalSign) → Fin (D+1) → TemperedDistribution ℝ ℂ)
    (pieces : (Fin (n+1) × ReciprocalSign) → TemperedDistribution ℝ ℂ)
    (T future : TemperedDistribution ℝ ℂ)
    (hsplit : (∑ b, pieces b) + future = T)
    (hlocal : ∀ b : Fin (n+1) × ReciprocalSign, DistributionVanishesOn
      (physicalPeriodicSet (actualPositiveGaps ψ) s (prefixScaleIndex b.1,b.2))ᶜ
      (pieces b-∑ r, monomialDistribution r.val (V b r)))
    (L : LocallyFiniteCarrier) (hL : L.carrier ⊆ carrierSet (actualPositiveGaps ψ) s)
    (hT : AtomicOnCarrier L T) (g : SchwartzMap ℝ ℂ) (hgc : HasCompactSupport g)
    (hg : tsupport g ⊆ Icc (-(n+1:ℝ)) (n+1:ℝ)) (h : ℝ)
    (hh : |h| ≤ (actualStage ψ n).translationBound)
    (havoid : ∀ b : Fin (n+1) × ReciprocalSign, tsupport (combSchwartzTranslation h g) ⊆
      (physicalPeriodicSet (actualPositiveGaps ψ) s (prefixScaleIndex b.1,b.2))ᶜ) :
    (∑ b, combDistributionTranslation h (∑ r, monomialDistribution r.val (V b r)) g) =
      -combDistributionTranslation h future g := by
  have hzero := actualStage_original_pairing_eq_zero ψ s hs n g hg h hh havoid L hL T hT
  have hpiece (b : Fin (n+1) × ReciprocalSign) :
      combDistributionTranslation h (pieces b) g =
        combDistributionTranslation h (∑ r, monomialDistribution r.val (V b r)) g := by
    have he := hlocal b (combSchwartzTranslation h g)
      (hgc.comp_homeomorph (Homeomorph.addLeft h)) (havoid b)
    simpa only [sub_apply,combDistributionTranslation_apply,sub_eq_zero] using he
  have he := congrArg (fun U : TemperedDistribution ℝ ℂ => combDistributionTranslation h U g) hsplit
  simp only [map_add,map_sum,add_apply,sum_apply] at he
  simp_rw [hpiece] at he
  rw [hzero] at he
  exact eq_neg_of_add_eq_zero_left he

/-- A finite polynomial error sum is exactly the normalized polynomial sum
minus its top coefficient sum. This is a finite algebra identity in every degree. -/
theorem summed_normalized_polynomial_error_identity {ι κ : Type*} [Fintype ι] [Fintype κ]
    (D : ℕ) (h : ι → ℝ) (g : ι → SchwartzMap ℝ ℂ)
    (V : κ → Fin (D+1) → TemperedDistribution ℝ ℂ) :
    (∑ i, ∑ b, ∑ r : Fin (D+1), (((-(h i:ℂ))^D)⁻¹ *
      combDistributionTranslation (h i) (monomialDistribution r.val (V b r)) (g i) -
      (if r.val=D then combDistributionTranslation (h i) (V b r) (g i) else 0))) =
    (∑ i, ((-(h i:ℂ))^D)⁻¹ * ∑ b, combDistributionTranslation (h i)
      (∑ r, monomialDistribution r.val (V b r)) (g i)) -
    (∑ i, ∑ b, combDistributionTranslation (h i) (V b ⟨D,Nat.lt_succ_self D⟩) (g i)) := by
  simp_rw [← normalized_polynomial_pairing_error_eq_sum]
  simp only [Finset.sum_sub_distrib,Finset.mul_sum]

/-- Three paid errors give the desired finite phase-sum bound. -/
theorem norm_phase_sum_le_of_three_errors (F P A Z : ℂ) (ε B C : ℝ)
    (hP : P = -F) (hF : ‖F‖ ≤ ε*C) (hL : ‖P-A‖ ≤ ε*B)
    (hphase : ‖A-Z‖ ≤ ε*B) : ‖Z‖ ≤ ε*(2*B+C) := by
  have hpNorm : ‖P‖ ≤ ε*C := by simpa only [hP,norm_neg] using hF
  have he : Z = (Z-A)+(A-P)+P := by ring
  calc
    ‖Z‖ = ‖(Z-A)+(A-P)+P‖ := congrArg norm he
    _ ≤ ‖Z-A‖+‖A-P‖+‖P‖ := (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ ε*(2*B+C) := by rw [norm_sub_rev Z A,norm_sub_rev A P]; nlinarith

/-- Combine the finite error sums for distributions before specializing the
Hermite coefficients. This keeps the finite-sum rewrites small. -/
private theorem norm_phase_sum_le_of_polynomial_errors {ι κ : Type*} [Fintype ι] [Fintype κ]
    (D : ℕ) (h : ι → ℝ) (a : ι → κ → ℝ) (g : ι → SchwartzMap ℝ ℂ)
    (W : κ → Fin (D+1) → TemperedDistribution ℝ ℂ)
    (future : TemperedDistribution ℝ ℂ) (ε B C : ℝ)
    (hpoly : ∀ i, (∑ b, combDistributionTranslation (h i)
      (∑ r, monomialDistribution r.val (W b r)) (g i)) =
      -combDistributionTranslation (h i) future (g i))
    (hlead : ‖∑ i, ∑ b, ∑ r : Fin (D+1), (((-(h i:ℂ))^D)⁻¹ *
      combDistributionTranslation (h i) (monomialDistribution r.val (W b r)) (g i) -
      (if r.val=D then combDistributionTranslation (h i) (W b r) (g i) else 0))‖ ≤ ε*B)
    (hphase : ‖∑ i, ∑ b,
      (combDistributionTranslation (h i) (W b ⟨D,Nat.lt_succ_self D⟩) (g i) -
      combDistributionTranslation (a i b) (W b ⟨D,Nat.lt_succ_self D⟩) (g i))‖ ≤ ε*B)
    (hfuture : ‖∑ i, ((-(h i:ℂ))^D)⁻¹ *
      combDistributionTranslation (h i) future (g i)‖ ≤ ε*C) :
    ‖∑ i, ∑ b, combDistributionTranslation (a i b)
      (W b ⟨D,Nat.lt_succ_self D⟩) (g i)‖ ≤ ε*(2*B+C) := by
  rw [summed_normalized_polynomial_error_identity] at hlead
  simp only [Finset.sum_sub_distrib] at hphase
  apply norm_phase_sum_le_of_three_errors _ _ _ _ _ B C _ hfuture hlead hphase
  simp_rw [hpoly,mul_neg,Finset.sum_neg_distrib]

/-- The finite two-phase argument combines supplied error bounds for
distributions before the selected Hermite coefficients are inserted. -/
private theorem top_coefficient_bound_of_stage_errors (ψ : SchwartzMap ℝ ℂ) (s : ℕ+ → ℝ)
    (hs : ActualGoodScale ψ s) (n D : ℕ)
    (V : (Fin (n+1) × ReciprocalSign) → Fin (D+1) → TemperedDistribution ℝ ℂ)
    (hV : ∀ b r, combDistributionTranslation (labelScale s (prefixScaleIndex b.1,b.2))⁻¹
      (V b r) = -V b r)
    (B C : ℝ)
    (pieces : (Fin (n+1) × ReciprocalSign) → TemperedDistribution ℝ ℂ)
    (T : TemperedDistribution ℝ ℂ) (future : TemperedDistribution ℝ ℂ)
    (hsplit : (∑ b, pieces b) + future = T)
    (hlocal : ∀ b : Fin (n+1) × ReciprocalSign, DistributionVanishesOn
      (physicalPeriodicSet (actualPositiveGaps ψ) s (prefixScaleIndex b.1,b.2))ᶜ
      (pieces b-∑ r, monomialDistribution r.val (V b r)))
    (L : LocallyFiniteCarrier) (hL : L.carrier ⊆ carrierSet (actualPositiveGaps ψ) s)
    (hT : AtomicOnCarrier L T) (target : Fin (n+1) × ReciprocalSign)
    (f : SchwartzMap ℝ ℂ) (hf : tsupport f ⊆ Icc (-(n+1:ℝ)) (n+1:ℝ))
    (hleading : ∀ h : Fin (actualStage ψ n).partitionSize → ℝ,
      (∀ i, (actualStage ψ n).translationStart ≤ h i) →
      ‖∑ i, ∑ b, ∑ r : Fin (D+1),
        (((-(h i:ℂ))^D)⁻¹ * combDistributionTranslation (h i)
          (monomialDistribution r.val (V b r))
            (SchwartzMap.smulLeftCLM ℂ ((actualStage ψ n).partition i) f) -
        (if r.val = D then combDistributionTranslation (h i) (V b r)
          (SchwartzMap.smulLeftCLM ℂ ((actualStage ψ n).partition i) f) else 0))‖ ≤
        (2:ℝ)^(-((n+1:ℕ):ℤ))*B)
    (hphaseBound : ∀ (flip : Bool) (c h : Fin (actualStage ψ n).partitionSize → ℝ),
      (∀ i, |c i| ≤ (n+1:ℝ)) →
      ∀ z : Fin (actualStage ψ n).partitionSize → (Fin (n+1) × ReciprocalSign) → ℤ,
      (∀ i b, |h i-pieceTargetPhase s target (c i) flip b-
        (z i b:ℝ)*(2/labelScale s (prefixScaleIndex b.1,b.2))| < (actualStage ψ n).phaseTolerance) →
      ‖∑ i, ∑ b,
        (combDistributionTranslation (h i) (V b ⟨D,Nat.lt_succ_self D⟩)
          (SchwartzMap.smulLeftCLM ℂ ((actualStage ψ n).partition i) f) -
        combDistributionTranslation (pieceTargetPhase s target (c i) flip b)
          (V b ⟨D,Nat.lt_succ_self D⟩)
          (SchwartzMap.smulLeftCLM ℂ ((actualStage ψ n).partition i) f))‖ ≤
        (2:ℝ)^(-((n+1:ℕ):ℤ))*B)
    (hfutureBound : ∀ h : Fin (actualStage ψ n).partitionSize → ℝ,
      (∀ i, (actualStage ψ n).translationStart ≤ h i) →
      (∀ i, h i ≤ (actualStage ψ n).translationBound) →
      ‖∑ i, ((-(h i:ℂ))^D)⁻¹ * combDistributionTranslation (h i) future
        (SchwartzMap.smulLeftCLM ℂ ((actualStage ψ n).partition i) f)‖ ≤
        (2:ℝ)^(-((n+1:ℕ):ℤ))*C)
    (δ : ℝ) (hδ : (actualStage ψ n).phaseTolerance ≤ δ)
    (hmargin : ∀ x ∈ tsupport f, ∀ y : ℝ, |y-x| < δ →
      y ∉ physicalPeriodicSet (actualPositiveGaps ψ) s (prefixScaleIndex target.1,target.2)) :
    ‖V target ⟨D,Nat.lt_succ_self D⟩ f‖ ≤
      (2:ℝ)^(-((n+1:ℕ):ℤ))*(2*B+C) := by
  classical
  let ζ := (actualStage ψ n).partition
  let g (i : Fin (actualStage ψ n).partitionSize) := SchwartzMap.smulLeftCLM ℂ (ζ i) f
  let c (i : Fin (actualStage ψ n).partitionSize) := testPieceCenter (g i)
  let W (b : Fin (n+1) × ReciprocalSign) (r : Fin (D+1)) := V b r
  let top : Fin (D+1) := ⟨D,Nat.lt_succ_self D⟩
  obtain ⟨h,z,hh,hphase,havoid⟩ := exists_actualStage_avoiding_translations ψ s hs n target f δ hδ hmargin
  have hg (i : Fin (actualStage ψ n).partitionSize) : tsupport (g i) ⊆ Icc (-(n+1:ℝ)) (n+1:ℝ) :=
    fun _ hx => hf (SchwartzMap.tsupport_smulLeftCLM_subset _ _ hx).1
  have hgc (i : Fin (actualStage ψ n).partitionSize) : HasCompactSupport (g i) :=
    ((actualStage_laws ψ n).compact i).of_isClosed_subset (isClosed_tsupport _)
      (fun _ hx => (SchwartzMap.tsupport_smulLeftCLM_subset _ _ hx).2)
  have hc (i : Fin (actualStage ψ n).partitionSize) : |c i| ≤ (n+1:ℝ) :=
    testPieceCenter_abs_le (g i) (n+1) (by positivity) (hg i)
  have hdesired (flip : Bool) :
      ‖∑ i, ∑ b, combDistributionTranslation (pieceTargetPhase s target (c i) flip b) (W b top) (g i)‖ ≤
        (2:ℝ)^(-((n+1:ℕ):ℤ))*(2*B+C) := by
    have hpoly (i : Fin (actualStage ψ n).partitionSize) :=
      actualStage_prefix_polynomial_pairing_eq_neg_future ψ s hs n D W pieces T
        future hsplit hlocal L hL hT (g i) (hgc i) (hg i) (h flip i)
        (by rw [abs_of_nonneg ((actualStage ψ n).translationStart_nonneg.trans (hh flip i).1)]; exact (hh flip i).2)
        (havoid flip i)
    have hlead := hleading (h flip) (fun i => (hh flip i).1)
    have hph := hphaseBound flip c (h flip) hc (z flip) (hphase flip)
    have hfu := hfutureBound (h flip) (fun i => (hh flip i).1) (fun i => (hh flip i).2)
    exact norm_phase_sum_le_of_polynomial_errors D (h flip)
      (fun i b => pieceTargetPhase s target (c i) flip b) g W
      future ((2:ℝ)^(-((n+1:ℕ):ℤ))) B C
      hpoly hlead hph hfu
  have hζ : ∀ x ∈ tsupport f, ∑ i, ζ i x = 1 := fun x hx =>
    (actualStage_laws ψ n).sum_one x (by simpa only [PNat.mk_coe,Nat.cast_add,Nat.cast_one] using hf hx)
  exact norm_le_of_two_phase_bounds
    (partition_phase_flip_identity s target c (fun b => W b top) (hV target top) ζ f hζ)
    (hdesired false) (hdesired true)

/-- At one actual stage, the top coefficient is bounded by the three paid errors.
The hypotheses are the finite whole-source split and the literal local polynomial
agreement, precisely the outputs to be supplied by source splitting and the lift. -/
theorem actualStage_top_coefficient_pairing_bound (ψ : SchwartzMap ℝ ℂ) (s : ℕ+ → ℝ)
    (hs : ActualGoodScale ψ s) (n p D : ℕ) (hp : p ≤ n+1) (hD : D ≤ 12*p)
    (V : (Fin (n+1) × ReciprocalSign) → Fin (D+1) → HermiteScale (-((liftOrder p):ℤ)))
    (hV : ∀ b r, combDistributionTranslation (labelScale s (prefixScaleIndex b.1,b.2))⁻¹
      (hermiteScaleDistribution (liftOrder p) (V b r)) = -hermiteScaleDistribution (liftOrder p) (V b r))
    (B : ℝ) (hB : 0 ≤ B) (hnorm : ∀ b r, ‖V b r‖ ≤ B)
    (pieces : (Fin (n+1) × ReciprocalSign) → TemperedDistribution ℝ ℂ)
    (T : TemperedDistribution ℝ ℂ) (future : HermiteScale (-((6*p:ℕ):ℤ)))
    (hfuture : DistributionSupportedOn {x : ℝ | (actualGaps ψ (n+1):ℝ)/3 < |x|}
      (𝓕 (hermiteScaleDistribution (6*p) future)))
    (hsplit : (∑ b, pieces b) + hermiteScaleDistribution (6*p) future = T)
    (hlocal : ∀ b : Fin (n+1) × ReciprocalSign, DistributionVanishesOn
      (physicalPeriodicSet (actualPositiveGaps ψ) s (prefixScaleIndex b.1,b.2))ᶜ
      (pieces b-∑ r, monomialDistribution r.val (hermiteScaleDistribution (liftOrder p) (V b r))))
    (L : LocallyFiniteCarrier) (hL : L.carrier ⊆ carrierSet (actualPositiveGaps ψ) s)
    (hT : AtomicOnCarrier L T) (target : Fin (n+1) × ReciprocalSign)
    (f : SchwartzMap ℝ ℂ) (hf : tsupport f ⊆ Icc (-(n+1:ℝ)) (n+1:ℝ))
    (hfA : ∀ r ≤ testOrder p, ∀ x, ‖iteratedDeriv r (f : ℝ → ℂ) x‖ ≤ 1)
    (δ : ℝ) (hδ : (actualStage ψ n).phaseTolerance ≤ δ)
    (hmargin : ∀ x ∈ tsupport f, ∀ y : ℝ, |y-x| < δ →
      y ∉ physicalPeriodicSet (actualPositiveGaps ψ) s (prefixScaleIndex target.1,target.2)) :
    ‖hermiteScaleDistribution (liftOrder p) (V target ⟨D,Nat.lt_succ_self D⟩) f‖ ≤
      (2:ℝ)^(-((n+1:ℕ):ℤ))*(2*B+‖future‖) := by
  apply top_coefficient_bound_of_stage_errors ψ s hs n D
    (fun b r => hermiteScaleDistribution (liftOrder p) (V b r)) hV B ‖future‖
    pieces T (hermiteScaleDistribution (6*p) future) hsplit hlocal L hL hT target f hf
    ?_ ?_ ?_ δ hδ hmargin
  · intro h hh
    exact actualStage_leading_error_bound ψ n p D hp hD h hh f hf hfA
      (fun b => (labelScale s (prefixScaleIndex b.1,b.2))⁻¹)
      (fun b => physical_period_mem_Icc s hs.1.1 (prefixScaleIndex b.1,b.2))
      V hV B hB hnorm
  · intro flip c h hc z happrox
    exact actualStage_net_phase_error_bound ψ s hs n p hp target flip f hf hfA c h hc
      z happrox (fun b => V b ⟨D,Nat.lt_succ_self D⟩)
      (fun b => hV b ⟨D,Nat.lt_succ_self D⟩) B hB
      (fun b => hnorm b ⟨D,Nat.lt_succ_self D⟩)
  · intro h hh₀ hh₁
    exact actualStage_normalized_future_sum_bound ψ n p D hp future hfuture f hf hfA h hh₀ hh₁

end
end MeyerGeneralProblem.Adaptive
