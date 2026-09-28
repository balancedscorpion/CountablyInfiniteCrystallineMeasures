module

public import MeyerGeneralProblem.Cardinal.Adaptive.GlobalPhaseDescent

@[expose] public section

/-! # Finite downward support descent at the original fixed native order -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open Set
open scoped FourierTransform

/-- Multiplication by an actual monomial preserves local distributional vanishing. -/
theorem DistributionVanishesOn.monomial {O : Set ℝ} {T : TemperedDistribution ℝ ℂ}
    (hT : DistributionVanishesOn O T) (d : ℕ) : DistributionVanishesOn O (monomialDistribution d T) := by
  intro f hfc hf
  have hsupport : tsupport (monomialTestCLM d f) ⊆ tsupport f := by
    apply closure_mono
    intro x hx
    by_contra hxf
    have hxzero : f x=0 := by simpa only [Function.mem_support,not_not] using hxf
    exact hx (by simp only [monomialTestCLM_apply,hxzero,mul_zero])
  exact hT _ (hfc.of_isClosed_subset (isClosed_tsupport _) hsupport) (hsupport.trans hf)

/-- Once the top coefficient vanishes on a region, the same whole source agrees
there with its degree-truncated polynomial. No source splitting is changed. -/
theorem truncate_local_polynomial_agreement (O : Set ℝ) (D : ℕ)
    (piece : TemperedDistribution ℝ ℂ) (V : Fin (D+2) → TemperedDistribution ℝ ℂ)
    (hlocal : DistributionVanishesOn O (piece-∑ r, monomialDistribution r.val (V r)))
    (htop : DistributionVanishesOn O (V (Fin.last (D+1)))) :
    DistributionVanishesOn O (piece-∑ r : Fin (D+1), monomialDistribution r.val (V r.castSucc)) := by
  have he : piece-(∑ r : Fin (D+1), monomialDistribution r.val (V r.castSucc)) =
      (piece-∑ r : Fin (D+2), monomialDistribution r.val (V r)) +
        monomialDistribution (D+1) (V (Fin.last (D+1))) := by
    rw [Fin.sum_univ_castSucc (fun r : Fin (D+2) => monomialDistribution r.val (V r))]
    simp only [Fin.val_castSucc,Fin.val_last]
    abel
  intro f hfc hf
  rw [he,add_apply,hlocal f hfc hf,(htop.monomial (D+1)) f hfc hf,add_zero]

/-- Every whole coefficient is supported on its own actual physical closure.
Downward induction repeatedly reuses the same finite source identity, future
norm bound, native order and prescribed test derivative order. -/
theorem all_coefficients_vanishOffClosure (ψ : SchwartzMap ℝ ℂ) (s : ℕ+ → ℝ)
    (hs : ActualGoodScale ψ s) (p D : ℕ) (hD : D ≤ 12*p)
    (V : Label → Fin (D+1) → HermiteScale (-((liftOrder p):ℤ)))
    (hV : ∀ b r, combDistributionTranslation (labelScale s b)⁻¹
      (hermiteScaleDistribution (liftOrder p) (V b r)) = -hermiteScaleDistribution (liftOrder p) (V b r))
    (B : ℝ) (hB : 0 ≤ B) (hnorm : ∀ b r, ‖V b r‖ ≤ B)
    (pieces : Label → TemperedDistribution ℝ ℂ) (T : TemperedDistribution ℝ ℂ)
    (future : ℕ → HermiteScale (-((6*p:ℕ):ℤ))) (BF : ℝ) (hBF : ∀ n, ‖future n‖ ≤ BF)
    (hfuture : ∀ n, DistributionSupportedOn {x : ℝ | (actualGaps ψ (n+1):ℝ)/3 < |x|}
      (𝓕 (hermiteScaleDistribution (6*p) (future n))))
    (hsplit : ∀ n, (∑ b : Fin (n+1) × ReciprocalSign, pieces (prefixScaleIndex b.1,b.2)) +
      hermiteScaleDistribution (6*p) (future n) = T)
    (hlocal : ∀ b : Label, DistributionVanishesOn (physicalPeriodicSet (actualPositiveGaps ψ) s b)ᶜ
      (pieces b-∑ r, monomialDistribution r.val (hermiteScaleDistribution (liftOrder p) (V b r))))
    (L : LocallyFiniteCarrier) (hL : L.carrier ⊆ carrierSet (actualPositiveGaps ψ) s)
    (hT : AtomicOnCarrier L T) :
    ∀ b r, DistributionVanishesOn (physicalPeriodicSet (actualPositiveGaps ψ) s b)ᶜ
      (hermiteScaleDistribution (liftOrder p) (V b r)) := by
  induction D with
  | zero =>
    intro b r
    have hr : r = ⟨0,Nat.zero_lt_succ 0⟩ := Fin.ext (by have := r.isLt; omega)
    subst r
    exact top_coefficient_vanishesOffClosure ψ s hs p 0 hD V hV B hB hnorm pieces T future BF hBF
      hfuture hsplit hlocal L hL hT b
  | succ D ih =>
    have htop (b : Label) := top_coefficient_vanishesOffClosure ψ s hs p (D+1) hD V hV B hB hnorm
      pieces T future BF hBF hfuture hsplit hlocal L hL hT b
    let V' (b : Label) (r : Fin (D+1)) := V b r.castSucc
    have hlocal' (b : Label) : DistributionVanishesOn (physicalPeriodicSet (actualPositiveGaps ψ) s b)ᶜ
        (pieces b-∑ r, monomialDistribution r.val (hermiteScaleDistribution (liftOrder p) (V' b r))) :=
      truncate_local_polynomial_agreement _ D (pieces b)
        (fun r => hermiteScaleDistribution (liftOrder p) (V b r)) (hlocal b) (htop b)
    have hlow := ih (by omega) V' (fun b r => hV b r.castSucc) (fun b r => hnorm b r.castSucc) hlocal'
    intro b r
    exact Fin.lastCases (htop b) (fun j => hlow b j) r

/-- Literal local vanishing off a set gives the repository's ordinary support
condition, including compact tests vanishing on neighborhoods of the set. -/
theorem DistributionVanishesOn.supportedOn {C : Set ℝ} {T : TemperedDistribution ℝ ℂ}
    (hT : DistributionVanishesOn Cᶜ T) : DistributionSupportedOn C T := by
  intro f hfc hf
  apply hT f hfc
  intro x hx hxC
  exact (notMem_tsupport_iff_eventuallyEq.mpr (hf x hxC)) hx

/-- Local polynomial agreement and support of every coefficient give ordinary
support of the actual whole source piece, with seams retained. -/
theorem piece_supportedOn_of_local_polynomial_agreement (C : Set ℝ) (D : ℕ)
    (piece : TemperedDistribution ℝ ℂ) (V : Fin (D+1) → TemperedDistribution ℝ ℂ)
    (hlocal : DistributionVanishesOn Cᶜ (piece-∑ r, monomialDistribution r.val (V r)))
    (hV : ∀ r, DistributionVanishesOn Cᶜ (V r)) : DistributionSupportedOn C piece := by
  apply DistributionVanishesOn.supportedOn
  intro f hfc hf
  have hsum : (∑ r, monomialDistribution r.val (V r)) f = 0 := by
    rw [sum_apply]
    exact Finset.sum_eq_zero (fun r _ => (hV r).monomial r.val f hfc hf)
  have he := hlocal f hfc hf
  simpa only [sub_apply,hsum,sub_zero] using he

end
end MeyerGeneralProblem.Adaptive
