module

public import MeyerGeneralProblem.Cardinal.Adaptive.EndpointLiteralMoments

@[expose] public section

/-! Quantitative recovery of the genuine original negative Hermite norm from test bounds. -/
noncomputable section
namespace MeyerGeneralProblem.Adaptive

/-- A whole tempered source with a declared original test bound has a native
representative with that same bound, at exactly the declared order. -/
theorem exists_native_representation_norm_le (p : ℕ) (T : TemperedDistribution ℝ ℂ)
    (C : ℝ) (hC : 0 ≤ C)
    (hT : ∀ f : SchwartzMap ℝ ℂ, ‖T f‖ ≤ C*‖schwartzToHermiteScale p f‖) :
    ∃ U : HermiteScale (-(p:ℤ)), ‖U‖ ≤ C ∧ hermiteScaleDistribution p U=T := by
  let A : HermiteScale (p:ℤ) →L[ℂ] ℂ :=
    T.toLinearMap.extendOfNorm (schwartzToHermiteScale p).toLinearMap
  let v := (InnerProductSpace.toDual ℂ (HermiteScale (p:ℤ))).symm A
  refine ⟨star v,?_,?_⟩
  · have hA : ‖A‖ ≤ C :=
      LinearMap.opNorm_extendOfNorm_le (schwartzToHermiteScale_denseRange p) hC hT
    simpa only [norm_star,v,LinearIsometryEquiv.norm_map] using hA
  · ext f
    rw [hermiteScaleDistribution_apply]
    have hp (u : HermiteScale (p:ℤ)) : hermiteScalePairing (p:ℤ) (star v) u=inner ℂ v u := by
      rw [hermiteScalePairing,lp.inner_eq_tsum]
      apply tsum_congr
      intro n
      simp [RCLike.inner_apply,mul_comm]
    rw [hp]
    exact InnerProductSpace.toDual_symm_apply.trans
      (LinearMap.extendOfNorm_eq (schwartzToHermiteScale_denseRange p) ⟨C,hT⟩ f)

/-- Every genuine native representative has the exact same norm bound when all
original Schwartz pairings have that bound; uniqueness removes the choice of lift. -/
theorem native_norm_le_of_schwartz_pairing (p : ℕ) (U : HermiteScale (-(p:ℤ)))
    (C : ℝ) (hC : 0 ≤ C)
    (hU : ∀ f : SchwartzMap ℝ ℂ,
      ‖hermiteScaleDistribution p U f‖ ≤ C*‖schwartzToHermiteScale p f‖) : ‖U‖ ≤ C := by
  obtain ⟨V,hV,he⟩ := exists_native_representation_norm_le p _ C hC hU
  exact (hermiteScaleDistribution_injective p he) ▸ hV

/-- The established actual-moment pairing estimate gives the same uniform bound
on every genuine native representative of the actual complete endpoint source. -/
theorem exists_rapidEndpointSource_actualMoment_native_bound {P R : ℕ}
    (hP : 1 ≤ P) (hR : 1 ≤ R) (L : ℕ) (hL : 4 < rapidBase P^L)
    (K : ℝ) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, ∀ c : EndpointMatrix k, ∀ A : ℝ, 0 ≤ A →
      (∀ (e d : Bool) (i j : Fin (k+1)),
        ‖halfNewtonMoment (fun r => rapidDistance P R r.val) (fun r => rapidDistance P R r.val)
          (halfWeylDistributionCLM (endpointPoissonSynthesis
            (rapidEndpointPhaseData P R k) (rapidEndpointPhaseData P R k) c)) i.val e j.val d‖ ≤
        A*K^(max i.val j.val)*shrinkingNewtonWeight (rapidDistance P R) (max i.val j.val)) →
      ∀ U : HermiteScale (-((2*L+2:ℕ):ℤ)),
      hermiteScaleDistribution (2*L+2) U = endpointPoissonSynthesis
        (rapidEndpointPhaseData P R k) (rapidEndpointPhaseData P R k) c → ‖U‖ ≤ C*A := by
  obtain ⟨C,hC,hb⟩ := exists_rapidEndpointSource_actualMoment_pairing_bound hP hR L hL K hK
  refine ⟨C,hC,?_⟩
  intro k c A hA hM U hU
  apply native_norm_le_of_schwartz_pairing (2*L+2) U (C*A) (mul_nonneg hC.le hA)
  intro f
  rw [hU]
  exact hb k c A hA hM f

end MeyerGeneralProblem.Adaptive
