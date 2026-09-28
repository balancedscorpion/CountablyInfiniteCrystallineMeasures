module

public import MeyerGeneralProblem.Atomic.SupportSubspace
public import MeyerGeneralProblem.Carrier.HermiteSynthesis
public import MeyerGeneralProblem.Carrier.Isolation

@[expose] public section

/-!
# Intrinsic carrier support in a negative Hermite scale

This module gives the carrier-supported subspace an intrinsic definition: it
is the annihilator, under Hermite duality, of every positive-scale vector
whose point evaluations vanish on the carrier.  Hilbert-space double
orthogonality then identifies this annihilator with the closed span of the
genuine normalized Dirac vectors.

The definition therefore excludes derivative atoms: membership is determined
by annihilating the full vanishing ideal, not merely by belonging to a
coefficient space bearing a suggestive name.
-/

namespace MeyerGeneralProblem

noncomputable section

/-- Hermite dual pairing as a continuous linear functional in its
positive-scale argument. -/
def hermiteScalePairingLeftCLM (m : ℕ)
    (T : HermiteScale (-(m : ℤ))) : HermiteScale (m : ℤ) →L[ℂ] ℂ :=
  (innerSL ℂ) (star T)

@[simp]
theorem hermiteScalePairingLeftCLM_apply (m : ℕ)
    (T : HermiteScale (-(m : ℤ))) (u : HermiteScale (m : ℤ)) :
    hermiteScalePairingLeftCLM m T u = hermiteScalePairing (m : ℤ) T u := by
  change inner ℂ (star T) u = hermiteScalePairing (m : ℤ) T u
  rw [lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  simp [RCLike.inner_apply, mul_comm]

/-- Hermite dual pairing as a linear functional in its negative-scale
argument. -/
def hermiteScalePairingRightLM (m : ℕ)
    (u : HermiteScale (m : ℤ)) : HermiteScale (-(m : ℤ)) →ₗ[ℂ] ℂ :=
  { toFun := fun T => hermiteScalePairing (m : ℤ) T u
    map_add' := by
      intro T U
      rw [hermiteScalePairing, hermiteScalePairing, hermiteScalePairing]
      simp_rw [lp.coeFn_add, Pi.add_apply, add_mul]
      exact Summable.tsum_add (summable_hermiteScalePairing (m : ℤ) T u)
        (summable_hermiteScalePairing (m : ℤ) U u)
    map_smul' := by
      intro c T
      rw [hermiteScalePairing, hermiteScalePairing]
      simp_rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
      exact tsum_mul_left }

/-- Hermite dual pairing as a continuous linear functional in its
negative-scale argument. -/
def hermiteScalePairingRightCLM (m : ℕ)
    (u : HermiteScale (m : ℤ)) : HermiteScale (-(m : ℤ)) →L[ℂ] ℂ :=
  (hermiteScalePairingRightLM m u).mkContinuous ‖u‖ fun T => by
    change ‖hermiteScalePairing (m : ℤ) T u‖ ≤ ‖u‖ * ‖T‖
    simpa only [mul_comm] using
      norm_hermiteScalePairing_le (m : ℤ) T u

@[simp]
theorem hermiteScalePairingRightCLM_apply (m : ℕ)
    (u : HermiteScale (m : ℤ)) (T : HermiteScale (-(m : ℤ))) :
    hermiteScalePairingRightCLM m u T = hermiteScalePairing (m : ℤ) T u :=
  rfl

theorem hermiteScalePairing_star_right (m : ℕ)
    (T z : HermiteScale (-(m : ℤ))) :
    hermiteScalePairing (m : ℤ) T (star z) = inner ℂ z T := by
  rw [hermiteScalePairing, lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  simp [RCLike.inner_apply]

theorem hermiteScalePairing_eq_inner_star_left (m : ℕ)
    (T : HermiteScale (-(m : ℤ))) (u : HermiteScale (m : ℤ)) :
    hermiteScalePairing (m : ℤ) T u = inner ℂ (star u) T := by
  rw [hermiteScalePairing, lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  simp [RCLike.inner_apply]

/-- Positive Hermite-scale vectors whose genuine point evaluations vanish at
every carrier node. -/
def carrierHermiteVanishingSubspace
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier) :
    ClosedSubmodule ℂ (HermiteScale (m : ℤ)) :=
  ⨅ j : ℤ, (⊥ : ClosedSubmodule ℂ ℂ).comap
    (hermiteScalePairingLeftCLM m (carrierHermitePointMass m hm Λ j))

@[simp]
theorem mem_carrierHermiteVanishingSubspace_iff
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier)
    (u : HermiteScale (m : ℤ)) :
    u ∈ carrierHermiteVanishingSubspace m hm Λ ↔
      ∀ j : ℤ, hermiteScalePairing (m : ℤ)
        (carrierHermitePointMass m hm Λ j) u = 0 := by
  simp [carrierHermiteVanishingSubspace]

/-- The intrinsic carrier-supported negative Hermite-scale subspace: the
annihilator of every positive-scale vector vanishing on the carrier. -/
def supportedHermiteMeasureSubspace
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier) :
    ClosedSubmodule ℂ (HermiteScale (-(m : ℤ))) :=
  ⨅ u : carrierHermiteVanishingSubspace m hm Λ,
    (⊥ : ClosedSubmodule ℂ ℂ).comap
      (hermiteScalePairingRightCLM m (u : HermiteScale (m : ℤ)))

@[simp]
theorem mem_supportedHermiteMeasureSubspace_iff
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier)
    (T : HermiteScale (-(m : ℤ))) :
    T ∈ supportedHermiteMeasureSubspace m hm Λ ↔
      ∀ u : carrierHermiteVanishingSubspace m hm Λ,
        hermiteScalePairing (m : ℤ) T (u : HermiteScale (m : ℤ)) = 0 := by
  simp [supportedHermiteMeasureSubspace]

/-- The intrinsic vanishing-ideal annihilator is exactly the closed span of
the genuine normalized carrier Dirac vectors. -/
theorem atomicSupportSubspace_eq_supportedHermiteMeasureSubspace
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier) :
    atomicSupportSubspace (carrierHermitePointMass m hm Λ) =
      (supportedHermiteMeasureSubspace m hm Λ).toSubmodule := by
  let A := atomicSupportSubspace (carrierHermitePointMass m hm Λ)
  let I := carrierHermiteVanishingSubspace m hm Λ
  let X := supportedHermiteMeasureSubspace m hm Λ
  apply le_antisymm
  · apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨j, rfl⟩
      change carrierHermitePointMass m hm Λ j ∈
        supportedHermiteMeasureSubspace m hm Λ
      rw [mem_supportedHermiteMeasureSubspace_iff]
      intro u
      exact (mem_carrierHermiteVanishingSubspace_iff m hm Λ u).mp
        u.property j
    · exact X.isClosed'
  · intro T hT
    have hdouble : T ∈ Aᗮᗮ := by
      rw [Submodule.mem_orthogonal]
      intro z hz
      have hstar : star z ∈ I := by
        rw [mem_carrierHermiteVanishingSubspace_iff]
        intro j
        rw [hermiteScalePairing_eq_inner_star_left]
        simpa using (A.mem_orthogonal' z).mp hz
          (carrierHermitePointMass m hm Λ j)
          (atom_mem_atomicSupportSubspace
            (carrierHermitePointMass m hm Λ) j)
      have hann :=
        (mem_supportedHermiteMeasureSubspace_iff m hm Λ T).mp hT
          ⟨star z, hstar⟩
      rw [hermiteScalePairing_star_right] at hann
      exact hann
    rw [A.orthogonal_orthogonal_eq_closure,
      (isClosed_atomicSupportSubspace
        (carrierHermitePointMass m hm Λ)).submodule_topologicalClosure_eq]
      at hdouble
    exact hdouble

/-- A Schwartz test vanishing at every carrier node gives a vector in the
positive-scale carrier vanishing ideal.  This ties the intrinsic Hilbert
definition directly to genuine distributional point evaluation. -/
theorem schwartzToHermiteScale_mem_carrierHermiteVanishingSubspace
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier)
    (f : SchwartzMap ℝ ℂ) (hf : ∀ j : ℤ, f (Λ j) = 0) :
    schwartzToHermiteScale m f ∈
      carrierHermiteVanishingSubspace m hm Λ := by
  rw [mem_carrierHermiteVanishingSubspace_iff]
  intro j
  rw [← hermiteScaleDistribution_apply]
  change hermiteScaleDistribution m
    (normalizedHermitePointMass m hm (Λ j)) f = 0
  rw [normalizedHermitePointMass_represents_delta]
  rw [smul_apply, pointMass_apply, hf j, smul_zero]

/-- Intrinsic carrier-supported vectors annihilate every Schwartz test that
vanishes on the carrier.  In particular this order-zero condition excludes
Dirac derivatives, which do not annihilate such tests. -/
theorem supportedHermiteMeasureSubspace_annihilates_vanishingSchwartz
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier)
    (T : HermiteScale (-(m : ℤ)))
    (hT : T ∈ supportedHermiteMeasureSubspace m hm Λ)
    (f : SchwartzMap ℝ ℂ) (hf : ∀ j : ℤ, f (Λ j) = 0) :
    hermiteScaleDistribution m T f = 0 := by
  rw [hermiteScaleDistribution_apply]
  exact (mem_supportedHermiteMeasureSubspace_iff m hm Λ T).mp hT
    ⟨schwartzToHermiteScale m f,
      schwartzToHermiteScale_mem_carrierHermiteVanishingSubspace
        m hm Λ f hf⟩

/-- A compactly supported Schwartz test is nonzero at only finitely many
carrier nodes. This is the local-finiteness input needed to turn the abstract
vanishing-ideal condition into an actual finite atomic formula. -/
theorem exists_finite_carrier_nonzero_values_of_hasCompactSupport
    (Λ : TwoSidedCarrier) (f : SchwartzMap ℝ ℂ)
    (hf : HasCompactSupport f) :
    ∃ E : Finset ℤ, ∀ k : ℤ, k ∉ E → f (Λ k) = 0 := by
  obtain ⟨R, hR⟩ :=
    (Metric.isBounded_iff_subset_ball 0).mp hf.isBounded
  let S : Set ℤ := {k : ℤ | Λ k ∈ Set.Icc (-R) R}
  have hS : S.Finite := Λ.finite_indices_in_Icc (-R) R
  refine ⟨hS.toFinset, ?_⟩
  intro k hk
  by_contra hne
  have hsupp : Λ k ∈ Function.support f := hne
  have htsupp : Λ k ∈ tsupport f := subset_tsupport f hsupp
  have hball := hR htsupp
  have habs : |Λ k| < R := by
    simpa [Real.dist_eq] using hball
  have hkS : k ∈ S := by
    exact ⟨le_of_lt (neg_lt_of_abs_lt habs),
      le_of_lt (lt_of_abs_lt habs)⟩
  exact hk (hS.mem_toFinset.mpr hkS)

/-- Local atomic action of an intrinsically carrier-supported vector. If all
nonzero carrier values of a Schwartz test lie in a finite set `E`, its action
is the corresponding finite sum of values against the isolating carrier
bumps. This is the explicit locally finite measure behavior behind the
vanishing-ideal definition. -/
theorem supportedHermiteMeasureSubspace_apply_eq_sum_isolation
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier)
    (T : HermiteScale (-(m : ℤ)))
    (hT : T ∈ supportedHermiteMeasureSubspace m hm Λ)
    (f : SchwartzMap ℝ ℂ) (E : Finset ℤ)
    (hE : ∀ k : ℤ, k ∉ E → f (Λ k) = 0) :
    hermiteScaleDistribution m T f =
      ∑ j ∈ E, f (Λ j) *
        hermiteScaleDistribution m T (Λ.isolationSchwartz j) := by
  let g : SchwartzMap ℝ ℂ :=
    f - ∑ j ∈ E, f (Λ j) • Λ.isolationSchwartz j
  have hg : ∀ k : ℤ, g (Λ k) = 0 := by
    intro k
    dsimp only [g]
    change f (Λ k) -
      (∑ j ∈ E, f (Λ j) • Λ.isolationSchwartz j) (Λ k) = 0
    rw [sub_eq_zero]
    simp only [_root_.sum_apply, smul_apply, smul_eq_mul]
    by_cases hk : k ∈ E
    · rw [Finset.sum_eq_single k]
      · rw [Λ.isolationSchwartz_self, mul_one]
      · intro j hj hjk
        rw [Λ.isolationSchwartz_of_ne hjk, mul_zero]
      · exact fun hnot => (hnot hk).elim
    · rw [Finset.sum_eq_zero]
      · exact hE k hk
      · intro j hj
        have hjk : j ≠ k := fun hjkeq => hk (hjkeq ▸ hj)
        rw [Λ.isolationSchwartz_of_ne hjk, mul_zero]
  have hzero :=
    supportedHermiteMeasureSubspace_annihilates_vanishingSchwartz
      m hm Λ T hT g hg
  dsimp only [g] at hzero
  rw [map_sub, map_sum] at hzero
  simp only [map_smul, smul_eq_mul, sub_eq_zero] at hzero
  exact hzero

/-- Every compactly supported Schwartz test admits the finite local atomic
action formula for an intrinsically carrier-supported vector. -/
theorem supportedHermiteMeasureSubspace_apply_eq_finite_sum_of_hasCompactSupport
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier)
    (T : HermiteScale (-(m : ℤ)))
    (hT : T ∈ supportedHermiteMeasureSubspace m hm Λ)
    (f : SchwartzMap ℝ ℂ) (hf : HasCompactSupport f) :
    ∃ E : Finset ℤ,
      (∀ k : ℤ, k ∉ E → f (Λ k) = 0) ∧
      hermiteScaleDistribution m T f =
        ∑ j ∈ E, f (Λ j) *
          hermiteScaleDistribution m T (Λ.isolationSchwartz j) := by
  obtain ⟨E, hE⟩ :=
    exists_finite_carrier_nonzero_values_of_hasCompactSupport Λ f hf
  exact ⟨E, hE,
    supportedHermiteMeasureSubspace_apply_eq_sum_isolation
      m hm Λ T hT f E hE⟩

end

end MeyerGeneralProblem
