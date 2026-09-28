module

public import MeyerGeneralProblem.Carrier.HermiteMeasureSupport
public import MeyerGeneralProblem.Carrier.GeneralIsolation
public import MeyerGeneralProblem.Distribution.SchwartzVanishing

@[expose] public section

/-!
# Intrinsic Hermite support for extensional carriers

This module removes the ordered `ℤ` presentation from the fixed-order
Hermite support construction.  All definitions are indexed by the subtype of
the extensional carrier, and the resulting support is characterized both as a
vanishing-ideal annihilator and as the closed span of the genuine normalized
Dirac vectors.
-/

namespace MeyerGeneralProblem

noncomputable section

/-- The normalized negative-scale Dirac vector at an extensional carrier
node. -/
def locallyFiniteCarrierHermitePointMass
    (m : ℕ) (hm : 1 ≤ m) (S : LocallyFiniteCarrier) (x : S.subtype) :
    HermiteScale (-(m : ℤ)) :=
  normalizedHermitePointMass m hm (x : ℝ)

@[simp]
theorem norm_locallyFiniteCarrierHermitePointMass
    (m : ℕ) (hm : 1 ≤ m) (S : LocallyFiniteCarrier) (x : S.subtype) :
    ‖locallyFiniteCarrierHermitePointMass m hm S x‖ = 1 :=
  norm_normalizedHermitePointMass m hm (x : ℝ)

/-- Positive-scale vectors whose genuine evaluations vanish on an
extensional carrier. -/
def locallyFiniteCarrierHermiteVanishingSubspace
    (m : ℕ) (hm : 1 ≤ m) (S : LocallyFiniteCarrier) :
    ClosedSubmodule ℂ (HermiteScale (m : ℤ)) :=
  ⨅ x : S.subtype, (⊥ : ClosedSubmodule ℂ ℂ).comap
    (hermiteScalePairingLeftCLM m
      (locallyFiniteCarrierHermitePointMass m hm S x))

@[simp]
theorem mem_locallyFiniteCarrierHermiteVanishingSubspace_iff
    (m : ℕ) (hm : 1 ≤ m) (S : LocallyFiniteCarrier)
    (u : HermiteScale (m : ℤ)) :
    u ∈ locallyFiniteCarrierHermiteVanishingSubspace m hm S ↔
      ∀ x : S.subtype, hermiteScalePairing (m : ℤ)
        (locallyFiniteCarrierHermitePointMass m hm S x) u = 0 := by
  simp [locallyFiniteCarrierHermiteVanishingSubspace]

/-- The intrinsic order-`m` physical support: the annihilator of the entire
positive-scale vanishing ideal of the carrier. -/
def locallyFiniteSupportedHermiteMeasureSubspace
    (m : ℕ) (hm : 1 ≤ m) (S : LocallyFiniteCarrier) :
    ClosedSubmodule ℂ (HermiteScale (-(m : ℤ))) :=
  ⨅ u : locallyFiniteCarrierHermiteVanishingSubspace m hm S,
    (⊥ : ClosedSubmodule ℂ ℂ).comap
      (hermiteScalePairingRightCLM m (u : HermiteScale (m : ℤ)))

@[simp]
theorem mem_locallyFiniteSupportedHermiteMeasureSubspace_iff
    (m : ℕ) (hm : 1 ≤ m) (S : LocallyFiniteCarrier)
    (T : HermiteScale (-(m : ℤ))) :
    T ∈ locallyFiniteSupportedHermiteMeasureSubspace m hm S ↔
      ∀ u : locallyFiniteCarrierHermiteVanishingSubspace m hm S,
        hermiteScalePairing (m : ℤ) T (u : HermiteScale (m : ℤ)) = 0 := by
  simp [locallyFiniteSupportedHermiteMeasureSubspace]

/-- The extensional vanishing-ideal annihilator is exactly the closed span
of normalized carrier Dirac vectors. -/
theorem locallyFiniteAtomicSupportSubspace_eq_supportedHermiteMeasureSubspace
    (m : ℕ) (hm : 1 ≤ m) (S : LocallyFiniteCarrier) :
    atomicSupportSubspace (locallyFiniteCarrierHermitePointMass m hm S) =
      (locallyFiniteSupportedHermiteMeasureSubspace m hm S).toSubmodule := by
  let A := atomicSupportSubspace (locallyFiniteCarrierHermitePointMass m hm S)
  let I := locallyFiniteCarrierHermiteVanishingSubspace m hm S
  let X := locallyFiniteSupportedHermiteMeasureSubspace m hm S
  apply le_antisymm
  · apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨x, rfl⟩
      change locallyFiniteCarrierHermitePointMass m hm S x ∈ X
      rw [mem_locallyFiniteSupportedHermiteMeasureSubspace_iff]
      intro u
      exact (mem_locallyFiniteCarrierHermiteVanishingSubspace_iff
        m hm S u).mp u.property x
    · exact X.isClosed'
  · intro T hT
    have hdouble : T ∈ Aᗮᗮ := by
      rw [Submodule.mem_orthogonal]
      intro z hz
      have hstar : star z ∈ I := by
        rw [mem_locallyFiniteCarrierHermiteVanishingSubspace_iff]
        intro x
        rw [hermiteScalePairing_eq_inner_star_left]
        simpa using (A.mem_orthogonal' z).mp hz
          (locallyFiniteCarrierHermitePointMass m hm S x)
          (atom_mem_atomicSupportSubspace
            (locallyFiniteCarrierHermitePointMass m hm S) x)
      have hann :=
        (mem_locallyFiniteSupportedHermiteMeasureSubspace_iff m hm S T).mp hT
          ⟨star z, hstar⟩
      rw [hermiteScalePairing_star_right] at hann
      exact hann
    rw [A.orthogonal_orthogonal_eq_closure,
      (isClosed_atomicSupportSubspace
        (locallyFiniteCarrierHermitePointMass m hm S)).submodule_topologicalClosure_eq]
      at hdouble
    exact hdouble

/-- Genuine Schwartz evaluation identifies carrier vanishing with membership
in the positive Hermite vanishing ideal. -/
theorem schwartzToHermiteScale_mem_locallyFiniteCarrierHermiteVanishingSubspace
    (m : ℕ) (hm : 1 ≤ m) (S : LocallyFiniteCarrier)
    (f : SchwartzMap ℝ ℂ) (hf : SchwartzVanishesOn S f) :
    schwartzToHermiteScale m f ∈
      locallyFiniteCarrierHermiteVanishingSubspace m hm S := by
  rw [mem_locallyFiniteCarrierHermiteVanishingSubspace_iff]
  intro x
  rw [← hermiteScaleDistribution_apply]
  change hermiteScaleDistribution m
    (normalizedHermitePointMass m hm (x : ℝ)) f = 0
  rw [normalizedHermitePointMass_represents_delta]
  rw [smul_apply, pointMass_apply, hf (x : ℝ) x.property, smul_zero]

/-- Intrinsically carrier-supported scale vectors annihilate every Schwartz
test vanishing on the extensional carrier. -/
theorem locallyFiniteSupportedHermiteMeasureSubspace_annihilates_vanishingSchwartz
    (m : ℕ) (hm : 1 ≤ m) (S : LocallyFiniteCarrier)
    (T : HermiteScale (-(m : ℤ)))
    (hT : T ∈ locallyFiniteSupportedHermiteMeasureSubspace m hm S)
    (f : SchwartzMap ℝ ℂ) (hf : SchwartzVanishesOn S f) :
    hermiteScaleDistribution m T f = 0 := by
  rw [hermiteScaleDistribution_apply]
  exact (mem_locallyFiniteSupportedHermiteMeasureSubspace_iff m hm S T).mp hT
    ⟨schwartzToHermiteScale m f,
      schwartzToHermiteScale_mem_locallyFiniteCarrierHermiteVanishingSubspace
        m hm S f hf⟩

end

end MeyerGeneralProblem
