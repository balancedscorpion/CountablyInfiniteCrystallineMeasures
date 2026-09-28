module

public import MeyerGeneralProblem.Endpoint.IntrinsicFixedOrder
public import MeyerGeneralProblem.Hermite.ScaleEmbedding
public import Mathlib.LinearAlgebra.Dimension.Basic
import all Mathlib.LinearAlgebra.Dimension.Basic

@[expose] public section

/-!
# Monotonicity of intrinsic fixed-order layers

The coherent Hermite-scale inclusion sends each genuine Dirac vector to the
same distribution at the next negative order.  Continuity therefore sends
the full closed physical span, and Fourier commutation sends the full Meyer
intersection, into the next layer.
-/

namespace MeyerGeneralProblem

noncomputable section

private theorem continuousLinearMap_maps_atomicSupportSubspace
    {ι H K : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup K] [NormedSpace ℂ K]
    (A : H →L[ℂ] K) (v : ι → H) (w : ι → K)
    (hatom : ∀ i, A (v i) ∈ atomicSupportSubspace w) :
    ∀ x ∈ atomicSupportSubspace v, A x ∈ atomicSupportSubspace w := by
  intro x hx
  have hxmap : A x ∈
      (atomicSupportSubspace v).map A.toLinearMap :=
    ⟨x, hx, rfl⟩
  apply ((show (atomicSupportSubspace v).map A.toLinearMap ≤
      atomicSupportSubspace w by
    unfold atomicSupportSubspace
    refine (Submodule.topologicalClosure_map A
      (Submodule.span ℂ (Set.range v))).trans ?_
    apply Submodule.topologicalClosure_minimal
    · rw [Submodule.map_le_iff_le_comap]
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact hatom i
    · exact isClosed_atomicSupportSubspace w)) hxmap

/-- An unnormalised Dirac vector includes coherently into the next negative
Hermite scale. -/
theorem hermiteScaleInclusion_hermitePointMass
    (m : ℕ) (hm : 1 ≤ m) (x : ℝ) :
    hermiteScaleInclusion m (hermitePointMass m hm x) =
      hermitePointMass (m + 1) (Nat.le_add_right_of_le hm) x := by
  apply hermiteScaleDistribution_injective (m + 1)
  rw [hermiteScaleDistribution_inclusion,
    hermitePointMass_represents_delta,
    hermitePointMass_represents_delta]

private theorem hermitePointMass_mem_normalized_atomicSupport
    (m : ℕ) (hm : 1 ≤ m) (x : ℝ) :
    hermitePointMass m hm x ∈
      atomicSupportSubspace (fun _ : Unit =>
        normalizedHermitePointMass m hm x) := by
  have hatom : normalizedHermitePointMass m hm x ∈
      atomicSupportSubspace (fun _ : Unit =>
        normalizedHermitePointMass m hm x) :=
    atom_mem_atomicSupportSubspace
      (fun _ : Unit => normalizedHermitePointMass m hm x) ()
  have hnorm : ‖hermitePointMass m hm x‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (hermitePointMass_ne_zero m hm x)
  have hscaled := (atomicSupportSubspace
    (fun _ : Unit => normalizedHermitePointMass m hm x)).smul_mem
      ((‖hermitePointMass m hm x‖ : ℝ) : ℂ) hatom
  simpa [normalizedHermitePointMass, smul_smul, hnorm] using hscaled

/-- Adjacent inclusion sends every normalized extensional carrier atom into
the next order's closed atomic support. -/
theorem hermiteScaleInclusion_locallyFiniteCarrierAtom_mem
    (S : LocallyFiniteCarrier) (m : ℕ) (hm : 1 ≤ m) (x : S.subtype) :
    hermiteScaleInclusion m
        (locallyFiniteCarrierHermitePointMass m hm S x) ∈
      atomicSupportSubspace
        (locallyFiniteCarrierHermitePointMass
          (m + 1) (Nat.le_add_right_of_le hm) S) := by
  unfold locallyFiniteCarrierHermitePointMass normalizedHermitePointMass
  rw [map_smul, hermiteScaleInclusion_hermitePointMass]
  apply Submodule.smul_mem
  have hpoint : hermitePointMass (m + 1) (Nat.le_add_right_of_le hm) (x : ℝ) ∈
      atomicSupportSubspace (fun _ : Unit =>
        normalizedHermitePointMass (m + 1)
          (Nat.le_add_right_of_le hm) (x : ℝ)) :=
    hermitePointMass_mem_normalized_atomicSupport
      (m + 1) (Nat.le_add_right_of_le hm) (x : ℝ)
  have hmono : atomicSupportSubspace (fun _ : Unit =>
      normalizedHermitePointMass (m + 1)
        (Nat.le_add_right_of_le hm) (x : ℝ)) ≤
      atomicSupportSubspace
        (locallyFiniteCarrierHermitePointMass
          (m + 1) (Nat.le_add_right_of_le hm) S) := by
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨_, rfl⟩
      exact atom_mem_atomicSupportSubspace
        (locallyFiniteCarrierHermitePointMass
          (m + 1) (Nat.le_add_right_of_le hm) S) x
    · exact isClosed_atomicSupportSubspace _
  exact hmono hpoint

/-- Adjacent Hermite inclusion preserves intrinsic physical support. -/
theorem hermiteScaleInclusion_mem_fixedOrderPhysicalSupport
    (S : LocallyFiniteCarrier) (m : ℕ) (hm : 1 ≤ m)
    (T : HermiteScale (-(m : ℤ)))
    (hT : T ∈ fixedOrderPhysicalSupport S m hm) :
    hermiteScaleInclusion m T ∈
      fixedOrderPhysicalSupport S (m + 1) (Nat.le_add_right_of_le hm) := by
  change T ∈ (locallyFiniteSupportedHermiteMeasureSubspace m hm S).toSubmodule at hT
  change hermiteScaleInclusion m T ∈
    (locallyFiniteSupportedHermiteMeasureSubspace
      (m + 1) (Nat.le_add_right_of_le hm) S).toSubmodule
  rw [← locallyFiniteAtomicSupportSubspace_eq_supportedHermiteMeasureSubspace]
  rw [← locallyFiniteAtomicSupportSubspace_eq_supportedHermiteMeasureSubspace] at hT
  exact continuousLinearMap_maps_atomicSupportSubspace
    (hermiteScaleInclusion m)
    (locallyFiniteCarrierHermitePointMass m hm S)
    (locallyFiniteCarrierHermitePointMass
      (m + 1) (Nat.le_add_right_of_le hm) S)
    (hermiteScaleInclusion_locallyFiniteCarrierAtom_mem S m hm) T hT

/-- Adjacent Hermite inclusion preserves the intrinsic fixed-order Meyer
layer. -/
theorem hermiteScaleInclusion_mem_fixedOrderMeyerLayer
    (S : LocallyFiniteCarrier) (m : ℕ) (hm : 1 ≤ m)
    (T : HermiteScale (-(m : ℤ)))
    (hT : T ∈ FixedOrderMeyerLayer S m hm) :
    hermiteScaleInclusion m T ∈
      FixedOrderMeyerLayer S (m + 1) (Nat.le_add_right_of_le hm) := by
  rw [mem_fixedOrderMeyerLayer_iff] at hT ⊢
  refine ⟨hermiteScaleInclusion_mem_fixedOrderPhysicalSupport
    S m hm T hT.1, ?_⟩
  rw [← hermiteFourier_inclusion_commute]
  exact hermiteScaleInclusion_mem_fixedOrderPhysicalSupport
    S m hm (hermiteFourier (-(m : ℤ)) T) hT.2

/-- The injective adjacent map between intrinsic Meyer layers. -/
def fixedOrderMeyerLayerInclusion
    (S : LocallyFiniteCarrier) (m : ℕ) (hm : 1 ≤ m) :
    FixedOrderMeyerLayer S m hm →ₗ[ℂ]
      FixedOrderMeyerLayer S (m + 1) (Nat.le_add_right_of_le hm) where
  toFun T := ⟨hermiteScaleInclusion m T,
    hermiteScaleInclusion_mem_fixedOrderMeyerLayer S m hm T T.property⟩
  map_add' T U := by
    apply Subtype.ext
    exact (hermiteScaleInclusion m).map_add T U
  map_smul' c T := by
    apply Subtype.ext
    exact (hermiteScaleInclusion m).map_smul c T

theorem fixedOrderMeyerLayerInclusion_injective
    (S : LocallyFiniteCarrier) (m : ℕ) (hm : 1 ≤ m) :
    Function.Injective (fixedOrderMeyerLayerInclusion S m hm) := by
  intro T U hTU
  apply Subtype.ext
  apply hermiteScaleInclusion_injective m
  exact congrArg Subtype.val hTU

/-- Adjacent fixed-order ranks are monotone. -/
theorem fixedOrderRank_succ
    (S : LocallyFiniteCarrier) (m : ℕ) (hm : 1 ≤ m) :
    Module.rank ℂ (FixedOrderMeyerLayer S m hm) ≤
      Module.rank ℂ
        (FixedOrderMeyerLayer S (m + 1) (Nat.le_add_right_of_le hm)) :=
  (fixedOrderMeyerLayerInclusion S m hm).rank_le_of_injective
  (fixedOrderMeyerLayerInclusion_injective S m hm)

/-- Fixed-order Meyer-layer rank is monotone in the positive Hermite order. -/
theorem fixedOrderRank_mono
    (S : LocallyFiniteCarrier) {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    Module.rank ℂ (FixedOrderMeyerLayer S m hm) ≤
      Module.rank ℂ (FixedOrderMeyerLayer S n (hm.trans hmn)) := by
  induction n, hmn using Nat.le_induction with
  | base => exact le_rfl
  | @succ n hmn ih =>
      exact ih.trans (by
        simpa only using fixedOrderRank_succ S n (hm.trans hmn))

end

end MeyerGeneralProblem
