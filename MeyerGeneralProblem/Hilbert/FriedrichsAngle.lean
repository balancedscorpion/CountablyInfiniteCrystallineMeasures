module

public import MeyerGeneralProblem.Hilbert.TwoProjections

@[expose] public section

/-!
# Friedrichs cross operator

The reduced cross operator restricts orthogonal projection from `M` to `N` to
the orthogonal complement, inside `M`, of the exact intersection.
-/

namespace MeyerGeneralProblem

noncomputable section

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The exact intersection, represented as a submodule of the source subspace. -/
def intersectionIn (M N : Submodule 𝕜 E) : Submodule 𝕜 M :=
  N.comap M.subtype

@[simp]
theorem mem_intersectionIn_iff {M N : Submodule 𝕜 E} {x : M} :
    x ∈ intersectionIn M N ↔ (x : E) ∈ N :=
  Iff.rfl

/-- Orthogonal projection from one closed subspace to another. -/
def projectionCross (M N : Submodule 𝕜 E) [N.HasOrthogonalProjection] :
    M →L[𝕜] N :=
  N.orthogonalProjectionOnto.comp M.subtypeL

@[simp]
theorem projectionCross_apply (M N : Submodule 𝕜 E)
    [N.HasOrthogonalProjection] (x : M) :
    projectionCross M N x = N.orthogonalProjectionOnto (x : E) :=
  rfl

/-- The cross operator after the exact intersection has been removed. -/
def reducedCross (M N : Submodule 𝕜 E) [N.HasOrthogonalProjection] :
    (intersectionIn M N).orthogonal →L[𝕜] N :=
  (projectionCross M N).comp (intersectionIn M N).orthogonal.subtypeL

@[simp]
theorem reducedCross_apply (M N : Submodule 𝕜 E)
    [N.HasOrthogonalProjection] (x : (intersectionIn M N).orthogonal) :
    reducedCross M N x = N.orthogonalProjectionOnto ((x : M) : E) :=
  rfl

/-- A nonzero reduced vector cannot attain equality in the projection
contraction. This is the pointwise contradiction behind the endpoint gap. -/
theorem reducedCross_apply_norm_lt (M N : Submodule 𝕜 E)
    [N.HasOrthogonalProjection] (x : (intersectionIn M N).orthogonal) (hx : x ≠ 0) :
    ‖reducedCross M N x‖ < ‖x‖ := by
  have hle : ‖reducedCross M N x‖ ≤ ‖x‖ := by
    change ‖N.starProjection (((x : (intersectionIn M N).orthogonal) : M) : E)‖ ≤
      ‖((x : (intersectionIn M N).orthogonal) : M)‖
    exact N.norm_starProjection_apply_le _
  refine lt_of_le_of_ne hle ?_
  intro heq
  have hnorm :
      ‖N.starProjection (((x : (intersectionIn M N).orthogonal) : M) : E)‖ =
        ‖(((x : (intersectionIn M N).orthogonal) : M) : E)‖ := by
    simpa only [reducedCross_apply, Submodule.starProjection_apply,
      Submodule.norm_coe] using heq
  have hxN : (((x : (intersectionIn M N).orthogonal) : M) : E) ∈ N :=
    (N.mem_iff_norm_starProjection _).mpr hnorm
  have hxInter : ((x : (intersectionIn M N).orthogonal) : M) ∈ intersectionIn M N := hxN
  have hxOrth : ((x : (intersectionIn M N).orthogonal) : M) ∈
      (intersectionIn M N).orthogonal := x.property
  have hxZero : ((x : (intersectionIn M N).orthogonal) : M) = 0 := by
    exact inner_self_eq_zero.mp (hxOrth _ hxInter)
  apply hx
  exact Subtype.ext hxZero

/-- The reduced cross operator is a contraction. -/
theorem reducedCross_norm_le_one (M N : Submodule 𝕜 E)
    [N.HasOrthogonalProjection] :
    ‖reducedCross M N‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖N.starProjection (((x : (intersectionIn M N).orthogonal) : M) : E)‖ ≤
    1 * ‖x‖
  simpa only [one_mul, Submodule.norm_coe] using
    N.norm_starProjection_apply_le ((((x : (intersectionIn M N).orthogonal) : M) : E))

/-- If the reduced cross norm is attained, the pointwise equality
contradiction upgrades the contraction to a strict operator-norm gap. The
compact-perturbation layer will supply norm attainment when the essential norm
is below one. -/
theorem reducedCross_norm_lt_one_of_attained (M N : Submodule 𝕜 E)
    [N.HasOrthogonalProjection]
    (hattain : ∃ x : (intersectionIn M N).orthogonal,
      ‖x‖ = 1 ∧ ‖reducedCross M N x‖ = ‖reducedCross M N‖) :
    ‖reducedCross M N‖ < 1 := by
  rcases hattain with ⟨x, hxNorm, hxAttain⟩
  have hx : x ≠ 0 := by
    intro hxZero
    subst x
    simp at hxNorm
  have hstrict := reducedCross_apply_norm_lt M N x hx
  rw [hxAttain, hxNorm] at hstrict
  exact hstrict

/-- The Friedrichs cosine of two closed subspaces. -/
def friedrichsCosine (M N : Submodule 𝕜 E) [N.HasOrthogonalProjection] : ℝ :=
  ‖reducedCross M N‖

end

end MeyerGeneralProblem
