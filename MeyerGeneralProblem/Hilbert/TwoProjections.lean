module

public import MeyerGeneralProblem.Basic
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import all Mathlib.Analysis.InnerProductSpace.Projection.Basic

@[expose] public section

/-!
# Two orthogonal projections

This file isolates the Hilbert-space identity underlying the endpoint problem.
The fixed space of `Pₘ Pₙ Pₘ` is exactly `M ∩ N`; no compactness or carrier
assumption enters here.
-/

namespace MeyerGeneralProblem

open ContinuousLinearMap

noncomputable section

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The alternating two-projection contraction `Pₘ Pₙ Pₘ`. -/
def twoProjectionOperator (M N : Submodule 𝕜 E)
    [M.HasOrthogonalProjection] [N.HasOrthogonalProjection] : E →L[𝕜] E :=
  M.starProjection.comp (N.starProjection.comp M.starProjection)

@[simp]
theorem twoProjectionOperator_apply (M N : Submodule 𝕜 E)
    [M.HasOrthogonalProjection] [N.HasOrthogonalProjection] (x : E) :
    twoProjectionOperator M N x = M.starProjection (N.starProjection (M.starProjection x)) :=
  rfl

/-- The one-eigenspace of the alternating projection operator is the exact
intersection of the two closed subspaces. -/
theorem ker_one_sub_twoProjectionOperator (M N : Submodule 𝕜 E)
    [M.HasOrthogonalProjection] [N.HasOrthogonalProjection] :
    (1 - twoProjectionOperator M N).ker = M ⊓ N := by
  ext x
  constructor
  · intro hx
    have heq : twoProjectionOperator M N x = x := by
      have hx0 : x - twoProjectionOperator M N x = 0 := by
        simpa using hx
      exact (sub_eq_zero.mp hx0).symm
    have hxM : x ∈ M := by
      rw [← heq]
      change M.starProjection (N.starProjection (M.starProjection x)) ∈ M
      simpa only [Submodule.starProjection_apply] using
        (M.orthogonalProjectionOnto (N.starProjection (M.starProjection x))).property
    have hMx : M.starProjection x = x := M.starProjection_eq_self_iff.mpr hxM
    have heq' : M.starProjection (N.starProjection x) = x := by
      simpa only [twoProjectionOperator_apply, hMx] using heq
    have hfirst : ‖M.starProjection (N.starProjection x)‖ ≤ ‖N.starProjection x‖ :=
      M.norm_starProjection_apply_le _
    have hsecond : ‖N.starProjection x‖ ≤ ‖x‖ := N.norm_starProjection_apply_le _
    have hnorm : ‖N.starProjection x‖ = ‖x‖ := by
      have heqNorm : ‖M.starProjection (N.starProjection x)‖ = ‖x‖ :=
        congrArg norm heq'
      linarith
    have hxN : x ∈ N := (N.mem_iff_norm_starProjection x).mpr hnorm
    exact ⟨hxM, hxN⟩
  · rintro ⟨hxM, hxN⟩
    have hMx : M.starProjection x = x := M.starProjection_eq_self_iff.mpr hxM
    have hNx : N.starProjection x = x := N.starProjection_eq_self_iff.mpr hxN
    change x - M.starProjection (N.starProjection (M.starProjection x)) = 0
    rw [hMx, hNx, hMx, sub_self]

end

end MeyerGeneralProblem
