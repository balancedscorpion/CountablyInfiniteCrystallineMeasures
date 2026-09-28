module

public import MeyerGeneralProblem.Hilbert.FriedrichsAngle

@[expose] public section

/-!
# Abstract reduced endpoint radius

The reduced endpoint operator is unitarily equivalent to the square of the
Friedrichs cross operator. At the abstract layer the radius is therefore the
square of its operator norm; concrete coefficient models later identify this
quantity with the physical endpoint compression.
-/

namespace MeyerGeneralProblem

noncomputable section

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace TwoProjectionEndpoint

/-- Abstract reduced endpoint radius for a pair of closed subspaces. -/
def reducedEndpointRadius (M N : Submodule 𝕜 E) [N.HasOrthogonalProjection] : ℝ :=
  ‖reducedCross M N‖ ^ 2

/-- Exact reduced-cross formula for the abstract endpoint radius. -/
theorem reducedEndpointRadius_eq_reducedCross_norm_sq
    (M N : Submodule 𝕜 E) [N.HasOrthogonalProjection] :
    reducedEndpointRadius M N = ‖reducedCross M N‖ ^ 2 :=
  rfl

end TwoProjectionEndpoint

end

end MeyerGeneralProblem
