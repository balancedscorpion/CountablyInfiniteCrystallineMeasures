module

public import MeyerGeneralProblem.Hermite.GeneralPointMassSupport
public import MeyerGeneralProblem.Endpoint.ReducedCross
public import MeyerGeneralProblem.Hilbert.TwoProjections

@[expose] public section

/-!
# Intrinsic fixed-order endpoint for extensional carriers

At a positive Hermite order, the physical support is the extensional
vanishing-ideal annihilator.  Its inverse-Fourier image is defined by the
genuine diagonal Hermite Fourier equivalence.  The fixed-order Meyer layer is
their intersection, independently of any enumeration or coefficient Gram
matrix.
-/

namespace MeyerGeneralProblem

noncomputable section

/-- Intrinsic physical support inside the order-`-m` Hermite Hilbert space. -/
def fixedOrderPhysicalSupport
    (S : LocallyFiniteCarrier) (m : ℕ) (hm : 1 ≤ m) :
    ClosedSubmodule ℂ (HermiteScale (-(m : ℤ))) :=
  locallyFiniteSupportedHermiteMeasureSubspace m hm S

/-- The inverse-Fourier support layer `𝓕⁻¹ X` inside the same Hermite scale. -/
def fixedOrderInverseFourierSupport
    (S : LocallyFiniteCarrier) (m : ℕ) (hm : 1 ≤ m) :
    ClosedSubmodule ℂ (HermiteScale (-(m : ℤ))) :=
  (fixedOrderPhysicalSupport S m hm).mapEquiv
    (hermiteFourier (-(m : ℤ))).symm

@[simp]
theorem mem_fixedOrderInverseFourierSupport_iff
    (S : LocallyFiniteCarrier) (m : ℕ) (hm : 1 ≤ m)
    (T : HermiteScale (-(m : ℤ))) :
    T ∈ fixedOrderInverseFourierSupport S m hm ↔
      hermiteFourier (-(m : ℤ)) T ∈ fixedOrderPhysicalSupport S m hm := by
  change T ∈ (fixedOrderPhysicalSupport S m hm).mapEquiv
      (hermiteFourier (-(m : ℤ))).symm ↔ _
  rw [ClosedSubmodule.mem_mapEquiv_iff]
  simp

/-- The intrinsic order-`m` Meyer layer: physical support intersected with
inverse-Fourier physical support. -/
def FixedOrderMeyerLayer
    (S : LocallyFiniteCarrier) (m : ℕ) (hm : 1 ≤ m) :
    Submodule ℂ (HermiteScale (-(m : ℤ))) :=
  (fixedOrderPhysicalSupport S m hm).toSubmodule ⊓
    (fixedOrderInverseFourierSupport S m hm).toSubmodule

@[simp]
theorem mem_fixedOrderMeyerLayer_iff
    (S : LocallyFiniteCarrier) (m : ℕ) (hm : 1 ≤ m)
    (T : HermiteScale (-(m : ℤ))) :
    T ∈ FixedOrderMeyerLayer S m hm ↔
      T ∈ fixedOrderPhysicalSupport S m hm ∧
        hermiteFourier (-(m : ℤ)) T ∈ fixedOrderPhysicalSupport S m hm := by
  simp [FixedOrderMeyerLayer]

/-- The intrinsic alternating-projection endpoint `P_X P_Y P_X`. -/
def fixedOrderEndpointOperator
    (S : LocallyFiniteCarrier) (m : ℕ) (hm : 1 ≤ m) :
    HermiteScale (-(m : ℤ)) →L[ℂ] HermiteScale (-(m : ℤ)) :=
  twoProjectionOperator
    (fixedOrderPhysicalSupport S m hm).toSubmodule
    (fixedOrderInverseFourierSupport S m hm).toSubmodule

/-- The eigenvalue-one subspace of the intrinsic endpoint. -/
def fixedOrderEndpointOneEigenspace
    (S : LocallyFiniteCarrier) (m : ℕ) (hm : 1 ≤ m) :
    Submodule ℂ (HermiteScale (-(m : ℤ))) :=
  (1 - fixedOrderEndpointOperator S m hm).ker

/-- The intrinsic fixed-order Meyer layer is exactly the endpoint's
eigenvalue-one space. -/
theorem fixedOrderMeyerLayer_eq_endpointOneEigenspace
    (S : LocallyFiniteCarrier) (m : ℕ) (hm : 1 ≤ m) :
    FixedOrderMeyerLayer S m hm =
      fixedOrderEndpointOneEigenspace S m hm := by
  unfold FixedOrderMeyerLayer fixedOrderEndpointOneEigenspace
    fixedOrderEndpointOperator
  exact (ker_one_sub_twoProjectionOperator
    (fixedOrderPhysicalSupport S m hm).toSubmodule
    (fixedOrderInverseFourierSupport S m hm).toSubmodule).symm

/-- The Friedrichs cosine of the intrinsic physical and inverse-Fourier
support layers. -/
def fixedOrderFriedrichsCosine
    (S : LocallyFiniteCarrier) (m : ℕ) (hm : 1 ≤ m) : ℝ :=
  friedrichsCosine
    (fixedOrderPhysicalSupport S m hm).toSubmodule
    (fixedOrderInverseFourierSupport S m hm).toSubmodule

/-- The reduced intrinsic endpoint radius. -/
def fixedOrderReducedRadius
    (S : LocallyFiniteCarrier) (m : ℕ) (hm : 1 ≤ m) : ℝ :=
  TwoProjectionEndpoint.reducedEndpointRadius
    (fixedOrderPhysicalSupport S m hm).toSubmodule
    (fixedOrderInverseFourierSupport S m hm).toSubmodule

/-- The reduced endpoint radius is the square of the intrinsic Friedrichs
cosine. -/
theorem fixedOrderReducedRadius_eq_friedrichsCosine_sq
    (S : LocallyFiniteCarrier) (m : ℕ) (hm : 1 ≤ m) :
    fixedOrderReducedRadius S m hm =
      fixedOrderFriedrichsCosine S m hm ^ 2 :=
  rfl

end

end MeyerGeneralProblem
