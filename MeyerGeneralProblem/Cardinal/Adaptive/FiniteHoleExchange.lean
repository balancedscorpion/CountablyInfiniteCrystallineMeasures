module

public import Mathlib.LinearAlgebra.Dimension.Finrank
import all Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import all Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Analysis.Normed.Operator.Basic
import all Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Tactic.Ring
import all Mathlib.Tactic.Ring

@[expose] public section

/-!
# Reversible correction by a common head space

The algebra in `HIGH_ORDER_GAP_SURGERY.md` §1 works on whole vector spaces.
Two coordinate maps invertible on the same head space give inverse corrections
between their entire kernels, and between their intersections with every
submodule containing the head. The analytic construction must still supply
the actual coordinate maps and their invertibility; this file does not assert
those missing inputs for the adaptive carrier.
-/

namespace MeyerGeneralProblem.Adaptive

noncomputable section

variable {𝕜 V U : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]
  [AddCommGroup U] [Module 𝕜 U]

/-- Subtract the unique head vector with the given observed coordinates. -/
def holeCorrection (W : Submodule 𝕜 V) (E : V →ₗ[𝕜] U) (L : W ≃ₗ[𝕜] U) :
    V →ₗ[𝕜] V :=
  LinearMap.id - W.subtype.comp (L.symm.toLinearMap.comp E)

theorem holeCorrection_apply (W : Submodule 𝕜 V) (E : V →ₗ[𝕜] U)
    (L : W ≃ₗ[𝕜] U) (v : V) :
    holeCorrection W E L v = v - (L.symm (E v) : V) := rfl

/-- Exact agreement of the finite head inverse makes the corrected observation zero. -/
theorem holeCorrection_mem_kernel (W : Submodule 𝕜 V) (E : V →ₗ[𝕜] U)
    (L : W ≃ₗ[𝕜] U) (hL : ∀ w : W, E w = L w) (v : V) :
    holeCorrection W E L v ∈ LinearMap.ker E := by
  change E (v - (L.symm (E v) : V)) = 0
  rw [map_sub, hL, L.apply_symm_apply, sub_self]

/-- The correction annihilates the entire head space, not just a chosen basis. -/
theorem holeCorrection_head (W : Submodule 𝕜 V) (E : V →ₗ[𝕜] U)
    (L : W ≃ₗ[𝕜] U) (hL : ∀ w : W, E w = L w) (w : W) :
    holeCorrection W E L w = 0 := by
  rw [holeCorrection_apply, hL, L.symm_apply_apply, sub_self]

/-- A source satisfying the original holes is fixed by its own correction. -/
theorem holeCorrection_fixed (W : Submodule 𝕜 V) (E : V →ₗ[𝕜] U)
    (L : W ≃ₗ[𝕜] U) {v : V} (hv : v ∈ LinearMap.ker E) :
    holeCorrection W E L v = v := by
  change E v = 0 at hv
  simp [holeCorrection_apply, hv]

/-- A second correction changes a vector only by a head vector; the first
correction therefore erases that change exactly. -/
theorem holeCorrection_comp (W : Submodule 𝕜 V)
    (E₀ E₁ : V →ₗ[𝕜] U) (L₀ L₁ : W ≃ₗ[𝕜] U)
    (hL₀ : ∀ w : W, E₀ w = L₀ w) (v : V) :
    holeCorrection W E₀ L₀ (holeCorrection W E₁ L₁ v) =
      holeCorrection W E₀ L₀ v := by
  rw [holeCorrection_apply W E₁ L₁, map_sub, holeCorrection_head W E₀ L₀ hL₀]
  exact sub_zero _

/-- No order is lost when the head already belongs to the native subspace. -/
theorem holeCorrection_mem_submodule (W H : Submodule 𝕜 V) (hWH : W ≤ H)
    (E : V →ₗ[𝕜] U) (L : W ≃ₗ[𝕜] U) {v : V} (hv : v ∈ H) :
    holeCorrection W E L v ∈ H :=
  H.sub_mem hv (hWH (L.symm (E v)).property)

/-- Exact two-way exchange on every complete subspace containing the head.
There is no finite-dimensionality assumption on the ambient kernel. -/
def holeExchangeEquiv (W H : Submodule 𝕜 V) (hWH : W ≤ H)
    (E₀ E₁ : V →ₗ[𝕜] U) (L₀ L₁ : W ≃ₗ[𝕜] U)
    (hL₀ : ∀ w : W, E₀ w = L₀ w) (hL₁ : ∀ w : W, E₁ w = L₁ w) :
    ↥(LinearMap.ker E₀ ⊓ H) ≃ₗ[𝕜] ↥(LinearMap.ker E₁ ⊓ H) where
  toFun v := ⟨holeCorrection W E₁ L₁ v,
    holeCorrection_mem_kernel W E₁ L₁ hL₁ v,
    holeCorrection_mem_submodule W H hWH E₁ L₁ v.property.2⟩
  invFun v := ⟨holeCorrection W E₀ L₀ v,
    holeCorrection_mem_kernel W E₀ L₀ hL₀ v,
    holeCorrection_mem_submodule W H hWH E₀ L₀ v.property.2⟩
  left_inv v := by
    apply Subtype.ext
    change holeCorrection W E₀ L₀ (holeCorrection W E₁ L₁ v) = v
    rw [holeCorrection_comp W E₀ E₁ L₀ L₁ hL₀]
    exact holeCorrection_fixed W E₀ L₀ v.property.1
  right_inv v := by
    apply Subtype.ext
    change holeCorrection W E₁ L₁ (holeCorrection W E₀ L₀ v) = v
    rw [holeCorrection_comp W E₁ E₀ L₁ L₀ hL₁]
    exact holeCorrection_fixed W E₁ L₁ v.property.1
  map_add' v w := Subtype.ext ((holeCorrection W E₁ L₁).map_add v w)
  map_smul' c v := Subtype.ext ((holeCorrection W E₁ L₁).map_smul c v)

/-- Both exchanged native kernels have exactly the same cardinal rank. -/
theorem holeExchange_rank (W H : Submodule 𝕜 V) (hWH : W ≤ H)
    (E₀ E₁ : V →ₗ[𝕜] U) (L₀ L₁ : W ≃ₗ[𝕜] U)
    (hL₀ : ∀ w : W, E₀ w = L₀ w) (hL₁ : ∀ w : W, E₁ w = L₁ w) :
    Module.rank 𝕜 ↥(LinearMap.ker E₀ ⊓ H) = Module.rank 𝕜 ↥(LinearMap.ker E₁ ⊓ H) :=
  (holeExchangeEquiv W H hWH E₀ E₁ L₀ L₁ hL₀ hL₁).rank_eq

/-- Finite dimension transports before any finrank interpretation is used. -/
theorem holeExchange_finiteDimensional (W H : Submodule 𝕜 V) (hWH : W ≤ H)
    (E₀ E₁ : V →ₗ[𝕜] U) (L₀ L₁ : W ≃ₗ[𝕜] U)
    (hL₀ : ∀ w : W, E₀ w = L₀ w) (hL₁ : ∀ w : W, E₁ w = L₁ w)
    [FiniteDimensional 𝕜 ↥(LinearMap.ker E₀ ⊓ H)] :
    FiniteDimensional 𝕜 ↥(LinearMap.ker E₁ ⊓ H) :=
  (holeExchangeEquiv W H hWH E₀ E₁ L₀ L₁ hL₀ hL₁).finiteDimensional

end

section NormBounds

variable {κ X Y : Type*} [NontriviallyNormedField κ] [NormedAddCommGroup X] [NormedSpace κ X]
  [NormedAddCommGroup Y] [NormedSpace κ Y]

/-- The continuous correction after the actual observation and repair maps
have been constructed. No bound uniform in head size is asserted. -/
def continuousHoleCorrection (E : X →L[κ] Y) (repair : Y →L[κ] X) : X →L[κ] X :=
  ContinuousLinearMap.id κ X - repair.comp E

/-- The original-norm correction estimate with both actual operator norms retained. -/
theorem continuousHoleCorrection_norm_le (E : X →L[κ] Y) (repair : Y →L[κ] X)
    (x : X) :
    ‖continuousHoleCorrection E repair x‖ ≤ (1 + ‖repair‖ * ‖E‖) * ‖x‖ := by
  calc
    ‖continuousHoleCorrection E repair x‖ = ‖x - repair (E x)‖ := rfl
    _ ≤ ‖x‖ + ‖repair (E x)‖ := norm_sub_le _ _
    _ ≤ ‖x‖ + ‖repair‖ * (‖E‖ * ‖x‖) :=
      add_le_add le_rfl ((repair.le_opNorm _).trans
        (mul_le_mul_of_nonneg_left (E.le_opNorm _) (norm_nonneg _)))
    _ = (1 + ‖repair‖ * ‖E‖) * ‖x‖ := by ring

end NormBounds

end MeyerGeneralProblem.Adaptive
