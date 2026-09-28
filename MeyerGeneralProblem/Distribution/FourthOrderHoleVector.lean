module

public import Mathlib.Analysis.Fourier.ZMod
import all Mathlib.Analysis.Fourier.ZMod
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import all Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Constructions
import all Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Tactic
import all Mathlib.Tactic

@[expose] public section

/-!
# Fourth-order finite Fourier components with prescribed zero coordinates

Four elementary components of an operator whose fourth power is identity
span every vector. A single finite orbit-constraint map then produces a
nonzero eigenvector satisfying fewer than one quarter as many coordinate
constraints as the ambient dimension. No eigenspace multiplicity is assumed.
-/

namespace MeyerGeneralProblem

noncomputable section

open scoped BigOperators

/-- The four complex fourth roots, indexed without any multiplicity formula. -/
def fourthRootValue : Fin 4 → ℂ := ![1, -1, Complex.I, -Complex.I]

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Four times the corresponding fourth-root spectral component.
The explicit finite formula avoids any assumed diagonalization. -/
def fourthRootComponent (U : Module.End ℂ V) : Fin 4 → Module.End ℂ V :=
  ![1 + U + U^2 + U^3,
    1 - U + U^2 - U^3,
    1 - Complex.I • U - U^2 + Complex.I • U^3,
    1 + Complex.I • U - U^2 - Complex.I • U^3]

/-- Each explicitly listed fourth root has fourth power one. -/
theorem fourthRootValue_pow_four (a : Fin 4) : fourthRootValue a ^ 4 = 1 := by
  fin_cases a <;> norm_num [fourthRootValue, Complex.I_sq]

/-- Every listed Fourier eigenvalue has unit complex norm. -/
theorem norm_fourthRootValue (a : Fin 4) : ‖fourthRootValue a‖ = 1 := by
  fin_cases a <;> norm_num [fourthRootValue]

/-- The four finite components sum to four times the original vector. -/
theorem sum_fourthRootComponent (U : Module.End ℂ V) (v : V) :
    ∑ a : Fin 4, fourthRootComponent U a v = (4:ℂ) • v := by
  simp [Fin.sum_univ_four, fourthRootComponent]
  module

/-- Under the actual fourth-power identity, every explicit component is
an eigenvector (possibly zero) with its named fourth root. -/
theorem fourthRootComponent_eigen (U : Module.End ℂ V) (hU : U^4 = 1)
    (a : Fin 4) (v : V) :
    U (fourthRootComponent U a v) = fourthRootValue a • fourthRootComponent U a v := by
  have hfour : U (U (U (U v))) = v := by
    have h := congrArg (fun A : Module.End ℂ V => A v) hU
    simpa only [pow_succ, pow_zero, Module.End.mul_apply, Module.End.one_apply] using h
  fin_cases a <;> dsimp [fourthRootComponent, fourthRootValue]
  all_goals simp [pow_succ, Module.End.mul_apply, map_smul, hfour,
    smul_add, smul_sub, smul_smul]
  all_goals module


/-- Record the prescribed coordinates of four consecutive orbit vectors. -/
def fourthOrbitConstraint {q : ℕ} (U : Module.End ℂ V)
    (L : V →ₗ[ℂ] (Fin q → ℂ)) : V →ₗ[ℂ] (Fin 4 → Fin q → ℂ) :=
  LinearMap.pi (fun a : Fin 4 => L.comp (U ^ a.val))

/-- Vanishing prescribed coordinates on the first four orbit vectors
passes to every actual fourth-root component. -/
theorem fourthRootComponent_constraint_zero {q : ℕ} (U : Module.End ℂ V)
    (L : V →ₗ[ℂ] (Fin q → ℂ)) (v : V)
    (hv : ∀ a : Fin 4, L ((U^a.val) v) = 0) (a : Fin 4) :
    L (fourthRootComponent U a v) = 0 := by
  have h0 : L v = 0 := by simpa using hv 0
  have h1 : L (U v) = 0 := by simpa using hv 1
  have h2 : L ((U^2) v) = 0 := hv 2
  have h3 : L ((U^3) v) = 0 := hv 3
  fin_cases a <;> simp [fourthRootComponent, map_smul, h0, h1, h2, h3]

/-- A nonzero vector has a nonzero explicit fourth-root component. -/
theorem exists_fourthRootComponent_ne_zero (U : Module.End ℂ V) {v : V} (hv : v ≠ 0) :
    ∃ a : Fin 4, fourthRootComponent U a v ≠ 0 := by
  by_contra h
  push Not at h
  have hs := sum_fourthRootComponent U v
  simp only [h, Finset.sum_const_zero] at hs
  exact (smul_ne_zero (by norm_num : (4:ℂ) ≠ 0) hv) hs.symm

/-- Fewer than one quarter as many coordinate constraints as the actual
ambient dimension allow a nonzero fourth-root eigenvector satisfying them.
The eigenspace size is derived by finite orbit constraints, not assumed. -/
theorem exists_fourthRoot_eigenvector_constraint_zero [FiniteDimensional ℂ V]
    (U : Module.End ℂ V) (hU : U^4 = 1) {q : ℕ}
    (L : V →ₗ[ℂ] (Fin q → ℂ)) (hq : 4*q < Module.finrank ℂ V) :
    ∃ (a : Fin 4) (v : V), v ≠ 0 ∧ U v = fourthRootValue a • v ∧ L v = 0 := by
  have hdim : Module.finrank ℂ (Fin 4 → Fin q → ℂ) < Module.finrank ℂ V := by
    simpa [Module.finrank_pi_fintype, Module.finrank_fintype_fun_eq_card] using hq
  obtain ⟨v,hvK,hv⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (LinearMap.ker_ne_bot_of_finrank_lt (f := fourthOrbitConstraint U L) hdim)
  have hvanish (a : Fin 4) : L ((U^a.val) v) = 0 := by
    exact congrFun (show fourthOrbitConstraint U L v = 0 from hvK) a
  obtain ⟨a,ha⟩ := exists_fourthRootComponent_ne_zero U hv
  exact ⟨a,fourthRootComponent U a v,ha,fourthRootComponent_eigen U hU a v,
    fourthRootComponent_constraint_zero U L v hvanish a⟩

end

end MeyerGeneralProblem
