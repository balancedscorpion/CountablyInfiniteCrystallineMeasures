module

public import MeyerGeneralProblem.Distribution.SchwartzVanishing
public import Mathlib.Analysis.Distribution.TemperedDistribution
import all Mathlib.Analysis.Distribution.TemperedDistribution
public import Mathlib.Analysis.LocallyConvex.Separation
import all Mathlib.Analysis.LocallyConvex.Separation

@[expose] public section

/-!
# Continuous annihilators of submodules

This file gives the carrier-agnostic functional-analytic step used by the
Schwartz-defect argument.  A complex submodule of a locally convex space has
a nonzero continuous annihilator exactly when its topological closure is
proper.  The reverse implication is complex geometric Hahn--Banach.
-/

open scoped SchwartzMap

namespace MeyerGeneralProblem

noncomputable section

/-- Continuous complex-linear functionals, equipped with pointwise
convergence, which vanish on a submodule. -/
def continuousAnnihilator {E : Type*} [TopologicalSpace E] [AddCommGroup E]
    [Module ℂ E] (W : Submodule ℂ E) : Submodule ℂ (E →Lₚₜ[ℂ] ℂ) where
  carrier := {T | ∀ x ∈ W, T x = 0}
  zero_mem' := by
    intro x hx
    simp
  add_mem' := by
    intro T U hT hU x hx
    simp [hT x hx, hU x hx]
  smul_mem' := by
    intro c T hT x hx
    simp [hT x hx]

@[simp]
theorem mem_continuousAnnihilator_iff
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℂ E]
    (W : Submodule ℂ E) (T : E →Lₚₜ[ℂ] ℂ) :
    T ∈ continuousAnnihilator W ↔ ∀ x ∈ W, T x = 0 :=
  Iff.rfl

def pointwiseFunctionalAsStrongDual
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℂ E]
    (T : E →Lₚₜ[ℂ] ℂ) : StrongDual ℂ E :=
  (UniformConvergenceCLM.ofFun (RingHom.id ℂ) ℂ
    {s : Set E | s.Finite}).symm T

@[simp]
private theorem pointwiseFunctionalAsStrongDual_apply
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℂ E]
    (T : E →Lₚₜ[ℂ] ℂ) (x : E) :
    pointwiseFunctionalAsStrongDual T x = T x :=
  rfl

private theorem strongDual_eq_zero_on_submodule_of_re_bounded
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℂ E]
    (W : Submodule ℂ E) (f : StrongDual ℂ E) (u : ℝ)
    (hf : ∀ x ∈ W, (f x).re < u) :
    ∀ x ∈ W, f x = 0 := by
  intro x hx
  have real_eq_zero : ∀ y ∈ W, (f y).re = 0 := by
    intro y hy
    by_contra hne
    let c : ℝ := (u + 1) / (f y).re
    have hc := hf ((c : ℂ) • y) (W.smul_mem (c : ℂ) hy)
    rw [map_smul] at hc
    simp only [smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero] at hc
    change (u + 1) / (f y).re * (f y).re < u at hc
    rw [div_mul_cancel₀ _ hne] at hc
    linarith
  have hre : (f x).re = 0 := real_eq_zero x hx
  have hI : (f (Complex.I • x)).re = 0 :=
    real_eq_zero (Complex.I • x) (W.smul_mem Complex.I hx)
  rw [map_smul] at hI
  simp only [smul_eq_mul, Complex.I_mul_re] at hI
  exact Complex.ext hre (neg_eq_zero.mp hI)

/-- A complex submodule of a locally convex space has a nonzero continuous
annihilator if and only if its topological closure is proper. -/
theorem continuousAnnihilator_ne_bot_iff_topologicalClosure_ne_top
    {E : Type*} [TopologicalSpace E] [AddCommGroup E]
    [Module ℝ E] [Module ℂ E] [IsScalarTower ℝ ℂ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [ContinuousSMul ℂ E]
    [LocallyConvexSpace ℝ E] (W : Submodule ℂ E) :
    continuousAnnihilator W ≠ ⊥ ↔ W.topologicalClosure ≠ ⊤ := by
  constructor
  · intro hAnn hClosure
    obtain ⟨T, hT, hTne⟩ :=
      (Submodule.ne_bot_iff (continuousAnnihilator W)).mp hAnn
    apply hTne
    apply UniformConvergenceCLM.ext
    intro x
    let f : StrongDual ℂ E := pointwiseFunctionalAsStrongDual T
    have hWker : W ≤ f.ker := by
      intro y hy
      change f y = 0
      rw [pointwiseFunctionalAsStrongDual_apply]
      exact hT y hy
    have hClosureKer : W.topologicalClosure ≤ f.ker :=
      W.topologicalClosure_minimal hWker f.isClosed_ker
    have hker : f.ker = ⊤ := by
      apply top_unique
      rw [← hClosure]
      exact hClosureKer
    have hf : f.toLinearMap = 0 := LinearMap.ker_eq_top.mp hker
    have hx : f x = 0 := by
      change f.toLinearMap x = 0
      rw [hf]
      rfl
    simpa [f] using hx
  · intro hClosure
    obtain ⟨x, -, hx⟩ :=
      SetLike.exists_of_lt ((lt_top_iff_ne_top).2 hClosure)
    have hconvex : Convex ℝ (W.topologicalClosure : Set E) := by
      change Convex ℝ (closure (W : Set E))
      exact (W.restrictScalars ℝ).convex.closure
    obtain ⟨f, u, hf, hfx⟩ :=
      RCLike.geometric_hahn_banach_closed_point (𝕜 := ℂ)
        hconvex W.isClosed_topologicalClosure hx
    let T : E →Lₚₜ[ℂ] ℂ :=
      ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) E ℂ f
    refine (Submodule.ne_bot_iff (continuousAnnihilator W)).2 ⟨T, ?_, ?_⟩
    · intro y hy
      change f y = 0
      exact strongDual_eq_zero_on_submodule_of_re_bounded
        W.topologicalClosure f u hf y (W.le_topologicalClosure hy)
    · intro hT
      have hxzero : RCLike.re (f x) = 0 := by
        have h := congrArg (fun A : E →Lₚₜ[ℂ] ℂ => (A x).re) hT
        change RCLike.re (f x) = 0 at h
        exact h
      have hzero := hf 0 W.topologicalClosure.zero_mem
      rw [hxzero] at hfx
      simp only [map_zero] at hzero hfx
      linarith

/-- The continuous annihilator of a Schwartz submodule, regarded as a
submodule of complex tempered distributions. -/
def schwartzAnnihilator (W : Submodule ℂ (SchwartzMap ℝ ℂ)) :
    Submodule ℂ (TemperedDistribution ℝ ℂ) :=
  continuousAnnihilator W

@[simp]
theorem mem_schwartzAnnihilator_iff
    (W : Submodule ℂ (SchwartzMap ℝ ℂ))
    (T : TemperedDistribution ℝ ℂ) :
    T ∈ schwartzAnnihilator W ↔ ∀ f ∈ W, T f = 0 :=
  Iff.rfl

/-- Schwartz specialization of the closed-submodule annihilator theorem. -/
theorem schwartzAnnihilator_ne_bot_iff_topologicalClosure_ne_top
    (W : Submodule ℂ (SchwartzMap ℝ ℂ)) :
    schwartzAnnihilator W ≠ ⊥ ↔ W.topologicalClosure ≠ ⊤ :=
  continuousAnnihilator_ne_bot_iff_topologicalClosure_ne_top W

end

end MeyerGeneralProblem
