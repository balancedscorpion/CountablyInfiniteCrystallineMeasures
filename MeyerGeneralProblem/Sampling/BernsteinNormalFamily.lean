module

public import MeyerGeneralProblem.Sampling.BernsteinGrowth
public import Mathlib.Analysis.Complex.LocallyUniformLimit
import all Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import all Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import TauCeti.Analysis.Complex.Conformal.Montel.Basic
import all TauCeti.Analysis.Complex.Conformal.Montel.Basic

@[expose] public section

/-!
# Normal families of entire functions with a common real-axis bound

The common compact bounds are derived from radial exponential type using the
sharp Phragmen–Lindelöf estimate. The radial-growth constants need not be uniform
over the family. Montel extraction preserves a positive value at the origin,
and all complex derivatives converge locally uniformly along the same subsequence.
-/

noncomputable section

open Set Filter Complex
open scoped Topology

namespace MeyerGeneralProblem

/-- Locally uniform convergence of entire functions gives locally uniform
convergence of every complex derivative along the original sequence. -/
theorem tendstoLocallyUniformlyOn_iteratedDeriv_of_entire
    {F : ℕ → ℂ → ℂ} {G : ℂ → ℂ}
    (hF : ∀ n, Differentiable ℂ (F n))
    (hconv : TendstoLocallyUniformlyOn F G atTop univ) (k : ℕ) :
    TendstoLocallyUniformlyOn (fun n => iteratedDeriv k (F n))
      (iteratedDeriv k G) atTop univ := by
  induction k with
  | zero => simpa only [iteratedDeriv_zero] using hconv
  | succ k ih =>
    have hdiff : ∀ᶠ n in atTop, DifferentiableOn ℂ (iteratedDeriv k (F n)) univ :=
      Eventually.of_forall fun n =>
        ((hF n).contDiff.differentiable_iteratedDeriv' k).differentiableOn
    simpa only [iteratedDeriv_succ, Function.comp_def] using ih.deriv hdiff isOpen_univ

/-- A family with common radial exponential type and a common real-axis bound
is bounded on every compact subset of the complex plane. -/
theorem isLocallyBoundedOn_of_entire_exponentialType
    {F : ℕ → ℂ → ℂ} {τ M : ℝ}
    (hF : ∀ n, Differentiable ℂ (F n)) (hτ : 0 ≤ τ) (hM : 0 ≤ M)
    (htype : ∀ n, ∀ ε > 0, ∃ C > 0, ∀ z,
      ‖F n z‖ ≤ C * Real.exp ((τ + ε) * ‖z‖))
    (hreal : ∀ n, ∀ x : ℝ, ‖F n x‖ ≤ M) :
    TauCeti.IsLocallyBoundedOn F univ := by
  rw [TauCeti.isLocallyBoundedOn_def]
  intro K _ hK
  have hcontinuous : Continuous (fun z : ℂ => M * Real.exp (τ * |z.im|)) := by
    fun_prop
  obtain ⟨C, hC⟩ := (hK.image hcontinuous).bddAbove
  exact ⟨C, fun n z hz =>
    (norm_entire_le_exp_abs_im (hF n) hτ hM (htype n) (hreal n) z).trans
      (hC (mem_image_of_mem _ hz))⟩

/-- A bounded-real-axis family of common exponential type has an entire locally
uniform subsequential limit. A positive lower bound at zero survives, as do the
sharp vertical bound and convergence of every complex derivative. -/
theorem exists_bernstein_subsequence
    {F : ℕ → ℂ → ℂ} {τ M δ : ℝ}
    (hF : ∀ n, Differentiable ℂ (F n)) (hτ : 0 ≤ τ) (hM : 0 ≤ M) (hδ : 0 < δ)
    (htype : ∀ n, ∀ ε > 0, ∃ C > 0, ∀ z,
      ‖F n z‖ ≤ C * Real.exp ((τ + ε) * ‖z‖))
    (hreal : ∀ n, ∀ x : ℝ, ‖F n x‖ ≤ M)
    (horigin : ∀ n, δ ≤ ‖F n 0‖) :
    ∃ (φ : ℕ → ℕ) (G : ℂ → ℂ), StrictMono φ ∧ Differentiable ℂ G ∧
      TendstoLocallyUniformlyOn (fun n => F (φ n)) G atTop univ ∧
      (∀ z, ‖G z‖ ≤ M * Real.exp (τ * |z.im|)) ∧
      δ ≤ ‖G 0‖ ∧ G 0 ≠ 0 ∧
      (∀ k : ℕ, TendstoLocallyUniformlyOn (fun n => iteratedDeriv k (F (φ n)))
        (iteratedDeriv k G) atTop univ) := by
  obtain ⟨φ, G, hφ, hG, hconv⟩ := TauCeti.montel isOpen_univ
    (fun n => (hF n).differentiableOn)
    (isLocallyBoundedOn_of_entire_exponentialType hF hτ hM htype hreal)
  have horigin' : δ ≤ ‖G 0‖ :=
    ge_of_tendsto (hconv.tendsto_at (mem_univ 0)).norm
      (Eventually.of_forall fun n => horigin (φ n))
  refine ⟨φ, G, hφ, differentiableOn_univ.mp hG, hconv, ?_, horigin', ?_, ?_⟩
  · intro z
    exact le_of_tendsto (hconv.tendsto_at (mem_univ z)).norm
      (Eventually.of_forall fun n =>
        norm_entire_le_exp_abs_im (hF (φ n)) hτ hM (htype (φ n)) (hreal (φ n)) z)
  · exact norm_pos_iff.mp (hδ.trans_le horigin')
  · exact tendstoLocallyUniformlyOn_iteratedDeriv_of_entire (fun n => hF (φ n)) hconv

/-- Unit real-axis normalization and a half-unit lower bound at zero produce a
nonzero entire limit, with all derivative limits on the same subsequence. -/
theorem exists_normalized_bernstein_subsequence
    {F : ℕ → ℂ → ℂ} {τ : ℝ}
    (hF : ∀ n, Differentiable ℂ (F n)) (hτ : 0 ≤ τ)
    (htype : ∀ n, ∀ ε > 0, ∃ C > 0, ∀ z,
      ‖F n z‖ ≤ C * Real.exp ((τ + ε) * ‖z‖))
    (hreal : ∀ n, ∀ x : ℝ, ‖F n x‖ ≤ 1)
    (horigin : ∀ n, (1 / 2 : ℝ) ≤ ‖F n 0‖) :
    ∃ (φ : ℕ → ℕ) (G : ℂ → ℂ), StrictMono φ ∧ Differentiable ℂ G ∧
      TendstoLocallyUniformlyOn (fun n => F (φ n)) G atTop univ ∧
      (∀ z, ‖G z‖ ≤ Real.exp (τ * |z.im|)) ∧
      (1 / 2 : ℝ) ≤ ‖G 0‖ ∧ G 0 ≠ 0 ∧
      (∀ k : ℕ, TendstoLocallyUniformlyOn (fun n => iteratedDeriv k (F (φ n)))
        (iteratedDeriv k G) atTop univ) := by
  simpa only [one_mul] using
    exists_bernstein_subsequence hF hτ (by norm_num : (0 : ℝ) ≤ 1)
      (by norm_num : (0 : ℝ) < 1 / 2) htype hreal horigin

end MeyerGeneralProblem
