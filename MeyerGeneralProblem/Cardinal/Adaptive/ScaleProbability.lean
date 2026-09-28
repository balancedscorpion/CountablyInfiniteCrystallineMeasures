module

public import MeyerGeneralProblem.Cardinal.Adaptive.Definitions
public import Mathlib.Probability.Independence.InfinitePi
import all Mathlib.Probability.Independence.InfinitePi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import all Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section

/-!
# The actual countable product of uniform reciprocal scale choices

Each coordinate has Lebesgue measure restricted to the interval [1,2],
whose length is exactly one. The scale law is an actual probability measure
on the complete sequence space; no good-event independence is assumed.
-/

namespace MeyerGeneralProblem.Adaptive

noncomputable section

open MeasureTheory Set Filter
open ProbabilityTheory

/-- The uniform probability law on the actual scale interval of length one. -/
def scaleLaw : Measure ℝ := volume.restrict (Icc 1 2)

instance scaleLaw_isProbabilityMeasure : IsProbabilityMeasure scaleLaw where
  measure_univ := by norm_num [scaleLaw]

instance scaleLaw_nullSingletonClass : NullSingletonClass scaleLaw := by
  unfold scaleLaw
  infer_instance

/-- Genuine infinite product probability on all positive-index scale sequences. -/
def scaleProbability : Measure (ℕ+ → ℝ) :=
  Measure.infinitePi (fun _ : ℕ+ => scaleLaw)

instance scaleProbability_isProbabilityMeasure : IsProbabilityMeasure scaleProbability := by
  unfold scaleProbability
  infer_instance

/-- Every coordinate has exactly the prescribed uniform law. -/
theorem scaleProbability_map_eval (i : ℕ+) :
    scaleProbability.map (fun s => s i) = scaleLaw :=
  Measure.infinitePi_map_eval (fun _ : ℕ+ => scaleLaw) i

/-- The complete coordinate family is independent under the genuine product measure. -/
theorem scaleProbability_iIndepFun : iIndepFun (fun i (s : ℕ+ → ℝ) => s i) scaleProbability :=
  iIndepFun_infinitePi (X := fun _ x => x) (by fun_prop)

/-- Distinct coordinate pairs have the genuine two-dimensional product law. -/
theorem scaleProbability_map_eval_pair {i j : ℕ+} (hij : i ≠ j) :
    scaleProbability.map (fun s => (s i, s j)) = scaleLaw.prod scaleLaw :=
  Measure.infinitePi_map_eval_prod hij

/-- Transfer any one-coordinate almost-everywhere fact through its exact marginal. -/
theorem ae_scale_coordinate (i : ℕ+) {p : ℝ → Prop}
    (hp : ∀ᵐ x ∂scaleLaw, p x) : ∀ᵐ s ∂scaleProbability, p (s i) := by
  apply ae_of_ae_map (measurable_pi_apply i).aemeasurable
  rwa [scaleProbability_map_eval]

/-- Almost every full sequence lies in the interval at every coordinate simultaneously. -/
theorem ae_all_scales_mem : ∀ᵐ s ∂scaleProbability, ∀ i, s i ∈ Icc (1 : ℝ) 2 := by
  apply ae_all_iff.mpr
  intro i
  exact ae_scale_coordinate i (ae_restrict_mem measurableSet_Icc)

/-- Countable one-coordinate exclusions lift to null events in the whole sequence space. -/
theorem ae_scale_coordinate_not_mem (i : ℕ+) {A : Set ℝ} (hA : A.Countable) :
    ∀ᵐ s ∂scaleProbability, s i ∉ A := by
  refine ae_scale_coordinate i (p := fun x => x ∉ A) ?_
  rw [ae_iff]
  simpa using hA.measure_zero scaleLaw

/-- The literal forward/reciprocal scalar operation at one coordinate. -/
def scaleFactor : ReciprocalSign → ℝ → ℝ
  | .forward, x => x
  | .reciprocal, x => x⁻¹

/-- This auxiliary scalar operation is exactly the existing label-scale formula. -/
theorem labelScale_eq_scaleFactor (s : ℕ+ → ℝ) (b : Label) :
    labelScale s b = scaleFactor b.2 (s b.1) := by
  rcases b with ⟨i, σ⟩
  cases σ <;> rfl

/-- Both reciprocal scalar operations are measurable on the full real line. -/
theorem measurable_scaleFactor (σ : ReciprocalSign) : Measurable (scaleFactor σ) := by
  cases σ with
  | forward => exact measurable_id
  | reciprocal => exact measurable_inv

/-- Inversion, including Lean's value at zero, is an injective scalar operation. -/
theorem scaleFactor_injective (σ : ReciprocalSign) : Function.Injective (scaleFactor σ) := by
  cases σ with
  | forward => exact Function.injective_id
  | reciprocal => exact inv_injective

/-- A nonzero atom remains an injective observation of one reciprocal scale. -/
theorem scaleFactor_mul_injective (σ : ReciprocalSign) {a : ℝ} (ha : a ≠ 0) :
    Function.Injective (fun x => scaleFactor σ x * a) := by
  intro x y h
  exact scaleFactor_injective σ (mul_right_cancel₀ ha h)

end
end MeyerGeneralProblem.Adaptive
