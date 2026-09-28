module

public import MeyerGeneralProblem.Sampling.BeurlingSmoothing
public import Mathlib.Analysis.Calculus.ParametricIntegral
import all Mathlib.Analysis.Calculus.ParametricIntegral

@[expose] public section

/-!
# Entire narrow-band localizers with derivative decay

The complex Fourier integral of an actual compact Schwartz bump is entire.
Its support bounds its exponential type, while its real restriction is the
Schwartz Fourier transform. This constructs the localizer used in the
grouped Bernstein-to-Paley–Wiener localization, without postulating a kernel.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology SchwartzMap FourierTransform

namespace MeyerGeneralProblem

/-- The actual complex extension of the negative-`2π` Fourier integral. -/
def complexFourierExtension (G : SchwartzMap ℝ ℂ) (z : ℂ) : ℂ :=
  ∫ t : ℝ, Complex.exp (((-2 * Real.pi * t : ℝ) : ℂ) * Complex.I * z) * G t

private theorem norm_complexFourierPhase_le {r : ℝ} (_hr : 0 ≤ r)
    {t : ℝ} (ht : |t| ≤ r) (z : ℂ) :
    ‖Complex.exp (((-2 * Real.pi * t : ℝ) : ℂ) * Complex.I * z)‖ ≤
      Real.exp (2 * Real.pi * r * ‖z‖) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ ‖(((-2 * Real.pi * t : ℝ) : ℂ) * Complex.I * z)‖ := Complex.re_le_norm _
    _ = 2 * Real.pi * |t| * ‖z‖ := by
      simp [abs_of_pos Real.pi_pos]
    _ ≤ _ := by gcongr

private theorem integrable_complexFourierExtension_integrand
    (G : SchwartzMap ℝ ℂ) {r : ℝ}
    (hs : Function.support G ⊆ Icc (-r) r) (z : ℂ) :
    Integrable (fun t : ℝ =>
      Complex.exp (((-2 * Real.pi * t : ℝ) : ℂ) * Complex.I * z) * G t) := by
  have hc : HasCompactSupport (G : ℝ → ℂ) :=
    HasCompactSupport.intro isCompact_Icc (fun t ht =>
      not_not.mp (fun hn => ht (hs hn)))
  exact (show Continuous (fun t : ℝ =>
    Complex.exp (((-2 * Real.pi * t : ℝ) : ℂ) * Complex.I * z) * G t) by
      fun_prop).integrable_of_hasCompactSupport hc.mul_left

/-- Compact frequency support gives the exact radial exponential bound for
the genuine complex integral, with the actual `L¹` mass as constant. -/
theorem norm_complexFourierExtension_le
    (G : SchwartzMap ℝ ℂ) {r : ℝ} (hr : 0 ≤ r)
    (hs : Function.support G ⊆ Icc (-r) r) (z : ℂ) :
    ‖complexFourierExtension G z‖ ≤
      (∫ t : ℝ, ‖G t‖) * Real.exp (2 * Real.pi * r * ‖z‖) := by
  unfold complexFourierExtension
  calc
    _ ≤ ∫ t : ℝ, ‖Complex.exp (((-2 * Real.pi * t : ℝ) : ℂ) *
        Complex.I * z) * G t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ, Real.exp (2 * Real.pi * r * ‖z‖) * ‖G t‖ := by
      apply integral_mono (integrable_complexFourierExtension_integrand G hs z).norm
        (G.integrable.norm.const_mul _)
      intro t
      dsimp only
      rw [norm_mul]
      by_cases ht : G t = 0
      · simp [ht]
      · exact mul_le_mul_of_nonneg_right
          (norm_complexFourierPhase_le hr (abs_le.mpr (hs ht)) z) (norm_nonneg _)
    _ = _ := by rw [integral_const_mul, mul_comm]

/-- Differentiation under the compact-frequency integral proves genuine
complex differentiability at every point. -/
theorem differentiable_complexFourierExtension
    (G : SchwartzMap ℝ ℂ) {r : ℝ} (hr : 0 ≤ r)
    (hs : Function.support G ⊆ Icc (-r) r) :
    Differentiable ℂ (complexFourierExtension G) := by
  intro z
  let a : ℝ → ℂ := fun t => ((-2 * Real.pi * t : ℝ) : ℂ) * Complex.I
  let F : ℂ → ℝ → ℂ := fun w t => Complex.exp (a t * w) * G t
  let F' : ℂ → ℝ → ℂ := fun w t => (Complex.exp (a t * w) * a t) * G t
  let B := 2 * Real.pi * r * Real.exp (2 * Real.pi * r * (‖z‖ + 1))
  have hc : HasCompactSupport (G : ℝ → ℂ) :=
    HasCompactSupport.intro isCompact_Icc (fun t ht =>
      not_not.mp (fun hn => ht (hs hn)))
  have hFcont (w : ℂ) : Continuous (F w) := by dsimp [F, a]; fun_prop
  have hF'cont (w : ℂ) : Continuous (F' w) := by dsimp [F', a]; fun_prop
  have hdiff : ∀ t w, HasDerivAt (fun u => F u t) (F' w t) w := by
    intro t w
    simpa only [F, F', mul_one, id_eq] using
      (((hasDerivAt_id w).const_mul (a t)).cexp.mul_const (G t))
  have hbound : ∀ᵐ t : ℝ, ∀ w ∈ Metric.ball z 1, ‖F' w t‖ ≤ B * ‖G t‖ := by
    filter_upwards [] with t w hw
    by_cases ht : G t = 0
    · simp [F', ht]
    have ht' : |t| ≤ r := abs_le.mpr (hs ht)
    have hw' : ‖w‖ ≤ ‖z‖ + 1 := by
      have htriangle := norm_le_norm_sub_add w z
      have hball : ‖w - z‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using hw
      linarith
    have ha : ‖a t‖ ≤ 2 * Real.pi * r := by
      dsimp [a]
      norm_num [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
      gcongr
    have he := norm_complexFourierPhase_le hr ht' w
    change ‖Complex.exp (a t * w)‖ ≤ _ at he
    have he' : ‖Complex.exp (a t * w)‖ ≤
        Real.exp (2 * Real.pi * r * (‖z‖ + 1)) := he.trans (by gcongr)
    simp only [F', norm_mul]
    calc
      _ ≤ (Real.exp (2 * Real.pi * r * (‖z‖ + 1)) *
          (2 * Real.pi * r)) * ‖G t‖ := by gcongr
      _ = _ := by dsimp [B]; ring
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := fun t => B * ‖G t‖)
    (Metric.ball_mem_nhds z zero_lt_one)
    (Eventually.of_forall fun w => (hFcont w).aestronglyMeasurable)
    (integrable_complexFourierExtension_integrand G hs z)
    (hF'cont z).aestronglyMeasurable hbound (G.integrable.norm.const_mul B)
    (Eventually.of_forall fun t w _ => hdiff t w)
  exact h.2.differentiableAt

/-- On the real axis the complex extension is exactly the Schwartz Fourier
transform, with the repository's negative-frequency sign convention. -/
theorem complexFourierExtension_ofReal (G : SchwartzMap ℝ ℂ) (x : ℝ) :
    complexFourierExtension G (x : ℂ) = (𝓕 G) x := by
  rw [complexFourierExtension]
  change _ = FourierTransform.fourier (G : ℝ → ℂ) x
  rw [fourier_eq_integral_gramPhase]
  apply integral_congr_ae
  filter_upwards [] with t
  congr 2
  push_cast
  ring

/-- Every Schwartz function has a single quadratic-decay constant controlling
all real derivatives through any prescribed finite order. -/
theorem exists_schwartz_uniform_quadratic_derivative_bound
    (K : SchwartzMap ℝ ℂ) (q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ j ≤ q, ∀ t : ℝ,
      ‖iteratedDeriv j (K : ℝ → ℂ) t‖ ≤ C / (1 + |t|) ^ 2 := by
  let b : Fin (q + 1) → ℝ := fun j =>
    2 * (|SchwartzMap.seminorm ℂ 0 j K| + |SchwartzMap.seminorm ℂ 2 j K|)
  let C := 1 + ∑ j, b j
  have hb (j) : 0 ≤ b j := by dsimp [b]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro j hj t
  let jj : Fin (q + 1) := ⟨j, by omega⟩
  have hzero : ‖iteratedDeriv j (K : ℝ → ℂ) t‖ ≤
      |SchwartzMap.seminorm ℂ 0 j K| := by
    have h := SchwartzMap.le_seminorm' ℂ 0 j K t
    simp only [pow_zero, one_mul] at h
    exact h.trans (le_abs_self _)
  have htwo : |t| ^ 2 * ‖iteratedDeriv j (K : ℝ → ℂ) t‖ ≤
      |SchwartzMap.seminorm ℂ 2 j K| :=
    (SchwartzMap.le_seminorm' ℂ 2 j K t).trans (le_abs_self _)
  have hweight : (1 + |t|) ^ 2 ≤ 2 * (1 + |t| ^ 2) := by
    nlinarith [sq_nonneg (|t| - 1)]
  have hlocal : ‖iteratedDeriv j (K : ℝ → ℂ) t‖ * (1 + |t|) ^ 2 ≤ b jj := by
    have hmul := mul_le_mul_of_nonneg_right hweight
      (norm_nonneg (iteratedDeriv j (K : ℝ → ℂ) t))
    dsimp [b, jj]
    nlinarith
  have hsingle : b jj ≤ ∑ k, b k :=
    Finset.single_le_sum (fun k _ => hb k) (Finset.mem_univ jj)
  apply (le_div_iff₀ (by positivity : 0 < (1 + |t|) ^ 2)).mpr
  exact hlocal.trans (hsingle.trans (by dsimp [C]; linarith))

/-- Every positive angular bandwidth has an actual normalized entire
localizer whose real restriction is Schwartz. One kernel works at all finite
derivative orders, with a uniform quadratic-decay constant at each order. -/
theorem exists_entire_schwartz_localizer {α : ℝ} (hα : 0 < α) :
    ∃ K : SchwartzMap ℝ ℂ, ∃ E : ℂ → ℂ,
      Differentiable ℂ E ∧
      (∀ t : ℝ, E (t : ℂ) = K t) ∧ K 0 = 1 ∧
      (∃ M : ℝ, 0 < M ∧ ∀ z : ℂ, ‖E z‖ ≤ M * Real.exp (α * ‖z‖)) ∧
      (∀ ε > 0, ∃ M : ℝ, 0 < M ∧ ∀ z : ℂ,
        ‖E z‖ ≤ M * Real.exp ((α + ε) * ‖z‖)) ∧
      ∀ q : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ j ≤ q, ∀ t : ℝ,
        ‖iteratedDeriv j (K : ℝ → ℂ) t‖ ≤ C / (1 + |t|) ^ 2 := by
  let r := α / (2 * Real.pi)
  have hr : 0 < r := by dsimp [r]; positivity
  have hscale : 2 * Real.pi * r = α := by
    dsimp [r]
    field_simp
  obtain ⟨G, hGs, hG0, _⟩ := exists_compact_positive_fourier_smoothing hr
  let K : SchwartzMap ℝ ℂ := 𝓕 G
  let E := complexFourierExtension G
  let M := 1 + ∫ t : ℝ, ‖G t‖
  have hM : 0 < M := by
    dsimp [M]
    have : 0 ≤ ∫ t : ℝ, ‖G t‖ := integral_nonneg (fun t => norm_nonneg (G t))
    linarith
  have hbound (z : ℂ) : ‖E z‖ ≤ M * Real.exp (α * ‖z‖) := by
    have h := norm_complexFourierExtension_le G hr.le hGs z
    rw [hscale] at h
    apply h.trans
    gcongr
    dsimp [M]
    linarith
  refine ⟨K, E, differentiable_complexFourierExtension G hr.le hGs,
    complexFourierExtension_ofReal G, ?_, ⟨M, hM, hbound⟩, ?_,
    exists_schwartz_uniform_quadratic_derivative_bound K⟩
  · exact hG0
  · intro ε hε
    refine ⟨M, hM, fun z => (hbound z).trans ?_⟩
    gcongr
    linarith

end MeyerGeneralProblem
