module

public import Mathlib.Analysis.Complex.PhragmenLindelof
import all Mathlib.Analysis.Complex.PhragmenLindelof

@[expose] public section

/-!
# Sharp vertical growth of bounded entire functions of exponential type

The radial exponential-type hypothesis is converted into the sharp vertical
estimate by exponential damping and the Phragmen–Lindelöf principle. No vertical
growth estimate is included among the hypotheses.
-/

noncomputable section

open Set Filter Asymptotics Complex Bornology
open scoped Topology

namespace MeyerGeneralProblem

private theorem norm_entire_right_half_plane_le_eps {G : ℂ → ℂ} {τ M ε : ℝ}
    (hG : Differentiable ℂ G) (hτ : 0 ≤ τ) (hε : 0 < ε)
    (htype : ∀ δ > 0, ∃ C > 0, ∀ z, ‖G z‖ ≤ C * Real.exp ((τ + δ) * ‖z‖))
    (haxis : ∀ x : ℝ, ‖G (x * I)‖ ≤ M) {z : ℂ} (hz : 0 ≤ z.re) :
    ‖G z‖ ≤ M * Real.exp ((τ + ε) * z.re) := by
  let F : ℂ → ℂ := fun w => Complex.exp (-(τ + ε : ℝ) * w) * G w
  have hFn (w : ℂ) : ‖F w‖ = Real.exp (-(τ + ε) * w.re) * ‖G w‖ := by
    simp [F, Complex.norm_exp]
  have hFd : Differentiable ℂ F :=
    (differentiable_id.const_mul _).cexp.mul hG
  have hFM : ‖F z‖ ≤ M := by
    apply PhragmenLindelof.right_half_plane_of_bounded_on_real hFd.diffContOnCl
    · obtain ⟨C, hC, hbound⟩ := htype 1 zero_lt_one
      refine ⟨1, by norm_num, τ + 1, IsBigO.of_bound C ?_⟩
      refine eventually_inf_principal.2 (Eventually.of_forall fun w hw => ?_)
      rw [hFn]
      calc
        Real.exp (-(τ + ε) * w.re) * ‖G w‖ ≤ ‖G w‖ :=
          mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.mpr
            (mul_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt hw)))
        _ ≤ C * ‖Real.exp ((τ + 1) * ‖w‖ ^ (1 : ℝ))‖ := by
          simpa only [Real.rpow_one, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
            using hbound w
    · obtain ⟨C, hC, hbound⟩ := htype (ε / 2) (by positivity)
      apply isBoundedUnder_of_eventually_le (a := C)
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
      rw [hFn]
      simp only [ofReal_re]
      calc
        Real.exp (-(τ + ε) * x) * ‖G x‖ ≤
            Real.exp (-(τ + ε) * x) * (C * Real.exp ((τ + ε / 2) * x)) := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
          simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx]
            using hbound (x : ℂ)
        _ = C * Real.exp (-(ε / 2) * x) := by
          rw [mul_left_comm, ← Real.exp_add]
          congr 2
          ring
        _ ≤ C := mul_le_of_le_one_right hC.le (Real.exp_le_one_iff.mpr
          (mul_nonpos_of_nonpos_of_nonneg (by linarith) hx))
    · intro x
      simpa [hFn] using haxis x
    · exact hz
  rw [hFn, neg_mul, Real.exp_neg] at hFM
  have hmul := mul_le_mul_of_nonneg_left hFM (Real.exp_pos ((τ + ε) * z.re)).le
  simpa only [← mul_assoc, mul_inv_cancel₀ (Real.exp_ne_zero _), one_mul,
    mul_comm (Real.exp ((τ + ε) * z.re)) M] using hmul

/-- Sharp exponential growth in a right half-plane, from radial exponential type
and a bound on the imaginary axis. -/
theorem norm_entire_right_half_plane_le {G : ℂ → ℂ} {τ M : ℝ}
    (hG : Differentiable ℂ G) (hτ : 0 ≤ τ)
    (htype : ∀ ε > 0, ∃ C > 0, ∀ z, ‖G z‖ ≤ C * Real.exp ((τ + ε) * ‖z‖))
    (haxis : ∀ x : ℝ, ‖G (x * I)‖ ≤ M) {z : ℂ} (hz : 0 ≤ z.re) :
    ‖G z‖ ≤ M * Real.exp (τ * z.re) := by
  have hlim : Tendsto (fun ε : ℝ => M * Real.exp ((τ + ε) * z.re))
      (𝓝[>] 0) (𝓝 (M * Real.exp (τ * z.re))) := by
    exact (Continuous.tendsto' (by fun_prop) _ _ (by simp)).mono_left
      nhdsWithin_le_nhds
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact norm_entire_right_half_plane_le_eps hG hτ hε htype haxis hz

/-- A bounded entire function of radial exponential type at most `τ` satisfies
the sharp vertical growth estimate, with the original real-axis bound `M`. -/
theorem norm_entire_le_exp_abs_im {G : ℂ → ℂ} {τ M : ℝ}
    (hG : Differentiable ℂ G) (hτ : 0 ≤ τ) (_hM : 0 ≤ M)
    (htype : ∀ ε > 0, ∃ C > 0, ∀ z, ‖G z‖ ≤ C * Real.exp ((τ + ε) * ‖z‖))
    (hreal : ∀ x : ℝ, ‖G x‖ ≤ M) (z : ℂ) :
    ‖G z‖ ≤ M * Real.exp (τ * |z.im|) := by
  by_cases hz : 0 ≤ z.im
  · have hrot := norm_entire_right_half_plane_le
      (G := fun w : ℂ => G (I * w))
      (hG.comp (differentiable_id.const_mul I)) hτ
      (fun ε hε => by
        obtain ⟨C, hC, hbound⟩ := htype ε hε
        exact ⟨C, hC, fun w => by simpa only [norm_mul, norm_I, one_mul] using hbound (I * w)⟩)
      (fun x => by
        convert hreal (-x) using 1
        congr 1
        push_cast
        ring_nf
        simp)
      (z := -I * z) (by simpa using hz)
    simpa [← mul_assoc, abs_of_nonneg hz] using hrot
  · have hz' : z.im ≤ 0 := le_of_not_ge hz
    have hrot := norm_entire_right_half_plane_le
      (G := fun w : ℂ => G (-I * w))
      (hG.comp (differentiable_id.const_mul (-I))) hτ
      (fun ε hε => by
        obtain ⟨C, hC, hbound⟩ := htype ε hε
        exact ⟨C, hC, fun w => by
          simpa only [norm_mul, norm_neg, norm_I, one_mul] using hbound (-I * w)⟩)
      (fun x => by
        convert hreal x using 1
        congr 1
        ring_nf
        simp)
      (z := I * z) (by simpa using neg_nonneg.mpr hz')
    simpa [← mul_assoc, abs_of_nonpos hz'] using hrot

end MeyerGeneralProblem
