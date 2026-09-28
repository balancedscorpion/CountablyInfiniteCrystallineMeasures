module

public import MeyerGeneralProblem.Cardinal.Adaptive.NativeOperators
public import MeyerGeneralProblem.Distribution.FiniteCombConvolution

@[expose] public section

/-!
# Polynomial translation and modulation bounds in the original Hermite norm

The oscillator conjugacy and original coefficient norm give polynomial growth
of degree `2*m`, uniformly before every translation parameter and test function.
Modulation follows from the actual Fourier conjugacy and the isometric diagonal
Hermite Fourier action. No mixed-derivative norm equivalence is assumed.
-/

namespace MeyerGeneralProblem.Adaptive
noncomputable section
open MeasureTheory
open scoped FourierTransform

/-- Fourier transform preserves every original positive Hermite norm. -/
theorem schwartzToHermiteScale_fourier_norm (m : ℕ) (f : SchwartzMap ℝ ℂ) :
    ‖schwartzToHermiteScale m (𝓕 f)‖ = ‖schwartzToHermiteScale m f‖ := by
  have he (n : ℕ) : ‖schwartzToHermiteScale m (𝓕 f) n‖ =
      ‖schwartzToHermiteScale m f n‖ := by
    rw [norm_schwartzToHermiteScale_apply, norm_schwartzToHermiteScale_apply,
      schwartzHermiteCoefficients_fourier, norm_mul, norm_hermiteFourierPhase, one_mul]
  exact le_antisymm
    (lp.norm_mono (by norm_num : (2:ENNReal) ≠ 0) (fun n => (he n).le))
    (lp.norm_mono (by norm_num : (2:ENNReal) ≠ 0) (fun n => (he n).ge))

/-- Inverse Fourier transform also preserves the same original norm. -/
theorem schwartzToHermiteScale_fourierInv_norm (m : ℕ) (f : SchwartzMap ℝ ℂ) :
    ‖schwartzToHermiteScale m (𝓕⁻ f)‖ = ‖schwartzToHermiteScale m f‖ := by
  have h := schwartzToHermiteScale_fourier_norm m (𝓕⁻ f)
  rw [FourierTransform.fourier_fourierInv_eq] at h
  exact h.symm

/-- Position multiplication costs at most one original Hermite order,
by the exact Fourier derivative identity. -/
theorem schwartzToHermiteScale_position_norm_bound (m : ℕ) (f : SchwartzMap ℝ ℂ) :
    ‖schwartzToHermiteScale m (coordinateMultiplicationCLM f)‖ ≤
      (‖Complex.I / (2 * (Real.pi : ℂ))‖ * (3 * (Real.sqrt (2*Real.pi) * 2^m))) *
        ‖schwartzToHermiteScale (m+1) f‖ := by
  rw [← schwartzToHermiteScale_fourier_norm m (coordinateMultiplicationCLM f),
    fourier_coordinateMultiplicationCLM, map_smul, norm_smul]
  have h := mul_le_mul_of_nonneg_left (schwartzToHermiteScale_derivative_norm_bound m (𝓕 f))
    (norm_nonneg (Complex.I / (2 * (Real.pi : ℂ))))
  rw [schwartzToHermiteScale_fourier_norm] at h
  simpa only [mul_assoc] using h

/-- Differentiation commutes with actual Schwartz translation. -/
theorem derivative_combSchwartzTranslation (a : ℝ) (f : SchwartzMap ℝ ℂ) :
    SchwartzMap.derivCLM ℂ ℂ (combSchwartzTranslation a f) =
      combSchwartzTranslation a (SchwartzMap.derivCLM ℂ ℂ f) := by
  ext x
  have he : (combSchwartzTranslation a f : ℝ → ℂ) = fun y => f (a+y) := rfl
  rw [SchwartzMap.derivCLM_apply, he]
  have h := (f.hasDerivAt (a+x)).scomp x ((hasDerivAt_id x).const_add a)
  simpa only [Function.comp_def, one_smul, combSchwartzTranslation_apply,
    SchwartzMap.derivCLM_apply] using h.deriv

/-- Position under translation retains the actual translation parameter. -/
theorem position_combSchwartzTranslation (a : ℝ) (f : SchwartzMap ℝ ℂ) :
    coordinateMultiplicationCLM (combSchwartzTranslation a f) =
      combSchwartzTranslation a (coordinateMultiplicationCLM f) -
        (a : ℂ) • combSchwartzTranslation a f := by
  ext x
  simp only [coordinateMultiplicationCLM_apply, combSchwartzTranslation_apply,
    sub_apply, smul_apply, smul_eq_mul, Complex.ofReal_add]
  ring

/-- Exact translation conjugacy of the original shifted oscillator. -/
theorem graph_combSchwartzTranslation (a : ℝ) (f : SchwartzMap ℝ ℂ) :
    hermiteGraphOperator (combSchwartzTranslation a f) =
      combSchwartzTranslation a
        (hermiteGraphOperator f - (2 * (Real.pi : ℂ) * a) • coordinateMultiplicationCLM f +
          ((Real.pi : ℂ) * (a : ℂ)^2) • f) := by
  have hposition : coordinateMultiplicationCLM
      (coordinateMultiplicationCLM (combSchwartzTranslation a f)) =
      combSchwartzTranslation a (coordinateMultiplicationCLM (coordinateMultiplicationCLM f)) -
        (2 * (a : ℂ)) • combSchwartzTranslation a (coordinateMultiplicationCLM f) +
        (a : ℂ)^2 • combSchwartzTranslation a f := by
    rw [position_combSchwartzTranslation, map_sub, map_smul,
      position_combSchwartzTranslation, position_combSchwartzTranslation]
    ext x
    simp only [sub_apply, add_apply, smul_apply, smul_eq_mul]
    ring
  simp only [hermiteGraphOperator, add_apply, smul_apply, neg_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    derivative_combSchwartzTranslation, hposition, map_add, map_sub, map_smul, map_neg]
  ext x
  simp only [smul_apply, add_apply, sub_apply, neg_apply, smul_eq_mul]
  field_simp
  ring

/-- Translation preserves the order-zero original norm exactly. -/
theorem schwartzToHermiteScale_zero_translation_norm (a : ℝ) (f : SchwartzMap ℝ ℂ) :
    ‖schwartzToHermiteScale 0 (combSchwartzTranslation a f)‖ =
      ‖schwartzToHermiteScale 0 f‖ := by
  rw [norm_schwartzToHermiteScale_zero, norm_schwartzToHermiteScale_zero,
    SchwartzMap.norm_toLp' (by norm_num : (2:ENNReal) ≠ 0) (by norm_num : (2:ENNReal) ≠ ⊤),
    SchwartzMap.norm_toLp' (by norm_num : (2:ENNReal) ≠ 0) (by norm_num : (2:ENNReal) ≠ ⊤)]
  congr 1
  exact integral_add_left_eq_self (fun x : ℝ => ‖f x‖ ^ (2:ENNReal).toReal) a

/-- The original order-`m` translation bound has degree exactly `2*m` in
`1+|a|`, with one constant for all shifts and all Schwartz inputs. -/
theorem exists_hermite_translation_bound (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℝ) (f : SchwartzMap ℝ ℂ),
      ‖schwartzToHermiteScale m (combSchwartzTranslation a f)‖ ≤
        C * (1 + |a|)^(2*m) * ‖schwartzToHermiteScale m f‖ := by
  induction m with
  | zero =>
      refine ⟨1, by norm_num, ?_⟩
      intro a f
      simp only [schwartzToHermiteScale_zero_translation_norm, mul_zero, pow_zero, one_mul, le_refl]
  | succ m ih =>
      obtain ⟨C, hC, hbound⟩ := ih
      let P : ℝ := ‖Complex.I / (2 * (Real.pi : ℂ))‖ *
        (3 * (Real.sqrt (2*Real.pi) * 2^m))
      have hP : 0 ≤ P := by dsimp [P]; positivity
      let B : ℝ := 1 + ‖2 * (Real.pi : ℂ)‖ * P + ‖(Real.pi : ℂ)‖
      have hB : 0 < B := by dsimp [B]; positivity
      refine ⟨C*B, mul_pos hC hB, ?_⟩
      intro a f
      let g := hermiteGraphOperator f - (2 * (Real.pi : ℂ) * a) • coordinateMultiplicationCLM f +
        ((Real.pi : ℂ) * (a : ℂ)^2) • f
      have hw : 1 ≤ (1 + |a|)^2 := by nlinarith [abs_nonneg a]
      have hwa : |a| ≤ (1 + |a|)^2 := by nlinarith [abs_nonneg a, sq_nonneg |a|]
      have hwa2 : |a|^2 ≤ (1 + |a|)^2 := by nlinarith [abs_nonneg a]
      have hg : ‖schwartzToHermiteScale m g‖ ≤
          B * (1 + |a|)^2 * ‖schwartzToHermiteScale (m+1) f‖ := by
        have hX : ‖schwartzToHermiteScale m (coordinateMultiplicationCLM f)‖ ≤
            P * ‖schwartzToHermiteScale (m+1) f‖ := schwartzToHermiteScale_position_norm_bound m f
        have hmono := schwartzToHermiteScale_norm_mono m f
        have hα : ‖2 * (Real.pi : ℂ) * a‖ ≤ ‖2 * (Real.pi : ℂ)‖ * (1+|a|)^2 := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left hwa (norm_nonneg _)
        have hβ : ‖(Real.pi : ℂ) * (a : ℂ)^2‖ ≤ ‖(Real.pi : ℂ)‖ * (1+|a|)^2 := by
          simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left hwa2 (abs_nonneg Real.pi)
        have hA := mul_le_mul hα hX (norm_nonneg _) (by positivity)
        have hD := mul_le_mul hβ hmono (norm_nonneg _) (by positivity)
        have hI := mul_le_mul_of_nonneg_right hw (norm_nonneg (schwartzToHermiteScale (m+1) f))
        dsimp only [g]
        rw [map_add, map_sub, map_smul, map_smul, schwartzToHermiteScale_graph]
        have htri := (norm_add_le
          (schwartzToHermiteScale (m+1) f - (2 * (Real.pi : ℂ) * a) •
            schwartzToHermiteScale m (coordinateMultiplicationCLM f))
          (((Real.pi : ℂ) * (a : ℂ)^2) • schwartzToHermiteScale m f)).trans
          (add_le_add (norm_sub_le _ _) le_rfl)
        simp only [norm_smul] at htri
        dsimp only [B] at ⊢
        nlinarith
      calc
        ‖schwartzToHermiteScale (m+1) (combSchwartzTranslation a f)‖ =
            ‖schwartzToHermiteScale m (hermiteGraphOperator (combSchwartzTranslation a f))‖ := by
          rw [schwartzToHermiteScale_graph]
        _ = ‖schwartzToHermiteScale m (combSchwartzTranslation a g)‖ := by
          rw [graph_combSchwartzTranslation]
        _ ≤ C * (1+|a|)^(2*m) * ‖schwartzToHermiteScale m g‖ := hbound a g
        _ ≤ C * (1+|a|)^(2*m) * (B * (1+|a|)^2 * ‖schwartzToHermiteScale (m+1) f‖) :=
          mul_le_mul_of_nonneg_left hg (by positivity)
        _ = (C*B) * (1+|a|)^(2*(m+1)) * ‖schwartzToHermiteScale (m+1) f‖ := by
          rw [show 2*(m+1) = 2*m+2 by omega, pow_add]
          ring

/-- Actual exponential modulation has the same original polynomial degree
as translation, by Fourier conjugacy without any additional order loss. -/
theorem exists_hermite_modulation_bound (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℝ) (f : SchwartzMap ℝ ℂ),
      ‖schwartzToHermiteScale m (combSchwartzModulation a f)‖ ≤
        C * (1 + |a|)^(2*m) * ‖schwartzToHermiteScale m f‖ := by
  obtain ⟨C, hC, hbound⟩ := exists_hermite_translation_bound m
  refine ⟨C, hC, ?_⟩
  intro a f
  change ‖schwartzToHermiteScale m (𝓕 (combSchwartzTranslation a (𝓕⁻ f)))‖ ≤ _
  rw [schwartzToHermiteScale_fourier_norm]
  have h := hbound a (𝓕⁻ f)
  rw [schwartzToHermiteScale_fourierInv_norm] at h
  exact h

end
end MeyerGeneralProblem.Adaptive
