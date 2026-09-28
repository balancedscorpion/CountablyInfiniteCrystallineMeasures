module

public import MeyerGeneralProblem.Sampling.KNSGraphSchwartzComparison
public import MeyerGeneralProblem.Hermite.DistributionCoherence

@[expose] public section

/-!
# The actual order-two graph oscillator and Hermite reconstruction

The shifted oscillator is constructed from the actual L2 graph coordinates.
Distributional differentiation and genuine smooth Hermite tests prove its exact
n+1 coefficient identity, including the inverse-Fourier sign and half shift.
The existing Schwartz graph embedding extends from the unrestricted positive
Hermite scale. Coefficient equality then reconstructs every actual graph vector,
so surjectivity is a conclusion, not an assumption. The oscillator has a uniform
graph-norm bound. No carrier-zero-constrained core or higher-order result is claimed.
-/

namespace MeyerGeneralProblem.KNSGraphOscillator

noncomputable section

open MeasureTheory MeyerGeneralProblem LineDeriv Complex
open scoped FourierTransform ComplexConjugate

/-- The shifted oscillator built from the actual four-coordinate graph. -/
def oscillator (v : KNSGraphSpace 2) : KNSL2 :=
  (Real.pi : ℂ) • (𝓕⁻ (KNSGraphSpace.frequencyWeight 2 v) +
    KNSGraphSpace.physicalWeight 2 v) +
  (1/2 : ℂ) • KNSGraphSpace.physical 2 v

/-- The L2 Hermite coefficient is actual evaluation of its distribution
on the real-valued normalized Hermite test. -/
theorem lp_hermite_coeff (f : KNSL2) (n : ℕ) :
    (TauCeti.twoPiHermiteHilbertBasis ℂ).repr f n =
      (f : TemperedDistribution ℝ ℂ) (normalizedHermiteSchwartz n) := by
  rw [HilbertBasis.repr_apply_apply, TauCeti.coe_twoPiHermiteHilbertBasis,
    ← TauCeti.toLp_twoPiHermiteSchwartzMap, MeasureTheory.L2.inner_def,
    Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [(TauCeti.twoPiHermiteSchwartzMap n).coeFn_toLp 2 volume] with x hx
  rw [hx]
  simp only [RCLike.inner_apply, smul_eq_mul]
  rw [normalizedHermiteSchwartz_eq_twoPi, TauCeti.twoPiHermiteSchwartzMap_apply]
  change f x * conj (TauCeti.twoPiHermiteFunction n x : ℂ) = _
  rw [Complex.conj_ofReal]
  ring

/-- The existing Schwartz oscillator acts on each genuine normalized
Hermite test by its exact eigenvalue n+1. -/
theorem hermite_graph_eigen (n : ℕ) :
    hermiteGraphOperator (normalizedHermiteSchwartz n) =
      ((n : ℂ) + 1) • normalizedHermiteSchwartz n := by
  apply schwartzToHermiteScale_injective 0
  apply lp.ext
  funext j
  simp only [map_smul]
  change schwartzHermiteCoefficients (hermiteGraphOperator (normalizedHermiteSchwartz n)) j =
    ((n : ℂ) + 1) * schwartzHermiteCoefficients (normalizedHermiteSchwartz n) j
  rw [hermiteGraphOperator_coeff, schwartzHermiteCoefficients_apply_repr,
    normalizedHermiteSchwartz_eq_twoPi, TauCeti.toLp_twoPiHermiteSchwartzMap]
  have hb : TauCeti.twoPiHermiteFunctionLp ℂ n = (TauCeti.twoPiHermiteHilbertBasis ℂ) n :=
    (congrFun (TauCeti.coe_twoPiHermiteHilbertBasis (𝕜 := ℂ)) n).symm
  rw [hb, HilbertBasis.repr_self]
  by_cases hj : j = n
  · subst j
    rfl
  · simp [lp.single_apply, hj]

/-- The inverse distributional Fourier derivative has the genuine
positive 2*pi*i multiplier. -/
theorem lineDeriv_inverse (T : TemperedDistribution ℝ ℂ) :
    lineDerivOp (1 : ℝ) (𝓕⁻ T) = (2 * Real.pi * Complex.I) •
      𝓕⁻ (TemperedDistribution.smulLeftCLM ℂ (fun x : ℝ => (x : ℂ)) T) := by
  rw [TemperedDistribution.lineDerivOp_fourierInv_eq]
  simp only [Real.inner_apply, mul_one, FourierTransform.fourierInv_smul]

/-- The genuine second inverse-Fourier derivative has coefficient
minus four pi squared; this is a distribution identity, not a C2 claim. -/
theorem second_lineDeriv_inverse (T : TemperedDistribution ℝ ℂ) :
    lineDerivOp (1 : ℝ) (lineDerivOp (1 : ℝ) (𝓕⁻ T)) =
      (-(4 * Real.pi^2) : ℂ) •
        𝓕⁻ (TemperedDistribution.smulLeftCLM ℂ (fun x : ℝ => (x : ℂ)^2) T) := by
  rw [lineDeriv_inverse, lineDerivOp_smul, lineDeriv_inverse, smul_smul]
  have hc : (2 * (Real.pi : ℂ) * Complex.I) * (2 * Real.pi * Complex.I) =
      -(4 * Real.pi^2) := by ring_nf; simp
  rw [hc, TemperedDistribution.smulLeftCLM_smulLeftCLM_apply (by fun_prop) (by fun_prop)]
  rw [show ((fun x : ℝ => (x : ℂ)) * fun x : ℝ => (x : ℂ)) =
    (fun x : ℝ => (x : ℂ)^2) from by funext x; simp [pow_two]]

/-- Two distributional derivatives of the physical graph coordinate
are exactly minus four pi squared times inverse Fourier of its weighted
frequency coordinate. No classical second derivative is asserted. -/
theorem graph_second_deriv (v : KNSGraphSpace 2) :
    lineDerivOp (1 : ℝ) (lineDerivOp (1 : ℝ)
      (KNSGraphSpace.physical 2 v : TemperedDistribution ℝ ℂ)) =
    (-(4 * Real.pi^2) : ℂ) •
      (𝓕⁻ (KNSGraphSpace.frequencyWeight 2 v) : KNSL2) := by
  have hq : (KNSGraphSpace.physical 2 v : TemperedDistribution ℝ ℂ) =
      𝓕⁻ (KNSGraphSpace.frequency 2 v : TemperedDistribution ℝ ℂ) := by
    rw [Lp.fourierInv_toTemperedDistribution_eq, KNSGraphSpace.frequency_eq_fourier,
      FourierTransform.fourierInv_fourier_eq]
  have hW : (KNSGraphSpace.frequencyWeight 2 v : TemperedDistribution ℝ ℂ) =
      TemperedDistribution.smulLeftCLM ℂ (fun x : ℝ => (x : ℂ)^2)
        (KNSGraphSpace.frequency 2 v : TemperedDistribution ℝ ℂ) := v.property.2.2
  rw [hq, second_lineDeriv_inverse, ← hW, Lp.fourierInv_toTemperedDistribution_eq]

/-- On Schwartz tests the unit directional derivative is the ordinary
Schwartz derivative map. -/
theorem lineDeriv_one (φ : SchwartzMap ℝ ℂ) :
    lineDerivOp (1 : ℝ) φ = SchwartzMap.derivCLM ℂ ℂ φ := by
  ext x
  simp [SchwartzMap.lineDerivOp_apply_eq_fderiv]

/-- The two distributional minus signs cancel on a Schwartz test. -/
theorem second_lineDeriv_apply (T : TemperedDistribution ℝ ℂ) (φ : SchwartzMap ℝ ℂ) :
    lineDerivOp (1 : ℝ) (lineDerivOp (1 : ℝ) T) φ =
      T (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ φ)) := by
  simp only [TemperedDistribution.lineDerivOp_apply_apply, map_neg, neg_neg,
    lineDeriv_one]

/-- The L2 oscillator acts on every Schwartz test by the actual shifted
Schwartz oscillator. This uses the graph's two distributional weight identities. -/
theorem oscillator_test (v : KNSGraphSpace 2) (φ : SchwartzMap ℝ ℂ) :
    (oscillator v : TemperedDistribution ℝ ℂ) φ =
      (KNSGraphSpace.physical 2 v : TemperedDistribution ℝ ℂ) (hermiteGraphOperator φ) := by
  have hd := congrArg (fun T : TemperedDistribution ℝ ℂ => T φ) (graph_second_deriv v)
  rw [second_lineDeriv_apply] at hd
  have hw := congrArg (fun T : TemperedDistribution ℝ ℂ => T φ) v.property.2.1
  change (KNSGraphSpace.physicalWeight 2 v : TemperedDistribution ℝ ℂ) φ =
    (KNSGraphSpace.physical 2 v : TemperedDistribution ℝ ℂ)
      (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => (x : ℂ)^2) φ) at hw
  have hW : SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => (x : ℂ)^2) φ =
      coordinateMultiplicationCLM (coordinateMultiplicationCLM φ) := by
    ext x
    rw [SchwartzMap.smulLeftCLM_apply_apply (by fun_prop)]
    simp only [coordinateMultiplicationCLM_apply, smul_eq_mul, pow_two, mul_assoc]
  rw [hW] at hw
  change (Lp.toTemperedDistributionCLM ℂ volume 2 (oscillator v)) φ = _
  simp only [oscillator, map_add, map_smul, add_apply,
    smul_apply, smul_eq_mul]
  simp only [hermiteGraphOperator, add_apply,
    smul_apply, neg_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, map_add, map_smul, map_neg]
  change (Real.pi : ℂ) * (_ + _) + (1/2 : ℂ) * _ =
    ((4 * (Real.pi : ℂ))⁻¹) * (-_ + (4 * (Real.pi : ℂ)^2) * _) + (1/2 : ℂ) * _
  rw [← hw]
  change _ = -(4 * (Real.pi : ℂ)^2) *
    ((𝓕⁻ (KNSGraphSpace.frequencyWeight 2 v) : KNSL2) : TemperedDistribution ℝ ℂ) φ at hd
  rw [hd]
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  simp only [Lp.toTemperedDistributionCLM_apply]
  field_simp

/-- The actual graph oscillator has exactly the n+1 Hermite coefficient,
proved by testing its distribution only on genuine smooth Hermite functions. -/
theorem oscillator_coeff (v : KNSGraphSpace 2) (n : ℕ) :
    (TauCeti.twoPiHermiteHilbertBasis ℂ).repr (oscillator v) n =
      ((n : ℂ) + 1) *
        (TauCeti.twoPiHermiteHilbertBasis ℂ).repr (KNSGraphSpace.physical 2 v) n := by
  rw [lp_hermite_coeff, oscillator_test, hermite_graph_eigen, map_smul, lp_hermite_coeff]
  rfl

/-- Extend the existing Schwartz graph embedding through the unrestricted
positive Hermite scale, using only the retained norm bound and dense range. -/
def graphExtension : HermiteScale 1 →L[ℂ] KNSGraphSpace 2 :=
  (KNSGraphSpace.schwartzEmbedding 2).toLinearMap.extendOfNorm
    (schwartzToHermiteScale 1).toLinearMap

/-- The extension actually agrees with the existing graph embedding. -/
theorem graphExtension_schwartz (φ : SchwartzMap ℝ ℂ) :
    graphExtension (schwartzToHermiteScale 1 φ) = KNSGraphSpace.schwartzEmbedding 2 φ := by
  exact LinearMap.extendOfNorm_eq (schwartzToHermiteScale_denseRange 1)
    ⟨3, KNSGraphSchwartzComparison.norm_schwartzEmbedding_two_le⟩ φ

/-- The extension's physical coefficient is normalized by precisely n+1.
The statement is derived by continuous equality on the unrestricted dense
Schwartz range, not by assuming a graph core. -/
theorem graphExtension_physical_coeff (u : HermiteScale 1) (n : ℕ) :
    ((n : ℂ) + 1) * (TauCeti.twoPiHermiteHilbertBasis ℂ).repr
      (KNSGraphSpace.physical 2 (graphExtension u)) n = u n := by
  let P : HermiteScale 1 → Prop := fun w =>
    ((n : ℂ) + 1) * (TauCeti.twoPiHermiteHilbertBasis ℂ).repr
      (KNSGraphSpace.physical 2 (graphExtension w)) n = w n
  change P u
  apply DenseRange.induction_on (p := P) (schwartzToHermiteScale_denseRange 1) u
  · have he := (lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 n).continuous
    exact isClosed_eq
      (continuous_const.mul (he.comp ((TauCeti.twoPiHermiteHilbertBasis ℂ).repr.continuous.comp
        ((KNSGraphSpace.physical 2).continuous.comp graphExtension.continuous))))
      he
  intro φ
  change ((n : ℂ) + 1) * (TauCeti.twoPiHermiteHilbertBasis ℂ).repr
    (KNSGraphSpace.physical 2 (graphExtension (schwartzToHermiteScale 1 φ))) n =
    schwartzToHermiteScale 1 φ n
  rw [graphExtension_schwartz, KNSGraphSpace.physical_schwartzEmbedding]
  rw [schwartzToHermiteScale_apply]
  simp [normalizeHermiteCoefficients, hermiteScaleWeight,
    schwartzHermiteCoefficients_apply_repr]

/-- The original graph vector is recovered by the extension from its
actual oscillator coefficient sequence. This proves the required
surjectivity; it is not an input or a definition of the graph space. -/
theorem graphExtension_oscillator (v : KNSGraphSpace 2) :
    graphExtension ((TauCeti.twoPiHermiteHilbertBasis ℂ).repr (oscillator v)) = v := by
  apply KNSGraphSpace.physical_injective 2
  apply (TauCeti.twoPiHermiteHilbertBasis ℂ).repr.injective
  apply lp.ext
  funext n
  have hc := graphExtension_physical_coeff
    ((TauCeti.twoPiHermiteHilbertBasis ℂ).repr (oscillator v)) n
  rw [oscillator_coeff] at hc
  exact mul_left_cancel₀ (by
    exact_mod_cast (by positivity : (n : ℝ) + 1 ≠ 0)) hc

/-- The actual oscillator has a uniform norm bound from its three graph
coordinates and the isometry of the genuine inverse Fourier transform. -/
theorem oscillator_norm_le (v : KNSGraphSpace 2) :
    ‖oscillator v‖ ≤ (2 * Real.pi + 1/2) * ‖v‖ := by
  have hi : ‖(𝓕⁻ (KNSGraphSpace.frequencyWeight 2 v) : KNSL2)‖ =
      ‖KNSGraphSpace.frequencyWeight 2 v‖ := by
    calc
      _ = ‖𝓕 (𝓕⁻ (KNSGraphSpace.frequencyWeight 2 v) : KNSL2)‖ :=
        (Lp.norm_fourier_eq _).symm
      _ = _ := by rw [FourierTransform.fourier_fourierInv_eq]
  have hp := KNSGraphSpace.norm_coordinate_le v 0
  have hw := KNSGraphSpace.norm_coordinate_le v 2
  have hq := KNSGraphSpace.norm_coordinate_le v 3
  calc
    ‖oscillator v‖ ≤ ‖(Real.pi : ℂ) •
        (𝓕⁻ (KNSGraphSpace.frequencyWeight 2 v) + KNSGraphSpace.physicalWeight 2 v)‖ +
        ‖(1/2 : ℂ) • KNSGraphSpace.physical 2 v‖ := norm_add_le _ _
    _ = Real.pi * ‖𝓕⁻ (KNSGraphSpace.frequencyWeight 2 v) +
        KNSGraphSpace.physicalWeight 2 v‖ + (1/2 : ℝ) * ‖KNSGraphSpace.physical 2 v‖ := by
      simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg Real.pi_pos.le]
      norm_num
    _ ≤ Real.pi * (‖(𝓕⁻ (KNSGraphSpace.frequencyWeight 2 v) : KNSL2)‖ +
        ‖KNSGraphSpace.physicalWeight 2 v‖) +
        (1/2 : ℝ) * ‖KNSGraphSpace.physical 2 v‖ := by
      gcongr
      exact norm_add_le _ _
    _ ≤ Real.pi * (‖v‖ + ‖v‖) + (1/2 : ℝ) * ‖v‖ := by
      rw [hi]
      gcongr
    _ = _ := by ring

end
end MeyerGeneralProblem.KNSGraphOscillator
