module

public import MeyerGeneralProblem.Distribution.PeriodicIntegerComb
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import all Mathlib.MeasureTheory.Measure.Haar.NormedSpace

@[expose] public section

/-!
# Actual distributional dilation of Dirac combs

The Fourier scaling law is proved by the real integral change of
variables. It applies to genuine Schwartz pullbacks and therefore to
the actual tempered distributions, with the absolute Jacobian retained.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set SchwartzMap MeasureTheory
open scoped SchwartzMap FourierTransform

/-- Nonzero dilation pullback on the actual Schwartz space. -/
def combSchwartzDilation (a : ℝ) (ha : a ≠ 0) :
    SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 a ha))

/-- The dilation pullback evaluates at the genuine scaled physical point. -/
theorem combSchwartzDilation_apply (a : ℝ) (ha : a ≠ 0) (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    combSchwartzDilation a ha f x=f (a*x) := by
  change f (x*a)=f (a*x)
  rw [mul_comm]

/-- Actual pushforward dilation of tempered distributions. -/
def combDistributionDilation (a : ℝ) (ha : a ≠ 0) :
    TemperedDistribution ℝ ℂ →L[ℂ] TemperedDistribution ℝ ℂ :=
  PointwiseConvergenceCLM.precomp ℂ (combSchwartzDilation a ha)

/-- Exact evaluation of the genuine distributional dilation. -/
theorem combDistributionDilation_apply (a : ℝ) (ha : a ≠ 0)
    (T : TemperedDistribution ℝ ℂ) (f : SchwartzMap ℝ ℂ) :
    combDistributionDilation a ha T f=T (combSchwartzDilation a ha f) := rfl

/-- Fourier scaling for Schwartz functions, proved from the actual integral
and its absolute Jacobian, for either sign of the nonzero dilation. -/
theorem fourier_combSchwartzDilation (a : ℝ) (ha : a ≠ 0) (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    𝓕 (combSchwartzDilation a ha f) x=|a⁻¹| • 𝓕 f (a⁻¹*x) := by
  simp only [SchwartzMap.fourier_coe,Real.fourier_real_eq_integral_exp_smul]
  rw [← Measure.integral_comp_mul_left
    (fun y : ℝ => Complex.exp ((-2*Real.pi*y*(a⁻¹*x):ℝ)*Complex.I) • f y) a]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [combSchwartzDilation_apply]
  congr 2
  congr 1
  field_simp

/-- The Fourier transform of the pushforward dilation retains exactly the
inverse absolute Jacobian and the reciprocal physical scale. -/
theorem fourier_combDistributionDilation (a : ℝ) (ha : a ≠ 0)
    (T : TemperedDistribution ℝ ℂ) :
    𝓕 (combDistributionDilation a ha T)=
      ((|a|⁻¹:ℝ):ℂ) • combDistributionDilation a⁻¹ (inv_ne_zero ha) (𝓕 T) := by
  ext f
  simp only [TemperedDistribution.fourier_apply,combDistributionDilation_apply,smul_apply]
  have heq : combSchwartzDilation a ha (𝓕 f)=
      ((|a|⁻¹:ℝ):ℂ) • 𝓕 (combSchwartzDilation a⁻¹ (inv_ne_zero ha) f) := by
    ext x
    rw [combSchwartzDilation_apply,smul_apply,fourier_combSchwartzDilation]
    simp only [inv_inv,Complex.real_smul,smul_eq_mul]
    have hn : ((|a|:ℝ):ℂ)≠0 := by exact_mod_cast abs_ne_zero.mpr ha
    simp [hn]
  rw [heq,map_smul]

/-- Actual dilated periodic coefficient comb. -/
def scaledPeriodicComb {N : ℕ} [NeZero N] (a : ℝ) (ha : a ≠ 0)
    (w : ZMod N → ℂ) : TemperedDistribution ℝ ℂ :=
  combDistributionDilation a ha (periodicIntegerComb w)

/-- Exact absolutely convergent action at the scaled integer nodes. -/
theorem scaledPeriodicComb_apply {N : ℕ} [NeZero N] (a : ℝ) (ha : a ≠ 0)
    (w : ZMod N → ℂ) (f : SchwartzMap ℝ ℂ) :
    scaledPeriodicComb a ha w f=∑' n : ℤ, w (n : ZMod N)*f (a*n) := by
  rw [scaledPeriodicComb,combDistributionDilation_apply,periodicIntegerComb_apply]
  simp only [combSchwartzDilation_apply]

/-- Exact Fourier transform in finite shifted-coset form before any
reindexing into one reciprocal lattice. -/
theorem fourier_scaledPeriodicComb {N : ℕ} [NeZero N] (a : ℝ) (ha : a ≠ 0)
    (w : ZMod N → ℂ) :
    𝓕 (scaledPeriodicComb a ha w)=
      (((|a|⁻¹:ℝ):ℂ)*(N:ℂ)⁻¹) • ∑ k : ZMod N,
        ZMod.dft w k • combDistributionDilation a⁻¹ (inv_ne_zero ha)
          (shiftedIntegerComb (k.val/(N:ℝ))) := by
  rw [scaledPeriodicComb,fourier_combDistributionDilation,fourier_periodicIntegerComb,
    map_smul,map_sum,smul_smul]
  simp only [map_smul]

end

end MeyerGeneralProblem
