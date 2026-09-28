module

public import MeyerGeneralProblem.Sampling.GroupedSpectralGap
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import all Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

@[expose] public section

/-!
# The order-two mixed weighted Schwartz estimate

Two genuine integrations by parts give the exact identity for the mixed
energy `∫ x² ‖f′‖²`. Young's inequality then controls it by the unweighted
mass and the two pure order-two energies, with coefficient `1/2`.
All functions here are actual complex Schwartz functions. No density or
extension to arbitrary elements of the completed KNS graph is asserted.
No Fourier transform or Fourier normalization is used in this proof.
-/

namespace MeyerGeneralProblem
namespace KNSMixedWeightedSchwartz

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

def X (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => x) f

private theorem X_apply (f : SchwartzMap ℝ ℂ) (x : ℝ) : X f x = x • f x :=
  SchwartzMap.smulLeftCLM_apply_apply (by fun_prop) f x

private theorem deriv_X (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    deriv (X f) x = f x + x • deriv f x := by
  have he : (X f : ℝ → ℂ) = fun x => x • f x := funext (X_apply f)
  rw [he]
  have h : HasDerivAt (fun t : ℝ => t • f t) (x • deriv f x + f x) x := by
    simpa only [one_smul, Pi.smul_def', id_eq] using
      ((hasDerivAt_id x).smul (f.hasDerivAt x))
  simpa only [add_comm] using h.deriv

private theorem deriv_XX (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    deriv (X (X f)) x = (2*x) • f x + x^2 • deriv f x := by
  rw [deriv_X, X_apply, deriv_X, smul_add, smul_smul]
  simp only [pow_two, two_mul, add_smul]
  abel

private theorem integrable_inner (f g : SchwartzMap ℝ ℂ) :
    Integrable (fun x => ⟪f x, g x⟫_ℝ) :=
  (SchwartzMap.pairing (innerSL ℝ) f g).integrable

private theorem integrable_mass (f : SchwartzMap ℝ ℂ) :
    Integrable (fun x => ‖f x‖^2) :=
  integrable_norm_sq_of_memLp_complex (f.memLp 2)

private theorem integrable_first_cross (f : SchwartzMap ℝ ℂ) :
    Integrable (fun x => x * ⟪f x, deriv f x⟫_ℝ) := by
  simpa only [X_apply, SchwartzMap.derivCLM_apply, real_inner_smul_left] using
    integrable_inner (X f) (SchwartzMap.derivCLM ℂ ℂ f)

private theorem first_cross (f : SchwartzMap ℝ ℂ) :
    2 * (∫ x : ℝ, x * ⟪f x, deriv f x⟫_ℝ) = -(∫ x : ℝ, ‖f x‖^2) := by
  have h := SchwartzMap.integral_bilinear_deriv_right_eq_neg_left f (X f) (innerSL ℝ)
  change (∫ x : ℝ, ⟪f x, deriv (X f) x⟫_ℝ) =
    -(∫ x : ℝ, ⟪deriv f x, X f x⟫_ℝ) at h
  simp_rw [deriv_X, inner_add_right, real_inner_self_eq_norm_sq,
    X_apply, real_inner_smul_right] at h
  simp only [real_inner_comm (f _) (deriv f _)] at h
  rw [integral_add (integrable_mass f) (integrable_first_cross f)] at h
  linarith

/-- The actual mixed order-two energy is integrable for every Schwartz function. -/
theorem integrable_mixed (f : SchwartzMap ℝ ℂ) :
    Integrable (fun x : ℝ => x^2 * ‖deriv f x‖^2) := by
  have he (x : ℝ) : ‖X (SchwartzMap.derivCLM ℂ ℂ f) x‖^2 =
      x^2 * ‖deriv f x‖^2 := by
    rw [X_apply, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
      SchwartzMap.derivCLM_apply]
  simpa only [he] using integrable_mass (X (SchwartzMap.derivCLM ℂ ℂ f))

private theorem integrable_top_cross (f : SchwartzMap ℝ ℂ) :
    Integrable (fun x : ℝ => ⟪x^2 • f x, deriv (deriv f) x⟫_ℝ) := by
  have h := integrable_inner (X (X f))
    (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ f))
  change Integrable (fun x => ⟪X (X f) x, deriv (deriv f) x⟫_ℝ) at h
  simpa only [X_apply, smul_smul, ← pow_two] using h

/-- Exact integration-by-parts identity. The real inner product is the
real part of the conjugate-bilinear complex pairing; boundary terms vanish
because all weighted derivatives are actual Schwartz functions. -/
theorem mixed_energy_identity (f : SchwartzMap ℝ ℂ) :
    (∫ x : ℝ, x^2 * ‖deriv f x‖^2) = (∫ x : ℝ, ‖f x‖^2) -
      ∫ x : ℝ, ⟪x^2 • f x, deriv (deriv f) x⟫_ℝ := by
  have h := SchwartzMap.integral_bilinear_deriv_right_eq_neg_left
    (X (X f)) (SchwartzMap.derivCLM ℂ ℂ f) (innerSL ℝ)
  change (∫ x : ℝ, ⟪X (X f) x, deriv (deriv f) x⟫_ℝ) =
    -(∫ x : ℝ, ⟪deriv (X (X f)) x, deriv f x⟫_ℝ) at h
  simp_rw [X_apply, smul_smul, ← pow_two, deriv_XX, inner_add_left,
    real_inner_smul_left, real_inner_self_eq_norm_sq] at h
  have hterm (x : ℝ) : (2*x) * ⟪f x, deriv f x⟫_ℝ =
      2 * (x * ⟪f x, deriv f x⟫_ℝ) := by ring
  simp_rw [hterm] at h
  rw [integral_add ((integrable_first_cross f).const_mul 2) (integrable_mixed f),
    integral_const_mul, first_cross] at h
  simp_rw [real_inner_smul_left]
  linarith

/-- The mixed Schwartz energy is bounded by mass plus half the two pure
order-two energies. This is a same-order estimate, not a higher-order
Hermite bound. -/
theorem mixed_energy_le (f : SchwartzMap ℝ ℂ) :
    (∫ x : ℝ, x^2 * ‖deriv f x‖^2) ≤ (∫ x : ℝ, ‖f x‖^2) +
      ((∫ x : ℝ, ‖x^2 • f x‖^2) + (∫ x : ℝ, ‖deriv (deriv f) x‖^2))/2 := by
  have hw : Integrable (fun x : ℝ => ‖x^2 • f x‖^2) := by
    simpa only [X_apply, smul_smul, ← pow_two] using integrable_mass (X (X f))
  have hd : Integrable (fun x : ℝ => ‖deriv (deriv f) x‖^2) := by
    exact integrable_mass (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ f))
  have hi := integral_mono (integrable_top_cross f).neg ((hw.add hd).div_const 2)
    (fun x : ℝ => show -⟪x^2 • f x, deriv (deriv f) x⟫_ℝ ≤
        (‖x^2 • f x‖^2 + ‖deriv (deriv f) x‖^2)/2 from by
      have hh := real_inner_le_norm (-(x^2 • f x)) (deriv (deriv f) x)
      rw [inner_neg_left, norm_neg] at hh
      nlinarith [sq_nonneg (‖x^2 • f x‖ - ‖deriv (deriv f) x‖)])
  simp only [Pi.neg_apply, Pi.add_apply] at hi
  rw [integral_neg, integral_div, integral_add hw hd] at hi
  rw [mixed_energy_identity]
  linarith

private theorem integrable_complex_inner (f g : SchwartzMap ℝ ℂ) :
    Integrable (fun x : ℝ => ⟪f x, g x⟫_ℂ) := by
  apply (L2.integrable_inner (𝕜 := ℂ) (f.toLp 2 volume) (g.toLp 2 volume)).congr
  filter_upwards [f.coeFn_toLp 2 volume, g.coeFn_toLp 2 volume] with x hf hg
  rw [hf, hg]

/-- The exact identity with the complex conjugation and the real part
outside the integral displayed explicitly. In particular the positive
mass correction and the conjugate on `f`, not `f″`, are fixed. -/
theorem mixed_energy_identity_re (f : SchwartzMap ℝ ℂ) :
    (∫ x : ℝ, x^2 * ‖deriv f x‖^2) = (∫ x : ℝ, ‖f x‖^2) -
      (∫ x : ℝ, (x : ℂ)^2 * deriv (deriv f) x * star (f x)).re := by
  have he (x : ℝ) : (x : ℂ)^2 * deriv (deriv f) x * star (f x) =
      ⟪X (X f) x, deriv (deriv f) x⟫_ℂ := by
    rw [X_apply, X_apply, smul_smul, ← pow_two,
      RCLike.real_smul_eq_coe_smul (K := ℂ)]
    rw [inner_smul_left, RCLike.inner_apply, RCLike.conj_ofReal, RCLike.ofReal_pow]
    change (x : ℂ)^2 * deriv (deriv f) x * star (f x) =
      (x : ℂ)^2 * (deriv (deriv f) x * star (f x))
    ring
  have hi : Integrable (fun x : ℝ => (x : ℂ)^2 * deriv (deriv f) x * star (f x)) := by
    simp_rw [he]
    exact integrable_complex_inner (X (X f))
      (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ f))
  change _ = _ - RCLike.re (∫ x : ℝ, (x : ℂ)^2 * deriv (deriv f) x * star (f x))
  rw [← integral_re hi, mixed_energy_identity]
  congr 1
  apply integral_congr_ae
  filter_upwards with x
  rw [he, ← real_inner_eq_re_inner ℂ, X_apply, X_apply, smul_smul, ← pow_two]

private theorem integral_mass_eq_norm (f : SchwartzMap ℝ ℂ) :
    (∫ x : ℝ, ‖f x‖^2) = ‖f.toLp 2 volume‖^2 :=
  integral_norm_sq_eq_toLp_norm_sq_complex (f.memLp 2)

/-- The requested estimate in actual L2 norms of the three Schwartz
functions `f`, `x²f`, and `f″`. No norm-equivalence hypothesis is supplied. -/
theorem mixed_energy_le_lp_norm (f : SchwartzMap ℝ ℂ) :
    (∫ x : ℝ, x^2 * ‖deriv f x‖^2) ≤ ‖f.toLp 2 volume‖^2 +
      (‖(SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => x^2) f).toLp 2 volume‖^2 +
        ‖(SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ f)).toLp 2 volume‖^2)/2 := by
  have hW : (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => x^2) f : ℝ → ℂ) =
      fun x => x^2 • f x := SchwartzMap.smulLeftCLM_apply (by fun_prop) f
  have hw := integral_mass_eq_norm (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => x^2) f)
  rw [hW] at hw
  have hd := integral_mass_eq_norm (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ f))
  change (∫ x : ℝ, ‖deriv (deriv f) x‖^2) = _ at hd
  simpa only [integral_mass_eq_norm, hw, hd] using mixed_energy_le f

/-- The same estimate with `‖x f′‖₂²` on the left, using the genuine
polynomial multiplier and derivative operators on Schwartz space. -/
theorem mixed_lp_norm_sq_le (f : SchwartzMap ℝ ℂ) :
    ‖(SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => x)
      (SchwartzMap.derivCLM ℂ ℂ f)).toLp 2 volume‖^2 ≤ ‖f.toLp 2 volume‖^2 +
      (‖(SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => x^2) f).toLp 2 volume‖^2 +
        ‖(SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ f)).toLp 2 volume‖^2)/2 := by
  have h := integral_mass_eq_norm (X (SchwartzMap.derivCLM ℂ ℂ f))
  have he (x : ℝ) : ‖X (SchwartzMap.derivCLM ℂ ℂ f) x‖^2 =
      x^2 * ‖deriv f x‖^2 := by
    rw [X_apply, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
      SchwartzMap.derivCLM_apply]
  simp_rw [he] at h
  change (∫ x : ℝ, x^2 * ‖deriv f x‖^2) =
    ‖(SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => x)
      (SchwartzMap.derivCLM ℂ ℂ f)).toLp 2 volume‖^2 at h
  rw [← h]
  exact mixed_energy_le_lp_norm f

end

end KNSMixedWeightedSchwartz
end MeyerGeneralProblem
