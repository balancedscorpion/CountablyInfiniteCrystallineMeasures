module

public import MeyerGeneralProblem.Sampling.KNSGraphSpaceSmooth
public import MeyerGeneralProblem.Sampling.KNSMixedWeightedSchwartz
public import MeyerGeneralProblem.Hermite.CutoffNorm

@[expose] public section

/-!
# Same-order Schwartz comparison: Hermite order one to KNS order two

The order-two mixed integration-by-parts identity controls the two pure
order-two energies by the shifted harmonic oscillator. The actual KNS
graph retains its negative-2π Fourier normalization: its derivative term
has coefficient `(2π)^(-4)`. The resulting comparison has safe constant 3.
Only actual Schwartz functions are considered. No extension operator,
surjectivity or density in the complete graph is asserted here.
-/

namespace MeyerGeneralProblem
namespace KNSGraphSchwartzComparison

noncomputable section

open MeasureTheory
open scoped InnerProductSpace ContDiff

def D (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ f)

def W (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  coordinateMultiplicationCLM (coordinateMultiplicationCLM f)

private theorem D_apply (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    D f x = deriv (deriv f) x := rfl

private theorem W_apply (f : SchwartzMap ℝ ℂ) (x : ℝ) : W f x = x^2 • f x := by
  simp only [W, coordinateMultiplicationCLM_apply, Complex.real_smul,
    pow_two, Complex.ofReal_mul, mul_assoc]

def H₀ (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  (4 * Real.pi^2 : ℝ) • W f - D f

private theorem mass_eq_norm (f : SchwartzMap ℝ ℂ) :
    (∫ x : ℝ, ‖f x‖^2) = ‖f.toLp 2 volume‖^2 :=
  integral_norm_sq_eq_toLp_norm_sq_complex (f.memLp 2)

private theorem integrable_mass (f : SchwartzMap ℝ ℂ) : Integrable (fun x => ‖f x‖^2) :=
  integrable_norm_sq_of_memLp_complex (f.memLp 2)

private theorem oscillator_norm (f : SchwartzMap ℝ ℂ) :
    ‖(hermiteGraphOperator f).toLp 2 volume‖ = ‖schwartzToHermiteScale 1 f‖ := by
  rw [← norm_schwartzToHermiteScale_zero, schwartzToHermiteScale_graph]

private theorem mass_norm_le (f : SchwartzMap ℝ ℂ) :
    ‖f.toLp 2 volume‖ ≤ ‖schwartzToHermiteScale 1 f‖ := by
  rw [← norm_schwartzToHermiteScale_zero]
  exact schwartzToHermiteScale_norm_mono 0 f

private theorem pure_energy_identity (f : SchwartzMap ℝ ℂ) :
    ‖(D f).toLp 2 volume‖^2 + 16 * Real.pi^4 * ‖(W f).toLp 2 volume‖^2 =
      ‖(H₀ f).toLp 2 volume‖^2 + 8 * Real.pi^2 * ‖f.toLp 2 volume‖^2 -
        8 * Real.pi^2 * (∫ x : ℝ, x^2 * ‖deriv f x‖^2) := by
  have hc : Integrable (fun x => ⟪W f x, D f x⟫_ℝ) :=
    (SchwartzMap.pairing (innerSL ℝ) (W f) (D f)).integrable
  have he (x : ℝ) : ‖H₀ f x‖^2 =
      16 * Real.pi^4 * ‖W f x‖^2 - 8 * Real.pi^2 * ⟪W f x, D f x⟫_ℝ + ‖D f x‖^2 := by
    change ‖(4 * Real.pi^2 : ℝ) • W f x - D f x‖^2 = _
    rw [norm_sub_sq_real, norm_smul, mul_pow, Real.norm_eq_abs,
      abs_of_nonneg (by positivity), real_inner_smul_left]
    ring
  have hH := mass_eq_norm (H₀ f)
  simp_rw [he] at hH
  have hi : Integrable (fun x => 16 * Real.pi^4 * ‖W f x‖^2 -
      8 * Real.pi^2 * ⟪W f x, D f x⟫_ℝ) := by
    simpa only [Pi.sub_def] using
      ((integrable_mass (W f)).const_mul (16 * Real.pi^4)).sub (hc.const_mul (8 * Real.pi^2))
  rw [integral_add hi
    (integrable_mass (D f)), integral_sub ((integrable_mass (W f)).const_mul _) (hc.const_mul _),
    integral_const_mul, integral_const_mul, mass_eq_norm, mass_eq_norm] at hH
  have hi := KNSMixedWeightedSchwartz.mixed_energy_identity f
  have hcross : (∫ x : ℝ, ⟪x^2 • f x, deriv (deriv f) x⟫_ℝ) =
      ∫ x : ℝ, ⟪W f x, D f x⟫_ℝ := by simp only [W_apply, D_apply]
  rw [mass_eq_norm, hcross] at hi
  nlinarith

private theorem H₀_eq (f : SchwartzMap ℝ ℂ) :
    H₀ f = (4 * Real.pi : ℝ) • (hermiteGraphOperator f - (1/2 : ℝ) • f) := by
  ext x
  simp only [H₀, W, D, hermiteGraphOperator, add_apply, smul_apply, neg_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, sub_apply,
    Complex.real_smul, smul_eq_mul,
    Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_ofNat, Complex.ofReal_div,
    Complex.ofReal_one]
  field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
  ring

private theorem unshifted_norm_le (f : SchwartzMap ℝ ℂ) :
    ‖(H₀ f).toLp 2 volume‖ ≤ 6 * Real.pi * ‖schwartzToHermiteScale 1 f‖ := by
  have he : (H₀ f).toLp 2 volume = (4 * Real.pi : ℝ) •
      ((hermiteGraphOperator f).toLp 2 volume - (1/2 : ℝ) • f.toLp 2 volume) := by
    change (SchwartzMap.toLpCLM ℝ ℂ 2 volume) (H₀ f) = _
    rw [H₀_eq, map_smul, map_sub, map_smul]
    rfl
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hb := norm_sub_le ((hermiteGraphOperator f).toLp 2 volume)
    ((1/2 : ℝ) • f.toLp 2 volume)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num), oscillator_norm] at hb
  have hm := mass_norm_le f
  nlinarith [mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 4 * Real.pi),
    mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ 2 * Real.pi)]

private theorem pure_energy_le (f : SchwartzMap ℝ ℂ) :
    ‖(D f).toLp 2 volume‖^2 + 16 * Real.pi^4 * ‖(W f).toLp 2 volume‖^2 ≤
      44 * Real.pi^2 * ‖schwartzToHermiteScale 1 f‖^2 := by
  rw [pure_energy_identity]
  have hH := unshifted_norm_le f
  have hm := mass_norm_le f
  have hH2 := sq_le_sq₀ (norm_nonneg _) (by positivity) |>.2 hH
  have hm2 := sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.2 hm
  have hI : 0 ≤ ∫ x : ℝ, x^2 * ‖deriv f x‖^2 := integral_nonneg (fun x => by positivity)
  nlinarith [mul_le_mul_of_nonneg_left hm2 (by positivity : 0 ≤ 8 * Real.pi^2),
    mul_nonneg (by positivity : 0 ≤ 8 * Real.pi^2) hI]

/-- The actual graph norm at order two, expressed using the physical
second derivative with its exact negative-2π Fourier factor `(2π)^(-4)`.
This identity is for the existing Schwartz embedding, not a replacement graph. -/
theorem norm_schwartzEmbedding_two_sq (f : SchwartzMap ℝ ℂ) :
    ‖KNSGraphSpace.schwartzEmbedding 2 f‖^2 = 2 * ‖f.toLp 2 volume‖^2 +
      ‖(coordinateMultiplicationCLM (coordinateMultiplicationCLM f)).toLp 2 volume‖^2 +
        ((2 * Real.pi)^4)⁻¹ *
          ‖(SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ f)).toLp 2 volume‖^2 := by
  have hWfun : (W f : ℝ → ℂ) = fun x : ℝ => (x : ℂ)^2 * f x := by
    funext x
    simp only [W, coordinateMultiplicationCLM_apply, pow_two, mul_assoc]
  have hDfun : (D f : ℝ → ℂ) = iteratedDeriv 2 f := by
    funext x
    rw [D_apply, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero]
  have hW : MemLp (fun x : ℝ => (x : ℂ)^2 * f x) 2 := by
    rw [← hWfun]
    exact (W f).memLp 2
  have hD : MemLp (iteratedDeriv 2 f) 2 := by
    rw [← hDfun]
    exact (D f).memLp 2
  have hWlp : hW.toLp = (W f).toLp 2 volume := by
    apply Lp.ext
    exact hW.coeFn_toLp.trans ((W f).coeFn_toLp 2 volume |>.trans (by rw [hWfun])).symm
  have hDlp : hD.toLp = (D f).toLp 2 volume := by
    apply Lp.ext
    exact hD.coeFn_toLp.trans ((D f).coeFn_toLp 2 volume |>.trans (by rw [hDfun])).symm
  have hf : ContDiff ℝ ∞ (f : ℝ → ℂ) := by simpa using f.smooth (⊤ : ℕ∞)
  have he : KNSGraphSpace.schwartzEmbedding 2 f =
      KNSGraphSpace.ofSmooth 2 hf (f.memLp 2) hW hD := by
    apply KNSGraphSpace.physical_injective 2
    rfl
  rw [he, KNSGraphSpace.norm_ofSmooth_sq, hWlp, hDlp]
  change 2 * ‖f.toLp 2 volume‖^2 + ‖(W f).toLp 2 volume‖^2 +
    (((2 * Real.pi)^2)⁻¹ * ‖(D f).toLp 2 volume‖)^2 =
      2 * ‖f.toLp 2 volume‖^2 + ‖(W f).toLp 2 volume‖^2 +
        ((2 * Real.pi)^4)⁻¹ * ‖(D f).toLp 2 volume‖^2
  field_simp

/-- Hermite order one controls the actual KNS graph of differential/weight
order two, with a safe universal constant 3. There is no increase of the
physical differential order and no graph-density assumption. -/
theorem norm_schwartzEmbedding_two_le (f : SchwartzMap ℝ ℂ) :
    ‖KNSGraphSpace.schwartzEmbedding 2 f‖ ≤ 3 * ‖schwartzToHermiteScale 1 f‖ := by
  have hE : 16 * Real.pi^4 * ‖KNSGraphSpace.schwartzEmbedding 2 f‖^2 =
      32 * Real.pi^4 * ‖f.toLp 2 volume‖^2 + ‖(D f).toLp 2 volume‖^2 +
        16 * Real.pi^4 * ‖(W f).toLp 2 volume‖^2 := by
    rw [norm_schwartzEmbedding_two_sq]
    change 16 * Real.pi^4 * (2 * ‖f.toLp 2 volume‖^2 + ‖(W f).toLp 2 volume‖^2 +
      ((2 * Real.pi)^4)⁻¹ * ‖(D f).toLp 2 volume‖^2) = _
    field_simp
    ring
  have hp := pure_energy_le f
  have hm2 := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 (mass_norm_le f)
  have hm := mul_le_mul_of_nonneg_left hm2 (by positivity : 0 ≤ 32 * Real.pi^4)
  have hcoef : 32 * Real.pi^4 + 44 * Real.pi^2 ≤ 9 * (16 * Real.pi^4) := by
    have hpi : 1 ≤ Real.pi^2 := by nlinarith [Real.two_le_pi]
    nlinarith [sq_nonneg (Real.pi^2 - 1)]
  have hc := mul_le_mul_of_nonneg_right hcoef (sq_nonneg ‖schwartzToHermiteScale 1 f‖)
  have hlarge : 16 * Real.pi^4 * ‖KNSGraphSpace.schwartzEmbedding 2 f‖^2 ≤
      16 * Real.pi^4 * (3 * ‖schwartzToHermiteScale 1 f‖)^2 := by
    nlinarith only [hE, hp, hm, hc]
  have hs := (mul_le_mul_iff_right₀ (by positivity : 0 < 16 * Real.pi^4)).mp hlarge
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hs

end
end KNSGraphSchwartzComparison
end MeyerGeneralProblem
