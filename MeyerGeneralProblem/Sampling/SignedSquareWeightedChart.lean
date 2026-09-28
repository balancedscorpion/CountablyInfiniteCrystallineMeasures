module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import all Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import all Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import all Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Function.JacobianOneDim
import all Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import all Mathlib.MeasureTheory.Integral.IntegralEqImproper

@[expose] public section

/-!
# The actual weighted inverse-square-root chart

The exterior chart in the retained supercritical proof is
`σ^((2k-1)/4) • h (ε * sqrt σ)`, for positive `σ` and ray sign `ε`.
This module computes actual derivatives, retaining their principal
coefficient, and proves the quadratic Jacobian identities. It does not
assert cutoff estimates, Sobolev-domain membership, or weighted transfer.
-/

namespace MeyerGeneralProblem

open Set MeasureTheory Filter
open scoped ContDiff Topology

noncomputable section

/-- A weighted actual derivative pulled back from the chosen physical ray. -/
def signedSquareChartMonomial (a ε : ℝ) (b : ℕ) (h : ℝ → ℂ) (σ : ℝ) : ℂ :=
  σ ^ a • iteratedDeriv b h (ε * Real.sqrt σ)

/-- The precise exterior weight in the signed-square transfer, before a
tail cutoff is multiplied in. The formula is used only at positive σ. -/
def signedSquareWeightedChart (k : ℕ) (ε : ℝ) (h : ℝ → ℂ) : ℝ → ℂ :=
  signedSquareChartMonomial ((2 * (k : ℝ) - 1) / 4) ε 0 h

/-- Exact first derivative of a chart monomial. The input derivative is
the actual derivative of h, not a postulated chain-rule expansion. -/
theorem hasDerivAt_signedSquareChartMonomial (a ε : ℝ) (b : ℕ) (h : ℝ → ℂ)
    {σ : ℝ} (hσ : 0 < σ)
    (hh : DifferentiableAt ℝ (iteratedDeriv b h) (ε * Real.sqrt σ)) :
    HasDerivAt (signedSquareChartMonomial a ε b h)
      (a • signedSquareChartMonomial (a - 1) ε b h σ +
        (ε / 2) • signedSquareChartMonomial (a - 1 / 2) ε (b + 1) h σ) σ := by
  have hsqrt : HasDerivAt Real.sqrt ((1 / 2 : ℝ) * σ ^ (-(1 / 2 : ℝ))) σ := by
    rw [show Real.sqrt = (fun x : ℝ => x ^ (1 / 2 : ℝ)) from funext Real.sqrt_eq_rpow]
    simpa only [show (1 / 2 : ℝ) - 1 = -(1 / 2) by norm_num] using
      (Real.hasDerivAt_rpow_const (p := (1 / 2 : ℝ)) (Or.inl hσ.ne'))
  have hd : HasDerivAt (iteratedDeriv b h)
      (iteratedDeriv (b + 1) h (ε * Real.sqrt σ)) (ε * Real.sqrt σ) := by
    rw [iteratedDeriv_succ]
    exact hh.hasDerivAt
  have hc := hd.scomp σ (hsqrt.const_mul ε)
  have hp := (Real.hasDerivAt_rpow_const (p := a) (Or.inl hσ.ne')).fun_smul hc
  apply hp.congr_deriv
  simp only [signedSquareChartMonomial, Function.comp_apply, smul_smul]
  rw [show a - 1 / 2 = a + -(1 / 2) by ring, Real.rpow_add hσ]
  module

/-- Exact second derivative at k=2, valid for any real multiplier ε.
The odd derivative changes sign between rays; the principal term contains
ε squared. No third derivative or smoothness of infinite order is needed. -/
theorem iteratedDeriv_two_signedSquareWeightedChart (ε : ℝ) {h : ℝ → ℂ}
    (hh : ContDiff ℝ 2 h) {σ : ℝ} (hσ : 0 < σ) :
    iteratedDeriv 2 (signedSquareWeightedChart 2 ε h) σ =
      (ε ^ 2 / 4) • signedSquareChartMonomial (-(1 / 4)) ε 2 h σ +
      (ε / 2) • signedSquareChartMonomial (-(3 / 4)) ε 1 h σ -
      (3 / 16 : ℝ) • signedSquareChartMonomial (-(5 / 4)) ε 0 h σ := by
  have hdiff (b : ℕ) (hb : b < 2) : Differentiable ℝ (iteratedDeriv b h) :=
    hh.differentiable_iteratedDeriv b (by exact_mod_cast hb)
  have heq : deriv (signedSquareWeightedChart 2 ε h) =ᶠ[𝓝 σ]
      (fun s => (3 / 4 : ℝ) • signedSquareChartMonomial (-(1 / 4)) ε 0 h s +
        (ε / 2) • signedSquareChartMonomial (1 / 4) ε 1 h s) := by
    filter_upwards [Ioi_mem_nhds hσ] with s hs
    have hd := (hasDerivAt_signedSquareChartMonomial (3 / 4) ε 0 h hs
      (hdiff 0 (by norm_num) _)).deriv
    norm_num [signedSquareWeightedChart] at hd ⊢
    exact hd
  have h₀ := (hasDerivAt_signedSquareChartMonomial (-(1 / 4)) ε 0 h hσ
    (hdiff 0 (by norm_num) _)).const_smul (3 / 4 : ℝ)
  have h₁ := (hasDerivAt_signedSquareChartMonomial (1 / 4) ε 1 h hσ
    (hdiff 1 (by norm_num) _)).const_smul (ε / 2)
  have hsum := h₀.add h₁
  conv_lhs => rw [show (2 : ℕ) = 1 + 1 by rfl, iteratedDeriv_succ, iteratedDeriv_one]
  rw [heq.deriv_eq]
  have hsumderiv := hsum.deriv
  simp only [Pi.add_def, Pi.smul_def] at hsumderiv
  rw [hsumderiv]
  norm_num only at *
  module

/-- Evaluation of each monomial at the physical square x², on x>0. -/
theorem signedSquareChartMonomial_sq (a ε : ℝ) (b : ℕ) (h : ℝ → ℂ)
    {x : ℝ} (hx : 0 < x) :
    signedSquareChartMonomial a ε b h (x ^ 2) =
      x ^ (2 * a) • iteratedDeriv b h (ε * x) := by
  rw [signedSquareChartMonomial, Real.sqrt_sq hx.le,
    ← Real.rpow_natCast_mul hx.le]
  norm_num

/-- The positive-ray k=2 formula, with the exact coefficients appearing
in the weighted-transfer proof. -/
theorem iteratedDeriv_two_signedSquareWeightedChart_pos {h : ℝ → ℂ}
    (hh : ContDiff ℝ 2 h) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv 2 (signedSquareWeightedChart 2 1 h) (x ^ 2) =
      (1 / 4 : ℝ) • (x ^ (-(1 / 2 : ℝ)) • iteratedDeriv 2 h x) +
      (1 / 2 : ℝ) • (x ^ (-(3 / 2 : ℝ)) • deriv h x) -
      (3 / 16 : ℝ) • (x ^ (-(5 / 2 : ℝ)) • h x) := by
  rw [iteratedDeriv_two_signedSquareWeightedChart 1 hh (sq_pos_of_pos hx)]
  simp only [signedSquareChartMonomial_sq _ _ _ _ hx]
  norm_num

/-- The negative-ray k=2 formula. Only the first-derivative term changes
sign; the second-derivative principal coefficient remains positive 1/4. -/
theorem iteratedDeriv_two_signedSquareWeightedChart_neg {h : ℝ → ℂ}
    (hh : ContDiff ℝ 2 h) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv 2 (signedSquareWeightedChart 2 (-1) h) (x ^ 2) =
      (1 / 4 : ℝ) • (x ^ (-(1 / 2 : ℝ)) • iteratedDeriv 2 h (-x)) -
      (1 / 2 : ℝ) • (x ^ (-(3 / 2 : ℝ)) • deriv h (-x)) -
      (3 / 16 : ℝ) • (x ^ (-(5 / 2 : ℝ)) • h (-x)) := by
  rw [iteratedDeriv_two_signedSquareWeightedChart (-1) hh (sq_pos_of_pos hx)]
  simp only [signedSquareChartMonomial_sq _ _ _ _ hx]
  norm_num [sub_eq_add_neg]

/-- The exact second-derivative principal term, including the ray
multiplier squared, as a function on the signed-square coordinate. -/
def signedSquareWeightedChartLeadingTwo (ε : ℝ) (h : ℝ → ℂ) (σ : ℝ) : ℂ :=
  (ε ^ 2 / 4) • signedSquareChartMonomial (-(1 / 4)) ε 2 h σ

/-- The square map identifies a positive physical tail with its
signed-square tail; no finite-prefix point is silently added. -/
theorem image_sq_Ioi_of_nonneg {R : ℝ} (hR : 0 ≤ R) :
    (fun x : ℝ => x ^ 2) '' Ioi R = Ioi (R ^ 2) := by
  ext σ
  constructor
  · rintro ⟨x, hx, rfl⟩
    change R < x at hx
    change R ^ 2 < x ^ 2
    nlinarith
  · intro hσ
    change R ^ 2 < σ at hσ
    have hσ0 : 0 ≤ σ := le_of_lt (lt_of_le_of_lt (sq_nonneg R) hσ)
    refine ⟨Real.sqrt σ, ?_, Real.sq_sqrt hσ0⟩
    change R < Real.sqrt σ
    nlinarith [Real.sq_sqrt hσ0, Real.sqrt_nonneg σ]

/-- Actual one-dimensional change of variables on a positive tail:
dσ = 2x dx. The equality also preserves Bochner nonintegrability. -/
theorem integral_signedSquare_jacobian (f : ℝ → ℝ) {R : ℝ} (hR : 0 ≤ R) :
    (∫ σ in Ioi (R ^ 2), f σ) = ∫ x in Ioi R, (2 * x) * f (x ^ 2) := by
  have hderiv (x : ℝ) (_hx : x ∈ Ioi R) :
      HasDerivWithinAt (fun x : ℝ => x ^ 2) (2 * x) (Ioi R) x := by
    simpa using (hasDerivAt_pow 2 x).hasDerivWithinAt
  have hinj : InjOn (fun x : ℝ => x ^ 2) (Ioi R) := by
    intro x hx y hy heq
    change R < x at hx
    change R < y at hy
    nlinarith
  have hj := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv hinj f
  rw [image_sq_Ioi_of_nonneg hR] at hj
  rw [hj]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  change |2 * x| * f (x ^ 2) = (2 * x) * f (x ^ 2)
  rw [abs_of_nonneg (by have := hR.trans hx.le; positivity)]

/-- Pointwise mass/Jacobian identity for k=2. The factor two is the same
one that will divide the derivative energy in the weighted transfer. -/
theorem signedSquareWeightedChart_two_mass_jacobian (ε : ℝ) (h : ℝ → ℂ)
    {x : ℝ} (hx : 0 < x) :
    (2 * x) * ‖signedSquareWeightedChart 2 ε h (x ^ 2)‖ ^ 2 =
      2 * (x ^ 4 * ‖h (ε * x)‖ ^ 2) := by
  norm_num [signedSquareWeightedChart, signedSquareChartMonomial_sq _ _ _ _ hx]
  rw [abs_of_nonneg (Real.rpow_nonneg hx.le _), mul_pow,
    ← Real.rpow_mul_natCast hx.le]
  norm_num
  ring

/-- Pointwise principal-energy/Jacobian identity on either actual ray.
The coefficient is 1/8 before division by the mass Jacobian's factor two. -/
theorem signedSquareWeightedChartLeadingTwo_jacobian {ε : ℝ} (hε : ε ^ 2 = 1)
    (h : ℝ → ℂ) {x : ℝ} (hx : 0 < x) :
    (2 * x) * ‖signedSquareWeightedChartLeadingTwo ε h (x ^ 2)‖ ^ 2 =
      (1 / 8 : ℝ) * ‖iteratedDeriv 2 h (ε * x)‖ ^ 2 := by
  rw [signedSquareWeightedChartLeadingTwo, hε,
    signedSquareChartMonomial_sq _ _ _ _ hx]
  norm_num only
  rw [norm_smul, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4),
    Real.norm_of_nonneg (Real.rpow_nonneg hx.le _), mul_pow, mul_pow,
    ← Real.rpow_mul_natCast hx.le]
  norm_num
  rw [Real.rpow_neg_one]
  field_simp
  ring

/-- The actual chart's mass integral under quadratic substitution. -/
theorem integral_signedSquareWeightedChart_two_mass (ε : ℝ) (h : ℝ → ℂ)
    {R : ℝ} (hR : 0 ≤ R) :
    (∫ σ in Ioi (R ^ 2), ‖signedSquareWeightedChart 2 ε h σ‖ ^ 2) =
      2 * ∫ x in Ioi R, x ^ 4 * ‖h (ε * x)‖ ^ 2 := by
  rw [integral_signedSquare_jacobian _ hR, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  exact signedSquareWeightedChart_two_mass_jacobian ε h (lt_of_le_of_lt hR hx)

/-- Leading derivative energy on a single ray, with its exact coefficient. -/
theorem integral_signedSquareWeightedChartLeadingTwo {ε : ℝ} (hε : ε ^ 2 = 1)
    (h : ℝ → ℂ) {R : ℝ} (hR : 0 ≤ R) :
    (∫ σ in Ioi (R ^ 2), ‖signedSquareWeightedChartLeadingTwo ε h σ‖ ^ 2) =
      (1 / 8 : ℝ) * ∫ x in Ioi R, ‖iteratedDeriv 2 h (ε * x)‖ ^ 2 := by
  rw [integral_signedSquare_jacobian _ hR, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  exact signedSquareWeightedChartLeadingTwo_jacobian hε h (lt_of_le_of_lt hR hx)

/-- Reflection carries the positive physical tail to the negative tail,
with unit absolute Jacobian. -/
theorem integral_reflected_positive_tail (f : ℝ → ℝ) (R : ℝ) :
    (∫ x in Ioi R, f (-x)) = ∫ x in Iio (-R), f x := by
  have himage : (fun x : ℝ => -x) '' Ioi R = Iio (-R) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change R < y at hy
      change -y < -R
      linarith
    · intro hx
      change x < -R at hx
      refine ⟨-x, ?_, neg_neg x⟩
      change R < -x
      linarith
  have hderiv (x : ℝ) (_hx : x ∈ Ioi R) :
      HasDerivWithinAt (fun x : ℝ => -x) (-1) (Ioi R) x :=
    (hasDerivAt_id x).neg.hasDerivWithinAt
  have hj := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv
    (neg_injective.injOn : InjOn (fun x : ℝ => -x) (Ioi R)) f
  simpa only [himage, abs_neg, abs_one, one_smul] using hj.symm

/-- Combining the two actual ray energies and dividing by the mass
Jacobian gives 1/16 times the sum of the disjoint physical tail energies.
No whole-line energy has been substituted separately for each ray. -/
theorem signedSquareWeightedChart_twoRay_leading_energy (h : ℝ → ℂ)
    {R : ℝ} (hR : 0 ≤ R) :
    (1 / 2 : ℝ) *
      ((∫ σ in Ioi (R ^ 2), ‖signedSquareWeightedChartLeadingTwo 1 h σ‖ ^ 2) +
        (∫ σ in Ioi (R ^ 2), ‖signedSquareWeightedChartLeadingTwo (-1) h σ‖ ^ 2)) =
      (1 / 16 : ℝ) *
        ((∫ x in Ioi R, ‖iteratedDeriv 2 h x‖ ^ 2) +
          (∫ x in Iio (-R), ‖iteratedDeriv 2 h x‖ ^ 2)) := by
  rw [integral_signedSquareWeightedChartLeadingTwo (by norm_num : (1 : ℝ)^2 = 1) h hR,
    integral_signedSquareWeightedChartLeadingTwo (by norm_num : (-1 : ℝ)^2 = 1) h hR]
  simp only [one_mul, neg_one_mul]
  rw [integral_reflected_positive_tail (fun x => ‖iteratedDeriv 2 h x‖ ^ 2) R]
  ring

/-- For a genuinely integrable derivative energy, the disjoint ray sum is
the symmetric tail integral. Thus the principal coefficient remains 1/16
on the full two-sided tail, not 1/8. -/
theorem signedSquareWeightedChart_symmetric_leading_energy (h : ℝ → ℂ)
    (hh : Integrable (fun x => ‖iteratedDeriv 2 h x‖ ^ 2)) {R : ℝ} (hR : 0 ≤ R) :
    (1 / 2 : ℝ) *
      ((∫ σ in Ioi (R ^ 2), ‖signedSquareWeightedChartLeadingTwo 1 h σ‖ ^ 2) +
        (∫ σ in Ioi (R ^ 2), ‖signedSquareWeightedChartLeadingTwo (-1) h σ‖ ^ 2)) =
      (1 / 16 : ℝ) * ∫ x in {x : ℝ | R < |x|}, ‖iteratedDeriv 2 h x‖ ^ 2 := by
  rw [signedSquareWeightedChart_twoRay_leading_energy h hR]
  have hset : {x : ℝ | R < |x|} = Ioi R ∪ Iio (-R) := by
    ext x
    simp only [mem_ofPred_eq, mem_union, mem_Ioi, mem_Iio, lt_abs]
    constructor <;> intro hx
    · rcases hx with hx | hx
      · exact Or.inl hx
      · exact Or.inr (by linarith)
    · rcases hx with hx | hx
      · exact Or.inl hx
      · exact Or.inr (by linarith)
  have hdisjoint : Disjoint (Ioi R) (Iio (-R)) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    change R < x at hx
    change x < -R at hy
    linarith
  rw [hset, setIntegral_union hdisjoint measurableSet_Iio hh.integrableOn hh.integrableOn]

/-- Finite differentiation recursion for the actual inverse-square-root
chart. Each step either differentiates the weight or the pulled-back h. -/
def signedSquareChartExpansion : ℕ → ℝ → ℝ → ℕ → (ℝ → ℂ) → ℝ → ℂ
  | 0, a, ε, b, h, σ => signedSquareChartMonomial a ε b h σ
  | n + 1, a, ε, b, h, σ =>
      a • signedSquareChartExpansion n (a - 1) ε b h σ +
        (ε / 2) • signedSquareChartExpansion n (a - 1 / 2) ε (b + 1) h σ

private theorem chart_contDiff_iteratedDeriv {h : ℝ → ℂ}
    (hh : ContDiff ℝ ∞ h) (b : ℕ) : ContDiff ℝ ∞ (iteratedDeriv b h) := by
  induction b with
  | zero => simpa using hh
  | succ b ih =>
    rw [iteratedDeriv_succ]
    exact (show ContDiff ℝ (∞ + 1) (iteratedDeriv b h) by simpa using ih).deriv'

/-- Chart monomials are smooth locally on the positive coordinate ray;
no smoothness is claimed at the square-root singularity σ=0. -/
theorem contDiffAt_signedSquareChartMonomial (a ε : ℝ) (b : ℕ) {h : ℝ → ℂ}
    (hh : ContDiff ℝ ∞ h) {σ : ℝ} (hσ : 0 < σ) :
    ContDiffAt ℝ ∞ (signedSquareChartMonomial a ε b h) σ := by
  exact (Real.contDiffAt_rpow_const_of_ne hσ.ne').smul
    ((chart_contDiff_iteratedDeriv hh b).contDiffAt.comp σ
      (contDiffAt_const.mul (Real.contDiffAt_sqrt (n := ∞) hσ.ne')))

/-- The finite chart recursion equals the actual iterated derivative on
σ>0. Infinite smoothness is used only for this optional all-order formula;
the k=2 theorem above requires just C2. -/
theorem iteratedDeriv_signedSquareChartMonomial (n : ℕ) (a ε : ℝ) (b : ℕ)
    {h : ℝ → ℂ} (hh : ContDiff ℝ ∞ h) {σ : ℝ} (hσ : 0 < σ) :
    iteratedDeriv n (signedSquareChartMonomial a ε b h) σ =
      signedSquareChartExpansion n a ε b h σ := by
  induction n generalizing a b with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ']
    have heq : deriv (signedSquareChartMonomial a ε b h) =ᶠ[𝓝 σ]
        (fun s => a • signedSquareChartMonomial (a - 1) ε b h s +
          (ε / 2) • signedSquareChartMonomial (a - 1 / 2) ε (b + 1) h s) := by
      filter_upwards [Ioi_mem_nhds hσ] with s hs
      exact (hasDerivAt_signedSquareChartMonomial a ε b h hs
        ((chart_contDiff_iteratedDeriv hh b).differentiable (by simp) _)).deriv
    rw [heq.iteratedDeriv_eq n]
    rw [iteratedDeriv_fun_add
      (((contDiffAt_signedSquareChartMonomial (a - 1) ε b hh hσ).of_le (by simp)).const_smul a)
      (((contDiffAt_signedSquareChartMonomial (a - 1 / 2) ε (b + 1) hh hσ).of_le
        (by simp)).const_smul (ε / 2))]
    simp only [iteratedDeriv_fun_const_smul_field, ih, signedSquareChartExpansion]

/-- The lower-order terms are an explicit recursion, not the difference
between an unknown derivative and an asserted principal term. -/
def signedSquareChartLowerTerms : ℕ → ℝ → ℝ → ℕ → (ℝ → ℂ) → ℝ → ℂ
  | 0, _, _, _, _, _ => 0
  | n + 1, a, ε, b, h, σ =>
      a • signedSquareChartExpansion n (a - 1) ε b h σ +
        (ε / 2) • signedSquareChartLowerTerms n (a - 1 / 2) ε (b + 1) h σ

/-- Extracting the branch that always differentiates h gives the exact
principal coefficient `(ε/2)^n`, with no unspecified multiplicative bound. -/
theorem signedSquareChartExpansion_leading (n : ℕ) (a ε : ℝ) (b : ℕ)
    (h : ℝ → ℂ) (σ : ℝ) :
    signedSquareChartExpansion n a ε b h σ =
      (ε / 2) ^ n • signedSquareChartMonomial (a - (n : ℝ) / 2) ε (b + n) h σ +
        signedSquareChartLowerTerms n a ε b h σ := by
  induction n generalizing a b with
  | zero => simp [signedSquareChartExpansion, signedSquareChartLowerTerms]
  | succ n ih =>
    simp only [signedSquareChartExpansion, signedSquareChartLowerTerms]
    rw [ih (a - 1 / 2) (b + 1)]
    have ha : a - 1 / 2 - (n : ℝ) / 2 = a - ((n + 1 : ℕ) : ℝ) / 2 := by
      push_cast
      ring
    rw [ha, show b + 1 + n = b + (n + 1) by omega]
    simp only [smul_add, smul_smul, pow_succ]
    module

/-- The full recursion depends only on the actual derivatives from b
through b+n at the pulled-back point. -/
theorem signedSquareChartExpansion_congr (n : ℕ) (a ε : ℝ) (b : ℕ)
    (h g : ℝ → ℂ) (σ : ℝ)
    (hsame : ∀ j, b ≤ j → j ≤ b + n →
      iteratedDeriv j h (ε * Real.sqrt σ) = iteratedDeriv j g (ε * Real.sqrt σ)) :
    signedSquareChartExpansion n a ε b h σ = signedSquareChartExpansion n a ε b g σ := by
  induction n generalizing a b with
  | zero => simp [signedSquareChartExpansion, signedSquareChartMonomial, hsame b le_rfl (by omega)]
  | succ n ih =>
    simp only [signedSquareChartExpansion]
    rw [ih (a - 1) b (fun j hj hj' => hsame j hj (by omega)),
      ih (a - 1 / 2) (b + 1) (fun j hj hj' => hsame j (by omega) (by omega))]

/-- The explicit remainder really uses only derivatives strictly below
the principal order b+n; no highest derivative is hidden in it. -/
theorem signedSquareChartLowerTerms_congr (n : ℕ) (a ε : ℝ) (b : ℕ)
    (h g : ℝ → ℂ) (σ : ℝ)
    (hsame : ∀ j, b ≤ j → j < b + n →
      iteratedDeriv j h (ε * Real.sqrt σ) = iteratedDeriv j g (ε * Real.sqrt σ)) :
    signedSquareChartLowerTerms n a ε b h σ = signedSquareChartLowerTerms n a ε b g σ := by
  induction n generalizing a b with
  | zero => rfl
  | succ n ih =>
    simp only [signedSquareChartLowerTerms]
    rw [signedSquareChartExpansion_congr n (a - 1) ε b h g σ
      (fun j hj hj' => hsame j hj (by omega)),
      ih (a - 1 / 2) (b + 1) (fun j hj hj' => hsame j (by omega) (by omega))]

/-- At the actual transfer weight the principal σ-power is always -1/4.
The positive-ray coefficient is 2^(-k), and the negative ray adds (-1)^k. -/
theorem iteratedDeriv_signedSquareWeightedChart_leading (k : ℕ) (ε : ℝ)
    {h : ℝ → ℂ} (hh : ContDiff ℝ ∞ h) {σ : ℝ} (hσ : 0 < σ) :
    iteratedDeriv k (signedSquareWeightedChart k ε h) σ =
      (ε / 2) ^ k • (σ ^ (-(1 / 4 : ℝ)) • iteratedDeriv k h (ε * Real.sqrt σ)) +
        signedSquareChartLowerTerms k ((2 * (k : ℝ) - 1) / 4) ε 0 h σ := by
  rw [signedSquareWeightedChart, iteratedDeriv_signedSquareChartMonomial k _ ε 0 hh hσ,
    signedSquareChartExpansion_leading]
  rw [show (2 * (k : ℝ) - 1) / 4 - (k : ℝ) / 2 = -(1 / 4 : ℝ) by ring]
  simp only [signedSquareChartMonomial, zero_add]

/-- In the physical coordinate the general principal term is
`ε^k / 2^k • x^(-1/2) • h^(k)(εx)`. The same explicit lower-order
recursion is retained, so the exact leading constant is not hidden. -/
theorem iteratedDeriv_signedSquareWeightedChart_leading_sq (k : ℕ) (ε : ℝ)
    {h : ℝ → ℂ} (hh : ContDiff ℝ ∞ h) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv k (signedSquareWeightedChart k ε h) (x ^ 2) =
      (ε ^ k / (2 : ℝ) ^ k) • (x ^ (-(1 / 2 : ℝ)) • iteratedDeriv k h (ε * x)) +
        signedSquareChartLowerTerms k ((2 * (k : ℝ) - 1) / 4) ε 0 h (x ^ 2) := by
  rw [iteratedDeriv_signedSquareWeightedChart_leading k ε hh (sq_pos_of_pos hx),
    Real.sqrt_sq hx.le, div_pow, ← Real.rpow_natCast_mul hx.le]
  norm_num

end

end MeyerGeneralProblem
