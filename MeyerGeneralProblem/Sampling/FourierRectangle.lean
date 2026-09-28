module

public import MeyerGeneralProblem.Sampling.LocalSobolev
public import Mathlib.Analysis.CStarAlgebra.Matrix
import all Mathlib.Analysis.CStarAlgebra.Matrix

@[expose] public section

/-!
# Irregular separated Fourier rectangles

This module combines local Sobolev sampling with the upper large sieve.  It
controls the full finite Fourier matrix in `ℓ²` operator norm, retaining all
coherent phase recombination and assuming only separation and interval
diameter bounds.
-/

namespace MeyerGeneralProblem

open MeasureTheory ComplexConjugate

noncomputable section

/-- The standard complex normed additive group, fixed locally so real
calculus instances elaborate definitionally consistently. -/
local instance : NormedAddCommGroup ℂ := Complex.instNormedAddCommGroup

open scoped BigOperators Matrix.Norms.L2Operator

/-- The scale-free absolute constant used by the arbitrary-interval upper
large sieve. -/
def fourierIntervalLargeSieveConstant : ℝ :=
  8 * (Real.cos (Real.pi / 4))⁻¹

theorem fourierIntervalLargeSieveConstant_pos :
    0 < fourierIntervalLargeSieveConstant := by
  unfold fourierIntervalLargeSieveConstant
  rw [Real.cos_pi_div_four]
  positivity

/-- Scaled upper cosine-window estimate.  Unlike the unit-window convenience
theorem, this retains the window radius `a`. -/
theorem integral_cosineWeight_mul_norm_sq_le_of_separated_scaled
    {a d : ℝ} (ha : 0 < a) (had : 1 < 2 * a * d)
    {n : ℕ} (x : Fin n → ℝ)
    (hsep : PairwiseFrequencySeparated x d) (c : Fin n → ℂ) :
    (∫ η : ℝ in Set.Icc (-a) a,
        cosineInghamWeight a η *
          ‖gramFourierPolynomial x c η‖ ^ 2) ≤
      (4 * a / Real.pi) * (1 + (2 * a * d)⁻¹ ^ 2) *
        ∑ i, ‖c i‖ ^ 2 := by
  let q : ℝ := 2 * a * d
  let D : ℝ := 4 * a / Real.pi
  let R : ℝ := D * q⁻¹ ^ 2
  let K : Fin n → Fin n → ℂ := fun i j =>
    cosineWindowKernel a (x j - x i)
  have hq : 1 < q := had
  have hscaled (i j : Fin n) (hij : i ≠ j) :
      q ≤ |2 * a * (x j - x i)| := by
    have ha0 : 0 ≤ 2 * a := by positivity
    calc
      q = (2 * a) * d := by rfl
      _ ≤ (2 * a) * |x j - x i| := by
        apply mul_le_mul_of_nonneg_left _ ha0
        simpa only [abs_sub_comm] using hsep i j hij
      _ = |2 * a * (x j - x i)| := by
        rw [abs_mul, abs_of_nonneg ha0]
  have hdiag (i : Fin n) : K i i = (D : ℂ) := by
    dsimp only [K, D]
    simpa using cosineWindowKernel_zero ha
  have hsymm (i j : Fin n) : ‖K i j‖ = ‖K j i‖ := by
    by_cases hij : i = j
    · subst j
      rfl
    · have hfar : 1 < |2 * a * (x j - x i)| :=
        hq.trans_le (hscaled i j hij)
      dsimp only [K]
      rw [show x i - x j = -(x j - x i) by ring,
        cosineWindowKernel_neg_of_far ha hfar]
  have hrow (i : Fin n) :
      ∑ j ∈ Finset.univ.erase i, ‖K i j‖ ≤ R := by
    dsimp only [K, R, D]
    exact sum_norm_cosineWindowKernel_offdiag_le Finset.univ x ha hq
      (fun i _ j _ hij => hscaled i j hij) i (Finset.mem_univ i)
  have hupper := finite_kernel_quadratic_re_le_of_offdiag_row
    K c D R hdiag hsymm hrow
  rw [integral_cosineWeight_mul_norm_sq_eq_kernel_re]
  calc
    (∑ i, ∑ j, conj (c i) * c j *
        cosineWindowKernel a (x j - x i)).re ≤
        (D + R) * ∑ i, ‖c i‖ ^ 2 := by
      simpa only [K] using hupper
    _ = (4 * a / Real.pi) * (1 + (2 * a * d)⁻¹ ^ 2) *
        ∑ i, ‖c i‖ ^ 2 := by
      dsimp only [D, R, q]
      ring

/-- On the central half of a positive cosine window, the taper is bounded
below by `cos (π/4)`. -/
theorem cos_pi_div_four_le_cosineInghamWeight
    {a η : ℝ} (ha : 0 < a)
    (hη : η ∈ Set.Icc (-(a / 2)) (a / 2)) :
    Real.cos (Real.pi / 4) ≤ cosineInghamWeight a η := by
  have hηabs : |η| ≤ a / 2 := by
    rw [abs_le]
    exact hη
  have harg : |Real.pi * η / (2 * a)| ≤ Real.pi / 4 := by
    rw [abs_div, abs_mul, abs_of_pos Real.pi_pos,
      abs_of_pos (by positivity : (0 : ℝ) < 2 * a)]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * a)]
    nlinarith [mul_le_mul_of_nonneg_left hηabs Real.pi_pos.le]
  unfold cosineInghamWeight
  have hπ : Real.pi / 4 ≤ Real.pi := by nlinarith [Real.pi_pos]
  have hcos := Real.cos_le_cos_of_nonneg_of_le_pi
    (abs_nonneg (Real.pi * η / (2 * a))) hπ harg
  simpa only [Real.cos_abs] using hcos

/-- Upper large sieve on the central half of an arbitrary positive cosine
window.  The right side is linear in the window radius. -/
theorem integral_norm_sq_le_centeredHalf_largeSieve
    {a d : ℝ} (ha : 0 < a) (had : 1 < 2 * a * d)
    {n : ℕ} (x : Fin n → ℝ)
    (hsep : PairwiseFrequencySeparated x d) (c : Fin n → ℂ) :
    (∫ η : ℝ in Set.Icc (-(a / 2)) (a / 2),
        ‖gramFourierPolynomial x c η‖ ^ 2) ≤
      fourierIntervalLargeSieveConstant * a * ∑ i, ‖c i‖ ^ 2 := by
  let energy : ℝ → ℝ := fun η => ‖gramFourierPolynomial x c η‖ ^ 2
  let weighted : ℝ → ℝ := fun η => cosineInghamWeight a η * energy η
  let w₀ : ℝ := Real.cos (Real.pi / 4)
  have hw₀ : 0 < w₀ := by
    dsimp only [w₀]
    rw [Real.cos_pi_div_four]
    positivity
  have henergy : Continuous energy :=
    (continuous_gramFourierPolynomial x c).norm.pow 2
  have hweighted : Continuous weighted := by
    dsimp only [weighted]
    exact (by
      unfold cosineInghamWeight
      fun_prop : Continuous (cosineInghamWeight a)).mul henergy
  have hsmall :
      w₀ * (∫ η : ℝ in Set.Icc (-(a / 2)) (a / 2), energy η) ≤
        ∫ η : ℝ in Set.Icc (-(a / 2)) (a / 2), weighted η := by
    rw [← integral_const_mul]
    apply integral_mono_ae
      (ContinuousOn.integrableOn_compact isCompact_Icc
        (henergy.const_mul w₀).continuousOn)
      (ContinuousOn.integrableOn_compact isCompact_Icc
        hweighted.continuousOn)
    filter_upwards [ae_restrict_mem measurableSet_Icc] with η hη
    dsimp only [weighted]
    exact mul_le_mul_of_nonneg_right
      (cos_pi_div_four_le_cosineInghamWeight ha hη) (sq_nonneg _)
  have hsets : Set.Icc (-(a / 2)) (a / 2) ⊆ Set.Icc (-a) a := by
    intro η hη
    constructor <;> linarith [hη.1, hη.2]
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Icc (-a) a)] weighted := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with η hη
    dsimp only [weighted]
    exact mul_nonneg (cosineInghamWeight_nonneg_on_Icc ha hη) (sq_nonneg _)
  have hmono :
      (∫ η : ℝ in Set.Icc (-(a / 2)) (a / 2), weighted η) ≤
        ∫ η : ℝ in Set.Icc (-a) a, weighted η := by
    exact setIntegral_mono_set
      (ContinuousOn.integrableOn_compact isCompact_Icc
        hweighted.continuousOn)
      hnonneg (ae_of_all _ hsets)
  have hbig := integral_cosineWeight_mul_norm_sq_le_of_separated_scaled
    ha had x hsep c
  have hqinv : (2 * a * d)⁻¹ ^ 2 ≤ 1 := by
    have hqpos : 0 < 2 * a * d := zero_lt_one.trans had
    have hinv : (2 * a * d)⁻¹ ≤ 1 := (inv_le_one₀ hqpos).2 had.le
    exact pow_le_one₀ (inv_nonneg.mpr hqpos.le) hinv
  have hpi : 1 ≤ Real.pi := le_trans (by norm_num) Real.two_le_pi
  have hcoeff :
      (4 * a / Real.pi) * (1 + (2 * a * d)⁻¹ ^ 2) ≤ 8 * a := by
    have hdiv : 4 * a / Real.pi ≤ 4 * a := by
      rw [div_le_iff₀ Real.pi_pos]
      nlinarith
    nlinarith [div_nonneg (by positivity : (0 : ℝ) ≤ 4 * a) Real.pi_pos.le]
  have hcombined :
      w₀ * (∫ η : ℝ in Set.Icc (-(a / 2)) (a / 2), energy η) ≤
        8 * a * ∑ i, ‖c i‖ ^ 2 := by
    calc
      _ ≤ ∫ η : ℝ in Set.Icc (-(a / 2)) (a / 2), weighted η := hsmall
      _ ≤ ∫ η : ℝ in Set.Icc (-a) a, weighted η := hmono
      _ ≤ (4 * a / Real.pi) * (1 + (2 * a * d)⁻¹ ^ 2) *
          ∑ i, ‖c i‖ ^ 2 := hbig
      _ ≤ 8 * a * ∑ i, ‖c i‖ ^ 2 := by
        gcongr
  change (∫ η : ℝ in Set.Icc (-(a / 2)) (a / 2), energy η) ≤ _
  calc
    (∫ η : ℝ in Set.Icc (-(a / 2)) (a / 2), energy η) ≤
        (8 * a * ∑ i, ‖c i‖ ^ 2) / w₀ := by
      rw [le_div_iff₀ hw₀]
      simpa only [mul_comm] using hcombined
    _ = fourierIntervalLargeSieveConstant * a * ∑ i, ‖c i‖ ^ 2 := by
      unfold fourierIntervalLargeSieveConstant
      rw [div_eq_mul_inv]
      ring

/-- Translation-invariant form of the scaled central-half large sieve. -/
theorem integral_norm_sq_le_shiftedCenteredHalf_largeSieve
    {a d : ℝ} (ha : 0 < a) (had : 1 < 2 * a * d)
    {n : ℕ} (x : Fin n → ℝ)
    (hsep : PairwiseFrequencySeparated x d) (c : Fin n → ℂ) (r : ℝ) :
    (∫ η : ℝ in Set.Icc (r - a / 2) (r + a / 2),
        ‖gramFourierPolynomial x c η‖ ^ 2) ≤
      fourierIntervalLargeSieveConstant * a * ∑ i, ‖c i‖ ^ 2 := by
  let c' : Fin n → ℂ := fun i => c i * gramPhase (x i) r
  have hpoly (η : ℝ) :
      gramFourierPolynomial x c' η = gramFourierPolynomial x c (η + r) := by
    unfold gramFourierPolynomial
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [c']
    rw [gramPhase_add_right]
    ring
  have hcoeff : (∑ i, ‖c' i‖ ^ 2) = ∑ i, ‖c i‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    simp [c']
  have hcenter := integral_norm_sq_le_centeredHalf_largeSieve
    ha had x hsep c'
  rw [hcoeff] at hcenter
  have htranslate :
      (∫ η : ℝ in Set.Icc (r - a / 2) (r + a / 2),
          ‖gramFourierPolynomial x c η‖ ^ 2) =
        ∫ η : ℝ in Set.Icc (-(a / 2)) (a / 2),
          ‖gramFourierPolynomial x c (η + r)‖ ^ 2 := by
    calc
      (∫ η : ℝ in Set.Icc (r - a / 2) (r + a / 2),
          ‖gramFourierPolynomial x c η‖ ^ 2) =
          ∫ η : ℝ in (r - a / 2)..(r + a / 2),
            ‖gramFourierPolynomial x c η‖ ^ 2 := by
        rw [intervalIntegral.integral_of_le (by linarith),
          ← integral_Icc_eq_integral_Ioc]
      _ = ∫ η : ℝ in (-(a / 2))..(a / 2),
            ‖gramFourierPolynomial x c (η + r)‖ ^ 2 := by
        symm
        simpa only [sub_eq_add_neg, add_comm] using
          (intervalIntegral.integral_comp_add_right
            (fun η : ℝ => ‖gramFourierPolynomial x c η‖ ^ 2)
            (a := -(a / 2)) (b := a / 2) r)
      _ = ∫ η : ℝ in Set.Icc (-(a / 2)) (a / 2),
            ‖gramFourierPolynomial x c (η + r)‖ ^ 2 := by
        rw [intervalIntegral.integral_of_le (by linarith),
          ← integral_Icc_eq_integral_Ioc]
  rw [htranslate]
  simpa only [← hpoly] using hcenter

/-- Upper large sieve on an arbitrary closed interval.  Its exact scale is
the interval length plus one inverse separation. -/
theorem integral_norm_sq_le_interval_largeSieve
    {d lo hi : ℝ} (hd : 0 < d) (hlohi : lo ≤ hi)
    {n : ℕ} (x : Fin n → ℝ)
    (hsep : PairwiseFrequencySeparated x d) (c : Fin n → ℂ) :
    (∫ η : ℝ in Set.Icc lo hi,
        ‖gramFourierPolynomial x c η‖ ^ 2) ≤
      fourierIntervalLargeSieveConstant * (hi - lo + d⁻¹) *
        ∑ i, ‖c i‖ ^ 2 := by
  let a : ℝ := hi - lo + d⁻¹
  let r : ℝ := (lo + hi) / 2
  have ha : 0 < a := by
    dsimp only [a]
    exact add_pos_of_nonneg_of_pos (sub_nonneg.mpr hlohi) (inv_pos.mpr hd)
  have had : 1 < 2 * a * d := by
    have hinv : d⁻¹ * d = 1 := inv_mul_cancel₀ hd.ne'
    have hnonneg : 0 ≤ (hi - lo) * d :=
      mul_nonneg (sub_nonneg.mpr hlohi) hd.le
    dsimp only [a]
    nlinarith
  have hsubset : Set.Icc lo hi ⊆ Set.Icc (r - a / 2) (r + a / 2) := by
    intro η hη
    have hinv0 : 0 ≤ d⁻¹ := inv_nonneg.mpr hd.le
    dsimp only [r, a]
    constructor <;> linarith [hη.1, hη.2]
  have hmono :
      (∫ η : ℝ in Set.Icc lo hi, ‖gramFourierPolynomial x c η‖ ^ 2) ≤
        ∫ η : ℝ in Set.Icc (r - a / 2) (r + a / 2),
          ‖gramFourierPolynomial x c η‖ ^ 2 := by
    exact setIntegral_mono_set
      (ContinuousOn.integrableOn_compact isCompact_Icc
        ((continuous_gramFourierPolynomial x c).norm.pow 2).continuousOn)
      (ae_of_all _ fun η => sq_nonneg ‖gramFourierPolynomial x c η‖)
      (ae_of_all _ hsubset)
  exact hmono.trans
    (integral_norm_sq_le_shiftedCenteredHalf_largeSieve
      ha had x hsep c r)

/-- Fourier polynomial indexed by an arbitrary finite type. -/
def finiteFourierPolynomial
    {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (c : ι → ℂ) (η : ℝ) : ℂ :=
  ∑ i, c i * gramPhase (x i) η

theorem continuous_finiteFourierPolynomial
    {ι : Type*} [Fintype ι] (x : ι → ℝ) (c : ι → ℂ) :
    Continuous (finiteFourierPolynomial x c) := by
  unfold finiteFourierPolynomial
  apply continuous_finsetSum
  intro i _
  apply continuous_const.mul
  unfold gramPhase
  fun_prop

/-- Arbitrary-finite-type form of the interval upper large sieve. -/
theorem integral_finiteFourierPolynomial_norm_sq_le_interval_largeSieve
    {ι : Type*} [Fintype ι]
    {d lo hi : ℝ} (hd : 0 < d) (hlohi : lo ≤ hi)
    (x : ι → ℝ)
    (hsep : ∀ i j, i ≠ j → d ≤ |x i - x j|)
    (c : ι → ℂ) :
    (∫ η : ℝ in Set.Icc lo hi,
        ‖finiteFourierPolynomial x c η‖ ^ 2) ≤
      fourierIntervalLargeSieveConstant * (hi - lo + d⁻¹) *
        ∑ i, ‖c i‖ ^ 2 := by
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let x' : Fin (Fintype.card ι) → ℝ := fun i => x (e.symm i)
  let c' : Fin (Fintype.card ι) → ℂ := fun i => c (e.symm i)
  have hsep' : PairwiseFrequencySeparated x' d := by
    intro i j hij
    apply hsep
    exact e.symm.injective.ne hij
  have hpoly (η : ℝ) :
      finiteFourierPolynomial x c η = gramFourierPolynomial x' c' η := by
    unfold finiteFourierPolynomial gramFourierPolynomial
    apply Fintype.sum_equiv e
    intro i
    simp only [x', c', Equiv.symm_apply_apply]
  have hcoeff : (∑ i, ‖c' i‖ ^ 2) = ∑ i, ‖c i‖ ^ 2 := by
    symm
    apply Fintype.sum_equiv e
    intro i
    simp only [c', Equiv.symm_apply_apply]
  have hfin := integral_norm_sq_le_interval_largeSieve
    hd hlohi x' hsep' c'
  rw [hcoeff] at hfin
  simpa only [hpoly] using hfin

/-- Derivative of the repository Fourier phase in its second variable. -/
theorem hasDerivAt_gramPhase_right (s t : ℝ) :
    HasDerivAt (gramPhase s)
      (gramPhase s t * (((2 * Real.pi * s : ℝ) : ℂ) * Complex.I)) t := by
  let ω : ℝ := 2 * Real.pi * s
  let θ : ℝ → ℝ := fun z => ω * z
  let sinICLM : ℝ →L[ℝ] ℂ := Complex.ofRealCLM.smulRight Complex.I
  have hθ : HasDerivAt θ ω t := by
    simpa only [θ, ω, id_eq, mul_one] using
      (hasDerivAt_id t).const_mul (2 * Real.pi * s)
  have hcos :=
    (Complex.ofRealCLM.hasFDerivAt.comp t hθ.cos.hasFDerivAt).hasDerivAt
  have hsin := (sinICLM.hasFDerivAt.comp t hθ.sin.hasFDerivAt).hasDerivAt
  have hsum := hcos.add hsin
  have hfun : gramPhase s = fun z =>
      Complex.ofRealCLM (Real.cos (θ z)) +
        sinICLM (Real.sin (θ z)) := by
    funext z
    unfold gramPhase
    rw [show 2 * Real.pi * s * z = θ z by rfl,
      Complex.exp_ofReal_mul_I]
    simp only [sinICLM, ContinuousLinearMap.smulRight_apply,
      Complex.ofRealCLM_apply, smul_eq_mul]
  rw [hfun]
  apply hsum.congr_deriv
  apply Complex.ext <;>
    simp [sinICLM, ContinuousLinearMap.smulRight_apply,
      Complex.ofRealCLM_apply, smul_eq_mul, ω]

/-- Fourier polynomial after removing a center frequency. -/
def centeredFiniteFourierPolynomial
    {ι : Type*} [Fintype ι]
    (y : ι → ℝ) (y₀ : ℝ) (c : ι → ℂ) : ℝ → ℂ :=
  finiteFourierPolynomial (fun j => y j - y₀) c

/-- Exact derivative of the centered finite Fourier polynomial. -/
def centeredFiniteFourierPolynomialDeriv
    {ι : Type*} [Fintype ι]
    (y : ι → ℝ) (y₀ : ℝ) (c : ι → ℂ) : ℝ → ℂ :=
  finiteFourierPolynomial (fun j => y j - y₀)
    (fun j => (((2 * Real.pi * (y j - y₀) : ℝ) : ℂ) * Complex.I) * c j)

theorem hasDerivAt_centeredFiniteFourierPolynomial
    {ι : Type*} [Fintype ι]
    (y : ι → ℝ) (y₀ : ℝ) (c : ι → ℂ) (t : ℝ) :
    HasDerivAt (centeredFiniteFourierPolynomial y y₀ c)
      (centeredFiniteFourierPolynomialDeriv y y₀ c t) t := by
  unfold centeredFiniteFourierPolynomial centeredFiniteFourierPolynomialDeriv
    finiteFourierPolynomial
  have hsum := HasDerivAt.sum (u := Finset.univ) (x := t)
      (fun j _ =>
        (hasDerivAt_gramPhase_right (y j - y₀) t).const_mul (c j))
  have hsum' : HasDerivAt
      (fun z => ∑ j, c j * gramPhase (y j - y₀) z)
      (∑ j, c j * (gramPhase (y j - y₀) t *
        (((2 * Real.pi * (y j - y₀) : ℝ) : ℂ) * Complex.I))) t := by
    exact hsum.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun z => by simp only [Finset.sum_apply])
  apply hsum'.congr_deriv
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem continuous_centeredFiniteFourierPolynomialDeriv
    {ι : Type*} [Fintype ι]
    (y : ι → ℝ) (y₀ : ℝ) (c : ι → ℂ) :
    Continuous (centeredFiniteFourierPolynomialDeriv y y₀ c) := by
  unfold centeredFiniteFourierPolynomialDeriv
  exact continuous_finiteFourierPolynomial _ _

/-- Removing a center frequency changes a Fourier polynomial only by a unit
phase, hence preserves every pointwise norm. -/
theorem norm_centeredFiniteFourierPolynomial
    {ι : Type*} [Fintype ι]
    (y : ι → ℝ) (y₀ : ℝ) (c : ι → ℂ) (t : ℝ) :
    ‖centeredFiniteFourierPolynomial y y₀ c t‖ =
      ‖finiteFourierPolynomial y c t‖ := by
  have hfactor :
      finiteFourierPolynomial y c t =
        centeredFiniteFourierPolynomial y y₀ c t * gramPhase y₀ t := by
    simp only [centeredFiniteFourierPolynomial, finiteFourierPolynomial]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    calc
      c j * gramPhase (y j) t =
          c j * gramPhase ((y j - y₀) + y₀) t := by
        congr 2
        ring
      _ = c j * gramPhase (y j - y₀) t * gramPhase y₀ t := by
        rw [gramPhase_add]
        ring
  rw [hfactor, norm_mul, norm_gramPhase, mul_one]

/-- Centering bounds every derivative coefficient by the diameter of the
frequency family. -/
theorem sum_norm_sq_centeredFourierDerivCoefficient_le
    {ι : Type*} [Fintype ι]
    (y : ι → ℝ) (j₀ : ι) {W : ℝ}
    (hdiam : ∀ j k, |y j - y k| ≤ W) (c : ι → ℂ) :
    (∑ j, ‖(((2 * Real.pi * (y j - y j₀) : ℝ) : ℂ) * Complex.I) * c j‖ ^ 2) ≤
      (2 * Real.pi * W) ^ 2 * ∑ j, ‖c j‖ ^ 2 := by
  calc
    (∑ j, ‖(((2 * Real.pi * (y j - y j₀) : ℝ) : ℂ) * Complex.I) * c j‖ ^ 2) ≤
        ∑ j, (2 * Real.pi * W) ^ 2 * ‖c j‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_I, mul_one, mul_pow]
      have hpi0 : 0 ≤ 2 * Real.pi := by positivity
      have hfreq : |2 * Real.pi * (y j - y j₀)| ≤ 2 * Real.pi * W := by
        rw [abs_mul, abs_of_nonneg hpi0]
        exact mul_le_mul_of_nonneg_left (hdiam j j₀) hpi0
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (abs_nonneg _) hfreq 2) (sq_nonneg _)
    _ = (2 * Real.pi * W) ^ 2 * ∑ j, ‖c j‖ ^ 2 := by
      rw [Finset.mul_sum]

/-- The genuine finite irregular Fourier rectangle.  Its entries use the
repository's positive `2π` phase convention. -/
def finiteFourierRectangle
    {ι κ : Type*}
    (x : ι → ℝ) (y : κ → ℝ) : Matrix ι κ ℂ :=
  fun i j => gramPhase (y j) (x i)

@[simp]
theorem finiteFourierRectangle_apply
    {ι κ : Type*}
    (x : ι → ℝ) (y : κ → ℝ) (i : ι) (j : κ) :
    finiteFourierRectangle x y i j = gramPhase (y j) (x i) := rfl

@[simp]
theorem finiteFourierRectangle_mulVec
    {ι κ : Type*} [Fintype κ]
    (x : ι → ℝ) (y : κ → ℝ) (c : κ → ℂ) (i : ι) :
    Matrix.mulVec (finiteFourierRectangle x y) c i =
      ∑ j, c j * gramPhase (y j) (x i) := by
  simp only [Matrix.mulVec_apply_eq_sum, finiteFourierRectangle_apply]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

theorem finiteFourierRectangle_mulVec_eq_finiteFourierPolynomial
    {ι κ : Type*} [Fintype κ]
    (x : ι → ℝ) (y : κ → ℝ) (c : κ → ℂ) (i : ι) :
    Matrix.mulVec (finiteFourierRectangle x y) c i =
      finiteFourierPolynomial y c (x i) := by
  simpa only [finiteFourierPolynomial] using
    finiteFourierRectangle_mulVec x y c i

/-- Negative-phase Fourier rectangle used by the cross-kernel model. -/
def finiteNegativeFourierRectangle
    {ι κ : Type*}
    (x : ι → ℝ) (y : κ → ℝ) : Matrix ι κ ℂ :=
  finiteFourierRectangle x (fun j => -y j)

@[simp]
theorem finiteNegativeFourierRectangle_apply
    {ι κ : Type*}
    (x : ι → ℝ) (y : κ → ℝ) (i : ι) (j : κ) :
    finiteNegativeFourierRectangle x y i j =
      gramPhase (-y j) (x i) := rfl

/-- Conjugate transpose swaps the two frequency families and changes the
negative Fourier phase to the positive phase. -/
@[simp]
theorem finiteNegativeFourierRectangle_conjTranspose
    {ι κ : Type*} (x : ι → ℝ) (y : κ → ℝ) :
    Matrix.conjTranspose (finiteNegativeFourierRectangle x y) =
      finiteFourierRectangle y x := by
  ext j i
  simp only [Matrix.conjTranspose_apply,
    finiteNegativeFourierRectangle_apply, finiteFourierRectangle_apply]
  unfold gramPhase
  rw [Complex.star_def, ← Complex.exp_conj]
  apply congrArg Complex.exp
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- Conjugate transpose swaps the two frequency families and changes the
positive Fourier phase to the negative phase. -/
@[simp]
theorem finiteFourierRectangle_conjTranspose
    {ι κ : Type*} (x : ι → ℝ) (y : κ → ℝ) :
    Matrix.conjTranspose (finiteFourierRectangle x y) =
      finiteNegativeFourierRectangle y x := by
  rw [← Matrix.conjTranspose_inj]
  simp only [Matrix.conjTranspose_conjTranspose,
    finiteNegativeFourierRectangle_conjTranspose]

/-- Swapping a negative Fourier rectangle to the positive orientation
preserves its matrix `ℓ²` operator norm, including empty carriers. -/
theorem finiteNegativeFourierRectangle_l2OpNorm_eq_swapped
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (x : ι → ℝ) (y : κ → ℝ) :
    ‖finiteNegativeFourierRectangle x y‖ =
      ‖finiteFourierRectangle y x‖ := by
  rw [← finiteNegativeFourierRectangle_conjTranspose,
    Matrix.l2_opNorm_conjTranspose]

/-- Swapping a positive Fourier rectangle to the negative orientation
preserves its matrix `ℓ²` operator norm, including empty carriers. -/
theorem finiteFourierRectangle_l2OpNorm_eq_swapped
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (x : ι → ℝ) (y : κ → ℝ) :
    ‖finiteFourierRectangle x y‖ =
      ‖finiteNegativeFourierRectangle y x‖ := by
  rw [← finiteFourierRectangle_conjTranspose,
    Matrix.l2_opNorm_conjTranspose]

@[simp]
theorem finiteNegativeFourierRectangle_mulVec
    {ι κ : Type*} [Fintype κ]
    (x : ι → ℝ) (y : κ → ℝ) (c : κ → ℂ) (i : ι) :
    Matrix.mulVec (finiteNegativeFourierRectangle x y) c i =
      ∑ j, c j * gramPhase (-y j) (x i) := by
  exact finiteFourierRectangle_mulVec x (fun j => -y j) c i

/-- The absolute constant in the separated Fourier-rectangle theorem. -/
def fourierRectangleConstant : ℝ :=
  12 * fourierIntervalLargeSieveConstant * (1 + Real.pi ^ 2)

theorem fourierRectangleConstant_pos : 0 < fourierRectangleConstant := by
  unfold fourierRectangleConstant
  exact mul_pos
    (mul_pos (by norm_num) fourierIntervalLargeSieveConstant_pos)
    (by positivity)

/-- Energy form of the irregular rectangle estimate, retaining the exact
length of the interval created by local sampling. -/
private theorem sum_norm_sq_finiteFourierRectangle_mulVec_le_of_nonempty
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [Nonempty ι] [Nonempty κ]
    (x : ι → ℝ) (y : κ → ℝ)
    {δx δy Lx Wy : ℝ}
    (hδx : 0 < δx) (hδy : 0 < δy)
    (hLx : 0 ≤ Lx) (_hWy : 0 ≤ Wy)
    (hxsep : ∀ i j, i ≠ j → δx ≤ |x i - x j|)
    (hysep : ∀ i j, i ≠ j → δy ≤ |y i - y j|)
    (hxdiam : ∀ i j, |x i - x j| ≤ Lx)
    (hydiam : ∀ i j, |y i - y j| ≤ Wy)
    (c : κ → ℂ) :
    (∑ i, ‖Matrix.mulVec (finiteFourierRectangle x y) c i‖ ^ 2) ≤
      4 * fourierIntervalLargeSieveConstant * (1 + Real.pi ^ 2) *
        (δx⁻¹ + δx * Wy ^ 2) *
        (2 * Lx + δx + δy⁻¹) * ∑ j, ‖c j‖ ^ 2 := by
  let i₀ : ι := Classical.choice inferInstance
  let j₀ : κ := Classical.choice inferInstance
  let lo : ℝ := x i₀ - Lx
  let hi : ℝ := x i₀ + Lx
  let left : ℝ := lo - δx / 2
  let right : ℝ := hi + δx / 2
  let f : ℝ → ℂ := centeredFiniteFourierPolynomial y (y j₀) c
  let f' : ℝ → ℂ := centeredFiniteFourierPolynomialDeriv y (y j₀) c
  let E : ℝ := ∑ j, ‖c j‖ ^ 2
  let S : ℝ := 2 * Lx + δx + δy⁻¹
  have hlo (i : ι) : lo ≤ x i := by
    have habs := hxdiam i i₀
    rw [abs_le] at habs
    dsimp only [lo]
    linarith [habs.1]
  have hhi (i : ι) : x i ≤ hi := by
    have habs := hxdiam i i₀
    rw [abs_le] at habs
    dsimp only [hi]
    linarith [habs.2]
  have hleftright : left ≤ right := by
    dsimp only [left, right, lo, hi]
    linarith
  have hysep' :
      ∀ i j, i ≠ j → δy ≤ |(y i - y j₀) - (y j - y j₀)| := by
    intro i j hij
    convert hysep i j hij using 1
    ring_nf
  have hS : right - left + δy⁻¹ = S := by
    dsimp only [right, left, hi, lo, S]
    ring
  have hI0 :
      (∫ t : ℝ in Set.Icc left right, ‖f t‖ ^ 2) ≤
        fourierIntervalLargeSieveConstant * S * E := by
    have hlarge :=
      integral_finiteFourierPolynomial_norm_sq_le_interval_largeSieve
        hδy hleftright (fun j => y j - y j₀) hysep' c
    simpa only [f, centeredFiniteFourierPolynomial, hS, E] using hlarge
  have hcoeff :
      (∑ j, ‖(((2 * Real.pi * (y j - y j₀) : ℝ) : ℂ) *
          Complex.I) * c j‖ ^ 2) ≤
        (2 * Real.pi * Wy) ^ 2 * E := by
    simpa only [E] using
      sum_norm_sq_centeredFourierDerivCoefficient_le y j₀ hydiam c
  have hI1 :
      (∫ t : ℝ in Set.Icc left right, ‖f' t‖ ^ 2) ≤
        fourierIntervalLargeSieveConstant * S *
          ((2 * Real.pi * Wy) ^ 2 * E) := by
    have hlarge :=
      integral_finiteFourierPolynomial_norm_sq_le_interval_largeSieve
        hδy hleftright (fun j => y j - y j₀) hysep'
          (fun j => (((2 * Real.pi * (y j - y j₀) : ℝ) : ℂ) *
            Complex.I) * c j)
    have hC0 : 0 ≤ fourierIntervalLargeSieveConstant :=
      fourierIntervalLargeSieveConstant_pos.le
    have hS0 : 0 ≤ S := by
      dsimp only [S]
      positivity
    calc
      (∫ t : ℝ in Set.Icc left right, ‖f' t‖ ^ 2) ≤
          fourierIntervalLargeSieveConstant * S *
            ∑ j, ‖(((2 * Real.pi * (y j - y j₀) : ℝ) : ℂ) *
              Complex.I) * c j‖ ^ 2 := by
        simpa only [f', centeredFiniteFourierPolynomialDeriv, hS] using hlarge
      _ ≤ fourierIntervalLargeSieveConstant * S *
          ((2 * Real.pi * Wy) ^ 2 * E) := by
        exact mul_le_mul_of_nonneg_left hcoeff (mul_nonneg hC0 hS0)
  have hlocal := sum_norm_sq_le_localSobolev x f f'
    (fun t => hasDerivAt_centeredFiniteFourierPolynomial y (y j₀) c t)
    (continuous_centeredFiniteFourierPolynomialDeriv y (y j₀) c)
    hδx hxsep hlo hhi
  have hleft : lo - δx / 2 = left := rfl
  have hright : hi + δx / 2 = right := rfl
  rw [hleft, hright] at hlocal
  have hsample :
      (∑ i, ‖Matrix.mulVec (finiteFourierRectangle x y) c i‖ ^ 2) =
        ∑ i, ‖f (x i)‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    rw [finiteFourierRectangle_mulVec_eq_finiteFourierPolynomial,
      norm_centeredFiniteFourierPolynomial]
  rw [hsample]
  have hE0 : 0 ≤ E := by
    dsimp only [E]
    positivity
  have hS0 : 0 ≤ S := by
    dsimp only [S]
    positivity
  have hC0 : 0 ≤ fourierIntervalLargeSieveConstant :=
    fourierIntervalLargeSieveConstant_pos.le
  have hpi0 : 0 ≤ Real.pi ^ 2 := sq_nonneg _
  calc
    (∑ i, ‖f (x i)‖ ^ 2) ≤
        2 * δx⁻¹ * (∫ t : ℝ in Set.Icc left right, ‖f t‖ ^ 2) +
          δx * (∫ t : ℝ in Set.Icc left right, ‖f' t‖ ^ 2) := hlocal
    _ ≤ 2 * δx⁻¹ *
          (fourierIntervalLargeSieveConstant * S * E) +
        δx * (fourierIntervalLargeSieveConstant * S *
          ((2 * Real.pi * Wy) ^ 2 * E)) := by
      gcongr
    _ ≤ 4 * fourierIntervalLargeSieveConstant * (1 + Real.pi ^ 2) *
        (δx⁻¹ + δx * Wy ^ 2) * S * E := by
      have hdxinv : 0 ≤ δx⁻¹ := inv_nonneg.mpr hδx.le
      have hdxW : 0 ≤ δx * Wy ^ 2 :=
        mul_nonneg hδx.le (sq_nonneg Wy)
      have hinner :
          δx⁻¹ + 2 * Real.pi ^ 2 * (δx * Wy ^ 2) ≤
            2 * (1 + Real.pi ^ 2) * (δx⁻¹ + δx * Wy ^ 2) := by
        nlinarith [mul_nonneg (sq_nonneg Real.pi) hdxinv,
          mul_nonneg (sq_nonneg Real.pi) hdxW]
      calc
        2 * δx⁻¹ * (fourierIntervalLargeSieveConstant * S * E) +
            δx * (fourierIntervalLargeSieveConstant * S *
              ((2 * Real.pi * Wy) ^ 2 * E)) =
            2 * fourierIntervalLargeSieveConstant * S * E *
              (δx⁻¹ + 2 * Real.pi ^ 2 * (δx * Wy ^ 2)) := by ring
        _ ≤ 2 * fourierIntervalLargeSieveConstant * S * E *
              (2 * (1 + Real.pi ^ 2) *
                (δx⁻¹ + δx * Wy ^ 2)) := by
          exact mul_le_mul_of_nonneg_left hinner
            (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC0) hS0) hE0)
        _ = 4 * fourierIntervalLargeSieveConstant *
              (1 + Real.pi ^ 2) * (δx⁻¹ + δx * Wy ^ 2) * S * E := by
          ring
    _ = 4 * fourierIntervalLargeSieveConstant * (1 + Real.pi ^ 2) *
        (δx⁻¹ + δx * Wy ^ 2) *
        (2 * Lx + δx + δy⁻¹) * ∑ j, ‖c j‖ ^ 2 := by
      rfl

/-- Energy form of the irregular rectangle estimate for arbitrary finite
carriers.  Empty row or column types are discharged automatically. -/
theorem sum_norm_sq_finiteFourierRectangle_mulVec_le
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (x : ι → ℝ) (y : κ → ℝ)
    {δx δy Lx Wy : ℝ}
    (hδx : 0 < δx) (hδy : 0 < δy)
    (hLx : 0 ≤ Lx) (hWy : 0 ≤ Wy)
    (hxsep : ∀ i j, i ≠ j → δx ≤ |x i - x j|)
    (hysep : ∀ i j, i ≠ j → δy ≤ |y i - y j|)
    (hxdiam : ∀ i j, |x i - x j| ≤ Lx)
    (hydiam : ∀ i j, |y i - y j| ≤ Wy)
    (c : κ → ℂ) :
    (∑ i, ‖Matrix.mulVec (finiteFourierRectangle x y) c i‖ ^ 2) ≤
      4 * fourierIntervalLargeSieveConstant * (1 + Real.pi ^ 2) *
        (δx⁻¹ + δx * Wy ^ 2) *
        (2 * Lx + δx + δy⁻¹) * ∑ j, ‖c j‖ ^ 2 := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · let _ := hι
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    have hfirst : 0 ≤ δx⁻¹ + δx * Wy ^ 2 :=
      add_nonneg (inv_nonneg.mpr hδx.le)
        (mul_nonneg hδx.le (sq_nonneg Wy))
    have hlength : 0 ≤ 2 * Lx + δx + δy⁻¹ := by
      positivity
    have hconstant : 0 ≤ 4 * fourierIntervalLargeSieveConstant *
        (1 + Real.pi ^ 2) := by
      exact mul_nonneg
        (mul_nonneg (by norm_num) fourierIntervalLargeSieveConstant_pos.le)
        (by positivity)
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hconstant hfirst) hlength) (by positivity)
  · let _ := hι
    rcases isEmpty_or_nonempty κ with hκ | hκ
    · let _ := hκ
      simp only [finiteFourierRectangle_mulVec, Finset.univ_eq_empty,
        Finset.sum_empty, norm_zero, zero_pow (by norm_num : 2 ≠ 0),
        Finset.sum_const_zero, mul_zero]
      exact le_rfl
    · let _ := hκ
      exact sum_norm_sq_finiteFourierRectangle_mulVec_le_of_nonempty
        x y hδx hδy hLx hWy hxsep hysep hxdiam hydiam c

/-- Negative-phase energy estimate.  Negating all frequencies preserves
both separation and diameter. -/
theorem sum_norm_sq_finiteNegativeFourierRectangle_mulVec_le
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (x : ι → ℝ) (y : κ → ℝ)
    {δx δy Lx Wy : ℝ}
    (hδx : 0 < δx) (hδy : 0 < δy)
    (hLx : 0 ≤ Lx) (hWy : 0 ≤ Wy)
    (hxsep : ∀ i j, i ≠ j → δx ≤ |x i - x j|)
    (hysep : ∀ i j, i ≠ j → δy ≤ |y i - y j|)
    (hxdiam : ∀ i j, |x i - x j| ≤ Lx)
    (hydiam : ∀ i j, |y i - y j| ≤ Wy)
    (c : κ → ℂ) :
    (∑ i, ‖Matrix.mulVec (finiteNegativeFourierRectangle x y) c i‖ ^ 2) ≤
      4 * fourierIntervalLargeSieveConstant * (1 + Real.pi ^ 2) *
        (δx⁻¹ + δx * Wy ^ 2) *
        (2 * Lx + δx + δy⁻¹) * ∑ j, ‖c j‖ ^ 2 := by
  have hysepNeg : ∀ i j, i ≠ j →
      δy ≤ |(-y i) - (-y j)| := by
    intro i j hij
    rw [show (-y i) - (-y j) = y j - y i by ring, abs_sub_comm]
    exact hysep i j hij
  have hydiamNeg : ∀ i j, |(-y i) - (-y j)| ≤ Wy := by
    intro i j
    rw [show (-y i) - (-y j) = y j - y i by ring, abs_sub_comm]
    exact hydiam i j
  simpa only [finiteNegativeFourierRectangle] using
    sum_norm_sq_finiteFourierRectangle_mulVec_le x (fun j => -y j)
      hδx hδy hLx hWy hxsep hysepNeg hxdiam hydiamNeg c

/-- An energy estimate implies the corresponding squared matrix `ℓ²`
operator-norm estimate. -/
theorem matrix_l2_opNorm_sq_le_of_energy
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ ℂ) {B : ℝ} (hB : 0 ≤ B)
    (henergy : ∀ c : κ → ℂ,
      (∑ i, ‖Matrix.mulVec A c i‖ ^ 2) ≤ B * ∑ j, ‖c j‖ ^ 2) :
    ‖A‖ ^ 2 ≤ B := by
  rw [Matrix.l2_opNorm_def]
  have hop :
      ‖(Matrix.toEuclideanLin ≪≫ₗ LinearMap.toContinuousLinearMap) A‖ ≤
        Real.sqrt B := by
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
    intro z
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    change Real.sqrt (∑ i, ‖Matrix.mulVec A (WithLp.ofLp z) i‖ ^ 2) ≤
      Real.sqrt B * Real.sqrt (∑ j, ‖WithLp.ofLp z j‖ ^ 2)
    rw [← Real.sqrt_mul hB]
    exact Real.sqrt_le_sqrt (henergy (WithLp.ofLp z))
  calc
    ‖(Matrix.toEuclideanLin ≪≫ₗ LinearMap.toContinuousLinearMap) A‖ ^ 2 ≤
        (Real.sqrt B) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hop 2
    _ = B := Real.sq_sqrt hB

/-- Singleton-safe separated Fourier-rectangle estimate in the matrix `ℓ²`
operator norm.  The additional `δx` is the padding introduced by the local
sampling intervals. -/
theorem finiteSeparatedFourierRectangle_l2OpNorm_sq_le_raw
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (x : ι → ℝ) (y : κ → ℝ)
    {δx δy Lx Wy : ℝ}
    (hδx : 0 < δx) (hδy : 0 < δy)
    (hLx : 0 ≤ Lx) (hWy : 0 ≤ Wy)
    (hxsep : ∀ i j, i ≠ j → δx ≤ |x i - x j|)
    (hysep : ∀ i j, i ≠ j → δy ≤ |y i - y j|)
    (hxdiam : ∀ i j, |x i - x j| ≤ Lx)
    (hydiam : ∀ i j, |y i - y j| ≤ Wy) :
    ‖finiteFourierRectangle x y‖ ^ 2 ≤
      fourierRectangleConstant *
        (δx⁻¹ + δx * Wy ^ 2) * (Lx + δx + δy⁻¹) := by
  let B := fourierRectangleConstant *
    (δx⁻¹ + δx * Wy ^ 2) * (Lx + δx + δy⁻¹)
  have hfirst : 0 ≤ δx⁻¹ + δx * Wy ^ 2 :=
    add_nonneg (inv_nonneg.mpr hδx.le)
      (mul_nonneg hδx.le (sq_nonneg Wy))
  have hlast : 0 ≤ Lx + δx + δy⁻¹ :=
    add_nonneg (add_nonneg hLx hδx.le) (inv_nonneg.mpr hδy.le)
  have hB : 0 ≤ B := by
    dsimp only [B]
    exact mul_nonneg
      (mul_nonneg fourierRectangleConstant_pos.le hfirst) hlast
  apply matrix_l2_opNorm_sq_le_of_energy (finiteFourierRectangle x y) hB
  intro c
  have hbase := sum_norm_sq_finiteFourierRectangle_mulVec_le
    x y hδx hδy hLx hWy hxsep hysep hxdiam hydiam c
  have hwidth : 2 * Lx + δx + δy⁻¹ ≤
      2 * (Lx + δx + δy⁻¹) := by
    linarith [inv_nonneg.mpr hδy.le]
  have hE : 0 ≤ ∑ j, ‖c j‖ ^ 2 := by positivity
  have hlead : 0 ≤ 4 * fourierIntervalLargeSieveConstant *
      (1 + Real.pi ^ 2) * (δx⁻¹ + δx * Wy ^ 2) :=
    mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) fourierIntervalLargeSieveConstant_pos.le)
        (by positivity)) hfirst
  calc
    _ ≤ 4 * fourierIntervalLargeSieveConstant * (1 + Real.pi ^ 2) *
        (δx⁻¹ + δx * Wy ^ 2) * (2 * Lx + δx + δy⁻¹) *
          ∑ j, ‖c j‖ ^ 2 := hbase
    _ ≤ 4 * fourierIntervalLargeSieveConstant * (1 + Real.pi ^ 2) *
        (δx⁻¹ + δx * Wy ^ 2) * (2 * (Lx + δx + δy⁻¹)) *
          ∑ j, ‖c j‖ ^ 2 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hwidth hlead) hE
    _ ≤ B * ∑ j, ‖c j‖ ^ 2 := by
      dsimp only [B, fourierRectangleConstant]
      have hfactor : 0 ≤ fourierIntervalLargeSieveConstant *
          (1 + Real.pi ^ 2) * (δx⁻¹ + δx * Wy ^ 2) *
            (Lx + δx + δy⁻¹) * ∑ j, ‖c j‖ ^ 2 :=
        mul_nonneg
          (mul_nonneg
            (mul_nonneg
              (mul_nonneg fourierIntervalLargeSieveConstant_pos.le
                (by positivity)) hfirst) hlast) hE
      nlinarith

/-- Archive-shaped positive-phase rectangle estimate.  The absorption
hypothesis is necessary: singleton carriers otherwise permit a vacuously
arbitrarily large claimed separation. -/
theorem finiteSeparatedFourierRectangle_l2OpNorm_sq_le
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (x : ι → ℝ) (y : κ → ℝ)
    {δx δy Lx Wy : ℝ}
    (hδx : 0 < δx) (hδy : 0 < δy)
    (hLx : 0 ≤ Lx) (hWy : 0 ≤ Wy)
    (habsorb : δx ≤ Lx + δy⁻¹)
    (hxsep : ∀ i j, i ≠ j → δx ≤ |x i - x j|)
    (hysep : ∀ i j, i ≠ j → δy ≤ |y i - y j|)
    (hxdiam : ∀ i j, |x i - x j| ≤ Lx)
    (hydiam : ∀ i j, |y i - y j| ≤ Wy) :
    ‖finiteFourierRectangle x y‖ ^ 2 ≤
      2 * fourierRectangleConstant *
        (δx⁻¹ + δx * Wy ^ 2) * (Lx + δy⁻¹) := by
  have hraw := finiteSeparatedFourierRectangle_l2OpNorm_sq_le_raw
    x y hδx hδy hLx hWy hxsep hysep hxdiam hydiam
  have hfirst : 0 ≤ δx⁻¹ + δx * Wy ^ 2 :=
    add_nonneg (inv_nonneg.mpr hδx.le)
      (mul_nonneg hδx.le (sq_nonneg Wy))
  have hlength : Lx + δx + δy⁻¹ ≤ 2 * (Lx + δy⁻¹) := by
    linarith
  calc
    _ ≤ fourierRectangleConstant * (δx⁻¹ + δx * Wy ^ 2) *
        (Lx + δx + δy⁻¹) := hraw
    _ ≤ fourierRectangleConstant * (δx⁻¹ + δx * Wy ^ 2) *
        (2 * (Lx + δy⁻¹)) := by
      exact mul_le_mul_of_nonneg_left hlength
        (mul_nonneg fourierRectangleConstant_pos.le hfirst)
    _ = 2 * fourierRectangleConstant *
        (δx⁻¹ + δx * Wy ^ 2) * (Lx + δy⁻¹) := by ring

/-- Singleton-safe negative-phase rectangle estimate for the actual cross
kernel convention. -/
theorem finiteSeparatedNegativeFourierRectangle_l2OpNorm_sq_le_raw
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (x : ι → ℝ) (y : κ → ℝ)
    {δx δy Lx Wy : ℝ}
    (hδx : 0 < δx) (hδy : 0 < δy)
    (hLx : 0 ≤ Lx) (hWy : 0 ≤ Wy)
    (hxsep : ∀ i j, i ≠ j → δx ≤ |x i - x j|)
    (hysep : ∀ i j, i ≠ j → δy ≤ |y i - y j|)
    (hxdiam : ∀ i j, |x i - x j| ≤ Lx)
    (hydiam : ∀ i j, |y i - y j| ≤ Wy) :
    ‖finiteNegativeFourierRectangle x y‖ ^ 2 ≤
      fourierRectangleConstant *
        (δx⁻¹ + δx * Wy ^ 2) * (Lx + δx + δy⁻¹) := by
  have hysepNeg : ∀ i j, i ≠ j →
      δy ≤ |(-y i) - (-y j)| := by
    intro i j hij
    rw [show (-y i) - (-y j) = y j - y i by ring, abs_sub_comm]
    exact hysep i j hij
  have hydiamNeg : ∀ i j, |(-y i) - (-y j)| ≤ Wy := by
    intro i j
    rw [show (-y i) - (-y j) = y j - y i by ring, abs_sub_comm]
    exact hydiam i j
  simpa only [finiteNegativeFourierRectangle] using
    finiteSeparatedFourierRectangle_l2OpNorm_sq_le_raw
      x (fun j => -y j) hδx hδy hLx hWy
        hxsep hysepNeg hxdiam hydiamNeg

/-- Archive-shaped negative-phase rectangle estimate. -/
theorem finiteSeparatedNegativeFourierRectangle_l2OpNorm_sq_le
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (x : ι → ℝ) (y : κ → ℝ)
    {δx δy Lx Wy : ℝ}
    (hδx : 0 < δx) (hδy : 0 < δy)
    (hLx : 0 ≤ Lx) (hWy : 0 ≤ Wy)
    (habsorb : δx ≤ Lx + δy⁻¹)
    (hxsep : ∀ i j, i ≠ j → δx ≤ |x i - x j|)
    (hysep : ∀ i j, i ≠ j → δy ≤ |y i - y j|)
    (hxdiam : ∀ i j, |x i - x j| ≤ Lx)
    (hydiam : ∀ i j, |y i - y j| ≤ Wy) :
    ‖finiteNegativeFourierRectangle x y‖ ^ 2 ≤
      2 * fourierRectangleConstant *
        (δx⁻¹ + δx * Wy ^ 2) * (Lx + δy⁻¹) := by
  have hysepNeg : ∀ i j, i ≠ j →
      δy ≤ |(-y i) - (-y j)| := by
    intro i j hij
    rw [show (-y i) - (-y j) = y j - y i by ring, abs_sub_comm]
    exact hysep i j hij
  have hydiamNeg : ∀ i j, |(-y i) - (-y j)| ≤ Wy := by
    intro i j
    rw [show (-y i) - (-y j) = y j - y i by ring, abs_sub_comm]
    exact hydiam i j
  simpa only [finiteNegativeFourierRectangle] using
    finiteSeparatedFourierRectangle_l2OpNorm_sq_le
      x (fun j => -y j) hδx hδy hLx hWy habsorb
        hxsep hysepNeg hxdiam hydiamNeg

end

end MeyerGeneralProblem
