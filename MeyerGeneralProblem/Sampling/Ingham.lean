module

public import MeyerGeneralProblem.Gram.UniversalKernel
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import all Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

/-!
# Finite Ingham window identities

This module exposes the exact finite-dimensional kernel behind the remaining
separated Ingham inequality.  No separation estimate is assumed here: the
window energy is expanded exactly, and the scalar interval kernel is reduced
to `sinc`.  The subsequent load-bearing theorem must bound the off-diagonal
part for separated frequencies.
-/

namespace MeyerGeneralProblem

open MeasureTheory ComplexConjugate

noncomputable section

/-- Fourier kernel of the symmetric Ingham window. -/
def inghamWindowKernel (a t : ℝ) : ℂ :=
  ∫ η : ℝ in Set.Icc (-a) a, gramPhase t η

/-- The symmetric interval kernel is the usual real sinc kernel in the
repository's `2π` Fourier convention. -/
theorem inghamWindowKernel_eq_sinc {a : ℝ} (ha : 0 ≤ a) (t : ℝ) :
    inghamWindowKernel a t =
      (2 * a * Real.sinc (2 * Real.pi * t * a) : ℝ) := by
  rw [inghamWindowKernel, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -a ≤ a)]
  let k : ℝ := 2 * Real.pi * t
  by_cases hk : k = 0
  · have ht : t = 0 := by
      simpa [k, Real.pi_ne_zero] using hk
    subst t
    simp [gramPhase]
    ring
  · have hphase : (fun η : ℝ ↦ gramPhase t η) =
        fun η : ℝ ↦ Complex.exp ((k * η : ℝ) * Complex.I) := by
      funext η
      unfold gramPhase
      dsimp [k]
    rw [hphase]
    have hscale := intervalIntegral.integral_comp_mul_left
      (fun u : ℝ ↦ Complex.exp (u * Complex.I))
      (a := -a) (b := a) hk
    have hbase := integral_exp_mul_I_eq_sinc (k * a)
    rw [show k * -a = -(k * a) by ring] at hscale
    rw [hbase] at hscale
    rw [hscale]
    rw [Complex.real_smul]
    rw [show 2 * Real.pi * t * a = k * a by rfl]
    push_cast
    have hkc : (k : ℂ) ≠ 0 := by exact_mod_cast hk
    field_simp [hkc]

/-- Exact finite quadratic-form expansion of the Ingham window energy. -/
theorem integral_gramFourierPolynomial_sq_eq_windowKernel
    {n : ℕ} (x : Fin n → ℝ) (c : Fin n → ℂ) (a : ℝ) :
    (∫ η : ℝ in Set.Icc (-a) a,
        (‖gramFourierPolynomial x c η‖ ^ 2 : ℂ)) =
      ∑ i, ∑ j, conj (c i) * c j *
        inghamWindowKernel a (x j - x i) := by
  have hphase (t : ℝ) : Continuous (gramPhase t) := by
    unfold gramPhase
    fun_prop
  have hint (i j : Fin n) : Integrable
      (fun η : ℝ ↦ conj (c i) * c j * gramPhase (x j - x i) η)
      (volume.restrict (Set.Icc (-a) a)) := by
    exact ContinuousOn.integrableOn_compact isCompact_Icc
      ((continuous_const.mul (hphase (x j - x i))).continuousOn)
  have hpoint (η : ℝ) :
      (‖gramFourierPolynomial x c η‖ ^ 2 : ℂ) =
        ∑ i, ∑ j, conj (c i) * c j * gramPhase (x j - x i) η := by
    have hnorm : (‖gramFourierPolynomial x c η‖ : ℂ) ^ 2 =
        conj (gramFourierPolynomial x c η) *
          gramFourierPolynomial x c η := by
      calc
        (‖gramFourierPolynomial x c η‖ : ℂ) ^ 2 =
            ((‖gramFourierPolynomial x c η‖ ^ 2 : ℝ) : ℂ) := by norm_cast
        _ = (Complex.normSq (gramFourierPolynomial x c η) : ℂ) := by
          rw [Complex.normSq_eq_norm_sq]
        _ = conj (gramFourierPolynomial x c η) *
            gramFourierPolynomial x c η :=
          Complex.normSq_eq_conj_mul_self
    rw [hnorm]
    unfold gramFourierPolynomial
    calc
      conj (∑ i, c i * gramPhase (x i) η) *
          (∑ j, c j * gramPhase (x j) η) =
          (∑ i, conj (c i * gramPhase (x i) η)) *
            ∑ j, c j * gramPhase (x j) η := by rw [map_sum]
      _ = ∑ i, ∑ j,
          conj (c i * gramPhase (x i) η) *
            (c j * gramPhase (x j) η) := by rw [Fintype.sum_mul_sum]
      _ = ∑ i, ∑ j,
          conj (c i) * c j * gramPhase (x j - x i) η := by
        apply Finset.sum_congr rfl
        intro i _hi
        apply Finset.sum_congr rfl
        intro j _hj
        rw [map_mul, gramPhase_sub]
        ring
  calc
    (∫ η : ℝ in Set.Icc (-a) a,
        (‖gramFourierPolynomial x c η‖ ^ 2 : ℂ)) =
        ∫ η : ℝ in Set.Icc (-a) a,
          ∑ i, ∑ j,
            conj (c i) * c j * gramPhase (x j - x i) η := by
      apply integral_congr_ae
      exact ae_of_all _ hpoint
    _ = ∑ i, ∑ j,
        ∫ η : ℝ in Set.Icc (-a) a,
          conj (c i) * c j * gramPhase (x j - x i) η := by
      rw [integral_finsetSum Finset.univ (fun i _hi ↦
        integrable_finsetSum Finset.univ (fun j _hj ↦ hint i j))]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [integral_finsetSum Finset.univ (fun j _hj ↦ hint i j)]
    _ = ∑ i, ∑ j, conj (c i) * c j *
        inghamWindowKernel a (x j - x i) := by
      apply Finset.sum_congr rfl
      intro i _hi
      apply Finset.sum_congr rfl
      intro j _hj
      rw [inghamWindowKernel, integral_const_mul]

/-- Real form of the exact finite window-energy identity. -/
theorem integral_norm_gramFourierPolynomial_sq_eq_windowKernel_re
    {n : ℕ} (x : Fin n → ℝ) (c : Fin n → ℂ) (a : ℝ) :
    (∫ η : ℝ in Set.Icc (-a) a,
        ‖gramFourierPolynomial x c η‖ ^ 2) =
      (∑ i, ∑ j, conj (c i) * c j *
        inghamWindowKernel a (x j - x i)).re := by
  have henergy : IntegrableOn
      (fun η : ℝ ↦ ‖gramFourierPolynomial x c η‖ ^ 2)
      (Set.Icc (-a) a) := by
    exact ContinuousOn.integrableOn_compact isCompact_Icc
      ((continuous_gramFourierPolynomial x c).norm.pow 2).continuousOn
  have hcomplex := integral_gramFourierPolynomial_sq_eq_windowKernel x c a
  have hre := congrArg Complex.re hcomplex
  have hcomplex_int : Integrable
      (fun η : ℝ ↦ (‖gramFourierPolynomial x c η‖ ^ 2 : ℂ))
      (volume.restrict (Set.Icc (-a) a)) := by
    exact ContinuousOn.integrableOn_compact isCompact_Icc
      ((Complex.continuous_ofReal.comp (continuous_gramFourierPolynomial x c).norm).pow 2).continuousOn
  calc
    (∫ η : ℝ in Set.Icc (-a) a,
        ‖gramFourierPolynomial x c η‖ ^ 2) =
        ∫ η : ℝ in Set.Icc (-a) a,
          ((‖gramFourierPolynomial x c η‖ ^ 2 : ℂ)).re := by
      apply integral_congr_ae
      filter_upwards with η
      simp only [pow_two, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, sub_zero]
    _ = (∫ η : ℝ in Set.Icc (-a) a,
        (‖gramFourierPolynomial x c η‖ ^ 2 : ℂ)).re :=
      by simpa only [RCLike.re_to_complex] using integral_re hcomplex_int
    _ = (∑ i, ∑ j, conj (c i) * c j *
        inghamWindowKernel a (x j - x i)).re := hre

/-- Fully explicit sinc-matrix form of the finite Ingham window energy. -/
theorem integral_norm_gramFourierPolynomial_sq_eq_sinc
    {n : ℕ} (x : Fin n → ℝ) (c : Fin n → ℂ)
    {a : ℝ} (ha : 0 ≤ a) :
    (∫ η : ℝ in Set.Icc (-a) a,
        ‖gramFourierPolynomial x c η‖ ^ 2) =
      (∑ i, ∑ j, conj (c i) * c j *
        (2 * a * Real.sinc (2 * Real.pi * (x j - x i) * a) : ℝ)).re := by
  rw [integral_norm_gramFourierPolynomial_sq_eq_windowKernel_re]
  apply congrArg Complex.re
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  rw [inghamWindowKernel_eq_sinc ha]

/-- Pairwise real-frequency separation used by the finite Ingham theorem. -/
def PairwiseFrequencySeparated {n : ℕ} (x : Fin n → ℝ) (d : ℝ) : Prop :=
  ∀ i j, i ≠ j → d ≤ |x i - x j|

end

end MeyerGeneralProblem
