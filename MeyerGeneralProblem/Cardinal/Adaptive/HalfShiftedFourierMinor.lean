module

public import Mathlib.Analysis.SpecialFunctions.Complex.Log
import all Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.LinearAlgebra.Vandermonde
import all Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import all Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Tactic
import all Mathlib.Tactic

@[expose] public section

/-!
# The consecutive half-shifted Fourier minor

The flat-window minor in `HIGH_ORDER_GAP_SURGERY.md` §2 has modulus
`4*k^2`, row indices `-k^2+r` and column indices `k^2+c`, with both
indices ranging over `2*k^2` entries. The two half shifts and the Poisson
normalization `1/(2*k)` are retained. Its invertibility follows from this
particular consecutive Vandermonde factorization, including composite moduli.

This is a finite matrix theorem. The whole distributional comb transform
and its identification with these coordinates are separate obligations.
-/

namespace MeyerGeneralProblem.Adaptive

noncomputable section

def minorPhase (k : ℕ) (x : ℝ) : ℂ :=
  Complex.exp (((-2 * Real.pi / (4 * (k : ℝ)^2) * x : ℝ) : ℂ) * Complex.I)

private theorem minorPhase_add (k : ℕ) (x y : ℝ) :
    minorPhase k (x+y) = minorPhase k x * minorPhase k y := by
  simp only [minorPhase, mul_add, Complex.ofReal_add, add_mul, Complex.exp_add]

private theorem minorPhase_nat_mul (k n : ℕ) (x : ℝ) :
    minorPhase k ((n : ℝ)*x) = (minorPhase k x)^n := by
  unfold minorPhase
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

private theorem minorPhase_ne_zero (k : ℕ) (x : ℝ) : minorPhase k x ≠ 0 :=
  Complex.exp_ne_zero _

private theorem minorPhase_injective_half {k : ℕ} (hk : 1 ≤ k)
    {x y : ℝ} (hx0 : 0 ≤ x) (hxn : x < 2 * (k : ℝ)^2)
    (hy0 : 0 ≤ y) (hyn : y < 2 * (k : ℝ)^2)
    (hxy : minorPhase k x = minorPhase k y) : x = y := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hd : 0 < 4 * (k : ℝ)^2 := by positivity
  have lower (z : ℝ) (hz : z < 2 * (k : ℝ)^2) :
      -Real.pi < -2 * Real.pi / (4 * (k : ℝ)^2) * z := by
    rw [div_mul_eq_mul_div]
    apply (lt_div_iff₀ hd).2
    have h := mul_lt_mul_of_pos_left hz (show 0 < 2 * Real.pi by positivity)
    nlinarith
  have upper (z : ℝ) (hz : 0 ≤ z) :
      -2 * Real.pi / (4 * (k : ℝ)^2) * z ≤ Real.pi := by
    have hn : -2 * Real.pi / (4 * (k : ℝ)^2) * z ≤ 0 := by
      exact mul_nonpos_of_nonpos_of_nonneg (div_nonpos_of_nonpos_of_nonneg
        (by nlinarith [Real.pi_pos]) (le_of_lt hd)) hz
    linarith [Real.pi_pos]
  have he := Complex.exp_inj_of_neg_pi_lt_of_le_pi
    (x := (((-2 * Real.pi / (4 * (k : ℝ)^2) * x : ℝ) : ℂ) * Complex.I))
    (y := (((-2 * Real.pi / (4 * (k : ℝ)^2) * y : ℝ) : ℂ) * Complex.I))
    (by simpa only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one,
      Complex.ofReal_im, Complex.I_re, mul_zero, add_zero] using lower x hxn)
    (by simpa only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one,
      Complex.ofReal_im, Complex.I_re, mul_zero, add_zero] using upper x hx0)
    (by simpa only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one,
      Complex.ofReal_im, Complex.I_re, mul_zero, add_zero] using lower y hyn)
    (by simpa only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one,
      Complex.ofReal_im, Complex.I_re, mul_zero, add_zero] using upper y hy0) hxy
  have him := congrArg Complex.im he
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one,
    Complex.ofReal_im, Complex.I_re, mul_zero, add_zero] at him
  exact mul_left_cancel₀ (div_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
    (ne_of_gt hd)) him

/-- The actual roots indexed by the remaining consecutive columns. -/
def halfShiftedMinorNode (k : ℕ) (c : Fin (2*k^2)) : ℂ :=
  minorPhase k ((k : ℝ)^2 + c)

/-- The consecutive nodes are distinct without any primality hypothesis. -/
theorem halfShiftedMinorNode_injective {k : ℕ} (hk : 1 ≤ k) :
    Function.Injective (halfShiftedMinorNode k) := by
  intro c d h
  simp only [halfShiftedMinorNode, minorPhase_add] at h
  have hcd := mul_left_cancel₀ (minorPhase_ne_zero k ((k : ℝ)^2)) h
  have he : (c : ℝ) = (d : ℝ) := minorPhase_injective_half hk
    (by positivity) (by exact_mod_cast c.isLt)
    (by positivity) (by exact_mod_cast d.isLt) hcd
  apply Fin.ext
  exact_mod_cast he

/-- The normalized half-shifted Fourier submatrix on the flat physical holes
and the complementary consecutive coefficient block. -/
def halfShiftedFourierMinor (k : ℕ) : Matrix (Fin (2*k^2)) (Fin (2*k^2)) ℂ :=
  fun r c => ((2*(k : ℝ) : ℝ) : ℂ)⁻¹ *
    minorPhase k (((k : ℝ)^2 + c + 1/2) * (-(k : ℝ)^2 + r + 1/2))

/-- Entry formula in the original negative Fourier convention, exposing the
modulus, both half shifts and the normalization without auxiliary phase notation. -/
theorem halfShiftedFourierMinor_apply (k : ℕ) (r c : Fin (2*k^2)) :
    halfShiftedFourierMinor k r c = (1 / (2*(k : ℂ))) *
      Complex.exp (-2 * (Real.pi : ℂ) * Complex.I *
        ((k : ℂ)^2 + c + 1/2) * (-(k : ℂ)^2 + r + 1/2) /
          (4*(k : ℂ)^2)) := by
  unfold halfShiftedFourierMinor minorPhase
  push_cast
  rw [one_div]
  congr 2 <;> ring

def minorRowFactor (k : ℕ) (r : Fin (2*k^2)) : ℂ :=
  ((2*(k : ℝ) : ℝ) : ℂ)⁻¹ * minorPhase k ((r : ℝ)/2)

def minorColumnFactor (k : ℕ) (c : Fin (2*k^2)) : ℂ :=
  minorPhase k (((k : ℝ)^2 + c + 1/2) * (-(k : ℝ)^2 + 1/2))

/-- Exact diagonal-factor/Vandermonde factorization with both half shifts. -/
theorem halfShiftedFourierMinor_factorization (k : ℕ) :
    halfShiftedFourierMinor k =
      Matrix.diagonal (minorRowFactor k) *
        (Matrix.vandermonde (halfShiftedMinorNode k)).transpose *
          Matrix.diagonal (minorColumnFactor k) := by
  ext r c
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.transpose_apply,
    Matrix.vandermonde_apply, halfShiftedFourierMinor, minorRowFactor,
    minorColumnFactor, halfShiftedMinorNode]
  rw [← minorPhase_nat_mul, mul_assoc, mul_assoc, ← minorPhase_add, ← minorPhase_add]
  congr 2
  ring

/-- The specific consecutive half-shifted Fourier minor has nonzero determinant. -/
theorem halfShiftedFourierMinor_det_ne_zero {k : ℕ} (hk : 1 ≤ k) :
    (halfShiftedFourierMinor k).det ≠ 0 := by
  rw [halfShiftedFourierMinor_factorization, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_diagonal, Matrix.det_diagonal, Matrix.det_transpose]
  apply mul_ne_zero
  · apply mul_ne_zero
    · apply Finset.prod_ne_zero_iff.mpr
      intro r _
      exact mul_ne_zero (inv_ne_zero (by
        have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt (lt_of_lt_of_le Nat.zero_lt_one hk))
        exact_mod_cast mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hk0))
        (minorPhase_ne_zero _ _)
    · exact Matrix.det_vandermonde_ne_zero_iff.mpr (halfShiftedMinorNode_injective hk)
  · apply Finset.prod_ne_zero_iff.mpr
    intro c _
    exact minorPhase_ne_zero _ _

/-- Invertibility of the actual normalized finite minor, also at composite modulus. -/
theorem halfShiftedFourierMinor_isUnit {k : ℕ} (hk : 1 ≤ k) :
    IsUnit (halfShiftedFourierMinor k) :=
  (Matrix.isUnit_iff_isUnit_det _).mpr
    (isUnit_iff_ne_zero.mpr (halfShiftedFourierMinor_det_ne_zero hk))

/-- Vanishing of the Fourier holes determines every remaining coefficient. -/
theorem halfShiftedFourierMinor_mulVec_injective {k : ℕ} (hk : 1 ≤ k) :
    Function.Injective (halfShiftedFourierMinor k).mulVec :=
  Matrix.mulVec_injective_iff_isUnit.mpr (halfShiftedFourierMinor_isUnit hk)

end

end MeyerGeneralProblem.Adaptive
