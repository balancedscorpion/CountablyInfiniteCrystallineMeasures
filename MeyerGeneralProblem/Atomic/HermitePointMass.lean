module

public import MeyerGeneralProblem.Hermite.Orthonormal

@[expose] public section

/-!
# Hermite coefficients of a Dirac mass

This module records the concrete normalized coefficient sequence of a Dirac
mass at `x`, proves its square summability at every integer order `m ≥ 1`, and
packages it as a genuine element of the negative Hermite scale.
-/

namespace MeyerGeneralProblem

noncomputable section

/-- The normalized order-`-m` Hermite coefficient sequence of evaluation at
`x`: `(1+n)^(-m) h_n(x)`.

The theorem `hermiteDiracCoefficients_memℓp` below proves that this sequence is
an element of `HermiteScale (-(m : ℤ))` whenever `m ≥ 1`.
-/
def hermiteDiracCoefficients (m : ℕ) (x : ℝ) (n : ℕ) : ℂ :=
  (hermiteScaleWeight (-(m : ℤ)) n : ℂ) *
    normalizedHermiteSchwartz n x

theorem hermiteDiracCoefficients_eq (m : ℕ) (x : ℝ) (n : ℕ) :
    hermiteDiracCoefficients m x n =
      ((((n : ℝ) + 1) ^ (-(m : ℤ)) : ℝ) : ℂ) *
        normalizedHermiteSchwartz n x :=
  rfl

@[simp]
theorem hermiteDiracCoefficients_zero_order (x : ℝ) (n : ℕ) :
    hermiteDiracCoefficients 0 x n = normalizedHermiteSchwartz n x := by
  simp [hermiteDiracCoefficients, hermiteScaleWeight]

private theorem hermiteScaleWeight_neg_nat_le_inv
    (m : ℕ) (hm : 1 ≤ m) (n : ℕ) :
    hermiteScaleWeight (-(m : ℤ)) n ≤ (((n : ℝ) + 1)⁻¹) := by
  rw [hermiteScaleWeight, zpow_neg, zpow_natCast]
  have hbase : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hp : ((n : ℝ) + 1) ^ 1 ≤ ((n : ℝ) + 1) ^ m :=
    pow_le_pow_right₀ hbase hm
  have hp' : (n : ℝ) + 1 ≤ ((n : ℝ) + 1) ^ m := by
    simpa only [pow_one] using hp
  exact (inv_le_inv₀ (by positivity : (0 : ℝ) < ((n : ℝ) + 1) ^ m)
      (by positivity : (0 : ℝ) < (n : ℝ) + 1)).mpr hp'

private theorem sqrt_div_sq (b : ℝ) (hb : 0 < b) :
    Real.sqrt b / b ^ 2 = 1 / b ^ (3 / 2 : ℝ) := by
  rw [Real.sqrt_eq_rpow]
  field_simp
  rw [← Real.rpow_natCast b 2, ← Real.rpow_add hb]
  norm_num

/-- The squared normalized Dirac coefficient is bounded by a convergent
`p = 3/2` majorant, uniformly in the evaluation point. -/
theorem hermiteDiracCoefficients_norm_sq_le
    (m : ℕ) (hm : 1 ≤ m) (x : ℝ) (n : ℕ) :
    ‖hermiteDiracCoefficients m x n‖ ^ 2 ≤
      (2 * Real.sqrt (2 * Real.pi)) /
        (((n : ℝ) + 1) ^ (3 / 2 : ℝ)) := by
  let b : ℝ := (n : ℝ) + 1
  have hb : 0 < b := by positivity
  have hwpos : 0 < hermiteScaleWeight (-(m : ℤ)) n :=
    hermiteScaleWeight_pos _ _
  have hw := hermiteScaleWeight_neg_nat_le_inv m hm n
  have hh := normalizedHermiteSchwartz_norm_sq_le n x
  rw [hermiteDiracCoefficients, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hwpos, mul_pow]
  calc
    hermiteScaleWeight (-(m : ℤ)) n ^ 2 *
        ‖normalizedHermiteSchwartz n x‖ ^ 2 ≤
      b⁻¹ ^ 2 *
        (2 * Real.sqrt (2 * Real.pi) * Real.sqrt b) := by
          gcongr
    _ = (2 * Real.sqrt (2 * Real.pi)) * (Real.sqrt b / b ^ 2) := by
      field_simp
    _ = (2 * Real.sqrt (2 * Real.pi)) / b ^ (3 / 2 : ℝ) := by
      rw [sqrt_div_sq b hb]
      ring
    _ = (2 * Real.sqrt (2 * Real.pi)) /
        (((n : ℝ) + 1) ^ (3 / 2 : ℝ)) := rfl

/-- Dirac evaluation belongs to every negative integer Hermite scale of order
at least one.  This is the first genuine point-evaluation summability theorem,
not an abstract coefficient-space hypothesis. -/
theorem hermiteDiracCoefficients_memℓp
    (m : ℕ) (hm : 1 ≤ m) (x : ℝ) :
    Memℓp (hermiteDiracCoefficients m x) 2 := by
  have hs₀ : Summable (fun n : ℕ =>
      1 / |(n : ℝ) + 1| ^ (3 / 2 : ℝ)) :=
    (Real.summable_one_div_nat_add_rpow 1 (3 / 2)).2 (by norm_num)
  have hs : Summable (fun n : ℕ =>
      (2 * Real.sqrt (2 * Real.pi)) /
        (((n : ℝ) + 1) ^ (3 / 2 : ℝ))) := by
    apply (hs₀.mul_left (2 * Real.sqrt (2 * Real.pi))).congr
    intro n
    rw [abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
    ring
  rw [memℓp_gen_iff (by norm_num : 0 < (2 : ENNReal).toReal)]
  simp only [ENNReal.toReal_ofNat]
  exact hs.of_nonneg_of_le
    (fun _ => Real.rpow_nonneg (norm_nonneg _) _) fun n => by
      simpa only [Real.rpow_two] using
        hermiteDiracCoefficients_norm_sq_le m hm x n

/-- The normalized Hermite coordinates of the Dirac mass at `x` in the
order-`-m` scale. -/
def hermitePointMass (m : ℕ) (hm : 1 ≤ m) (x : ℝ) :
    HermiteScale (-(m : ℤ)) :=
  ⟨hermiteDiracCoefficients m x,
    hermiteDiracCoefficients_memℓp m hm x⟩

@[simp]
theorem hermitePointMass_apply (m : ℕ) (hm : 1 ≤ m) (x : ℝ) (n : ℕ) :
    hermitePointMass m hm x n = hermiteDiracCoefficients m x n :=
  rfl

/-- Decoding the normalized negative-scale vector recovers the unweighted
Hermite coefficient `h_n(x)` of Dirac evaluation. -/
@[simp]
theorem rawHermiteCoefficients_hermitePointMass
    (m : ℕ) (hm : 1 ≤ m) (x : ℝ) (n : ℕ) :
    rawHermiteCoefficients (-(m : ℤ)) (hermitePointMass m hm x) n =
      normalizedHermiteSchwartz n x := by
  change (hermiteScaleWeight (-(m : ℤ)) n : ℂ)⁻¹ *
      ((hermiteScaleWeight (-(m : ℤ)) n : ℂ) *
        normalizedHermiteSchwartz n x) = _
  rw [← mul_assoc, inv_mul_cancel₀]
  · exact one_mul _
  · exact_mod_cast hermiteScaleWeight_ne_zero (-(m : ℤ)) n

/-- The raw coefficient of the packaged Hermite point mass is exactly Dirac
evaluation on the corresponding concrete Hermite test function. -/
theorem rawHermiteCoefficients_hermitePointMass_eq_pointMass
    (m : ℕ) (hm : 1 ≤ m) (x : ℝ) (n : ℕ) :
    rawHermiteCoefficients (-(m : ℤ)) (hermitePointMass m hm x) n =
      pointMass x (normalizedHermiteSchwartz n) := by
  rw [rawHermiteCoefficients_hermitePointMass,
    pointMass_normalizedHermiteSchwartz]

end

end MeyerGeneralProblem
