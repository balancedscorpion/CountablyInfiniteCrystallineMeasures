module

public import MeyerGeneralProblem.Atomic.RieszSynthesis

@[expose] public section

/-!
# Hermite Hilbert scales in normalized coefficient coordinates

At each integer order, the weighted Hermite coefficient space is identified
isometrically with plain `ℓ²` by absorbing the order-dependent weight into the
coordinates.  Keeping the order in the type records which decoding is meant,
while the Fourier transform is the same diagonal fourth-root-of-unity unitary
on every normalized scale.
-/

namespace MeyerGeneralProblem

noncomputable section

open scoped ComplexConjugate

/-- The order-`m` Hermite Hilbert scale in normalized Hermite coordinates. -/
abbrev HermiteScale (_m : ℤ) := CoefficientSpace ℕ

/-- The raw Hermite coefficient of order `n` is normalized by
`(1+n)^m` in the order-`m` scale. -/
def hermiteScaleWeight (m : ℤ) (n : ℕ) : ℝ :=
  ((n : ℝ) + 1) ^ m

theorem hermiteScaleWeight_pos (m : ℤ) (n : ℕ) :
    0 < hermiteScaleWeight m n := by
  exact zpow_pos (by positivity) m

theorem hermiteScaleWeight_ne_zero (m : ℤ) (n : ℕ) :
    hermiteScaleWeight m n ≠ 0 :=
  (hermiteScaleWeight_pos m n).ne'

@[simp]
theorem hermiteScaleWeight_neg (m : ℤ) (n : ℕ) :
    hermiteScaleWeight (-m) n = (hermiteScaleWeight m n)⁻¹ := by
  simp [hermiteScaleWeight, zpow_neg]

@[simp]
theorem hermiteScaleWeight_zero (n : ℕ) :
    hermiteScaleWeight 0 n = 1 := by
  simp [hermiteScaleWeight]

theorem hermiteScaleWeight_add (m k : ℤ) (n : ℕ) :
    hermiteScaleWeight (m + k) n =
      hermiteScaleWeight m n * hermiteScaleWeight k n := by
  exact zpow_add₀ (by positivity) m k

@[simp]
theorem hermiteScaleWeight_neg_mul (m : ℤ) (n : ℕ) :
    hermiteScaleWeight (-m) n * hermiteScaleWeight m n = 1 := by
  rw [hermiteScaleWeight, hermiteScaleWeight, zpow_neg]
  exact inv_mul_cancel₀ (zpow_ne_zero m (by positivity))

/-- Normalize a raw Hermite coefficient sequence into order-`m`
coordinates.  Membership in `ℓ²` is the definition of belonging to the
weighted Hermite scale. -/
def normalizeHermiteCoefficients (m : ℤ) (u : ℕ → ℂ) (n : ℕ) : ℂ :=
  (hermiteScaleWeight m n : ℂ) * u n

/-- Raw Hermite coefficient sequences whose order-`m` normalization is
square-summable. -/
def RawHermiteScale (m : ℤ) :=
  {u : ℕ → ℂ // Memℓp (normalizeHermiteCoefficients m u) 2}

theorem mem_rawHermiteScale_iff (m : ℤ) (u : ℕ → ℂ) :
    Memℓp (normalizeHermiteCoefficients m u) 2 ↔
      Summable (fun n : ℕ =>
        hermiteScaleWeight m n ^ 2 * ‖u n‖ ^ 2) := by
  rw [memℓp_gen_iff (by norm_num : 0 < (2 : ENNReal).toReal)]
  apply summable_congr
  intro n
  simp only [normalizeHermiteCoefficients, ENNReal.toReal_ofNat,
    norm_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_pos (hermiteScaleWeight_pos m n)]
  rw [Real.rpow_two]
  exact mul_pow (hermiteScaleWeight m n) ‖u n‖ 2

/-- Recover raw Hermite coefficients from normalized order-`m`
coordinates. -/
def rawHermiteCoefficients (m : ℤ) (u : HermiteScale m) (n : ℕ) : ℂ :=
  (hermiteScaleWeight m n : ℂ)⁻¹ * u n

@[simp]
theorem normalize_rawHermiteCoefficients (m : ℤ) (u : HermiteScale m) :
    normalizeHermiteCoefficients m (rawHermiteCoefficients m u) = u := by
  funext n
  simp only [normalizeHermiteCoefficients, rawHermiteCoefficients]
  rw [← mul_assoc, mul_inv_cancel₀]
  · exact one_mul _
  · exact_mod_cast hermiteScaleWeight_ne_zero m n

/-- The normalized `ℓ²` realization of a raw order-`m` coefficient
sequence. -/
def normalizedRawHermite (m : ℤ) (u : RawHermiteScale m) : HermiteScale m :=
  ⟨normalizeHermiteCoefficients m u.1, u.property⟩

@[simp]
theorem raw_normalizedRawHermite (m : ℤ) (u : RawHermiteScale m) :
    rawHermiteCoefficients m (normalizedRawHermite m u) = u.1 := by
  funext n
  change (hermiteScaleWeight m n : ℂ)⁻¹ *
      ((hermiteScaleWeight m n : ℂ) * u.1 n) = u.1 n
  rw [← mul_assoc, inv_mul_cancel₀]
  · exact one_mul _
  · exact_mod_cast hermiteScaleWeight_ne_zero m n

/-- The usual weighted definition
`sum (1+n)^(2m) |u_n|^2 < ∞` is equivalent to the normalized `ℓ²`
coordinate model used throughout the operator proof. -/
def hermiteScaleRawEquiv (m : ℤ) : HermiteScale m ≃ RawHermiteScale m where
  toFun u :=
    ⟨rawHermiteCoefficients m u,
      by
        rw [show normalizeHermiteCoefficients m
          (rawHermiteCoefficients m u) = u from
            normalize_rawHermiteCoefficients m u]
        exact u.property⟩
  invFun := normalizedRawHermite m
  left_inv u := by
    apply Subtype.ext
    change normalizeHermiteCoefficients m
      (rawHermiteCoefficients m u) = u
    exact normalize_rawHermiteCoefficients m u
  right_inv u := by
    apply Subtype.ext
    exact raw_normalizedRawHermite m u

/-- The bilinear coefficient pairing between the dual scales `H_(-m)` and
`H_m`.  With the usual identification of a distribution with its Hermite
coefficients this is its action on a test vector. -/
def hermiteScalePairing (m : ℤ)
    (T : HermiteScale (-m)) (u : HermiteScale m) : ℂ :=
  ∑' n : ℕ, T n * u n

theorem summable_hermiteScalePairing (m : ℤ)
    (T : HermiteScale (-m)) (u : HermiteScale m) :
    Summable (fun n : ℕ => T n * u n) := by
  apply Summable.of_norm_bounded
    (lp.summable_mul (p := (2 : ENNReal)) (q := (2 : ENNReal))
      (by rw [Real.holderConjugate_iff]; norm_num) T u)
  intro n
  simp only [norm_mul]
  exact le_rfl

theorem norm_hermiteScalePairing_le (m : ℤ)
    (T : HermiteScale (-m)) (u : HermiteScale m) :
    ‖hermiteScalePairing m T u‖ ≤ ‖T‖ * ‖u‖ := by
  calc
    ‖hermiteScalePairing m T u‖ ≤ ∑' n : ℕ, ‖T n * u n‖ :=
      norm_tsum_le_tsum_norm (summable_hermiteScalePairing m T u).norm
    _ = ∑' n : ℕ, ‖T n‖ * ‖u n‖ := by
      congr 1
      funext n
      exact norm_mul _ _
    _ ≤ ‖T‖ * ‖u‖ :=
      lp.tsum_mul_le_mul_norm'
        (by rw [Real.holderConjugate_iff]; norm_num) T u

/-- The order weights in the raw `H_(-m)`--`H_m` pairing cancel exactly. -/
theorem rawHermiteCoefficients_dual_term (m : ℤ)
    (T : HermiteScale (-m)) (u : HermiteScale m) (n : ℕ) :
    rawHermiteCoefficients (-m) T n * rawHermiteCoefficients m u n =
      T n * u n := by
  have hw : (hermiteScaleWeight m n : ℂ) ≠ 0 := by
    exact_mod_cast hermiteScaleWeight_ne_zero m n
  have hcast : (((hermiteScaleWeight m n)⁻¹ : ℝ) : ℂ) =
      (hermiteScaleWeight m n : ℂ)⁻¹ := by
    norm_cast
  have hnegWeight :
      (hermiteScaleWeight (-m) n : ℂ)⁻¹ =
        (hermiteScaleWeight m n : ℂ) := by
    calc
      (hermiteScaleWeight (-m) n : ℂ)⁻¹ =
          ((((hermiteScaleWeight m n)⁻¹ : ℝ) : ℂ))⁻¹ := by
            rw [hermiteScaleWeight_neg]
      _ = ((hermiteScaleWeight m n : ℂ)⁻¹)⁻¹ :=
        congrArg Inv.inv hcast
      _ = (hermiteScaleWeight m n : ℂ) := inv_inv _
  have hrawNeg : rawHermiteCoefficients (-m) T n =
      (hermiteScaleWeight m n : ℂ) * T n := by
    unfold rawHermiteCoefficients
    exact congrArg (fun z : ℂ => z * T n) hnegWeight
  have hrawPos : rawHermiteCoefficients m u n =
      (hermiteScaleWeight m n : ℂ)⁻¹ * u n := rfl
  rw [hrawNeg, hrawPos]
  field_simp

theorem hermiteScalePairing_eq_raw (m : ℤ)
    (T : HermiteScale (-m)) (u : HermiteScale m) :
    hermiteScalePairing m T u =
      ∑' n : ℕ,
        rawHermiteCoefficients (-m) T n * rawHermiteCoefficients m u n := by
  apply tsum_congr
  intro n
  exact (rawHermiteCoefficients_dual_term m T u n).symm

/-- Fourier eigenvalue of the `n`th normalized Hermite coordinate. -/
def hermiteFourierPhase (n : ℕ) : ℂ :=
  (-Complex.I) ^ n

@[simp]
theorem norm_hermiteFourierPhase (n : ℕ) :
    ‖hermiteFourierPhase n‖ = 1 := by
  simp [hermiteFourierPhase]

@[simp]
theorem conj_hermiteFourierPhase_mul (n : ℕ) :
    conj (hermiteFourierPhase n) * hermiteFourierPhase n = 1 := by
  rw [← Complex.normSq_eq_conj_mul_self]
  simp [Complex.normSq_eq_norm_sq]

/-- The Fourier-phase twist of the canonical coefficient basis. -/
def hermiteFourierAtom (n : ℕ) : CoefficientSpace ℕ :=
  hermiteFourierPhase n • coefficientAtom n

theorem orthonormal_hermiteFourierAtom :
    Orthonormal ℂ hermiteFourierAtom := by
  rw [orthonormal_iff_ite]
  intro i j
  simp only [hermiteFourierAtom, inner_smul_left, inner_smul_right]
  change hermiteFourierPhase j *
      (conj (hermiteFourierPhase i) *
        inner ℂ ((coefficientHilbertBasis ℕ) i)
          ((coefficientHilbertBasis ℕ) j)) = _
  rw [orthonormal_iff_ite.mp (coefficientHilbertBasis ℕ).orthonormal i j]
  split_ifs with hij
  · subst j
    simpa [mul_comm] using conj_hermiteFourierPhase_mul i
  · simp

theorem hermiteFourierAtom_dense_span :
    ⊤ ≤ (Submodule.span ℂ (Set.range hermiteFourierAtom)).topologicalClosure := by
  rw [← coefficientAtom_dense_span]
  apply Submodule.topologicalClosure_mono
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  have hatom : hermiteFourierAtom i ∈
      Submodule.span ℂ (Set.range hermiteFourierAtom) :=
    Submodule.subset_span ⟨i, rfl⟩
  have hsmul := (Submodule.span ℂ
    (Set.range hermiteFourierAtom)).smul_mem
      (conj (hermiteFourierPhase i)) hatom
  change coefficientAtom i ∈
    Submodule.span ℂ (Set.range hermiteFourierAtom)
  simpa only [hermiteFourierAtom, smul_smul,
    conj_hermiteFourierPhase_mul, one_smul] using hsmul

/-- The Fourier-twisted Hilbert basis. -/
def hermiteFourierHilbertBasis :
    HilbertBasis ℕ ℂ (CoefficientSpace ℕ) :=
  HilbertBasis.mk orthonormal_hermiteFourierAtom
    hermiteFourierAtom_dense_span

@[simp]
theorem hermiteFourierHilbertBasis_apply (n : ℕ) :
    hermiteFourierHilbertBasis n = hermiteFourierAtom n := by
  exact congrFun (HilbertBasis.coe_mk orthonormal_hermiteFourierAtom
    hermiteFourierAtom_dense_span) n

/-- Fourier transform on normalized Hermite coordinates. -/
def hermiteFourier (m : ℤ) : HermiteScale m ≃ₗᵢ[ℂ] HermiteScale m :=
  (coefficientHilbertBasis ℕ).repr.trans
    (hermiteFourierHilbertBasis.repr.symm)

@[simp]
theorem hermiteFourier_coefficientAtom (m : ℤ) (n : ℕ) :
    hermiteFourier m (coefficientAtom n) =
      hermiteFourierPhase n • coefficientAtom n := by
  change hermiteFourierHilbertBasis.repr.symm
      ((coefficientHilbertBasis ℕ).repr ((coefficientHilbertBasis ℕ) n)) =
    hermiteFourierPhase n • (coefficientHilbertBasis ℕ) n
  rw [HilbertBasis.repr_self,
    HilbertBasis.repr_symm_single,
    hermiteFourierHilbertBasis_apply]
  rfl

theorem hermiteFourier_norm (m : ℤ) (f : HermiteScale m) :
    ‖hermiteFourier m f‖ = ‖f‖ :=
  (hermiteFourier m).norm_map f

@[simp]
theorem hermiteFourierPhase_pow_four (n : ℕ) :
    hermiteFourierPhase n ^ 4 = 1 := by
  unfold hermiteFourierPhase
  rw [← pow_mul, Nat.mul_comm n 4, pow_mul]
  rw [(by decide : Even 4).neg_pow Complex.I,
    Complex.I_pow_four, one_pow]

/-- Four applications of Fourier are the identity on every normalized
Hermite scale. -/
theorem hermiteFourier_fourth (m : ℤ) (f : HermiteScale m) :
    hermiteFourier m
        (hermiteFourier m
          (hermiteFourier m (hermiteFourier m f))) = f := by
  let F : HermiteScale m →L[ℂ] HermiteScale m :=
    (hermiteFourier m).toContinuousLinearEquiv.toContinuousLinearMap
  have hdense : Dense
      (Submodule.span ℂ
        (Set.range (coefficientAtom : ℕ → HermiteScale m)) :
          Set (HermiteScale m)) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top]
    exact coefficientAtom_dense_span
  have hfourth : F.comp (F.comp (F.comp F)) =
      ContinuousLinearMap.id ℂ (HermiteScale m) := by
    apply ContinuousLinearMap.ext_on hdense
    rintro _ ⟨n, rfl⟩
    change hermiteFourier m
        (hermiteFourier m
          (hermiteFourier m (hermiteFourier m (coefficientAtom n)))) =
      coefficientAtom n
    simp only [hermiteFourier_coefficientAtom, map_smul, smul_smul]
    have hphase := congrArg
      (fun z : ℂ => z • coefficientAtom n)
      (hermiteFourierPhase_pow_four n)
    simpa only [pow_succ, pow_zero, one_mul, one_smul] using hphase
  exact congrArg (fun T : HermiteScale m →L[ℂ] HermiteScale m => T f)
    hfourth

end

end MeyerGeneralProblem
