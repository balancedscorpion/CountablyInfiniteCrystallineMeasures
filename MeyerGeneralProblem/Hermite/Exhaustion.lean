module

public import MeyerGeneralProblem.Hermite.ScaleEmbedding

@[expose] public section

/-!
# Exhaustion of tempered distributions by negative Hermite scales

This module records the analytic estimates used to identify the strong dual
of Schwartz space with the union of the negative Hermite Hilbert scales.
-/

open MeasureTheory
open scoped NNReal SchwartzMap

namespace MeyerGeneralProblem

noncomputable section

/-- A continuous tempered distribution is bounded by finitely many seminorms
in the concrete Schwartz seminorm presentation.  The
constant is chosen nonzero so that it can subsequently be enlarged without a
degenerate case split. -/
theorem temperedDistribution_norm_le_finsetSchwartzSeminorm
    (T : TemperedDistribution ℝ ℂ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ≥0, C ≠ 0 ∧
      ∀ f : SchwartzMap ℝ ℂ,
        ‖T f‖ ≤ C * s.sup (schwartzSeminormFamily ℂ ℝ ℂ) f := by
  let q : Seminorm ℂ (SchwartzMap ℝ ℂ) :=
    (normSeminorm ℂ ℂ).comp T.toLinearMap
  have hq : Continuous q := by
    exact continuous_norm.comp T.continuous
  obtain ⟨s, C, hC, hbound⟩ :=
    Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ ℝ ℂ) q hq
  exact ⟨s, C, hC, fun f => hbound f⟩

/-- Raising coefficient in the Fourier-normalized position ladder. -/
def hermitePositionUp (n : ℕ) : ℂ :=
  ((Real.sqrt (((n : ℝ) + 1) / 2) / Real.sqrt (2 * Real.pi) : ℝ) : ℂ)

/-- Lowering coefficient in the Fourier-normalized position ladder. -/
def hermitePositionDown (n : ℕ) : ℂ :=
  ((Real.sqrt ((n : ℝ) / 2) / Real.sqrt (2 * Real.pi) : ℝ) : ℂ)

/-- Lowering coefficient in the Fourier-normalized derivative ladder. -/
def hermiteDerivativeDown (n : ℕ) : ℂ :=
  ((Real.sqrt (2 * Real.pi) * Real.sqrt ((n : ℝ) / 2) : ℝ) : ℂ)

/-- Raising coefficient in the Fourier-normalized derivative ladder. -/
def hermiteDerivativeUp (n : ℕ) : ℂ :=
  ((Real.sqrt (2 * Real.pi) * Real.sqrt (((n : ℝ) + 1) / 2) : ℝ) : ℂ)

/-- The position ladder relation for the Fourier-normalized complex Hermite
family, bundled as an equality in Schwartz space. -/
theorem coordinateMultiplication_normalizedHermiteSchwartz (n : ℕ) :
    coordinateMultiplicationCLM (normalizedHermiteSchwartz n) =
      hermitePositionUp n • normalizedHermiteSchwartz (n + 1) +
        hermitePositionDown n • normalizedHermiteSchwartz (n - 1) := by
  ext x
  rw [coordinateMultiplicationCLM_apply,
    normalizedHermiteSchwartz_eq_twoPi,
    TauCeti.twoPiHermiteSchwartzMap_apply]
  simp only [add_apply, smul_apply, smul_eq_mul, hermitePositionUp,
    hermitePositionDown]
  rw [normalizedHermiteSchwartz_eq_twoPi (n + 1),
    normalizedHermiteSchwartz_eq_twoPi (n - 1),
    TauCeti.twoPiHermiteSchwartzMap_apply,
    TauCeti.twoPiHermiteSchwartzMap_apply]
  exact_mod_cast TauCeti.mul_twoPiHermiteFunction n x

private theorem deriv_twoPiHermiteFunction_ofReal (n : ℕ) (x : ℝ) :
    deriv (fun y : ℝ => (TauCeti.twoPiHermiteFunction n y : ℂ)) x =
      ((deriv (TauCeti.twoPiHermiteFunction n) : ℝ → ℝ) x : ℂ) := by
  have h := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x
    ((TauCeti.hasDerivAt_twoPiHermiteFunction n x).differentiableAt.hasDerivAt)
  change deriv (Complex.ofRealCLM ∘ TauCeti.twoPiHermiteFunction n) x = _
  simpa only [Complex.ofRealCLM_apply] using h.deriv

/-- The derivative ladder relation for the Fourier-normalized complex
Hermite family, bundled as an equality in Schwartz space. -/
theorem deriv_normalizedHermiteSchwartz (n : ℕ) :
    SchwartzMap.derivCLM ℂ ℂ (normalizedHermiteSchwartz n) =
      hermiteDerivativeDown n • normalizedHermiteSchwartz (n - 1) -
        hermiteDerivativeUp n • normalizedHermiteSchwartz (n + 1) := by
  ext x
  rw [SchwartzMap.derivCLM_apply,
    normalizedHermiteSchwartz_eq_twoPi,
    TauCeti.coe_twoPiHermiteSchwartzMap,
    deriv_twoPiHermiteFunction_ofReal,
    TauCeti.deriv_twoPiHermiteFunction]
  simp only [sub_apply, smul_apply, smul_eq_mul, hermiteDerivativeDown,
    hermiteDerivativeUp]
  rw [normalizedHermiteSchwartz_eq_twoPi (n - 1),
    normalizedHermiteSchwartz_eq_twoPi (n + 1),
    TauCeti.twoPiHermiteSchwartzMap_apply,
    TauCeti.twoPiHermiteSchwartzMap_apply]
  push_cast
  ring

/-- The `(k,l)` Schwartz seminorm of the `n`th normalized Hermite
function. -/
def normalizedHermiteSchwartzSeminorm (k l n : ℕ) : ℝ :=
  SchwartzMap.seminorm ℂ k l (normalizedHermiteSchwartz n)

private theorem normalizedHermiteSchwartzSeminorm_position
    (k n : ℕ) :
    normalizedHermiteSchwartzSeminorm (k + 1) 0 n ≤
      ‖hermitePositionUp n‖ * normalizedHermiteSchwartzSeminorm k 0 (n + 1) +
        ‖hermitePositionDown n‖ * normalizedHermiteSchwartzSeminorm k 0 (n - 1) := by
  let p : Seminorm ℂ (SchwartzMap ℝ ℂ) := SchwartzMap.seminorm ℂ k 0
  let Xn : SchwartzMap ℝ ℂ := coordinateMultiplicationCLM (normalizedHermiteSchwartz n)
  have hfirst : normalizedHermiteSchwartzSeminorm (k + 1) 0 n ≤ p Xn := by
    apply SchwartzMap.seminorm_le_bound' ℂ (k + 1) 0
      (normalizedHermiteSchwartz n) (apply_nonneg p Xn)
    intro x
    have hx := SchwartzMap.le_seminorm' ℂ k 0 Xn x
    simp only [iteratedDeriv_zero] at hx ⊢
    change |x| ^ (k + 1) * ‖normalizedHermiteSchwartz n x‖ ≤ _
    change |x| ^ k * ‖Xn x‖ ≤ _ at hx
    rw [show Xn x = (x : ℂ) * normalizedHermiteSchwartz n x by
      exact coordinateMultiplicationCLM_apply _ _] at hx
    simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, pow_succ,
      mul_assoc] using hx
  refine hfirst.trans ?_
  rw [show Xn = hermitePositionUp n • normalizedHermiteSchwartz (n + 1) +
      hermitePositionDown n • normalizedHermiteSchwartz (n - 1) by
    exact coordinateMultiplication_normalizedHermiteSchwartz n]
  exact (map_add_le_add p _ _).trans_eq (by
    rw [map_smul_eq_mul, map_smul_eq_mul]
    rfl)

private theorem normalizedHermiteSchwartzSeminorm_derivative
    (k l n : ℕ) :
    normalizedHermiteSchwartzSeminorm k (l + 1) n ≤
      ‖hermiteDerivativeDown n‖ * normalizedHermiteSchwartzSeminorm k l (n - 1) +
        ‖hermiteDerivativeUp n‖ * normalizedHermiteSchwartzSeminorm k l (n + 1) := by
  let p : Seminorm ℂ (SchwartzMap ℝ ℂ) := SchwartzMap.seminorm ℂ k l
  let Dn : SchwartzMap ℝ ℂ :=
    SchwartzMap.derivCLM ℂ ℂ (normalizedHermiteSchwartz n)
  have hfirst : normalizedHermiteSchwartzSeminorm k (l + 1) n ≤ p Dn := by
    apply SchwartzMap.seminorm_le_bound' ℂ k (l + 1)
      (normalizedHermiteSchwartz n) (apply_nonneg p Dn)
    intro x
    have hx := SchwartzMap.le_seminorm' ℂ k l Dn x
    change |x| ^ k * ‖iteratedDeriv (l + 1)
      (normalizedHermiteSchwartz n) x‖ ≤ _
    rw [iteratedDeriv_succ']
    have hDn : ⇑Dn = deriv (⇑(normalizedHermiteSchwartz n)) :=
      funext (SchwartzMap.derivCLM_apply ℂ (normalizedHermiteSchwartz n))
    rwa [hDn] at hx
  refine hfirst.trans ?_
  rw [show Dn = hermiteDerivativeDown n • normalizedHermiteSchwartz (n - 1) -
      hermiteDerivativeUp n • normalizedHermiteSchwartz (n + 1) by
    exact deriv_normalizedHermiteSchwartz n]
  exact (map_sub_le_add p _ _).trans_eq (by
    rw [map_smul_eq_mul, map_smul_eq_mul]
    rfl)

/-- A real sequence has at most polynomial growth.  Keeping the exponent
existential makes this interface stable under the finite ladder operations
used below. -/
def NatPolynomiallyBounded (a : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ d : ℕ, ∀ n : ℕ,
    a n ≤ C * ((n : ℝ) + 1) ^ d

namespace NatPolynomiallyBounded

theorem mono {a b : ℕ → ℝ} (hb : NatPolynomiallyBounded b)
    (hab : ∀ n, a n ≤ b n) : NatPolynomiallyBounded a := by
  obtain ⟨C, hC, d, hd⟩ := hb
  exact ⟨C, hC, d, fun n => (hab n).trans (hd n)⟩

theorem add {a b : ℕ → ℝ} (ha : NatPolynomiallyBounded a)
    (hb : NatPolynomiallyBounded b) :
    NatPolynomiallyBounded (fun n => a n + b n) := by
  obtain ⟨A, hA, d, hd⟩ := ha
  obtain ⟨B, hB, e, he⟩ := hb
  refine ⟨A + B, add_nonneg hA hB, d + e, fun n => ?_⟩
  have hn0 : (0 : ℝ) ≤ n := by exact_mod_cast Nat.zero_le n
  have hbase : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith
  calc
    a n + b n ≤ A * ((n : ℝ) + 1) ^ d +
        B * ((n : ℝ) + 1) ^ e := add_le_add (hd n) (he n)
    _ ≤ A * ((n : ℝ) + 1) ^ (d + e) +
        B * ((n : ℝ) + 1) ^ (d + e) := by
      gcongr
      · exact Nat.le_add_right d e
      · exact Nat.le_add_left e d
    _ = (A + B) * ((n : ℝ) + 1) ^ (d + e) := by ring

theorem mul {a b : ℕ → ℝ} (_ha0 : ∀ n, 0 ≤ a n)
    (hb0 : ∀ n, 0 ≤ b n) (ha : NatPolynomiallyBounded a)
    (hb : NatPolynomiallyBounded b) :
    NatPolynomiallyBounded (fun n => a n * b n) := by
  obtain ⟨A, hA, d, hd⟩ := ha
  obtain ⟨B, hB, e, he⟩ := hb
  refine ⟨A * B, mul_nonneg hA hB, d + e, fun n => ?_⟩
  calc
    a n * b n ≤ (A * ((n : ℝ) + 1) ^ d) *
        (B * ((n : ℝ) + 1) ^ e) :=
      mul_le_mul (hd n) (he n) (hb0 n) (mul_nonneg hA (by positivity))
    _ = (A * B) * ((n : ℝ) + 1) ^ (d + e) := by rw [pow_add]; ring

theorem succ {a : ℕ → ℝ} (ha : NatPolynomiallyBounded a) :
    NatPolynomiallyBounded (fun n => a (n + 1)) := by
  obtain ⟨A, hA, d, hd⟩ := ha
  refine ⟨A * 2 ^ d, mul_nonneg hA (by positivity), d, fun n => ?_⟩
  calc
    a (n + 1) ≤ A * (((n + 1 : ℕ) : ℝ) + 1) ^ d := hd (n + 1)
    _ ≤ A * (2 * ((n : ℝ) + 1)) ^ d := by
      gcongr
      have hn0 : (0 : ℝ) ≤ n := by exact_mod_cast Nat.zero_le n
      norm_num
      linarith
    _ = (A * 2 ^ d) * ((n : ℝ) + 1) ^ d := by rw [mul_pow]; ring

theorem pred {a : ℕ → ℝ} (ha : NatPolynomiallyBounded a) :
    NatPolynomiallyBounded (fun n => a (n - 1)) := by
  obtain ⟨A, hA, d, hd⟩ := ha
  refine ⟨A, hA, d, fun n => (hd (n - 1)).trans ?_⟩
  gcongr
  exact_mod_cast Nat.sub_le n 1

theorem const_mul (A : ℝ) (hA : 0 ≤ A) {a : ℕ → ℝ}
    (ha : NatPolynomiallyBounded a) :
    NatPolynomiallyBounded (fun n => A * a n) := by
  obtain ⟨C, hC, d, hd⟩ := ha
  refine ⟨A * C, mul_nonneg hA hC, d, fun n => ?_⟩
  exact (mul_le_mul_of_nonneg_left (hd n) hA).trans_eq (by ring)

end NatPolynomiallyBounded

private theorem hermitePositionUp_polynomiallyBounded :
    NatPolynomiallyBounded (fun n => ‖hermitePositionUp n‖) := by
  let A : ℝ := (Real.sqrt (2 * Real.pi))⁻¹
  refine ⟨A, inv_nonneg.mpr (Real.sqrt_nonneg _), 1, fun n => ?_⟩
  have hs : Real.sqrt (((n : ℝ) + 1) / 2) ≤ (n : ℝ) + 1 := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · have hn : (0 : ℝ) ≤ n := by positivity
      nlinarith
  simp only [hermitePositionUp, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)), pow_one]
  dsimp only [A]
  rw [div_eq_mul_inv]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_right hs
    (inv_nonneg.mpr (Real.sqrt_nonneg (2 * Real.pi)))

private theorem hermitePositionDown_polynomiallyBounded :
    NatPolynomiallyBounded (fun n => ‖hermitePositionDown n‖) := by
  let A : ℝ := (Real.sqrt (2 * Real.pi))⁻¹
  refine ⟨A, inv_nonneg.mpr (Real.sqrt_nonneg _), 1, fun n => ?_⟩
  have hs : Real.sqrt ((n : ℝ) / 2) ≤ (n : ℝ) + 1 := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · have hn : (0 : ℝ) ≤ n := by positivity
      nlinarith
  simp only [hermitePositionDown, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)), pow_one]
  dsimp only [A]
  rw [div_eq_mul_inv]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_right hs
    (inv_nonneg.mpr (Real.sqrt_nonneg (2 * Real.pi)))

private theorem hermiteDerivativeDown_polynomiallyBounded :
    NatPolynomiallyBounded (fun n => ‖hermiteDerivativeDown n‖) := by
  let A : ℝ := Real.sqrt (2 * Real.pi)
  refine ⟨A, Real.sqrt_nonneg _, 1, fun n => ?_⟩
  have hs : Real.sqrt ((n : ℝ) / 2) ≤ (n : ℝ) + 1 := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · have hn : (0 : ℝ) ≤ n := by positivity
      nlinarith
  simp only [hermiteDerivativeDown, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)), pow_one]
  dsimp only [A]
  exact mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg _)

private theorem hermiteDerivativeUp_polynomiallyBounded :
    NatPolynomiallyBounded (fun n => ‖hermiteDerivativeUp n‖) := by
  let A : ℝ := Real.sqrt (2 * Real.pi)
  refine ⟨A, Real.sqrt_nonneg _, 1, fun n => ?_⟩
  have hs : Real.sqrt (((n : ℝ) + 1) / 2) ≤ (n : ℝ) + 1 := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · have hn : (0 : ℝ) ≤ n := by positivity
      nlinarith
  simp only [hermiteDerivativeUp, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)), pow_one]
  dsimp only [A]
  exact mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg _)

private theorem normalizedHermiteSchwartzSeminorm_zero_zero_polynomiallyBounded :
    NatPolynomiallyBounded
      (fun n => normalizedHermiteSchwartzSeminorm 0 0 n) := by
  let K : ℝ := 2 * Real.sqrt (2 * Real.pi)
  refine ⟨1 + K, by dsimp only [K]; positivity, 1, fun n => ?_⟩
  apply SchwartzMap.seminorm_le_bound' ℂ 0 0 (normalizedHermiteSchwartz n)
  · dsimp only [K]
    positivity
  intro x
  simp only [pow_zero, one_mul, iteratedDeriv_zero, pow_one]
  have hsq := normalizedHermiteSchwartz_norm_sq_le n x
  have hnorm : ‖normalizedHermiteSchwartz n x‖ ≤
      1 + ‖normalizedHermiteSchwartz n x‖ ^ 2 := by
    nlinarith [sq_nonneg (‖normalizedHermiteSchwartz n x‖ - 1)]
  have hsqrt : Real.sqrt ((n : ℝ) + 1) ≤ (n : ℝ) + 1 := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · have hn : (0 : ℝ) ≤ n := by positivity
      nlinarith
  calc
    ‖normalizedHermiteSchwartz n x‖ ≤
        1 + ‖normalizedHermiteSchwartz n x‖ ^ 2 := hnorm
    _ ≤ 1 + K * Real.sqrt ((n : ℝ) + 1) := by
      dsimp only [K]
      gcongr
    _ ≤ 1 + K * ((n : ℝ) + 1) := by
      gcongr
    _ ≤ (1 + K) * ((n : ℝ) + 1) := by
      have hn : (0 : ℝ) ≤ n := by positivity
      nlinarith [show 0 ≤ K by dsimp only [K]; positivity]

/-- Every fixed Schwartz seminorm of the normalized Hermite family grows at
most polynomially in the Hermite index.  This is the key quantitative output
of the two ladder relations. -/
theorem normalizedHermiteSchwartzSeminorm_polynomiallyBounded (k l : ℕ) :
    NatPolynomiallyBounded
      (fun n => normalizedHermiteSchwartzSeminorm k l n) := by
  have hposition : ∀ k : ℕ,
      NatPolynomiallyBounded
        (fun n => normalizedHermiteSchwartzSeminorm k 0 n) := by
    intro j
    induction j with
    | zero => exact normalizedHermiteSchwartzSeminorm_zero_zero_polynomiallyBounded
    | succ j ih =>
        apply NatPolynomiallyBounded.mono
          (NatPolynomiallyBounded.add
            (NatPolynomiallyBounded.mul (fun _ => norm_nonneg _)
              (fun _ => apply_nonneg _ _)
              hermitePositionUp_polynomiallyBounded
              (NatPolynomiallyBounded.succ ih))
            (NatPolynomiallyBounded.mul (fun _ => norm_nonneg _)
              (fun _ => apply_nonneg _ _)
              hermitePositionDown_polynomiallyBounded
              (NatPolynomiallyBounded.pred ih)))
        intro n
        simpa only [Nat.succ_eq_add_one, normalizedHermiteSchwartzSeminorm] using
          normalizedHermiteSchwartzSeminorm_position j n
  induction l with
  | zero => exact hposition k
  | succ l ih =>
      apply NatPolynomiallyBounded.mono
        (NatPolynomiallyBounded.add
          (NatPolynomiallyBounded.mul (fun _ => norm_nonneg _)
            (fun _ => apply_nonneg _ _)
            hermiteDerivativeDown_polynomiallyBounded
            (NatPolynomiallyBounded.pred ih))
          (NatPolynomiallyBounded.mul (fun _ => norm_nonneg _)
            (fun _ => apply_nonneg _ _)
            hermiteDerivativeUp_polynomiallyBounded
            (NatPolynomiallyBounded.succ ih)))
      intro n
      simpa only [Nat.succ_eq_add_one, normalizedHermiteSchwartzSeminorm] using
        normalizedHermiteSchwartzSeminorm_derivative k l n

private theorem finsetSup_normalizedHermiteSchwartzSeminorm_polynomiallyBounded
    (s : Finset (ℕ × ℕ)) :
    NatPolynomiallyBounded (fun n =>
      s.sup (schwartzSeminormFamily ℂ ℝ ℂ) (normalizedHermiteSchwartz n)) := by
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨0, le_rfl, 0, fun n => ?_⟩
      simp
  | @insert a s ha ih =>
      apply NatPolynomiallyBounded.mono
        (NatPolynomiallyBounded.add
          (normalizedHermiteSchwartzSeminorm_polynomiallyBounded a.1 a.2) ih)
      intro n
      rw [Finset.sup_insert]
      change max
          (normalizedHermiteSchwartzSeminorm a.1 a.2 n)
          (s.sup (schwartzSeminormFamily ℂ ℝ ℂ)
            (normalizedHermiteSchwartz n)) ≤ _
      exact max_le_add_of_nonneg
        (apply_nonneg (schwartzSeminormFamily ℂ ℝ ℂ a)
          (normalizedHermiteSchwartz n))
        (apply_nonneg (s.sup (schwartzSeminormFamily ℂ ℝ ℂ))
          (normalizedHermiteSchwartz n))

/-- A tempered distribution's values on normalized Hermite functions have
at most polynomial growth. -/
theorem temperedDistribution_hermiteCoefficients_polynomiallyBounded
    (T : TemperedDistribution ℝ ℂ) :
    NatPolynomiallyBounded (fun n => ‖T (normalizedHermiteSchwartz n)‖) := by
  obtain ⟨s, C, hC, hbound⟩ :=
    temperedDistribution_norm_le_finsetSchwartzSeminorm T
  apply NatPolynomiallyBounded.mono
    (NatPolynomiallyBounded.const_mul (C : ℝ) C.coe_nonneg
      (finsetSup_normalizedHermiteSchwartzSeminorm_polynomiallyBounded s))
  intro n
  exact hbound (normalizedHermiteSchwartz n)

/-- A complex sequence of polynomial growth is the decoded coefficient
sequence of a vector in some negative Hermite scale. -/
theorem exists_negativeHermiteScale_of_polynomiallyBounded
    (a : ℕ → ℂ) (ha : NatPolynomiallyBounded (fun n => ‖a n‖)) :
    ∃ m : ℕ, ∃ u : HermiteScale (-(m : ℤ)),
      rawHermiteCoefficients (-(m : ℤ)) u = a := by
  obtain ⟨C, hC, d, hd⟩ := ha
  let m : ℕ := d + 1
  have hsBase : Summable (fun n : ℕ =>
      1 / |(n : ℝ) + 1| ^ (2 : ℝ)) :=
    (Real.summable_one_div_nat_add_rpow 1 2).2 (by norm_num)
  have hs : Summable (fun n : ℕ => C ^ 2 / ((n : ℝ) + 1) ^ 2) := by
    apply (hsBase.mul_left (C ^ 2)).congr
    intro n
    rw [abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1), Real.rpow_two]
    ring
  have hmem : Memℓp (normalizeHermiteCoefficients (-(m : ℤ)) a) 2 := by
    rw [mem_rawHermiteScale_iff]
    apply Summable.of_nonneg_of_le
      (fun n => mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (fun n => ?_) hs
    have hx : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hsq : ‖a n‖ ^ 2 ≤
        (C * ((n : ℝ) + 1) ^ d) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hd n) 2
    rw [hermiteScaleWeight, zpow_neg, zpow_natCast]
    calc
      (((n : ℝ) + 1) ^ m)⁻¹ ^ 2 * ‖a n‖ ^ 2 ≤
          (((n : ℝ) + 1) ^ m)⁻¹ ^ 2 *
            (C * ((n : ℝ) + 1) ^ d) ^ 2 := by
        gcongr
      _ = C ^ 2 / ((n : ℝ) + 1) ^ 2 := by
        dsimp only [m]
        simp only [pow_succ]
        field_simp
  let raw : RawHermiteScale (-(m : ℤ)) := ⟨a, hmem⟩
  exact ⟨m, normalizedRawHermite (-(m : ℤ)) raw,
    raw_normalizedRawHermite (-(m : ℤ)) raw⟩

/-- Every tempered distribution determines a coefficient vector in some
negative Hermite scale.  The remaining exhaustion step is to identify its
realization with the original distribution. -/
theorem exists_hermiteScale_coefficients (T : TemperedDistribution ℝ ℂ) :
    ∃ m : ℕ, ∃ u : HermiteScale (-(m : ℤ)),
      rawHermiteCoefficients (-(m : ℤ)) u =
        fun n => T (normalizedHermiteSchwartz n) := by
  exact exists_negativeHermiteScale_of_polynomiallyBounded _
    (temperedDistribution_hermiteCoefficients_polynomiallyBounded T)

/-- Rapid decrease of the Hermite coefficients of a Schwartz function
absorbs every polynomially bounded nonnegative factor. -/
theorem summable_norm_schwartzHermiteCoefficients_mul_of_polynomiallyBounded
    (f : SchwartzMap ℝ ℂ) (a : ℕ → ℝ) (ha0 : ∀ n, 0 ≤ a n)
    (ha : NatPolynomiallyBounded a) :
    Summable (fun n => ‖schwartzHermiteCoefficients f n‖ * a n) := by
  obtain ⟨C, hC, d, hd⟩ := ha
  let r : ℕ := d + 2
  let U : ℝ := ‖schwartzToHermiteScale r f‖
  have hsBase : Summable (fun n : ℕ =>
      1 / |(n : ℝ) + 1| ^ (2 : ℝ)) :=
    (Real.summable_one_div_nat_add_rpow 1 2).2 (by norm_num)
  have hs : Summable (fun n : ℕ => (C * U) / ((n : ℝ) + 1) ^ 2) := by
    apply (hsBase.mul_left (C * U)).congr
    intro n
    rw [abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1), Real.rpow_two]
    ring
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (norm_nonneg _) (ha0 n)) (fun n => ?_) hs
  have hx : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hu := lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0)
    (schwartzToHermiteScale r f) n
  rw [schwartzToHermiteScale_apply, normalizeHermiteCoefficients,
    hermiteScaleWeight, zpow_natCast, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (pow_pos hx r)] at hu
  have hc : ‖schwartzHermiteCoefficients f n‖ ≤
      U / ((n : ℝ) + 1) ^ r := by
    apply (le_div_iff₀ (pow_pos hx r)).2
    simpa only [mul_comm, U] using hu
  calc
    ‖schwartzHermiteCoefficients f n‖ * a n ≤
        ‖schwartzHermiteCoefficients f n‖ *
          (C * ((n : ℝ) + 1) ^ d) :=
      mul_le_mul_of_nonneg_left (hd n) (norm_nonneg _)
    _ ≤ (U / ((n : ℝ) + 1) ^ r) *
          (C * ((n : ℝ) + 1) ^ d) :=
      mul_le_mul_of_nonneg_right hc (mul_nonneg hC (by positivity))
    _ = (C * U) / ((n : ℝ) + 1) ^ 2 := by
      dsimp only [r]
      simp only [pow_succ]
      field_simp

/-- One Schwartz-valued term of the Hermite expansion. -/
def hermiteSchwartzTerm (f : SchwartzMap ℝ ℂ) (n : ℕ) : SchwartzMap ℝ ℂ :=
  schwartzHermiteCoefficients f n • normalizedHermiteSchwartz n

/-- Every fixed Schwartz seminorm of the Hermite expansion terms is
summable. -/
theorem summable_seminorm_hermiteSchwartzTerm
    (f : SchwartzMap ℝ ℂ) (k l : ℕ) :
    Summable (fun n => SchwartzMap.seminorm ℂ k l (hermiteSchwartzTerm f n)) := by
  simp only [hermiteSchwartzTerm, map_smul_eq_mul]
  exact summable_norm_schwartzHermiteCoefficients_mul_of_polynomiallyBounded f _
    (fun n => apply_nonneg _ _)
    (normalizedHermiteSchwartzSeminorm_polynomiallyBounded k l)

private theorem hermiteSchwartzTerm_iteratedFDeriv_bound
    (f : SchwartzMap ℝ ℂ) (l n : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ l (⇑(hermiteSchwartzTerm f n)) x‖ ≤
      SchwartzMap.seminorm ℂ 0 l (hermiteSchwartzTerm f n) := by
  exact SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ _ _ _

/-- Hermite reconstruction remains valid after any number of derivatives.
It follows from the summable uniform derivative bounds, not from a
pointwise exchange of limits and differentiation. -/
theorem hermite_reconstruction_iteratedDeriv
    (f : SchwartzMap ℝ ℂ) (l : ℕ) (x : ℝ) :
    iteratedDeriv l (⇑f) x =
      ∑' n : ℕ, iteratedDeriv l (⇑(hermiteSchwartzTerm f n)) x := by
  have hsumfun : (fun y : ℝ => ∑' n : ℕ, hermiteSchwartzTerm f n y) = ⇑f := by
    funext y
    simpa only [hermiteSchwartzTerm, smul_apply, smul_eq_mul] using
      hermite_reconstruction f y
  have hderiv : iteratedFDeriv ℝ l (⇑f) =
      fun y => ∑' n : ℕ, iteratedFDeriv ℝ l (⇑(hermiteSchwartzTerm f n)) y := by
    rw [← hsumfun]
    exact iteratedFDeriv_tsum (N := ⊤)
      (fun n => (hermiteSchwartzTerm f n).smooth ⊤)
      (fun k _ => summable_seminorm_hermiteSchwartzTerm f 0 k)
      (fun k n y _ => hermiteSchwartzTerm_iteratedFDeriv_bound f k n y) (by simp)
  have hs : Summable (fun n : ℕ =>
      iteratedFDeriv ℝ l (⇑(hermiteSchwartzTerm f n)) x) := by
    exact Summable.of_norm_bounded (summable_seminorm_hermiteSchwartzTerm f 0 l)
      (fun n => hermiteSchwartzTerm_iteratedFDeriv_bound f l n x)
  rw [iteratedDeriv_eq_iteratedFDeriv, hderiv,
    ContinuousMultilinearMap.tsum_eval hs]
  apply tsum_congr
  intro n
  exact (iteratedDeriv_eq_iteratedFDeriv).symm

/-- The first `N` terms of the Hermite expansion, as a Schwartz function. -/
def hermiteSchwartzPartialSum (f : SchwartzMap ℝ ℂ) (N : ℕ) : SchwartzMap ℝ ℂ :=
  ∑ n ∈ Finset.range N, hermiteSchwartzTerm f n

private theorem hermiteSchwartzPartialSum_iteratedDeriv
    (f : SchwartzMap ℝ ℂ) (N l : ℕ) (x : ℝ) :
    iteratedDeriv l (⇑(hermiteSchwartzPartialSum f N)) x =
      ∑ n ∈ Finset.range N, iteratedDeriv l (⇑(hermiteSchwartzTerm f n)) x := by
  have hcoe : ⇑(hermiteSchwartzPartialSum f N) =
      fun y : ℝ => ∑ n ∈ Finset.range N, hermiteSchwartzTerm f n y := by
    funext y
    simp only [hermiteSchwartzPartialSum, sum_apply]
  rw [hcoe]
  exact iteratedDeriv_fun_sum
    (fun n _ => (hermiteSchwartzTerm f n).smooth (l : ℕ∞) |>.contDiffAt)

/-- Hermite partial sums converge to a Schwartz function in the full
Schwartz topology, not merely pointwise or in `L²`. -/
theorem hermiteSchwartzPartialSum_tendsto (f : SchwartzMap ℝ ℂ) :
    Filter.Tendsto (hermiteSchwartzPartialSum f) Filter.atTop (nhds f) := by
  apply (WithSeminorms.tendsto_nhds (schwartz_withSeminorms ℂ ℝ ℂ)
    (hermiteSchwartzPartialSum f) f).2
  rintro ⟨k, l⟩ ε hε
  let q : ℕ → ℝ → ℂ := fun n x =>
    (x : ℂ) ^ k * iteratedDeriv l (⇑(hermiteSchwartzTerm f n)) x
  have hqbound : ∀ n x, ‖q n x‖ ≤
      SchwartzMap.seminorm ℂ k l (hermiteSchwartzTerm f n) := by
    intro n x
    simpa only [q, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs] using
      SchwartzMap.le_seminorm' ℂ k l (hermiteSchwartzTerm f n) x
  have huniform := tendstoUniformly_tsum_nat
    (summable_seminorm_hermiteSchwartzTerm f k l) hqbound
  have htsum : ∀ x : ℝ, (∑' n : ℕ, q n x) =
      (x : ℂ) ^ k * iteratedDeriv l (⇑f) x := by
    intro x
    dsimp only [q]
    rw [tsum_mul_left, ← hermite_reconstruction_iteratedDeriv]
  have hpartial : ∀ N : ℕ, ∀ x : ℝ,
      (∑ n ∈ Finset.range N, q n x) =
        (x : ℂ) ^ k * iteratedDeriv l (⇑(hermiteSchwartzPartialSum f N)) x := by
    intro N x
    dsimp only [q]
    rw [← Finset.mul_sum, ← hermiteSchwartzPartialSum_iteratedDeriv]
  have hhalf : 0 < ε / 2 := half_pos hε
  filter_upwards [(Metric.tendstoUniformly_iff.mp huniform) (ε / 2) hhalf] with N hN
  change SchwartzMap.seminorm ℂ k l (hermiteSchwartzPartialSum f N - f) < ε
  apply lt_of_le_of_lt
    (SchwartzMap.seminorm_le_bound' ℂ k l
      (hermiteSchwartzPartialSum f N - f) hhalf.le ?_) (half_lt_self hε)
  intro x
  have hx := hN x
  rw [htsum x, hpartial N x, dist_eq_norm, ← mul_sub, norm_mul,
    norm_pow, Complex.norm_real, Real.norm_eq_abs, norm_sub_rev] at hx
  have hdsub : iteratedDeriv l (⇑(hermiteSchwartzPartialSum f N - f)) x =
      iteratedDeriv l (⇑(hermiteSchwartzPartialSum f N)) x -
        iteratedDeriv l (⇑f) x := by
    exact iteratedDeriv_fun_sub
      ((hermiteSchwartzPartialSum f N).smooth (l : ℕ∞) |>.contDiffAt)
      (f.smooth (l : ℕ∞) |>.contDiffAt)
  rw [hdsub]
  exact hx.le

/-- A tempered distribution acts on a Schwartz function by the convergent
bilinear pairing of their Hermite coefficients. -/
theorem temperedDistribution_apply_eq_tsum_hermiteCoefficients
    (T : TemperedDistribution ℝ ℂ) (f : SchwartzMap ℝ ℂ) :
    T f = ∑' n : ℕ,
      T (normalizedHermiteSchwartz n) * schwartzHermiteCoefficients f n := by
  have hnorm := summable_norm_schwartzHermiteCoefficients_mul_of_polynomiallyBounded
    f (fun n => ‖T (normalizedHermiteSchwartz n)‖) (fun n => norm_nonneg _)
    (temperedDistribution_hermiteCoefficients_polynomiallyBounded T)
  have hs : Summable (fun n : ℕ =>
      T (normalizedHermiteSchwartz n) * schwartzHermiteCoefficients f n) := by
    apply Summable.of_norm_bounded hnorm
    intro n
    simp only [norm_mul, mul_comm, le_refl]
  have ht := (T.continuous.tendsto f).comp (hermiteSchwartzPartialSum_tendsto f)
  change Filter.Tendsto (fun N : ℕ => T (hermiteSchwartzPartialSum f N))
    Filter.atTop (nhds (T f)) at ht
  have ht' : Filter.Tendsto (fun N : ℕ =>
      ∑ n ∈ Finset.range N,
        T (normalizedHermiteSchwartz n) * schwartzHermiteCoefficients f n)
      Filter.atTop (nhds (T f)) := by
    simpa only [Function.comp_apply, hermiteSchwartzPartialSum,
      hermiteSchwartzTerm, map_sum, map_smul, smul_eq_mul, mul_comm] using ht
  exact tendsto_nhds_unique ht' hs.hasSum.tendsto_sum_nat

/-- Every complex tempered distribution is realized by a vector in one of
the negative integer Hermite scales. -/
theorem exists_hermiteScale_representation (T : TemperedDistribution ℝ ℂ) :
    ∃ m : ℕ, ∃ u : HermiteScale (-(m : ℤ)),
      hermiteScaleDistribution m u = T := by
  obtain ⟨m, u, hu⟩ := exists_hermiteScale_coefficients T
  refine ⟨m, u, ?_⟩
  ext f
  rw [hermiteScaleDistribution_apply_raw, hu]
  exact (temperedDistribution_apply_eq_tsum_hermiteCoefficients T f).symm

end

end MeyerGeneralProblem
