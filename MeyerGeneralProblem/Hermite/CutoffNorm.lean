module

public import MeyerGeneralProblem.Hermite.Exhaustion
public import MeyerGeneralProblem.Distribution.CompactSchwartzDensity

@[expose] public section

/-!
# Uniform compact-cutoff bounds in fixed Hermite norms

The weight `(n+1)^m` is the graph norm of the `m`th power of the shifted
harmonic oscillator. Its product commutator and the Hermite derivative
ladder prove that a family of Schwartz multipliers with every derivative
uniformly bounded acts uniformly boundedly on each fixed Hermite scale.
In particular this applies to the expanding compact cutoffs, without
increasing the Hermite order. No mixed-derivative norm equivalence is
assumed; in that alternative formulation the required total order is `2*m`.
-/

open MeasureTheory
namespace MeyerGeneralProblem
noncomputable section

/-- The shifted Fourier-normalized harmonic oscillator, with eigenvalues `n+1`. -/
def hermiteGraphOperator : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
  ((4 * (Real.pi : ℂ))⁻¹) •
    (-(SchwartzMap.derivCLM ℂ ℂ).comp (SchwartzMap.derivCLM ℂ ℂ) +
      (4 * (Real.pi : ℂ)^2) •
        coordinateMultiplicationCLM.comp coordinateMultiplicationCLM) +
    (1/2 : ℂ) • ContinuousLinearMap.id ℂ _

/-- The graph operator multiplies the `n`th Hermite coefficient by `n+1`. -/
theorem hermiteGraphOperator_coeff (f : SchwartzMap ℝ ℂ) (n : ℕ) :
    schwartzHermiteCoefficients (hermiteGraphOperator f) n =
      ((n : ℂ) + 1) * schwartzHermiteCoefficients f n := by
  have h := schwartzToHermiteScale_apply 1 f n
  change schwartzHermiteCoefficients (hermiteGraphOperator f) n = _ at h
  simpa [normalizeHermiteCoefficients, hermiteScaleWeight] using h

/-- One graph-operator application is exactly one additional Hermite weight. -/
theorem schwartzToHermiteScale_graph (m : ℕ) (f : SchwartzMap ℝ ℂ) :
    schwartzToHermiteScale m (hermiteGraphOperator f) =
      schwartzToHermiteScale (m+1) f := by
  apply lp.ext
  funext n
  rw [schwartzToHermiteScale_apply, schwartzToHermiteScale_apply]
  simp only [normalizeHermiteCoefficients, hermiteScaleWeight,
    zpow_natCast, hermiteGraphOperator_coeff, Complex.ofReal_pow,
    Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one, pow_succ]
  push_cast
  ring

/-- Increasing the nonnegative Hermite order increases the norm. -/
theorem schwartzToHermiteScale_norm_mono (m : ℕ) (f : SchwartzMap ℝ ℂ) :
    ‖schwartzToHermiteScale m f‖ ≤ ‖schwartzToHermiteScale (m+1) f‖ := by
  apply lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0)
  intro n
  rw [schwartzToHermiteScale_apply, schwartzToHermiteScale_apply]
  simp only [normalizeHermiteCoefficients, hermiteScaleWeight, zpow_natCast,
    norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h : (1 : ℝ) ≤ (n : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg n)
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ h (Nat.le_succ m)) (norm_nonneg _)

/-- The order-zero Hermite norm is exactly the ordinary `L²` norm. -/
theorem norm_schwartzToHermiteScale_zero (f : SchwartzMap ℝ ℂ) :
    ‖schwartzToHermiteScale 0 f‖ = ‖f.toLp 2 volume‖ := by
  change ‖(TauCeti.twoPiHermiteHilbertBasis ℂ).repr (f.toLp 2 volume)‖ = _
  exact (TauCeti.twoPiHermiteHilbertBasis ℂ).repr.norm_map _

/-- A uniformly bounded multiplier acts boundedly in the order-zero norm. -/
theorem norm_schwartzToHermiteScale_zero_mul (g f : SchwartzMap ℝ ℂ)
    (C : ℝ) (hC : ∀ x, ‖g x‖ ≤ C) :
    ‖schwartzToHermiteScale 0 (SchwartzMap.smulLeftCLM ℂ g f)‖ ≤
      C * ‖schwartzToHermiteScale 0 f‖ := by
  rw [norm_schwartzToHermiteScale_zero, norm_schwartzToHermiteScale_zero]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [(SchwartzMap.smulLeftCLM ℂ g f).coeFn_toLp 2 volume,
    f.coeFn_toLp 2 volume] with x hx hfx
  rw [hx, hfx, SchwartzMap.smulLeftCLM_apply_apply g.hasTemperateGrowth,
    norm_smul]
  exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _)

/-- Integration by parts transfers the derivative ladder to Schwartz coefficients. -/
theorem schwartzHermiteCoefficients_deriv (f : SchwartzMap ℝ ℂ) (n : ℕ) :
    schwartzHermiteCoefficients (SchwartzMap.derivCLM ℂ ℂ f) n =
      hermiteDerivativeUp n * schwartzHermiteCoefficients f (n+1) -
      hermiteDerivativeDown n * schwartzHermiteCoefficients f (n-1) := by
  have hI (u v : SchwartzMap ℝ ℂ) : Integrable (fun x => u x * v x) volume :=
    (SchwartzMap.pairing (ContinuousLinearMap.mul ℝ ℂ) u v).integrable
  rw [schwartzHermiteCoefficients_apply_integral]
  simp only [SchwartzMap.derivCLM_apply]
  rw [SchwartzMap.integral_mul_deriv_eq_neg_deriv_mul]
  have hd : deriv (normalizedHermiteSchwartz n) =
      fun x => hermiteDerivativeDown n * normalizedHermiteSchwartz (n-1) x -
        hermiteDerivativeUp n * normalizedHermiteSchwartz (n+1) x := by
    funext x
    rw [← SchwartzMap.derivCLM_apply ℂ, deriv_normalizedHermiteSchwartz]
    rfl
  rw [hd]
  simp_rw [sub_mul, mul_assoc]
  rw [integral_sub ((hI _ f).const_mul _) ((hI _ f).const_mul _),
    integral_const_mul, integral_const_mul,
    ← schwartzHermiteCoefficients_apply_integral,
    ← schwartzHermiteCoefficients_apply_integral]
  ring

/-- A finite coordinate square sum is bounded by the full Hilbert norm squared. -/
theorem coeffSpace_sum_sq_le (v : CoefficientSpace ℕ) (s : Finset ℕ) :
    ∑ n ∈ s, ‖v n‖^2 ≤ ‖v‖^2 := by
  simpa using lp.sum_rpow_le_norm_rpow (by norm_num : 0 < (2 : ENNReal).toReal) v s

/-- The forward coordinate shift does not increase finite square sums. -/
theorem coeffSpace_sum_succ_sq_le (v : CoefficientSpace ℕ) (s : Finset ℕ) :
    ∑ n ∈ s, ‖v (n+1)‖^2 ≤ ‖v‖^2 := by
  have h := coeffSpace_sum_sq_le v (s.image (fun n => n+1))
  rw [Finset.sum_image] at h
  · exact h
  · intro a ha b hb hab
    dsimp at hab
    omega

/-- The truncated predecessor shift repeats only the zeroth coordinate. -/
theorem coeffSpace_sum_pred_sq_le (v : CoefficientSpace ℕ) (s : Finset ℕ) :
    ∑ n ∈ s, ‖v (n-1)‖^2 ≤ 2 * ‖v‖^2 := by
  classical
  have he : ∑ n ∈ s.erase 0, ‖v (n-1)‖^2 ≤ ‖v‖^2 := by
    have h := coeffSpace_sum_sq_le v ((s.erase 0).image (fun n => n-1))
    rw [Finset.sum_image] at h
    · exact h
    · intro a ha b hb hab
      dsimp at hab
      have ha' := (Finset.mem_erase.mp ha).1
      have hb' := (Finset.mem_erase.mp hb).1
      omega
  have hzero := coeffSpace_sum_sq_le v {0}
  simp only [Finset.sum_singleton] at hzero
  by_cases hs : 0 ∈ s
  · have hsum := Finset.sum_erase_add (s := s) (a := 0)
      (f := fun n => ‖v (n-1)‖^2) hs
    simp only [Nat.zero_sub] at hsum
    linarith
  · rw [Finset.erase_eq_of_notMem hs] at he
    nlinarith [sq_nonneg ‖v‖]

/-- An adjacent-coordinate envelope controls the full coefficient-space norm. -/
theorem coeffSpace_norm_le_of_adjacent_bound (u v : CoefficientSpace ℕ)
    (K : ℝ) (hK : 0 ≤ K)
    (h : ∀ n, ‖u n‖ ≤ K * (‖v (n+1)‖ + ‖v (n-1)‖)) :
    ‖u‖ ≤ 3 * K * ‖v‖ := by
  apply lp.norm_le_of_forall_sum_le (by norm_num : 0 < (2 : ENNReal).toReal)
    (by positivity)
  intro s
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  calc
    ∑ n ∈ s, ‖u n‖^2 ≤
        ∑ n ∈ s, 2*K^2*(‖v (n+1)‖^2 + ‖v (n-1)‖^2) := by
      apply Finset.sum_le_sum
      intro n hn
      have hsq := sq_le_sq₀ (norm_nonneg (u n)) (by positivity) |>.mpr (h n)
      have hdiff := sq_nonneg (‖v (n+1)‖ - ‖v (n-1)‖)
      nlinarith [mul_nonneg (sq_nonneg K) hdiff]
    _ = 2*K^2*((∑ n ∈ s, ‖v (n+1)‖^2) + ∑ n ∈ s, ‖v (n-1)‖^2) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ 2*K^2*(‖v‖^2 + 2*‖v‖^2) := by
      exact mul_le_mul_of_nonneg_left
        (add_le_add (coeffSpace_sum_succ_sq_le v s)
          (coeffSpace_sum_pred_sq_le v s)) (by positivity)
    _ ≤ (3*K*‖v‖)^2 := by nlinarith [mul_nonneg (sq_nonneg K) (sq_nonneg ‖v‖)]

/-- The norm of each normalized Hermite coordinate is its real weight times the coefficient norm. -/
theorem norm_schwartzToHermiteScale_apply (m : ℕ) (f : SchwartzMap ℝ ℂ) (n : ℕ) :
    ‖schwartzToHermiteScale m f n‖ =
      ((n : ℝ)+1)^m * ‖schwartzHermiteCoefficients f n‖ := by
  rw [schwartzToHermiteScale_apply]
  simp only [normalizeHermiteCoefficients, hermiteScaleWeight, zpow_natCast,
    norm_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity)]

/-- The raising derivative ladder loses at most one Hermite order. -/
theorem hermiteDerivativeUp_weight_bound (m n : ℕ) :
    ((n : ℝ)+1)^m * ‖hermiteDerivativeUp n‖ ≤
      (Real.sqrt (2*Real.pi) * 2^m) * (((n+1 : ℕ) : ℝ)+1)^(m+1) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hs : Real.sqrt (((n : ℝ)+1)/2) ≤ (n : ℝ)+2 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith [sq_nonneg (n : ℝ)]
  have hp : ((n : ℝ)+1)^m ≤ ((n : ℝ)+2)^m := by gcongr; norm_num
  have ht : (1 : ℝ) ≤ 2^m := one_le_pow₀ (by norm_num)
  simp only [hermiteDerivativeUp, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity)]
  push_cast
  calc
    ((n : ℝ)+1)^m * (Real.sqrt (2*Real.pi) * Real.sqrt (((n : ℝ)+1)/2))
      ≤ ((n : ℝ)+2)^m * (Real.sqrt (2*Real.pi) * ((n : ℝ)+2)) := by gcongr
    _ ≤ (Real.sqrt (2*Real.pi) * 2^m) * (((n : ℝ)+1)+1)^(m+1) := by
      rw [show ((n : ℝ)+1)+1 = (n : ℝ)+2 by ring, pow_succ]
      nlinarith [mul_nonneg (sub_nonneg.mpr ht)
        (mul_nonneg (Real.sqrt_nonneg (2*Real.pi))
          (mul_nonneg (pow_nonneg (by positivity : 0 ≤ (n : ℝ)+2) m) (by positivity : 0 ≤ (n : ℝ)+2)))]

/-- The lowering derivative ladder loses at most one Hermite order. -/
theorem hermiteDerivativeDown_weight_bound (m n : ℕ) :
    ((n : ℝ)+1)^m * ‖hermiteDerivativeDown n‖ ≤
      (Real.sqrt (2*Real.pi) * 2^m) * (((n-1 : ℕ) : ℝ)+1)^(m+1) := by
  cases n with
  | zero => simp [hermiteDerivativeDown]
  | succ n =>
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hs : Real.sqrt (((n : ℝ)+1)/2) ≤ (n : ℝ)+1 := by
      apply Real.sqrt_le_iff.mpr
      constructor
      · positivity
      · nlinarith [sq_nonneg (n : ℝ)]
    have hp : ((n : ℝ)+2)^m ≤ (2*((n : ℝ)+1))^m := by gcongr; linarith
    simp only [hermiteDerivativeDown, Complex.norm_real, Real.norm_eq_abs,
      Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    rw [abs_of_nonneg (by positivity)]
    calc
      (((n : ℝ)+1)+1)^m * (Real.sqrt (2*Real.pi) * Real.sqrt (((n : ℝ)+1)/2))
        ≤ (2*((n : ℝ)+1))^m * (Real.sqrt (2*Real.pi) * ((n : ℝ)+1)) := by
          rw [show ((n : ℝ)+1)+1 = (n : ℝ)+2 by ring]
          gcongr
      _ = _ := by rw [mul_pow, pow_succ]; ring

/-- A spatial derivative maps order `m+1` to order `m`, with an explicit bound. -/
theorem schwartzToHermiteScale_derivative_norm_bound (m : ℕ) (f : SchwartzMap ℝ ℂ) :
    ‖schwartzToHermiteScale m (SchwartzMap.derivCLM ℂ ℂ f)‖ ≤
      (3 * (Real.sqrt (2*Real.pi) * 2^m)) * ‖schwartzToHermiteScale (m+1) f‖ := by
  apply coeffSpace_norm_le_of_adjacent_bound _ _ _ (by positivity)
  intro n
  rw [norm_schwartzToHermiteScale_apply, schwartzHermiteCoefficients_deriv]
  calc
    ((n : ℝ)+1)^m *
        ‖hermiteDerivativeUp n * schwartzHermiteCoefficients f (n+1) -
          hermiteDerivativeDown n * schwartzHermiteCoefficients f (n-1)‖
      ≤ ((n : ℝ)+1)^m *
        (‖hermiteDerivativeUp n‖ * ‖schwartzHermiteCoefficients f (n+1)‖ +
          ‖hermiteDerivativeDown n‖ * ‖schwartzHermiteCoefficients f (n-1)‖) := by
          gcongr
          simpa only [norm_mul] using norm_sub_le
            (hermiteDerivativeUp n * schwartzHermiteCoefficients f (n+1))
            (hermiteDerivativeDown n * schwartzHermiteCoefficients f (n-1))
    _ ≤ (Real.sqrt (2*Real.pi) * 2^m) *
        (‖schwartzToHermiteScale (m+1) f (n+1)‖ +
          ‖schwartzToHermiteScale (m+1) f (n-1)‖) := by
      rw [norm_schwartzToHermiteScale_apply, norm_schwartzToHermiteScale_apply]
      rw [mul_add, mul_add, ← mul_assoc, ← mul_assoc]
      apply add_le_add
      · simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
          (hermiteDerivativeUp_weight_bound m n)
          (norm_nonneg (schwartzHermiteCoefficients f (n+1)))
      · simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
          (hermiteDerivativeDown_weight_bound m n)
          (norm_nonneg (schwartzHermiteCoefficients f (n-1)))

/-- The ordinary product rule bundled in Schwartz space. -/
theorem schwartzDerivative_mul (g f : SchwartzMap ℝ ℂ) :
    SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.smulLeftCLM ℂ g f) =
      SchwartzMap.smulLeftCLM ℂ (SchwartzMap.derivCLM ℂ ℂ g) f +
        SchwartzMap.smulLeftCLM ℂ g (SchwartzMap.derivCLM ℂ ℂ f) := by
  ext x
  rw [SchwartzMap.derivCLM_apply]
  have hg : ⇑(SchwartzMap.smulLeftCLM ℂ g f) = fun y => g y * f y := by
    funext y
    rw [SchwartzMap.smulLeftCLM_apply_apply g.hasTemperateGrowth]
    rfl
  rw [hg]
  change deriv (⇑g * ⇑f) x = _
  rw [deriv_mul g.differentiableAt f.differentiableAt]
  simp only [add_apply, SchwartzMap.smulLeftCLM_apply_apply g.hasTemperateGrowth,
    SchwartzMap.smulLeftCLM_apply_apply (SchwartzMap.derivCLM ℂ ℂ g).hasTemperateGrowth,
    SchwartzMap.derivCLM_apply, smul_eq_mul]

/-- The oscillator product commutator involves only the first two multiplier derivatives. -/
theorem hermiteGraphOperator_mul (g f : SchwartzMap ℝ ℂ) :
    hermiteGraphOperator (SchwartzMap.smulLeftCLM ℂ g f) =
      SchwartzMap.smulLeftCLM ℂ g (hermiteGraphOperator f) -
        ((2*(Real.pi : ℂ))⁻¹) •
          SchwartzMap.smulLeftCLM ℂ (SchwartzMap.derivCLM ℂ ℂ g)
            (SchwartzMap.derivCLM ℂ ℂ f) -
        ((4*(Real.pi : ℂ))⁻¹) •
          SchwartzMap.smulLeftCLM ℂ (SchwartzMap.derivCLM ℂ ℂ
            (SchwartzMap.derivCLM ℂ ℂ g)) f := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  ext x
  simp only [hermiteGraphOperator, add_apply,
    smul_apply, neg_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
  rw [schwartzDerivative_mul, map_add, schwartzDerivative_mul, schwartzDerivative_mul]
  simp only [add_apply, sub_apply, neg_apply, smul_apply, smul_eq_mul,
    coordinateMultiplicationCLM_apply,
    SchwartzMap.smulLeftCLM_apply_apply g.hasTemperateGrowth,
    SchwartzMap.smulLeftCLM_apply_apply (SchwartzMap.derivCLM ℂ ℂ g).hasTemperateGrowth,
    SchwartzMap.smulLeftCLM_apply_apply
      (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ g)).hasTemperateGrowth]
  field_simp
  ring

/-- Every derivative of the multiplier family has a radius-independent supremum bound. -/
def SchwartzMultiplierFamilyBounded (g : ℕ → SchwartzMap ℝ ℂ) : Prop :=
  ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ N x,
    ‖((SchwartzMap.derivCLM ℂ ℂ : SchwartzMap ℝ ℂ → SchwartzMap ℝ ℂ)^[k]) (g N) x‖ ≤ C

/-- Uniform derivative bounds are stable under differentiating the family. -/
theorem SchwartzMultiplierFamilyBounded.deriv {g : ℕ → SchwartzMap ℝ ℂ}
    (hg : SchwartzMultiplierFamilyBounded g) :
    SchwartzMultiplierFamilyBounded (fun N => SchwartzMap.derivCLM ℂ ℂ (g N)) := by
  intro k
  obtain ⟨C, hC, hc⟩ := hg (k+1)
  exact ⟨C, hC, fun N x => by simpa only [Function.iterate_succ_apply] using hc N x⟩

/-- Uniform derivative-bounded multiplier families act uniformly on every fixed Hermite scale. -/
theorem schwartzMultiplierFamily_hermiteNormBound (m : ℕ)
    (g : ℕ → SchwartzMap ℝ ℂ) (hg : SchwartzMultiplierFamilyBounded g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N f,
      ‖schwartzToHermiteScale m (SchwartzMap.smulLeftCLM ℂ (g N) f)‖ ≤
        C * ‖schwartzToHermiteScale m f‖ := by
  induction m generalizing g with
  | zero =>
    obtain ⟨C, hC, hc⟩ := hg 0
    refine ⟨C, hC, fun N f => norm_schwartzToHermiteScale_zero_mul (g N) f C ?_⟩
    intro x
    exact hc N x
  | succ m ih =>
    obtain ⟨A, hA, ha⟩ := ih g hg
    obtain ⟨B, hB, hb⟩ := ih (fun N => SchwartzMap.derivCLM ℂ ℂ (g N)) hg.deriv
    obtain ⟨C, hC, hc⟩ := ih
      (fun N => SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ (g N))) hg.deriv.deriv
    let a : ℝ := ‖((2*(Real.pi : ℂ))⁻¹)‖
    let b : ℝ := ‖((4*(Real.pi : ℂ))⁻¹)‖
    let d : ℝ := 3 * (Real.sqrt (2*Real.pi) * 2^m)
    refine ⟨A+a*B*d+b*C, by dsimp [a,b,d]; positivity, fun N f => ?_⟩
    rw [← schwartzToHermiteScale_graph, hermiteGraphOperator_mul,
      map_sub, map_sub, map_smul, map_smul]
    calc
      _ ≤ ‖schwartzToHermiteScale m (SchwartzMap.smulLeftCLM ℂ (g N) (hermiteGraphOperator f))‖ +
          a * ‖schwartzToHermiteScale m (SchwartzMap.smulLeftCLM ℂ
            (SchwartzMap.derivCLM ℂ ℂ (g N)) (SchwartzMap.derivCLM ℂ ℂ f))‖ +
          b * ‖schwartzToHermiteScale m (SchwartzMap.smulLeftCLM ℂ
            (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ (g N))) f)‖ := by
        refine (norm_sub_le _ _).trans ?_
        rw [norm_smul]
        refine add_le_add ?_ (le_refl _)
        exact (norm_sub_le _ _).trans_eq (by rw [norm_smul])
      _ ≤ A * ‖schwartzToHermiteScale m (hermiteGraphOperator f)‖ +
          a * (B * ‖schwartzToHermiteScale m (SchwartzMap.derivCLM ℂ ℂ f)‖) +
          b * (C * ‖schwartzToHermiteScale m f‖) := by
        gcongr
        · exact ha N _
        · exact hb N _
        · exact hc N _
      _ ≤ A * ‖schwartzToHermiteScale (m+1) f‖ +
          a * (B * (d * ‖schwartzToHermiteScale (m+1) f‖)) +
          b * (C * ‖schwartzToHermiteScale (m+1) f‖) := by
        rw [schwartzToHermiteScale_graph]
        gcongr
        · exact schwartzToHermiteScale_derivative_norm_bound m f
        · exact schwartzToHermiteScale_norm_mono m f
      _ = _ := by ring

/-- Iterating the bundled Schwartz derivative agrees with the ordinary iterated derivative. -/
theorem schwartzDerivative_iterate_apply (k : ℕ) (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    ((SchwartzMap.derivCLM ℂ ℂ : SchwartzMap ℝ ℂ → SchwartzMap ℝ ℂ)^[k]) f x =
      iteratedDeriv k f x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', SchwartzMap.derivCLM_apply, iteratedDeriv_succ]
    have heq : ⇑(((SchwartzMap.derivCLM ℂ ℂ : SchwartzMap ℝ ℂ → SchwartzMap ℝ ℂ)^[k]) f) =
        iteratedDeriv k f := by
      funext y
      exact ih y
    rw [heq]

/-- All derivatives of the expanding compact cutoffs are uniformly bounded. -/
theorem scaledCompactSchwartzCutoff_familyBounded :
    SchwartzMultiplierFamilyBounded scaledCompactSchwartzCutoff := by
  intro k
  refine ⟨SchwartzMap.seminorm ℂ 0 k compactSchwartzCutoff,
    apply_nonneg _ _, fun N x => ?_⟩
  rw [schwartzDerivative_iterate_apply]
  refine (norm_iteratedDeriv_scaledCompactSchwartzCutoff_le N k x).trans ?_
  exact mul_le_of_le_one_left (apply_nonneg _ _)
    (pow_le_one₀ (compactSchwartzCutoffScale_pos N).le (compactSchwartzCutoffScale_le_one N))

/-- Compact-cutoff multiplication is uniformly bounded in the same Hermite order. -/
theorem compactSchwartzApproximation_uniform_hermiteNormBound (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N f,
      ‖schwartzToHermiteScale m (compactSchwartzApproximation N f)‖ ≤
        C * ‖schwartzToHermiteScale m f‖ :=
  schwartzMultiplierFamily_hermiteNormBound m scaledCompactSchwartzCutoff
    scaledCompactSchwartzCutoff_familyBounded

end
end MeyerGeneralProblem
