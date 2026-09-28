module

public import MeyerGeneralProblem.Hermite.CutoffNorm
public import MeyerGeneralProblem.Distribution.CombScaling

@[expose] public section

/-!
# Original Hermite norm bounds for adaptive operators

The estimates use the actual coefficient norm and shifted oscillator of
`Hermite.CutoffNorm`. In particular, two ordinary derivatives cost only one
Hermite order. This is the sharper ladder estimate needed for compact-range
same-order dilation; composing the older one-derivative bound would lose two
orders.
-/

namespace MeyerGeneralProblem.Adaptive

noncomputable section
open MeasureTheory

private theorem norm_derivativeUp_le (n : ℕ) :
    ‖hermiteDerivativeUp n‖ ≤ Real.sqrt (2 * Real.pi) * Real.sqrt ((n : ℝ) + 1) := by
  simp only [hermiteDerivativeUp, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity)]
  gcongr
  have hn := Nat.cast_nonneg (α := ℝ) n
  linarith

private theorem norm_derivativeDown_le (n : ℕ) :
    ‖hermiteDerivativeDown n‖ ≤ Real.sqrt (2 * Real.pi) * Real.sqrt ((n : ℝ) + 1) := by
  simp only [hermiteDerivativeDown, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity)]
  gcongr
  have hn := Nat.cast_nonneg (α := ℝ) n
  linarith

private theorem ladder_pair_weight_bound (m n k l : ℕ) (c d : ℂ)
    (hn : n ≤ l + 2) (hk : k ≤ l + 1)
    (hc : ‖c‖ ≤ Real.sqrt (2 * Real.pi) * Real.sqrt ((n : ℝ) + 1))
    (hd : ‖d‖ ≤ Real.sqrt (2 * Real.pi) * Real.sqrt ((k : ℝ) + 1)) :
    ((n : ℝ) + 1)^m * (‖c‖ * ‖d‖) ≤
      (6 * Real.pi * 3^m) * ((l : ℝ) + 1)^(m+1) := by
  have hn' : (n : ℝ) + 1 ≤ 3 * ((l : ℝ) + 1) := by
    have hh : (n : ℝ) ≤ (l : ℝ) + 2 := by exact_mod_cast hn
    have hl := Nat.cast_nonneg (α := ℝ) l
    linarith
  have hk' : (k : ℝ) + 1 ≤ 3 * ((l : ℝ) + 1) := by
    have hh : (k : ℝ) ≤ (l : ℝ) + 1 := by exact_mod_cast hk
    have hl := Nat.cast_nonneg (α := ℝ) l
    linarith
  have hc' : ‖c‖ ≤ Real.sqrt (2 * Real.pi) * Real.sqrt (3 * ((l : ℝ) + 1)) := by
    exact hc.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hn') (by positivity))
  have hd' : ‖d‖ ≤ Real.sqrt (2 * Real.pi) * Real.sqrt (3 * ((l : ℝ) + 1)) := by
    exact hd.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hk') (by positivity))
  calc
    ((n : ℝ) + 1)^m * (‖c‖ * ‖d‖) ≤
        (3 * ((l : ℝ) + 1))^m *
          ((Real.sqrt (2 * Real.pi) * Real.sqrt (3 * ((l : ℝ) + 1)))^2) := by
      rw [pow_two]
      exact mul_le_mul (pow_le_pow_left₀ (by positivity) hn' m)
        (mul_le_mul hc' hd' (norm_nonneg _) (by positivity))
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by positivity)
    _ = (6 * Real.pi * 3^m) * ((l : ℝ) + 1)^(m+1) := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 * Real.pi),
        Real.sq_sqrt (by positivity : 0 ≤ 3 * ((l : ℝ) + 1)), pow_succ]
      ring

private theorem coeffSpace_sum_shift_sq_le (v : CoefficientSpace ℕ)
    (s : Finset ℕ) (j : ℕ) : ∑ n ∈ s, ‖v (n+j)‖^2 ≤ ‖v‖^2 := by
  classical
  have h := coeffSpace_sum_sq_le v (s.image (fun n => n+j))
  rw [Finset.sum_image] at h
  · exact h
  · intro a ha b hb hab
    dsimp at hab
    omega

private theorem coeffSpace_sum_sub_sq_le (v : CoefficientSpace ℕ)
    (s : Finset ℕ) (j : ℕ) : ∑ n ∈ s, ‖v (n-j)‖^2 ≤ (j+1) * ‖v‖^2 := by
  classical
  induction j generalizing s with
  | zero => simpa using coeffSpace_sum_sq_le v s
  | succ j ih =>
      have hzero : ‖v 0‖^2 ≤ ‖v‖^2 := by
        simpa using coeffSpace_sum_sq_le v {0}
      have hrest : ∑ n ∈ s.erase 0, ‖v (n-(j+1))‖^2 ≤ (j+1) * ‖v‖^2 := by
        have h := ih ((s.erase 0).image (fun n => n-1))
        rw [Finset.sum_image] at h
        · simpa only [Nat.sub_sub, Nat.add_comm 1 j] using h
        · intro a ha b hb hab
          have ha' := (Finset.mem_erase.mp ha).1
          have hb' := (Finset.mem_erase.mp hb).1
          dsimp at hab
          omega
      by_cases hs : 0 ∈ s
      · have he := Finset.sum_erase_add (s := s) (a := 0)
          (f := fun n => ‖v (n-(j+1))‖^2) hs
        simp only [Nat.zero_sub] at he
        push_cast
        push_cast at hrest
        nlinarith
      · rw [Finset.erase_eq_of_notMem hs] at hrest
        push_cast
        push_cast at hrest
        nlinarith [sq_nonneg ‖v‖]

private theorem coeffSpace_sum_pred_succ_sq_le (v : CoefficientSpace ℕ)
    (s : Finset ℕ) : ∑ n ∈ s, ‖v ((n-1)+1)‖^2 ≤ 2 * ‖v‖^2 := by
  classical
  have hrest : ∑ n ∈ s.erase 0, ‖v ((n-1)+1)‖^2 ≤ ‖v‖^2 := by
    have h := coeffSpace_sum_sq_le v (s.erase 0)
    apply (Finset.sum_congr rfl (fun n hn => ?_)).trans_le h
    have hh := (Finset.mem_erase.mp hn).1
    rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hh)]
  have hfirst : ‖v 1‖^2 ≤ ‖v‖^2 := by simpa using coeffSpace_sum_sq_le v {1}
  by_cases hs : 0 ∈ s
  · have he := Finset.sum_erase_add (s := s) (a := 0)
        (f := fun n => ‖v ((n-1)+1)‖^2) hs
    simp only [Nat.zero_sub, zero_add] at he
    linarith
  · rw [Finset.erase_eq_of_notMem hs] at hrest
    nlinarith [sq_nonneg ‖v‖]

private theorem coeffSpace_norm_le_of_double_adjacent_bound (u v : CoefficientSpace ℕ)
    (K : ℝ) (hK : 0 ≤ K)
    (h : ∀ n, ‖u n‖ ≤ K *
      (‖v (n+2)‖ + ‖v n‖ + ‖v ((n-1)+1)‖ + ‖v (n-2)‖)) :
    ‖u‖ ≤ 6 * K * ‖v‖ := by
  apply lp.norm_le_of_forall_sum_le (by norm_num : 0 < (2 : ENNReal).toReal)
    (by positivity)
  intro s
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  have hpoint (n : ℕ) : ‖u n‖^2 ≤ 4*K^2 *
      (‖v (n+2)‖^2 + ‖v n‖^2 + ‖v ((n-1)+1)‖^2 + ‖v (n-2)‖^2) := by
    have hs := (sq_le_sq₀ (norm_nonneg (u n)) (by positivity)).mpr (h n)
    have hab := sq_nonneg (‖v (n+2)‖ - ‖v n‖)
    have hcd := sq_nonneg (‖v ((n-1)+1)‖ - ‖v (n-2)‖)
    have hp := sq_nonneg ((‖v (n+2)‖ + ‖v n‖) -
      (‖v ((n-1)+1)‖ + ‖v (n-2)‖))
    have hsum : (‖v (n+2)‖ + ‖v n‖ + ‖v ((n-1)+1)‖ + ‖v (n-2)‖)^2 ≤
        4 * (‖v (n+2)‖^2 + ‖v n‖^2 + ‖v ((n-1)+1)‖^2 + ‖v (n-2)‖^2) := by
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hsum (sq_nonneg K)]
  calc
    ∑ n ∈ s, ‖u n‖^2 ≤ ∑ n ∈ s, 4*K^2 *
        (‖v (n+2)‖^2 + ‖v n‖^2 + ‖v ((n-1)+1)‖^2 + ‖v (n-2)‖^2) :=
      Finset.sum_le_sum (fun n hn => hpoint n)
    _ = 4*K^2 * ((∑ n ∈ s, ‖v (n+2)‖^2) + (∑ n ∈ s, ‖v n‖^2) +
        (∑ n ∈ s, ‖v ((n-1)+1)‖^2) + ∑ n ∈ s, ‖v (n-2)‖^2) := by
      rw [← Finset.mul_sum]
      simp only [Finset.sum_add_distrib]
    _ ≤ 4*K^2 * (‖v‖^2 + ‖v‖^2 + 2*‖v‖^2 + 3*‖v‖^2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add (add_le_add (add_le_add
        (coeffSpace_sum_shift_sq_le v s 2) (coeffSpace_sum_sq_le v s))
        (coeffSpace_sum_pred_succ_sq_le v s))
        (by simpa only [Nat.cast_ofNat, show (2:ℝ)+1=3 by norm_num] using coeffSpace_sum_sub_sq_le v s 2)
    _ ≤ (6*K*‖v‖)^2 := by nlinarith [mul_nonneg (sq_nonneg K) (sq_nonneg ‖v‖)]

/-- Two ordinary derivatives lose one original Hermite order, with an explicit constant. -/
theorem schwartzToHermiteScale_secondDerivative_norm_bound (m : ℕ) (f : SchwartzMap ℝ ℂ) :
    ‖schwartzToHermiteScale m (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ f))‖ ≤
      (36 * Real.pi * 3^m) * ‖schwartzToHermiteScale (m+1) f‖ := by
  let K : ℝ := 6 * Real.pi * 3^m
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hb (n k l : ℕ) (c d : ℂ) (hn : n ≤ l+2) (hk : k ≤ l+1)
      (hc : ‖c‖ ≤ Real.sqrt (2*Real.pi)*Real.sqrt ((n:ℝ)+1))
      (hd : ‖d‖ ≤ Real.sqrt (2*Real.pi)*Real.sqrt ((k:ℝ)+1)) :
      ((n:ℝ)+1)^m * (‖c‖*‖d‖*‖schwartzHermiteCoefficients f l‖) ≤
        K * ‖schwartzToHermiteScale (m+1) f l‖ := by
    rw [norm_schwartzToHermiteScale_apply]
    simpa only [K, mul_assoc] using
      (mul_le_mul_of_nonneg_right (ladder_pair_weight_bound m n k l c d hn hk hc hd)
        (norm_nonneg (schwartzHermiteCoefficients f l)))
  have hpoint (n : ℕ) :
      ‖schwartzToHermiteScale m (SchwartzMap.derivCLM ℂ ℂ
        (SchwartzMap.derivCLM ℂ ℂ f)) n‖ ≤ K *
        (‖schwartzToHermiteScale (m+1) f (n+2)‖ + ‖schwartzToHermiteScale (m+1) f n‖ +
          ‖schwartzToHermiteScale (m+1) f ((n-1)+1)‖ +
            ‖schwartzToHermiteScale (m+1) f (n-2)‖) := by
    rw [norm_schwartzToHermiteScale_apply, schwartzHermiteCoefficients_deriv,
      schwartzHermiteCoefficients_deriv, schwartzHermiteCoefficients_deriv]
    have htriangle :
        ‖hermiteDerivativeUp n *
          (hermiteDerivativeUp (n+1)*schwartzHermiteCoefficients f ((n+1)+1) -
            hermiteDerivativeDown (n+1)*schwartzHermiteCoefficients f ((n+1)-1)) -
          hermiteDerivativeDown n *
          (hermiteDerivativeUp (n-1)*schwartzHermiteCoefficients f ((n-1)+1) -
            hermiteDerivativeDown (n-1)*schwartzHermiteCoefficients f ((n-1)-1))‖ ≤
        ‖hermiteDerivativeUp n‖ *
          (‖hermiteDerivativeUp (n+1)‖*‖schwartzHermiteCoefficients f (n+2)‖ +
            ‖hermiteDerivativeDown (n+1)‖*‖schwartzHermiteCoefficients f n‖) +
          ‖hermiteDerivativeDown n‖ *
          (‖hermiteDerivativeUp (n-1)‖*‖schwartzHermiteCoefficients f ((n-1)+1)‖ +
            ‖hermiteDerivativeDown (n-1)‖*‖schwartzHermiteCoefficients f (n-2)‖) := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul, norm_mul]
      apply add_le_add
      · apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        simpa only [norm_mul, Nat.add_sub_cancel, Nat.add_assoc] using norm_sub_le
          (hermiteDerivativeUp (n+1)*schwartzHermiteCoefficients f ((n+1)+1))
          (hermiteDerivativeDown (n+1)*schwartzHermiteCoefficients f ((n+1)-1))
      · apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        simpa only [norm_mul, Nat.sub_sub] using norm_sub_le
          (hermiteDerivativeUp (n-1)*schwartzHermiteCoefficients f ((n-1)+1))
          (hermiteDerivativeDown (n-1)*schwartzHermiteCoefficients f ((n-1)-1))
    have hh := mul_le_mul_of_nonneg_left htriangle (pow_nonneg (by positivity : 0 ≤ (n:ℝ)+1) m)
    have h1 := hb n (n+1) (n+2) (hermiteDerivativeUp n) (hermiteDerivativeUp (n+1))
      (by omega) (by omega) (norm_derivativeUp_le n) (norm_derivativeUp_le (n+1))
    have h2 := hb n (n+1) n (hermiteDerivativeUp n) (hermiteDerivativeDown (n+1))
      (by omega) (by omega) (norm_derivativeUp_le n) (norm_derivativeDown_le (n+1))
    have h3 := hb n (n-1) ((n-1)+1) (hermiteDerivativeDown n) (hermiteDerivativeUp (n-1))
      (by omega) (by omega) (norm_derivativeDown_le n) (norm_derivativeUp_le (n-1))
    have h4 := hb n (n-1) (n-2) (hermiteDerivativeDown n) (hermiteDerivativeDown (n-1))
      (by omega) (by omega) (norm_derivativeDown_le n) (norm_derivativeDown_le (n-1))
    nlinarith
  have h := coeffSpace_norm_le_of_double_adjacent_bound
    (schwartzToHermiteScale m (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ f)))
    (schwartzToHermiteScale (m+1) f) K hK hpoint
  convert h using 1
  dsimp [K]
  ring


/-- The actual chain rule for the Schwartz dilation pullback. -/
theorem derivative_combSchwartzDilation (a : ℝ) (ha : a ≠ 0) (f : SchwartzMap ℝ ℂ) :
    SchwartzMap.derivCLM ℂ ℂ (combSchwartzDilation a ha f) =
      (a : ℂ) • combSchwartzDilation a ha (SchwartzMap.derivCLM ℂ ℂ f) := by
  ext x
  have he : (combSchwartzDilation a ha f : ℝ → ℂ) = fun y => f (a*y) :=
    funext (combSchwartzDilation_apply a ha f)
  rw [SchwartzMap.derivCLM_apply, he]
  have h := (f.hasDerivAt (a*x)).scomp x ((hasDerivAt_id x).const_mul a)
  simpa only [smul_apply, combSchwartzDilation_apply, SchwartzMap.derivCLM_apply,
    mul_one, Complex.real_smul, smul_eq_mul, Function.comp_def] using h.deriv

/-- Two chain-rule factors for the actual second derivative. -/
theorem secondDerivative_combSchwartzDilation (a : ℝ) (ha : a ≠ 0)
    (f : SchwartzMap ℝ ℂ) :
    SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ (combSchwartzDilation a ha f)) =
      (a : ℂ)^2 • combSchwartzDilation a ha
        (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ f)) := by
  rw [derivative_combSchwartzDilation, map_smul, derivative_combSchwartzDilation,
    smul_smul, pow_two]

/-- Multiplication by position transforms with the reciprocal scale. -/
theorem position_combSchwartzDilation (a : ℝ) (ha : a ≠ 0) (f : SchwartzMap ℝ ℂ) :
    coordinateMultiplicationCLM (combSchwartzDilation a ha f) =
      (a : ℂ)⁻¹ • combSchwartzDilation a ha (coordinateMultiplicationCLM f) := by
  ext x
  simp only [coordinateMultiplicationCLM_apply, smul_apply, combSchwartzDilation_apply,
    smul_eq_mul, Complex.ofReal_mul]
  field_simp [Complex.ofReal_ne_zero.mpr ha]

/-- Conjugating the original oscillator keeps the original second derivative
and the original Hermite norm; no equivalent-norm premise is introduced. -/
theorem graph_combSchwartzDilation (a : ℝ) (ha : a ≠ 0) (f : SchwartzMap ℝ ℂ) :
    hermiteGraphOperator (combSchwartzDilation a ha f) =
      combSchwartzDilation a ha
        ((a : ℂ)⁻¹^2 • hermiteGraphOperator f +
          ((4 * (Real.pi : ℂ))⁻¹ * ((a : ℂ)⁻¹^2 - (a : ℂ)^2)) •
            SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ f) +
          ((1 - (a : ℂ)⁻¹^2)/2) • f) := by
  have hposition : coordinateMultiplicationCLM
      (coordinateMultiplicationCLM (combSchwartzDilation a ha f)) =
      (a : ℂ)⁻¹^2 • combSchwartzDilation a ha
        (coordinateMultiplicationCLM (coordinateMultiplicationCLM f)) := by
    rw [position_combSchwartzDilation, map_smul, position_combSchwartzDilation,
      smul_smul, pow_two]
  simp only [hermiteGraphOperator, add_apply,
    smul_apply, neg_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    secondDerivative_combSchwartzDilation, hposition,
    map_add, map_smul, map_neg]
  ext x
  simp only [smul_apply, add_apply, neg_apply, smul_eq_mul]
  field_simp [Complex.ofReal_ne_zero.mpr ha]
  ring

private theorem schwartz_toLp_norm_sq (f : SchwartzMap ℝ ℂ) :
    ‖f.toLp 2 volume‖^2 = ∫ x : ℝ, ‖f x‖^2 := by
  have he : ‖f.toLp 2 volume‖ = Real.sqrt (∫ x : ℝ, ‖f x‖^2) := by
    rw [SchwartzMap.norm_toLp' (by norm_num : (2:ENNReal) ≠ 0)
      (by norm_num : (2:ENNReal) ≠ ⊤)]
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.sqrt_eq_rpow]
    norm_num
  rw [he, Real.sq_sqrt (integral_nonneg (fun x => sq_nonneg _))]

/-- The original order-zero norm has the exact dilation Jacobian. -/
theorem schwartzToHermiteScale_zero_dilation_norm_sq (a : ℝ) (ha : a ≠ 0)
    (f : SchwartzMap ℝ ℂ) :
    ‖schwartzToHermiteScale 0 (combSchwartzDilation a ha f)‖^2 =
      |a⁻¹| * ‖schwartzToHermiteScale 0 f‖^2 := by
  rw [norm_schwartzToHermiteScale_zero, norm_schwartzToHermiteScale_zero,
    schwartz_toLp_norm_sq, schwartz_toLp_norm_sq]
  simp only [combSchwartzDilation_apply]
  exact Measure.integral_comp_mul_left (fun y : ℝ => ‖f y‖^2) a


private theorem dilation_coefficients_bound (a : ℝ) (ha : a ∈ Set.Icc (1/2:ℝ) 2) :
    ‖(a : ℂ)⁻¹^2‖ ≤ 4 ∧
    ‖(4 * (Real.pi : ℂ))⁻¹ * ((a : ℂ)⁻¹^2 - (a : ℂ)^2)‖ ≤
      8 * ‖(4 * (Real.pi : ℂ))⁻¹‖ ∧
    ‖(1 - (a : ℂ)⁻¹^2)/2‖ ≤ 3 := by
  have hap : 0 < a := by linarith [ha.1]
  have hi : a⁻¹ ≤ 2 := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hap).mpr
    linarith [ha.1]
  have hn : ‖(a : ℂ)‖ ≤ 2 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hap] using ha.2
  have hni : ‖(a : ℂ)⁻¹‖ ≤ 2 := by
    simpa only [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hap] using hi
  have hsq : ‖(a : ℂ)^2‖ ≤ 4 := by
    rw [norm_pow]
    nlinarith [norm_nonneg (a:ℂ)]
  have hisq : ‖(a : ℂ)⁻¹^2‖ ≤ 4 := by
    rw [norm_pow]
    nlinarith [norm_nonneg ((a:ℂ)⁻¹)]
  refine ⟨hisq, ?_, ?_⟩
  · rw [norm_mul]
    have hsub := (norm_sub_le ((a:ℂ)⁻¹^2) ((a:ℂ)^2)).trans (add_le_add hisq hsq)
    nlinarith [mul_le_mul_of_nonneg_left hsub (norm_nonneg ((4*(Real.pi:ℂ))⁻¹))]
  · rw [norm_div]
    norm_num only [Complex.norm_ofNat]
    have hh := norm_sub_le (1:ℂ) ((a:ℂ)⁻¹^2)
    rw [norm_one] at hh
    linarith

/-- Every fixed original positive Hermite norm is uniformly stable under actual
Schwartz dilation for all scales in `[1/2,2]`. The bound precedes the scale and
input function and does not assume an equivalent mixed-derivative norm. -/
theorem exists_uniform_hermite_dilation_bound (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℝ) (ha : a ≠ 0), a ∈ Set.Icc (1/2:ℝ) 2 →
      ∀ f : SchwartzMap ℝ ℂ,
        ‖schwartzToHermiteScale m (combSchwartzDilation a ha f)‖ ≤
          C * ‖schwartzToHermiteScale m f‖ := by
  induction m with
  | zero =>
      refine ⟨2, by norm_num, ?_⟩
      intro a ha hab f
      have hap : 0 < a := by linarith [hab.1]
      have hi : |a⁻¹| ≤ 2 := by
        rw [abs_of_pos (inv_pos.mpr hap)]
        rw [inv_eq_one_div]
        apply (div_le_iff₀ hap).mpr
        linarith [hab.1]
      have he := schwartzToHermiteScale_zero_dilation_norm_sq a ha f
      have hh := mul_le_mul_of_nonneg_right hi (sq_nonneg ‖schwartzToHermiteScale 0 f‖)
      nlinarith [norm_nonneg (schwartzToHermiteScale 0 (combSchwartzDilation a ha f)),
        norm_nonneg (schwartzToHermiteScale 0 f)]
  | succ m ih =>
      obtain ⟨C, hC, hbound⟩ := ih
      let B : ℝ := 4 + 8 * ‖(4 * (Real.pi : ℂ))⁻¹‖ * (36 * Real.pi * 3^m) + 3
      have hB : 0 < B := by dsimp [B]; positivity
      refine ⟨C * B, mul_pos hC hB, ?_⟩
      intro a ha hab f
      obtain ⟨hα, hβ, hγ⟩ := dilation_coefficients_bound a hab
      let α : ℂ := (a:ℂ)⁻¹^2
      let β : ℂ := (4 * (Real.pi:ℂ))⁻¹ * ((a:ℂ)⁻¹^2 - (a:ℂ)^2)
      let γ : ℂ := (1 - (a:ℂ)⁻¹^2)/2
      let g := α • hermiteGraphOperator f +
        β • SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ f) + γ • f
      have hg : ‖schwartzToHermiteScale m g‖ ≤ B * ‖schwartzToHermiteScale (m+1) f‖ := by
        have hD := schwartzToHermiteScale_secondDerivative_norm_bound m f
        have hmono := schwartzToHermiteScale_norm_mono m f
        have hA := mul_le_mul_of_nonneg_right hα (norm_nonneg (schwartzToHermiteScale (m+1) f))
        have hB' := mul_le_mul hβ hD (norm_nonneg _) (by positivity)
        have hG := mul_le_mul hγ hmono (norm_nonneg _) (by positivity)
        dsimp only [g]
        rw [map_add, map_add, map_smul, map_smul, map_smul, schwartzToHermiteScale_graph]
        have htri := (norm_add_le
          (α • schwartzToHermiteScale (m+1) f + β • schwartzToHermiteScale m
            (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ f)))
          (γ • schwartzToHermiteScale m f)).trans
          (add_le_add (norm_add_le _ _) le_rfl)
        simp only [norm_smul] at htri
        dsimp only [α, β, γ, B] at htri ⊢
        nlinarith
      calc
        ‖schwartzToHermiteScale (m+1) (combSchwartzDilation a ha f)‖ =
            ‖schwartzToHermiteScale m (hermiteGraphOperator (combSchwartzDilation a ha f))‖ := by
          rw [schwartzToHermiteScale_graph]
        _ = ‖schwartzToHermiteScale m (combSchwartzDilation a ha g)‖ := by
          rw [graph_combSchwartzDilation]
        _ ≤ C * ‖schwartzToHermiteScale m g‖ := hbound a ha hab g
        _ ≤ C * (B * ‖schwartzToHermiteScale (m+1) f‖) :=
          mul_le_mul_of_nonneg_left hg hC.le
        _ = (C * B) * ‖schwartzToHermiteScale (m+1) f‖ := by ring

end
end MeyerGeneralProblem.Adaptive
