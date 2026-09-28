module

public import Mathlib.Topology.Algebra.Polynomial
import all Mathlib.Topology.Algebra.Polynomial

public import MeyerGeneralProblem.Cardinal.Adaptive.ScaleProbability
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import all Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.LinearAlgebra.Lagrange
import all Mathlib.LinearAlgebra.Lagrange

@[expose] public section

/-!
# A quantitative quadratic sublevel estimate on the actual scale interval

Three separated samples control every quadratic coefficient by Lagrange
interpolation. A set without three separated points is covered by two short
intervals, yielding an actual Lebesgue-measure bound with an absolute constant.
-/

namespace MeyerGeneralProblem.Adaptive

noncomputable section

open MeasureTheory Set

/-- An actual quadratic, with all three coefficients displayed. -/
def quadraticValue (a b c x : ℝ) : ℝ := a*x^2+b*x+c

/-- Three-point Lagrange identities, with shared denominator factors. -/
theorem quadratic_three_point_coefficients (a b c x y z : ℝ)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    let A := quadraticValue a b c x / ((x-y)*(x-z))
    let B := -quadraticValue a b c y / ((x-y)*(y-z))
    let C := quadraticValue a b c z / ((x-z)*(y-z))
    a = A+B+C ∧ b = -((y+z)*A+(x+z)*B+(x+y)*C) ∧
      c = y*z*A+x*z*B+x*y*C := by
  have hxy' := sub_ne_zero.mpr hxy
  have hxz' := sub_ne_zero.mpr hxz
  have hyz' := sub_ne_zero.mpr hyz
  dsimp [quadraticValue]
  constructor
  · field_simp
    ring
  · constructor
    · field_simp
      ring
    · field_simp
      ring

/-- A two-factor separation lower bound controls an interpolation weight. -/
theorem interpolation_weight_bound {u δ v d e : ℝ} (hu : 0 ≤ u) (hδ : 0 < δ)
    (hv : |v| ≤ u) (hd : δ ≤ |d|) (he : δ ≤ |e|) :
    |v / (d*e)| ≤ u / δ^2 := by
  have hsq : 0 < δ^2 := sq_pos_of_pos hδ
  have hden : δ^2 ≤ |d*e| := by
    rw [abs_mul]
    nlinarith [mul_le_mul hd he hδ.le (abs_nonneg d)]
  rw [abs_div]
  exact (div_le_div_of_nonneg_right hv ((hsq.le).trans hden)).trans
    (div_le_div_of_nonneg_left hu hsq hden)

/-- The elementary triangle inequality for three scalar summands. -/
theorem abs_sum_three_le (x y z : ℝ) : |x+y+z| ≤ |x|+|y|+|z| :=
  (abs_add_le (x+y) z).trans (add_le_add (abs_add_le x y) le_rfl)

/-- Bounded nodes give uniform coefficient bounds for the three interpolation weights. -/
theorem interpolation_coefficient_bounds {x y z A B C K : ℝ}
    (hx : |x| ≤ 2) (hy : |y| ≤ 2) (hz : |z| ≤ 2)
    (hA : |A| ≤ K) (hB : |B| ≤ K) (hC : |C| ≤ K) :
    |A+B+C| ≤ 12*K ∧ |-((y+z)*A+(x+z)*B+(x+y)*C)| ≤ 12*K ∧
      |y*z*A+x*z*B+x*y*C| ≤ 12*K := by
  have hK : 0 ≤ K := (abs_nonneg A).trans hA
  have hsum : ∀ v w W : ℝ, |v| ≤ 2 → |w| ≤ 2 → |W| ≤ K →
      |(v+w)*W| ≤ 4*K := by
    intro v w W hv hw hW
    have hvw : |v+w| ≤ 4 := (abs_add_le v w).trans (by linarith)
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right hvw (abs_nonneg W)).trans
      (mul_le_mul_of_nonneg_left hW (by norm_num))
  have hprod : ∀ v w W : ℝ, |v| ≤ 2 → |w| ≤ 2 → |W| ≤ K →
      |v*w*W| ≤ 4*K := by
    intro v w W hv hw hW
    have hvw : |v*w| ≤ 4 := by
      rw [abs_mul]
      nlinarith [mul_le_mul hv hw (abs_nonneg w) (by norm_num : (0:ℝ) ≤ 2)]
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right hvw (abs_nonneg W)).trans
      (mul_le_mul_of_nonneg_left hW (by norm_num))
  constructor
  · have h := abs_sum_three_le A B C
    linarith
  · constructor
    · rw [abs_neg]
      have h := abs_sum_three_le ((y+z)*A) ((x+z)*B) ((x+y)*C)
      have h1 := hsum y z A hy hz hA
      have h2 := hsum x z B hx hz hB
      have h3 := hsum x y C hx hy hC
      linarith
    · have h := abs_sum_three_le (y*z*A) (x*z*B) (x*y*C)
      have h1 := hprod y z A hy hz hA
      have h2 := hprod x z B hx hz hB
      have h3 := hprod x y C hx hy hC
      linarith

/-- Three separated small values control each original coefficient, with no normalization change. -/
theorem quadratic_coefficients_le_of_three_samples (a b c u δ x y z : ℝ)
    (hu : 0 ≤ u) (hδ : 0 < δ)
    (hx : x ∈ Icc 1 2) (hy : y ∈ Icc 1 2) (hz : z ∈ Icc 1 2)
    (hxy : δ ≤ |x-y|) (hxz : δ ≤ |x-z|) (hyz : δ ≤ |y-z|)
    (hqx : |quadraticValue a b c x| ≤ u)
    (hqy : |quadraticValue a b c y| ≤ u)
    (hqz : |quadraticValue a b c z| ≤ u) :
    |a| ≤ 12 * (u / δ^2) ∧ |b| ≤ 12 * (u / δ^2) ∧ |c| ≤ 12 * (u / δ^2) := by
  have hxy' : x ≠ y := by intro h; subst y; simpa using hδ.trans_le hxy
  have hxz' : x ≠ z := by intro h; subst z; simpa using hδ.trans_le hxz
  have hyz' : y ≠ z := by intro h; subst z; simpa using hδ.trans_le hyz
  obtain ⟨ha, hb, hc⟩ := quadratic_three_point_coefficients a b c x y z hxy' hxz' hyz'
  have hA := interpolation_weight_bound hu hδ hqx hxy hxz
  have hB := interpolation_weight_bound (v := -quadraticValue a b c y) hu hδ
    (by simpa only [abs_neg] using hqy) hxy hyz
  have hC := interpolation_weight_bound hu hδ hqz hxz hyz
  have hxabs : |x| ≤ 2 := by rw [abs_of_nonneg (by linarith [hx.1])]; exact hx.2
  have hyabs : |y| ≤ 2 := by rw [abs_of_nonneg (by linarith [hy.1])]; exact hy.2
  have hzabs : |z| ≤ 2 := by rw [abs_of_nonneg (by linarith [hz.1])]; exact hz.2
  have h := interpolation_coefficient_bounds hxabs hyabs hzabs hA hB hC
  simpa only [← ha, ← hb, ← hc] using h

/-- A subset of the line without three δ-separated points has measure at most 4δ. -/
theorem volume_le_four_radius_of_no_separated_triple (S : Set ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hthree : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S,
      δ ≤ |x-y| → δ ≤ |x-z| → δ ≤ |y-z| → False) :
    volume S ≤ ENNReal.ofReal (4*δ) := by
  by_cases hS : S.Nonempty
  · obtain ⟨x, hx⟩ := hS
    by_cases hfirst : S ⊆ Metric.ball x δ
    · calc
        volume S ≤ volume (Metric.ball x δ) := measure_mono hfirst
        _ = ENNReal.ofReal (2*δ) := Real.volume_ball _ _
        _ ≤ ENNReal.ofReal (4*δ) := ENNReal.ofReal_le_ofReal (by linarith)
    · obtain ⟨y, hy, hyout⟩ := Set.not_subset.mp hfirst
      have hxy : δ ≤ |x-y| := by
        have h := le_of_not_gt (show ¬ dist y x < δ from hyout)
        simpa only [Real.dist_eq, abs_sub_comm] using h
      have hcover : S ⊆ Metric.ball x δ ∪ Metric.ball y δ := by
        intro z hz
        by_contra hout
        have hout' : z ∉ Metric.ball x δ ∧ z ∉ Metric.ball y δ := not_or.mp hout
        have hxz : δ ≤ |x-z| := by
          have h := le_of_not_gt (show ¬ dist z x < δ from hout'.1)
          simpa only [Real.dist_eq, abs_sub_comm] using h
        have hyz : δ ≤ |y-z| := by
          have h := le_of_not_gt (show ¬ dist z y < δ from hout'.2)
          simpa only [Real.dist_eq, abs_sub_comm] using h
        exact hthree x hx y hy z hz hxy hxz hyz
      calc
        volume S ≤ volume (Metric.ball x δ ∪ Metric.ball y δ) := measure_mono hcover
        _ ≤ volume (Metric.ball x δ) + volume (Metric.ball y δ) := measure_union_le _ _
        _ = ENNReal.ofReal (4*δ) := by
          rw [Real.volume_ball, Real.volume_ball, ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          ring
  · rw [Set.not_nonempty_iff_eq_empty.mp hS]
    simp

/-- Actual coefficient-normalized quadratic sublevel volume on the scale interval. -/
theorem quadratic_sublevel_volume_le (a b c d u : ℝ) (hd : 0 < d) (hu : 0 < u)
    (hcoef : d ≤ |a| ∨ d ≤ |b| ∨ d ≤ |c|) :
    volume {x : ℝ | x ∈ Icc 1 2 ∧ |quadraticValue a b c x| < u} ≤
      ENNReal.ofReal (16 * Real.sqrt (u / d)) := by
  let δ : ℝ := 4 * Real.sqrt (u / d)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδsq : δ^2 = 16 * (u/d) := by
    dsimp [δ]
    nlinarith [Real.sq_sqrt (by positivity : 0 ≤ u/d)]
  have hbound := volume_le_four_radius_of_no_separated_triple
    {x : ℝ | x ∈ Icc 1 2 ∧ |quadraticValue a b c x| < u} hδ
  have htri : ∀ x ∈ {x : ℝ | x ∈ Icc 1 2 ∧ |quadraticValue a b c x| < u},
      ∀ y ∈ {x : ℝ | x ∈ Icc 1 2 ∧ |quadraticValue a b c x| < u},
      ∀ z ∈ {x : ℝ | x ∈ Icc 1 2 ∧ |quadraticValue a b c x| < u},
      δ ≤ |x-y| → δ ≤ |x-z| → δ ≤ |y-z| → False := by
    intro x hx y hy z hz hxy hxz hyz
    obtain ⟨ha, hb, hc⟩ := quadratic_coefficients_le_of_three_samples a b c u δ x y z
      hu.le hδ hx.1 hy.1 hz.1 hxy hxz hyz hx.2.le hy.2.le hz.2.le
    have hdsmall : d ≤ 12 * (u/δ^2) := by
      rcases hcoef with h | h | h
      · exact h.trans ha
      · exact h.trans hb
      · exact h.trans hc
    have hmul : d*δ^2 ≤ 12*u := by
      apply (le_div_iff₀ (sq_pos_of_pos hδ)).mp
      simpa only [mul_div_assoc] using hdsmall
    have heq : d*δ^2 = 16*u := by
      rw [hδsq]
      field_simp
    linarith
  simpa only [δ, show (4 : ℝ) * (4 * Real.sqrt (u/d)) = 16 * Real.sqrt (u/d) by ring]
    using hbound htri

/-- Every polynomial of degree at most two has exactly the displayed quadratic evaluation. -/
theorem eval_eq_quadraticValue (p : Polynomial ℝ) (hp : p.natDegree ≤ 2) (x : ℝ) :
    p.eval x = quadraticValue (p.coeff 2) (p.coeff 1) (p.coeff 0) x := by
  rw [Polynomial.eval_eq_sum_range' (n := 3) (by omega)]
  simp [Finset.sum_range_succ, quadraticValue]
  ring

/-- The quadratic estimate applies to any genuine polynomial with one nontrivial coefficient. -/
theorem polynomial_quadratic_sublevel_volume_le (p : Polynomial ℝ) (hp : p.natDegree ≤ 2)
    (d u : ℝ) (hd : 0 < d) (hu : 0 < u) (hc : ∃ i, d ≤ |p.coeff i|) :
    volume {x : ℝ | x ∈ Icc 1 2 ∧ |p.eval x| < u} ≤
      ENNReal.ofReal (16 * Real.sqrt (u / d)) := by
  obtain ⟨i, hi⟩ := hc
  have hi2 : i ≤ 2 := by
    by_contra h
    have hz : p.coeff i = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    simp only [hz, abs_zero] at hi
    linarith
  have hcoef : d ≤ |p.coeff 2| ∨ d ≤ |p.coeff 1| ∨ d ≤ |p.coeff 0| := by
    interval_cases i <;> tauto
  simpa only [eval_eq_quadraticValue p hp] using
    quadratic_sublevel_volume_le (p.coeff 2) (p.coeff 1) (p.coeff 0) d u hd hu hcoef

/-- Coefficient-normalized quadratic small-ball probability for the actual uniform scale law. -/
theorem polynomial_quadratic_scaleLaw_sublevel_le (p : Polynomial ℝ) (hp : p.natDegree ≤ 2)
    (d u : ℝ) (hd : 0 < d) (hu : 0 < u) (hc : ∃ i, d ≤ |p.coeff i|) :
    scaleLaw {x : ℝ | |p.eval x| < u} ≤
      min 1 (ENNReal.ofReal (16 * Real.sqrt (u / d))) := by
  apply le_min
  · calc
      _ ≤ scaleLaw Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  · unfold scaleLaw
    rw [Measure.restrict_apply₀]
    · rw [Set.inter_comm]
      exact polynomial_quadratic_sublevel_volume_le p hp d u hd hu hc
    · exact (isOpen_lt (p.continuous.abs) continuous_const).measurableSet.nullMeasurableSet

/-- The single-coordinate bound also holds in the genuine infinite product scale space. -/
theorem polynomial_quadratic_coordinate_sublevel_le (i : ℕ+) (p : Polynomial ℝ)
    (hp : p.natDegree ≤ 2) (d u : ℝ) (hd : 0 < d) (hu : 0 < u)
    (hc : ∃ k, d ≤ |p.coeff k|) :
    scaleProbability {s : ℕ+ → ℝ | |p.eval (s i)| < u} ≤
      min 1 (ENNReal.ofReal (16 * Real.sqrt (u / d))) := by
  have hm : MeasurableSet {x : ℝ | |p.eval x| < u} :=
    (isOpen_lt (p.continuous.abs) continuous_const).measurableSet
  have hmap := Measure.map_apply (μ := scaleProbability) (measurable_pi_apply i) hm
  rw [scaleProbability_map_eval] at hmap
  change scaleProbability ((fun s => s i) ⁻¹' {x : ℝ | |p.eval x| < u}) ≤ _
  rw [← hmap]
  exact polynomial_quadratic_scaleLaw_sublevel_le p hp d u hd hu hc

end
end MeyerGeneralProblem.Adaptive
