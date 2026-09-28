module

public import MeyerGeneralProblem.Distribution.CompactSmoothDivision
public import Mathlib.Analysis.Calculus.ParametricIntegral
import all Mathlib.Analysis.Calculus.ParametricIntegral

@[expose] public section

/-!
# All derivative bounds for the actual smooth divided difference

The derivative-integral formula loses precisely one input derivative. This is
an analytic estimate for the numerator of removable division, not an assumed
global division operator.
-/

namespace MeyerGeneralProblem

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff

/-- The integral appearing after differentiating the genuine divided difference `n` times. -/
def weightedDividedDifference (ψ : SchwartzMap ℝ ℂ) (z : ℝ) (n : ℕ) (x : ℝ) : ℂ :=
  ∫ t in (0 : ℝ)..1, (t^n) • iteratedDeriv (n+1) ψ (z+t*(x-z))

/-- Differentiating under the fixed compact parameter integral is justified by
 the next actual Schwartz derivative bound. -/
theorem weightedDividedDifference_hasDerivAt
    (ψ : SchwartzMap ℝ ℂ) (z : ℝ) (n : ℕ) (x : ℝ) :
    HasDerivAt (weightedDividedDifference ψ z n)
      (weightedDividedDifference ψ z (n+1) x) x := by
  let μ := volume.restrict (Ioc (0 : ℝ) 1)
  let F : ℝ → ℝ → ℂ := fun y t => t^n • iteratedDeriv (n+1) ψ (z+t*(y-z))
  let F' : ℝ → ℝ → ℂ := fun y t => t^(n+1) • iteratedDeriv (n+2) ψ (z+t*(y-z))
  have hc (m : ℕ) : Continuous (iteratedDeriv m ψ) :=
    (ψ.smooth (⊤ : ℕ∞)).continuous_iteratedDeriv m (by simp)
  have hFc (y : ℝ) : Continuous (F y) := by dsimp [F]; fun_prop
  have hF'c (y : ℝ) : Continuous (F' y) := by dsimp [F']; fun_prop
  have hdiff (t y : ℝ) : HasDerivAt (fun y => F y t) (F' y t) y := by
    have hd := ((ψ.smooth ((n+2 : ℕ) : ℕ∞)).differentiable_iteratedDeriv (n+1) (by norm_cast; omega)
      (z+t*(y-z))).hasDerivAt
    have hi : HasDerivAt (fun y : ℝ => z+t*(y-z)) t y := by
      convert! ((((hasDerivAt_id y).sub_const z).const_mul t).const_add z) using 1
      simp
    have h := (hd.scomp y hi).const_smul (t^n)
    convert! h using 1
    simp only [F', smul_smul, ← iteratedDeriv_succ, pow_succ]
  have hbound : ∀ᵐ t ∂μ, ∀ y ∈ (univ : Set ℝ),
      ‖F' y t‖ ≤ SchwartzMap.seminorm ℂ 0 (n+2) ψ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    intro y _
    have ht1 : |t| ≤ 1 := by simpa only [abs_of_pos ht.1] using ht.2
    have hp : |t|^(n+1) ≤ 1 := pow_le_one₀ (abs_nonneg t) ht1
    have hd := ψ.le_seminorm ℂ 0 (n+2) (z+t*(y-z))
    simp only [pow_zero, one_mul, norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hd
    calc
      ‖F' y t‖ = |t|^(n+1) * ‖iteratedDeriv (n+2) ψ (z+t*(y-z))‖ := by
        simp only [F', norm_smul, Real.norm_eq_abs, abs_pow]
      _ ≤ 1 * SchwartzMap.seminorm ℂ 0 (n+2) ψ :=
        mul_le_mul hp hd (norm_nonneg _) (by positivity)
      _ = _ := one_mul _
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (F := F) (F' := F') (s := (univ : Set ℝ))
    (bound := fun _ => SchwartzMap.seminorm ℂ 0 (n+2) ψ)
    (Filter.univ_mem : (univ : Set ℝ) ∈ 𝓝 x)
    (Filter.Eventually.of_forall (fun y => (hFc y).aestronglyMeasurable))
    ((hFc x).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    (hF'c x).aestronglyMeasurable hbound
    (integrable_const _)
    (Filter.Eventually.of_forall (fun t y _ => hdiff t y))
  unfold weightedDividedDifference
  simpa only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    F, F', μ, Nat.add_assoc, Nat.reduceAdd] using h.2

/-- Exact all-order differentiation formula for the genuine smooth divided difference. -/
theorem iteratedDeriv_smoothDividedDifference (ψ : SchwartzMap ℝ ℂ) (z : ℝ) (n : ℕ) :
    iteratedDeriv n (smoothDividedDifference ψ z) = weightedDividedDifference ψ z n := by
  induction n with
  | zero =>
    funext x
    simp only [iteratedDeriv_zero, weightedDividedDifference, pow_zero, one_smul,
      Nat.zero_add, iteratedDeriv_one, smoothDividedDifference]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    exact (weightedDividedDifference_hasDerivAt ψ z n x).deriv

/-- The actual all-order divided difference estimate with one input derivative loss. -/
theorem norm_iteratedDeriv_smoothDividedDifference_le
    (ψ : SchwartzMap ℝ ℂ) (z x : ℝ) (n : ℕ) :
    ‖iteratedDeriv n (smoothDividedDifference ψ z) x‖ ≤
      SchwartzMap.seminorm ℂ 0 (n+1) ψ := by
  rw [iteratedDeriv_smoothDividedDifference]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (C := SchwartzMap.seminorm ℂ 0 (n+1) ψ)
    (f := fun t => t^n • iteratedDeriv (n+1) ψ (z+t*(x-z))) (fun t ht => by
      have ht' : t ∈ Ioc (0 : ℝ) 1 := by simpa using ht
      have hp : |t|^n ≤ 1 := pow_le_one₀ (abs_nonneg t)
        (by simpa only [abs_of_pos ht'.1] using ht'.2)
      rw [norm_smul, Real.norm_eq_abs, abs_pow]
      have hd := ψ.le_seminorm ℂ 0 (n+1) (z+t*(x-z))
      simp only [pow_zero, one_mul, norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hd
      exact (mul_le_mul hp hd (norm_nonneg _) (by positivity)).trans_eq (one_mul _))
  simpa only [weightedDividedDifference, sub_zero, one_mul, mul_one, abs_one] using h


/-- Weighted all-order control on any fixed-radius divided-difference neighborhood.
The estimate uses only input Schwartz derivatives through order `n+1`. -/
theorem weighted_norm_iteratedDeriv_smoothDividedDifference_le
    (ψ : SchwartzMap ℝ ℂ) (z x r : ℝ) (hr : 0 ≤ r) (hxz : |x-z| ≤ r) (k n : ℕ) :
    (1+‖x‖)^k * ‖iteratedDeriv n (smoothDividedDifference ψ z) x‖ ≤
      ((1+r)^k * 2^k) *
        (Finset.Iic (k,n+1)).sup (schwartzSeminormFamily ℂ ℝ ℂ) ψ := by
  let C := ((1+r)^k * 2^k) *
    (Finset.Iic (k,n+1)).sup (schwartzSeminormFamily ℂ ℝ ℂ) ψ
  have hbound : ∀ t ∈ Set.uIoc (0 : ℝ) 1,
      ‖(1+‖x‖)^k • (t^n • iteratedDeriv (n+1) ψ (z+t*(x-z)))‖ ≤ C := by
    intro t ht
    have ht' : t ∈ Ioc (0 : ℝ) 1 := by simpa using ht
    let u := z+t*(x-z)
    have hxu : |x-u| ≤ r := by
      have heq : x-u = (1-t)*(x-z) := by dsimp [u]; ring
      rw [heq, abs_mul, abs_of_nonneg (sub_nonneg.mpr ht'.2)]
      calc
        (1-t) * |x-z| ≤ 1 * r :=
          mul_le_mul (by linarith [ht'.1]) hxz (abs_nonneg _) (by norm_num)
        _ = r := one_mul _
    have hw : 1+‖x‖ ≤ (1+r)*(1+‖u‖) := by
      have htri := norm_add_le (x-u) u
      simp only [sub_add_cancel, Real.norm_eq_abs] at htri ⊢
      nlinarith [abs_nonneg u]
    have hp : |t|^n ≤ 1 := pow_le_one₀ (abs_nonneg t)
      (by simpa only [abs_of_pos ht'.1] using ht'.2)
    have hv := SchwartzMap.one_add_le_sup_seminorm_apply
      (𝕜 := ℂ) (m := (k,n+1)) le_rfl le_rfl ψ u
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hv
    calc
      _ = (1+‖x‖)^k * (|t|^n * ‖iteratedDeriv (n+1) ψ u‖) := by
        simp only [norm_smul, Real.norm_eq_abs, abs_pow,
          abs_of_nonneg (by positivity : 0 ≤ 1+|x|), u]
      _ ≤ ((1+r)*(1+‖u‖))^k * (1 * ‖iteratedDeriv (n+1) ψ u‖) := by gcongr
      _ = (1+r)^k * ((1+‖u‖)^k * ‖iteratedDeriv (n+1) ψ u‖) := by rw [mul_pow]; ring
      _ ≤ (1+r)^k * (2^k * (Finset.Iic (k,n+1)).sup (schwartzSeminormFamily ℂ ℝ ℂ) ψ) :=
        mul_le_mul_of_nonneg_left hv (by positivity)
      _ = C := by dsimp [C]; ring
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (C := C)
    (f := fun t => (1+‖x‖)^k • (t^n • iteratedDeriv (n+1) ψ (z+t*(x-z)))) hbound
  rw [intervalIntegral.integral_smul, norm_smul,
    Real.norm_eq_abs, abs_pow, abs_of_nonneg (by positivity : 0 ≤ 1+‖x‖)] at h
  rw [iteratedDeriv_smoothDividedDifference]
  simpa only [C, weightedDividedDifference, sub_zero, abs_one, mul_one] using h

#print axioms weightedDividedDifference_hasDerivAt
#print axioms iteratedDeriv_smoothDividedDifference
#print axioms norm_iteratedDeriv_smoothDividedDifference_le
#print axioms weighted_norm_iteratedDeriv_smoothDividedDifference_le

end
end MeyerGeneralProblem
