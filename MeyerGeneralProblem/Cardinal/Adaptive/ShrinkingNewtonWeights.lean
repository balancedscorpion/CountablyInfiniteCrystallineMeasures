module

public import MeyerGeneralProblem.Cardinal.Adaptive.PhaseGeometry
public import Mathlib.Analysis.SpecialFunctions.Exp
import all Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecificLimits.Normed
import all Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
import all Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
import all Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Tactic
import all Mathlib.Tactic

@[expose] public section

/-! Numerical membership estimates for the actual variable shrinking Newton weights. -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open Filter Finset
open scoped Topology

/-- Rapid half-seam distances, indexed by their original positive index. -/
def shrinkingRapidDistance (c d b : ℝ) (i : ℕ) : ℝ := c * Real.exp (-d*b^i)

/-- The positive-index Newton normalization contains each original distance exactly once. -/
def shrinkingNewtonWeight (ε : ℕ → ℝ) (i : ℕ) : ℝ := ∏ l ∈ Finset.range i, ε (l+1)

/-- The scalar majorant paid by the variable cutoff and Newton derivatives. The zeroth
entry is harmless; positive entries are exactly formula (10) of the native barrier. -/
def shrinkingNewtonMajorant (ε : ℕ → ℝ) (m i : ℕ) : ℝ :=
  ((i:ℝ)+1)^m / (ε i-ε (i+1))^m / (ε i)^(2*m) * 32^i * shrinkingNewtonWeight ε i

/-- A supergeometric exponential dominates every fixed polynomial and geometric factor. -/
theorem summable_polynomial_geometric_superexponential (m : ℕ) (K A D b : ℝ)
    (hK : 0 ≤ K) (hD : 0 < D) (hb : 1 < b) :
    Summable (fun i : ℕ => ((i:ℝ)+1)^m * K^i * Real.exp (A-D*b^i)) := by
  let f : ℕ → ℝ := fun i => ((i:ℝ)+1)^m * K^i * Real.exp (A-D*b^i)
  have hexp : Tendsto (fun i : ℕ => Real.exp (-(D*(b-1))*b^i)) atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    exact (tendsto_pow_atTop_atTop_of_one_lt hb).const_mul_atTop_of_neg (by nlinarith)
  have hsmall : ∀ᶠ i : ℕ in atTop, (2:ℝ)^m*K*Real.exp (-(D*(b-1))*b^i) ≤ 1/2 := by
    have ht := hexp.const_mul ((2:ℝ)^m*K)
    simp only [mul_zero] at ht
    exact ht.eventually_le_const (by norm_num)
  apply summable_of_ratio_norm_eventually_le (r := (1:ℝ)/2) (by norm_num)
  filter_upwards [hsmall] with i hi
  have hpoly : ((i:ℝ)+1+1)^m ≤ (2:ℝ)^m*((i:ℝ)+1)^m := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    nlinarith
  have hstep : Real.exp (A-D*b^(i+1)) =
      Real.exp (A-D*b^i)*Real.exp (-(D*(b-1))*b^i) := by
    rw [← Real.exp_add,pow_succ]
    congr 1
    ring
  change ‖f (i+1)‖ ≤ 1/2*‖f i‖
  have hpos : ∀ i, 0 ≤ f i := fun i => by dsimp [f]; positivity
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (hpos _),abs_of_nonneg (hpos _)]
  dsimp [f]
  rw [Nat.cast_add,Nat.cast_one,pow_succ,hstep]
  calc
    _ ≤ ((2:ℝ)^m*((i:ℝ)+1)^m)*(K^i*K)*
        (Real.exp (A-D*b^i)*Real.exp (-(D*(b-1))*b^i)) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hpoly (by positivity)) (by positivity)
    _ = ((i:ℝ)+1)^m*K^i*Real.exp (A-D*b^i)*
        ((2:ℝ)^m*K*Real.exp (-(D*(b-1))*b^i)) := by ring
    _ ≤ ((i:ℝ)+1)^m*K^i*Real.exp (A-D*b^i)*(1/2) :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ = _ := by ring

/-- The complete product of the first i rapid distances, with no missing first factor. -/
theorem shrinkingRapidDistance_product (c d b : ℝ) (hb : b ≠ 1) (i : ℕ) :
    shrinkingNewtonWeight (shrinkingRapidDistance c d b) i =
      c^i * Real.exp (-d*b*(b^i-1)/(b-1)) := by
  induction i with
  | zero => simp [shrinkingNewtonWeight]
  | succ i hi =>
    rw [shrinkingNewtonWeight,Finset.prod_range_succ]
    change shrinkingNewtonWeight (shrinkingRapidDistance c d b) i *
      shrinkingRapidDistance c d b (i+1) = _
    rw [hi,shrinkingRapidDistance,pow_succ]
    calc
      _ = (c^i*c)*(Real.exp (-d*b*(b^i-1)/(b-1))*Real.exp (-d*b^(i+1))) := by ring
      _ = _ := by
        rw [← Real.exp_add,pow_succ]
        congr 2
        field_simp
        ring

/-- Each rapid gap has a single positive lower relative bound, independent of the row. -/
theorem shrinkingRapidDistance_gap_lower (c d b : ℝ)
    (hc : 0 < c) (hd : 0 < d) (hb : 1 < b) (i : ℕ) :
    (1-Real.exp (-d*(b-1)))*shrinkingRapidDistance c d b i ≤
      shrinkingRapidDistance c d b i-shrinkingRapidDistance c d b (i+1) := by
  have hp : (1:ℝ) ≤ b^i := one_le_pow₀ hb.le
  have he : Real.exp (-d*(b-1)*b^i) ≤ Real.exp (-d*(b-1)) := by
    apply Real.exp_le_exp.mpr
    exact (mul_le_mul_of_nonpos_left hp (by nlinarith : -d*(b-1) ≤ 0)).trans_eq (mul_one _)
  have hstep : shrinkingRapidDistance c d b (i+1) =
      shrinkingRapidDistance c d b i*Real.exp (-d*(b-1)*b^i) := by
    simp only [shrinkingRapidDistance]
    rw [mul_assoc,← Real.exp_add,pow_succ]
    congr 2
    ring
  rw [hstep]
  have hh := mul_le_mul_of_nonneg_left he (show 0 ≤ shrinkingRapidDistance c d b i by
    dsimp [shrinkingRapidDistance]; positivity)
  nlinarith

/-- The exact normalized rapid Newton product displays the strict native barrier coefficient. -/
theorem shrinkingRapidDistance_normalized_product (c d b : ℝ) (_hc : 0 < c)
    (hb : 1 < b) (m i : ℕ) :
    shrinkingNewtonWeight (shrinkingRapidDistance c d b) i /
      shrinkingRapidDistance c d b i ^ (3*m) =
    c^i/c^(3*m)*Real.exp (d*b/(b-1)-d*(b/(b-1)-3*m)*b^i) := by
  rw [shrinkingRapidDistance_product c d b (ne_of_gt hb)]
  simp only [shrinkingRapidDistance,mul_pow,← Real.exp_nat_mul]
  rw [mul_div_mul_comm,← Real.exp_sub]
  congr 2
  push_cast
  field_simp
  ring

/-- The derivative majorant for actual rapid phases is absolutely summable under
exactly the strict numerical threshold used by the native-order barrier. -/
theorem summable_shrinkingNewtonMajorant_rapid (c d b : ℝ) (hc : 0 < c)
    (hd : 0 < d) (hb : 1 < b) (m : ℕ) (hm : 3*(m:ℝ) < b/(b-1)) :
    Summable (shrinkingNewtonMajorant (shrinkingRapidDistance c d b) m) := by
  let ε := shrinkingRapidDistance c d b
  let θ := 1-Real.exp (-d*(b-1))
  have hθ : 0 < θ := by
    dsimp [θ]
    have he : Real.exp (-d*(b-1)) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
    linarith
  have hε : ∀ i, 0 < ε i := fun i => by dsimp [ε,shrinkingRapidDistance]; positivity
  have hgap : ∀ i, θ*ε i ≤ ε i-ε (i+1) :=
    shrinkingRapidDistance_gap_lower c d b hc hd hb
  have hgpos : ∀ i, 0 < ε i-ε (i+1) := fun i => lt_of_lt_of_le (mul_pos hθ (hε i)) (hgap i)
  have hD : 0 < d*(b/(b-1)-3*m) := mul_pos hd (sub_pos.mpr hm)
  have hs := (summable_polynomial_geometric_superexponential m (32*c)
    (d*b/(b-1)) (d*(b/(b-1)-3*m)) b (by positivity) hD hb).mul_left (1/(θ^m*c^(3*m)))
  apply hs.of_norm_bounded
  intro i
  have hw : 0 < shrinkingNewtonWeight ε i := by
    apply Finset.prod_pos
    intro l hl
    exact hε _
  have hei := hε i
  have hgi := hgpos i
  have hnonneg : 0 ≤ shrinkingNewtonMajorant ε m i := by
    unfold shrinkingNewtonMajorant
    positivity
  rw [Real.norm_eq_abs,abs_of_nonneg hnonneg]
  unfold shrinkingNewtonMajorant
  calc
    _ ≤ ((i:ℝ)+1)^m/(θ*ε i)^m/(ε i)^(2*m)*32^i*shrinkingNewtonWeight ε i := by
      gcongr
      exact hgap i
    _ = (1/θ^m)*((i:ℝ)+1)^m*32^i*
        (shrinkingNewtonWeight ε i / ε i^(3*m)) := by
      rw [show 3*m=m+2*m by omega,pow_add,mul_pow]
      field_simp
    _ = _ := by
      rw [shrinkingRapidDistance_normalized_product c d b hc hb]
      rw [mul_pow]
      ring

/-- The same actual variable-weight majorant is square summable; this is the
numerical input to full tensor moment membership, not a realization assumption. -/
theorem summable_sq_shrinkingNewtonMajorant_rapid (c d b : ℝ) (hc : 0 < c)
    (hd : 0 < d) (hb : 1 < b) (m : ℕ) (hm : 3*(m:ℝ) < b/(b-1)) :
    Summable (fun i => (shrinkingNewtonMajorant (shrinkingRapidDistance c d b) m i)^2) := by
  have hs := summable_shrinkingNewtonMajorant_rapid c d b hc hd hb m hm
  have hn : ∀ i, 0 ≤ shrinkingNewtonMajorant (shrinkingRapidDistance c d b) m i := by
    intro i
    have hgap := shrinkingRapidDistance_gap_lower c d b hc hd hb i
    have he : Real.exp (-d*(b-1)) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
    have hp : 0 < shrinkingRapidDistance c d b i := by dsimp [shrinkingRapidDistance]; positivity
    have hg : 0 < shrinkingRapidDistance c d b i-shrinkingRapidDistance c d b (i+1) :=
      lt_of_lt_of_le (mul_pos (by linarith) hp) hgap
    have hw : 0 ≤ shrinkingNewtonWeight (shrinkingRapidDistance c d b) i := by
      apply Finset.prod_nonneg
      intro l hl
      dsimp [shrinkingRapidDistance]
      positivity
    unfold shrinkingNewtonMajorant
    positivity
  have hp := (hs.mul_of_nonneg hs hn hn).comp_injective (show Function.Injective (fun i : ℕ => (i,i)) from fun i j h => congrArg Prod.fst h)
  simpa only [pow_two, Function.comp_apply] using! hp

/-- The actual block base satisfies the strict low-order membership threshold
simultaneously for every original native order p≤P, including p=0. -/
theorem rapidBase_native_membership_threshold (P p : ℕ) (hP : 1 ≤ P) (hp : p ≤ P) :
    3*((2*p:ℕ):ℝ) < rapidBase P/(rapidBase P-1) := by
  have hPpos : (0:ℝ) < P := by exact_mod_cast hP
  have hple : (p:ℝ) ≤ P := by exact_mod_cast hp
  have he : rapidBase P/(rapidBase P-1) = 6*(P:ℝ)+1 := by
    unfold rapidBase
    field_simp
    ring
  rw [he]
  push_cast
  linarith

/-- The majorant of the actual high-order block's rapid tail is square summable
at the exact compact distribution order 2p used by native exclusion. -/
theorem summable_sq_actualRapidNewtonMajorant (P R p : ℕ)
    (hP : 1 ≤ P) (hR : 1 ≤ R) (hp : p ≤ P) :
    Summable (fun i => (shrinkingNewtonMajorant (rapidDistance P R) (2*p) i)^2) :=
  summable_sq_shrinkingNewtonMajorant_rapid (1/16) (rapidDecay P R) (rapidBase P)
    (by norm_num) (rapidDecay_pos hP hR) (rapidBase_one_lt hP) (2*p)
    (rapidBase_native_membership_threshold P p hP hp)

/-- The whole two-index square majorant is summable, with both infinite arms
included. Restricting to the principal quadrant is unnecessary. -/
theorem summable_sq_actualRapidNewtonTensor (P R p : ℕ)
    (hP : 1 ≤ P) (hR : 1 ≤ R) (hp : p ≤ P) :
    Summable (fun ij : ℕ×ℕ =>
      (shrinkingNewtonMajorant (rapidDistance P R) (2*p) ij.1)^2 *
      (shrinkingNewtonMajorant (rapidDistance P R) (2*p) ij.2)^2) :=
  (summable_sq_actualRapidNewtonMajorant P R p hP hR hp).mul_of_nonneg
    (summable_sq_actualRapidNewtonMajorant P R p hP hR hp)
    (fun _ => sq_nonneg _) (fun _ => sq_nonneg _)

end
end MeyerGeneralProblem.Adaptive
