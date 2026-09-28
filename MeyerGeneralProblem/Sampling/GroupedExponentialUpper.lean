module

public import MeyerGeneralProblem.Sampling.GroupedExponential
public import MeyerGeneralProblem.Sampling.FourierRectangle
public import Mathlib.Analysis.Convex.Integral
import all Mathlib.Analysis.Convex.Integral
public import Mathlib.Algebra.Order.Chebyshev
import all Mathlib.Algebra.Order.Chebyshev

@[expose] public section

/-!
# Dimension-uniform upper bounds for grouped exponentials

Hermite–Genocchi averaging keeps each virtual frequency inside its own group
interval.  Distinct intervals remain positively separated, so the existing
upper large sieve applies without any minimum gap inside a group.
-/

namespace MeyerGeneralProblem

open MeasureTheory Set
open scoped Interval

noncomputable section

/-- Jensen's inequality on the unit interval, in the complex norm squared. -/
theorem norm_unit_interval_integral_sq_le (f : ℝ → ℂ) (hf : Continuous f) :
    ‖∫ u : ℝ in Icc (0 : ℝ) 1, f u‖ ^ 2 ≤
      ∫ u : ℝ in Icc (0 : ℝ) 1, ‖f u‖ ^ 2 := by
  have hconv : ConvexOn ℝ Set.univ (fun z : ℂ => ‖z‖ ^ 2) :=
    convexOn_univ_norm.pow (fun _ _ => norm_nonneg _) 2
  have h := hconv.map_set_average_le (by fun_prop) isClosed_univ
    (by simp : volume (Icc (0 : ℝ) 1) ≠ 0)
    (by simp : volume (Icc (0 : ℝ) 1) ≠ ⊤)
    (Filter.Eventually.of_forall (fun u => Set.mem_univ (f u)))
    (hf.continuousOn.integrableOn_compact isCompact_Icc)
    ((hf.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc)
  simpa only [setAverage_eq, Real.volume_real_Icc_of_le (by norm_num : (0 : ℝ) ≤ 1),
    sub_zero, inv_one, one_smul] using h

/-- Averaging a continuous family of functions over the unit interval does
not enlarge a common squared `L²` bound on a compact time interval. -/
theorem integral_norm_unit_average_sq_le
    (f : ℝ → ℝ → ℂ) (hf : Continuous (Function.uncurry f))
    {lo hi B : ℝ}
    (hB : ∀ u ∈ Icc (0 : ℝ) 1,
      (∫ t : ℝ in Icc lo hi, ‖f u t‖ ^ 2) ≤ B) :
    (∫ t : ℝ in Icc lo hi, ‖∫ u : ℝ in Icc (0 : ℝ) 1, f u t‖ ^ 2) ≤ B := by
  have hprod : Integrable (fun p : ℝ × ℝ => ‖f p.2 p.1‖ ^ 2)
      ((volume.restrict (Icc lo hi)).prod (volume.restrict (Icc (0 : ℝ) 1))) := by
    rw [Measure.prod_restrict]
    exact ((hf.comp continuous_swap).norm.pow 2).continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)
  have hswap : Continuous (fun p : ℝ × ℝ => f p.2 p.1) := hf.comp continuous_swap
  have havg : Continuous (fun t : ℝ => ∫ u : ℝ in Icc (0 : ℝ) 1, f u t) :=
    continuous_parametric_integral_of_continuous hswap isCompact_Icc
  calc
    _ ≤ ∫ t : ℝ in Icc lo hi, ∫ u : ℝ in Icc (0 : ℝ) 1, ‖f u t‖ ^ 2 := by
      apply integral_mono (havg.norm.pow 2).integrableOn_Icc hprod.integral_prod_left
      intro t
      exact norm_unit_interval_integral_sq_le _ (hf.comp (continuous_id.prodMk continuous_const))
    _ = ∫ u : ℝ in Icc (0 : ℝ) 1, ∫ t : ℝ in Icc lo hi, ‖f u t‖ ^ 2 :=
      integral_integral_swap hprod
    _ ≤ ∫ _u : ℝ in Icc (0 : ℝ) 1, B := by
      exact setIntegral_mono_on hprod.integral_prod_right (integrable_const _) measurableSet_Icc hB
    _ = B := by simp

private theorem continuous_weighted_group_average
    (order : ℕ) (g : ℝ → ℝ → ℂ) (hg : Continuous (Function.uncurry g)) (a : ℝ) :
    Continuous (fun p : ℝ × ℝ => weightedDerivativeAverage order (fun s => g s p.2) a p.1) := by
  have hc : Continuous (fun p : (ℝ × ℝ) × ℝ =>
      p.2 ^ order • g (a + (p.1.1 - a) * p.2) p.1.2) := by
    apply (continuous_snd.pow order).smul
    exact hg.comp (show Continuous (fun p : (ℝ × ℝ) × ℝ =>
      (a + (p.1.1 - a) * p.2, p.1.2)) by fun_prop)
  have hi : Continuous (fun p : ℝ × ℝ => ∫ u : ℝ in Icc (0 : ℝ) 1,
      u ^ order • g (a + (p.1 - a) * u) p.2) :=
    continuous_parametric_integral_of_continuous hc isCompact_Icc
  simpa only [weightedDerivativeAverage,
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_Icc_eq_integral_Ioc] using hi

/-- Weighted affine averaging of every group preserves a common virtual-node
synthesis energy bound.  Only interval convexity is used. -/
theorem virtual_frequency_bound_weighted_average
    {n : ℕ} (order : ℕ) (g : Fin n → ℝ → ℝ → ℂ) (c : Fin n → ℂ)
    (hg : ∀ i, Continuous (Function.uncurry (g i)))
    (L U base : Fin n → ℝ) (hbase : ∀ i, base i ∈ Icc (L i) (U i))
    {lo hi B : ℝ}
    (hbound : ∀ x : Fin n → ℝ, (∀ i, x i ∈ Icc (L i) (U i)) →
      (∫ t : ℝ in Icc lo hi, ‖∑ i, c i * g i (x i) t‖ ^ 2) ≤ B)
    (x : Fin n → ℝ) (hx : ∀ i, x i ∈ Icc (L i) (U i)) :
    (∫ t : ℝ in Icc lo hi,
      ‖∑ i, c i * weightedDerivativeAverage order (fun s => g i s t) (base i) (x i)‖ ^ 2) ≤ B := by
  let f : ℝ → ℝ → ℂ := fun u t =>
    ∑ i, c i * (u ^ order • g i (base i + (x i - base i) * u) t)
  have hf : Continuous (Function.uncurry f) := by
    apply continuous_finsetSum
    intro i hi
    apply continuous_const.mul
    apply (continuous_fst.pow order).smul
    exact (hg i).comp (show Continuous (fun p : ℝ × ℝ =>
      (base i + (x i - base i) * p.1, p.2)) by fun_prop)
  have heq (t : ℝ) :
      (∑ i, c i * weightedDerivativeAverage order (fun s => g i s t) (base i) (x i)) =
        ∫ u : ℝ in Icc (0 : ℝ) 1, f u t := by
    simp only [weightedDerivativeAverage,
      intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      ← integral_Icc_eq_integral_Ioc, f]
    rw [integral_finsetSum]
    · simp only [integral_const_mul]
    · intro i hi
      apply Continuous.integrableOn_Icc
      apply continuous_const.mul
      apply (continuous_id.pow order).smul
      exact (hg i).comp (show Continuous (fun u : ℝ =>
        (base i + (x i - base i) * u, t)) by fun_prop)
  simp_rw [heq]
  apply integral_norm_unit_average_sq_le f hf
  intro u hu
  let y : Fin n → ℝ := fun i => base i + (x i - base i) * u
  have hy (i : Fin n) : y i ∈ Icc (L i) (U i) :=
    uIcc_subset_Icc (hbase i) (hx i) (affineNode_mem_uIcc (base i) (x i) hu)
  have hfactor (t : ℝ) : f u t = (u ^ order : ℝ) • (∑ i, c i * g i (y i) t) := by
    simp only [f, y, Finset.smul_sum, Complex.real_smul]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hpow : (u ^ order) ^ 2 ≤ 1 := pow_le_one₀ (pow_nonneg hu.1 _) (pow_le_one₀ hu.1 hu.2)
  have hnonneg : 0 ≤ ∫ t : ℝ in Icc lo hi, ‖∑ i, c i * g i (y i) t‖ ^ 2 :=
    integral_nonneg (fun t => sq_nonneg _)
  calc
    _ = (u ^ order) ^ 2 * ∫ t : ℝ in Icc lo hi, ‖∑ i, c i * g i (y i) t‖ ^ 2 := by
      simp only [hfactor, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (pow_nonneg hu.1 _), mul_pow, integral_const_mul]
    _ ≤ ∫ t : ℝ in Icc lo hi, ‖∑ i, c i * g i (y i) t‖ ^ 2 := by
      nlinarith
    _ ≤ B := hbound y hy

/-- Genuine Hermite–Genocchi integration preserves a uniform synthesis
bound valid for all virtual frequencies in the enclosing group intervals.
The estimate is independent of the number of groups and all internal gaps. -/
theorem integral_hermiteGenocchi_synthesis_sq_le
    {n : ℕ} (nodes : Fin n → ℕ → ℝ) (order : ℕ)
    (g : Fin n → ℝ → ℝ → ℂ) (c : Fin n → ℂ)
    (hg : ∀ i, Continuous (Function.uncurry (g i)))
    (L U : Fin n → ℝ) (hnodes : ∀ i j, j ≤ order → nodes i j ∈ Icc (L i) (U i))
    {lo hi B : ℝ}
    (hbound : ∀ x : Fin n → ℝ, (∀ i, x i ∈ Icc (L i) (U i)) →
      (∫ t : ℝ in Icc lo hi, ‖∑ i, c i * g i (x i) t‖ ^ 2) ≤ B) :
    (∫ t : ℝ in Icc lo hi,
      ‖∑ i, c i * hermiteGenocchiIntegral (nodes i) order (fun s => g i s t)‖ ^ 2) ≤ B := by
  induction order generalizing nodes g with
  | zero => exact hbound (fun i => nodes i 0) (fun i => hnodes i 0 (by omega))
  | succ order ih =>
      let G : Fin n → ℝ → ℝ → ℂ := fun i x t =>
        weightedDerivativeAverage order (fun s => g i s t) (nodes i 0) x
      apply ih (fun i j => nodes i (j + 1)) G
        (fun i => continuous_weighted_group_average order (g i) (hg i) (nodes i 0))
        (fun i j hj => hnodes i (j + 1) (by omega))
      exact virtual_frequency_bound_weighted_average order g c hg L U (fun i => nodes i 0)
        (fun i => hnodes i 0 (by omega)) hbound

/-- Fixed-order grouped exponentials satisfy a dimension-uniform upper
window inequality when their group intervals are separated.  Nodes inside
each interval may collide or appear in any order. -/
theorem groupedExponential_fixedOrder_upper
    {n : ℕ} (nodes : Fin n → ℕ → ℝ) (order : ℕ) (L U : Fin n → ℝ)
    (hnodes : ∀ i j, j ≤ order → nodes i j ∈ Icc (L i) (U i))
    {a d : ℝ} (ha : 0 ≤ a) (hd : 0 < d)
    (hsep : ∀ i j, i ≠ j → ∀ x ∈ Icc (L i) (U i),
      ∀ y ∈ Icc (L j) (U j), d ≤ |x - y|) (c : Fin n → ℂ) :
    (∫ t : ℝ in Icc (-a) a, ‖∑ i, c i * groupedExponential (nodes i) order t‖ ^ 2) ≤
      (2 * Real.pi * a) ^ (2 * order) *
        (fourierIntervalLargeSieveConstant * (2 * a + d⁻¹)) * ∑ i, ‖c i‖ ^ 2 := by
  simp_rw [groupedExponential_eq_hermiteGenocchi]
  have hg : ∀ i : Fin n, Continuous (Function.uncurry
      (fun s t : ℝ => gramPhaseFrequencyMultiplier t ^ order * gramPhase s t)) := by
    intro i
    unfold Function.uncurry gramPhaseFrequencyMultiplier gramPhase
    fun_prop
  apply integral_hermiteGenocchi_synthesis_sq_le nodes order _ c hg L U hnodes
  intro x hx
  have hsep' : PairwiseFrequencySeparated x d :=
    fun i j hij => hsep i j hij (x i) (hx i) (x j) (hx j)
  have hfactor (t : ℝ) :
      (∑ i, c i * (gramPhaseFrequencyMultiplier t ^ order * gramPhase (x i) t)) =
        gramPhaseFrequencyMultiplier t ^ order * gramFourierPolynomial x c t := by
    simp only [gramFourierPolynomial, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hcontinuous : Continuous (fun t : ℝ =>
      ‖gramPhaseFrequencyMultiplier t ^ order * gramFourierPolynomial x c t‖ ^ 2) := by
    unfold gramPhaseFrequencyMultiplier gramFourierPolynomial gramPhase
    fun_prop
  have hpoly : IntegrableOn (fun t => ‖gramFourierPolynomial x c t‖ ^ 2) (Icc (-a) a) volume :=
    ((continuous_gramFourierPolynomial x c).norm.pow 2).integrableOn_Icc
  simp_rw [hfactor]
  calc
    _ ≤ ∫ t : ℝ in Icc (-a) a,
        (2 * Real.pi * a) ^ (2 * order) * ‖gramFourierPolynomial x c t‖ ^ 2 := by
      apply setIntegral_mono_on hcontinuous.integrableOn_Icc
        (hpoly.const_mul _) measurableSet_Icc
      intro t ht
      rw [norm_mul, norm_pow, norm_gramPhaseFrequencyMultiplier, mul_pow,
        ← pow_mul, mul_comm order 2]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact pow_le_pow_left₀ (by positivity)
        (mul_le_mul_of_nonneg_left (abs_le.mpr ht) (by positivity)) _
    _ = (2 * Real.pi * a) ^ (2 * order) *
        ∫ t : ℝ in Icc (-a) a, ‖gramFourierPolynomial x c t‖ ^ 2 := integral_const_mul _ _
    _ ≤ (2 * Real.pi * a) ^ (2 * order) *
        ((fourierIntervalLargeSieveConstant * (2 * a + d⁻¹)) * ∑ i, ‖c i‖ ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [sub_neg_eq_add, ← two_mul] using
        integral_norm_sq_le_interval_largeSieve hd (by linarith : -a ≤ a) x hsep' c
    _ = _ := by ring

/-- The squared norm of a sum of `q` complex vectors is at most `q` times
the sum of their squared norms. -/
theorem norm_sum_fin_sq_le {q : ℕ} (z : Fin q → ℂ) :
    ‖∑ j, z j‖ ^ 2 ≤ (q : ℝ) * ∑ j, ‖z j‖ ^ 2 := by
  calc
    _ ≤ (∑ j, ‖z j‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) _
    _ ≤ _ := by
      simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun j => ‖z j‖)

/-- Time continuity of an arbitrary finite-prefix grouped exponential,
including repeated nodes. -/
theorem continuous_groupedExponential (nodes : ℕ → ℝ) (order : ℕ) :
    Continuous (groupedExponential nodes order) := by
  change Continuous (fun t => groupedExponential nodes order t)
  simp only [groupedExponential_eq_hermiteGenocchi]
  apply continuous_hermiteGenocchiIntegral_parametric
  · intro j
    exact continuous_const
  · unfold Function.uncurry gramPhaseFrequencyMultiplier gramPhase
    fun_prop

/-- Simultaneously summing the first `q` divided-difference orders over
separated group intervals has an explicit upper constant independent of
the number of groups and every within-group gap.  In particular, all nodes
in any group may coincide. -/
theorem groupedExponential_rectangular_upper
    {n q : ℕ} (nodes : Fin n → ℕ → ℝ) (L U : Fin n → ℝ)
    (hnodes : ∀ i j, j < q → nodes i j ∈ Icc (L i) (U i))
    {a d : ℝ} (ha : 0 ≤ a) (hd : 0 < d)
    (hsep : ∀ i j, i ≠ j → ∀ x ∈ Icc (L i) (U i),
      ∀ y ∈ Icc (L j) (U j), d ≤ |x - y|) (c : Fin q → Fin n → ℂ) :
    (∫ t : ℝ in Icc (-a) a,
      ‖∑ j, ∑ i, c j i * groupedExponential (nodes i) j t‖ ^ 2) ≤
      (q : ℝ) * (max 1 (2 * Real.pi * a)) ^ (2 * q) *
        (fourierIntervalLargeSieveConstant * (2 * a + d⁻¹)) *
          ∑ j, ∑ i, ‖c j i‖ ^ 2 := by
  let P : Fin q → ℝ → ℂ := fun j t =>
    ∑ i, c j i * groupedExponential (nodes i) j t
  have hP (j : Fin q) : Continuous (P j) := by
    exact continuous_finsetSum _ (fun i _ =>
      continuous_const.mul (continuous_groupedExponential (nodes i) j))
  have hconstant : 0 ≤ fourierIntervalLargeSieveConstant * (2 * a + d⁻¹) := by
    have := fourierIntervalLargeSieveConstant_pos
    positivity
  have hbound (j : Fin q) :
      (∫ t : ℝ in Icc (-a) a, ‖P j t‖ ^ 2) ≤
        (max 1 (2 * Real.pi * a)) ^ (2 * q) *
          (fourierIntervalLargeSieveConstant * (2 * a + d⁻¹)) * ∑ i, ‖c j i‖ ^ 2 := by
    have hpow : (2 * Real.pi * a) ^ (2 * j.val) ≤
        (max 1 (2 * Real.pi * a)) ^ (2 * q) :=
      (pow_le_pow_left₀ (by positivity) (le_max_right _ _) _).trans
        (pow_le_pow_right₀ (le_max_left _ _) (by omega))
    exact (groupedExponential_fixedOrder_upper nodes j L U
      (fun i k hk => hnodes i k (by omega)) ha hd hsep (c j)).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpow hconstant)
          (Finset.sum_nonneg (fun i hi => sq_nonneg _)))
  calc
    _ ≤ ∫ t : ℝ in Icc (-a) a, (q : ℝ) * ∑ j, ‖P j t‖ ^ 2 := by
      apply integral_mono
        ((continuous_finsetSum _ (fun j _ => hP j)).norm.pow 2).integrableOn_Icc
        ((continuous_finsetSum _ (fun j _ => (hP j).norm.pow 2)).const_mul _).integrableOn_Icc
      intro t
      exact norm_sum_fin_sq_le (fun j => P j t)
    _ = (q : ℝ) * ∑ j, ∫ t : ℝ in Icc (-a) a, ‖P j t‖ ^ 2 := by
      rw [integral_const_mul, integral_finsetSum]
      intro j hj
      exact ((hP j).norm.pow 2).integrableOn_Icc
    _ ≤ (q : ℝ) * ∑ j, (max 1 (2 * Real.pi * a)) ^ (2 * q) *
        (fourierIntervalLargeSieveConstant * (2 * a + d⁻¹)) * ∑ i, ‖c j i‖ ^ 2 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ => hbound j)) (by positivity)
    _ = _ := by simp only [← Finset.mul_sum]; ring

private theorem sum_fin_zeroExtend {M : Type*} [AddCommMonoid M]
    {r q : ℕ} (hr : r ≤ q) (f : Fin r → M) :
    (∑ j : Fin q, if h : j.val < r then f ⟨j.val, h⟩ else 0) = ∑ j : Fin r, f j := by
  symm
  apply Fintype.sum_of_injective (Fin.castLE hr) (Fin.castLE_injective hr)
  · intro j hj
    have hnot : ¬j.val < r := by
      intro hlt
      exact hj ⟨⟨j.val, hlt⟩, rfl⟩
    simp [hnot]
  · intro j
    simp

/-- The actual finite family of initial-segment exponential divided
differences for nonempty groups of size at most `q` has a uniform upper
window bound.  There is no within-group separation hypothesis and no
dependence on the number of groups.  Zero extension in the order index is
proved explicitly, so different groups may have different sizes. -/
theorem groupedExponentialInitial_upper
    {n q : ℕ} (r : Fin n → ℕ) (hrpos : ∀ i, 0 < r i) (hrq : ∀ i, r i ≤ q)
    (nodes : (i : Fin n) → Fin (r i) → ℝ) (L U : Fin n → ℝ)
    (hnodes : ∀ i j, nodes i j ∈ Icc (L i) (U i))
    {a d : ℝ} (ha : 0 ≤ a) (hd : 0 < d)
    (hsep : ∀ i j, i ≠ j → ∀ x ∈ Icc (L i) (U i),
      ∀ y ∈ Icc (L j) (U j), d ≤ |x - y|)
    (c : (i : Fin n) → Fin (r i) → ℂ) :
    (∫ t : ℝ in Icc (-a) a,
      ‖∑ i, ∑ j, c i j * groupedExponentialInitial (nodes i) j t‖ ^ 2) ≤
      (q : ℝ) * (max 1 (2 * Real.pi * a)) ^ (2 * q) *
        (fourierIntervalLargeSieveConstant * (2 * a + d⁻¹)) *
          ∑ i, ∑ j, ‖c i j‖ ^ 2 := by
  let N : Fin n → ℕ → ℝ := fun i k =>
    if h : k < r i then nodes i ⟨k, h⟩ else nodes i ⟨0, hrpos i⟩
  let C : Fin q → Fin n → ℂ := fun j i =>
    if h : j.val < r i then c i ⟨j.val, h⟩ else 0
  have hN : ∀ i k, k < q → N i k ∈ Icc (L i) (U i) := by
    intro i k hk
    dsimp [N]
    split <;> apply hnodes
  have hprefix (i : Fin n) (j : Fin (r i)) (t : ℝ) :
      groupedExponential (N i) j t = groupedExponentialInitial (nodes i) j t := by
    apply analyticDividedDifference_congr_nodes
    intro k hk
    have hkr : k < r i := by omega
    simp [N, finiteNodeSequence, hkr]
  have hsum (t : ℝ) :
      (∑ j : Fin q, ∑ i, C j i * groupedExponential (N i) j t) =
        ∑ i, ∑ j : Fin (r i), c i j * groupedExponentialInitial (nodes i) j t := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    calc
      _ = ∑ j : Fin q, if h : j.val < r i then
          c i ⟨j.val, h⟩ * groupedExponentialInitial (nodes i) ⟨j.val, h⟩ t else 0 := by
        apply Finset.sum_congr rfl
        intro j hj
        by_cases h : j.val < r i
        · simp only [C, dite_eq_left h]
          rw [hprefix i ⟨j.val, h⟩ t]
        · simp [C, h]
      _ = _ := sum_fin_zeroExtend (hrq i)
        (fun j => c i j * groupedExponentialInitial (nodes i) j t)
  have hcoeff : (∑ j : Fin q, ∑ i, ‖C j i‖ ^ 2) = ∑ i, ∑ j : Fin (r i), ‖c i j‖ ^ 2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    calc
      _ = ∑ j : Fin q, if h : j.val < r i then ‖c i ⟨j.val, h⟩‖ ^ 2 else 0 := by
        apply Finset.sum_congr rfl
        intro j hj
        by_cases h : j.val < r i <;> simp [C, h]
      _ = _ := sum_fin_zeroExtend (hrq i) (fun j => ‖c i j‖ ^ 2)
  have h := groupedExponential_rectangular_upper N L U hN ha hd hsep C
  simpa only [hsum, hcoeff] using h

/-- Ordered group intervals with a gap of at least `d` satisfy the actual
initial-segment upper estimate.  The endpoint inequalities permit exact
inter-group gaps of `d`, and no condition is imposed on internal gaps. -/
theorem groupedExponentialInitial_upper_of_ordered_intervals
    {n q : ℕ} (r : Fin n → ℕ) (hrpos : ∀ i, 0 < r i) (hrq : ∀ i, r i ≤ q)
    (nodes : (i : Fin n) → Fin (r i) → ℝ) (L U : Fin n → ℝ)
    (hnodes : ∀ i j, nodes i j ∈ Icc (L i) (U i))
    {a d : ℝ} (ha : 0 ≤ a) (hd : 0 < d)
    (hordered : ∀ i j, i < j → U i + d ≤ L j)
    (c : (i : Fin n) → Fin (r i) → ℂ) :
    (∫ t : ℝ in Icc (-a) a,
      ‖∑ i, ∑ j, c i j * groupedExponentialInitial (nodes i) j t‖ ^ 2) ≤
      (q : ℝ) * (max 1 (2 * Real.pi * a)) ^ (2 * q) *
        (fourierIntervalLargeSieveConstant * (2 * a + d⁻¹)) *
          ∑ i, ∑ j, ‖c i j‖ ^ 2 := by
  apply groupedExponentialInitial_upper r hrpos hrq nodes L U hnodes ha hd _ c
  intro i j hij x hx y hy
  rcases lt_or_gt_of_ne hij with hij | hji
  · have hgap := hordered i j hij
    have hxy : d ≤ y - x := by linarith [hx.2, hy.1]
    exact hxy.trans (by rw [abs_sub_comm]; exact le_abs_self _)
  · have hgap := hordered j i hji
    have hxy : d ≤ x - y := by linarith [hy.2, hx.1]
    exact hxy.trans (le_abs_self _)

/-- A strictly positive uniform Bessel constant exists for the genuine
grouped exponentials.  Its parameters are only the maximum group size,
window radius, and inter-group separation; the number, positions, sizes,
and internal gaps of the individual groups are universally quantified. -/
theorem exists_groupedExponentialInitial_uniform_upper
    (q : ℕ) {a d : ℝ} (ha : 0 ≤ a) (hd : 0 < d) :
    ∃ B : ℝ, 0 < B ∧ ∀ (n : ℕ) (r : Fin n → ℕ),
      (∀ i, 0 < r i) → (∀ i, r i ≤ q) →
      ∀ (nodes : (i : Fin n) → Fin (r i) → ℝ) (L U : Fin n → ℝ),
      (∀ i j, nodes i j ∈ Icc (L i) (U i)) →
      (∀ i j, i ≠ j → ∀ x ∈ Icc (L i) (U i),
        ∀ y ∈ Icc (L j) (U j), d ≤ |x - y|) →
      ∀ c : (i : Fin n) → Fin (r i) → ℂ,
        (∫ t : ℝ in Icc (-a) a,
          ‖∑ i, ∑ j, c i j * groupedExponentialInitial (nodes i) j t‖ ^ 2) ≤
            B * ∑ i, ∑ j, ‖c i j‖ ^ 2 := by
  let B : ℝ := ((q : ℝ) + 1) * (max 1 (2 * Real.pi * a)) ^ (2 * q) *
    (fourierIntervalLargeSieveConstant * (2 * a + d⁻¹))
  have hlarge := fourierIntervalLargeSieveConstant_pos
  have hmax : 0 < max 1 (2 * Real.pi * a) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨B, hB, ?_⟩
  intro n r hrpos hrq nodes L U hnodes hsep c
  apply (groupedExponentialInitial_upper r hrpos hrq nodes L U hnodes ha hd hsep c).trans
  apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun i hi =>
    Finset.sum_nonneg (fun j hj => sq_nonneg _)))
  dsimp [B]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)

end

end MeyerGeneralProblem
