module

public import MeyerGeneralProblem.Cardinal.Adaptive.FiniteFourierProducts
public import MeyerGeneralProblem.Cardinal.Adaptive.NativeMultipliers

@[expose] public section

/-! # Uniform finite-stage multiplier and spatial-tail bounds in original norms -/

namespace MeyerGeneralProblem.Adaptive
noncomputable section
open Function Filter
open scoped BigOperators ContDiff Topology

private theorem periodic_derivative_bound (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
    (hp : Periodic g 1) (n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖iteratedDeriv n g x‖ ≤ C := by
  have hpn : Periodic (iteratedDeriv n g) 1 := by
    intro x
    have he : (fun y => g (y+1)) = g := funext hp
    have h := congrFun (iteratedDeriv_comp_add_const n g 1) x
    rw [he] at h
    exact h.symm
  obtain ⟨C,hC,hb⟩ := (hpn.isBounded_of_continuous (by norm_num)
    (hg.continuous_iteratedDeriv n (by simp))).exists_pos_norm_le
  exact ⟨C,hC.le,fun x => hb _ ⟨x,rfl⟩⟩

private theorem scaled_periodic_derivative_bound (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
    (hp : Periodic g 1) (n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℝ, |a| ≤ 2 → ∀ x,
      ‖iteratedDeriv n (fun y => g (a*y)) x‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ := periodic_derivative_bound g hg hp n
  refine ⟨2^n*C,by positivity,fun a ha x => ?_⟩
  have hd := congrFun (iteratedDeriv_comp_const_smul (n := n) (hg.of_le (by simp)) a) x
  rw [hd, norm_smul, Real.norm_eq_abs, abs_pow]
  exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) ha n) (hb _) (norm_nonneg _) (by positivity)

/-- All derivatives of every finite-stage product are bounded before its
compact scale tuple is selected. -/
theorem finite_periodic_product_derivative_bounds (q : ℕ) (g : Fin q → ℝ → ℂ)
    (hg : ∀ j, ContDiff ℝ ∞ (g j)) (hp : ∀ j, Periodic (g j) 1) :
    ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : Fin q → ℝ), (∀ j, |s j| ≤ 2) → ∀ x,
      ‖iteratedDeriv n (fun y => ∏ j, g j (s j*y)) x‖ ≤ C := by
  induction q with
  | zero =>
    intro n
    refine ⟨1,by norm_num,fun s hs x => ?_⟩
    have he : (fun y : ℝ => ∏ j : Fin 0, g j (s j*y)) = (fun _ : ℝ => (1:ℂ)) := by funext y; simp
    rw [he]
    cases n <;> simp [iteratedDeriv_const]
  | succ q ih =>
    intro n
    choose A hA hAb using (fun k => scaled_periodic_derivative_bound (g 0) (hg 0) (hp 0) k)
    choose B hB hBb using ih (fun j => g j.succ) (fun j => hg j.succ) (fun j => hp j.succ)
    refine ⟨∑ k ∈ Finset.range (n+1), (n.choose k:ℝ)*A k*B (n-k),
      Finset.sum_nonneg (fun k _ => mul_nonneg (mul_nonneg (by positivity) (hA k)) (hB (n-k))),fun s hs x => ?_⟩
    have hf : ContDiff ℝ ∞ (fun y => g 0 (s 0*y)) :=
      (hg 0).comp (contDiff_const.mul contDiff_id)
    have ht : ContDiff ℝ ∞ (fun y => ∏ j : Fin q, g j.succ (s j.succ*y)) := by
      fun_prop
    simp only [Fin.prod_univ_succ]
    change ‖iteratedDeriv n ((fun y => g 0 (s 0*y)) * (fun y => ∏ j : Fin q, g j.succ (s j.succ*y))) x‖ ≤ _
    rw [iteratedDeriv_mul (hf.of_le (by simp)).contDiffAt (ht.of_le (by simp)).contDiffAt]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro k hk
    simp only [norm_mul, Complex.norm_natCast]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hAb k (s 0) (hs 0) x) (by positivity))
      (hBb (n-k) (fun j => s j.succ) (fun j => hs j.succ) x)
      (norm_nonneg _) (mul_nonneg (by positivity) (hA k))

/-- A single same-order native multiplier bound controls all compact scale
choices of a fixed finite product. -/
theorem exists_finite_periodic_product_multiplier_bound (q p : ℕ)
    (g : Fin q → ℝ → ℂ) (hg : ∀ j, ContDiff ℝ ∞ (g j))
    (hp : ∀ j, Periodic (g j) 1) :
    ∃ B : ℝ, 0 < B ∧ ∀ (s : Fin q → ℝ), (∀ j, |s j| ≤ 2) →
      ∀ f : SchwartzMap ℝ ℂ,
        ‖schwartzToHermiteScale p (SchwartzMap.smulLeftCLM ℂ (fun x => ∏ j, g j (s j*x)) f)‖ ≤
          B*‖schwartzToHermiteScale p f‖ := by
  choose C hC hb using finite_periodic_product_derivative_bounds q g hg hp
  let A := ∑ r ∈ Finset.range (2*p+1), C r
  have hA : 0 ≤ A := Finset.sum_nonneg (fun r _ => hC r)
  obtain ⟨B,hB,hbound⟩ := exists_native_bounded_multiplier_bound p A hA
  refine ⟨B,hB,fun s hs f => hbound _ (finite_periodic_product_hasTemperateGrowth q g hg hp s) ?_ f⟩
  intro r hr x
  exact (hb r s hs x).trans
    (Finset.single_le_sum (fun r _ => hC r) (Finset.mem_range.mpr (by omega)))

/-- Uniform spatial tail budget at every fixed stage and native order. The
cutoff threshold is chosen before the compact scale tuple. -/
theorem finite_periodic_product_spatial_tail (q p : ℕ)
    (g : Fin q → ℝ → ℂ) (hg : ∀ j, ContDiff ℝ ∞ (g j))
    (hp : ∀ j, Periodic (g j) 1) (f : SchwartzMap ℝ ℂ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (s : Fin q → ℝ), (∀ j, |s j| ≤ 2) →
      ‖schwartzToHermiteScale p (SchwartzMap.smulLeftCLM ℂ (fun x => ∏ j, g j (s j*x))
        (f-compactSchwartzApproximation N f))‖ < ε := by
  obtain ⟨B,hB,hbound⟩ := exists_finite_periodic_product_multiplier_bound q p g hg hp
  have ht : Tendsto (fun N => ‖schwartzToHermiteScale p (f-compactSchwartzApproximation N f)‖)
      atTop (nhds 0) := by
    have h := (((schwartzToHermiteScale p).continuous.tendsto (f-f)).comp
      (tendsto_const_nhds.sub (compactSchwartzApproximation_tendsto f))).norm
    simpa only [sub_self, map_zero, norm_zero, Function.comp_apply] using h
  obtain ⟨N₀,hN⟩ := Filter.eventually_atTop.mp (ht.eventually (eventually_lt_nhds (div_pos hε hB)))
  refine ⟨N₀,fun N hNN s hs => (hbound s hs _).trans_lt ?_⟩
  have h := mul_lt_mul_of_pos_left (hN N hNN) hB
  simpa only [mul_div_cancel₀ _ hB.ne'] using h
end
end MeyerGeneralProblem.Adaptive
