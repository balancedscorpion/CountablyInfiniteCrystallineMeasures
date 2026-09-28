module

public import MeyerGeneralProblem.Cardinal.Adaptive.NativeCutoffBounds
public import MeyerGeneralProblem.Cardinal.Adaptive.RankArithmetic

@[expose] public section

/-! # Fixed-regularity translated-test tails in original Hermite norms -/

namespace MeyerGeneralProblem.Adaptive
noncomputable section
open MeasureTheory Filter
open scoped Topology FourierTransform

private theorem iteratedDeriv_tsupport_subset (f : ℝ → ℂ) (n : ℕ) :
    tsupport (iteratedDeriv n f) ⊆ tsupport f := by
  induction n with
  | zero => simpa only [iteratedDeriv_zero] using (Set.Subset.rfl : tsupport f ⊆ tsupport f)
  | succ n ih => rw [iteratedDeriv_succ]; exact tsupport_deriv_subset.trans ih

/-- Compact tests with only 2p bounded derivatives have bounded original H_p
norm, uniformly over all such tests. No higher Schwartz seminorm is assumed. -/
theorem exists_compact_finite_regularity_native_bound (p : ℕ) (H : ℝ) (hH : 0 ≤ H) :
    ∃ B : ℝ, 0 < B ∧ ∀ f : SchwartzMap ℝ ℂ,
      tsupport f ⊆ Set.Icc (-H) H →
      (∀ r ≤ 2*p, ∀ x, ‖iteratedDeriv r (f : ℝ → ℂ) x‖ ≤ 1) →
      ‖schwartzToHermiteScale p f‖ ≤ B := by
  classical
  obtain ⟨C,hC,hb⟩ := exists_hermite_norm_le_mixedL2Sum p
  let g := scaledCompactSchwartzCutoff ⌈H⌉₊
  let E : ℝ := ∑ z ∈ mixedIndices (2*p), (1+H)^z.1*‖g.toLp 2 volume‖
  have hE : 0 ≤ E := by dsimp [E]; positivity
  refine ⟨C*E+1,by positivity,fun f hs hf => ?_⟩
  have hterm (j k : ℕ) (hjk : j+k ≤ 2*p) :
      ‖(mixedSchwartz j k f).toLp 2 volume‖ ≤ (1+H)^j*‖g.toLp 2 volume‖ := by
    have hn := schwartz_norm_toLp_le_weighted_sum {()} (fun _ : Unit => (1+H)^j)
      (fun _ _ => by positivity) (mixedSchwartz j k f) (fun _ => g) (fun x => ?_)
    · simpa only [Finset.sum_singleton] using hn
    simp only [Finset.sum_singleton,mixedSchwartz_apply,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs]
    by_cases hx : x ∈ Set.Icc (-H) H
    · have hab : |x| ≤ H := abs_le.mpr hx
      have hg : g x = 1 := scaledCompactSchwartzCutoff_eq_one _
        (hab.trans ((Nat.le_ceil H).trans (by linarith)))
      rw [hg,norm_one,mul_one]
      have hp : |x|^j ≤ (1+H)^j := pow_le_pow_left₀ (abs_nonneg x) (by linarith) _
      exact (mul_le_mul hp (hf k (by omega) x) (norm_nonneg _) (by positivity)).trans_eq (mul_one _)
    · have hnot : x ∉ tsupport (iteratedDeriv k (f : ℝ → ℂ)) := fun h =>
        hx (hs ((iteratedDeriv_tsupport_subset (f : ℝ → ℂ) k) h))
      rw [image_eq_zero_of_notMem_tsupport hnot,norm_zero,mul_zero]
      positivity
  have hm : mixedL2Sum (2*p) f ≤ E := by
    apply Finset.sum_le_sum
    intro z hz
    exact hterm z.1 z.2 ((mem_mixedIndices _ _ _).mp hz)
  exact (hb f).trans ((mul_le_mul_of_nonneg_left hm hC.le).trans (by linarith))

/-- A fixed compact partition factor and a bounded translation preserve the
native bound from finitely many test derivatives, for either Fourier sign. -/
theorem exists_translated_compact_fourier_native_bound (q : ℕ) (ζ : SchwartzMap ℝ ℂ)
    (H S : ℝ) (hH : 0 ≤ H) (hS : 0 ≤ S) :
    ∃ B : ℝ, 0 < B ∧ ∀ f : SchwartzMap ℝ ℂ,
      tsupport f ⊆ Set.Icc (-H) H →
      (∀ r ≤ 2*q, ∀ x, ‖iteratedDeriv r (f : ℝ → ℂ) x‖ ≤ 1) →
      ∀ h : ℝ, |h| ≤ S → ∀ inverse : Bool,
      let v := combSchwartzTranslation h (SchwartzMap.smulLeftCLM ℂ ζ f)
      ‖schwartzToHermiteScale q (if inverse then 𝓕⁻ v else 𝓕 v)‖ ≤ B := by
  obtain ⟨F,hF,hfb⟩ := exists_compact_finite_regularity_native_bound q H hH
  let A : ℝ := ∑ r ∈ Finset.range (2*q+1), SchwartzMap.seminorm ℂ 0 r ζ
  have hA : 0 ≤ A := Finset.sum_nonneg (fun r _ => apply_nonneg _ _)
  obtain ⟨C,hC,hcb⟩ := exists_native_bounded_multiplier_bound q A hA
  have hcζ (r : ℕ) (hr : r ≤ 2*q) (x : ℝ) : ‖iteratedDeriv r (ζ : ℝ → ℂ) x‖ ≤ A := by
    have h := SchwartzMap.le_seminorm' ℂ 0 r ζ x
    simp only [pow_zero,one_mul] at h
    exact h.trans (Finset.single_le_sum (fun r _ => apply_nonneg _ _) (Finset.mem_range.mpr (by omega)))
  obtain ⟨T,hT,htb⟩ := exists_hermite_translation_bound q
  refine ⟨T*(1+S)^(2*q)*(C*F)+1,by positivity,fun f hs hf h hh inverse => ?_⟩
  have hu := hcb ζ ζ.hasTemperateGrowth hcζ f
  have hf' := hfb f hs hf
  have ht := htb h (SchwartzMap.smulLeftCLM ℂ ζ f)
  have hb : ‖schwartzToHermiteScale q (combSchwartzTranslation h (SchwartzMap.smulLeftCLM ℂ ζ f))‖ ≤
      T*(1+S)^(2*q)*(C*F) := by
    apply ht.trans
    apply mul_le_mul _ (hu.trans (mul_le_mul_of_nonneg_left hf' hC.le)) (norm_nonneg _) (by positivity)
    gcongr
  cases inverse <;> simp only [Bool.false_eq_true,ite_false,ite_true]
  · rw [schwartzToHermiteScale_fourier_norm]
    exact hb.trans (by linarith)
  · rw [schwartzToHermiteScale_fourierInv_norm]
    exact hb.trans (by linarith)

/-- Fixed finite regularity suffices for the inverse-radius Fourier tail bound.
The constants may depend on stage support, partition and translation bounds;
the derivative order2(p+1) depends only on the output native order. -/
theorem exists_translated_test_tail_bound (p : ℕ) (ζ : SchwartzMap ℝ ℂ)
    (H S : ℝ) (hH : 0 ≤ H) (hS : 0 ≤ S) :
    ∃ D : ℝ, 0 < D ∧ ∀ N : ℕ, ∀ f : SchwartzMap ℝ ℂ,
      tsupport f ⊆ Set.Icc (-H) H →
      (∀ r ≤ 2*(p+1), ∀ x, ‖iteratedDeriv r (f : ℝ → ℂ) x‖ ≤ 1) →
      ∀ h : ℝ, |h| ≤ S → ∀ inverse : Bool,
      let v := combSchwartzTranslation h (SchwartzMap.smulLeftCLM ℂ ζ f)
      let F := if inverse then 𝓕⁻ v else 𝓕 v
      ‖schwartzToHermiteScale p (F-compactSchwartzApproximation N F)‖ ≤
        compactSchwartzCutoffScale N*D := by
  obtain ⟨B,hB,hb⟩ := exists_translated_compact_fourier_native_bound (p+1) ζ H S hH hS
  obtain ⟨C,hC,hc⟩ := exists_native_cutoff_error_bound p
  refine ⟨C*B,mul_pos hC hB,fun N f hs hf h hh inverse => ?_⟩
  exact (hc N _).trans ((mul_le_mul_of_nonneg_left (hb f hs hf h hh inverse)
    (mul_nonneg (compactSchwartzCutoffScale_pos N).le hC.le)).trans_eq (by ring))

/-- Budget B uses the prescribed Kp=testOrder p derivatives at each native
order. A finite partition and every bounded translation share one cutoff;
no stage-dependent derivative order enters the input class. -/
theorem exists_fixed_regularity_translated_budget (M J : ℕ)
    (ζ : Fin J → SchwartzMap ℝ ℂ) (H S ε : ℝ)
    (hH : 0 ≤ H) (hS : 0 ≤ S) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p ≤ M, ∀ j : Fin J,
      ∀ f : SchwartzMap ℝ ℂ, tsupport f ⊆ Set.Icc (-H) H →
      (∀ r ≤ testOrder p, ∀ x, ‖iteratedDeriv r (f : ℝ → ℂ) x‖ ≤ 1) →
      ∀ h : ℝ, |h| ≤ S → ∀ inverse : Bool,
      let v := combSchwartzTranslation h (SchwartzMap.smulLeftCLM ℂ (ζ j) f)
      let F := if inverse then 𝓕⁻ v else 𝓕 v
      ‖schwartzToHermiteScale (6*p) (F-compactSchwartzApproximation N F)‖ < ε/(1+(J:ℝ)) := by
  have hevent (p : Fin (M+1)) (j : Fin J) :
      ∀ᶠ N : ℕ in atTop, ∀ f : SchwartzMap ℝ ℂ,
        tsupport f ⊆ Set.Icc (-H) H →
        (∀ r ≤ testOrder p, ∀ x, ‖iteratedDeriv r (f : ℝ → ℂ) x‖ ≤ 1) →
        ∀ h : ℝ, |h| ≤ S → ∀ inverse : Bool,
        let v := combSchwartzTranslation h (SchwartzMap.smulLeftCLM ℂ (ζ j) f)
        let F := if inverse then 𝓕⁻ v else 𝓕 v
        ‖schwartzToHermiteScale (6*p.val) (F-compactSchwartzApproximation N F)‖ < ε/(1+(J:ℝ)) := by
    obtain ⟨D,hD,hb⟩ := exists_translated_test_tail_bound (6*p.val) (ζ j) H S hH hS
    have ht : Tendsto (fun N => compactSchwartzCutoffScale N*D) atTop (nhds 0) := by
      simpa only [zero_mul] using compactSchwartzCutoffScale_tendsto.mul_const D
    filter_upwards [ht.eventually (eventually_lt_nhds (by positivity : 0 < ε/(1+(J:ℝ))))] with N hN
    intro f hs hf h hh inverse
    exact (hb N f hs (fun r hr => hf r (by have := sixfold_order_margin p.val; omega)) h hh inverse).trans_lt hN
  obtain ⟨N₀,hN⟩ := eventually_atTop.mp
    (eventually_all.mpr (fun p => eventually_all.mpr (hevent p)))
  exact ⟨N₀,fun N hNN p hp => hN N hNN ⟨p,by omega⟩⟩

end
end MeyerGeneralProblem.Adaptive
