module

public import MeyerGeneralProblem.Cardinal.Adaptive.FiniteFourierProducts

@[expose] public section

/-! # Uniform inverse-polynomial bounds for the full Fourier translation tail -/

namespace MeyerGeneralProblem.Adaptive
noncomputable section
open scoped BigOperators

private theorem one_add_sum_le_product (q : ℕ) (a : Fin q → ℝ) (ha : ∀ j, 0 ≤ a j) :
    1+∑ j, a j ≤ ∏ j, (1+a j) := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Fin.sum_univ_succ, Fin.prod_univ_succ]
    have hi := ih (fun j => a j.succ) (fun j => ha j.succ)
    have hp := mul_nonneg (ha 0) (Finset.sum_nonneg (s := Finset.univ) (fun (j : Fin q) _ => ha j.succ))
    have hm := mul_le_mul_of_nonneg_left hi (by linarith [ha 0] : 0 ≤ 1+a 0)
    nlinarith

/-- Every inverse polynomial tail rate follows from the next actual coefficient
moment, uniformly over the full compact scale tuple. -/
theorem exists_finite_product_translation_tail_bound (q m r : ℕ) (c : Fin q → ℤ → ℂ)
    (h : ∀ j, Summable (fun n : ℤ => (1+|(n:ℝ)|)^(2*m+r) * ‖c j n‖)) :
    ∃ B : ℝ, 0 < B ∧ ∀ (s : Fin q → ℝ), (∀ j, |s j| ≤ 2) → ∀ L : ℕ,
      ‖∑' k : {k : Fin q → ℤ // (L:ℝ) < ∑ j, |(k j:ℝ)|},
        (∏ j, c j (k.val j)) • nativeTranslation m (∑ j, s j*(k.val j:ℝ))‖ ≤
          B / (1+(L:ℝ))^r := by
  obtain ⟨C,hC,hbound⟩ := exists_nativeTranslation_norm_bound m
  let W (k : Fin q → ℤ) := ∏ j, (1+|(k j:ℝ)|)^(2*m+r) * ‖c j (k j)‖
  have hW : Summable W := summable_fin_coefficient_moments q c (2*m+r) h
  have hWn (k) : 0 ≤ W k := Finset.prod_nonneg (fun j _ => by positivity)
  let B := C*2^(q*(2*m))*(∑' k, W k)+1
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨B,hB,fun s hs L => ?_⟩
  have hden : 0 < (1+(L:ℝ))^r := by positivity
  let K := {k : Fin q → ℤ // (L:ℝ) < ∑ j, |(k j:ℝ)|}
  have hsub : Summable (fun k : K => W k.val) := hW.subtype _
  have hpoint (k : K) :
      ‖(∏ j, c j (k.val j)) • nativeTranslation m (∑ j, s j*(k.val j:ℝ))‖ ≤
        (C*2^(q*(2*m))/(1+(L:ℝ))^r) * W k.val := by
    have hp : (1+(L:ℝ))^r ≤ ∏ j, (1+|(k.val j:ℝ)|)^r := by
      rw [Finset.prod_pow]
      gcongr
      exact (by linarith [k.property] : 1+(L:ℝ) ≤ 1+∑ j, |(k.val j:ℝ)|).trans
        (one_add_sum_le_product q _ (fun j => abs_nonneg _))
    have hnorm : ‖(∏ j, c j (k.val j)) • nativeTranslation m (∑ j, s j*(k.val j:ℝ))‖ ≤
        C * (2^(q*(2*m)) * ∏ j, (1+|(k.val j:ℝ)|)^(2*m) * ‖c j (k.val j)‖) := by
      rw [norm_smul]
      calc
        _ ≤ ‖∏ j, c j (k.val j)‖ * (C*(1+|∑ j, s j*(k.val j:ℝ)|)^(2*m)) :=
          mul_le_mul_of_nonneg_left (hbound _) (norm_nonneg _)
        _ = C*((1+|∑ j, s j*(k.val j:ℝ)|)^(2*m)*‖∏ j, c j (k.val j)‖) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (finite_frequency_moment_le q c s hs (2*m) k.val) hC.le
    rw [div_mul_eq_mul_div, le_div_iff₀ hden]
    calc
      _ ≤ (C * (2^(q*(2*m)) * ∏ j, (1+|(k.val j:ℝ)|)^(2*m) * ‖c j (k.val j)‖)) *
          (∏ j, (1+|(k.val j:ℝ)|)^r) :=
        mul_le_mul hnorm hp (le_of_lt hden) (by positivity)
      _ = _ := by
        dsimp [W]
        simp only [pow_add, Finset.prod_mul_distrib]
        ring
  have hn := tsum_of_norm_bounded
    (hsub.hasSum.mul_left (C*2^(q*(2*m))/(1+(L:ℝ))^r)) hpoint
  apply hn.trans
  have ht : (∑' k : K, W k.val) ≤ ∑' k, W k := by
    exact Summable.tsum_subtype_le W _ hWn hW
  calc
    _ ≤ (C*2^(q*(2*m))/(1+(L:ℝ))^r) * (∑' k, W k) := by gcongr
    _ ≤ B/(1+(L:ℝ))^r := by
      rw [div_mul_eq_mul_div]
      apply div_le_div_of_nonneg_right _ hden.le
      dsimp [B]
      linarith
end
end MeyerGeneralProblem.Adaptive
