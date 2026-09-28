module

public import MeyerGeneralProblem.Cardinal.Adaptive.RapidInterpolationGrid
public import MeyerGeneralProblem.Cardinal.Adaptive.ShrinkingNewtonWeights

@[expose] public section

/-! # Convergence of the actual rapid interpolation majorant

The scalar estimate uses the full maximum of the two Newton indices and the
source threshold b^L>4. It makes no assertion that moment decay itself holds.
-/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open Set

/-- Exact tail ratio of the rapid distance products in the admission majorant. -/
theorem rapidAdmission_product_ratio (c d b : ℝ) (_hc : 0 < c) (hb : 1 < b) (L m : ℕ) :
    shrinkingNewtonWeight (shrinkingRapidDistance c d b) (m+L) /
      shrinkingNewtonWeight (shrinkingRapidDistance c d b) m ^ 4 =
    c^L*(c/c^4)^m*Real.exp (-3*d*b/(b-1)-(d*b/(b-1)*(b^L-4))*b^m) := by
  rw [shrinkingRapidDistance_product c d b (ne_of_gt hb),shrinkingRapidDistance_product c d b (ne_of_gt hb)]
  rw [mul_pow,mul_div_mul_comm,← Real.exp_nat_mul,← Real.exp_sub]
  have he : -d*b*(b^(m+L)-1)/(b-1)-(4:ℝ)*(-d*b*(b^m-1)/(b-1)) =
      -3*d*b/(b-1)-(d*b/(b-1)*(b^L-4))*b^m := by
    rw [pow_add]
    ring
  norm_num only [Nat.cast_ofNat]
  rw [he]
  congr 1
  rw [pow_add,div_pow,pow_right_comm]
  ring

/-- The exact product-ratio majorant is summable at the strict source threshold. -/
theorem summable_rapidAdmission_product_ratio (c d b K : ℝ) (hc : 0 < c) (hd : 0 < d)
    (hb : 1 < b) (hK : 0 ≤ K) (L : ℕ) (hL : 4 < b^L) :
    Summable (fun m : ℕ => ((m:ℝ)+1)*K^m*
      (shrinkingNewtonWeight (shrinkingRapidDistance c d b) m /
        shrinkingNewtonWeight (shrinkingRapidDistance c d b) (m-L)^4)) := by
  have hD : 0 < d*b/(b-1)*(b^L-4) := by positivity
  have hs := (summable_polynomial_geometric_superexponential 1 (K*(c/c^4))
    (-3*d*b/(b-1)) (d*b/(b-1)*(b^L-4)) b (by positivity) hD hb).mul_left
      (((L:ℝ)+1)*K^L*c^L)
  apply (summable_nat_add_iff L).mp
  apply hs.of_norm_bounded
  intro m
  have hw (i : ℕ) : 0 < shrinkingNewtonWeight (shrinkingRapidDistance c d b) i := by
    apply Finset.prod_pos
    intro a _
    dsimp [shrinkingRapidDistance]
    positivity
  have hwm := hw (m+L)
  have hwq := hw (m+L-L)
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity),Nat.add_sub_cancel,
    rapidAdmission_product_ratio c d b hc hb L m]
  have hpoly : ((m+L:ℕ):ℝ)+1 ≤ ((L:ℝ)+1)*((m:ℝ)+1) := by push_cast; nlinarith
  calc
    _ ≤ (((L:ℝ)+1)*((m:ℝ)+1))*K^(m+L)*
        (c^L*(c/c^4)^m*Real.exp (-3*d*b/(b-1)-(d*b/(b-1)*(b^L-4))*b^m)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpoly (by positivity)) (by positivity)
    _ = _ := by rw [pow_add,mul_pow,pow_one]; ring

/-- Characteristic denominator product for the actual infinite rapid sequence. -/
def rapidCharacteristicProduct (P R q : ℕ) : ℝ :=
  ∏ j ∈ Finset.range q, parityNewtonCoordinate (rapidDistance P R (j+1))

/-- The actual distance law is exactly the positive-index exponential law. -/
theorem rapidDistance_eq_shrinking (P R : ℕ) :
    rapidDistance P R=shrinkingRapidDistance (1/16) (rapidDecay P R) (rapidBase P) := rfl

/-- Literal characteristic nodes dominate the squared actual distances. -/
theorem rapidDistance_sq_le_characteristic {P R : ℕ} (hP : 1 ≤ P) (hR : 1 ≤ R) (j : ℕ) :
    rapidDistance P R j^2 ≤ parityNewtonCoordinate (rapidDistance P R j) := by
  have hd := rapidDistance_bounds hP hR j
  have hs := sine_phase_bounds _ hd.1.le hd.2
  rw [parityNewtonCoordinate_eq]
  have hn : 0 ≤ Real.sin (Real.pi*rapidDistance P R j) := by linarith [hs.1]
  nlinarith

/-- The actual product denominator is positive at every finite order. -/
theorem rapidCharacteristicProduct_pos {P R : ℕ} (hP : 1 ≤ P) (hR : 1 ≤ R) (q : ℕ) :
    0 < rapidCharacteristicProduct P R q := by
  apply Finset.prod_pos
  intro j _
  exact lt_of_lt_of_le (sq_pos_of_pos (rapidDistance_bounds hP hR (j+1)).1)
    (rapidDistance_sq_le_characteristic hP hR (j+1))

/-- Squaring the actual denominator product pays the fourth power of the
corresponding distance product, without omitting any initial factor. -/
theorem rapid_distance_product_fourth_le {P R : ℕ} (hP : 1 ≤ P) (hR : 1 ≤ R) (q : ℕ) :
    shrinkingNewtonWeight (rapidDistance P R) q ^4 ≤ rapidCharacteristicProduct P R q ^2 := by
  have hsq : shrinkingNewtonWeight (rapidDistance P R) q ^2 ≤ rapidCharacteristicProduct P R q := by
    rw [shrinkingNewtonWeight,← Finset.prod_pow]
    exact Finset.prod_le_prod₀ (fun j _ => sq_nonneg _) (fun j _ => rapidDistance_sq_le_characteristic hP hR (j+1))
  have hp := rapidCharacteristicProduct_pos hP hR q
  nlinarith [sq_nonneg (shrinkingNewtonWeight (rapidDistance P R) q ^2)]

/-- The complete maximum-index numerical majorant from rapid admission is summable.
The hypothesis is exactly b^L>4, and the coefficient K may be any fixed nonnegative number. -/
theorem summable_rapidAdmission_majorant {P R : ℕ} (hP : 1 ≤ P) (hR : 1 ≤ R)
    (K : ℝ) (hK : 0 ≤ K) (L : ℕ) (hL : 4 < rapidBase P^L) :
    Summable (fun m : ℕ => (2*(m:ℝ)+1)*K^m*shrinkingNewtonWeight (rapidDistance P R) m /
      rapidCharacteristicProduct P R (m-L)^2) := by
  have hs := (summable_rapidAdmission_product_ratio (1/16) (rapidDecay P R) (rapidBase P) K
    (by norm_num) (rapidDecay_pos hP hR) (rapidBase_one_lt hP) hK L hL).mul_left 2
  rw [← rapidDistance_eq_shrinking] at hs
  apply hs.of_norm_bounded
  intro m
  have hw (i : ℕ) : 0 < shrinkingNewtonWeight (rapidDistance P R) i := by
    exact Finset.prod_pos (fun j _ => (rapidDistance_bounds hP hR (j+1)).1)
  have hp := rapidCharacteristicProduct_pos hP hR (m-L)
  have hwm := hw m
  have hwq := hw (m-L)
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  calc
    _ ≤ (2*(m:ℝ)+1)*K^m*shrinkingNewtonWeight (rapidDistance P R) m /
        shrinkingNewtonWeight (rapidDistance P R) (m-L)^4 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (rapid_distance_product_fourth_le hP hR (m-L))
    _ ≤ _ := by
      have hpoly : 2*(m:ℝ)+1 ≤ 2*((m:ℝ)+1) := by linarith
      have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpoly (pow_nonneg hK m))
        (div_nonneg (hw m).le (by positivity : 0 ≤ shrinkingNewtonWeight (rapidDistance P R) (m-L)^4))
      simpa only [div_eq_mul_inv,mul_assoc] using hh

/-- Every denominator appearing below a finite interpolation cap is the same
initial product from the actual infinite sequence. The endpoint is not counted. -/
theorem rapidGrid_prefix_product_eq (P R k q : ℕ) (hq : q ≤ k) :
    (∏ j ∈ Finset.range q, finiteNodeSequence
      (fun a => parityNewtonCoordinate (rapidInterpolationPhase P R k a)) j) =
    rapidCharacteristicProduct P R q := by
  apply Finset.prod_congr rfl
  intro j hj
  have hjq := Finset.mem_range.mp hj
  have hjk : j<k := by omega
  simp only [finiteNodeSequence,dite_eq_left (show j<k+1 by omega),
    rapidInterpolationPhase,rapidFiniteDistance,ite_eq_left hjk]

/-- Each actual characteristic node lies below one. -/
theorem rapid_characteristic_le_one {P R : ℕ} (hP : 1 ≤ P) (hR : 1 ≤ R) (j : ℕ) :
    parityNewtonCoordinate (rapidDistance P R j) ≤ 1 := by
  have hd := rapidDistance_bounds hP hR j
  have hs := sine_phase_bounds _ hd.1.le hd.2
  have hsin : 0 ≤ Real.sin (Real.pi*rapidDistance P R j) := by linarith [hs.1]
  rw [parityNewtonCoordinate_eq]
  nlinarith

/-- Adding a characteristic denominator factor can only decrease the product. -/
theorem rapidCharacteristicProduct_antitone {P R : ℕ} (hP : 1 ≤ P) (hR : 1 ≤ R) :
    Antitone (rapidCharacteristicProduct P R) := by
  apply antitone_nat_of_succ_le
  intro q
  rw [rapidCharacteristicProduct,Finset.prod_range_succ]
  have hp := (rapidCharacteristicProduct_pos hP hR q).le
  have hh := mul_le_mul_of_nonneg_left (rapid_characteristic_le_one hP hR (q+1)) hp
  simpa only [rapidCharacteristicProduct,mul_one] using hh

/-- The denominator with the maximum index controls both tensor arms at once. -/
theorem rapidCharacteristicProduct_max_le {P R : ℕ} (hP : 1 ≤ P) (hR : 1 ≤ R) (i j L : ℕ) :
    rapidCharacteristicProduct P R (max i j-L)^2 ≤
      rapidCharacteristicProduct P R (i-L)*rapidCharacteristicProduct P R (j-L) := by
  have h1 := rapidCharacteristicProduct_antitone hP hR (Nat.sub_le_sub_right (le_max_left i j) L)
  have h2 := rapidCharacteristicProduct_antitone hP hR (Nat.sub_le_sub_right (le_max_right i j) L)
  simpa only [pow_two] using mul_le_mul h1 h2 (rapidCharacteristicProduct_pos hP hR _).le
    (rapidCharacteristicProduct_pos hP hR _).le

/-- Some fixed finite derivative order always satisfies the actual rapid admission threshold. -/
theorem exists_rapid_admission_order {P : ℕ} (hP : 1 ≤ P) :
    ∃ L : ℕ, 4 < rapidBase P^L := by
  have h := (tendsto_pow_atTop_atTop_of_one_lt (rapidBase_one_lt hP)).eventually
    (Filter.eventually_gt_atTop (4:ℝ))
  exact h.exists


end
end MeyerGeneralProblem.Adaptive
