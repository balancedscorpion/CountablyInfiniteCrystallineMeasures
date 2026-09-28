module

public import MeyerGeneralProblem.Sampling.GroupedHarauxRemoval
public import MeyerGeneralProblem.Sampling.GroupedExponential

@[expose] public section

/-!
# Whole-cluster insertion in actual divided-difference coordinates

The clustered exponential sum is converted algebraically to a finite ordinary
exponential polynomial solely for exact annihilation. No norm is taken on
the inverse-gap coefficients. A local cluster floor then combines with the
exterior coefficient bound to give a true joint lower inequality.
-/

namespace MeyerGeneralProblem

noncomputable section

open MeasureTheory

/-- The genuine finite synthesis in initial-segment divided differences. -/
def groupedExponentialPolynomial {k : ℕ} (nodes : Fin k → ℝ) (a : Fin k → ℂ) (t : ℝ) : ℂ :=
  ∑ j, a j * groupedExponentialInitial nodes j t

/-- The actual finite grouped synthesis is continuous, including collisions. -/
theorem continuous_groupedExponentialPolynomial {k : ℕ} (nodes : Fin k → ℝ) (a : Fin k → ℂ) :
    Continuous (groupedExponentialPolynomial nodes a) := by
  apply continuous_finsetSum
  intro j hj
  exact continuous_const.mul (continuous_groupedExponentialInitial nodes j)

/-- Algebraic conversion at distinct nodes. The ordinary coefficients exist,
but no bound on them is asserted or needed. -/
theorem exists_gramFourierPolynomial_eq_groupedExponentialPolynomial
    {k : ℕ} (nodes : Fin k → ℝ) (hnodes : Function.Injective nodes) (a : Fin k → ℂ) :
    ∃ c : Fin k → ℂ, gramFourierPolynomial nodes c = groupedExponentialPolynomial nodes a := by
  refine ⟨fun i => ∑ j, a j * groupedNewtonWeight (fun x => (nodes x : ℂ)) j i, ?_⟩
  funext t
  simp only [groupedExponentialPolynomial, groupedExponentialInitial_eq_groupedNewtonWeights nodes hnodes,
    gramFourierPolynomial, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Whole-cluster insertion in actual grouped coordinates, uniform in finite
dimension and internal gaps. The exterior lower/upper and local cluster floor
are explicit genuine integral inequalities, not the joint conclusion. -/
theorem exists_uniform_finite_lowerBound_insert_cluster
    (q : ℕ) {r d A B C : ℝ} (hr : 0 < r) (hd : 0 < d)
    (hA : 0 < A) (hB : 0 ≤ B) (hC : 0 < C) :
    ∃ A' : ℝ, 0 < A' ∧ ∀ b : ℝ, 0 ≤ b → ∀ n k : ℕ, k ≤ q →
      ∀ (s : Fin n → ℝ) (ω : Fin k → ℝ), Function.Injective ω →
      (∀ i j, d ≤ |s i - ω j|) →
      (∀ c : Fin n → ℂ, A * ∑ i, ‖c i‖ ^ 2 ≤
        ∫ t : ℝ in Set.Icc (-b) b, ‖gramFourierPolynomial s c t‖ ^ 2) →
      (∀ c : Fin n → ℂ,
        (∫ t : ℝ in Set.Icc (-(b + q * r)) (b + q * r),
          ‖gramFourierPolynomial s c t‖ ^ 2) ≤ B * ∑ i, ‖c i‖ ^ 2) →
      (∀ a : Fin k → ℂ, C * ∑ j, ‖a j‖ ^ 2 ≤
        ∫ t : ℝ in Set.Icc (-(b + q * r)) (b + q * r),
          ‖groupedExponentialPolynomial ω a t‖ ^ 2) →
      ∀ (c : Fin n → ℂ) (a : Fin k → ℂ),
        A' * ((∑ i, ‖c i‖ ^ 2) + ∑ j, ‖a j‖ ^ 2) ≤
          ∫ t : ℝ in Set.Icc (-(b + q * r)) (b + q * r),
            ‖gramFourierPolynomial s c t + groupedExponentialPolynomial ω a t‖ ^ 2 := by
  obtain ⟨P, hP, hexterior⟩ := exists_uniform_exterior_bound_after_cluster_removal q hr hd hA
  let L := 2 * P + 2 * B + C
  have hL : 0 < L := by dsimp [L]; positivity
  refine ⟨P * C / L, by positivity, ?_⟩
  intro b hb n k hk s ω hω hsep hlower hupper hcluster c a
  let Q := ∑ i, ‖c i‖ ^ 2
  let T := ∑ j, ‖a j‖ ^ 2
  let W := Set.Icc (-(b + q * r)) (b + q * r)
  let f := gramFourierPolynomial s c
  let g := groupedExponentialPolynomial ω a
  let E := ∫ t : ℝ in W, ‖f t + g t‖ ^ 2
  have hf : Continuous f := by unfold f gramFourierPolynomial gramPhase; fun_prop
  have hg : Continuous g := continuous_groupedExponentialPolynomial ω a
  obtain ⟨v, hv⟩ := exists_gramFourierPolynomial_eq_groupedExponentialPolynomial ω hω a
  have hPQ : P * Q ≤ E := by
    have h := hexterior b hb n k hk s ω hsep hlower c v
    simpa only [hv] using h
  have hpoint (t : ℝ) : ‖g t‖ ^ 2 ≤ 2 * ‖f t + g t‖ ^ 2 + 2 * ‖f t‖ ^ 2 := by
    have hn : ‖g t‖ ≤ ‖f t + g t‖ + ‖f t‖ := by
      simpa only [add_sub_cancel_left] using norm_sub_le (f t + g t) (f t)
    have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hn
    nlinarith [sq_nonneg (‖f t + g t‖ - ‖f t‖)]
  have hCT : C * T ≤ 2 * E + 2 * B * Q := by
    have hInt := integral_mono (μ := volume.restrict W)
      ((hg.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc)
      ((((hf.add hg).norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc).const_mul 2 |>.add
        (((hf.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc).const_mul 2)) hpoint
    simp only [Pi.add_apply, Pi.pow_apply] at hInt
    rw [integral_add (f := fun t => 2 * ‖f t + g t‖ ^ 2)
      (g := fun t => 2 * ‖f t‖ ^ 2)
      ((((hf.add hg).norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc).const_mul 2)
      (((hf.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc).const_mul 2),
      integral_const_mul, integral_const_mul] at hInt
    have hc := hcluster a
    have hu := hupper c
    change C * T ≤ _ at hc
    change _ ≤ B * Q at hu
    change _ ≤ 2 * E + 2 * ∫ t : ℝ in W, ‖f t‖ ^ 2 at hInt
    linarith
  have hmulCT := mul_le_mul_of_nonneg_left hCT hP.le
  have hmulPQB := mul_le_mul_of_nonneg_left hPQ hB
  have hmulPQC := mul_le_mul_of_nonneg_left hPQ hC.le
  change (P * C / L) * (Q + T) ≤ E
  rw [div_mul_eq_mul_div, div_le_iff₀ hL]
  dsimp [L]
  nlinarith

end

end MeyerGeneralProblem
