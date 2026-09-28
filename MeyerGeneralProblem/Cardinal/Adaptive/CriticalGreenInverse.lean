module

public import MeyerGeneralProblem.Cardinal.Adaptive.CriticalGreenCutoff

@[expose] public section

/-! # Whole tempered-distribution right inverse for the actual head difference operator -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open scoped BigOperators

private theorem tsum_int_eq_tsum_positive {f : ℤ → ℂ} (hf : Summable f)
    (hz : ∀ n : ℤ, n ≤ 0 → f n=0) :
    (∑' n : ℤ, f n) = ∑' n : ℕ, f ((n : ℤ)+1) := by
  have hn : Summable (fun n : ℕ => f (n : ℤ)) := hf.comp_injective Nat.cast_injective
  have hneg : (fun n : ℕ => f (-((n : ℤ)+1))) = 0 := by
    funext n
    exact hz _ (by omega)
  have he := tsum_of_nat_of_neg_add_one hn (show Summable (fun n : ℕ => f (-((n : ℤ)+1))) by rw [hneg]; exact summable_zero)
  rw [hneg] at he
  change (∑' n : ℤ, f n) = (∑' n : ℕ, f (n : ℤ))+(∑' n : ℕ, (0 : ℂ)) at he
  rw [tsum_zero,add_zero,hn.tsum_eq_zero_add] at he
  simpa only [Nat.cast_zero,hz 0 (by omega),zero_add,Nat.cast_add,Nat.cast_one] using he


private theorem tsum_int_eq_tsum_negative {f : ℤ → ℂ} (hf : Summable f)
    (hz : ∀ n : ℤ, 0 ≤ n → f n=0) :
    (∑' n : ℤ, f n) = ∑' n : ℕ, f (-((n : ℤ)+1)) := by
  have he := tsum_int_eq_tsum_positive (hf.comp_injective neg_injective)
    (fun n hn => hz (-n) (by omega))
  have heq : (∑' n : ℤ, (f ∘ Neg.neg) n) = ∑' n : ℤ, f n :=
    (Equiv.neg ℤ).tsum_eq f
  exact heq.symm.trans he

/-- The absolutely convergent whole integer translation series at each test point. -/
def integerGreenAction (w : ℤ → ℂ) (f : SchwartzMap ℝ ℂ) (x : ℝ) : ℂ :=
  ∑' t : ℤ, w t*f (x+(t : ℝ))

/-- Bounded Green coefficients act absolutely on every translated Schwartz test. -/
theorem summable_integerGreenAction (w : ℤ → ℂ) {B : ℝ} (hB : 0 ≤ B)
    (hw : ∀ t, ‖w t‖ ≤ B) (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    Summable (fun t : ℤ => w t*f (x+(t : ℝ))) :=
  summable_weightedInteger_samples w hB hw (combSchwartzTranslation x f)

/-- The actual difference operator on tests, with the source's exact centered
indices and coefficient normalization. -/
def criticalHeadDifferenceTestCLM {k : ℕ} (α : Fin k → ℝ) :
    SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
  ∑ i : Fin (Fintype.card (Fin k × Bool)+1), criticalHeadDifferenceCoeff α i •
    combSchwartzTranslation ((i : ℤ)-(k : ℤ))

/-- Pointwise action of the finite whole-source difference operator. -/
theorem criticalHeadDifferenceTestCLM_apply {k : ℕ} (α : Fin k → ℝ)
    (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    criticalHeadDifferenceTestCLM α f x =
      ∑ i : Fin (Fintype.card (Fin k × Bool)+1), criticalHeadDifferenceCoeff α i *
        f (x+(((i : ℤ)-(k : ℤ) : ℤ) : ℝ)) := by
  simp only [criticalHeadDifferenceTestCLM,_root_.sum_apply,
    _root_.smul_apply,smul_eq_mul,Int.cast_sub,
    combSchwartzTranslation_apply,add_comm]

/-- Both one-sided source Green sequences vanish on their opposite closed half-line. -/
theorem criticalHeadGreen_opposite_zero {k : ℕ} (hk : 1 ≤ k) (α : Fin k → ℝ) (t : ℤ) :
    (t ≤ 0 → criticalHeadGreen true α t=0) ∧
    (0 ≤ t → criticalHeadGreen false α t=0) := by
  constructor
  · intro ht
    simp only [criticalHeadGreen,ite_true]
    rw [criticalHeadPositiveGreen_eq_zero α t (by omega),mul_zero]
  · intro ht
    simp only [criticalHeadGreen,Bool.false_eq_true,ite_false]
    rw [criticalHeadNegativeGreen_eq_zero α t (by omega),mul_zero]

/-- The constructed Schwartz transpose equals the complete bilateral action
of its two one-sided Green sequences, with the cutoffs outside the sums. -/
theorem criticalGreenTestCLM_bilateral {k : ℕ} (hk : 1 ≤ k) (α : Fin k → ℝ)
    (hα : Function.Injective α) (hi : ∀ i, 0 < α i ∧ α i < 1/2)
    (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    criticalGreenTestCLM α hα hi f x =
      criticalPositiveCutoff x*integerGreenAction (criticalHeadGreen true α) f x +
      criticalNegativeCutoff x*integerGreenAction (criticalHeadGreen false α) f x := by
  have hs (b : Bool) := summable_integerGreenAction (criticalHeadGreen b α)
    (actualGreenBound_nonneg b α hα hi) (norm_criticalHeadGreen_le b α hα hi) f x
  have hp := tsum_int_eq_tsum_positive (hs true) (fun t ht => by
    rw [(criticalHeadGreen_opposite_zero hk α t).1 ht,zero_mul])
  have hn := tsum_int_eq_tsum_negative (hs false) (fun t ht => by
    rw [(criticalHeadGreen_opposite_zero hk α t).2 ht,zero_mul])
  rw [criticalGreenTestCLM_apply,integerGreenAction,integerGreenAction,hp,hn]
  simp only [Int.cast_add,Int.cast_one,Int.cast_neg,Int.cast_natCast,← sub_eq_add_neg]
  rw [← tsum_mul_left,← tsum_mul_left]
  congr 1 <;> apply tsum_congr <;> intro n <;> ring


/-- Each complete bilateral Green action inverts the actual finite difference
operator on Schwartz tests. Absolute convergence justifies all finite exchanges. -/
theorem integerGreenAction_difference {k : ℕ} (hk : 1 ≤ k) (b : Bool) (α : Fin k → ℝ)
    (hα : Function.Injective α) (hi : ∀ i, 0 < α i ∧ α i < 1/2)
    (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    integerGreenAction (criticalHeadGreen b α) (criticalHeadDifferenceTestCLM α f) x = f x := by
  classical
  let I := Fin (Fintype.card (Fin k × Bool)+1)
  let l : I → ℤ := fun i => (i : ℤ)-(k : ℤ)
  let c : I → ℂ := criticalHeadDifferenceCoeff α
  let w : ℤ → ℂ := criticalHeadGreen b α
  have hs (i : I) : Summable (fun t : ℤ => c i*w t*f (x+(t : ℝ)+(l i : ℝ))) := by
    have hh := (summable_integerGreenAction w (actualGreenBound_nonneg b α hα hi)
      (norm_criticalHeadGreen_le b α hα hi) (combSchwartzTranslation (l i) f) x).mul_left (c i)
    simpa only [combSchwartzTranslation_apply,mul_assoc,add_comm,add_left_comm,add_assoc] using hh
  have hcast (i : I) (t : ℤ) : x+((t-l i : ℤ) : ℝ)+(l i : ℝ)=x+(t : ℝ) := by
    push_cast
    ring
  have hequiv (i : I) (t : ℤ) : (Equiv.addRight (-(l i))) t=t-l i := rfl
  have hshift (i : I) : (∑' t : ℤ, c i*w t*f (x+(t : ℝ)+(l i : ℝ))) =
      ∑' t : ℤ, c i*w (t-l i)*f (x+(t : ℝ)) := by
    have he := (Equiv.addRight (-(l i))).tsum_eq
      (fun t : ℤ => c i*w t*f (x+(t : ℝ)+(l i : ℝ)))
    simpa only [hequiv,hcast] using he.symm
  have hs' (i : I) : Summable (fun t : ℤ => c i*w (t-l i)*f (x+(t : ℝ))) := by
    have hh := (hs i).comp_injective (Equiv.addRight (-(l i))).injective
    simpa only [Function.comp_def,hequiv,hcast] using hh
  calc
    _ = ∑' t : ℤ, ∑ i : I, c i*w t*f (x+(t : ℝ)+(l i : ℝ)) := by
      unfold integerGreenAction
      apply tsum_congr
      intro t
      rw [criticalHeadDifferenceTestCLM_apply,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      change w t*(c i*f (x+(t : ℝ)+(l i : ℝ))) = _
      ring
    _ = ∑ i : I, ∑' t : ℤ, c i*w t*f (x+(t : ℝ)+(l i : ℝ)) :=
      Summable.tsum_finsetSum (fun i _ => hs i)
    _ = ∑ i : I, ∑' t : ℤ, c i*w (t-l i)*f (x+(t : ℝ)) := by
      exact Finset.sum_congr rfl (fun i _ => hshift i)
    _ = ∑' t : ℤ, ∑ i : I, c i*w (t-l i)*f (x+(t : ℝ)) :=
      (Summable.tsum_finsetSum (fun i _ => hs' i)).symm
    _ = ∑' t : ℤ, (if t=0 then 1 else 0)*f (x+(t : ℝ)) := by
      apply tsum_congr
      intro t
      rw [← Finset.sum_mul]
      congr 1
      exact criticalHeadGreen_impulse hk b α t
    _ = f x := by simp

/-- The actual whole Schwartz transpose is a left inverse to the actual test
difference operator. Both cutoffs contribute their exact partition of unity. -/
theorem criticalGreenTestCLM_difference {k : ℕ} (hk : 1 ≤ k) (α : Fin k → ℝ)
    (hα : Function.Injective α) (hi : ∀ i, 0 < α i ∧ α i < 1/2)
    (f : SchwartzMap ℝ ℂ) :
    criticalGreenTestCLM α hα hi (criticalHeadDifferenceTestCLM α f) = f := by
  ext x
  rw [criticalGreenTestCLM_bilateral hk,integerGreenAction_difference hk true α hα hi,
    integerGreenAction_difference hk false α hα hi,← add_mul,criticalCutoff_partition,one_mul]

/-- The actual finite difference operator on whole tempered distributions. -/
def criticalHeadDifferenceDistributionCLM {k : ℕ} (α : Fin k → ℝ) :
    TemperedDistribution ℝ ℂ →L[ℂ] TemperedDistribution ℝ ℂ :=
  PointwiseConvergenceCLM.precomp ℂ (criticalHeadDifferenceTestCLM α)

/-- Whole-source right inversion, with no atomicity, source decomposition or
boundary condition imposed on the incoming tempered distribution. -/
theorem criticalGreenDistribution_rightInverse {k : ℕ} (hk : 1 ≤ k) (α : Fin k → ℝ)
    (hα : Function.Injective α) (hi : ∀ i, 0 < α i ∧ α i < 1/2)
    (T : TemperedDistribution ℝ ℂ) :
    criticalHeadDifferenceDistributionCLM α (criticalGreenDistributionCLM α hα hi T) = T := by
  ext f
  change T (criticalGreenTestCLM α hα hi (criticalHeadDifferenceTestCLM α f)) = T f
  rw [criticalGreenTestCLM_difference hk]


/-- Integer translation series commute pointwise with a genuine periodic
Schwartz multiplier, retaining the whole bilateral sum. -/
theorem integerGreenAction_periodic_multiplier (w : ℤ → ℂ) (g : ℝ → ℂ)
    (hg : g.HasTemperateGrowth) (hp : Function.Periodic g 1)
    (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    integerGreenAction w (SchwartzMap.smulLeftCLM ℂ g f) x =
      g x*integerGreenAction w f x := by
  have hper (t : ℤ) : g (x+(t : ℝ))=g x := by simpa using hp.int_mul t x
  simp only [integerGreenAction,SchwartzMap.smulLeftCLM_apply_apply hg,smul_eq_mul,hper]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro t
  ring

/-- The constructed whole Schwartz Green transpose commutes with every actual
periodic multiplier of temperate growth. -/
theorem criticalGreenTestCLM_periodic_multiplier {k : ℕ} (hk : 1 ≤ k) (α : Fin k → ℝ)
    (hα : Function.Injective α) (hi : ∀ i, 0 < α i ∧ α i < 1/2)
    (g : ℝ → ℂ) (hg : g.HasTemperateGrowth) (hp : Function.Periodic g 1)
    (f : SchwartzMap ℝ ℂ) :
    criticalGreenTestCLM α hα hi (SchwartzMap.smulLeftCLM ℂ g f) =
      SchwartzMap.smulLeftCLM ℂ g (criticalGreenTestCLM α hα hi f) := by
  ext x
  rw [criticalGreenTestCLM_bilateral hk,SchwartzMap.smulLeftCLM_apply_apply hg,
    criticalGreenTestCLM_bilateral hk,integerGreenAction_periodic_multiplier _ g hg hp,
    integerGreenAction_periodic_multiplier _ g hg hp]
  simp only [smul_eq_mul]
  ring

/-- The corresponding whole tempered-distribution operators commute, without
requiring a phasewise decomposition of the source. -/
theorem criticalGreenDistribution_periodic_multiplier {k : ℕ} (hk : 1 ≤ k) (α : Fin k → ℝ)
    (hα : Function.Injective α) (hi : ∀ i, 0 < α i ∧ α i < 1/2)
    (g : ℝ → ℂ) (hg : g.HasTemperateGrowth) (hp : Function.Periodic g 1)
    (T : TemperedDistribution ℝ ℂ) :
    criticalGreenDistributionCLM α hα hi
      (PointwiseConvergenceCLM.precomp ℂ (SchwartzMap.smulLeftCLM ℂ g) T) =
    PointwiseConvergenceCLM.precomp ℂ (SchwartzMap.smulLeftCLM ℂ g)
      (criticalGreenDistributionCLM α hα hi T) := by
  ext f
  change T (SchwartzMap.smulLeftCLM ℂ g (criticalGreenTestCLM α hα hi f)) =
    T (criticalGreenTestCLM α hα hi (SchwartzMap.smulLeftCLM ℂ g f))
  rw [criticalGreenTestCLM_periodic_multiplier hk α hα hi g hg hp]

end
end MeyerGeneralProblem.Adaptive
