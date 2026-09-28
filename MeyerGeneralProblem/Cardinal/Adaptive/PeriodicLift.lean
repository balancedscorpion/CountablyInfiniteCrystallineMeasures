module

public import MeyerGeneralProblem.Cardinal.Adaptive.PeriodicDescent
public import MeyerGeneralProblem.Cardinal.Adaptive.RankArithmetic

@[expose] public section

/-! # A constructed finite polynomial lift of local periodic differences -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section

/-- Exact original-order consumption of all leading-coefficient descents. -/
def periodicDescentCost : ℕ → ℕ
  | 0 => 2
  | d+1 => d+3+periodicDescentCost d

/-- The descent cost is the exact triangular sum of the d+2 losses. -/
theorem periodicDescentCost_twice (d : ℕ) :
    2*periodicDescentCost d = (d+1)*(d+4) := by
  induction d with
  | zero => rfl
  | succ d ih => simp only [periodicDescentCost]; nlinarith

/-- Every permitted descent fits in the fixed original lift budget. -/
theorem periodicDescentCost_lt_liftOrder (p d : ℕ) (hd : d ≤ 12*p) :
    6*p+periodicDescentCost d < liftOrder p := by
  have hc := periodicDescentCost_twice d
  have hb := lift_loss_lt_liftOrder p
  have hpow : d*d ≤ (12*p)*(12*p) := Nat.mul_self_le_mul_self hd
  nlinarith

/-- The actual native coefficient maps, recursively composed from leading
periodization and bounded monomial subtraction. All choices precede the source
and have no exceptional-set argument. -/
def nativePeriodicCoefficient : (d q : ℕ) → (P : ℝ) →
    (hP : P ∈ Set.Icc (1/2:ℝ) 2) → Fin (d+1) →
      (HermiteScale (-(q:ℤ)) →L[ℂ] HermiteScale (-((q+periodicDescentCost d:ℕ):ℤ)))
  | 0, q, P, hP, _ => nativePeriodicLeading q 0 P hP
  | d+1, q, P, hP, i => Fin.lastCases
      ((nativeOrderInclusion (q+2) (q+periodicDescentCost (d+1))).comp
        (nativePeriodicLeading q (d+1) P hP))
      (fun j => (nativeOrderInclusion (q+2+(d+1)+periodicDescentCost d)
          (q+periodicDescentCost (d+1))).comp
        ((nativePeriodicCoefficient d (q+2+(d+1)) P hP j).comp
          (nativePeriodicRemainder q (d+1) P hP))) i

/-- Every coefficient produced by the fixed linear construction is a whole
periodic distribution, before any local difference hypothesis is supplied. -/
theorem nativePeriodicCoefficient_periodic (d q : ℕ) (P : ℝ)
    (hP : P ∈ Set.Icc (1/2:ℝ) 2) (i : Fin (d+1)) (T : HermiteScale (-(q:ℤ))) :
    combDistributionTranslation P
      (hermiteScaleDistribution (q+periodicDescentCost d) (nativePeriodicCoefficient d q P hP i T)) =
      hermiteScaleDistribution (q+periodicDescentCost d) (nativePeriodicCoefficient d q P hP i T) := by
  induction d generalizing q with
  | zero => exact nativePeriodicLeading_periodic q 0 P hP T
  | succ d ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [nativePeriodicCoefficient, Fin.lastCases_last, ContinuousLinearMap.comp_apply]
        rw [nativeOrderInclusion_realizes (q+2) _ (by simp [periodicDescentCost]; omega)]
        exact nativePeriodicLeading_periodic q (d+1) P hP T
      · simp only [nativePeriodicCoefficient, Fin.lastCases_castSucc, ContinuousLinearMap.comp_apply]
        rw [nativeOrderInclusion_realizes _ _ (by simp [periodicDescentCost]; omega)]
        exact ih (q+2+(d+1)) j (nativePeriodicRemainder q (d+1) P hP T)

/-- The full finite polynomial of the constructed whole periodic coefficients. -/
def periodicLiftPolynomial (d q : ℕ) (P : ℝ) (hP : P ∈ Set.Icc (1/2:ℝ) 2)
    (T : HermiteScale (-(q:ℤ))) : TemperedDistribution ℝ ℂ :=
  ∑ i : Fin (d+1), monomialDistribution i.val
    (hermiteScaleDistribution (q+periodicDescentCost d) (nativePeriodicCoefficient d q P hP i T))

set_option maxHeartbeats 800000 in
private theorem periodicLiftPolynomial_succ (d q : ℕ) (P : ℝ)
    (hP : P ∈ Set.Icc (1/2:ℝ) 2) (T : HermiteScale (-(q:ℤ))) :
    periodicLiftPolynomial (d+1) q P hP T =
      periodicLiftPolynomial d (q+2+(d+1)) P hP (nativePeriodicRemainder q (d+1) P hP T) +
      monomialDistribution (d+1)
        (hermiteScaleDistribution (q+2) (nativePeriodicLeading q (d+1) P hP T)) := by
  unfold periodicLiftPolynomial
  rw [Fin.sum_univ_castSucc]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    simp only [nativePeriodicCoefficient, Fin.lastCases_castSucc, Fin.val_castSucc,
      ContinuousLinearMap.comp_apply]
    rw [nativeOrderInclusion_realizes _ _ (by simp [periodicDescentCost]; omega)]
  · simp only [nativePeriodicCoefficient, Fin.lastCases_last, Fin.val_last,
      ContinuousLinearMap.comp_apply]
    rw [nativeOrderInclusion_realizes _ _ (by simp [periodicDescentCost]; omega)]

/-- The complete constructed finite polynomial agrees with the original source
on the periodic region of its local finite-difference equation. The remainder
is retained as an actual distribution vanishing on that region. -/
theorem periodicLiftPolynomial_agrees (d q : ℕ) (P : ℝ)
    (hP : P ∈ Set.Icc (1/2:ℝ) 2) (O : Set ℝ) (hopen : IsOpen O)
    (hO : Function.Periodic (fun x => x ∈ O) P) (T : HermiteScale (-(q:ℤ)))
    (hT : DistributionVanishesOn O
      ((distributionDifference P : TemperedDistribution ℝ ℂ → TemperedDistribution ℝ ℂ)^[d+1]
        (hermiteScaleDistribution q T))) :
    DistributionVanishesOn O (hermiteScaleDistribution q T - periodicLiftPolynomial d q P hP T) := by
  induction d generalizing q with
  | zero =>
      intro f hf hs
      have h := nativePeriodicLeading_agrees q 0 P hP O hopen hO T hT f hf hs
      simp only [differenceLeadingFactor, Nat.factorial_zero, Nat.cast_one, pow_zero,
        mul_one, inv_one, one_mul, Function.iterate_zero_apply] at h
      change hermiteScaleDistribution q T f - periodicLiftPolynomial 0 q P hP T f = 0
      have he : periodicLiftPolynomial 0 q P hP T f =
          hermiteScaleDistribution (q+2) (nativePeriodicLeading q 0 P hP T) f := by
        unfold periodicLiftPolynomial
        rw [Fin.sum_univ_one]
        rfl
      rw [he, h, sub_self]
  | succ d ih =>
      have hr := nativePeriodicRemainder_vanishes q (d+1) P hP O hopen hO T hT
      have h := ih (q+2+(d+1)) (nativePeriodicRemainder q (d+1) P hP T) hr
      rw [nativePeriodicRemainder_realizes] at h
      rw [periodicLiftPolynomial_succ]
      convert h using 1
      abel

/-- All constructed coefficient maps have one original native bound, uniform
in the period and coefficient index and fixed before the source or region. -/
theorem exists_nativePeriodicCoefficient_norm_bound (d q : ℕ) :
    ∃ B > 0, ∀ (P : ℝ) (hP : P ∈ Set.Icc (1/2:ℝ) 2) (i : Fin (d+1)),
      ‖nativePeriodicCoefficient d q P hP i‖ ≤ B := by
  induction d generalizing q with
  | zero =>
      obtain ⟨B,hB,hb⟩ := exists_nativePeriodicLeading_norm_bound q 0
      exact ⟨B,hB,fun P hP _ => hb P hP⟩
  | succ d ih =>
      obtain ⟨A,hA,ha⟩ := exists_nativePeriodicLeading_norm_bound q (d+1)
      obtain ⟨B,hB,hb⟩ := ih (q+2+(d+1))
      obtain ⟨C,hC,hc⟩ := exists_nativePeriodicRemainder_norm_bound q (d+1)
      refine ⟨A+B*C+1,by positivity,?_⟩
      intro P hP i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [nativePeriodicCoefficient, Fin.lastCases_last]
        have hi := nativeOrderInclusion_norm_le (q+2) (q+periodicDescentCost (d+1))
          (by simp [periodicDescentCost]; omega)
        have hh := (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul hi (ha P hP) (norm_nonneg _) (by norm_num))
        exact hh.trans (by nlinarith)
      · simp only [nativePeriodicCoefficient, Fin.lastCases_castSucc]
        have hi := nativeOrderInclusion_norm_le (q+2+(d+1)+periodicDescentCost d)
          (q+periodicDescentCost (d+1)) (by simp [periodicDescentCost]; omega)
        have hc' := (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul (hb P hP j) (hc P hP) (norm_nonneg _) hB.le)
        have hh := (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul hi hc' (norm_nonneg _) (by norm_num))
        exact hh.trans (by nlinarith)

/-- The same actual coefficient at the fixed order Qp, for a degree within
its proved budget. The definition has no region or source-dependent choice. -/
def nativePeriodicCoefficientAtBudget (p d : ℕ) (P : ℝ)
    (hP : P ∈ Set.Icc (1/2:ℝ) 2) (i : Fin (d+1)) :
    HermiteScale (-((6*p:ℕ):ℤ)) →L[ℂ] HermiteScale (-((liftOrder p):ℤ)) :=
  (nativeOrderInclusion (6*p+periodicDescentCost d) (liftOrder p)).comp
    (nativePeriodicCoefficient d (6*p) P hP i)

/-- Re-embedding a permitted coefficient at Qp preserves the whole source. -/
theorem nativePeriodicCoefficientAtBudget_realizes (p d : ℕ) (hd : d ≤ 12*p)
    (P : ℝ) (hP : P ∈ Set.Icc (1/2:ℝ) 2) (i : Fin (d+1))
    (T : HermiteScale (-((6*p:ℕ):ℤ))) :
    hermiteScaleDistribution (liftOrder p) (nativePeriodicCoefficientAtBudget p d P hP i T) =
      hermiteScaleDistribution (6*p+periodicDescentCost d)
        (nativePeriodicCoefficient d (6*p) P hP i T) :=
  nativeOrderInclusion_realizes _ _ (periodicDescentCost_lt_liftOrder p d hd).le _

/-- One positive original native bound serves every allowed degree, period and
coefficient at fixed p, before the region or unknown source is given. -/
theorem exists_nativePeriodicCoefficientAtBudget_norm_bound (p : ℕ) :
    ∃ B > 0, ∀ (d : ℕ), d ≤ 12*p → ∀ (P : ℝ) (hP : P ∈ Set.Icc (1/2:ℝ) 2)
      (i : Fin (d+1)), ‖nativePeriodicCoefficientAtBudget p d P hP i‖ ≤ B := by
  classical
  choose C hC hc using fun d : Fin (12*p+1) => exists_nativePeriodicCoefficient_norm_bound d.val (6*p)
  have hs0 : 0 ≤ ∑ d : Fin (12*p+1), C d := Finset.sum_nonneg (fun d _ => (hC d).le)
  refine ⟨(∑ d : Fin (12*p+1), C d)+1, by linarith, ?_⟩
  intro d hd P hP i
  let j : Fin (12*p+1) := ⟨d,by omega⟩
  have hi := nativeOrderInclusion_norm_le (6*p+periodicDescentCost d) (liftOrder p)
    (periodicDescentCost_lt_liftOrder p d hd).le
  have hh := (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul hi (hc j P hP i) (norm_nonneg _) (by norm_num))
  change ‖nativePeriodicCoefficientAtBudget p d P hP i‖ ≤ _ at hh
  have hs : C j ≤ ∑ k : Fin (12*p+1), C k :=
    Finset.single_le_sum (fun k _ => (hC k).le) (Finset.mem_univ j)
  exact hh.trans (by linarith)

end
end MeyerGeneralProblem.Adaptive
