module

public import MeyerGeneralProblem.Cardinal.Adaptive.AntiperiodicConjugation
public import MeyerGeneralProblem.Cardinal.Adaptive.PeriodicLift

@[expose] public section

/-! # Actual bounded generalized antiperiodic lifts at the fixed original order -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section

/-- Zero modulation is the identity on the complete tempered source. -/
theorem distributionModulation_zero (T : TemperedDistribution ℝ ℂ) :
    combDistributionModulation 0 T = T := by
  ext f
  change T (combSchwartzModulation 0 f) = T f
  congr 1
  ext x
  simp only [combSchwartzModulation_apply, combModulationCharacter_zero_left, one_mul]

/-- Undoing the half-period modulation turns whole periodic coefficients into
whole antiperiodic coefficients. -/
theorem inverseHalfPeriodModulation_antiperiodic (P : ℝ) (hP : P ≠ 0)
    (T : TemperedDistribution ℝ ℂ) (hT : combDistributionTranslation P T = T) :
    combDistributionTranslation P (combDistributionModulation (-halfPeriodFrequency P) T) =
      -combDistributionModulation (-halfPeriodFrequency P) T := by
  have h := halfPeriodModulation_translation P hP
    (combDistributionModulation (-halfPeriodFrequency P) T)
  rw [distributionModulation_add, add_neg_cancel, distributionModulation_zero, hT] at h
  have hh := congrArg (combDistributionModulation (-halfPeriodFrequency P)) h
  rw [map_neg, distributionModulation_neg_cancel] at hh
  have hn := congrArg Neg.neg hh
  simpa only [neg_neg] using hn.symm

/-- Coordinate monomials commute with the genuine whole modulation map. -/
theorem distributionModulation_monomial (a : ℝ) (d : ℕ) (T : TemperedDistribution ℝ ℂ) :
    combDistributionModulation a (monomialDistribution d T) =
      monomialDistribution d (combDistributionModulation a T) := by
  ext f
  change T (monomialTestCLM d (combSchwartzModulation a f)) =
    T (combSchwartzModulation a (monomialTestCLM d f))
  congr 1
  ext x
  simp only [monomialTestCLM_apply, combSchwartzModulation_apply]
  ring

/-- The exact coefficient maps at Qp: conjugate the source, apply the actual
recursive periodic lift, then undo the modulation on each coefficient. -/
def nativeAntiperiodicCoefficient (p d : ℕ) (P : ℝ)
    (hP : P ∈ Set.Icc (1/2:ℝ) 2) (i : Fin (d+1)) :
    HermiteScale (-((6*p:ℕ):ℤ)) →L[ℂ] HermiteScale (-((liftOrder p):ℤ)) :=
  (nativeModulation (liftOrder p) (-halfPeriodFrequency P)).comp
    ((nativePeriodicCoefficientAtBudget p d P hP i).comp
      (nativeModulation (6*p) (halfPeriodFrequency P)))

/-- Every constructed coefficient is the actual unmodulated periodic coefficient
as a whole tempered distribution. -/
theorem nativeAntiperiodicCoefficient_realizes (p d : ℕ) (hd : d ≤ 12*p)
    (P : ℝ) (hP : P ∈ Set.Icc (1/2:ℝ) 2) (i : Fin (d+1))
    (T : HermiteScale (-((6*p:ℕ):ℤ))) :
    hermiteScaleDistribution (liftOrder p) (nativeAntiperiodicCoefficient p d P hP i T) =
      combDistributionModulation (-halfPeriodFrequency P)
        (hermiteScaleDistribution (6*p+periodicDescentCost d)
          (nativePeriodicCoefficient d (6*p) P hP i
            (nativeModulation (6*p) (halfPeriodFrequency P) T))) := by
  simp only [nativeAntiperiodicCoefficient, ContinuousLinearMap.comp_apply,
    nativeModulation_realizes, nativePeriodicCoefficientAtBudget_realizes p d hd]

/-- Whole antiperiodicity is automatic for the constructed maps and holds on
all Schwartz tests before any local source hypothesis is supplied. -/
theorem nativeAntiperiodicCoefficient_antiperiodic (p d : ℕ) (hd : d ≤ 12*p)
    (P : ℝ) (hP : P ∈ Set.Icc (1/2:ℝ) 2) (i : Fin (d+1))
    (T : HermiteScale (-((6*p:ℕ):ℤ))) :
    combDistributionTranslation P
      (hermiteScaleDistribution (liftOrder p) (nativeAntiperiodicCoefficient p d P hP i T)) =
      -hermiteScaleDistribution (liftOrder p) (nativeAntiperiodicCoefficient p d P hP i T) := by
  rw [nativeAntiperiodicCoefficient_realizes p d hd]
  exact inverseHalfPeriodModulation_antiperiodic P (by linarith [hP.1]) _
    (nativePeriodicCoefficient_periodic d (6*p) P hP i _)

/-- The full finite polynomial built from the actual antiperiodic coefficients. -/
def antiperiodicLiftPolynomial (p d : ℕ) (P : ℝ)
    (hP : P ∈ Set.Icc (1/2:ℝ) 2) (T : HermiteScale (-((6*p:ℕ):ℤ))) :
    TemperedDistribution ℝ ℂ :=
  ∑ i : Fin (d+1), monomialDistribution i.val
    (hermiteScaleDistribution (liftOrder p) (nativeAntiperiodicCoefficient p d P hP i T))

/-- Exact whole modulation identity for the finite polynomial, with no lost
seam term or restriction of the distribution to individual atoms. -/
theorem antiperiodicLiftPolynomial_eq (p d : ℕ) (hd : d ≤ 12*p)
    (P : ℝ) (hP : P ∈ Set.Icc (1/2:ℝ) 2) (T : HermiteScale (-((6*p:ℕ):ℤ))) :
    antiperiodicLiftPolynomial p d P hP T =
      combDistributionModulation (-halfPeriodFrequency P)
        (periodicLiftPolynomial d (6*p) P hP (nativeModulation (6*p) (halfPeriodFrequency P) T)) := by
  simp only [antiperiodicLiftPolynomial, periodicLiftPolynomial, map_sum,
    distributionModulation_monomial, nativeAntiperiodicCoefficient_realizes p d hd]

/-- The required whole-source generalized antiperiodic decomposition. The
remainder is retained and vanishes on the given periodic open set; the fixed
coefficient maps depend only on p,d,P, never on that set or the source. -/
theorem antiperiodicLiftPolynomial_agrees (p d : ℕ) (hd : d ≤ 12*p)
    (P : ℝ) (hP : P ∈ Set.Icc (1/2:ℝ) 2) (O : Set ℝ) (hopen : IsOpen O)
    (hO : Function.Periodic (fun x => x ∈ O) P) (T : HermiteScale (-((6*p:ℕ):ℤ)))
    (hT : DistributionVanishesOn O
      ((distributionAntidifference P : TemperedDistribution ℝ ℂ → TemperedDistribution ℝ ℂ)^[d+1]
        (hermiteScaleDistribution (6*p) T))) :
    DistributionVanishesOn O
      (hermiteScaleDistribution (6*p) T - antiperiodicLiftPolynomial p d P hP T) := by
  have hdif := nativeModulation_local_difference (6*p) (d+1) P
    (by linarith [hP.1]) O T hT
  have h := (periodicLiftPolynomial_agrees d (6*p) P hP O hopen hO _ hdif).modulation
    (-halfPeriodFrequency P)
  rw [map_sub, nativeModulation_realizes, distributionModulation_neg_cancel,
    ← antiperiodicLiftPolynomial_eq p d hd] at h
  exact h

/-- Half-period modulation frequencies stay in a fixed compact range. -/
theorem halfPeriodFrequency_abs_le_one (P : ℝ) (hP : P ∈ Set.Icc (1/2:ℝ) 2) :
    |halfPeriodFrequency P| ≤ 1 := by
  have hp : 0 < 2*P := by linarith [hP.1]
  rw [halfPeriodFrequency, abs_of_pos (div_pos zero_lt_one hp), div_le_one hp]
  linarith [hP.1]

private theorem exists_native_modulation_compact_bound (q : ℕ) :
    ∃ B > 0, ∀ a : ℝ, |a| ≤ 1 → ‖nativeModulation q a‖ ≤ B := by
  obtain ⟨B,hB,hb⟩ := exists_nativeModulation_norm_bound q
  refine ⟨B*2^(2*q),by positivity,?_⟩
  intro a ha
  exact (hb a).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity) (by linarith : 1+|a| ≤ 2) _) hB.le)

/-- A single fixed-p bound controls all degrees through12p, all allowed periods,
and all constructed actual antiperiodic coefficients in the original H_-Qp. -/
theorem exists_nativeAntiperiodicCoefficient_norm_bound (p : ℕ) :
    ∃ B > 0, ∀ (d : ℕ), d ≤ 12*p → ∀ (P : ℝ) (hP : P ∈ Set.Icc (1/2:ℝ) 2)
      (i : Fin (d+1)), ‖nativeAntiperiodicCoefficient p d P hP i‖ ≤ B := by
  obtain ⟨A,hA,ha⟩ := exists_native_modulation_compact_bound (liftOrder p)
  obtain ⟨B,hB,hb⟩ := exists_nativePeriodicCoefficientAtBudget_norm_bound p
  obtain ⟨C,hC,hc⟩ := exists_native_modulation_compact_bound (6*p)
  refine ⟨A*(B*C),by positivity,?_⟩
  intro d hd P hP i
  have hh : |halfPeriodFrequency P| ≤ 1 := halfPeriodFrequency_abs_le_one P hP
  have hn : |-halfPeriodFrequency P| ≤ 1 := by simpa only [abs_neg] using hh
  have hi := (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul (hb d hd P hP i) (hc _ hh) (norm_nonneg _) hB.le)
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul (ha _ hn) hi (norm_nonneg _) hA.le)

end
end MeyerGeneralProblem.Adaptive
