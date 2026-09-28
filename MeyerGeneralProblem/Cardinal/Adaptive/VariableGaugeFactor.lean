module

public import MeyerGeneralProblem.Cardinal.Adaptive.VariablePairedPowers

@[expose] public section

/-! Complete summation of the retained two-axis gauge row factors. -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section

private theorem gaugeCoefficient_norm_le (n : ℕ) : ‖halfNewtonGaugeCoefficient n‖ ≤ 8^n := by
  have hp : ‖(-2*Real.pi*Complex.I : ℂ)‖ ≤ 8 := by
    simp only [norm_mul,norm_neg,Complex.norm_ofNat,Complex.norm_real,
      Real.norm_eq_abs,abs_of_pos Real.pi_pos,Complex.norm_I,mul_one]
    linarith [Real.pi_lt_four]
  rw [halfNewtonGaugeCoefficient,norm_div,norm_pow,Complex.norm_natCast]
  apply (div_le_iff₀ (by exact_mod_cast Nat.factorial_pos n)).2
  exact (pow_le_pow_left₀ (norm_nonneg _) hp n).trans
    (le_mul_of_one_le_right (by positivity) (by exact_mod_cast Nat.factorial_pos n))

/-- A genuinely bounded core of each positive full gauge power, constructed
from the actual paired phase factorization. -/
def variableGaugePowerCore (P R Q S : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R)
    (hQ : 1 ≤ Q) (hS : 1 ≤ S) (n : ℕ) : SeamMomentArray →L[ℂ] SeamMomentArray :=
  (variableCoordinateSource_paired_power_factor P R Q S hP hR hQ hS n).choose

/-- The complete positive exponential term after retaining both phase weights. -/
def variableGaugeFactoredTerm (P R Q S : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R)
    (hQ : 1 ≤ Q) (hS : 1 ≤ S) (n : ℕ) : SeamMomentArray →L[ℂ] SeamMomentArray :=
  halfNewtonGaugeCoefficient (n+1) • variableGaugePowerCore P R Q S hP hR hQ hS n

theorem variableGaugePowerCore_norm_le (P R Q S : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R)
    (hQ : 1 ≤ Q) (hS : 1 ≤ S) (n : ℕ) :
    ‖variableGaugePowerCore P R Q S hP hR hQ hS n‖ ≤
      shrinkingNewtonSourceKappa⁻¹^2*(shrinkingNewtonSourceKappa^4)^(2*(n/2)) :=
  (variableCoordinateSource_paired_power_factor P R Q S hP hR hQ hS n).choose_spec.2

theorem variableGaugeFactoredTerm_bound (P R Q S : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R)
    (hQ : 1 ≤ Q) (hS : 1 ≤ S) (n : ℕ) :
    ‖variableGaugeFactoredTerm P R Q S hP hR hQ hS n‖ ≤
      8^(n+1)*(shrinkingNewtonSourceKappa⁻¹^2*(shrinkingNewtonSourceKappa^4)^(2*(n/2))) := by
  rw [variableGaugeFactoredTerm,norm_smul]
  exact mul_le_mul (gaugeCoefficient_norm_le (n+1))
    (variableGaugePowerCore_norm_le P R Q S hP hR hQ hS n) (norm_nonneg _) (by positivity)

/-- All terms beyond the first have a small geometric majorant after both
actual next-level weights have already been retained. -/
theorem variableGaugeFactoredTerm_tail_bound (P R Q S : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R)
    (hQ : 1 ≤ Q) (hS : 1 ≤ S) (n : ℕ) :
    ‖variableGaugeFactoredTerm P R Q S hP hR hQ hS (n+1)‖ ≤
      (64*shrinkingNewtonSourceKappa⁻¹^2)*(8*shrinkingNewtonSourceKappa^4)^n := by
  apply (variableGaugeFactoredTerm_bound P R Q S hP hR hQ hS (n+1)).trans
  have hr : (shrinkingNewtonSourceKappa^4)^(2*((n+1)/2)) ≤ (shrinkingNewtonSourceKappa^4)^n :=
    pow_le_pow_of_le_one (by positivity [shrinkingNewtonSourceKappa_pos])
      (by norm_num [shrinkingNewtonSourceKappa]) (by omega)
  calc
    _ ≤ 8^(n+1+1)*(shrinkingNewtonSourceKappa⁻¹^2*(shrinkingNewtonSourceKappa^4)^n) := by gcongr
    _ = _ := by rw [pow_succ,pow_succ,mul_pow]; ring

/-- The bounded row-factor series converges in the original full operator norm. -/
theorem variableGaugeFactoredTerm_summable_norm (P R Q S : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R)
    (hQ : 1 ≤ Q) (hS : 1 ≤ S) :
    Summable (fun n => ‖variableGaugeFactoredTerm P R Q S hP hR hQ hS n‖) := by
  have hs : Summable (fun n => ‖variableGaugeFactoredTerm P R Q S hP hR hQ hS (n+1)‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) (variableGaugeFactoredTerm_tail_bound P R Q S hP hR hQ hS)
      ((summable_geometric_of_lt_one (by positivity : 0 ≤ 8*shrinkingNewtonSourceKappa^4)
        (by norm_num [shrinkingNewtonSourceKappa])).mul_left (64*shrinkingNewtonSourceKappa⁻¹^2))
  exact (summable_nat_add_iff 1).mp hs

/-- The entire bounded core behind the actual two-axis gauge row. -/
def variableGaugeRowFactor (P R Q S : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R)
    (hQ : 1 ≤ Q) (hS : 1 ≤ S) : SeamMomentArray →L[ℂ] SeamMomentArray :=
  ∑' n, variableGaugeFactoredTerm P R Q S hP hR hQ hS n

/-- The retained complete row factor obeys the source's uniform constant 100. -/
theorem variableGaugeRowFactor_norm_le (P R Q S : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R)
    (hQ : 1 ≤ Q) (hS : 1 ≤ S) :
    ‖variableGaugeRowFactor P R Q S hP hR hQ hS‖ ≤ 100*shrinkingNewtonSourceKappa⁻¹^2 := by
  have hs := variableGaugeFactoredTerm_summable_norm P R Q S hP hR hQ hS
  have hg := (summable_geometric_of_lt_one (by positivity : 0 ≤ 8*shrinkingNewtonSourceKappa^4)
    (by norm_num [shrinkingNewtonSourceKappa])).mul_left (64*shrinkingNewtonSourceKappa⁻¹^2)
  have ht := (hs.comp_injective Nat.succ_injective).tsum_le_tsum
    (variableGaugeFactoredTerm_tail_bound P R Q S hP hR hQ hS) hg
  have h0 := variableGaugeFactoredTerm_bound P R Q S hP hR hQ hS 0
  unfold variableGaugeRowFactor
  calc
    _ ≤ ∑' n, ‖variableGaugeFactoredTerm P R Q S hP hR hQ hS n‖ := norm_tsum_le_tsum_norm hs
    _ = ‖variableGaugeFactoredTerm P R Q S hP hR hQ hS 0‖+
        ∑' n, ‖variableGaugeFactoredTerm P R Q S hP hR hQ hS (n+1)‖ := hs.tsum_eq_zero_add
    _ ≤ _ := by
      rw [tsum_mul_left,tsum_geometric_of_lt_one (by positivity) (by norm_num [shrinkingNewtonSourceKappa])] at ht
      norm_num [shrinkingNewtonSourceKappa] at h0 ht ⊢
      linarith

/-- The entire positive Taylor series has the actual complete gauge remainder as its sum. -/
theorem variableGaugeOperator_positive_hasSum (P R Q S : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R)
    (hQ : 1 ≤ Q) (hS : 1 ≤ S) :
    HasSum (fun n => halfNewtonGaugeCoefficient (n+1) •
      (variableCoordinateSourceRow P R hP hR * variableCoordinateSourceColumn Q S hQ hS)^(n+1))
      (variableGaugeOperator P R Q S hP hR hQ hS-1) := by
  let Z := variableGaugeGenerator P R Q S hP hR hQ hS
  have hZ : ‖Z‖ < 1 := (variableGaugeGenerator_norm_le P R Q S hP hR hQ hS).trans_lt
    (by norm_num [shrinkingNewtonSourceKappa])
  have hs := ((boundedOperatorSeries_summable_norm (fun n => (n.factorial:ℂ)⁻¹)
    inverseFactorial_norm_le_one Z hZ).of_norm.comp_injective Nat.succ_injective).hasSum
  have he : variableGaugeOperator P R Q S hP hR hQ hS-1 =
      ∑' n, ((n+1).factorial:ℂ)⁻¹ • Z^(n+1) := by
    rw [variableGaugeOperator,fullExponential_eq_series]
    simpa only [Nat.factorial_zero,Nat.cast_one,inv_one,one_smul] using
      boundedOperatorSeries_sub_constant (fun n => (n.factorial:ℂ)⁻¹)
        inverseFactorial_norm_le_one Z hZ
  have ht : (fun n => ((n+1).factorial:ℂ)⁻¹ • Z^(n+1)) =
      (fun n => halfNewtonGaugeCoefficient (n+1) •
        (variableCoordinateSourceRow P R hP hR * variableCoordinateSourceColumn Q S hQ hS)^(n+1)) := by
    funext n
    dsimp only [Z,variableGaugeGenerator]
    rw [smul_pow,smul_smul,halfNewtonGaugeCoefficient,div_eq_mul_inv]
    rw [mul_comm]
    rfl
  rw [ht] at he
  rw [he]
  rw [←ht]
  exact hs

/-- Exact full two-axis row factorization of the genuine exponential gauge.
Both phase weights are retained before summation, and the remaining operator
has the proved uniform bound; no inverse phase diagonal appears. -/
theorem variableGaugeOperator_row_factor (P R Q S : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R)
    (hQ : 1 ≤ Q) (hS : 1 ≤ S) :
    (momentProjection (seamRowParity true) * momentProjection {p : SeamMomentIndex | p.2.2=true}) *
      (variableGaugeOperator P R Q S hP hR hQ hS-1) =
    (variableNewtonRowWeight (rapidDistance P R) (shrinkingNewtonSourceKappa^4)
        (variableNewton_source_phase_bound P R hP hR) *
      variableNewtonColumnWeight (rapidDistance Q S) (shrinkingNewtonSourceKappa^4)
        (variableNewton_source_phase_bound Q S hQ hS)) *
      variableGaugeRowFactor P R Q S hP hR hQ hS := by
  let A := momentProjection (seamRowParity true) * momentProjection {p : SeamMomentIndex | p.2.2=true}
  let D := variableNewtonRowWeight (rapidDistance P R) (shrinkingNewtonSourceKappa^4)
      (variableNewton_source_phase_bound P R hP hR) *
    variableNewtonColumnWeight (rapidDistance Q S) (shrinkingNewtonSourceKappa^4)
      (variableNewton_source_phase_bound Q S hQ hS)
  have hleft := (operatorComposeLeft A).hasSum
    (variableGaugeOperator_positive_hasSum P R Q S hP hR hQ hS)
  have hright := (operatorComposeLeft D).hasSum
    (variableGaugeFactoredTerm_summable_norm P R Q S hP hR hQ hS).of_norm.hasSum
  have he : (fun n => operatorComposeLeft A (halfNewtonGaugeCoefficient (n+1) •
      (variableCoordinateSourceRow P R hP hR * variableCoordinateSourceColumn Q S hQ hS)^(n+1))) =
      (fun n => operatorComposeLeft D (variableGaugeFactoredTerm P R Q S hP hR hQ hS n)) := by
    funext n
    change A * (halfNewtonGaugeCoefficient (n+1) • _) = D * (halfNewtonGaugeCoefficient (n+1) • _)
    rw [mul_smul_comm,mul_smul_comm]
    congr 1
    exact (variableCoordinateSource_paired_power_factor P R Q S hP hR hQ hS n).choose_spec.1
  rw [he] at hleft
  exact hleft.unique hright

end
end MeyerGeneralProblem.Adaptive
