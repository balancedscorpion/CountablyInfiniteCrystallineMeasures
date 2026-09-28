module

public import MeyerGeneralProblem.Cardinal.Adaptive.EndpointPoissonSource
public import MeyerGeneralProblem.Cardinal.Adaptive.CriticalForwardKernel

@[expose] public section

/-! # Whole bilateral recurrence on finite endpoint cosets -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open scoped FourierTransform BigOperators

/-- Negative Fourier roots match the transpose convention of whole distributions. -/
def endpointPolynomial {k : ℕ} (β : Fin k → ℝ) : Polynomial ℂ :=
  Lagrange.nodal Finset.univ (fun b => criticalCharacter 1 (-endpointPhase β b))

/-- Coefficients of the full simple-root Fourier annihilator polynomial. -/
def endpointDifferenceCoeff {k : ℕ} (β : Fin k → ℝ)
    (i : Fin (Fintype.card (EndpointPhaseIndex k)+1)) : ℂ :=
  (endpointPolynomial β).coeff i

/-- The finite integer-translation operator with the exact annihilator coefficients. -/
def endpointDifferenceTest {k : ℕ} (β : Fin k → ℝ) :
    SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
  ∑ i : Fin (Fintype.card (EndpointPhaseIndex k)+1), endpointDifferenceCoeff β i •
    combSchwartzTranslation (i.val : ℝ)

theorem endpointDifferenceCoeff_extremes {k : ℕ} (β : Fin k → ℝ) :
    endpointDifferenceCoeff β 0 ≠ 0 ∧
    endpointDifferenceCoeff β (Fin.last (Fintype.card (EndpointPhaseIndex k))) ≠ 0 := by
  constructor
  · simp only [endpointDifferenceCoeff,Fin.val_zero,Polynomial.coeff_zero_eq_eval_zero,
      endpointPolynomial,Lagrange.eval_nodal,sub_eq_add_neg,zero_add]
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact neg_ne_zero.mpr (Complex.exp_ne_zero _)
  · have he := (Lagrange.nodal_monic (s := Finset.univ)
      (v := fun b => criticalCharacter 1 (-endpointPhase β b))).coeff_natDegree
    have ht : endpointDifferenceCoeff β (Fin.last (Fintype.card (EndpointPhaseIndex k)))=1 := by
      simpa [endpointDifferenceCoeff,endpointPolynomial,Lagrange.natDegree_nodal] using he
    rw [ht]
    exact one_ne_zero

theorem endpointCharacter_integer_periodic (x : ℝ) (n : ℤ) :
    criticalCharacter 1 (x+n)=criticalCharacter 1 x := by
  unfold criticalCharacter
  have he : 2*(Real.pi : ℂ)*Complex.I*(1 : ℤ)*(x+(n : ℝ)) =
      2*(Real.pi : ℂ)*Complex.I*(1 : ℤ)*x+(n : ℂ)*(2*Real.pi*Complex.I) := by
    push_cast
    ring
  push_cast
  rw [show 2*(Real.pi : ℂ)*Complex.I*1*(x+(n : ℂ))=
      2*(Real.pi : ℂ)*Complex.I*1*x+(n : ℂ)*(2*Real.pi*Complex.I) by ring,
    Complex.exp_add,Complex.exp_int_mul_two_pi_mul_I,mul_one]

theorem endpointDifference_symbol {k : ℕ} (β : Fin k → ℝ) (x : ℝ) :
    ∑ i : Fin (Fintype.card (EndpointPhaseIndex k)+1),
      endpointDifferenceCoeff β i*criticalCharacter (i.val : ℤ) x =
        (endpointPolynomial β).eval (criticalCharacter 1 x) := by
  have he := Polynomial.eval_eq_sum_range (p := endpointPolynomial β) (criticalCharacter 1 x)
  simp only [endpointPolynomial,Lagrange.natDegree_nodal,Finset.card_univ] at he
  rw [← Fin.sum_univ_eq_sum_range] at he
  simpa only [endpointDifferenceCoeff,endpointPolynomial,endpointCharacter_nat] using he.symm

theorem endpointDifference_fourier_apply {k : ℕ} (β : Fin k → ℝ)
    (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    𝓕 (endpointDifferenceTest β f) x =
      (endpointPolynomial β).eval (criticalCharacter 1 x)*𝓕 f x := by
  have hm (n : ℕ) : combModulationCharacter (n : ℝ) x=criticalCharacter (n : ℤ) x := by
    rw [combModulationCharacter_eq_exp]
    simp [criticalCharacter]
  change (FourierTransform.fourierCLM ℂ (SchwartzMap ℝ ℂ)) (endpointDifferenceTest β f) x=_
  simp only [endpointDifferenceTest,_root_.sum_apply,_root_.smul_apply,map_sum,map_smul,
    FourierTransform.fourierCLM_apply,smul_eq_mul,fourier_combSchwartzTranslation,hm,
    ← mul_assoc,← Finset.sum_mul,endpointDifference_symbol]

/-- Every whole source with the actual spectral record annihilates this exact
finite difference of every Schwartz test. -/
theorem endpointDifference_annihilated {k : ℕ} (β : Fin k → ℝ)
    (T : TemperedDistribution ℝ ℂ) (hFT : AtomicOnCarrier (endpointCosetCarrier β) (𝓕 T))
    (f : SchwartzMap ℝ ℂ) : T (endpointDifferenceTest β f)=0 := by
  have he : T (endpointDifferenceTest β f)=𝓕 T (𝓕⁻ (endpointDifferenceTest β f)) := by
    change _=T (𝓕 (𝓕⁻ (endpointDifferenceTest β f)))
    rw [FourierTransform.fourier_fourierInv_eq]
  rw [he]
  apply hFT
  rintro x ⟨b,n,rfl⟩
  change 𝓕 (endpointDifferenceTest β f) (-(endpointPhase β b+(n : ℝ)))=0
  rw [endpointDifference_fourier_apply]
  have hc : criticalCharacter 1 (-(endpointPhase β b+(n : ℝ)))=
      criticalCharacter 1 (-endpointPhase β b) := by
    convert endpointCharacter_integer_periodic (-endpointPhase β b) (-n) using 1 <;> push_cast <;> ring
  rw [hc]
  have hz : (endpointPolynomial β).eval (criticalCharacter 1 (-endpointPhase β b))=0 :=
    Lagrange.eval_nodal_at_node (v := fun a => criticalCharacter 1 (-endpointPhase β a)) (Finset.mem_univ b)
  rw [hz,zero_mul]

/-- Actual whole-source recurrence at every integer translate, without
finite-support, decay or solution-form assumptions. -/
theorem endpoint_test_recurrence {k : ℕ} (β : Fin k → ℝ)
    (T : TemperedDistribution ℝ ℂ) (hFT : AtomicOnCarrier (endpointCosetCarrier β) (𝓕 T))
    (f : SchwartzMap ℝ ℂ) (n : ℤ) :
    ∑ i : Fin (Fintype.card (EndpointPhaseIndex k)+1), endpointDifferenceCoeff β i*
      T (combSchwartzTranslation ((n+(i.val : ℤ) : ℤ) : ℝ) f)=0 := by
  have he := endpointDifference_annihilated β T hFT (combSchwartzTranslation (n : ℝ) f)
  simp only [endpointDifferenceTest,_root_.sum_apply,_root_.smul_apply,map_sum,map_smul,
    smul_eq_mul] at he
  convert he using 1
  apply Finset.sum_congr rfl
  intro i _
  congr 2
  ext x
  simp only [combSchwartzTranslation_apply,Int.cast_add]
  congr 1
  push_cast
  ring

end
end MeyerGeneralProblem.Adaptive
