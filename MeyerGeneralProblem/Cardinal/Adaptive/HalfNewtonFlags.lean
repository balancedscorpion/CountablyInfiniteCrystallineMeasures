module

public import MeyerGeneralProblem.Cardinal.Adaptive.ZakClusterExtraction

@[expose] public section

/-! # Exact finite Fourier bands and whole-source Newton triangular flags -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open scoped BigOperators FourierTransform

/-- The positive extreme Fourier coefficient of the two half parities. -/
def halfNewtonParityPositive (e : Bool) : ℂ := if e then 1/(2*Complex.I) else 1/2

/-- The negative extreme Fourier coefficient of the two half parities. -/
def halfNewtonParityNegative (e : Bool) : ℂ := if e then -(1/(2*Complex.I)) else 1/2

private theorem half_character_euler (x : ℝ) :
    combModulationCharacter (1/2) x=(Real.cos (Real.pi*x) : ℂ)+Complex.I*(Real.sin (Real.pi*x) : ℂ) ∧
    combModulationCharacter (-1/2) x=(Real.cos (Real.pi*x) : ℂ)-Complex.I*(Real.sin (Real.pi*x) : ℂ) := by
  constructor
  · rw [combModulationCharacter_eq_exp,
      show 2*(Real.pi : ℂ)*Complex.I*((1/2 : ℝ) : ℂ)*(x : ℂ)=((Real.pi*x : ℝ) : ℂ)*Complex.I by push_cast; ring]
    rw [Complex.exp_mul_I]
    simp only [Complex.ofReal_cos,Complex.ofReal_sin]
    ring
  · rw [combModulationCharacter_eq_exp,
      show 2*(Real.pi : ℂ)*Complex.I*((-1/2 : ℝ) : ℂ)*(x : ℂ)=((-(Real.pi*x) : ℝ) : ℂ)*Complex.I by push_cast; ring]
    rw [Complex.exp_mul_I]
    simp only [Complex.ofReal_cos,Complex.ofReal_sin,Complex.ofReal_neg,Complex.cos_neg,Complex.sin_neg]
    ring

/-- Exact integer Fourier content of the characteristic-adjusted parity. -/
theorem halfNewtonParity_characteristic (e : Bool) (x : ℝ) :
    combModulationCharacter (-1/2) x *
      (if e then (Real.sin (Real.pi*x) : ℂ) else (Real.cos (Real.pi*x) : ℂ))=
    halfNewtonParityPositive e+halfNewtonParityNegative e*combModulationCharacter (-1) x := by
  obtain ⟨hp,hn⟩ := half_character_euler x
  have hzero := combModulationCharacter_add_left (-1/2) (1/2) x
  norm_num only [show (-1/2 : ℝ)+1/2=0 by ring,combModulationCharacter_zero_left] at hzero
  rw [show -(1/2 : ℝ)=(-1/2 : ℝ) by ring] at hzero
  have hone := combModulationCharacter_add_left (-1/2) (-1/2) x
  rw [show (-1/2 : ℝ)+(-1/2) = -1 by ring] at hone
  have hc : (Real.cos (Real.pi*x) : ℂ)=
      (combModulationCharacter (1/2) x+combModulationCharacter (-1/2) x)/2 := by rw [hp,hn]; ring
  have hs : (Real.sin (Real.pi*x) : ℂ)=
      (combModulationCharacter (1/2) x-combModulationCharacter (-1/2) x)/(2*Complex.I) := by
    rw [hp,hn]
    field_simp
    ring
  cases e
  · simp only [halfNewtonParityPositive,halfNewtonParityNegative,Bool.false_eq_true,ite_false]
    rw [hc,hone]
    linear_combination (-1/2 : ℂ)*hzero
  · simp only [halfNewtonParityPositive,halfNewtonParityNegative,ite_true]
    rw [hs,hone]
    field_simp
    simp only [neg_div] at hzero ⊢
    linear_combination (-1 : ℂ)*hzero

/-- The ordered Newton product is the exact previously normalized finite head
symbol, with its actual initial phase sequence. -/
theorem halfNewtonProduct_eq_head (ε : ℕ+ → ℝ) (j : ℕ) (x : ℝ) :
    halfNewtonProduct ε j x=criticalHeadTrigProduct (criticalPrefixPhases ε j) x := by
  simp only [halfNewtonProduct,criticalHeadTrigProduct,criticalPrefixPhases]
  exact (Fin.prod_univ_eq_prod_range _ _).symm

/-- The characteristic-adjusted column test has its exact finite Fourier
expansion. Both endpoint characters and both parity coefficients are retained. -/
theorem halfNewtonTest_characteristic_expansion (ε : ℕ+ → ℝ) (j : ℕ) (e : Bool) :
    combSchwartzModulation (-1/2) (halfNewtonTest ε j e)=
      ∑ r : Fin (Fintype.card (Fin j × Bool)+1),
        criticalHeadDifferenceCoeff (criticalPrefixPhases ε j) r •
          (halfNewtonParityPositive e • zakChartFourierProbe ((r : ℤ)-(j : ℤ))+
           halfNewtonParityNegative e • zakChartFourierProbe ((r : ℤ)-(j : ℤ)-1)) := by
  ext x
  simp only [combSchwartzModulation_apply,halfNewtonTest_apply,halfNewtonFunction,
    _root_.sum_apply,_root_.smul_apply,_root_.add_apply,smul_eq_mul,zakChartFourierProbe,
    combSchwartzModulation_apply]
  have hchar (n : ℤ) : criticalCharacter n x=combModulationCharacter (n : ℝ) x := by
    simp only [criticalCharacter,combModulationCharacter_eq_exp,Complex.ofReal_intCast]
  have hshift (n : ℤ) : combModulationCharacter ((n-1 : ℤ) : ℝ) x=
      combModulationCharacter (-1) x*combModulationCharacter (n : ℝ) x := by
    rw [show ((n-1 : ℤ) : ℝ)=(-1 : ℝ)+(n : ℝ) by push_cast; ring,
      combModulationCharacter_add_left]
  calc
    _ = zakCentralCutoff x *
        (combModulationCharacter (-1/2) x *
          (if e then (Real.sin (Real.pi*x) : ℂ) else (Real.cos (Real.pi*x) : ℂ))) *
          halfNewtonProduct ε j x := by ring
    _ = zakCentralCutoff x *
        (halfNewtonParityPositive e+halfNewtonParityNegative e*combModulationCharacter (-1) x) *
          (∑ r : Fin (Fintype.card (Fin j × Bool)+1),
            criticalHeadDifferenceCoeff (criticalPrefixPhases ε j) r * criticalCharacter ((r : ℤ)-(j : ℤ)) x) := by
      rw [halfNewtonParity_characteristic,halfNewtonProduct_eq_head,criticalHeadDifferenceCoeff_symbol]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      rw [hchar,hshift]
      ring

/-- Every true Newton coordinate above the permitted physical triangular flag
vanishes. The proof combines actual cluster extraction with the complete
finite Fourier expansion, including both parity branches. -/
theorem halfNewtonCoordinate_upper_flag (α β : ℕ+ → ℝ)
    (hia : ∀ j, 0 < α j ∧ α j < 1/2) (hib : ∀ j, 0 < β j ∧ β j < 1/2)
    (hsmall : ∀ j, 1/4 ≤ β j) (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier ((criticalPhaseTailCarrier α hia 0 0).translate (-1/2)) T)
    (hFT : AtomicOnCarrier ((criticalPhaseTailCarrier β hib 0 0).translate (-1/2)) (𝓕 T))
    (i j : ℕ) (e f : Bool) (hij : j < i) :
    halfNewtonCoordinate (fun l => 1/2-α l) (fun l => 1/2-β l) T i e j f=0 := by
  unfold halfNewtonCoordinate halfNewtonBilinear
  rw [halfNewtonTest_characteristic_expansion]
  rw [← zakTensorSlice_apply,map_sum]
  apply Finset.sum_eq_zero
  intro r _
  rw [map_smul,map_add,map_smul,map_smul]
  have hr : (r : ℕ) ≤ 2*j := by
    have hh := r.isLt
    simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool] at hh
    omega
  have hfirst : ((r : ℤ)-(j : ℤ)).natAbs ≤ i ∧ (((r : ℤ)-(j : ℤ))+1).natAbs ≤ i := by omega
  have hsecond : ((r : ℤ)-(j : ℤ)-1).natAbs ≤ i ∧ (((r : ℤ)-(j : ℤ)-1)+1).natAbs ≤ i := by omega
  rw [zakTensorSlice_apply,zakTensorSlice_apply,
    halfNewtonRow_chartFourierProbe_zero α β hia hib hsmall T hT hFT i e _ hfirst.1 hfirst.2,
    halfNewtonRow_chartFourierProbe_zero α β hia hib hsmall T hT hFT i e _ hsecond.1 hsecond.2]
  simp only [smul_zero,zero_add]

/-- The fixed source normalization preserves the exact upper triangular flag. -/
theorem halfNewtonMoment_upper_flag (α β : ℕ+ → ℝ)
    (hia : ∀ j, 0 < α j ∧ α j < 1/2) (hib : ∀ j, 0 < β j ∧ β j < 1/2)
    (hsmall : ∀ j, 1/4 ≤ β j) (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier ((criticalPhaseTailCarrier α hia 0 0).translate (-1/2)) T)
    (hFT : AtomicOnCarrier ((criticalPhaseTailCarrier β hib 0 0).translate (-1/2)) (𝓕 T))
    (i j : ℕ) (e f : Bool) (hij : j < i) :
    halfNewtonMoment (fun l => 1/2-α l) (fun l => 1/2-β l) T i e j f=0 := by
  rw [halfNewtonMoment_eq_zero_iff]
  exact halfNewtonCoordinate_upper_flag α β hia hib hsmall T hT hFT i j e f hij

end
end MeyerGeneralProblem.Adaptive
