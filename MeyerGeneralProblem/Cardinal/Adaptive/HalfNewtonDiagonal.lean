module

public import MeyerGeneralProblem.Cardinal.Adaptive.HalfNewtonFlags

@[expose] public section

/-! # Actual extreme-cluster readings on the Newton diagonal -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open scoped BigOperators FourierTransform

/-- A complete source reading at one signed physical cluster, using the actual
characteristic-adjusted Newton row test. -/
def halfNewtonClusterReading (ε : ℕ+ → ℝ) (T : TemperedDistribution ℝ ℂ)
    (i : ℕ) (e : Bool) (m : ℤ) : ℂ :=
  T (combSchwartzTranslation (-(m : ℝ)) (combSchwartzModulation (1/2) (halfNewtonTest ε i e)))

/-- Both literal extreme Laurent coefficients have exactly the same scalar,
including the empty product at level zero. -/
theorem criticalHeadDifferenceCoeff_extreme_values {i : ℕ} (α : Fin i → ℝ) :
    criticalHeadDifferenceCoeff α 0=(-1/2 : ℂ)^i ∧
    criticalHeadDifferenceCoeff α (Fin.last (Fintype.card (Fin i × Bool)))=(-1/2 : ℂ)^i := by
  have hzero : (criticalHeadPolynomial α).coeff 0=1 := by
    rw [Polynomial.coeff_zero_eq_eval_zero,criticalHeadPolynomial_factorization,Polynomial.eval_prod]
    simp
  have htop : (criticalHeadPolynomial α).coeff (Fintype.card (Fin i × Bool))=1 := by
    simpa [criticalHeadPolynomial] using
      (Lagrange.nodal_monic (s := Finset.univ) (v := criticalHeadRoots α)).coeff_natDegree
  constructor <;> simp only [criticalHeadDifferenceCoeff,Fin.val_zero,Fin.val_last,hzero,htop,mul_one]

/-- Every actual diagonal Newton coordinate depends on exactly the two extreme
clusters, with their genuine parity coefficients and Fourier signs. -/
theorem halfNewtonCoordinate_diagonal_clusters (α β : ℕ+ → ℝ)
    (hia : ∀ j, 0 < α j ∧ α j < 1/2) (hib : ∀ j, 0 < β j ∧ β j < 1/2)
    (hsmall : ∀ j, 1/4 ≤ β j) (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier ((criticalPhaseTailCarrier α hia 0 0).translate (-1/2)) T)
    (hFT : AtomicOnCarrier ((criticalPhaseTailCarrier β hib 0 0).translate (-1/2)) (𝓕 T))
    (i : ℕ) (e f : Bool) :
    halfNewtonCoordinate (fun l => 1/2-α l) (fun l => 1/2-β l) T i e i f=
      (-1/2 : ℂ)^i *
        (halfNewtonParityPositive f*halfNewtonClusterReading (fun l => 1/2-α l) T i e (i : ℤ)+
         halfNewtonParityNegative f*halfNewtonClusterReading (fun l => 1/2-α l) T i e (-(i : ℤ)-1)) := by
  let row := combSchwartzModulation (1/2) (halfNewtonTest (fun l => 1/2-α l) i e)
  let reading (m : ℤ) := zakTensorAction T row (zakChartFourierProbe m)
  let coeff := criticalHeadDifferenceCoeff (criticalPrefixPhases (fun l => 1/2-β l) i)
  have hz (m : ℤ) (hm : m.natAbs ≤ i) (hm' : (m+1).natAbs ≤ i) : reading m=0 :=
    halfNewtonRow_chartFourierProbe_zero α β hia hib hsmall T hT hFT i e m hm hm'
  have hp : (∑ r : Fin (Fintype.card (Fin i × Bool)+1),
      coeff r * halfNewtonParityPositive f * reading ((r : ℤ)-(i : ℤ)))=
      (-1/2 : ℂ)^i * halfNewtonParityPositive f * reading (i : ℤ) := by
    rw [Finset.sum_eq_single (Fin.last (Fintype.card (Fin i × Bool)))]
    · dsimp only [coeff]
      rw [(criticalHeadDifferenceCoeff_extreme_values _).2]
      congr 1
      congr 1
      simp only [Fin.val_last,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool]
      push_cast
      ring
    · intro r _ hr
      have hrlt : (r : ℕ) < 2*i := by
        have h := r.isLt
        have hn : (r : ℕ) ≠ Fintype.card (Fin i × Bool) := by
          intro he
          apply hr
          exact Fin.ext he
        simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool] at h hn
        omega
      rw [hz _ (by omega) (by omega),mul_zero]
    · simp
  have hn : (∑ r : Fin (Fintype.card (Fin i × Bool)+1),
      coeff r * halfNewtonParityNegative f * reading ((r : ℤ)-(i : ℤ)-1))=
      (-1/2 : ℂ)^i * halfNewtonParityNegative f * reading (-(i : ℤ)-1) := by
    rw [Finset.sum_eq_single (0 : Fin (Fintype.card (Fin i × Bool)+1))]
    · dsimp only [coeff]
      rw [(criticalHeadDifferenceCoeff_extreme_values _).1]
      simp only [Fin.val_zero,Nat.cast_zero,zero_sub]
    · intro r _ hr
      have hrpos : 0 < (r : ℕ) := by
        have hn : (r : ℕ) ≠ 0 := by intro he; apply hr; exact Fin.ext he
        omega
      have hrle : (r : ℕ) ≤ 2*i := by
        have h := r.isLt
        simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool] at h
        omega
      rw [hz _ (by omega) (by omega),mul_zero]
    · simp
  have hexp : halfNewtonCoordinate (fun l => 1/2-α l) (fun l => 1/2-β l) T i e i f=
      (∑ r : Fin (Fintype.card (Fin i × Bool)+1),
        coeff r * halfNewtonParityPositive f * reading ((r : ℤ)-(i : ℤ)))+
      (∑ r : Fin (Fintype.card (Fin i × Bool)+1),
        coeff r * halfNewtonParityNegative f * reading ((r : ℤ)-(i : ℤ)-1)) := by
    unfold halfNewtonCoordinate halfNewtonBilinear
    rw [halfNewtonTest_characteristic_expansion,← zakTensorSlice_apply,map_sum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r _
    simp only [map_smul,map_add,smul_eq_mul,zakTensorSlice_apply]
    change _ = coeff r * halfNewtonParityPositive f * reading ((r : ℤ)-(i : ℤ))+
      coeff r * halfNewtonParityNegative f * reading ((r : ℤ)-(i : ℤ)-1)
    dsimp only [coeff,reading,row]
    ring
  rw [hexp,hp,hn]
  have hreading (m : ℤ) : reading m=halfNewtonClusterReading (fun l => 1/2-α l) T i e m :=
    zakTensorAction_chartFourierProbe β hib hsmall T hFT row m
  rw [hreading,hreading]
  ring

private theorem cluster_parity_relation (α : ℕ+ → ℝ)
    (hia : ∀ j, 0 < α j ∧ α j < 1/2) (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier ((criticalPhaseTailCarrier α hia 0 0).translate (-1/2)) T)
    (i : ℕ) (m : ℤ) (t : ℂ)
    (hminus : ∀ j : ℕ+, (j : ℕ) ≤ m.natAbs →
      halfNewtonProduct (fun l => 1/2-α l) i (-(1/2-α j))=0 ∨
      (Real.sin (Real.pi*(-(1/2-α j))) : ℂ)=t*(Real.cos (Real.pi*(-(1/2-α j))) : ℂ))
    (hplus : ∀ j : ℕ+, (j : ℕ) ≤ (m+1).natAbs →
      halfNewtonProduct (fun l => 1/2-α l) i (1/2-α j)=0 ∨
      (Real.sin (Real.pi*(1/2-α j)) : ℂ)=t*(Real.cos (Real.pi*(1/2-α j)) : ℂ)) :
    halfNewtonClusterReading (fun l => 1/2-α l) T i true m=
      t*halfNewtonClusterReading (fun l => 1/2-α l) T i false m := by
  let u := halfNewtonTest (fun l => 1/2-α l) i true-t •halfNewtonTest (fun l => 1/2-α l) i false
  have he (x : ℝ) : u x=zakCentralCutoff x*
      ((Real.sin (Real.pi*x) : ℂ)-t*(Real.cos (Real.pi*x) : ℂ))*
      halfNewtonProduct (fun l => 1/2-α l) i x := by
    simp only [u,_root_.sub_apply,_root_.smul_apply,smul_eq_mul,halfNewtonTest_apply,
      halfNewtonFunction,ite_true,Bool.false_eq_true,ite_false]
    ring
  have hz := halfWeylSource_cluster_zero α hia T hT (combSchwartzModulation (1/2) u)
    (by intro x hx; rw [combSchwartzModulation_apply,he,zakCentralCutoff_zero x hx,zero_mul,zero_mul,mul_zero]) m
    (by
      intro j hj
      rw [combSchwartzModulation_apply,he]
      rcases hminus j hj with hd|hp
      · rw [hd,mul_zero,mul_zero]
      · rw [hp,sub_self,mul_zero,zero_mul,mul_zero])
    (by
      intro j hj
      rw [combSchwartzModulation_apply,he]
      rcases hplus j hj with hd|hp
      · rw [hd,mul_zero,mul_zero]
      · rw [hp,sub_self,mul_zero,zero_mul,mul_zero])
  simp only [u,map_sub,map_smul,smul_eq_mul] at hz
  exact sub_eq_zero.mp hz

/-- The two actual surviving endpoint clusters have opposite tangent parity
ratios. No division by a Newton product or atomic coefficient is used. -/
theorem halfNewtonClusterReading_extreme_parities (α : ℕ+ → ℝ)
    (hia : ∀ j, 0 < α j ∧ α j < 1/2) (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier ((criticalPhaseTailCarrier α hia 0 0).translate (-1/2)) T)
    (i : ℕ) :
    halfNewtonClusterReading (fun l => 1/2-α l) T i true (i : ℤ)=
      (Real.tan (Real.pi*(1/2-α ⟨i+1,Nat.succ_pos i⟩)) : ℂ)*
        halfNewtonClusterReading (fun l => 1/2-α l) T i false (i : ℤ) ∧
    halfNewtonClusterReading (fun l => 1/2-α l) T i true (-(i : ℤ)-1)=
      -(Real.tan (Real.pi*(1/2-α ⟨i+1,Nat.succ_pos i⟩)) : ℂ)*
        halfNewtonClusterReading (fun l => 1/2-α l) T i false (-(i : ℤ)-1) := by
  let a := 1/2-α ⟨i+1,Nat.succ_pos i⟩
  have ha : 0<a ∧ a<1/2 := by dsimp only [a]; constructor <;> linarith [(hia ⟨i+1,Nat.succ_pos i⟩).1,(hia ⟨i+1,Nat.succ_pos i⟩).2]
  have hc : Real.cos (Real.pi*a) ≠ 0 := ne_of_gt (Real.cos_pos_of_mem_Ioo (by
    constructor <;> nlinarith [Real.pi_pos]))
  have hp : (Real.sin (Real.pi*a) : ℂ)=
      (Real.tan (Real.pi*a) : ℂ)*(Real.cos (Real.pi*a) : ℂ) := by
    rw [Real.tan_eq_sin_div_cos,Complex.ofReal_div,div_mul_cancel₀ _ (by exact_mod_cast hc)]
  have hn : (Real.sin (Real.pi*(-a)) : ℂ)=
      -(Real.tan (Real.pi*a) : ℂ)*(Real.cos (Real.pi*(-a)) : ℂ) := by
    rw [mul_neg,Real.sin_neg,Real.cos_neg,Complex.ofReal_neg,hp]
    ring
  constructor
  · apply cluster_parity_relation α hia T hT
    · intro j hj
      exact Or.inl (halfNewtonProduct_neg_phase_zero _ i j (by simpa only [Int.natAbs_natCast] using hj))
    · intro j hj
      by_cases hj0 : (j : ℕ) ≤ i
      · exact Or.inl (halfNewtonProduct_phase_zero _ i j hj0)
      · have hj1 : j=⟨i+1,Nat.succ_pos i⟩ := by apply Subtype.ext; change (j : ℕ)=i+1; omega
        rw [hj1]
        exact Or.inr hp
  · apply cluster_parity_relation α hia T hT
    · intro j hj
      by_cases hj0 : (j : ℕ) ≤ i
      · exact Or.inl (halfNewtonProduct_neg_phase_zero _ i j hj0)
      · have hj1 : j=⟨i+1,Nat.succ_pos i⟩ := by apply Subtype.ext; change (j : ℕ)=i+1; omega
        rw [hj1]
        exact Or.inr hn
    · intro j hj
      exact Or.inl (halfNewtonProduct_phase_zero _ i j (by omega))

/-- The two exact physical diagonal equations before normalization, derived
from the actual extreme clusters and their opposite tangent ratios. -/
theorem halfNewtonCoordinate_diagonal_relations (α β : ℕ+ → ℝ)
    (hia : ∀ j, 0 < α j ∧ α j < 1/2) (hib : ∀ j, 0 < β j ∧ β j < 1/2)
    (hsmall : ∀ j, 1/4 ≤ β j) (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier ((criticalPhaseTailCarrier α hia 0 0).translate (-1/2)) T)
    (hFT : AtomicOnCarrier ((criticalPhaseTailCarrier β hib 0 0).translate (-1/2)) (𝓕 T))
    (i : ℕ) :
    halfNewtonCoordinate (fun l => 1/2-α l) (fun l => 1/2-β l) T i true i false=
      Complex.I*(Real.tan (Real.pi*(1/2-α ⟨i+1,Nat.succ_pos i⟩)) : ℂ)*
        halfNewtonCoordinate (fun l => 1/2-α l) (fun l => 1/2-β l) T i false i true ∧
    halfNewtonCoordinate (fun l => 1/2-α l) (fun l => 1/2-β l) T i true i true=
      -Complex.I*(Real.tan (Real.pi*(1/2-α ⟨i+1,Nat.succ_pos i⟩)) : ℂ)*
        halfNewtonCoordinate (fun l => 1/2-α l) (fun l => 1/2-β l) T i false i false := by
  obtain ⟨hp,hn⟩ := halfNewtonClusterReading_extreme_parities α hia T hT i
  simp only [halfNewtonCoordinate_diagonal_clusters α β hia hib hsmall T hT hFT,
    hp,hn,halfNewtonParityPositive,halfNewtonParityNegative,ite_true,Bool.false_eq_true,ite_false]
  constructor <;> field_simp
  all_goals ring_nf
  all_goals simp [Complex.I_sq]

/-- The exact fixed-normalized physical diagonal equations, including the
factor 1/R in parity 11. Here R=1/4096 is the source's prescribed scale. -/
theorem halfNewtonMoment_diagonal_relations (α β : ℕ+ → ℝ)
    (hia : ∀ j, 0 < α j ∧ α j < 1/2) (hib : ∀ j, 0 < β j ∧ β j < 1/2)
    (hsmall : ∀ j, 1/4 ≤ β j) (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier ((criticalPhaseTailCarrier α hia 0 0).translate (-1/2)) T)
    (hFT : AtomicOnCarrier ((criticalPhaseTailCarrier β hib 0 0).translate (-1/2)) (𝓕 T))
    (i : ℕ) :
    halfNewtonMoment (fun l => 1/2-α l) (fun l => 1/2-β l) T i true i false=
      Complex.I*(Real.tan (Real.pi*(1/2-α ⟨i+1,Nat.succ_pos i⟩)) : ℂ)*
        halfNewtonMoment (fun l => 1/2-α l) (fun l => 1/2-β l) T i false i true ∧
    halfNewtonMoment (fun l => 1/2-α l) (fun l => 1/2-β l) T i true i true=
      (-Complex.I*(Real.tan (Real.pi*(1/2-α ⟨i+1,Nat.succ_pos i⟩)) : ℂ)/(1/4096 : ℂ))*
        halfNewtonMoment (fun l => 1/2-α l) (fun l => 1/2-β l) T i false i false := by
  obtain ⟨hp,hn⟩ := halfNewtonCoordinate_diagonal_relations α β hia hib hsmall T hT hFT i
  simp only [halfNewtonMoment,hp,hn,Bool.toNat_true,Bool.toNat_false]
  constructor
  · norm_num
    ring
  · norm_num [mul_inv_rev]
    ring

end
end MeyerGeneralProblem.Adaptive
