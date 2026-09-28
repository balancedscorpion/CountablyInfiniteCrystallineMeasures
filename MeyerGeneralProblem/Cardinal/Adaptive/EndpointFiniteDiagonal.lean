module

public import MeyerGeneralProblem.Cardinal.Adaptive.EndpointFiniteFlags

@[expose] public section

/-! Exact diagonal constraints of complete finite endpoint Newton sources. -/
noncomputable section
open scoped BigOperators FourierTransform
namespace MeyerGeneralProblem.Adaptive

/-- Finite endpoint diagonal coordinates retain exactly the two extreme clusters. -/
theorem endpointNewtonCoordinate_diagonal_clusters {P R : ℕ} (hP : 1 ≤ P) (hR : 1 ≤ R)
    (k : ℕ) (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier ((endpointDeletedCarrier (rapidEndpointPhaseData P R k)).translate (-1/2)) T)
    (hFT : AtomicOnCarrier ((endpointDeletedCarrier (rapidEndpointPhaseData P R k)).translate (-1/2)) (𝓕 T))
    (i : ℕ) (e f : Bool) :
    halfNewtonCoordinate (endpointPaddedDistance P R k) (endpointPaddedDistance P R k) T i e i f=
      (-1/2 : ℂ)^i *
        (halfNewtonParityPositive f*halfNewtonClusterReading (endpointPaddedDistance P R k) T i e (i:ℤ)+
         halfNewtonParityNegative f*halfNewtonClusterReading (endpointPaddedDistance P R k) T i e (-(i:ℤ)-1)) := by
  let row := combSchwartzModulation (1/2) (halfNewtonTest (endpointPaddedDistance P R k) i e)
  let reading (m : ℤ) := zakTensorAction T row (zakChartFourierProbe m)
  let coeff := criticalHeadDifferenceCoeff (criticalPrefixPhases (endpointPaddedDistance P R k) i)
  have hz (m : ℤ) (hm : m.natAbs ≤ i) (hm' : (m+1).natAbs ≤ i) : reading m=0 :=
    endpointNewtonRow_chartProbe_zero hP hR k T hT hFT i e m hm hm'
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
  have hexp : halfNewtonCoordinate (endpointPaddedDistance P R k) (endpointPaddedDistance P R k) T i e i f=
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
  have hreading (m : ℤ) : reading m=halfNewtonClusterReading (endpointPaddedDistance P R k) T i e m :=
    zakTensorAction_endpoint_chartProbe _ (rapidEndpointPhaseData_injective hP hR k)
      (rapidEndpointPhaseData_interior hP hR k) (fun j => by
        unfold rapidEndpointPhaseData
        linarith [(rapidDistance_bounds hP hR (j.val+1)).2]) T hFT row m
  rw [hreading,hreading]
  ring

private theorem endpoint_cluster_parity_relation {P R : ℕ} (hP : 1 ≤ P) (hR : 1 ≤ R)
    (k : ℕ) (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier ((endpointDeletedCarrier (rapidEndpointPhaseData P R k)).translate (-1/2)) T)
    (i : ℕ) (m : ℤ) (t : ℂ)
    (hminus : ∀ j : Fin k, j.val < m.natAbs →
      halfNewtonProduct (endpointPaddedDistance P R k) i (-(1/2-rapidEndpointPhaseData P R k j))=0 ∨
      (Real.sin (Real.pi*(-(1/2-rapidEndpointPhaseData P R k j))) : ℂ)=
        t*(Real.cos (Real.pi*(-(1/2-rapidEndpointPhaseData P R k j))) : ℂ))
    (hplus : ∀ j : Fin k, j.val < (m+1).natAbs →
      halfNewtonProduct (endpointPaddedDistance P R k) i (1/2-rapidEndpointPhaseData P R k j)=0 ∨
      (Real.sin (Real.pi*(1/2-rapidEndpointPhaseData P R k j)) : ℂ)=
        t*(Real.cos (Real.pi*(1/2-rapidEndpointPhaseData P R k j)) : ℂ))
    (hseam : (m < -(k:ℤ) ∨ (k:ℤ) ≤ m) →
      halfNewtonProduct (endpointPaddedDistance P R k) i 0=0 ∨ t=0) :
    halfNewtonClusterReading (endpointPaddedDistance P R k) T i true m=
      t*halfNewtonClusterReading (endpointPaddedDistance P R k) T i false m := by
  let u := halfNewtonTest (endpointPaddedDistance P R k) i true-t •halfNewtonTest (endpointPaddedDistance P R k) i false
  have he (x : ℝ) : u x=zakCentralCutoff x*
      ((Real.sin (Real.pi*x) : ℂ)-t*(Real.cos (Real.pi*x) : ℂ))*
      halfNewtonProduct (endpointPaddedDistance P R k) i x := by
    simp only [u,_root_.sub_apply,_root_.smul_apply,smul_eq_mul,halfNewtonTest_apply,
      halfNewtonFunction,ite_true,Bool.false_eq_true,ite_false]
    ring
  have hz := endpointSource_cluster_zero _ (rapidEndpointPhaseData_injective hP hR k)
    (rapidEndpointPhaseData_interior hP hR k) T hT (combSchwartzModulation (1/2) u)
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
    (by
      intro hs
      rw [combSchwartzModulation_apply,he]
      rcases hseam hs with hd|ht
      · rw [hd,mul_zero,mul_zero]
      · simp only [ht,mul_zero,Real.sin_zero,Complex.ofReal_zero,zero_mul,sub_self])
  simp only [u,map_sub,map_smul,smul_eq_mul] at hz
  exact sub_eq_zero.mp hz

/-- The two surviving finite endpoint clusters have the exact opposite tangent
ratios. At and beyond the cap the actual next phase is zero. -/
theorem endpointNewtonCluster_extreme_parities {P R : ℕ} (hP : 1 ≤ P) (hR : 1 ≤ R)
    (k : ℕ) (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier ((endpointDeletedCarrier (rapidEndpointPhaseData P R k)).translate (-1/2)) T)
    (i : ℕ) :
    halfNewtonClusterReading (endpointPaddedDistance P R k) T i true (i:ℤ)=
      (Real.tan (Real.pi*endpointPaddedDistance P R k ⟨i+1,by omega⟩) : ℂ)*
        halfNewtonClusterReading (endpointPaddedDistance P R k) T i false (i:ℤ) ∧
    halfNewtonClusterReading (endpointPaddedDistance P R k) T i true (-(i:ℤ)-1)=
      -(Real.tan (Real.pi*endpointPaddedDistance P R k ⟨i+1,by omega⟩) : ℂ)*
        halfNewtonClusterReading (endpointPaddedDistance P R k) T i false (-(i:ℤ)-1) := by
  let a := endpointPaddedDistance P R k ⟨i+1,by omega⟩
  have ha : 0 ≤ a ∧ a < 1/2 := by
    change 0 ≤ (if i+1 ≤ k then rapidDistance P R (i+1) else 0) ∧
      (if i+1 ≤ k then rapidDistance P R (i+1) else 0) < 1/2
    split_ifs
    · have hh := rapidDistance_bounds hP hR (i+1)
      exact ⟨hh.1.le,by linarith [hh.2]⟩
    · norm_num
  have hc : Real.cos (Real.pi*a) ≠ 0 := ne_of_gt (Real.cos_pos_of_mem_Ioo (by
    constructor <;> nlinarith [Real.pi_pos]))
  have hp : (Real.sin (Real.pi*a) : ℂ)=(Real.tan (Real.pi*a) : ℂ)*(Real.cos (Real.pi*a) : ℂ) := by
    rw [Real.tan_eq_sin_div_cos,Complex.ofReal_div,div_mul_cancel₀ _ (by exact_mod_cast hc)]
  have hn : (Real.sin (Real.pi*(-a)) : ℂ)= -(Real.tan (Real.pi*a) : ℂ)*(Real.cos (Real.pi*(-a)) : ℂ) := by
    rw [mul_neg,Real.sin_neg,Real.cos_neg,Complex.ofReal_neg,hp]
    ring
  have hphase (j : Fin k) : 1/2-rapidEndpointPhaseData P R k j=rapidDistance P R (j.val+1) := by
    unfold rapidEndpointPhaseData
    ring
  have hnext (j : Fin k) (hj : j.val=i) : 1/2-rapidEndpointPhaseData P R k j=a := by
    rw [hphase,hj]
    dsimp only [a,endpointPaddedDistance]
    exact (ite_eq_left (show (⟨i+1,by omega⟩ : ℕ+).val ≤ k by change i+1 ≤ k; omega)).symm
  have hzero (hi : k ≤ i) : a=0 := by
    dsimp only [a,endpointPaddedDistance]
    apply ite_eq_right
    change ¬ i+1 ≤ k
    omega
  constructor
  · apply endpoint_cluster_parity_relation hP hR k T hT i (i:ℤ)
    · intro j hj
      left
      rw [hphase]
      exact halfNewtonProduct_endpointPadded_phase_zero P R k i j (by simpa using hj) _ (Or.inr rfl)
    · intro j hj
      by_cases hj0 : j.val < i
      · left
        rw [hphase]
        exact halfNewtonProduct_endpointPadded_phase_zero P R k i j hj0 _ (Or.inl rfl)
      · right
        rw [hnext j (by omega)]
        exact hp
    · intro hs
      right
      change (Real.tan (Real.pi*a) : ℂ)=0
      rw [hzero (by omega)]
      simp
  · apply endpoint_cluster_parity_relation hP hR k T hT i (-(i:ℤ)-1)
    · intro j hj
      by_cases hj0 : j.val < i
      · left
        rw [hphase]
        exact halfNewtonProduct_endpointPadded_phase_zero P R k i j hj0 _ (Or.inr rfl)
      · right
        rw [hnext j (by omega)]
        exact hn
    · intro j hj
      left
      rw [hphase]
      exact halfNewtonProduct_endpointPadded_phase_zero P R k i j (by omega) _ (Or.inl rfl)
    · intro hs
      right
      change -(Real.tan (Real.pi*a) : ℂ)=0
      rw [hzero (by omega)]
      simp
/-- The two exact physical diagonal equations before normalization, derived
from the actual extreme clusters and their opposite tangent ratios. -/
theorem endpointNewtonCoordinate_diagonal_relations {P R : ℕ} (hP : 1 ≤ P) (hR : 1 ≤ R)
    (k : ℕ) (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier ((endpointDeletedCarrier (rapidEndpointPhaseData P R k)).translate (-1/2)) T)
    (hFT : AtomicOnCarrier ((endpointDeletedCarrier (rapidEndpointPhaseData P R k)).translate (-1/2)) (𝓕 T))
    (i : ℕ) :
    halfNewtonCoordinate (endpointPaddedDistance P R k) (endpointPaddedDistance P R k) T i true i false=
      Complex.I*(Real.tan (Real.pi*(endpointPaddedDistance P R k ⟨i+1,by omega⟩)) : ℂ)*
        halfNewtonCoordinate (endpointPaddedDistance P R k) (endpointPaddedDistance P R k) T i false i true ∧
    halfNewtonCoordinate (endpointPaddedDistance P R k) (endpointPaddedDistance P R k) T i true i true=
      -Complex.I*(Real.tan (Real.pi*(endpointPaddedDistance P R k ⟨i+1,by omega⟩)) : ℂ)*
        halfNewtonCoordinate (endpointPaddedDistance P R k) (endpointPaddedDistance P R k) T i false i false := by
  obtain ⟨hp,hn⟩ := endpointNewtonCluster_extreme_parities hP hR k T hT i
  simp only [endpointNewtonCoordinate_diagonal_clusters hP hR k T hT hFT,
    hp,hn,halfNewtonParityPositive,halfNewtonParityNegative,ite_true,Bool.false_eq_true,ite_false]
  constructor <;> field_simp
  all_goals ring_nf
  all_goals simp [Complex.I_sq]

/-- The exact fixed-normalized physical diagonal equations, including the
factor 1/R in parity 11. Here R=1/4096 is the source's prescribed scale. -/
theorem endpointNewtonMoment_diagonal_relations {P R : ℕ} (hP : 1 ≤ P) (hR : 1 ≤ R)
    (k : ℕ) (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier ((endpointDeletedCarrier (rapidEndpointPhaseData P R k)).translate (-1/2)) T)
    (hFT : AtomicOnCarrier ((endpointDeletedCarrier (rapidEndpointPhaseData P R k)).translate (-1/2)) (𝓕 T))
    (i : ℕ) :
    halfNewtonMoment (endpointPaddedDistance P R k) (endpointPaddedDistance P R k) T i true i false=
      Complex.I*(Real.tan (Real.pi*(endpointPaddedDistance P R k ⟨i+1,by omega⟩)) : ℂ)*
        halfNewtonMoment (endpointPaddedDistance P R k) (endpointPaddedDistance P R k) T i false i true ∧
    halfNewtonMoment (endpointPaddedDistance P R k) (endpointPaddedDistance P R k) T i true i true=
      (-Complex.I*(Real.tan (Real.pi*(endpointPaddedDistance P R k ⟨i+1,by omega⟩)) : ℂ)/(1/4096 : ℂ))*
        halfNewtonMoment (endpointPaddedDistance P R k) (endpointPaddedDistance P R k) T i false i false := by
  obtain ⟨hp,hn⟩ := endpointNewtonCoordinate_diagonal_relations hP hR k T hT hFT i
  simp only [halfNewtonMoment,hp,hn,Bool.toNat_true,Bool.toNat_false]
  constructor
  · norm_num
    ring
  · norm_num [mul_inv_rev]
    ring
/-- The actual Fourier companion has exactly the reversed imaginary diagonal
signs. No equality to an analytic gauge is assumed to obtain these equations. -/
theorem endpointNewtonFourierMoment_diagonal_relations {P R : ℕ} (hP : 1 ≤ P) (hR : 1 ≤ R)
    (k : ℕ) (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier (endpointDeletedCarrier (rapidEndpointPhaseData P R k)) T)
    (hFT : AtomicOnCarrier (endpointDeletedCarrier (rapidEndpointPhaseData P R k)) (𝓕 T))
    (i : ℕ) :
    halfNewtonFourierMoment (endpointPaddedDistance P R k) (endpointPaddedDistance P R k) T i false i true=
      -Complex.I*(Real.tan (Real.pi*(endpointPaddedDistance P R k ⟨i+1,by omega⟩)) : ℂ)*
        halfNewtonFourierMoment (endpointPaddedDistance P R k) (endpointPaddedDistance P R k) T i true i false ∧
    halfNewtonFourierMoment (endpointPaddedDistance P R k) (endpointPaddedDistance P R k) T i true i true=
      (Complex.I*(Real.tan (Real.pi*(endpointPaddedDistance P R k ⟨i+1,by omega⟩)) : ℂ)/(1/4096 : ℂ))*
        halfNewtonFourierMoment (endpointPaddedDistance P R k) (endpointPaddedDistance P R k) T i false i false := by
  obtain ⟨hp,hq⟩ := halfWeylEndpointFourierCompanion_atomic_records _ _ T hT hFT
  obtain ⟨hc,hd⟩ := endpointNewtonMoment_diagonal_relations hP hR k
    (halfWeylFourierCompanion T) hp hq i
  simp only [halfNewtonFourierMoment_eq_transposed,halfNewtonParitySign,
    ite_true,Bool.false_eq_true,ite_false,one_mul,neg_one_mul]
  rw [hc,hd]
  constructor <;> ring


end MeyerGeneralProblem.Adaptive
