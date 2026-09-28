module

public import MeyerGeneralProblem.Cardinal.Adaptive.ActualSourceGauge
public import MeyerGeneralProblem.Cardinal.Adaptive.SeamCompleteKernel
public import MeyerGeneralProblem.Cardinal.Adaptive.CriticalForwardMap

@[expose] public section

/-! # Zeroth-reading faithfulness for complete actual small-tail sources -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open scoped FourierTransform

/-- Literal small positive phase distances supply both actual operator inputs. -/
theorem smallPhase_operator_bounds (t : ℝ) (ht : 0 ≤ t) (hs : t ≤ 1/549755813888) :
    ‖criticalNewtonNode t‖ ≤ (1/4096:ℝ)^2 ∧
      ‖(Real.tan (Real.pi*t):ℂ)‖ ≤ (1/4096:ℝ)^3 := by
  constructor
  · have hz := shrinkingNewton_cos_factor_le t 0 ht (hs.trans (by norm_num)) (by simpa using ht)
    have hn : ‖criticalNewtonNode t‖ ≤ 32*t^2 := by
      simpa only [criticalNewtonNode,Complex.norm_real,Real.norm_eq_abs,mul_zero,Real.cos_zero,abs_sub_comm] using hz
    have hsq : t^2 ≤ (1/549755813888:ℝ)^2 := (sq_le_sq₀ ht (by positivity)).mpr hs
    exact hn.trans ((mul_le_mul_of_nonneg_left hsq (by norm_num)).trans (by norm_num))
  · have hn : 0 ≤ Real.tan (Real.pi*t) :=
      Real.tan_nonneg_of_nonneg_of_le_pi_div_two (mul_nonneg Real.pi_pos.le ht)
        (by have hh := hs.trans (by norm_num : (1/549755813888:ℝ) ≤ 1/2); nlinarith [Real.pi_pos])
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hn]
    exact (tan_phase_le_eight_mul t ht (hs.trans (by norm_num))).trans
      ((mul_le_mul_of_nonneg_left hs (by norm_num)).trans (by norm_num))

/-- An actual complete small-tail source with vanishing zeroth Newton reading
is zero. Full source membership, gauge action, graphs, and Schur inversion are
all derived from the original paired atomic records. -/
theorem actualSmallTail_zero_of_zeroth (α β : ℕ+ → ℝ)
    (hia : ∀ j, 0 < α j ∧ α j < 1/2) (hib : ∀ j, 0 < β j ∧ β j < 1/2)
    (ha : ∀ j, |1/2-α j| ≤ 1/549755813888) (hb : ∀ j, |1/2-β j| ≤ 1/549755813888)
    (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier (criticalPhaseTailCarrier α hia 0 0) T)
    (hFT : AtomicOnCarrier (criticalPhaseTailCarrier β hib 0 0) (𝓕 T))
    (hz : halfNewtonMoment (fun l => 1/2-α l) (fun l => 1/2-β l)
      (halfWeylDistributionCLM T) 0 false 0 false=0) : T=0 := by
  have ha' (j : ℕ+) : |1/2-α j| ≤ (1/8192:ℝ) := (ha j).trans (by norm_num)
  have hb' (j : ℕ+) : |1/2-β j| ≤ (1/8192:ℝ) := (hb j).trans (by norm_num)
  let a (n : ℕ) := criticalNewtonNode (1/2-α ⟨n+1,by omega⟩)
  let b (n : ℕ) := criticalNewtonNode (1/2-β ⟨n+1,by omega⟩)
  let ta (n : ℕ) : ℂ := Real.tan (Real.pi*(1/2-α ⟨n+1,by omega⟩))
  let tb (n : ℕ) : ℂ := Real.tan (Real.pi*(1/2-β ⟨n+1,by omega⟩))
  have hpa (n : ℕ) := smallPhase_operator_bounds (1/2-α ⟨n+1,by omega⟩)
    (by linarith [(hia ⟨n+1,by omega⟩).2]) ((le_abs_self _).trans (ha _))
  have hpb (n : ℕ) := smallPhase_operator_bounds (1/2-β ⟨n+1,by omega⟩)
    (by linarith [(hib ⟨n+1,by omega⟩).2]) ((le_abs_self _).trans (hb _))
  have hna : ∀ n, ‖a n‖ ≤ (1/4096:ℝ)^2 := fun n => (hpa n).1
  have hnb : ∀ n, ‖b n‖ ≤ (1/4096:ℝ)^2 := fun n => (hpb n).1
  have hta : ∀ n, ‖ta n‖ ≤ (1/4096:ℝ)^3 := fun n => (hpa n).2
  have htb : ∀ n, ‖tb n‖ ≤ (1/4096:ℝ)^3 := fun n => (hpb n).2
  obtain ⟨hp,hq⟩ := halfWeylDistribution_atomic_records α β hia hib T hT hFT
  let A := actualConstantNewtonArray α β hia hib ha' hb' (halfWeylDistributionCLM T) hp hq
  let B := actualConstantFourierArray α β hia hib ha' hb' T hT hFT
  have hrec : A=seamPProjection A+seamPhysicalGraph ta hta (seamPProjection A) :=
    seamPhysicalGraph_reconstruct ta hta A
      (actualConstantNewtonArray_upper_flag α β hia hib ha' hb' _ hp hq)
      (actualConstantNewtonArray_diagonal α β hia hib ha' hb' _ hp hq)
  have hspec : seamQProjection B-seamSpectralGraph tb htb B=0 :=
    seamSpectralGraph_equation tb htb B
      (actualConstantFourierArray_lower_flag α β hia hib ha' hb' T hT hFT)
      (actualConstantFourierArray_diagonal α β hia hib ha' hb' T hT hFT)
  have hg := seamGauge_actualArrays α β hia hib ha' hb' hna hnb T hT hFT
  have hker : seamFullOperator a b ta tb hna hnb hta htb (seamPProjection A)=0 :=
    seamFullGraph_kernel ta tb hta htb _ A B hrec hspec hg
  have hzA : A ((0,false),(0,false))=0 := hz
  have hzP : seamPProjection A ((0,false),(0,false))=0 := by
    simpa only [seamPProjection,momentProjection_apply,seamDIndices,seamCIndices,
      Set.mem_union,Set.mem_setOf_eq,not_lt,le_refl,and_self,or_true,true_or,if_true] using hzA
  have hP : seamPProjection A=0 := seamFull_flag_zero a b ta tb hna hnb hta htb
    (seamPProjection A) (momentProjection_idempotent _ _) hker hzP
  have hAz : A=0 := by
    calc
      A=seamPProjection A+seamPhysicalGraph ta hta (seamPProjection A) := hrec
      _=0 := by rw [hP,map_zero,add_zero]
  have hW := actualConstantNewtonArray_faithful α β hia hib ha' hb' _ hp hq hAz
  apply halfWeylDistribution_injective
  simpa only [map_zero] using hW

/-- The actual zeroth compact Newton reading on the complete critical source
is a complex linear map, with the original characteristic recentering. -/
def actualSmallTailZeroth (α β : ℕ+ → ℝ)
    (hia : ∀ j, 0 < α j ∧ α j < 1/2) (hib : ∀ j, 0 < β j ∧ β j < 1/2) :
    criticalCompleteSource α β hia hib 0 →ₗ[ℂ] ℂ where
  toFun T := halfNewtonMoment (fun l => 1/2-α l) (fun l => 1/2-β l)
    (halfWeylDistributionCLM T) 0 false 0 false
  map_add' T U := by
    simp only [Submodule.coe_add,halfNewtonMoment,halfNewtonCoordinate,halfNewtonBilinear,
      map_add,zakTensorAction_add_source,mul_add]
  map_smul' c T := by
    simp only [Submodule.coe_smul,halfNewtonMoment,halfNewtonCoordinate,halfNewtonBilinear,
      map_smul,zakTensorAction_smul_source,smul_eq_mul,RingHom.id_apply]
    ring

/-- The true zeroth reading is injective on the entire original small-tail
source, not only on a finite endpoint or supplied array class. -/
theorem actualSmallTailZeroth_injective (α β : ℕ+ → ℝ)
    (hia : ∀ j, 0 < α j ∧ α j < 1/2) (hib : ∀ j, 0 < β j ∧ β j < 1/2)
    (ha : ∀ j, |1/2-α j| ≤ 1/549755813888) (hb : ∀ j, |1/2-β j| ≤ 1/549755813888) :
    Function.Injective (actualSmallTailZeroth α β hia hib) := by
  apply (LinearMap.ker_eq_bot).mp
  rw [LinearMap.ker_eq_bot']
  intro T hT
  apply Subtype.ext
  exact actualSmallTail_zero_of_zeroth α β hia hib ha hb T T.property.1 T.property.2 hT

/-- The entire original paired source is finite dimensional by its constructed
injection into one complex scalar. -/
theorem actualSmallTail_finite (α β : ℕ+ → ℝ)
    (hia : ∀ j, 0 < α j ∧ α j < 1/2) (hib : ∀ j, 0 < β j ∧ β j < 1/2)
    (ha : ∀ j, |1/2-α j| ≤ 1/549755813888) (hb : ∀ j, |1/2-β j| ≤ 1/549755813888) :
    Module.Finite ℂ (criticalCompleteSource α β hia hib 0) :=
  Module.Finite.of_injective (actualSmallTailZeroth α β hia hib)
    (actualSmallTailZeroth_injective α β hia hib ha hb)

/-- The complete actual small-tail source has complex dimension at most one. -/
theorem actualSmallTail_finrank_le_one (α β : ℕ+ → ℝ)
    (hia : ∀ j, 0 < α j ∧ α j < 1/2) (hib : ∀ j, 0 < β j ∧ β j < 1/2)
    (ha : ∀ j, |1/2-α j| ≤ 1/549755813888) (hb : ∀ j, |1/2-β j| ≤ 1/549755813888) :
    Module.finrank ℂ (criticalCompleteSource α β hia hib 0) ≤ 1 := by
  simpa only [Module.finrank_self] using
    LinearMap.finrank_le_finrank_of_injective (actualSmallTailZeroth_injective α β hia hib ha hb)

/-- Every complete small-tail source is a scalar multiple of any nonzero
source, with the scalar fixed by the actual compact zeroth reading. -/
theorem actualSmallTail_eq_scalar (α β : ℕ+ → ℝ)
    (hia : ∀ j, 0 < α j ∧ α j < 1/2) (hib : ∀ j, 0 < β j ∧ β j < 1/2)
    (ha : ∀ j, |1/2-α j| ≤ 1/549755813888) (hb : ∀ j, |1/2-β j| ≤ 1/549755813888)
    (T U : criticalCompleteSource α β hia hib 0) (hU : U ≠ 0) :
    T=(actualSmallTailZeroth α β hia hib T / actualSmallTailZeroth α β hia hib U) • U := by
  have hi := actualSmallTailZeroth_injective α β hia hib ha hb
  have hn : actualSmallTailZeroth α β hia hib U ≠ 0 := by
    intro hz
    apply hU
    apply hi
    simpa only [map_zero] using hz
  apply hi
  rw [map_smul,smul_eq_mul,div_mul_cancel₀ _ hn]

/-- Any actual nonzero source closes the lower bound and makes the whole
critical small-tail space exactly a complex line. -/
theorem actualSmallTail_finrank_eq_one (α β : ℕ+ → ℝ)
    (hia : ∀ j, 0 < α j ∧ α j < 1/2) (hib : ∀ j, 0 < β j ∧ β j < 1/2)
    (ha : ∀ j, |1/2-α j| ≤ 1/549755813888) (hb : ∀ j, |1/2-β j| ≤ 1/549755813888)
    (T : criticalCompleteSource α β hia hib 0) (hT : T ≠ 0) :
    Module.finrank ℂ (criticalCompleteSource α β hia hib 0)=1 := by
  letI := actualSmallTail_finite α β hia hib ha hb
  have hp : 0 < Module.finrank ℂ (criticalCompleteSource α β hia hib 0) :=
    Module.finrank_pos_iff_exists_ne_zero.mpr ⟨T,hT⟩
  have hu := actualSmallTail_finrank_le_one α β hia hib ha hb
  omega

end
end MeyerGeneralProblem.Adaptive
