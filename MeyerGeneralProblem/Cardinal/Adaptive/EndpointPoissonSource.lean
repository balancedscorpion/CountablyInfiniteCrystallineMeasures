module

public import MeyerGeneralProblem.Cardinal.Adaptive.EndpointMatrixConstruction

@[expose] public section

/-! # Whole Poisson sources on the single-endpoint coset family -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open scoped FourierTransform BigOperators

/-- The complete finite union of integer cosets, with one endpoint representative. -/
def endpointCosetCarrier {k : ℕ} (α : Fin k → ℝ) : LocallyFiniteCarrier where
  carrier := {x | ∃ a : EndpointPhaseIndex k, ∃ n : ℤ, endpointPhase α a+n=x}
  finite_inter_Icc x y := by
    have hf : (⋃ a : EndpointPhaseIndex k,
        (shiftedIntegerCombCarrier (endpointPhase α a)).carrier ∩ Set.Icc x y).Finite :=
      Set.finite_iUnion (fun a => (shiftedIntegerCombCarrier (endpointPhase α a)).finite_inter_Icc x y)
    apply hf.subset
    rintro z ⟨⟨a,n,rfl⟩,hz⟩
    exact Set.mem_iUnion.mpr ⟨a,⟨⟨n,rfl⟩,hz⟩⟩

/-- The literal point in a complete endpoint coset with its carrier membership. -/
def endpointPoint {k : ℕ} (α : Fin k → ℝ) (a : EndpointPhaseIndex k) (n : ℤ) :
    (endpointCosetCarrier α).subtype := ⟨endpointPhase α a+n,⟨a,n,rfl⟩⟩

theorem endpointPoint_injective {k : ℕ} (α : Fin k → ℝ)
    (ha : Function.Injective α) (hi : ∀ i, 0 < α i ∧ α i < 1/2)
    {a b : EndpointPhaseIndex k} {n m : ℤ}
    (he : endpointPhase α a+n=endpointPhase α b+m) : a=b ∧ n=m := by
  have ha' := endpointPhase_range α hi a
  have hb' := endpointPhase_range α hi b
  have hlo : (-1 : ℤ) < n-m := by
    exact_mod_cast (show (-1 : ℝ) < (n : ℝ)-(m : ℝ) by linarith)
  have hhi : n-m < (1 : ℤ) := by
    exact_mod_cast (show (n : ℝ)-(m : ℝ) < 1 by linarith)
  have hn : n=m := by omega
  subst m
  exact ⟨endpointPhase_injective α ha hi (by linarith),rfl⟩

/-- Evaluation of the whole source on the canonical carrier isolation test. -/
def endpointCoefficient {k : ℕ} (α : Fin k → ℝ) (a : EndpointPhaseIndex k) (n : ℤ) :
    TemperedDistribution ℝ ℂ →ₗ[ℂ] ℂ where
  toFun T := T ((endpointCosetCarrier α).isolationSchwartz (endpointPoint α a n))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem endpointIsolation_apply {k : ℕ} (α : Fin k → ℝ)
    (ha : Function.Injective α) (hi : ∀ i, 0 < α i ∧ α i < 1/2)
    (a b : EndpointPhaseIndex k) (n m : ℤ) :
    (endpointCosetCarrier α).isolationSchwartz (endpointPoint α a n)
      (endpointPhase α b+m) = if b=a ∧ m=n then 1 else 0 := by
  by_cases he : b=a ∧ m=n
  · obtain ⟨rfl,rfl⟩ := he
    simp only [and_self,ite_true]
    exact (endpointCosetCarrier α).isolationSchwartz_self _
  · rw [ite_eq_right he]
    exact (endpointCosetCarrier α).isolationSchwartz_of_mem_of_ne _ ⟨b,m,rfl⟩
      (fun h => he (endpointPoint_injective α ha hi h))

theorem endpointCoefficient_wholePoisson {k : ℕ} (α : Fin k → ℝ)
    (ha : Function.Injective α) (hi : ∀ i, 0 < α i ∧ α i < 1/2)
    (a A : EndpointPhaseIndex k) (n : ℤ) (b : ℝ) :
    endpointCoefficient α a n (wholePoissonSource (endpointPhase α A) b) =
      if A=a then criticalCharacter n b else 0 := by
  change wholePoissonSource _ b ((endpointCosetCarrier α).isolationSchwartz _) = _
  rw [wholePoissonSource_apply]
  simp only [endpointIsolation_apply α ha hi]
  by_cases h : A=a
  · subst A
    rw [ite_eq_left rfl,tsum_eq_single n]
    · simp
    · intro m hm; simp [hm]
  · simp [h]

/-- The entire finite endpoint source, with the full infinite integer combs. -/
def endpointPoissonSynthesis {k : ℕ} (α β : Fin k → ℝ) :
    EndpointMatrix k →ₗ[ℂ] TemperedDistribution ℝ ℂ where
  toFun c := ∑ a,∑ b,c a b • wholePoissonSource (endpointPhase α a) (endpointPhase β b)
  map_add' c d := by
    ext f
    simp only [_root_.add_apply,sum_apply,smul_apply,smul_eq_mul,Pi.add_apply,add_mul,Finset.sum_add_distrib]
  map_smul' a c := by simp [Finset.smul_sum,smul_smul]

theorem endpointCoefficient_synthesis {k : ℕ} (α β : Fin k → ℝ)
    (ha : Function.Injective α) (hi : ∀ i, 0 < α i ∧ α i < 1/2)
    (c : EndpointMatrix k) (a : EndpointPhaseIndex k) (n : ℤ) :
    endpointCoefficient α a n (endpointPoissonSynthesis α β c) = endpointRow β c a n := by
  change endpointCoefficient α a n (∑ A,∑ b,c A b •wholePoissonSource _ _)=_
  simp only [map_sum,map_smul,smul_eq_mul,endpointCoefficient_wholePoisson α ha hi]
  simp [endpointRow,Finset.sum_ite_irrel,mul_comm]

theorem endpointCoefficient_fourier_wholePoisson {k : ℕ} (β : Fin k → ℝ)
    (hb : Function.Injective β) (hi : ∀ i, 0 < β i ∧ β i < 1/2)
    (b B : EndpointPhaseIndex k) (n : ℤ) (a : ℝ) :
    endpointCoefficient β b n (𝓕 (wholePoissonSource a (endpointPhase β B))) =
      if B=b then combModulationCharacter (-a) (endpointPhase β b+n) else 0 := by
  change 𝓕 (wholePoissonSource a _) ((endpointCosetCarrier β).isolationSchwartz _) = _
  rw [fourier_wholePoissonSource_apply]
  simp only [endpointIsolation_apply β hb hi]
  by_cases h : B=b
  · subst B
    rw [ite_eq_left rfl,tsum_eq_single n]
    · simp
    · intro m hm; simp [hm]
  · simp [h]

theorem endpointGauge_modulation (a b : ℝ) (n : ℤ) :
    combModulationCharacter (-a) (b+n) = criticalCharacter (-n) a*endpointGauge a b := by
  rw [combModulationCharacter_eq_exp]
  unfold criticalCharacter endpointGauge
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem endpointCoefficient_fourier_synthesis {k : ℕ} (α β : Fin k → ℝ)
    (hb : Function.Injective β) (hi : ∀ i, 0 < β i ∧ β i < 1/2)
    (c : EndpointMatrix k) (b : EndpointPhaseIndex k) (n : ℤ) :
    endpointCoefficient β b n (𝓕 (endpointPoissonSynthesis α β c)) = endpointFourierRow α β c b n := by
  change endpointCoefficient β b n (temperedFourierLinearMap (∑ a,∑ B,c a B •wholePoissonSource _ _))=_
  simp only [map_sum,map_smul,smul_eq_mul,temperedFourierLinearMap_apply,
    endpointCoefficient_fourier_wholePoisson β hb hi]
  simp [endpointFourierRow,Finset.sum_ite_irrel,endpointGauge_modulation,mul_comm,mul_left_comm,mul_assoc]

/-- Physical and Fourier records hold for the whole synthesized source. -/
theorem endpointPoissonSynthesis_atomic {k : ℕ} (α β : Fin k → ℝ) (c : EndpointMatrix k) :
    AtomicOnCarrier (endpointCosetCarrier α) (endpointPoissonSynthesis α β c) ∧
    AtomicOnCarrier (endpointCosetCarrier β) (𝓕 (endpointPoissonSynthesis α β c)) := by
  have hA (a b) : AtomicOnCarrier (endpointCosetCarrier α)
      (wholePoissonSource (endpointPhase α a) (endpointPhase β b)) := by
    intro f hf
    rw [wholePoissonSource_apply]
    have hz (n : ℤ) : f (endpointPhase α a+n)=0 := hf _ ⟨a,n,rfl⟩
    simp only [hz,mul_zero,tsum_zero]
  have hB (a b) : AtomicOnCarrier (endpointCosetCarrier β)
      (𝓕 (wholePoissonSource (endpointPhase α a) (endpointPhase β b))) := by
    intro f hf
    rw [fourier_wholePoissonSource_apply]
    have hz (n : ℤ) : f (endpointPhase β b+n)=0 := hf _ ⟨b,n,rfl⟩
    simp only [hz,mul_zero,tsum_zero]
  constructor
  · intro f hf
    change (∑ a,∑ b,c a b •wholePoissonSource _ _) f=0
    simp only [sum_apply,smul_apply,smul_eq_mul,hA _ _ f hf,mul_zero,Finset.sum_const_zero]
  · intro f hf
    change temperedFourierLinearMap (∑ a,∑ b,c a b •wholePoissonSource _ _) f=0
    simp only [map_sum,map_smul,temperedFourierLinearMap_apply,sum_apply,smul_apply,
      smul_eq_mul,hB _ _ f hf,mul_zero,Finset.sum_const_zero]

/-- The whole synthesis lies in the original first Hermite layer. -/
theorem endpointPoissonSynthesis_native_one {k : ℕ} (α β : Fin k → ℝ) (c : EndpointMatrix k) :
    endpointPoissonSynthesis α β c ∈ originalNativeDistributionSpace 1 := by
  apply Submodule.sum_mem
  intro a _
  apply Submodule.sum_mem
  intro b _
  exact Submodule.smul_mem _ _ (wholePoissonSource_native_one _ _)

/-- Consecutive actual isolated physical coefficients distinguish every whole source. -/
theorem endpointPoissonSynthesis_injective {k : ℕ} (α β : Fin k → ℝ)
    (ha : Function.Injective α) (hb : Function.Injective β)
    (hia : ∀ i, 0 < α i ∧ α i < 1/2) (hib : ∀ i, 0 < β i ∧ β i < 1/2) :
    Function.Injective (endpointPoissonSynthesis α β) := by
  rw [← LinearMap.ker_eq_bot,Submodule.eq_bot_iff]
  intro c hc
  have hz : endpointPoissonSynthesis α β c = 0 := hc
  funext a
  apply finiteCharacter_consecutive_zero (endpointPhase β) (c a) (endpointCharacters_injective β hb hib) 0
  intro n
  have he := congrArg (endpointCoefficient α a (n : ℕ)) hz
  simpa only [endpointCoefficient_synthesis α β ha hia,map_zero,zero_add,endpointRow] using he

end
end MeyerGeneralProblem.Adaptive
