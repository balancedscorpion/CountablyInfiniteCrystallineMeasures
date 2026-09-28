module

public import MeyerGeneralProblem.Cardinal.Adaptive.CriticalMultiplierRecovery

@[expose] public section

/-! # Actual finite Poisson repair for arbitrary distinct interior heads -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open scoped FourierTransform BigOperators

/-- The literal point on an unrestricted signed head coset. -/
def criticalHeadPoint {k : ℕ} (α : Fin k → ℝ) (i : Fin k) (u : Bool) (n : ℤ) : ℝ :=
  (n : ℝ)+criticalSignedPhase u (α i)

/-- Every signed head point belongs to the full physical head carrier. -/
theorem criticalHeadPoint_mem {k : ℕ} (α : Fin k → ℝ) (i : Fin k) (u : Bool) (n : ℤ) :
    criticalHeadPoint α i u n ∈ criticalHeadCosetSet α := by
  refine ⟨i,!u,n,?_⟩
  rw [signedPhase_eq_criticalSignedPhase,Bool.not_not]
  rfl

/-- Distinct interior phases, signs and integer cells give distinct actual head points. -/
theorem criticalHeadPoint_injective {k : ℕ} (α : Fin k → ℝ) (ha : Function.Injective α)
    (hi : ∀ i, 0 < α i ∧ α i < 1/2) {i j : Fin k} {u v : Bool} {n m : ℤ}
    (h : criticalHeadPoint α i u n = criticalHeadPoint α j v m) :
    i=j ∧ u=v ∧ n=m := by
  have habs (i : Fin k) (u : Bool) : |criticalSignedPhase u (α i)|=α i := by
    cases u <;> simp [criticalSignedPhase,abs_of_pos (hi i).1]
  obtain ⟨hn,he⟩ := integer_cell_unique
    (by rw [habs]; exact (hi i).2) (by rw [habs]; exact (hi j).2) h
  have hij : i=j := ha (by simpa only [habs] using congrArg abs he)
  subst j
  refine ⟨rfl,?_,hn⟩
  cases u <;> cases v <;> simp only [criticalSignedPhase,Bool.false_eq_true,ite_false,ite_true] at he ⊢ <;>
    first | rfl | exfalso; linarith [(hi i).1]

/-- Actual coefficient extraction in any complete ambient carrier containing the head. -/
def criticalHeadCoefficient {k : ℕ} (α : Fin k → ℝ) (S : LocallyFiniteCarrier)
    (hS : criticalHeadCosetSet α ⊆ S.carrier) (i : Fin k) (u : Bool) (n : ℤ) :
    TemperedDistribution ℝ ℂ →ₗ[ℂ] ℂ where
  toFun T := T (S.isolationSchwartz ⟨criticalHeadPoint α i u n,hS (criticalHeadPoint_mem α i u n)⟩)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The ambient isolation test distinguishes all complete head cells exactly. -/
theorem criticalHeadIsolation_apply {k : ℕ} (α : Fin k → ℝ) (ha : Function.Injective α)
    (hi : ∀ i, 0 < α i ∧ α i < 1/2) (S : LocallyFiniteCarrier)
    (hS : criticalHeadCosetSet α ⊆ S.carrier) (i j : Fin k) (u v : Bool) (n m : ℤ) :
    S.isolationSchwartz ⟨criticalHeadPoint α i u n,hS (criticalHeadPoint_mem α i u n)⟩
      (criticalHeadPoint α j v m) = if j=i ∧ v=u ∧ m=n then 1 else 0 := by
  by_cases he : j=i ∧ v=u ∧ m=n
  · obtain ⟨rfl,rfl,rfl⟩ := he
    rw [ite_eq_left ⟨rfl,rfl,rfl⟩]
    exact S.isolationSchwartz_self _
  · rw [ite_eq_right he]
    exact S.isolationSchwartz_of_mem_of_ne _ (hS (criticalHeadPoint_mem α j v m))
      (fun h => he (criticalHeadPoint_injective α ha hi h))

/-- Every actual whole signed Poisson basis vector has the expected complete
physical coefficient, with no truncation of the integer comb. -/
theorem criticalHeadCoefficient_wholePoisson {k : ℕ} (α : Fin k → ℝ) (ha : Function.Injective α)
    (hi : ∀ i, 0 < α i ∧ α i < 1/2) (S : LocallyFiniteCarrier)
    (hS : criticalHeadCosetSet α ⊆ S.carrier) (i I : Fin k) (u U : Bool) (n : ℤ) (b : ℝ) :
    criticalHeadCoefficient α S hS i u n (wholePoissonSource (criticalSignedPhase U (α I)) b) =
      if I=i ∧ U=u then criticalCharacter n b else 0 := by
  change wholePoissonSource _ b (S.isolationSchwartz _) = _
  rw [wholePoissonSource_apply]
  have he (m : ℤ) : criticalSignedPhase U (α I)+(m : ℝ) = criticalHeadPoint α I U m := add_comm _ _
  simp only [he,criticalHeadIsolation_apply α ha hi S hS]
  by_cases h : I=i ∧ U=u
  · rw [ite_eq_left h,tsum_eq_single n]
    · simp only [h.1,h.2,and_self,ite_true,mul_one]
    · intro m hm
      simp [hm]
  · rw [ite_eq_right h]
    have hz (m : ℤ) : ¬ (I=i ∧ U=u ∧ m=n) := fun hh => h ⟨hh.1,hh.2.1⟩
    simp only [ite_eq_right (hz _),mul_zero,tsum_zero]

/-- Whole signed Poisson synthesis for two arbitrary finite phase heads. -/
def criticalPoissonSynthesis {k : ℕ} (α β : Fin k → ℝ) :
    (Fin k → Fin k → SignedMassBlock) →ₗ[ℂ] TemperedDistribution ℝ ℂ where
  toFun c := ∑ I, ∑ u, ∑ J, ∑ v, c I J u v •
    wholePoissonSource (criticalSignedPhase u (α I)) (criticalSignedPhase v (β J))
  map_add' c d := by
    ext f
    simp only [_root_.add_apply,sum_apply,smul_apply,smul_eq_mul,Pi.add_apply,
      add_mul,Finset.sum_add_distrib]
  map_smul' a c := by simp [Finset.smul_sum,smul_smul]

/-- The actual physical observation of the whole synthesis is the checked finite row sample. -/
theorem criticalHeadCoefficient_synthesis {k : ℕ} (α β : Fin k → ℝ) (ha : Function.Injective α)
    (hi : ∀ i, 0 < α i ∧ α i < 1/2) (S : LocallyFiniteCarrier)
    (hS : criticalHeadCosetSet α ⊆ S.carrier) (c : Fin k → Fin k → SignedMassBlock)
    (i : Fin k) (u : Bool) (n : ℤ) :
    criticalHeadCoefficient α S hS i u n (criticalPoissonSynthesis α β c) =
      finiteSignedRow β (fun J v => c i J u v) (criticalCharacter n) := by
  change criticalHeadCoefficient α S hS i u n (∑ I,∑ u,∑ J,∑ v,c I J u v •wholePoissonSource _ _) = _
  simp only [map_sum,map_smul,smul_eq_mul,criticalHeadCoefficient_wholePoisson α ha hi S hS]
  simp [finiteSignedRow,ite_and,mul_comm]

/-- Complete Fourier coefficients of every actual Poisson basis source,
including the phase depending on the physical shift. -/
theorem criticalHeadCoefficient_fourier_wholePoisson {k : ℕ} (β : Fin k → ℝ) (hb : Function.Injective β)
    (hi : ∀ i, 0 < β i ∧ β i < 1/2) (S : LocallyFiniteCarrier)
    (hS : criticalHeadCosetSet β ⊆ S.carrier) (j J : Fin k) (v V : Bool) (n : ℤ) (a : ℝ) :
    criticalHeadCoefficient β S hS j v n (𝓕 (wholePoissonSource a (criticalSignedPhase V (β J)))) =
      if J=j ∧ V=v then combModulationCharacter (-a) (criticalSignedPhase v (β j)+n) else 0 := by
  change 𝓕 (wholePoissonSource a _) (S.isolationSchwartz _) = _
  rw [fourier_wholePoissonSource_apply]
  have he (m : ℤ) : criticalSignedPhase V (β J)+(m : ℝ) = criticalHeadPoint β J V m := add_comm _ _
  simp only [he,criticalHeadIsolation_apply β hb hi S hS]
  by_cases h : J=j ∧ V=v
  · rw [ite_eq_left h,tsum_eq_single n]
    · simp only [h.1,h.2,and_self,ite_true,mul_one,criticalHeadPoint,add_comm]
    · intro m hm
      simp [hm]
  · rw [ite_eq_right h]
    have hz (m : ℤ) : ¬ (J=j ∧ V=v ∧ m=n) := fun hh => h ⟨hh.1,hh.2.1⟩
    simp only [ite_eq_right (hz _),mul_zero,tsum_zero]

private theorem poisson_modulation_gauge (a b : ℝ) (u v : Bool) (n : ℤ) (z : ℂ) :
    z * combModulationCharacter (-(criticalSignedPhase u a)) (criticalSignedPhase v b+n) =
      criticalCharacter (-n) (criticalSignedPhase u a) *
        signedGauge (2*Real.pi*a*b) (fun _ _ => z) u v := by
  rw [combModulationCharacter_eq_exp]
  unfold criticalCharacter signedGauge criticalSignedPhase
  rw [← mul_assoc,mul_comm z,mul_assoc,← Complex.exp_add]
  congr 2
  cases u <;> cases v <;> simp <;> ring

/-- Actual Fourier observations of the entire synthesis give exactly the
full-gauge column samples of the checked finite triangular kernel theorem. -/
theorem criticalHeadCoefficient_fourier_synthesis {k : ℕ} (α β : Fin k → ℝ) (hb : Function.Injective β)
    (hi : ∀ i, 0 < β i ∧ β i < 1/2) (S : LocallyFiniteCarrier)
    (hS : criticalHeadCosetSet β ⊆ S.carrier) (c : Fin k → Fin k → SignedMassBlock)
    (j : Fin k) (v : Bool) (n : ℤ) :
    criticalHeadCoefficient β S hS j v n (𝓕 (criticalPoissonSynthesis α β c)) =
      finiteSignedRow α (fun I u => signedGauge (2*Real.pi*α I*β j) (c I j) u v)
        (criticalCharacter (-n)) := by
  change criticalHeadCoefficient β S hS j v n
    (temperedFourierLinearMap (∑ I,∑ u,∑ J,∑ v,c I J u v •wholePoissonSource _ _)) = _
  simp only [map_sum,map_smul,smul_eq_mul,temperedFourierLinearMap_apply,
    criticalHeadCoefficient_fourier_wholePoisson β hb hi S hS]
  simp only [ite_and,mul_ite,mul_zero]
  unfold finiteSignedRow
  simp only [LinearMap.coe_mk,AddHom.coe_mk]
  apply Finset.sum_congr rfl
  intro I _
  apply Finset.sum_congr rfl
  intro u _
  simp only [Finset.sum_ite_irrel,Finset.sum_const_zero]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  exact poisson_modulation_gauge _ _ u v n (c I j u v)

/-- Both actual triangular coefficient lists on complete ambient carriers. -/
def criticalTriangularObservation {k : ℕ} (α β : Fin k → ℝ)
    (S R : LocallyFiniteCarrier) (hS : criticalHeadCosetSet α ⊆ S.carrier)
    (hR : criticalHeadCosetSet β ⊆ R.carrier) :
    TemperedDistribution ℝ ℂ →ₗ[ℂ] TriangularHoleCoordinates k where
  toFun T := Sum.elim
    (fun h => criticalHeadCoefficient α S hS h.1 h.2.1 (triangularHoleCell h) T)
    (fun h => criticalHeadCoefficient β R hR h.1 h.2.1 (triangularHoleCell h) (𝓕 T))
  map_add' T U := by ext h; cases h <;> simp [FourierTransform.fourier_add]
  map_smul' a T := by ext h; cases h <;> simp [FourierTransform.fourier_smul]

/-- Actual whole Poisson synthesis followed by both observed triangular lists
is injective for arbitrary distinct strictly interior finite heads. -/
theorem criticalTriangularObservation_synthesis_injective {k : ℕ} (α β : Fin k → ℝ)
    (ha : Function.Injective α) (hia : ∀ i, 0 < α i ∧ α i < 1/2)
    (hb : Function.Injective β) (hib : ∀ i, 0 < β i ∧ β i < 1/2)
    (S R : LocallyFiniteCarrier) (hS : criticalHeadCosetSet α ⊆ S.carrier)
    (hR : criticalHeadCosetSet β ⊆ R.carrier) :
    Function.Injective ((criticalTriangularObservation α β S R hS hR).comp (criticalPoissonSynthesis α β)) := by
  rw [← LinearMap.ker_eq_bot,Submodule.eq_bot_iff]
  intro c hc
  have hz : criticalTriangularObservation α β S R hS hR (criticalPoissonSynthesis α β c)=0 := hc
  apply critical_triangular_samples_kernel α β ha hb hia hib c
  · intro I u n hn
    obtain ⟨h,hI,hu,hn'⟩ := triangularHoleCell_surjective I u n hn
    have he := congrFun hz (.inl h)
    change criticalHeadCoefficient α S hS h.1 h.2.1 (triangularHoleCell h) (criticalPoissonSynthesis α β c)=0 at he
    simpa only [hI,hu,hn',criticalHeadCoefficient_synthesis α β ha hia S hS] using he
  · intro J v n hn
    obtain ⟨h,hJ,hv,hn'⟩ := triangularHoleCell_surjective J v n hn
    have he := congrFun hz (.inr h)
    change criticalHeadCoefficient β R hR h.1 h.2.1 (triangularHoleCell h) (𝓕 (criticalPoissonSynthesis α β c))=0 at he
    simpa only [hJ,hv,hn',criticalHeadCoefficient_fourier_synthesis α β hb hib R hR] using he

/-- The actual square triangular observation matrix has a constructed inverse;
no finite-head inverse hypothesis is supplied. -/
def criticalTriangularSynthesisEquiv {k : ℕ} (α β : Fin k → ℝ)
    (ha : Function.Injective α) (hia : ∀ i, 0 < α i ∧ α i < 1/2)
    (hb : Function.Injective β) (hib : ∀ i, 0 < β i ∧ β i < 1/2)
    (S R : LocallyFiniteCarrier) (hS : criticalHeadCosetSet α ⊆ S.carrier)
    (hR : criticalHeadCosetSet β ⊆ R.carrier) :
    (Fin k → Fin k → SignedMassBlock) ≃ₗ[ℂ] TriangularHoleCoordinates k :=
  LinearEquiv.ofInjectiveOfFinrankEq
    ((criticalTriangularObservation α β S R hS hR).comp (criticalPoissonSynthesis α β))
    (criticalTriangularObservation_synthesis_injective α β ha hia hb hib S R hS hR)
    (by
      have hd : Module.finrank ℂ (TriangularHoleCoordinates k) = 4*k^2 := by
        rw [Module.finrank_pi,Fintype.card_sum,triangularHoleIndex_card]
        ring
      rw [hd]
      simp [SignedMassBlock,Module.finrank_pi_fintype]
      ring)

/-- Correct the actual forbidden head coefficients by a whole finite Poisson source. -/
def criticalPoissonCorrection {k : ℕ} (α β : Fin k → ℝ)
    (ha : Function.Injective α) (hia : ∀ i, 0 < α i ∧ α i < 1/2)
    (hb : Function.Injective β) (hib : ∀ i, 0 < β i ∧ β i < 1/2)
    (S R : LocallyFiniteCarrier) (hS : criticalHeadCosetSet α ⊆ S.carrier)
    (hR : criticalHeadCosetSet β ⊆ R.carrier) :
    TemperedDistribution ℝ ℂ →ₗ[ℂ] TemperedDistribution ℝ ℂ :=
  (criticalPoissonSynthesis α β).comp
    ((criticalTriangularSynthesisEquiv α β ha hia hb hib S R hS hR).symm.toLinearMap.comp
      (criticalTriangularObservation α β S R hS hR))

/-- The constructed whole correction has exactly the observed physical and
Fourier head coefficients of its input. -/
theorem criticalPoissonCorrection_observation {k : ℕ} (α β : Fin k → ℝ)
    (ha : Function.Injective α) (hia : ∀ i, 0 < α i ∧ α i < 1/2)
    (hb : Function.Injective β) (hib : ∀ i, 0 < β i ∧ β i < 1/2)
    (S R : LocallyFiniteCarrier) (hS : criticalHeadCosetSet α ⊆ S.carrier)
    (hR : criticalHeadCosetSet β ⊆ R.carrier) (T : TemperedDistribution ℝ ℂ) :
    criticalTriangularObservation α β S R hS hR (criticalPoissonCorrection α β ha hia hb hib S R hS hR T) =
      criticalTriangularObservation α β S R hS hR T :=
  (criticalTriangularSynthesisEquiv α β ha hia hb hib S R hS hR).apply_symm_apply _

/-- Subtraction of the actual correction removes both finite forbidden lists. -/
theorem criticalPoissonCorrection_holes_zero {k : ℕ} (α β : Fin k → ℝ)
    (ha : Function.Injective α) (hia : ∀ i, 0 < α i ∧ α i < 1/2)
    (hb : Function.Injective β) (hib : ∀ i, 0 < β i ∧ β i < 1/2)
    (S R : LocallyFiniteCarrier) (hS : criticalHeadCosetSet α ⊆ S.carrier)
    (hR : criticalHeadCosetSet β ⊆ R.carrier) (T : TemperedDistribution ℝ ℂ) :
    criticalTriangularObservation α β S R hS hR (T-criticalPoissonCorrection α β ha hia hb hib S R hS hR T)=0 := by
  rw [map_sub,criticalPoissonCorrection_observation,sub_self]

/-- A whole Poisson source has value-only action on its complete physical head carrier. -/
theorem wholePoissonSource_atomic_head {k : ℕ} (α : Fin k → ℝ)
    (i : Fin k) (u : Bool) (b : ℝ) :
    AtomicOnCarrier (criticalHeadCosetCarrier α) (wholePoissonSource (criticalSignedPhase u (α i)) b) := by
  intro f hf
  rw [wholePoissonSource_apply]
  have hz (n : ℤ) : f (criticalSignedPhase u (α i)+n)=0 := by
    apply hf
    simpa only [criticalHeadCosetCarrier,criticalHeadPoint,add_comm] using criticalHeadPoint_mem α i u n
  simp only [hz,mul_zero,tsum_zero]

/-- The same whole Poisson source has its complete value-only Fourier head record. -/
theorem fourier_wholePoissonSource_atomic_head {k : ℕ} (β : Fin k → ℝ)
    (j : Fin k) (v : Bool) (a : ℝ) :
    AtomicOnCarrier (criticalHeadCosetCarrier β) (𝓕 (wholePoissonSource a (criticalSignedPhase v (β j)))) := by
  intro f hf
  rw [fourier_wholePoissonSource_apply]
  have hz (n : ℤ) : f (criticalSignedPhase v (β j)+n)=0 := by
    apply hf
    simpa only [criticalHeadCosetCarrier,criticalHeadPoint,add_comm] using criticalHeadPoint_mem β j v n
  simp only [hz,mul_zero,tsum_zero]

/-- The finite synthesis retains both complete head records. -/
theorem criticalPoissonSynthesis_atomic_records {k : ℕ} (α β : Fin k → ℝ)
    (c : Fin k → Fin k → SignedMassBlock) :
    AtomicOnCarrier (criticalHeadCosetCarrier α) (criticalPoissonSynthesis α β c) ∧
    AtomicOnCarrier (criticalHeadCosetCarrier β) (𝓕 (criticalPoissonSynthesis α β c)) := by
  constructor
  · intro f hf
    change (∑ I,∑ u,∑ J,∑ v,c I J u v •wholePoissonSource _ _) f=0
    simp only [sum_apply,smul_apply,smul_eq_mul,
      wholePoissonSource_atomic_head α _ _ _ f hf,mul_zero,Finset.sum_const_zero]
  · intro f hf
    change temperedFourierLinearMap (∑ I,∑ u,∑ J,∑ v,c I J u v •wholePoissonSource _ _) f=0
    simp only [map_sum,map_smul,temperedFourierLinearMap_apply,sum_apply,smul_apply,smul_eq_mul,
      fourier_wholePoissonSource_atomic_head β _ _ _ f hf,mul_zero,Finset.sum_const_zero]

/-- Actual head multiplication kills every complete Poisson synthesis. -/
theorem criticalPoissonSynthesis_multiplier_zero {k : ℕ} (α β : Fin k → ℝ)
    (c : Fin k → Fin k → SignedMassBlock) :
    criticalHeadMultiplierDistributionCLM α (criticalPoissonSynthesis α β c)=0 := by
  ext f
  change criticalPoissonSynthesis α β c (criticalHeadMultiplierTestCLM α f)=0
  apply (criticalPoissonSynthesis_atomic_records α β c).1
  intro x hx
  rw [criticalHeadMultiplierTestCLM_apply,(criticalHeadTrigProduct_zero_iff α x).mpr hx,zero_mul]

/-- The other actual head difference also kills every complete Poisson synthesis. -/
theorem criticalPoissonSynthesis_difference_zero {k : ℕ} (α β : Fin k → ℝ)
    (c : Fin k → Fin k → SignedMassBlock) :
    criticalHeadDifferenceDistributionCLM β (criticalPoissonSynthesis α β c)=0 := by
  apply (FourierTransform.fourierEquiv ℂ (TemperedDistribution ℝ ℂ)).injective
  change 𝓕 (criticalHeadDifferenceDistributionCLM β (criticalPoissonSynthesis α β c))=𝓕 (0 : TemperedDistribution ℝ ℂ)
  rw [fourier_criticalHeadDifferenceDistribution,FourierTransform.fourier_zero]
  ext f
  change 𝓕 (criticalPoissonSynthesis α β c) (criticalHeadMultiplierTestCLM β f)=0
  apply (criticalPoissonSynthesis_atomic_records α β c).2
  intro x hx
  rw [criticalHeadMultiplierTestCLM_apply,(criticalHeadTrigProduct_zero_iff β x).mpr hx,zero_mul]

/-- Every whole character comb obeys a genuine original first-order bound. -/
theorem wholePoissonSource_original_one_bound (a b : ℝ) :
    ∃ C > 0, ∀ f : SchwartzMap ℝ ℂ,
      ‖wholePoissonSource a b f‖ ≤ C*‖schwartzToHermiteScale 1 f‖ := by
  obtain ⟨C,hC,hbound⟩ := exists_lattice_absolute_hermite_one_bound 1 a (by norm_num)
  refine ⟨C,hC,fun f => ?_⟩
  rw [wholePoissonSource_apply]
  have hn (n : ℤ) : ‖criticalCharacter n b*f (a+n)‖ = ‖f (a+n)‖ := by
    rw [norm_mul]
    have hc : ‖criticalCharacter n b‖=1 := by
      simp [criticalCharacter,Complex.norm_exp,Complex.mul_re,Complex.mul_im]
    rw [hc,one_mul]
  have hs : Summable (fun n : ℤ => ‖criticalCharacter n b*f (a+n)‖) := by
    simpa only [hn,one_mul] using (hbound f).1
  have h := norm_tsum_le_tsum_norm hs
  simp only [hn] at h
  exact h.trans (by simpa only [one_mul] using (hbound f).2)

/-- Every actual whole Poisson basis source has an original H_-1 representative. -/
theorem wholePoissonSource_native_one (a b : ℝ) :
    ∃ u : HermiteScale (-1), hermiteScaleDistribution 1 u = wholePoissonSource a b := by
  obtain ⟨C,_,hb⟩ := wholePoissonSource_original_one_bound a b
  exact exists_native_representation_of_bound 1 _ ⟨C,hb⟩

/-- The complete finite synthesis belongs to every original negative layer of order at least one. -/
theorem criticalPoissonSynthesis_mem_native {k : ℕ} (α β : Fin k → ℝ)
    (c : Fin k → Fin k → SignedMassBlock) (p : ℕ) (hp : 1 ≤ p) :
    criticalPoissonSynthesis α β c ∈ originalNativeDistributionSpace p := by
  apply originalNativeDistributionSpace_mono hp
  change (∑ I,∑ u,∑ J,∑ v,c I J u v •wholePoissonSource _ _) ∈ originalNativeDistributionSpace 1
  apply Submodule.sum_mem
  intro I _
  apply Submodule.sum_mem
  intro u _
  apply Submodule.sum_mem
  intro J _
  apply Submodule.sum_mem
  intro v _
  exact Submodule.smul_mem _ _ (wholePoissonSource_native_one _ _)

end
end MeyerGeneralProblem.Adaptive
