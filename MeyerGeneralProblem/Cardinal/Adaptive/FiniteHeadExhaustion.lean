module

public import MeyerGeneralProblem.Cardinal.Adaptive.CriticalForwardKernel

@[expose] public section

/-! # Complete finite-head source exhaustion by whole Poisson distributions -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open scoped BigOperators FourierTransform

/-- An actual central-cell test reads only the finitely many head coefficients
in that same cell, so zero coefficients annihilate the whole translated test. -/
theorem finiteHead_cell_test_zero {k : ℕ} (α : Fin k → ℝ)
    (hia : ∀ i, 0 < α i ∧ α i < 1/2) (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier (criticalHeadCosetCarrier α) T)
    (f : SchwartzMap ℝ ℂ) (hf : ∀ x : ℝ, 1/2 ≤ |x| → f x=0) (n : ℤ)
    (hz : ∀ i : Fin k, ∀ u : Bool, criticalHeadCoefficient α (criticalHeadCosetCarrier α)
      (criticalHeadCosetCarrier_contains α) i u (-n) T=0) :
    T (combSchwartzTranslation (n : ℝ) f)=0 := by
  let g := combSchwartzTranslation (n : ℝ) f
  have hgc : HasCompactSupport g := by
    apply HasCompactSupport.of_support_subset_isCompact
      (isCompact_Icc : IsCompact (Set.Icc (-(n : ℝ)-1/2) (-(n : ℝ)+1/2)))
    intro x hx
    have hx' : |(n : ℝ)+x|<1/2 := lt_of_not_ge (fun h => hx (hf _ h))
    have hh := abs_lt.mp hx'
    constructor <;> linarith
  obtain ⟨E,_,hE⟩ := atomicOnCarrier_isLocallyAtomicCoefficientFamily _ T hT g hgc
  change T g=0
  rw [hE]
  apply Finset.sum_eq_zero
  intro x _
  by_cases hgx : g x=0
  · rw [hgx,mul_zero]
  · obtain ⟨i,u,m,he⟩ := x.property
    have hphase : |signedPhase u (α i)|<1/2 := by
      cases u <;> simpa [signedPhase,abs_of_pos (hia i).1] using (hia i).2
    have hxsmall : |(n : ℝ)+(x : ℝ)|<1/2 :=
      lt_of_not_ge (fun h => hgx (hf _ h))
    have hnm : |((n+m : ℤ) : ℝ)|<1 := by
      have htri := abs_add_le ((n : ℝ)+(x : ℝ)) (-signedPhase u (α i))
      simp only [← sub_eq_add_neg,abs_neg] at htri
      have he' : (n : ℝ)+(x : ℝ)-signedPhase u (α i)=((n+m : ℤ) : ℝ) := by
        rw [he,Int.cast_add]
        ring
      rw [he'] at htri
      linarith
    have hm : m = -n := by
      have hi : |n+m|<(1 : ℤ) := by exact_mod_cast hnm
      have h := abs_lt.mp hi
      omega
    have hex : x = ⟨criticalHeadPoint α i (!u) (-n),criticalHeadCosetCarrier_contains α (criticalHeadPoint_mem α i (!u) (-n))⟩ := by
      apply Subtype.ext
      rw [he,hm]
      simp only [criticalHeadPoint,signedPhase_eq_criticalSignedPhase]
    rw [hex]
    change criticalHeadCoefficient α (criticalHeadCosetCarrier α)
      (criticalHeadCosetCarrier_contains α) i (!u) (-n) T * _=0
    rw [hz,zero_mul]

/-- An actual Fourier head record is killed by its literal head difference. -/
theorem finiteFourierHead_difference_zero {k : ℕ} (β : Fin k → ℝ)
    (T : TemperedDistribution ℝ ℂ)
    (hFT : AtomicOnCarrier (criticalHeadCosetCarrier β) (𝓕 T)) :
    criticalHeadDifferenceDistributionCLM β T=0 := by
  apply (FourierTransform.fourierEquiv ℂ (TemperedDistribution ℝ ℂ)).injective
  change 𝓕 (criticalHeadDifferenceDistributionCLM β T)=𝓕 (0 : TemperedDistribution ℝ ℂ)
  rw [fourier_criticalHeadDifferenceDistribution,FourierTransform.fourier_zero]
  ext f
  apply hFT
  intro x hx
  change criticalHeadMultiplierTestCLM β f x=0
  rw [criticalHeadMultiplierTestCLM_apply,(criticalHeadTrigProduct_zero_iff β x).mpr hx,zero_mul]

/-- Consecutive whole atomic coefficients on all physical head cosets. -/
def finiteHeadRectangleObservation {k : ℕ} (α : Fin k → ℝ) :
    TemperedDistribution ℝ ℂ →ₗ[ℂ] (Fin k → Bool → Fin (Fintype.card (Fin k × Bool)) → ℂ) :=
  LinearMap.pi (fun i => LinearMap.pi (fun u => LinearMap.pi (fun r =>
    criticalHeadCoefficient α (criticalHeadCosetCarrier α) (criticalHeadCosetCarrier_contains α)
      i u ((k : ℤ)-(r.val : ℤ)))))

/-- The actual finite rectangle determines every complete two-sided head source.
This follows from whole recurrence propagation and atomic coefficient exhaustion. -/
theorem finiteHeadRectangleObservation_kernel {k : ℕ} (hk : 1 ≤ k) (α β : Fin k → ℝ)
    (hia : ∀ i, 0 < α i ∧ α i < 1/2) (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier (criticalHeadCosetCarrier α) T)
    (hFT : AtomicOnCarrier (criticalHeadCosetCarrier β) (𝓕 T))
    (hz : finiteHeadRectangleObservation α T=0) : T=0 := by
  apply atomicOnCarrier_eq_zero_of_cell_tests _ T hT
  · rintro ⟨x,i,u,n,rfl⟩
    refine ⟨n,?_⟩
    simp only [add_sub_cancel_left]
    cases u <;> simpa [signedPhase,abs_of_pos (hia i).1] using (hia i).2
  · intro f hf
    apply criticalHeadDifference_all_test_translates hk β T
      (finiteFourierHead_difference_zero β T hFT) f
    intro r
    apply finiteHead_cell_test_zero α hia T hT f hf
    intro i u
    have h := congrFun (congrFun (congrFun hz i) u) r
    change criticalHeadCoefficient α (criticalHeadCosetCarrier α)
      (criticalHeadCosetCarrier_contains α) i u ((k : ℤ)-(r.val : ℤ)) T=0 at h
    simpa only [neg_sub] using h


/-- The complete two-sided actual head source, with no synthesis assumption. -/
def finiteHeadSource {k : ℕ} (α β : Fin k → ℝ) : Submodule ℂ (TemperedDistribution ℝ ℂ) :=
  pairedAtomicSource (criticalHeadCosetCarrier α) (criticalHeadCosetCarrier β)

/-- Restrict consecutive actual observations to the complete head source. -/
def finiteHeadSourceObservation {k : ℕ} (α β : Fin k → ℝ) :
    finiteHeadSource α β →ₗ[ℂ] (Fin k → Bool → Fin (Fintype.card (Fin k × Bool)) → ℂ) :=
  (finiteHeadRectangleObservation α).comp (finiteHeadSource α β).subtype

/-- The whole head source injects into its literal finite rectangle of readings. -/
theorem finiteHeadSourceObservation_injective {k : ℕ} (hk : 1 ≤ k) (α β : Fin k → ℝ)
    (hia : ∀ i, 0 < α i ∧ α i < 1/2) :
    Function.Injective (finiteHeadSourceObservation α β) := by
  intro T U h
  apply sub_eq_zero.mp
  apply Subtype.ext
  change (T : TemperedDistribution ℝ ℂ)-(U : TemperedDistribution ℝ ℂ)=0
  apply finiteHeadRectangleObservation_kernel hk α β hia _ (T-U).property.1 (T-U).property.2
  change finiteHeadRectangleObservation α ((T : TemperedDistribution ℝ ℂ)-U)=0
  rw [map_sub]
  exact sub_eq_zero.mpr h

/-- Actual complete finite-head sources are finite dimensional by an explicitly
proved whole-source observation injection. -/
theorem finiteHeadSource_finiteDimensional {k : ℕ} (hk : 1 ≤ k) (α β : Fin k → ℝ)
    (hia : ∀ i, 0 < α i ∧ α i < 1/2) : FiniteDimensional ℂ (finiteHeadSource α β) :=
  FiniteDimensional.of_injective (finiteHeadSourceObservation α β)
    (finiteHeadSourceObservation_injective hk α β hia)

/-- Actual whole Poisson synthesis takes values in the complete source. -/
def finiteHeadSourceSynthesis {k : ℕ} (α β : Fin k → ℝ) :
    (Fin k → Fin k → SignedMassBlock) →ₗ[ℂ] finiteHeadSource α β :=
  (criticalPoissonSynthesis α β).codRestrict _ (criticalPoissonSynthesis_atomic_records α β)

/-- The already constructed triangular inverse proves independence of the
actual whole Poisson distributions inside the complete source. -/
theorem finiteHeadSourceSynthesis_injective {k : ℕ} (α β : Fin k → ℝ)
    (ha : Function.Injective α) (hia : ∀ i, 0 < α i ∧ α i < 1/2)
    (hb : Function.Injective β) (hib : ∀ i, 0 < β i ∧ β i < 1/2) :
    Function.Injective (finiteHeadSourceSynthesis α β) := by
  intro c d h
  apply criticalTriangularObservation_synthesis_injective α β ha hia hb hib
    (criticalHeadCosetCarrier α) (criticalHeadCosetCarrier β)
    (criticalHeadCosetCarrier_contains α) (criticalHeadCosetCarrier_contains β)
  exact congrArg (criticalTriangularObservation α β (criticalHeadCosetCarrier α)
    (criticalHeadCosetCarrier β) (criticalHeadCosetCarrier_contains α)
    (criticalHeadCosetCarrier_contains β)) (congrArg Subtype.val h)

/-- The entire actual finite-head source is exactly the whole Poisson span.
Surjectivity follows from the proved consecutive-observation dimension bound
and actual whole-comb independence, not from a representation hypothesis. -/
def finiteHeadPoissonEquiv {k : ℕ} (hk : 1 ≤ k) (α β : Fin k → ℝ)
    (ha : Function.Injective α) (hia : ∀ i, 0 < α i ∧ α i < 1/2)
    (hb : Function.Injective β) (hib : ∀ i, 0 < β i ∧ β i < 1/2) :
    (Fin k → Fin k → SignedMassBlock) ≃ₗ[ℂ] finiteHeadSource α β := by
  letI := finiteHeadSource_finiteDimensional hk α β hia
  apply LinearEquiv.ofInjectiveOfFinrankEq (finiteHeadSourceSynthesis α β)
    (finiteHeadSourceSynthesis_injective α β ha hia hb hib)
  apply le_antisymm
  · exact LinearMap.finrank_le_finrank_of_injective
      (finiteHeadSourceSynthesis_injective α β ha hia hb hib)
  · have h := LinearMap.finrank_le_finrank_of_injective
      (finiteHeadSourceObservation_injective hk α β hia)
    have he : Module.finrank ℂ (Fin k → Bool → Fin (Fintype.card (Fin k × Bool)) → ℂ)=
        Module.finrank ℂ (Fin k → Fin k → SignedMassBlock) := by
      simp only [SignedMassBlock,Module.finrank_pi_fintype,Fintype.card_fin,Fintype.card_bool,
        Fintype.card_prod,Module.finrank_self,Finset.sum_const,Finset.card_univ,nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]
      ring
    exact h.trans_eq he

/-- Every arbitrary actual complete head source has exact whole Poisson
coordinates, simultaneously realizing all physical and Fourier tests. -/
theorem finiteHeadSource_exists_poisson {k : ℕ} (hk : 1 ≤ k) (α β : Fin k → ℝ)
    (ha : Function.Injective α) (hia : ∀ i, 0 < α i ∧ α i < 1/2)
    (hb : Function.Injective β) (hib : ∀ i, 0 < β i ∧ β i < 1/2)
    (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier (criticalHeadCosetCarrier α) T)
    (hFT : AtomicOnCarrier (criticalHeadCosetCarrier β) (𝓕 T)) :
    ∃ c : Fin k → Fin k → SignedMassBlock, criticalPoissonSynthesis α β c=T := by
  obtain ⟨c,hc⟩ := (finiteHeadPoissonEquiv hk α β ha hia hb hib).surjective ⟨T,hT,hFT⟩
  exact ⟨c,congrArg Subtype.val hc⟩


/-- The literal original critical holes annihilate the fixed head-only tests
on the complete original source, including every phase in the infinite tail. -/
theorem criticalHoleTest_original_zero (α : ℕ+ → ℝ)
    (ha : Function.Injective α) (hia : ∀ j, 0 < α j ∧ α j < 1/2) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ) (hT : AtomicOnCarrier (criticalPhaseTailCarrier α hia 0 0) T)
    (h : TriangularHoleIndex k) : T (criticalHoleTest (criticalPrefixPhases α k) h)=0 := by
  apply hT
  rintro y ⟨j,u,n,hn,rfl⟩
  simp only [criticalTailPhases_zero] at *
  by_cases hj : (j : ℕ) ≤ k
  · let i : Fin k := ⟨(j : ℕ)-1,by have := j.pos; omega⟩
    have hij : (⟨i.val+1,by omega⟩ : ℕ+)=j := by
      apply Subtype.ext
      change (j : ℕ)-1+1=(j : ℕ)
      have := j.pos
      omega
    have he : (n : ℝ)+signedPhase u (α j)=criticalHeadPoint (criticalPrefixPhases α k) i (!u) n := by
      simp only [criticalHeadPoint,criticalPrefixPhases,hij,signedPhase_eq_criticalSignedPhase]
    rw [he]
    apply LocallyFiniteCarrier.isolationSchwartz_of_mem_of_ne
    · exact criticalHeadPoint_mem _ _ _ _
    · intro heq
      obtain ⟨hi,_,hn'⟩ := criticalHeadPoint_injective _ (criticalPrefixPhases_injective α ha k)
        (criticalPrefixPhases_inside α hia k) heq
      have hbound := triangularHoleCell_bound h
      have hidx : (j : ℕ)=h.1.val+1 := by
        have hh := congrArg Fin.val hi
        dsimp [i] at hh
        have := j.pos
        omega
      have hnabs : (j : ℕ) ≤ n.natAbs := by simpa using hn
      have hnat : (n.natAbs : ℤ)=|n| := Int.natCast_natAbs n
      rw [← hn'] at hbound
      omega
  · apply criticalHoleTest_zero_on_tail α hia k h
    apply (criticalPhaseTailSet_restored_iff α k _).mpr
    exact ⟨j,u,n,by omega,by simpa using hn,rfl⟩

/-- Every complete original source in the critical head-product kernel is
zero. The proof combines actual whole recurrence reduction, complete finite
Poisson exhaustion, and the signed triangular forbidden-cell inverse. -/
theorem criticalProduct_original_kernel {k : ℕ} (hk : 1 ≤ k)
    (α β : ℕ+ → ℝ)
    (ha : Function.Injective α) (hia : ∀ j, 0 < α j ∧ α j < 1/2)
    (hb : Function.Injective β) (hib : ∀ j, 0 < β j ∧ β j < 1/2)
    (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier (criticalPhaseTailCarrier α hia 0 0) T)
    (hFT : AtomicOnCarrier (criticalPhaseTailCarrier β hib 0 0) (𝓕 T))
    (hR : criticalHeadMultiplierDistributionCLM (criticalPrefixPhases α k)
      (criticalHeadDifferenceDistributionCLM (criticalPrefixPhases β k) T)=0) : T=0 := by
  have hcap := criticalProduct_kernel_finite_records hk α β ha hia hb hib T hT hFT hR
  let a := criticalPrefixPhases α k
  let b := criticalPrefixPhases β k
  let ia := criticalPrefixPhases_injective α ha k
  let ib := criticalPrefixPhases_injective β hb k
  let pa := criticalPrefixPhases_inside α hia k
  let pb := criticalPrefixPhases_inside β hib k
  obtain ⟨c,hc⟩ := finiteHeadSource_exists_poisson hk a b ia pa ib pb T hcap.1 hcap.2
  have hz : criticalTriangularObservation a b (criticalHeadCosetCarrier a) (criticalHeadCosetCarrier b)
      (criticalHeadCosetCarrier_contains a) (criticalHeadCosetCarrier_contains b) T=0 := by
    ext h
    cases h with
    | inl h => exact criticalHoleTest_original_zero α ha hia k T hT h
    | inr h => exact criticalHoleTest_original_zero β hb hib k (𝓕 T) hFT h
  have hcz : c=0 := by
    apply criticalTriangularObservation_synthesis_injective a b ia pa ib pb
      (criticalHeadCosetCarrier a) (criticalHeadCosetCarrier b)
      (criticalHeadCosetCarrier_contains a) (criticalHeadCosetCarrier_contains b)
    simp only [LinearMap.comp_apply,hc,hz,map_zero]
  rw [hcz,map_zero] at hc
  exact hc.symm

end
end MeyerGeneralProblem.Adaptive
