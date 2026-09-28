module

public import MeyerGeneralProblem.Cardinal.Adaptive.CriticalCarrierRepair

@[expose] public section

/-! # Whole bilateral recurrence kernel at the critical head boundary -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open scoped BigOperators FourierTransform

/-- The rightmost coefficient propagates a complete zero window one step
forward in an actual bilateral recurrence. -/
theorem bilateralRecurrence_zero_right {d : ℕ} (c : Fin (d+1) → ℂ)
    (hc : c (Fin.last d) ≠ 0) (u : ℤ → ℂ)
    (hrec : ∀ n, ∑ i : Fin (d+1), c i*u (n+(i.val : ℤ))=0)
    (n : ℤ) (hz : ∀ i : Fin d, u (n+(i.val : ℤ))=0) : u (n+d)=0 := by
  have h := hrec n
  rw [Fin.sum_univ_castSucc] at h
  have hs : (∑ i : Fin d, c i.castSucc*u (n+(i.castSucc.val : ℤ)))=0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [show i.castSucc.val=i.val from rfl,hz i,mul_zero]
  rw [hs,zero_add,Fin.val_last] at h
  exact (mul_eq_zero.mp h).resolve_left hc

/-- The leftmost coefficient propagates the same actual zero window backward. -/
theorem bilateralRecurrence_zero_left {d : ℕ} (c : Fin (d+1) → ℂ)
    (hc : c 0 ≠ 0) (u : ℤ → ℂ)
    (hrec : ∀ n, ∑ i : Fin (d+1), c i*u (n+(i.val : ℤ))=0)
    (n : ℤ) (hz : ∀ i : Fin d, u (n+(i.val : ℤ))=0) : u (n-1)=0 := by
  have h := hrec (n-1)
  rw [Fin.sum_univ_succ] at h
  have hs : (∑ i : Fin d, c i.succ*u (n-1+(i.succ.val : ℤ)))=0 := by
    apply Finset.sum_eq_zero
    intro i _
    have he : n-1+(i.succ.val : ℤ)=n+(i.val : ℤ) := by
      simp only [Fin.val_succ,Nat.cast_add,Nat.cast_one]
      ring
    rw [he,hz i,mul_zero]
  rw [hs,add_zero] at h
  simp only [Fin.val_zero,Nat.cast_zero,add_zero] at h
  exact (mul_eq_zero.mp h).resolve_left hc

/-- A genuine bilateral recurrence with nonzero extreme coefficients has no
nonzero solution with a full consecutive zero window. No decay, periodicity,
or finite support condition is imposed on the sequence. -/
theorem bilateralRecurrence_eq_zero {d : ℕ} (hd : 1 ≤ d) (c : Fin (d+1) → ℂ)
    (hc0 : c 0 ≠ 0) (hcd : c (Fin.last d) ≠ 0) (u : ℤ → ℂ)
    (hrec : ∀ n, ∑ i : Fin (d+1), c i*u (n+(i.val : ℤ))=0)
    (hz : ∀ i : Fin d, u (i.val : ℤ)=0) : ∀ n, u n=0 := by
  have hw : ∀ n : ℤ, ∀ i : Fin d, u (n+(i.val : ℤ))=0 := by
    intro n
    refine Int.induction_on (motive := fun z => ∀ i : Fin d, u (z+(i.val : ℤ))=0) n ?_ ?_ ?_
    · intro i
      simpa only [zero_add] using hz i
    · intro n hn i
      by_cases hi : i.val+1<d
      · have h := hn ⟨i.val+1,hi⟩
        convert h using 1
        simp only [Nat.cast_add,Nat.cast_one]
        congr 1
        ring
      · have he : i.val+1=d := by omega
        have h := bilateralRecurrence_zero_right c hcd u hrec n hn
        convert h using 1
        have he' : (i.val : ℤ)+1=d := by exact_mod_cast he
        congr 1
        omega
    · intro n hn i
      by_cases hi : i.val=0
      · have h := bilateralRecurrence_zero_left c hc0 u hrec (-n) hn
        simpa only [hi,Nat.cast_zero,add_zero] using h
      · have hj : i.val-1<d := by omega
        have h := hn ⟨i.val-1,hj⟩
        convert h using 1
        have he : ((i.val-1 : ℕ) : ℤ)=(i.val : ℤ)-1 := by omega
        rw [he]
        congr 1
        ring
  intro n
  simpa only [Fin.val_zero,Nat.cast_zero,add_zero] using hw n ⟨0,by omega⟩


/-- Both extreme coefficients of the literal critical difference are nonzero. -/
theorem criticalHeadDifferenceCoeff_extremes {k : ℕ} (α : Fin k → ℝ) :
    criticalHeadDifferenceCoeff α 0 ≠ 0 ∧
      criticalHeadDifferenceCoeff α (Fin.last (Fintype.card (Fin k × Bool))) ≠ 0 := by
  have hzero : (criticalHeadPolynomial α).coeff 0 = 1 := by
    rw [Polynomial.coeff_zero_eq_eval_zero,criticalHeadPolynomial_factorization]
    rw [Polynomial.eval_prod]
    simp
  have htop : (criticalHeadPolynomial α).coeff (Fintype.card (Fin k × Bool))=1 := by
    simpa [criticalHeadPolynomial] using
      (Lagrange.nodal_monic (s := Finset.univ) (v := criticalHeadRoots α)).coeff_natDegree
  constructor <;> simp only [criticalHeadDifferenceCoeff,Fin.val_zero,Fin.val_last,hzero,htop,mul_one]
  all_goals exact pow_ne_zero _ (by norm_num)

/-- The actual whole distribution equation yields the exact centered bilateral
recurrence for every translated Schwartz test. -/
theorem criticalHeadDifference_test_recurrence {k : ℕ} (α : Fin k → ℝ)
    (T : TemperedDistribution ℝ ℂ) (hT : criticalHeadDifferenceDistributionCLM α T=0)
    (f : SchwartzMap ℝ ℂ) (n : ℤ) :
    ∑ i : Fin (Fintype.card (Fin k × Bool)+1), criticalHeadDifferenceCoeff α i *
      T (combSchwartzTranslation ((n+(i.val : ℤ)-(k : ℤ) : ℤ) : ℝ) f)=0 := by
  have h := congrArg (fun U : TemperedDistribution ℝ ℂ => U (combSchwartzTranslation (n : ℝ) f)) hT
  change T (criticalHeadDifferenceTestCLM α (combSchwartzTranslation (n : ℝ) f))=0 at h
  simp only [criticalHeadDifferenceTestCLM,_root_.sum_apply,_root_.smul_apply,
    map_sum,map_smul,smul_eq_mul] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  congr 2
  ext x
  simp only [combSchwartzTranslation_apply,Int.cast_add,Int.cast_sub]
  congr 1
  ring

/-- Whole recurrence propagation of the central test window, preserving every
integer translate and the exact centered normalization. -/
theorem criticalHeadDifference_all_test_translates {k : ℕ} (hk : 1 ≤ k) (α : Fin k → ℝ)
    (T : TemperedDistribution ℝ ℂ) (hT : criticalHeadDifferenceDistributionCLM α T=0)
    (f : SchwartzMap ℝ ℂ)
    (hz : ∀ i : Fin (Fintype.card (Fin k × Bool)),
      T (combSchwartzTranslation (((i.val : ℤ)-(k : ℤ) : ℤ) : ℝ) f)=0) :
    ∀ n : ℤ, T (combSchwartzTranslation (n : ℝ) f)=0 := by
  have h := bilateralRecurrence_eq_zero (show 1 ≤ Fintype.card (Fin k × Bool) by simp; omega)
    (criticalHeadDifferenceCoeff α) (criticalHeadDifferenceCoeff_extremes α).1
    (criticalHeadDifferenceCoeff_extremes α).2
    (fun n => T (combSchwartzTranslation (((n : ℤ)-(k : ℤ) : ℤ) : ℝ) f))
    (criticalHeadDifference_test_recurrence α T hT f) hz
  intro n
  simpa only [add_sub_cancel_right] using h (n+k)


/-- The actual restored tail lies beyond the recurrence's entire initial
window; hence its difference kernel annihilates every translated central test. -/
theorem criticalHeadDifference_tail_cell_tests {k : ℕ} (hk : 1 ≤ k) (β : Fin k → ℝ)
    (α : ℕ+ → ℝ) (hia : ∀ j, 0 < α j ∧ α j < 1/2)
    (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier (criticalPhaseTailCarrier α hia k k) T)
    (hD : criticalHeadDifferenceDistributionCLM β T=0)
    (f : SchwartzMap ℝ ℂ) (hf : ∀ x : ℝ, 1/2 ≤ |x| → f x=0) :
    ∀ n : ℤ, T (combSchwartzTranslation (n : ℝ) f)=0 := by
  apply criticalHeadDifference_all_test_translates hk β T hD f
  intro i
  apply hT
  intro x hx
  rw [combSchwartzTranslation_apply]
  apply hf
  have hxlarge := criticalPhaseTail_abs_lower α hia k hx
  have hi : i.val < 2*k := by simpa only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,mul_comm] using i.isLt
  have hn : |(((i.val : ℤ)-(k : ℤ) : ℤ) : ℝ)| ≤ k := by
    rw [Int.cast_sub,Int.cast_natCast,Int.cast_natCast]
    apply abs_le.mpr
    have hi' : (i.val : ℝ) < 2*(k : ℝ) := by exact_mod_cast hi
    constructor <;> nlinarith [show (0 : ℝ) ≤ i.val from Nat.cast_nonneg _]
  have htri := abs_add_le ((((i.val : ℤ)-(k : ℤ) : ℤ) : ℝ)+x)
    (-(((i.val : ℤ)-(k : ℤ) : ℤ) : ℝ))
  simp only [abs_neg] at htri
  rw [show ((((i.val : ℤ)-(k : ℤ) : ℤ) : ℝ)+x)+
      -(((i.val : ℤ)-(k : ℤ) : ℤ) : ℝ)=x by ring] at htri
  linarith


/-- An actual locally finite carrier point in an open integer cell has a
Schwartz isolation test entirely inside that same cell. -/
theorem exists_cell_isolation_test (S : LocallyFiniteCarrier) (z : S.subtype)
    (n : ℤ) (hn : |(z : ℝ)-(n : ℝ)|<1/2) :
    ∃ g : SchwartzMap ℝ ℂ, g z=1 ∧
      (∀ y : ℝ, y ∈ S.carrier → y≠(z : ℝ) → g y=0) ∧
      (∀ y : ℝ, 1/2 ≤ |y-(n : ℝ)| → g y=0) := by
  let r := min (S.isolationRadius z) (1/2-|(z : ℝ)-(n : ℝ)|)
  have hr : 0<r := lt_min (S.isolationRadius_pos z) (by linarith)
  let b : ContDiffBump (z : ℝ) :=
    {rIn := r/4, rOut := r/2, rIn_pos := by positivity, rIn_lt_rOut := by linarith}
  let g : SchwartzMap ℝ ℂ :=
    (b.hasCompactSupport.comp_left (show ((0 : ℝ) : ℂ)=0 by rfl)).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp b.contDiff)
  have hg (y : ℝ) : g y=(b y : ℝ) := rfl
  refine ⟨g,?_,?_,?_⟩
  · rw [hg,b.one_of_mem_closedBall]
    · norm_num
    · simpa using b.rIn_pos.le
  · intro y hy hne
    rw [hg,b.zero_of_le_dist]
    · norm_num
    · change r/2 ≤ dist y (z : ℝ)
      have hm : r ≤ S.isolationRadius z := min_le_left _ _
      have hd := S.isolationRadius_le_dist z hy hne
      linarith
  · intro y hy
    rw [hg,b.zero_of_le_dist]
    · norm_num
    · change r/2 ≤ dist y (z : ℝ)
      have hm : r ≤ 1/2-|(z : ℝ)-(n : ℝ)| := min_le_right _ _
      have ht := abs_add_le (y-(z : ℝ)) ((z : ℝ)-(n : ℝ))
      rw [sub_add_sub_cancel] at ht
      rw [Real.dist_eq]
      linarith

/-- On a genuine locally finite carrier, zero canonical atomic coefficients
force the entire original tempered distribution to vanish. -/
theorem atomicOnCarrier_eq_zero_of_isolation_zero (S : LocallyFiniteCarrier)
    (T : TemperedDistribution ℝ ℂ) (hT : AtomicOnCarrier S T)
    (hz : ∀ z : S.subtype, T (S.isolationSchwartz z)=0) : T=0 := by
  ext f
  have hzero : ∀ N : ℕ, T (compactSchwartzApproximation N f)=0 := by
    intro N
    obtain ⟨E,_,hE⟩ := atomicOnCarrier_isLocallyAtomicCoefficientFamily S T hT
      (compactSchwartzApproximation N f) (compactSchwartzApproximation_hasCompactSupport N f)
    rw [hE]
    simp only [hz,zero_mul,Finset.sum_const_zero]
  have hlim := (T.continuous.tendsto f).comp (compactSchwartzApproximation_tendsto f)
  have hlim0 : Filter.Tendsto (fun N => T (compactSchwartzApproximation N f))
      Filter.atTop (nhds (0 : ℂ)) := by
    simpa only [hzero] using
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (0 : ℂ)) Filter.atTop (nhds 0))
  exact tendsto_nhds_unique hlim hlim0

/-- Vanishing of every actual open-cell test and its integer translates
exhausts a complete value-only source whose carrier has no seam atoms. -/
theorem atomicOnCarrier_eq_zero_of_cell_tests (S : LocallyFiniteCarrier)
    (T : TemperedDistribution ℝ ℂ) (hT : AtomicOnCarrier S T)
    (hcell : ∀ z : S.subtype, ∃ n : ℤ, |(z : ℝ)-(n : ℝ)|<1/2)
    (hz : ∀ f : SchwartzMap ℝ ℂ, (∀ x : ℝ, 1/2 ≤ |x| → f x=0) →
      ∀ n : ℤ, T (combSchwartzTranslation (n : ℝ) f)=0) : T=0 := by
  apply atomicOnCarrier_eq_zero_of_isolation_zero S T hT
  intro z
  obtain ⟨n,hn⟩ := hcell z
  obtain ⟨g,hgz,hgo,hgs⟩ := exists_cell_isolation_test S z n hn
  have hg : T g=0 := by
    let f := combSchwartzTranslation (n : ℝ) g
    have hf : ∀ x : ℝ, 1/2 ≤ |x| → f x=0 := by
      intro x hx
      change g ((n : ℝ)+x)=0
      apply hgs
      simpa only [add_sub_cancel_left] using hx
    have hh := hz f hf (-n)
    have he : combSchwartzTranslation ((-n : ℤ) : ℝ) f=g := by
      ext x
      simp only [f,combSchwartzTranslation_apply,Int.cast_neg]
      congr 1
      ring
    rwa [he] at hh
  have he : T (S.isolationSchwartz z-g)=0 := by
    apply hT
    intro y hy
    simp only [_root_.sub_apply]
    by_cases he : y=(z : ℝ)
    · subst y
      rw [S.isolationSchwartz_self,hgz,sub_self]
    · rw [S.isolationSchwartz_of_mem_of_ne z hy he,hgo y hy he,sub_self]
  rw [map_sub,hg,sub_zero] at he
  exact he

/-- The complete actual restored tail has trivial kernel under the exact
critical difference. This is whole-source propagation, not a finite coefficient surrogate. -/
theorem criticalHeadDifference_tail_kernel {k : ℕ} (hk : 1 ≤ k) (β : Fin k → ℝ)
    (α : ℕ+ → ℝ) (hia : ∀ j, 0 < α j ∧ α j < 1/2)
    (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier (criticalPhaseTailCarrier α hia k k) T)
    (hD : criticalHeadDifferenceDistributionCLM β T=0) : T=0 := by
  apply atomicOnCarrier_eq_zero_of_cell_tests _ T hT
  · rintro ⟨x,j,u,n,hn,rfl⟩
    refine ⟨n,?_⟩
    simpa only [add_sub_cancel_left] using criticalTailPhase_abs_lt_half α hia k j u
  · exact criticalHeadDifference_tail_cell_tests hk β α hia T hT hD


/-- Applying the actual prefix multiplier to a complete original critical
record leaves precisely the original scheduled tail support. -/
theorem criticalPrefixMultiplier_original_tail (α : ℕ+ → ℝ)
    (hia : ∀ j, 0 < α j ∧ α j < 1/2) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier (criticalPhaseTailCarrier α hia 0 0) T) :
    AtomicOnCarrier (criticalPhaseTailCarrier α hia k k)
      (criticalHeadMultiplierDistributionCLM (criticalPrefixPhases α k) T) := by
  intro f hf
  change T (criticalHeadMultiplierTestCLM (criticalPrefixPhases α k) f)=0
  apply hT
  rintro x ⟨j,u,n,hn,rfl⟩
  rw [criticalHeadMultiplierTestCLM_apply]
  simp only [criticalTailPhases_zero] at *
  by_cases hj : (j : ℕ) ≤ k
  · have hx : (n : ℝ)+signedPhase u (α j) ∈ criticalHeadCosetSet (criticalPrefixPhases α k) := by
      let i : Fin k := ⟨(j : ℕ)-1,by have := j.pos; omega⟩
      refine ⟨i,u,n,?_⟩
      have he : (⟨i.val+1,by omega⟩ : ℕ+)=j := by
        apply Subtype.ext
        change (j : ℕ)-1+1=(j : ℕ)
        have := j.pos
        omega
      simp only [criticalPrefixPhases,he]
    rw [(criticalHeadTrigProduct_zero_iff _ _).mpr hx,zero_mul]
  · have hx : (n : ℝ)+signedPhase u (α j) ∈ criticalPhaseTailSet α k k := by
      apply (criticalPhaseTailSet_restored_iff α k _).mpr
      exact ⟨j,u,n,by omega,by simpa using hn,rfl⟩
    rw [hf _ hx,mul_zero]

/-- The two literal head operators commute on the entire original tempered space. -/
theorem criticalHeadMultiplier_difference_commute {k l : ℕ} (α : Fin k → ℝ) (β : Fin l → ℝ)
    (T : TemperedDistribution ℝ ℂ) :
    criticalHeadMultiplierDistributionCLM α (criticalHeadDifferenceDistributionCLM β T)=
      criticalHeadDifferenceDistributionCLM β (criticalHeadMultiplierDistributionCLM α T) := by
  ext f
  change T (criticalHeadDifferenceTestCLM β (criticalHeadMultiplierTestCLM α f))=
    T (criticalHeadMultiplierTestCLM α (criticalHeadDifferenceTestCLM β f))
  congr 1
  ext x
  rw [criticalHeadDifferenceTestCLM_apply,criticalHeadMultiplierTestCLM_apply,
    criticalHeadDifferenceTestCLM_apply,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [criticalHeadMultiplierTestCLM_apply]
  have hp : criticalHeadTrigProduct α (x+((((i.val : ℤ)-(l : ℤ)) : ℤ) : ℝ))=
      criticalHeadTrigProduct α x := by
    simpa using (criticalHeadTrigProduct_periodic α).int_mul ((i.val : ℤ)-(l : ℤ)) x
  rw [hp]
  ring

/-- A vector in the whole critical product kernel already lies in the actual
prefix multiplier kernel. This is the source-level finite-cap reduction. -/
theorem criticalProduct_kernel_prefix_multiplier {k : ℕ} (hk : 1 ≤ k)
    (α : ℕ+ → ℝ) (hia : ∀ j, 0 < α j ∧ α j < 1/2) (β : Fin k → ℝ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier (criticalPhaseTailCarrier α hia 0 0) T)
    (hR : criticalHeadMultiplierDistributionCLM (criticalPrefixPhases α k)
      (criticalHeadDifferenceDistributionCLM β T)=0) :
    criticalHeadMultiplierDistributionCLM (criticalPrefixPhases α k) T=0 := by
  apply criticalHeadDifference_tail_kernel hk β α hia _
    (criticalPrefixMultiplier_original_tail α hia k T hT)
  rw [← criticalHeadMultiplier_difference_commute]
  exact hR


/-- The kernel of the actual simple-zero head multiplier is a complete
value-only source on the corresponding full signed head cosets. -/
theorem criticalHeadMultiplier_kernel_atomic {k : ℕ} (α : Fin k → ℝ)
    (ha : Function.Injective α) (hia : ∀ i, 0 < α i ∧ α i < 1/2)
    (T : TemperedDistribution ℝ ℂ) (hT : criticalHeadMultiplierDistributionCLM α T=0) :
    AtomicOnCarrier (criticalHeadCosetCarrier α) T := by
  let Z : LocallyFiniteCarrier := {carrier := ∅,finite_inter_Icc := by intro a b; simp}
  have hz : AtomicOnCarrier Z (criticalHeadMultiplierDistributionCLM α T) := by
    rw [hT]
    intro f hf
    rfl
  have h := criticalHeadMultiplier_recovers_atomic α ha hia Z
    (fun x hx => False.elim hx) T hz
  intro f hf
  apply h
  intro x hx
  rcases hx with hx|hx
  · exact hf x hx
  · exact False.elim hx

/-- A complete physical finite-cap source in the original paired critical
space also has the corresponding complete Fourier finite cap. -/
theorem criticalPhysicalCap_implies_fourierCap {k : ℕ} (hk : 1 ≤ k)
    (α : Fin k → ℝ) (β : ℕ+ → ℝ)
    (hb : Function.Injective β) (hib : ∀ j, 0 < β j ∧ β j < 1/2)
    (T : TemperedDistribution ℝ ℂ)
    (hFT : AtomicOnCarrier (criticalPhaseTailCarrier β hib 0 0) (𝓕 T))
    (hA : criticalHeadMultiplierDistributionCLM α T=0) :
    AtomicOnCarrier (criticalHeadCosetCarrier (criticalPrefixPhases β k)) (𝓕 T) := by
  apply criticalHeadMultiplier_kernel_atomic _ (criticalPrefixPhases_injective β hb k)
    (criticalPrefixPhases_inside β hib k)
  apply criticalHeadDifference_tail_kernel hk α β hib _
    (criticalPrefixMultiplier_original_tail β hib k (𝓕 T) hFT)
  rw [← criticalHeadMultiplier_difference_commute,← fourier_criticalHeadMultiplierDistribution,hA]
  simp only [FourierTransform.fourier_zero,map_zero]

/-- The complete critical product kernel is an actual two-sided finite-cap
source. The next remaining implication is its whole finite Poisson representation. -/
theorem criticalProduct_kernel_finite_records {k : ℕ} (hk : 1 ≤ k)
    (α β : ℕ+ → ℝ)
    (ha : Function.Injective α) (hia : ∀ j, 0 < α j ∧ α j < 1/2)
    (hb : Function.Injective β) (hib : ∀ j, 0 < β j ∧ β j < 1/2)
    (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier (criticalPhaseTailCarrier α hia 0 0) T)
    (hFT : AtomicOnCarrier (criticalPhaseTailCarrier β hib 0 0) (𝓕 T))
    (hR : criticalHeadMultiplierDistributionCLM (criticalPrefixPhases α k)
      (criticalHeadDifferenceDistributionCLM (criticalPrefixPhases β k) T)=0) :
    AtomicOnCarrier (criticalHeadCosetCarrier (criticalPrefixPhases α k)) T ∧
    AtomicOnCarrier (criticalHeadCosetCarrier (criticalPrefixPhases β k)) (𝓕 T) := by
  have hA := criticalProduct_kernel_prefix_multiplier hk α hia (criticalPrefixPhases β k) T hT hR
  exact ⟨criticalHeadMultiplier_kernel_atomic _ (criticalPrefixPhases_injective α ha k)
    (criticalPrefixPhases_inside α hia k) T hA,
    criticalPhysicalCap_implies_fourierCap hk _ β hb hib T hFT hA⟩

end
end MeyerGeneralProblem.Adaptive
