module

public import MeyerGeneralProblem.Cardinal.Adaptive.CriticalGreenNativeBounds
public import MeyerGeneralProblem.Cardinal.Adaptive.ConcreteHoleCarriers

@[expose] public section

/-! # Whole Green support restoration for an arbitrary infinite critical tail -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section

/-- Reindex a full infinite phase sequence after its first k phases. -/
def criticalTailPhases (α : ℕ+ → ℝ) (k : ℕ) (j : ℕ+) : ℝ :=
  α ⟨k+(j : ℕ),by have := j.pos; omega⟩

/-- Zero reindexing retains the original infinite sequence exactly. -/
theorem criticalTailPhases_zero (α : ℕ+ → ℝ) : criticalTailPhases α 0 = α := by
  funext j
  apply congrArg α
  apply Subtype.ext
  exact Nat.zero_add _

/-- The full reindexed critical tail, with d additional deleted integer cells.
At d=0 this is the tail's own critical schedule; at d=k its original schedule. -/
def criticalPhaseTailSet (α : ℕ+ → ℝ) (k d : ℕ) : Set ℝ :=
  {x | ∃ (j : ℕ+) (positive : Bool) (n : ℤ), (j : ℕ)+d ≤ n.natAbs ∧
    x = (n : ℝ)+signedPhase positive (criticalTailPhases α k j)}

/-- Every signed arbitrary interior phase has absolute value less than half. -/
theorem criticalTailPhase_abs_lt_half (α : ℕ+ → ℝ)
    (hi : ∀ j, 0 < α j ∧ α j < 1/2) (k : ℕ) (j : ℕ+) (u : Bool) :
    |signedPhase u (criticalTailPhases α k j)| < 1/2 := by
  have h := hi ⟨k+(j : ℕ),by have := j.pos; omega⟩
  cases u <;> simpa [signedPhase,criticalTailPhases,abs_of_pos h.1] using h.2

/-- Local finiteness comes from the unbounded original cell thresholds, without
any uniform phase separation and without cutting the infinite phase tail. -/
theorem criticalPhaseTailSet_finite_inter_Icc (α : ℕ+ → ℝ)
    (hi : ∀ j, 0 < α j ∧ α j < 1/2) (k d : ℕ) (a b : ℝ) :
    (criticalPhaseTailSet α k d ∩ Set.Icc a b).Finite := by
  obtain ⟨N : ℕ,hN⟩ := exists_nat_gt (max |a| |b|+1)
  let f : ℕ × Bool × ℤ → ℝ := fun q => (q.2.2 : ℝ)+
    signedPhase q.2.1 (criticalTailPhases α k ⟨max q.1 1,by omega⟩)
  have hf : ((Set.Icc 1 N) ×ˢ ((Set.univ : Set Bool) ×ˢ
      Set.Icc (-(N : ℤ)) (N : ℤ))).Finite :=
    (Set.finite_Icc 1 N).prod (Set.finite_univ.prod (Set.finite_Icc _ _))
  apply (hf.image f).subset
  rintro x ⟨⟨j,u,n,hn,hx⟩,hxa,hxb⟩
  have hxabs : |x| ≤ max |a| |b| := by
    apply abs_le.mpr
    constructor
    · have := neg_abs_le a; have := le_max_left |a| |b|; linarith
    · exact hxb.trans ((le_abs_self b).trans (le_max_right |a| |b|))
  have hphase := criticalTailPhase_abs_lt_half α hi k j u
  have hnreal : |(n : ℝ)| < N := by
    have ht := abs_sub_le (n : ℝ) x 0
    rw [hx] at ht
    simp only [sub_add_cancel_left,sub_zero,abs_neg] at ht
    rw [← hx] at ht
    linarith
  have hnabs : n.natAbs ≤ N := by
    have hc : (n.natAbs : ℝ) ≤ N := by simpa using hnreal.le
    exact_mod_cast hc
  refine ⟨((j : ℕ),u,n),⟨⟨j.pos,by omega⟩,Set.mem_univ _,?_⟩,?_⟩
  · obtain ⟨hl,hr⟩ := abs_le.mp hnreal.le
    constructor
    · exact_mod_cast hl
    · exact_mod_cast hr
  · have hj : (⟨max (j : ℕ) 1,by omega⟩ : ℕ+) = j := by
      apply Subtype.ext
      exact Nat.max_eq_left j.pos
    change (n : ℝ)+signedPhase u (criticalTailPhases α k _) = x
    rw [hj]
    exact hx.symm

/-- The actual complete reindexed or restored critical tail as a locally finite carrier. -/
def criticalPhaseTailCarrier (α : ℕ+ → ℝ)
    (hi : ∀ j, 0 < α j ∧ α j < 1/2) (k d : ℕ) : LocallyFiniteCarrier where
  carrier := criticalPhaseTailSet α k d
  finite_inter_Icc := criticalPhaseTailSet_finite_inter_Icc α hi k d

/-- Positive translations of at least k restore every original positive hole. -/
theorem criticalPhaseTail_positive_shift (α : ℕ+ → ℝ)
    (hi : ∀ j, 0 < α j ∧ α j < 1/2) (k : ℕ) {x : ℝ}
    (hx : x ∈ criticalPhaseTailSet α k 0) (hpos : -1/4 ≤ x)
    (t : ℤ) (ht : (k : ℤ) ≤ t) : x+(t : ℝ) ∈ criticalPhaseTailSet α k k := by
  obtain ⟨j,u,n,hn,rfl⟩ := hx
  have ha := criticalTailPhase_abs_lt_half α hi k j u
  have hnpos : 0 ≤ n := by
    by_contra h
    have hnle : n ≤ -1 := by omega
    have hnle' : (n : ℝ) ≤ -1 := by exact_mod_cast hnle
    have := (abs_lt.mp ha).2
    linarith
  have htpos : 0 ≤ t := by omega
  refine ⟨j,u,n+t,?_,by push_cast; ring⟩
  have hnabs : (n.natAbs : ℤ) = n := Int.natAbs_of_nonneg hnpos
  have habs : ((n+t).natAbs : ℤ) = n+t := Int.natAbs_of_nonneg (by omega)
  omega

/-- Negative translations restore every original negative hole as well. -/
theorem criticalPhaseTail_negative_shift (α : ℕ+ → ℝ)
    (hi : ∀ j, 0 < α j ∧ α j < 1/2) (k : ℕ) {x : ℝ}
    (hx : x ∈ criticalPhaseTailSet α k 0) (hneg : x ≤ 1/4)
    (t : ℤ) (ht : t ≤ -(k : ℤ)) : x+(t : ℝ) ∈ criticalPhaseTailSet α k k := by
  obtain ⟨j,u,n,hn,rfl⟩ := hx
  have ha := criticalTailPhase_abs_lt_half α hi k j u
  have hnneg : n ≤ 0 := by
    by_contra h
    have hnle : 1 ≤ n := by omega
    have hnle' : (1 : ℝ) ≤ n := by exact_mod_cast hnle
    have := (abs_lt.mp ha).1
    linarith
  have htneg : t ≤ 0 := by omega
  refine ⟨j,u,n+t,?_,by push_cast; ring⟩
  have hnabs : (n.natAbs : ℤ) = -n := by
    rw [← Int.natAbs_neg]
    exact Int.natAbs_of_nonneg (by omega)
  have habs : ((n+t).natAbs : ℤ) = -(n+t) := by
    rw [← Int.natAbs_neg]
    exact Int.natAbs_of_nonneg (by omega)
  omega

/-- The actual Green transpose sends the full restored-tail vanishing ideal
into the full reindexed-tail vanishing ideal. -/
theorem criticalGreenTestCLM_restores_tail_vanishing {k : ℕ} (β : Fin k → ℝ)
    (hb : Function.Injective β) (hib : ∀ i, 0 < β i ∧ β i < 1/2)
    (α : ℕ+ → ℝ) (hi : ∀ j, 0 < α j ∧ α j < 1/2)
    (f : SchwartzMap ℝ ℂ) (hf : SchwartzVanishesOn (criticalPhaseTailCarrier α hi k k) f) :
    SchwartzVanishesOn (criticalPhaseTailCarrier α hi k 0) (criticalGreenTestCLM β hb hib f) := by
  intro x hx
  rw [criticalGreenTestCLM_apply]
  have hp : ∀ n : ℕ, criticalHeadGreen true β ((n : ℤ)+1) *
      (criticalPositiveCutoff x*f (x+((n : ℝ)+1))) = 0 := by
    intro n
    by_cases hn : ((n : ℤ)+1) < k
    · simp only [criticalHeadGreen,ite_true,criticalHeadPositiveGreen_eq_zero β _ hn,mul_zero,zero_mul]
    by_cases hxpos : x ≤ -1/4
    · rw [criticalPositiveCutoff_eq_zero hxpos,zero_mul,mul_zero]
    have hz := hf (x+(((n : ℤ)+1 : ℤ) : ℝ))
      (criticalPhaseTail_positive_shift α hi k hx (by linarith) _ (by omega))
    simp only [Int.cast_add,Int.cast_natCast,Int.cast_one] at hz
    rw [hz,mul_zero,mul_zero]
  have hm : ∀ n : ℕ, criticalHeadGreen false β (-((n : ℤ)+1)) *
      (criticalNegativeCutoff x*f (x-((n : ℝ)+1))) = 0 := by
    intro n
    by_cases hn : ((n : ℤ)+1) < k
    · have hz := criticalHeadNegativeGreen_eq_zero β (-((n : ℤ)+1)) (by omega)
      simp only [criticalHeadGreen,Bool.false_eq_true,ite_false,hz,mul_zero,zero_mul]
    by_cases hxneg : 1/4 ≤ x
    · simp only [criticalNegativeCutoff,criticalPositiveCutoff_eq_one hxneg,sub_self,zero_mul,mul_zero]
    have hz := hf (x+((-((n : ℤ)+1) : ℤ) : ℝ))
      (criticalPhaseTail_negative_shift α hi k hx (by linarith) _ (by omega))
    simp only [Int.cast_neg,Int.cast_add,Int.cast_natCast,Int.cast_one,← sub_eq_add_neg] at hz
    rw [hz,mul_zero,mul_zero]
  simp only [hp,hm,tsum_zero,zero_add]

/-- Whole atomic support and value-only action survive the actual inverse,
restoring ALL original holes of the arbitrary infinite phase tail. -/
theorem criticalGreenDistribution_restores_tail {k : ℕ} (β : Fin k → ℝ)
    (hb : Function.Injective β) (hib : ∀ i, 0 < β i ∧ β i < 1/2)
    (α : ℕ+ → ℝ) (hi : ∀ j, 0 < α j ∧ α j < 1/2)
    (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier (criticalPhaseTailCarrier α hi k 0) T) :
    AtomicOnCarrier (criticalPhaseTailCarrier α hi k k) (criticalGreenDistributionCLM β hb hib T) := by
  intro f hf
  rw [criticalGreenDistributionCLM_apply]
  exact hT _ (criticalGreenTestCLM_restores_tail_vanishing β hb hib α hi f hf)

/-- The constructed native inverse has the same complete tail restoration,
with precisely its proved one-order loss. -/
theorem criticalGreenNativeCLM_restores_tail {k : ℕ} (β : Fin k → ℝ)
    (hb : Function.Injective β) (hib : ∀ i, 0 < β i ∧ β i < 1/2)
    (α : ℕ+ → ℝ) (hi : ∀ j, 0 < α j ∧ α j < 1/2)
    (p : ℕ) (T : HermiteScale (-(p : ℤ)))
    (hT : AtomicOnCarrier (criticalPhaseTailCarrier α hi k 0) (hermiteScaleDistribution p T)) :
    AtomicOnCarrier (criticalPhaseTailCarrier α hi k k)
      (hermiteScaleDistribution (p+1) (criticalGreenNativeCLM β hb hib p T)) := by
  rw [criticalGreenNativeCLM_realizes]
  exact criticalGreenDistribution_restores_tail β hb hib α hi _ hT

/-- At zero truncation this generic full source is the concrete original critical block. -/
theorem criticalPhaseTailSet_block_zero (P R : ℕ) :
    criticalPhaseTailSet (blockPhase P R) 0 0 = criticalBlockSet P R := by
  ext x
  simp only [criticalPhaseTailSet,criticalBlockSet,Set.mem_ofPred_eq,Nat.add_zero,
    criticalTailPhases_zero]

/-- Restoring the first k holes retains exactly the original infinite phase
indices beyond k, rather than an arbitrary finite-cap replacement. -/
theorem criticalPhaseTailSet_restored_iff (α : ℕ+ → ℝ) (k : ℕ) (x : ℝ) :
    x ∈ criticalPhaseTailSet α k k ↔ ∃ (j : ℕ+) (u : Bool) (n : ℤ),
      k < (j : ℕ) ∧ (j : ℕ) ≤ n.natAbs ∧ x = (n : ℝ)+signedPhase u (α j) := by
  constructor
  · rintro ⟨j,u,n,hn,hx⟩
    refine ⟨⟨k+(j : ℕ),by have := j.pos; omega⟩,u,n,?_,?_,hx⟩
    · change k < k+(j : ℕ); have := j.pos; omega
    · change k+(j : ℕ) ≤ n.natAbs; omega
  · rintro ⟨j,u,n,hj,hn,hx⟩
    let i : ℕ+ := ⟨(j : ℕ)-k,by omega⟩
    have he : (⟨k+(i : ℕ),by have := i.pos; omega⟩ : ℕ+) = j := by
      apply Subtype.ext
      change k+((j : ℕ)-k)=(j : ℕ)
      omega
    refine ⟨i,u,n,by dsimp [i]; omega,?_⟩
    simpa only [criticalTailPhases,he] using hx

/-- The actual infinite scheduled rapid tail is precisely the restored carrier. -/
theorem criticalPhaseTailSet_block_restored (P R : ℕ) :
    criticalPhaseTailSet (blockPhase P R) (headLength R) (headLength R) =
      scheduledTailSet P R := by
  ext x
  exact criticalPhaseTailSet_restored_iff _ _ x

/-- Restoration never introduces an atom outside the original critical carrier. -/
theorem criticalPhaseTailSet_restored_subset (α : ℕ+ → ℝ) (k : ℕ) :
    criticalPhaseTailSet α k k ⊆ criticalPhaseTailSet α 0 0 := by
  intro x hx
  obtain ⟨j,u,n,_,hn,hx⟩ := (criticalPhaseTailSet_restored_iff α k x).mp hx
  refine ⟨j,u,n,by simpa using hn,?_⟩
  simpa only [criticalTailPhases_zero] using hx

end
end MeyerGeneralProblem.Adaptive
