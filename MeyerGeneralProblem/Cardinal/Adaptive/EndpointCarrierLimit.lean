module

public import MeyerGeneralProblem.Cardinal.Adaptive.EndpointReflection
public import MeyerGeneralProblem.Cardinal.Adaptive.NativeWeakCompactness

@[expose] public section

/-! # Exact compact-set stabilization of the finite endpoint carriers -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open Set Filter
open scoped Topology FourierTransform

/-- The zero-based finite prefix of a positive-indexed infinite phase family. -/
def endpointPhasePrefix (α : ℕ+ → ℝ) (k : ℕ) (i : Fin k) : ℝ :=
  α ⟨i.val+1,by omega⟩

theorem endpointPhasePrefix_injective (α : ℕ+ → ℝ) (ha : Function.Injective α) (k : ℕ) :
    Function.Injective (endpointPhasePrefix α k) := by
  intro i j he
  have h := congrArg Subtype.val (ha he)
  apply Fin.ext
  dsimp at h
  omega

theorem endpointPhasePrefix_interior (α : ℕ+ → ℝ)
    (hi : ∀ j, 0 < α j ∧ α j < 1/2) (k : ℕ) (i : Fin k) :
    0 < endpointPhasePrefix α k i ∧ endpointPhasePrefix α k i < 1/2 := hi _

/-- The actual forbidden integer cells at an interior signed phase. -/
theorem endpointHoleSet_some_iff {k : ℕ} (α : Fin k → ℝ)
    (ha : Function.Injective α) (hi : ∀ i, 0 < α i ∧ α i < 1/2)
    (i : Fin k) (u : Bool) (n : ℤ) :
    (endpointPoint α (some (i,u)) n : ℝ) ∈ endpointHoleSet α ↔ |n| ≤ (i : ℤ) := by
  constructor
  · rintro ⟨h,he⟩
    cases h with
    | inl h =>
      have hh := endpointPoint_injective α ha hi he
      have hp := Option.some_injective _ hh.1
      have hn := triangularHoleCell_bound h
      have hi' : h.1=i := congrArg Prod.fst hp
      simpa only [hi',hh.2] using hn
    | inr r =>
      have hh := endpointPoint_injective α ha hi he
      cases hh.1
  · intro hn
    obtain ⟨h,he1,he2,he3⟩ := triangularHoleCell_surjective i u n hn
    refine ⟨.inl h,?_⟩
    change endpointPhase α (some (h.1,h.2.1))+(triangularHoleCell h : ℝ)=_
    simp only [he1,he2,he3,endpointPoint]

/-- The single endpoint has exactly `2k` forbidden cells, with no duplicated seam. -/
theorem endpointHoleSet_none_iff {k : ℕ} (α : Fin k → ℝ)
    (ha : Function.Injective α) (hi : ∀ i, 0 < α i ∧ α i < 1/2) (n : ℤ) :
    (endpointPoint α none n : ℝ) ∈ endpointHoleSet α ↔ -(k : ℤ) ≤ n ∧ n < k := by
  constructor
  · rintro ⟨h,he⟩
    cases h with
    | inl h =>
      have hh := endpointPoint_injective α ha hi he
      cases hh.1
    | inr r =>
      have hh := (endpointPoint_injective α ha hi he).2
      have hr := r.isLt
      change -(k : ℤ)+(r.val : ℤ)=n at hh
      omega
  · rintro ⟨hlo,hhi⟩
    let r : Fin (2*k) := ⟨(n+k).toNat,by omega⟩
    refine ⟨.inr r,?_⟩
    change (1/2 : ℝ)+(-(k : ℤ)+(r.val : ℤ) : ℤ)=(1/2 : ℝ)+(n : ℝ)
    have hr : -(k : ℤ)+(r.val : ℤ)=n := by dsimp [r]; omega
    rw [hr]

/-- The deleted family has exactly its original interior tails and one escaping
half-integer tail. This identifies the literal carrier, not merely its closure. -/
theorem endpointDeletedCarrier_mem_iff {k : ℕ} (α : Fin k → ℝ)
    (ha : Function.Injective α) (hi : ∀ i, 0 < α i ∧ α i < 1/2) (x : ℝ) :
    x ∈ (endpointDeletedCarrier α).carrier ↔
      (∃ (i : Fin k) (u : Bool) (n : ℤ), i.val < n.natAbs ∧ x=criticalSignedPhase u (α i)+n) ∨
      (∃ n : ℤ, (n < -(k : ℤ) ∨ (k : ℤ) ≤ n) ∧ x=1/2+n) := by
  constructor
  · rintro ⟨⟨a,n,rfl⟩,hn⟩
    cases a with
    | none =>
      right
      refine ⟨n,?_,rfl⟩
      have hh := mt (endpointHoleSet_none_iff α ha hi n).mpr hn
      omega
    | some a =>
      rcases a with ⟨i,u⟩
      left
      refine ⟨i,u,n,?_,rfl⟩
      have hh := mt (endpointHoleSet_some_iff α ha hi i u n).mpr hn
      have habs : (n.natAbs : ℤ)=|n| := Int.natCast_natAbs n
      omega
  · rintro (⟨i,u,n,hn,rfl⟩|⟨n,hn,rfl⟩)
    · refine ⟨⟨some (i,u),n,rfl⟩,?_⟩
      intro hh
      have he := (endpointHoleSet_some_iff α ha hi i u n).mp hh
      have habs : (n.natAbs : ℤ)=|n| := Int.natCast_natAbs n
      omega
    · refine ⟨⟨none,n,rfl⟩,?_⟩
      intro hh
      have he := (endpointHoleSet_none_iff α ha hi n).mp hh
      omega

/-- Away from the escaping endpoint cells, a sufficiently long literal finite
prefix agrees exactly with the original infinite critical schedule. -/
theorem endpointPrefix_mem_iff_of_abs_lt (α : ℕ+ → ℝ) (ha : Function.Injective α)
    (hi : ∀ j, 0 < α j ∧ α j < 1/2) (k : ℕ) (x : ℝ) (hx : |x|+1 < k) :
    x ∈ (endpointDeletedCarrier (endpointPhasePrefix α k)).carrier ↔
      x ∈ criticalPhaseTailSet α 0 0 := by
  rw [endpointDeletedCarrier_mem_iff _ (endpointPhasePrefix_injective α ha k)
    (endpointPhasePrefix_interior α hi k)]
  constructor
  · rintro (⟨i,u,n,hn,he⟩|⟨n,hn,he⟩)
    · refine ⟨⟨i.val+1,by omega⟩,!u,n,by dsimp; omega,?_⟩
      rw [he]
      simp only [criticalTailPhases_zero,endpointPhasePrefix,signedPhase_eq_criticalSignedPhase,Bool.not_not]
      ring
    · exfalso
      have hxlo := neg_abs_le x
      have hxhi := le_abs_self x
      rcases hn with hn|hn
      · have hn' : (n : ℝ) ≤ -(k : ℝ)-1 := by exact_mod_cast (show n ≤ -(k : ℤ)-1 by omega)
        linarith
      · have hn' : (k : ℝ) ≤ n := by exact_mod_cast hn
        linarith
  · rintro ⟨j,u,n,hn,he⟩
    simp only [criticalTailPhases_zero] at he
    have hp := criticalTailPhase_abs_lt_half α hi 0 j u
    simp only [criticalTailPhases_zero] at hp
    have hnr : (n.natAbs : ℝ) < k := by
      have ht := abs_sub_le x 0 (signedPhase u (α j))
      simp only [sub_zero,zero_sub,abs_neg] at ht
      have he' : x-signedPhase u (α j)=(n : ℝ) := by rw [he]; ring
      rw [he'] at ht
      have heabs : |(n : ℝ)|=(n.natAbs : ℝ) := by simp
      rw [heabs] at ht
      linarith
    have hnk : n.natAbs < k := by exact_mod_cast hnr
    let i : Fin k := ⟨(j : ℕ)-1,by have := j.pos; omega⟩
    have hj : (⟨i.val+1,by omega⟩ : ℕ+)=j := by
      apply Subtype.ext
      change (j : ℕ)-1+1=(j : ℕ)
      exact Nat.sub_add_cancel j.pos
    left
    refine ⟨i,!u,n,by dsimp [i]; have := j.pos; omega,?_⟩
    rw [he]
    simp only [endpointPhasePrefix,hj,signedPhase_eq_criticalSignedPhase]
    ring

/-- Exact eventual equality on every compact set pays the carrier premise of
the original-norm weak-limit theorem; it does not use convergence of individual atoms. -/
theorem endpointDeletedCarrier_eventually_locally_equal (α : ℕ+ → ℝ) (ha : Function.Injective α)
    (hi : ∀ j, 0 < α j ∧ α j < 1/2) :
    EventuallyLocallyEqualCarriers
      (fun k => endpointDeletedCarrier (endpointPhasePrefix α k))
      (criticalPhaseTailCarrier α hi 0 0) := by
  intro K hK
  obtain ⟨R,hR⟩ := (Metric.isBounded_iff_subset_ball 0).mp hK.isBounded
  obtain ⟨N : ℕ,hN⟩ := exists_nat_gt (R+1)
  filter_upwards [eventually_ge_atTop N] with k hk
  ext x
  constructor
  · rintro ⟨hx,hxK⟩
    refine ⟨?_,hxK⟩
    apply (endpointPrefix_mem_iff_of_abs_lt α ha hi k x ?_).mp hx
    have hr : |x| < R := by simpa [Real.dist_eq] using hR hxK
    have hk' : (N : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  · rintro ⟨hx,hxK⟩
    refine ⟨?_,hxK⟩
    apply (endpointPrefix_mem_iff_of_abs_lt α ha hi k x ?_).mpr hx
    have hr : |x| < R := by simpa [Real.dist_eq] using hR hxK
    have hk' : (N : ℝ) ≤ k := by exact_mod_cast hk
    linarith

end
end MeyerGeneralProblem.Adaptive
