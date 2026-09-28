module

public import MeyerGeneralProblem.Cardinal.Adaptive.ActualHoleExchange
public import MeyerGeneralProblem.Cardinal.Adaptive.PhaseGeometry

@[expose] public section

/-! # Concrete finite-hole surgery on the original rapid-tail carrier

The restored carrier contains all matched head cells and exactly the original
scheduled infinite tail. Only the finite head hole pattern changes.
-/
namespace MeyerGeneralProblem.Adaptive
noncomputable section

/-- Original critical carrier, including its triangular head schedule. -/
def criticalBlockSet (P R : ℕ) : Set ℝ :=
  {x | ∃ (j : ℕ+) (positive : Bool) (n : ℤ), (j : ℕ) ≤ n.natAbs ∧
    x = (n : ℝ)+signedPhase positive (blockPhase P R j)}

/-- Unchanged infinite rapid tail, with every original cell threshold. -/
def scheduledTailSet (P R : ℕ) : Set ℝ :=
  {x | ∃ (j : ℕ+) (positive : Bool) (n : ℤ), headLength R < (j : ℕ) ∧
    (j : ℕ) ≤ n.natAbs ∧ x = (n : ℝ)+signedPhase positive (blockPhase P R j)}

/-- Restore the complete matched head grid; retain precisely the original tail. -/
def restoredHeadSet (P R : ℕ) : Set ℝ :=
  Set.range (halfShiftedGridPoint (headLength R)) ∪ scheduledTailSet P R

theorem scheduledTailSet_subset_blockSet (P R : ℕ) : scheduledTailSet P R ⊆ blockSet P R := by
  rintro x ⟨j,u,n,hj,hn,rfl⟩
  refine ⟨j,u,n,?_,rfl⟩
  simpa [cellThreshold, not_le.mpr hj] using hn

/-- The restored mixed carrier is locally finite, despite its infinite tail. -/
def restoredHeadCarrier (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) : LocallyFiniteCarrier where
  carrier := restoredHeadSet P R
  finite_inter_Icc a b := by
    apply (((halfShiftedGridCarrier (headLength R) (headLength_pos hR)).finite_inter_Icc a b).union
      (blockSet_finite_inter_Icc hP hR a b)).subset
    rintro x ⟨hx,hI⟩
    rcases hx with hx|hx
    · exact Or.inl ⟨hx,hI⟩
    · exact Or.inr ⟨scheduledTailSet_subset_blockSet P R hx,hI⟩

theorem headGrid_subset_restoredHeadSet (P R : ℕ) :
    Set.range (halfShiftedGridPoint (headLength R)) ⊆ restoredHeadSet P R :=
  Set.subset_union_left

theorem blockPhase_head_eq_matched (P R : ℕ) (i : Fin (headLength R)) :
    blockPhase P R ⟨i.val+1,by omega⟩ = matchedHeadPhase (headLength R) i := by
  unfold blockPhase
  rw [ite_eq_left (by exact i.isLt)]
  unfold matchedHeadPhase
  change (2 * ((i.val + 1 : ℕ) : ℝ) - 1) / (4 * (headLength R : ℝ)) = _
  push_cast
  ring

/-- The two source sign conventions agree after Boolean negation. -/
theorem signedPhase_eq_criticalSignedPhase (u : Bool) (a : ℝ) :
    signedPhase u a = criticalSignedPhase (!u) a := by
  cases u <;> rfl

/-- Every grid index belongs to one original signed head orbit and integer cell. -/
theorem exists_matchedOrbitIndex (k : ℕ) (hk : 1 ≤ k) (m : ℤ) :
    ∃ (i : Fin k) (u : Bool) (n : ℤ), matchedOrbitIndex k i u n = m := by
  have hp : (0 : ℤ) < 2*(k : ℤ) := by positivity
  let r := m % (2*(k : ℤ))
  let q := m / (2*(k : ℤ))
  have hr0 : 0 ≤ r := Int.emod_nonneg _ (ne_of_gt hp)
  have hrlt : r < 2*(k : ℤ) := Int.emod_lt_of_pos _ hp
  have he : r+2*(k : ℤ)*q = m := Int.emod_add_mul_ediv _ _
  by_cases h : r < k
  · let i : Fin k := ⟨r.toNat,(Int.toNat_lt hr0).mpr h⟩
    refine ⟨i,false,q,?_⟩
    have hi : (i : ℤ) = r := Int.toNat_of_nonneg hr0
    simp only [matchedOrbitIndex, Bool.false_eq_true, ite_false, hi]
    linarith
  · have hr : 0 ≤ 2*(k : ℤ)-r-1 := by omega
    let i : Fin k := ⟨(2*(k : ℤ)-r-1).toNat,(Int.toNat_lt hr).mpr (by omega)⟩
    refine ⟨i,true,q+1,?_⟩
    have hi : (i : ℤ) = 2*(k : ℤ)-r-1 := Int.toNat_of_nonneg hr
    simp only [matchedOrbitIndex, ite_true, hi]
    nlinarith

/-- Restored head cells are exactly the complete half-shifted grid. -/
theorem mem_headGrid_iff (P R : ℕ) (hR : 1 ≤ R) (x : ℝ) :
    x ∈ Set.range (halfShiftedGridPoint (headLength R)) ↔
      ∃ (j : ℕ+) (u : Bool) (n : ℤ), (j : ℕ) ≤ headLength R ∧
        x = (n : ℝ)+signedPhase u (blockPhase P R j) := by
  constructor
  · rintro ⟨m,rfl⟩
    obtain ⟨i,u,n,hm⟩ := exists_matchedOrbitIndex (headLength R) (headLength_pos hR) m
    refine ⟨⟨i.val+1,by omega⟩,!u,n,i.isLt,?_⟩
    rw [← hm, matchedOrbitIndex_point _ (headLength_pos hR),
      blockPhase_head_eq_matched, signedPhase_eq_criticalSignedPhase, Bool.not_not]
  · rintro ⟨j,u,n,hj,rfl⟩
    let i : Fin (headLength R) := ⟨(j : ℕ)-1,by have := j.pos; omega⟩
    have hi : (⟨i.val+1,by omega⟩ : ℕ+) = j := by
      apply Subtype.ext
      change (j : ℕ)-1+1 = (j : ℕ)
      have := j.pos
      omega
    refine ⟨matchedOrbitIndex (headLength R) i (!u) n,?_⟩
    rw [matchedOrbitIndex_point _ (headLength_pos hR), signedPhase_eq_criticalSignedPhase,
      ← hi, blockPhase_head_eq_matched]

/-- Integer cells are unique when both offsets lie strictly inside the half-cell. -/
theorem integer_cell_unique {n m : ℤ} {a b : ℝ}
    (ha : |a| < 1/2) (hb : |b| < 1/2) (h : (n : ℝ)+a = m+b) : n = m ∧ a = b := by
  obtain ⟨ha0,ha1⟩ := abs_lt.mp ha
  obtain ⟨hb0,hb1⟩ := abs_lt.mp hb
  have hl : (n : ℝ) < m+1 := by linarith
  have hh : (m : ℝ) < n+1 := by linarith
  have hl' : n < m+1 := by exact_mod_cast hl
  have hh' : m < n+1 := by exact_mod_cast hh
  have he : n = m := by omega
  exact ⟨he,by rw [he] at h; linarith⟩

/-- The unchanged scheduled tail is too far out to meet either finite head
hole pattern; this fact does not need head/tail phase separation. -/
theorem scheduledTail_abs_lower {P R : ℕ} (hP : 1 ≤ P) (hR : 1 ≤ R)
    {x : ℝ} (hx : x ∈ scheduledTailSet P R) : (headLength R : ℝ)+1/2 < |x| := by
  obtain ⟨j,u,n,hj,hn,rfl⟩ := hx
  have hphase := abs_signedPhase_lt_half hP hR j u
  have hnj : (j : ℝ) ≤ |(n : ℝ)| := by
    simpa using (show (j : ℝ) ≤ (n.natAbs : ℝ) by exact_mod_cast hn)
  have hjk : (headLength R : ℝ)+1 ≤ j := by exact_mod_cast hj
  have htri := abs_sub_le (n : ℝ)
    ((n : ℝ)+signedPhase u (blockPhase P R j)) 0
  have hnabs : |(n : ℝ)| ≤ |(n : ℝ)+signedPhase u (blockPhase P R j)|+
      |signedPhase u (blockPhase P R j)| := by simpa [add_comm] using htri
  linarith


theorem matched_signed_phase_injective (k : ℕ) (hk : 1 ≤ k) :
    Function.Injective (fun a : Fin k × Bool =>
      criticalSignedPhase a.2 (matchedHeadPhase k a.1)) := by
  rintro ⟨i,u⟩ ⟨j,v⟩ he
  have hi := matchedHeadPhase_interior k hk i
  have hj := matchedHeadPhase_interior k hk j
  cases u <;> cases v <;>
    simp only [criticalSignedPhase, Bool.false_eq_true, ite_false, ite_true] at he
  · exact Prod.ext (matchedHeadPhase_injective k hk he) rfl
  · linarith
  · linarith
  · exact Prod.ext (matchedHeadPhase_injective k hk (neg_inj.mp he)) rfl

theorem abs_criticalSignedPhase_head_lt (k : ℕ) (hk : 1 ≤ k)
    (i : Fin k) (u : Bool) : |criticalSignedPhase u (matchedHeadPhase k i)| < 1/2 := by
  have hi := matchedHeadPhase_interior k hk i
  cases u <;> simp only [criticalSignedPhase, Bool.false_eq_true, ite_false, ite_true,
    abs_neg, abs_of_pos hi.1] <;> exact hi.2

/-- The old holes remove exactly the cells with absolute index at most the
zero-based head index. This is equality of actual real carrier points. -/
theorem mem_triangularHoleSet_orbit_iff (k : ℕ) (hk : 1 ≤ k)
    (i : Fin k) (u : Bool) (n : ℤ) :
    (n : ℝ)+criticalSignedPhase u (matchedHeadPhase k i) ∈
      gridHoleSet k (triangularGridIndices k) ↔ n.natAbs ≤ i.val := by
  constructor
  · rintro ⟨h,he⟩
    change halfShiftedGridPoint k (matchedOrbitIndex k h.1 h.2.1 (triangularHoleCell h)) = _ at he
    rw [matchedOrbitIndex_point k hk] at he
    obtain ⟨hn,hphase⟩ := integer_cell_unique
      (abs_criticalSignedPhase_head_lt k hk h.1 h.2.1)
      (abs_criticalSignedPhase_head_lt k hk i u) he
    have hij := matched_signed_phase_injective k hk (a₁ := (h.1,h.2.1)) (a₂ := (i,u)) hphase
    have hbound := triangularHoleCell_bound h
    rw [hn, show h.1 = i from congrArg Prod.fst hij] at hbound
    have hh : (n.natAbs : ℤ) ≤ (i.val : ℤ) := by simpa only [Int.natCast_natAbs] using hbound
    exact_mod_cast hh
  · intro hn
    have hn' : |n| ≤ (i : ℤ) := by
      have hh : (n.natAbs : ℤ) ≤ (i.val : ℤ) := by exact_mod_cast hn
      simpa only [Int.natCast_natAbs] using hh
    obtain ⟨h,hi,hu,hcell⟩ := triangularHoleCell_surjective i u n hn'
    refine ⟨h,?_⟩
    change halfShiftedGridPoint k (matchedOrbitIndex k h.1 h.2.1 (triangularHoleCell h)) = _
    rw [matchedOrbitIndex_point k hk]
    simp only [hi,hu,hcell]

theorem headLength_cast (R : ℕ) (hR : 1 ≤ R) :
    (headLength R : ℝ) = 2*(R : ℝ)-1 := by
  unfold headLength
  rw [Nat.cast_sub (by omega)]
  push_cast
  ring

theorem mem_centralHoleSet_iff (k : ℕ) (hk : 1 ≤ k) (x : ℝ) :
    x ∈ gridHoleSet k (centralGridIndices k) ↔
      x ∈ Set.range (halfShiftedGridPoint k) ∧ |x| < (k : ℝ)/2 := by
  constructor
  · rintro ⟨r,rfl⟩
    exact ⟨⟨_,rfl⟩,(centralHoleIndex_iff k hk _).mp ⟨r,rfl⟩⟩
  · rintro ⟨⟨m,rfl⟩,hm⟩
    obtain ⟨r,hr⟩ := (centralHoleIndex_iff k hk m).mpr hm
    exact ⟨r,by simp only [centralGridIndices,hr]⟩

/-- Filling the head and removing its central window produces exactly the
source's flat carrier, with all infinite tail thresholds retained. -/
theorem restoredHeadSet_delete_central (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) :
    restoredHeadSet P R \ gridHoleSet (headLength R) (centralGridIndices (headLength R)) =
      blockSet P R := by
  ext x
  constructor
  · rintro ⟨hx,hnot⟩
    rcases hx with hx|hx
    · obtain ⟨j,u,n,hj,rfl⟩ := (mem_headGrid_iff P R hR x).mp hx
      refine ⟨j,u,n,?_,rfl⟩
      simp only [cellThreshold,ite_eq_left hj]
      by_contra hn
      have hn' : n.natAbs ≤ R-1 := by omega
      have hnreal : |(n : ℝ)| ≤ (R : ℝ)-1 := by
        have hh : (n.natAbs : ℝ) ≤ ((R-1 : ℕ) : ℝ) := by exact_mod_cast hn'
        simpa [Nat.cast_sub hR] using hh
      have hphase := abs_signedPhase_lt_half hP hR j u
      have htri := abs_add_le (n : ℝ) (signedPhase u (blockPhase P R j))
      apply hnot
      apply (mem_centralHoleSet_iff _ (headLength_pos hR) _).mpr
      refine ⟨hx,?_⟩
      rw [headLength_cast R hR]
      linarith
    · exact scheduledTailSet_subset_blockSet P R hx
  · intro hx
    refine ⟨?_,?_⟩
    · obtain ⟨j,u,n,hn,he⟩ := hx
      by_cases hj : (j : ℕ) ≤ headLength R
      · exact Or.inl ((mem_headGrid_iff P R hR x).mpr ⟨j,u,n,hj,he⟩)
      · exact Or.inr ⟨j,u,n,by omega,by simpa [cellThreshold,hj] using hn,he⟩
    · intro hhole
      have hh := ((mem_centralHoleSet_iff _ (headLength_pos hR) _).mp hhole).2
      have hgap := blockSet_central_gap hP hR hx
      rw [headLength_cast R hR] at hh
      linarith


theorem triangularHoleSet_abs_upper (k : ℕ) (hk : 1 ≤ k) {x : ℝ}
    (hx : x ∈ gridHoleSet k (triangularGridIndices k)) : |x| < (k : ℝ)-1/2 := by
  obtain ⟨h,rfl⟩ := hx
  change |halfShiftedGridPoint k (matchedOrbitIndex k h.1 h.2.1 (triangularHoleCell h))| < _
  rw [matchedOrbitIndex_point k hk]
  have hcell : |(triangularHoleCell h : ℝ)| ≤ (h.1 : ℝ) := by
    exact_mod_cast triangularHoleCell_bound h
  have hi : (h.1 : ℝ)+1 ≤ k := by exact_mod_cast h.1.isLt
  have hphase := abs_criticalSignedPhase_head_lt k hk h.1 h.2.1
  have htri := abs_add_le (triangularHoleCell h : ℝ)
    (criticalSignedPhase h.2.1 (matchedHeadPhase k h.1))
  linarith

theorem mem_triangularHoleSet_head_iff (P R : ℕ) (hR : 1 ≤ R)
    (j : ℕ+) (hj : (j : ℕ) ≤ headLength R) (u : Bool) (n : ℤ) :
    (n : ℝ)+signedPhase u (blockPhase P R j) ∈
      gridHoleSet (headLength R) (triangularGridIndices (headLength R)) ↔ n.natAbs < (j : ℕ) := by
  let i : Fin (headLength R) := ⟨(j : ℕ)-1,by have := j.pos; omega⟩
  have hi : (⟨i.val+1,by omega⟩ : ℕ+) = j := by
    apply Subtype.ext
    change (j : ℕ)-1+1 = (j : ℕ)
    have := j.pos
    omega
  have he : blockPhase P R j = matchedHeadPhase (headLength R) i := by
    rw [← hi,blockPhase_head_eq_matched]
  rw [he,signedPhase_eq_criticalSignedPhase,
    mem_triangularHoleSet_orbit_iff _ (headLength_pos hR)]
  change n.natAbs ≤ (j : ℕ)-1 ↔ n.natAbs < (j : ℕ)
  have := j.pos
  omega

/-- Removing the triangular holes recovers the exact original critical schedule,
including every original cell of every rapid phase. -/
theorem restoredHeadSet_delete_triangular (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) :
    restoredHeadSet P R \ gridHoleSet (headLength R) (triangularGridIndices (headLength R)) =
      criticalBlockSet P R := by
  ext x
  constructor
  · rintro ⟨hx,hnot⟩
    rcases hx with hx|hx
    · obtain ⟨j,u,n,hj,rfl⟩ := (mem_headGrid_iff P R hR x).mp hx
      refine ⟨j,u,n,?_,rfl⟩
      have hh := mt (mem_triangularHoleSet_head_iff P R hR j hj u n).mpr hnot
      omega
    · obtain ⟨j,u,n,_,hn,he⟩ := hx
      exact ⟨j,u,n,hn,he⟩
  · rintro ⟨j,u,n,hn,rfl⟩
    by_cases hj : (j : ℕ) ≤ headLength R
    · refine ⟨Or.inl ((mem_headGrid_iff P R hR _).mpr ⟨j,u,n,hj,rfl⟩),?_⟩
      rw [mem_triangularHoleSet_head_iff P R hR j hj u n]
      omega
    · have ht : (n : ℝ)+signedPhase u (blockPhase P R j) ∈ scheduledTailSet P R :=
        ⟨j,u,n,by omega,hn,rfl⟩
      refine ⟨Or.inr ht,?_⟩
      intro hh
      have hlow := scheduledTail_abs_lower hP hR ht
      have hhigh := triangularHoleSet_abs_upper _ (headLength_pos hR) hh
      linarith

/-- The original critical schedule as an extensional locally finite carrier. -/
def criticalBlockCarrier (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) : LocallyFiniteCarrier :=
  (restoredHeadCarrier P R hP hR).restrict (criticalBlockSet P R) (by
    rw [← restoredHeadSet_delete_triangular P R hP hR]
    exact Set.sdiff_subset)

theorem delete_restored_triangular (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) :
    deleteCarrier (restoredHeadCarrier P R hP hR)
      (gridHoleSet (headLength R) (triangularGridIndices (headLength R))) =
      criticalBlockCarrier P R hP hR := by
  apply LocallyFiniteCarrier.ext
  exact restoredHeadSet_delete_triangular P R hP hR

theorem delete_restored_central (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) :
    deleteCarrier (restoredHeadCarrier P R hP hR)
      (gridHoleSet (headLength R) (centralGridIndices (headLength R))) =
      blockCarrier P R hP hR := by
  apply LocallyFiniteCarrier.ext
  exact restoredHeadSet_delete_central P R hP hR

/-- The unrestricted complete atomic-pair spaces have the same exact
finite-head exchange. No tail representation hypothesis is supplied. -/
def concreteBlockHoleExchange (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) :
    pairedAtomicSource (criticalBlockCarrier P R hP hR) (criticalBlockCarrier P R hP hR) ≃ₗ[ℂ]
    pairedAtomicSource (blockCarrier P R hP hR) (blockCarrier P R hP hR) := by
  have e := deletedCarrierHoleExchange (headLength R) (headLength_pos hR)
    (restoredHeadCarrier P R hP hR) (restoredHeadCarrier P R hP hR)
    (headGrid_subset_restoredHeadSet P R) (headGrid_subset_restoredHeadSet P R)
  rw [delete_restored_triangular,delete_restored_central] at e
  exact e

/-- Exact surgery between the complete critical and flat source spaces in every
original native order p ≥ 1; the infinite rapid tail is retained in both spaces. -/
def concreteBlockNativeHoleExchange (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R)
    (p : ℕ) (hp : 1 ≤ p) :
    ↥(pairedAtomicSource (criticalBlockCarrier P R hP hR) (criticalBlockCarrier P R hP hR) ⊓
      originalNativeDistributionSpace p) ≃ₗ[ℂ]
    ↥(pairedAtomicSource (blockCarrier P R hP hR) (blockCarrier P R hP hR) ⊓
      originalNativeDistributionSpace p) := by
  have e := deletedCarrierNativeHoleExchange (headLength R) (headLength_pos hR)
    (restoredHeadCarrier P R hP hR) (restoredHeadCarrier P R hP hR)
    (headGrid_subset_restoredHeadSet P R) (headGrid_subset_restoredHeadSet P R) p hp
  rw [delete_restored_triangular,delete_restored_central] at e
  exact e

theorem concreteBlockNativeHoleExchange_rank (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R)
    (p : ℕ) (hp : 1 ≤ p) :
    Module.rank ℂ ↥(pairedAtomicSource (criticalBlockCarrier P R hP hR)
      (criticalBlockCarrier P R hP hR) ⊓ originalNativeDistributionSpace p) =
    Module.rank ℂ ↥(pairedAtomicSource (blockCarrier P R hP hR)
      (blockCarrier P R hP hR) ⊓ originalNativeDistributionSpace p) :=
  (concreteBlockNativeHoleExchange P R hP hR p hp).rank_eq

end
end MeyerGeneralProblem.Adaptive
