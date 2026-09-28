module

public import MeyerGeneralProblem.Trace.GroupedTrace

@[expose] public section

/-!
# Quantitative geometry of the exact canonical short-gap groups

The equivalence relation uses strict gaps below d. The actual increasing
enumeration has short consecutive gaps, bounded diameter, and mutually
separated convex hulls. A gap equal to d remains a boundary.
-/

namespace MeyerGeneralProblem

noncomputable section

/-- A cut through a gap in one actual class is invariant along all short-gap
paths in that class. Points of other classes are irrelevant to this cut. -/
theorem clusterClass_cut_invariant {S : LocallyFiniteCarrier} {d a b : ℝ}
    (root : S.subtype) (hgap : d ≤ b-a)
    (hempty : ∀ z ∈ clusterClass S d root, ¬ (a < (z:ℝ) ∧ (z:ℝ) < b))
    {x y : S.subtype} (hxy : (clusterSetoid S d).r x y) :
    (x ∈ clusterClass S d root ∧ (x:ℝ) ≤ a) ↔
      (y ∈ clusterClass S d root ∧ (y:ℝ) ≤ a) := by
  have hstep (u v : S.subtype) (huv : |(u:ℝ)-(v:ℝ)| < d)
      (hu : u ∈ clusterClass S d root ∧ (u:ℝ) ≤ a) :
      v ∈ clusterClass S d root ∧ (v:ℝ) ≤ a := by
    have hv : v ∈ clusterClass S d root :=
      Relation.EqvGen.trans _ _ _ hu.1 (Relation.EqvGen.rel _ _ huv)
    refine ⟨hv, ?_⟩
    by_contra h
    have hlt : a < (v:ℝ) := lt_of_not_ge h
    have hge : b ≤ (v:ℝ) := le_of_not_gt (fun hh => hempty v hv ⟨hlt, hh⟩)
    have hdist := (abs_lt.mp huv).1
    linarith [hu.2]
  induction hxy with
  | rel u v huv => exact ⟨hstep u v huv, hstep v u (by simpa [abs_sub_comm] using huv)⟩
  | refl u => rfl
  | symm u v _ ih => exact ih.symm
  | trans u v w _ _ ih₁ ih₂ => exact ih₁.trans ih₂

namespace BoundedClusterOrder

variable {S : LocallyFiniteCarrier} {d : ℝ} {q : ℕ} (horder : BoundedClusterOrder S d q)

/-- Actual ordered nodes of a canonical class, as real coordinates. -/
def realClusterNode (C : CanonicalClusterIndex S d) (i : Fin (horder.clusterSize C)) : ℝ :=
  horder.orderedClusterNode C i

/-- The real enumeration is strictly increasing and hence has no duplicates. -/
theorem realClusterNode_strictMono (C : CanonicalClusterIndex S d) :
    StrictMono (horder.realClusterNode C) := (horder.orderedClusterNode C).strictMono

/-- Every real enumerated node is an actual carrier point. -/
theorem realClusterNode_mem (C : CanonicalClusterIndex S d) (i : Fin (horder.clusterSize C)) :
    horder.realClusterNode C i ∈ S.carrier := (horder.orderedClusterNode C i).property

/-- Distinct canonical quotient classes have the original d separation. -/
theorem realClusterNode_separated {C E : CanonicalClusterIndex S d} (hne : C ≠ E)
    (i : Fin (horder.clusterSize C)) (j : Fin (horder.clusterSize E)) :
    d ≤ |horder.realClusterNode C i-horder.realClusterNode E j| := by
  apply cluster_distance_ge_of_not_related
  intro h
  apply hne
  rw [← horder.orderedClusterNode_class C i, ← horder.orderedClusterNode_class E j]
  exact Quotient.sound h

/-- Consecutive nodes in the increasing class enumeration have a strict
short gap. Equality at d would disconnect the canonical class. -/
theorem realClusterNode_consecutive_gap (C : CanonicalClusterIndex S d)
    (k : ℕ) (hk : k+1 < horder.clusterSize C) :
    horder.realClusterNode C ⟨k+1,hk⟩-
      horder.realClusterNode C ⟨k,by omega⟩ < d := by
  let i : Fin (horder.clusterSize C) := ⟨k, by omega⟩
  let j : Fin (horder.clusterSize C) := ⟨k+1, hk⟩
  let x := horder.orderedClusterNode C i
  let y := horder.orderedClusterNode C j
  have hx : x ∈ clusterClass S d C.out := by
    rw [← horder.range_orderedClusterNode C]
    exact ⟨i, rfl⟩
  have hy : y ∈ clusterClass S d C.out := by
    rw [← horder.range_orderedClusterNode C]
    exact ⟨j, rfl⟩
  have hxy : (clusterSetoid S d).r x y :=
    Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hx) hy
  by_contra h
  have hgap : d ≤ (y:ℝ)-(x:ℝ) := le_of_not_gt h
  have hempty : ∀ z ∈ clusterClass S d C.out,
      ¬ ((x:ℝ)<(z:ℝ) ∧ (z:ℝ)<(y:ℝ)) := by
    intro z hz hbetween
    rw [← horder.range_orderedClusterNode C] at hz
    obtain ⟨l, rfl⟩ := hz
    have hlo : i < l := (horder.orderedClusterNode C).lt_iff_lt.mp hbetween.1
    have hhi : l < j := (horder.orderedClusterNode C).lt_iff_lt.mp hbetween.2
    change k < l.val at hlo
    change l.val < k+1 at hhi
    omega
  have hcut := clusterClass_cut_invariant C.out hgap hempty hxy
  have hle := (hcut.mp ⟨hx, le_rfl⟩).2
  have hlt := horder.realClusterNode_strictMono C (show i < j by change k < k+1; omega)
  change (x:ℝ)<(y:ℝ) at hlt
  linarith

/-- The actual cluster diameter is uniformly bounded by q*d. -/
theorem realClusterNode_diameter (hd : 0 < d) (C : CanonicalClusterIndex S d)
    (i j : Fin (horder.clusterSize C)) :
    dist (horder.realClusterNode C i) (horder.realClusterNode C j) ≤ (q:ℝ)*d := by
  let z : Fin (horder.clusterSize C) := ⟨0, horder.clusterSize_pos C⟩
  have hupper : ∀ k (hk : k < horder.clusterSize C),
      horder.realClusterNode C ⟨k,hk⟩ ≤ horder.realClusterNode C z+(k:ℝ)*d := by
    intro k
    induction k with
    | zero => intro hk; simp [z]
    | succ k ih =>
      intro hk
      have hg := horder.realClusterNode_consecutive_gap C k hk
      have hu := ih (by omega)
      push_cast
      linarith
  have hb (l : Fin (horder.clusterSize C)) :
      horder.realClusterNode C z ≤ horder.realClusterNode C l ∧
      horder.realClusterNode C l ≤ horder.realClusterNode C z+(q:ℝ)*d := by
    refine ⟨(horder.realClusterNode_strictMono C).monotone (by change (0:ℕ) ≤ l.val; omega), ?_⟩
    have hq : (l:ℝ) ≤ q := by exact_mod_cast l.isLt.le.trans (horder.clusterSize_le C)
    exact (hupper l l.isLt).trans (by gcongr)
  rw [Real.dist_eq, abs_le]
  constructor <;> linarith [hb i, hb j]

/-- The actual first coordinate of a nonempty canonical cluster. -/
def clusterLower (C : CanonicalClusterIndex S d) : ℝ :=
  horder.realClusterNode C ⟨0, horder.clusterSize_pos C⟩

/-- The actual last coordinate of a nonempty canonical cluster. -/
def clusterUpper (C : CanonicalClusterIndex S d) : ℝ :=
  horder.realClusterNode C ⟨horder.clusterSize C-1, Nat.sub_lt (horder.clusterSize_pos C) (by omega)⟩

/-- The actual ordered nodes lie in their exact real convex hull. -/
theorem realClusterNode_mem_hull (C : CanonicalClusterIndex S d)
    (i : Fin (horder.clusterSize C)) :
    horder.realClusterNode C i ∈ Set.Icc (horder.clusterLower C) (horder.clusterUpper C) := by
  constructor
  · exact (horder.realClusterNode_strictMono C).monotone (by change (0:ℕ) ≤ i.val; omega)
  · exact (horder.realClusterNode_strictMono C).monotone (by
      change i.val ≤ horder.clusterSize C-1
      omega)

/-- Order of the first nodes orders the entire canonical clusters, with the
full separation d between them. This excludes interleaving convex hulls. -/
theorem realClusterNode_add_gap_le_other_lower (hd : 0 < d)
    {C E : CanonicalClusterIndex S d} (hne : C ≠ E)
    (hle : horder.clusterLower C ≤ horder.clusterLower E)
    (i : Fin (horder.clusterSize C)) :
    horder.realClusterNode C i+d ≤ horder.clusterLower E := by
  let z : Fin (horder.clusterSize C) := ⟨0, horder.clusterSize_pos C⟩
  let w : Fin (horder.clusterSize E) := ⟨0, horder.clusterSize_pos E⟩
  have hmem (j : Fin (horder.clusterSize C)) :
      horder.orderedClusterNode C j ∈ clusterClass S d C.out := by
    rw [← horder.range_orderedClusterNode C]
    exact ⟨j, rfl⟩
  have haway (u : S.subtype) (hu : u ∈ clusterClass S d C.out) :
      d ≤ |(u:ℝ)-horder.clusterLower E| := by
    apply cluster_distance_ge_of_not_related
    intro h
    have hCu : Quotient.mk (clusterSetoid S d) u = C :=
      (Quotient.sound hu).symm.trans C.out_eq
    exact hne (hCu.symm.trans ((Quotient.sound h).trans (horder.orderedClusterNode_class E w)))
  have hstart := horder.realClusterNode_separated hne z w
  change d ≤ |horder.clusterLower C-horder.clusterLower E| at hstart
  rw [abs_of_nonpos (sub_nonpos.mpr hle)] at hstart
  have hempty : ∀ u ∈ clusterClass S d C.out,
      ¬ (horder.clusterLower E-d < (u:ℝ) ∧ (u:ℝ) < horder.clusterLower E+d) := by
    intro u hu hh
    have ha := haway u hu
    have hb : |(u:ℝ)-horder.clusterLower E| < d := abs_lt.mpr ⟨by linarith [hh.1], by linarith [hh.2]⟩
    linarith
  have hconn : (clusterSetoid S d).r (horder.orderedClusterNode C z)
      (horder.orderedClusterNode C i) :=
    Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (hmem z)) (hmem i)
  have hcut := clusterClass_cut_invariant C.out
    (a := horder.clusterLower E-d) (b := horder.clusterLower E+d)
    (by linarith) hempty hconn
  have hi := (hcut.mp ⟨hmem z, by change horder.clusterLower C ≤ _; linarith⟩).2
  change horder.realClusterNode C i ≤ horder.clusterLower E-d at hi
  linarith

/-- The full convex hulls of distinct canonical groups are separated by d,
as required by Hermite--Genocchi averaging in the upper synthesis bound. -/
theorem cluster_hulls_separated (hd : 0 < d)
    {C E : CanonicalClusterIndex S d} (hne : C ≠ E)
    {x y : ℝ} (hx : x ∈ Set.Icc (horder.clusterLower C) (horder.clusterUpper C))
    (hy : y ∈ Set.Icc (horder.clusterLower E) (horder.clusterUpper E)) :
    d ≤ |x-y| := by
  rcases le_total (horder.clusterLower C) (horder.clusterLower E) with hle | hle
  · have h := horder.realClusterNode_add_gap_le_other_lower hd hne hle
      ⟨horder.clusterSize C-1, Nat.sub_lt (horder.clusterSize_pos C) (by omega)⟩
    change horder.clusterUpper C+d ≤ horder.clusterLower E at h
    have ha := neg_abs_le (x-y)
    linarith [hx.2, hy.1]
  · have h := horder.realClusterNode_add_gap_le_other_lower hd hne.symm hle
      ⟨horder.clusterSize E-1, Nat.sub_lt (horder.clusterSize_pos E) (by omega)⟩
    change horder.clusterUpper E+d ≤ horder.clusterLower C at h
    have ha := le_abs_self (x-y)
    linarith [hx.1, hy.2]

end BoundedClusterOrder

end

end MeyerGeneralProblem
