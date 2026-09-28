module

public import MeyerGeneralProblem.Carrier.CanonicalClusterGeometry
public import MeyerGeneralProblem.Carrier.GroupedLimitJets
public import MeyerGeneralProblem.Carrier.IndexedMultisetCounts
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import all Mathlib.Topology.Algebra.InfiniteSum.ENNReal

@[expose] public section

/-!
# Exact canonical interpretation of integer-indexed source blocks

The boundary bit at an integer index uses the actual preceding gap. Its
maximal finite blocks are exactly the canonical strict-short-gap clusters.
The identification preserves increasing node order and every prefix datum.
Integer anchors repeat a cluster exactly as many times as it has nodes.
-/

noncomputable section

open Set Filter
open scoped Topology BigOperators ENNReal

namespace MeyerGeneralProblem

namespace TwoSidedCarrier

/-- The original integer parametrization as an equivalence with the actual
extensional carrier subtype. -/
def indexSubtypeEquiv (Λ : TwoSidedCarrier) : ℤ ≃ Λ.toLocallyFinite.subtype :=
  Equiv.ofBijective (fun a => ⟨Λ a, ⟨a, rfl⟩⟩)
    ⟨fun a b h => Λ.strictMono.injective (congrArg Subtype.val h),
      fun x => by rcases x.property with ⟨a, ha⟩; exact ⟨a, Subtype.ext ha⟩⟩

/-- The canonical strict-gap quotient class containing an actual integer
anchor. This definition does not depend on a chosen source-block record. -/
def anchorClass (Λ : TwoSidedCarrier) (d : ℝ) (a : ℤ) :
    CanonicalClusterIndex Λ.toLocallyFinite d :=
  Quotient.mk (clusterSetoid Λ.toLocallyFinite d) (Λ.indexSubtypeEquiv a)

/-- The real coordinate of the integer-to-subtype equivalence is unchanged. -/
@[simp]
theorem coe_indexSubtypeEquiv (Λ : TwoSidedCarrier) (a : ℤ) :
    (Λ.indexSubtypeEquiv a : ℝ) = Λ a := rfl

/-- Every canonical cluster is represented by some integer anchor. -/
theorem anchorClass_surjective (Λ : TwoSidedCarrier) (d : ℝ) :
    Function.Surjective (Λ.anchorClass d) := by
  intro C
  refine ⟨Λ.indexSubtypeEquiv.symm C.out, ?_⟩
  simp only [anchorClass, Equiv.apply_symm_apply, Quotient.out_eq]

/-- The actual integer anchors in a canonical class are equivalent to its
ordered finite node set. -/
def anchorClassFiberEquiv (Λ : TwoSidedCarrier) {d : ℝ} {q : ℕ}
    (hcluster : BoundedClusterOrder Λ.toLocallyFinite d q)
    (C : CanonicalClusterIndex Λ.toLocallyFinite d) :
    {a : ℤ // Λ.anchorClass d a = C} ≃ Fin (hcluster.clusterSize C) := by
  let f : Fin (hcluster.clusterSize C) → {a : ℤ // Λ.anchorClass d a = C} :=
    fun i => ⟨Λ.indexSubtypeEquiv.symm (hcluster.orderedClusterNode C i), by
      simpa only [anchorClass, Equiv.apply_symm_apply] using
        hcluster.orderedClusterNode_class C i⟩
  apply (Equiv.ofBijective f ?_).symm
  constructor
  · intro i j hij
    apply (hcluster.orderedClusterNode C).injective
    exact Λ.indexSubtypeEquiv.symm.injective (congrArg Subtype.val hij)
  · intro a
    have ha : Λ.indexSubtypeEquiv a.val ∈ clusterClass Λ.toLocallyFinite d C.out := by
      change (clusterSetoid Λ.toLocallyFinite d).r C.out (Λ.indexSubtypeEquiv a.val)
      exact @Quotient.exact _ (clusterSetoid Λ.toLocallyFinite d) _ _
        (C.out_eq.trans a.property.symm)
    rw [← hcluster.range_orderedClusterNode C] at ha
    obtain ⟨i, hi⟩ := ha
    refine ⟨i, Subtype.ext ?_⟩
    change Λ.indexSubtypeEquiv.symm (hcluster.orderedClusterNode C i) = a.val
    rw [hi, Equiv.symm_apply_apply]

/-- Every anchor fiber is finite, independently of the size of the whole
carrier. -/
theorem finite_anchorClass_fiber (Λ : TwoSidedCarrier) {d : ℝ} {q : ℕ}
    (hcluster : BoundedClusterOrder Λ.toLocallyFinite d q)
    (C : CanonicalClusterIndex Λ.toLocallyFinite d) :
    {a : ℤ | Λ.anchorClass d a = C}.Finite := by
  apply Set.finite_coe_iff.mp
  exact
    Finite.of_equiv (Fin (hcluster.clusterSize C)) (Λ.anchorClassFiberEquiv hcluster C).symm

/-- Indexing by every integer repeats a canonical cluster exactly once per
actual node, not by an uncontrolled infinite multiplicity. -/
theorem ncard_anchorClass_fiber (Λ : TwoSidedCarrier) {d : ℝ} {q : ℕ}
    (hcluster : BoundedClusterOrder Λ.toLocallyFinite d q)
    (C : CanonicalClusterIndex Λ.toLocallyFinite d) :
    {a : ℤ | Λ.anchorClass d a = C}.ncard = hcluster.clusterSize C := by
  change Nat.card {a : ℤ // Λ.anchorClass d a = C} = _
  simpa only [Nat.card_fin] using
    Nat.card_congr (Λ.anchorClassFiberEquiv hcluster C)

end TwoSidedCarrier

namespace IndexedSourceBlock

variable {Λ : TwoSidedCarrier} {d : ℝ} {a : ℤ}

/-- Actual source-block nodes viewed in the extensional carrier subtype. -/
def carrierNode (P : IndexedSourceBlock (Λ.clusterBoundary d 0) a)
    (i : Fin P.size) : Λ.toLocallyFinite.subtype := Λ.indexSubtypeEquiv (P.index i)

/-- Source-block enumeration is strictly increasing in the actual carrier. -/
theorem carrierNode_strictMono (P : IndexedSourceBlock (Λ.clusterBoundary d 0) a) :
    StrictMono P.carrierNode := by
  intro i j hij
  apply Λ.strictMono
  change P.first + (i : ℤ) < P.first + (j : ℤ)
  have hij' : i.val < j.val := hij
  omega

/-- Adjacent nodes of a source block are connected by an actual strict
short-gap edge, including the exact boundary convention. -/
theorem carrierNode_related_first
    (P : IndexedSourceBlock (Λ.clusterBoundary d 0) a) (i : Fin P.size) :
    (clusterSetoid Λ.toLocallyFinite d).r
      (P.carrierNode ⟨0, by have := P.anchor_mem; omega⟩) (P.carrierNode i) := by
  have hchain : ∀ k (hk : k < P.size),
      (clusterSetoid Λ.toLocallyFinite d).r
        (P.carrierNode ⟨0, by have := P.anchor_mem; omega⟩)
        (P.carrierNode ⟨k, hk⟩) := by
    intro k
    induction k with
    | zero => intro hk; exact Relation.EqvGen.refl _
    | succ k ih =>
      intro hk
      apply Relation.EqvGen.trans _ _ _ (ih (by omega))
      apply Relation.EqvGen.rel
      let i : Fin P.size := ⟨k, by omega⟩
      let j : Fin P.size := ⟨k + 1, hk⟩
      have hb := P.interior (P.index j)
        (by change P.first < P.first + ((k + 1 : ℕ) : ℤ); omega)
        (P.index_mem j).2
      have hg : Λ (P.index j) - Λ (P.index j - 1) < d := by
        simpa only [TwoSidedCarrier.clusterBoundary, add_zero, decide_eq_false_iff_not,
          not_le] using hb
      have heq : P.index j - 1 = P.index i := by
        change P.first + ((k + 1 : ℕ) : ℤ) - 1 = P.first + (k : ℤ)
        omega
      rw [heq] at hg
      change |Λ (P.index i) - Λ (P.index j)| < d
      have hmono : Λ (P.index i) < Λ (P.index j) :=
        P.carrierNode_strictMono (show i < j by change k < k+1; omega)
      rw [abs_of_neg (sub_neg.mpr hmono)]
      linarith
  exact hchain i i.isLt

private theorem range_carrierNode_invariant
    (P : IndexedSourceBlock (Λ.clusterBoundary d 0) a)
    {x y : Λ.toLocallyFinite.subtype}
    (hxy : (clusterSetoid Λ.toLocallyFinite d).r x y) :
    x ∈ Set.range P.carrierNode ↔ y ∈ Set.range P.carrierNode := by
  have hstep (u v : Λ.toLocallyFinite.subtype) (huv : |(u : ℝ) - (v : ℝ)| < d)
      (hu : u ∈ Set.range P.carrierNode) : v ∈ Set.range P.carrierNode := by
    obtain ⟨j, rfl⟩ := hu
    obtain ⟨k, hk⟩ := Λ.indexSubtypeEquiv.surjective v
    subst v
    have hleft : d ≤ Λ P.first - Λ (P.first - 1) := by
      simpa only [TwoSidedCarrier.clusterBoundary, add_zero, decide_eq_true_eq] using
        P.left_boundary
    have hright : d ≤ Λ (P.first + P.size) - Λ (P.first + P.size - 1) := by
      simpa only [TwoSidedCarrier.clusterBoundary, add_zero, decide_eq_true_eq] using
        P.right_boundary
    have hj := P.index_mem j
    change |Λ (P.index j) - Λ k| < d at huv
    have hkblock : P.first ≤ k ∧ k < P.first + P.size := by
      constructor
      · by_contra hn
        have hlo := Λ.strictMono.monotone (show k ≤ P.first - 1 by omega)
        have hhi := Λ.strictMono.monotone hj.1
        change Λ k ≤ Λ (P.first - 1) at hlo
        change Λ P.first ≤ Λ (P.index j) at hhi
        linarith [(abs_lt.mp huv).2]
      · by_contra hn
        have hlo := Λ.strictMono.monotone (show P.index j ≤ P.first + P.size - 1 by omega)
        have hhi := Λ.strictMono.monotone (show P.first + P.size ≤ k by omega)
        change Λ (P.index j) ≤ Λ (P.first + P.size - 1) at hlo
        change Λ (P.first + P.size) ≤ Λ k at hhi
        linarith [(abs_lt.mp huv).1]
    obtain ⟨i, hi⟩ := P.exists_index hkblock
    exact ⟨i, by simp only [carrierNode, hi]⟩
  induction hxy with
  | rel u v huv => exact ⟨hstep u v huv, hstep v u (by simpa [abs_sub_comm] using huv)⟩
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- The finite block is exactly the canonical equivalence class containing
its anchor, as an equality of actual carrier-point sets. -/
theorem range_carrierNode_eq_clusterClass
    (P : IndexedSourceBlock (Λ.clusterBoundary d 0) a) :
    Set.range P.carrierNode =
      clusterClass Λ.toLocallyFinite d (Λ.indexSubtypeEquiv a) := by
  obtain ⟨j, hj⟩ := P.exists_index P.anchor_mem
  have hjnode : P.carrierNode j = Λ.indexSubtypeEquiv a := by simp only [carrierNode, hj]
  have hanchor : Λ.indexSubtypeEquiv a ∈ Set.range P.carrierNode := ⟨j, hjnode⟩
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    rw [← hjnode]
    exact Relation.EqvGen.trans _ _ _
      (Relation.EqvGen.symm _ _ (P.carrierNode_related_first j))
      (P.carrierNode_related_first i)
  · intro hx
    exact (P.range_carrierNode_invariant hx).mp hanchor

/-- The source block and the canonical increasing enumeration have exactly
the same range of actual carrier points. -/
theorem range_carrierNode_eq_orderedClusterNode {q : ℕ}
    (hcluster : BoundedClusterOrder Λ.toLocallyFinite d q)
    (P : IndexedSourceBlock (Λ.clusterBoundary d 0) a) :
    Set.range P.carrierNode =
      Set.range (hcluster.orderedClusterNode (Λ.anchorClass d a)) := by
  rw [P.range_carrierNode_eq_clusterClass, hcluster.range_orderedClusterNode]
  apply (clusterClass_eq_of_related
    (x := (Λ.anchorClass d a).out) (y := Λ.indexSubtypeEquiv a) ?_).symm
  exact @Quotient.mk_out _ (clusterSetoid Λ.toLocallyFinite d) (Λ.indexSubtypeEquiv a)

/-- A genuine boundary block has exactly the size of its canonical cluster. -/
theorem size_eq_clusterSize {q : ℕ}
    (hcluster : BoundedClusterOrder Λ.toLocallyFinite d q)
    (P : IndexedSourceBlock (Λ.clusterBoundary d 0) a) :
    P.size = hcluster.clusterSize (Λ.anchorClass d a) := by
  have h := congrArg Set.ncard (P.range_carrierNode_eq_orderedClusterNode hcluster)
  simpa only [Set.ncard_range_of_injective P.carrierNode_strictMono.injective,
    Set.ncard_range_of_injective (hcluster.orderedClusterNode (Λ.anchorClass d a)).injective,
    Nat.card_fin] using h

private theorem strictMono_eq_cast_of_range_eq {m n : ℕ} {β : Type*} [LinearOrder β]
    {f : Fin m → β} {g : Fin n → β} (h : m = n)
    (hf : StrictMono f) (hg : StrictMono g) (hrange : Set.range f = Set.range g)
    (i : Fin m) : f i = g (Fin.cast h i) := by
  subst n
  exact congrFun ((hf.range_inj hg).mp hrange) i

/-- Increasing source-block nodes agree point for point with the actual
canonical node enumeration; only the proved size equality is transported. -/
theorem node_eq_realClusterNode {q : ℕ}
    (hcluster : BoundedClusterOrder Λ.toLocallyFinite d q)
    (P : IndexedSourceBlock (Λ.clusterBoundary d 0) a) (i : Fin P.size) :
    Λ (P.index i) = hcluster.realClusterNode (Λ.anchorClass d a)
      (Fin.cast (P.size_eq_clusterSize hcluster) i) := by
  have h := strictMono_eq_cast_of_range_eq (P.size_eq_clusterSize hcluster)
    P.carrierNode_strictMono (hcluster.orderedClusterNode (Λ.anchorClass d a)).strictMono
    (P.range_carrierNode_eq_orderedClusterNode hcluster) i
  exact congrArg Subtype.val h

private theorem finite_prefix_dataNorm_congr {m n : ℕ} (h : m = n)
    (x : Fin m → ℝ) (y : Fin n → ℝ)
    (hxy : ∀ i, x i = y (Fin.cast h i)) (f : ℝ → ℂ) :
    (∑ j : Fin m, ‖analyticDividedDifference (finiteNodeSequence x) j f‖) =
      ∑ j : Fin n, ‖analyticDividedDifference (finiteNodeSequence y) j f‖ := by
  subst n
  have heq : x = y := funext hxy
  rw [heq]

/-- Full source-block data are exactly the canonical full-prefix data, for
an arbitrary function, with no smoothness or interpolation premise. -/
theorem dataNorm_eq_canonical {q : ℕ}
    (hcluster : BoundedClusterOrder Λ.toLocallyFinite d q)
    (P : IndexedSourceBlock (Λ.clusterBoundary d 0) a) (f : ℝ → ℂ) :
    P.dataNorm Λ f =
      ∑ j : Fin (hcluster.clusterSize (Λ.anchorClass d a)),
        ‖analyticDividedDifference
          (finiteNodeSequence (hcluster.realClusterNode (Λ.anchorClass d a))) j f‖ := by
  exact finite_prefix_dataNorm_congr (P.size_eq_clusterSize hcluster)
    (fun i => Λ (P.index i)) (hcluster.realClusterNode (Λ.anchorClass d a))
    (P.node_eq_realClusterNode hcluster) f

/-- The squared full-prefix norm is bounded by `q` times the actual sum of
squared canonical data. This is the only within-cluster Cauchy–Schwarz loss. -/
theorem dataNorm_sq_le_canonical_energy {q : ℕ}
    (hcluster : BoundedClusterOrder Λ.toLocallyFinite d q)
    (P : IndexedSourceBlock (Λ.clusterBoundary d 0) a) (f : ℝ → ℂ) :
    (P.dataNorm Λ f) ^ 2 ≤ (q : ℝ) *
      ∑ j : Fin (hcluster.clusterSize (Λ.anchorClass d a)),
        ‖analyticDividedDifference
          (finiteNodeSequence (hcluster.realClusterNode (Λ.anchorClass d a))) j f‖ ^ 2 := by
  rw [P.dataNorm_eq_canonical hcluster]
  let v := fun j : Fin (hcluster.clusterSize (Λ.anchorClass d a)) =>
    ‖analyticDividedDifference
      (finiteNodeSequence (hcluster.realClusterNode (Λ.anchorClass d a))) j f‖
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ => (1 : ℝ)) v
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at hcs
  exact hcs.trans (mul_le_mul_of_nonneg_right
    (by exact_mod_cast hcluster.clusterSize_le (Λ.anchorClass d a))
    (Finset.sum_nonneg (fun j _ => sq_nonneg (v j))))

end IndexedSourceBlock

namespace TwoSidedCarrier

/-- Exact nonnegative repetition formula for integer anchors. It retains
infinite sums as `ℝ≥0∞`, so no summability premise or lost infinity is hidden. -/
theorem tsum_anchorClass_eq_weighted (Λ : TwoSidedCarrier) {d : ℝ} {q : ℕ}
    (hcluster : BoundedClusterOrder Λ.toLocallyFinite d q)
    (e : CanonicalClusterIndex Λ.toLocallyFinite d → ℝ≥0∞) :
    (∑' a : ℤ, e (Λ.anchorClass d a)) =
      ∑' C, (hcluster.clusterSize C : ℝ≥0∞) * e C := by
  rw [← ENNReal.tsum_fiberwise (fun a => e (Λ.anchorClass d a)) (Λ.anchorClass d)]
  apply tsum_congr
  intro C
  change (∑' a : {a : ℤ // Λ.anchorClass d a = C}, e (Λ.anchorClass d a.val)) = _
  have heq : (∑' a : {a : ℤ // Λ.anchorClass d a = C}, e (Λ.anchorClass d a.val)) =
      ∑' _ : {a : ℤ // Λ.anchorClass d a = C}, e C :=
    tsum_congr (fun a => congrArg e a.property)
  rw [heq, ← (Λ.anchorClassFiberEquiv hcluster C).symm.tsum_eq
    (fun _ : {a : ℤ // Λ.anchorClass d a = C} => e C)]
  simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]

/-- Bounded cluster order gives the uniform `q` repetition factor for
arbitrary nonnegative cluster energies. -/
theorem tsum_anchorClass_le (Λ : TwoSidedCarrier) {d : ℝ} {q : ℕ}
    (hcluster : BoundedClusterOrder Λ.toLocallyFinite d q)
    (e : CanonicalClusterIndex Λ.toLocallyFinite d → ℝ≥0∞) :
    (∑' a : ℤ, e (Λ.anchorClass d a)) ≤ (q : ℝ≥0∞) * ∑' C, e C := by
  rw [Λ.tsum_anchorClass_eq_weighted hcluster, ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro C
  gcongr
  exact_mod_cast hcluster.clusterSize_le C

/-- Summability of nonnegative canonical energies survives repetition over
every integer anchor, because each actual fiber has at most `q` elements. -/
theorem summable_anchorClass (Λ : TwoSidedCarrier) {d : ℝ} {q : ℕ}
    (hcluster : BoundedClusterOrder Λ.toLocallyFinite d q)
    {e : CanonicalClusterIndex Λ.toLocallyFinite d → ℝ}
    (he : ∀ C, 0 ≤ e C) (hsum : Summable e) :
    Summable (fun a : ℤ => e (Λ.anchorClass d a)) := by
  let v : CanonicalClusterIndex Λ.toLocallyFinite d → NNReal := fun C => ⟨e C, he C⟩
  have hv : Summable v := NNReal.summable_coe.mp hsum
  have hfinite : (q : ℝ≥0∞) * ∑' C, (v C : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top q)
      (ENNReal.tsum_coe_ne_top_iff_summable.mpr hv)
  have hrep : (∑' a : ℤ, (v (Λ.anchorClass d a) : ℝ≥0∞)) ≠ ⊤ :=
    ne_top_of_le_ne_top hfinite (Λ.tsum_anchorClass_le hcluster (fun C => (v C : ℝ≥0∞)))
  exact NNReal.summable_coe.mpr (ENNReal.tsum_coe_ne_top_iff_summable.mp hrep)

/-- The real-valued repetition bound, with summability proved for the anchor
sum rather than added as a second hypothesis. -/
theorem tsum_anchorClass_real_le (Λ : TwoSidedCarrier) {d : ℝ} {q : ℕ}
    (hcluster : BoundedClusterOrder Λ.toLocallyFinite d q)
    {e : CanonicalClusterIndex Λ.toLocallyFinite d → ℝ}
    (he : ∀ C, 0 ≤ e C) (hsum : Summable e) :
    (∑' a : ℤ, e (Λ.anchorClass d a)) ≤ (q : ℝ) * ∑' C, e C := by
  have h := Λ.tsum_anchorClass_le hcluster (fun C => ENNReal.ofReal (e C))
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun a => he (Λ.anchorClass d a))
      (Λ.summable_anchorClass hcluster he hsum),
    ← ENNReal.ofReal_tsum_of_nonneg he hsum,
    ← ENNReal.ofReal_natCast q, ← ENNReal.ofReal_mul (Nat.cast_nonneg q)] at h
  exact (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (Nat.cast_nonneg q) (tsum_nonneg he))).mp h

end TwoSidedCarrier

end MeyerGeneralProblem
