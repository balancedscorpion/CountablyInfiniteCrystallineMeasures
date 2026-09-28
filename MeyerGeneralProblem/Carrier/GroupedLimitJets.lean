module

public import MeyerGeneralProblem.Carrier.IndexedMultisetCompactness
public import MeyerGeneralProblem.Interpolation.GroupedSubdata
public import MeyerGeneralProblem.Interpolation.MovingDividedDifferences
public import MeyerGeneralProblem.Sampling.BernsteinNormalFamily
public import Mathlib.Analysis.Complex.RealDeriv
import all Mathlib.Analysis.Complex.RealDeriv

@[expose] public section

/-!
# Actual grouped data force multiplicity jets in an indexed limit

Source groups are contiguous finite integer blocks, with their actual boundary
bits. Their sizes may vary. Full prefix data, not point values alone, control
every selected colliding subgroup by the gap-independent Newton estimate.
Complex derivative limits restrict to real derivative limits without changing
their normalization. No lower bound for a within-group gap is used.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set Filter
open scoped Topology BigOperators

/-- Real restriction of an entire function preserves every complex derivative
as the corresponding real derivative. -/
theorem iteratedDeriv_comp_ofReal_of_entire {G : ℂ → ℂ}
    (hG : Differentiable ℂ G) (j : ℕ) :
    iteratedDeriv j (fun x : ℝ => G (x : ℂ)) =
      fun x : ℝ => iteratedDeriv j G (x : ℂ) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    simpa only [iteratedDeriv_succ] using
      ((hG.contDiff.differentiable_iteratedDeriv' j x).hasDerivAt.comp_ofReal).deriv

/-- Entire functions restrict to real smooth functions of every finite order. -/
theorem contDiff_comp_ofReal_of_entire {G : ℂ → ℂ}
    (hG : Differentiable ℂ G) (j : ℕ) :
    ContDiff ℝ j (fun x : ℝ => G (x : ℂ)) := by
  exact (hG.contDiff.restrict_scalars ℝ).comp Complex.ofRealCLM.contDiff

/-- The complex normal-family derivative convergence supplies the exact real
derivative convergence required by the moving-node HG theorem. -/
theorem tendstoLocallyUniformly_real_iteratedDeriv_of_entire
    {F : ℕ → ℂ → ℂ} {G : ℂ → ℂ}
    (hF : ∀ n, Differentiable ℂ (F n)) (hG : Differentiable ℂ G)
    (hconv : TendstoLocallyUniformlyOn F G atTop univ) (j : ℕ) :
    TendstoLocallyUniformly
      (fun n => iteratedDeriv j (fun x : ℝ => F n (x : ℂ)))
      (iteratedDeriv j (fun x : ℝ => G (x : ℂ))) atTop := by
  simp only [iteratedDeriv_comp_ofReal_of_entire (hF _),
    iteratedDeriv_comp_ofReal_of_entire hG]
  exact (tendstoLocallyUniformlyOn_univ.mp
    (tendstoLocallyUniformlyOn_iteratedDeriv_of_entire hF hconv j)).comp
      Complex.ofReal Complex.continuous_ofReal

/-- A genuine contiguous source group containing an anchor index. Both ends
are actual boundaries, and no boundary lies in its interior. -/
structure IndexedSourceBlock (b : ℤ → Bool) (anchor : ℤ) where
  /-- First integer index of the actual source group. -/
  first : ℤ
  /-- Number of nodes in the actual source group. -/
  size : ℕ
  anchor_mem : first ≤ anchor ∧ anchor < first + size
  left_boundary : b first = true
  right_boundary : b (first + size) = true
  interior : ∀ k : ℤ, first < k → k < first + size → b k = false

namespace IndexedSourceBlock

variable {b : ℤ → Bool} {anchor : ℤ}

/-- The actual integer indices of the source group, in increasing order. -/
def index (P : IndexedSourceBlock b anchor) : Fin P.size ↪ ℤ where
  toFun j := P.first + j
  inj' := by
    intro i j hij
    apply Fin.ext
    exact_mod_cast (add_left_cancel hij : (i : ℤ) = (j : ℤ))

/-- Every listed index lies in the actual half-open group block. -/
theorem index_mem (P : IndexedSourceBlock b anchor) (j : Fin P.size) :
    P.first ≤ P.index j ∧ P.index j < P.first + P.size := by
  change P.first ≤ P.first + (j : ℤ) ∧ P.first + (j : ℤ) < P.first + P.size
  constructor <;> omega

/-- Every index of the half-open block occurs in its explicit enumeration. -/
theorem exists_index (P : IndexedSourceBlock b anchor) {k : ℤ}
    (hk : P.first ≤ k ∧ k < P.first + P.size) : ∃ j, P.index j = k := by
  refine ⟨⟨(k - P.first).toNat, by omega⟩, ?_⟩
  change P.first + ((k - P.first).toNat : ℤ) = k
  omega

/-- Absence of a boundary between two indices forces the second index into
the actual block containing the first. Endpoint boundary bits are essential. -/
theorem mem_of_no_boundary (P : IndexedSourceBlock b anchor) {k : ℤ}
    (hforward : ¬ ∃ l, anchor < l ∧ l ≤ k ∧ b l = true)
    (hbackward : ¬ ∃ l, k < l ∧ l ≤ anchor ∧ b l = true) :
    P.first ≤ k ∧ k < P.first + P.size := by
  constructor
  · by_contra h
    exact hbackward ⟨P.first, lt_of_not_ge h, P.anchor_mem.1, P.left_boundary⟩
  · by_contra h
    exact hforward ⟨P.first + P.size, P.anchor_mem.2, le_of_not_gt h,
      P.right_boundary⟩

/-- Common adjacent-gap bounds give a group diameter bound independent of
location and every within-group gap. -/
theorem diameter_le {q : ℕ} {d H : ℝ} {s : ℤ → ℝ}
    (P : IndexedSourceBlock b anchor) (h : IndexedMultisetGeometry q d H s)
    (hsize : P.size ≤ q) (i j : Fin P.size) :
    dist (s (P.index i)) (s (P.index j)) ≤ (q : ℝ) * H := by
  have hbound (k : Fin P.size) :
      s P.first ≤ s (P.index k) ∧ s (P.index k) ≤ s P.first + (q : ℝ) * H := by
    refine ⟨h.monotone (P.index_mem k).1, ?_⟩
    have hupper := h.add_nat_upper P.first q
    have hle : P.index k ≤ P.first + q := by
      have := (P.index_mem k).2
      omega
    exact (h.monotone hle).trans hupper
  rw [Real.dist_eq, abs_le]
  constructor <;> linarith [hbound i, hbound j]

/-- Sum of the norms of all actual initial-segment divided differences on the
entire source group. This includes data at every order below its size. -/
def dataNorm (P : IndexedSourceBlock b anchor) (s : ℤ → ℝ) (f : ℝ → ℂ) : ℝ :=
  ∑ j : Fin P.size,
    ‖analyticDividedDifference (finiteNodeSequence (fun i => s (P.index i))) j f‖

/-- A selected subgroup of actual integer indices is controlled by the full
source group, even if its complementary nodes converge to other centers. -/
theorem norm_subgroup_le {q m : ℕ} {d H : ℝ} {s : ℤ → ℝ}
    (P : IndexedSourceBlock b anchor) (h : IndexedMultisetGeometry q d H s)
    (hs : Function.Injective s) (hsize : P.size ≤ q)
    (indices : Fin m ↪ ℤ)
    (hmem : ∀ i, P.first ≤ indices i ∧ indices i < P.first + P.size)
    (f : ℝ → ℂ) (j : Fin m) :
    ‖analyticDividedDifference (finiteNodeSequence (fun i => s (indices i))) j f‖ ≤
      boundedClusterNewtonBound q ((q : ℝ) * H) * P.dataNorm s f := by
  choose selection hselection using fun i => P.exists_index (hmem i)
  let e : Fin m ↪ Fin P.size := ⟨selection, fun i k hik =>
    indices.injective ((hselection i).symm.trans
      ((congrArg P.index hik).trans (hselection k)))⟩
  have heq : (fun i => s (P.index (e i))) = fun i => s (indices i) := by
    funext i
    exact congrArg s (hselection i)
  have hbound := norm_analyticDividedDifference_subgroup_le_of_diameter_bound
    hsize (fun i => s (P.index i)) (hs.comp P.index.injective) e f j
    (mul_nonneg (Nat.cast_nonneg q) h.upperGap_nonneg) (P.diameter_le h hsize)
  rw [heq] at hbound
  exact hbound

end IndexedSourceBlock

/-- Actual boundaries occurring within every q-index interval construct a
full source block of size at most q at every anchor. This is a finite minimum
and maximum construction, not a presumed group decomposition. -/
theorem exists_indexedSourceBlock_of_boundary_every_q_steps
    {b : ℤ → Bool} {q : ℕ}
    (hboundary : ∀ i : ℤ, ∃ k ∈ Finset.Ioc i (i + q), b k = true) (anchor : ℤ) :
    ∃ P : IndexedSourceBlock b anchor, P.size ≤ q := by
  classical
  let left := (Finset.Ioc (anchor - q) anchor).filter (fun k => b k = true)
  have hleft : left.Nonempty := by
    obtain ⟨k, hk, hbk⟩ := hboundary (anchor - q)
    refine ⟨k, Finset.mem_filter.mpr ⟨?_, hbk⟩⟩
    simpa only [sub_add_cancel] using hk
  let first := left.max' hleft
  have hfirst : anchor - q < first ∧ first ≤ anchor ∧ b first = true := by
    have h := Finset.mem_filter.mp (left.max'_mem hleft)
    exact ⟨(Finset.mem_Ioc.mp h.1).1, (Finset.mem_Ioc.mp h.1).2, h.2⟩
  let right := (Finset.Ioc first (first + q)).filter (fun k => b k = true)
  have hright : right.Nonempty := by
    obtain ⟨k, hk, hbk⟩ := hboundary first
    exact ⟨k, Finset.mem_filter.mpr ⟨hk, hbk⟩⟩
  let last := right.min' hright
  have hlast : first < last ∧ last ≤ first + q ∧ b last = true := by
    have h := Finset.mem_filter.mp (right.min'_mem hright)
    exact ⟨(Finset.mem_Ioc.mp h.1).1, (Finset.mem_Ioc.mp h.1).2, h.2⟩
  have hanchor : anchor < last := by
    by_contra h
    have hmem : last ∈ left :=
      Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr
        ⟨hfirst.1.trans hlast.1, le_of_not_gt h⟩, hlast.2.2⟩
    have := left.le_max' last hmem
    omega
  have hsize : ((last - first).toNat : ℤ) = last - first := by omega
  refine ⟨{
    first := first
    size := (last - first).toNat
    anchor_mem := by rw [hsize]; constructor <;> omega
    left_boundary := hfirst.2.2
    right_boundary := by simpa only [hsize, add_sub_cancel] using hlast.2.2
    interior := ?_ }, by change (last - first).toNat ≤ q; omega⟩
  intro k hk hk'
  have hklt : k < last := by omega
  by_contra h
  have hbk : b k = true := by cases hval : b k <;> simp_all
  have hmem : k ∈ right := Finset.mem_filter.mpr
    ⟨Finset.mem_Ioc.mpr ⟨hk, hklt.le.trans hlast.2.1⟩, hbk⟩
  have := right.min'_le k hmem
  omega

/-- Stabilized genuine group boundaries place any finite collided index
selection into one actual source block eventually. -/
theorem eventually_collided_indices_mem_sourceBlock
    {B : ℕ → ℤ → Bool} {s : ℤ → ℝ} {b : ℤ → Bool}
    {d : ℝ} {m : ℕ} (indices : Fin (m + 1) ↪ ℤ) {x : ℝ}
    (hcollision : ∀ i, s (indices i) = x)
    (hbits : ∀ j, ∀ᶠ n in atTop, B n j = b j)
    (hsep : IndexedGroupSeparation s b d) (hd : 0 < d)
    (P : ∀ n, IndexedSourceBlock (B n) (indices 0)) :
    ∀ᶠ n in atTop, ∀ i,
      (P n).first ≤ indices i ∧ indices i < (P n).first + (P n).size := by
  apply eventually_all.mpr
  intro i
  have hforward := eventually_no_source_boundary_of_equal_coordinates hbits hsep hd
    ((hcollision 0).trans (hcollision i).symm)
  have hbackward := eventually_no_source_boundary_of_equal_coordinates hbits hsep hd
    ((hcollision i).trans (hcollision 0).symm)
  filter_upwards [hforward, hbackward] with n hn hk
  exact (P n).mem_of_no_boundary hn hk

/-- Vanishing full-group data imply a true derivative jet at any selected
collision. Nodes elsewhere in the source group need not collide. -/
theorem iteratedDeriv_eq_zero_of_collided_sourceBlock_data
    {q order : ℕ} {d H : ℝ} {S : ℕ → ℤ → ℝ} {B : ℕ → ℤ → Bool}
    {s : ℤ → ℝ} {b : ℤ → Bool} {x : ℝ}
    (hS : ∀ n, IndexedMultisetGeometry q d H (S n))
    (hinjective : ∀ n, Function.Injective (S n)) (hd : 0 < d)
    (hcoords : ∀ j, Tendsto (fun n => S n j) atTop (𝓝 (s j)))
    (hbits : ∀ j, ∀ᶠ n in atTop, B n j = b j)
    (hsep : IndexedGroupSeparation s b d)
    (indices : Fin (order + 1) ↪ ℤ) (hcollision : ∀ i, s (indices i) = x)
    (P : ∀ n, IndexedSourceBlock (B n) (indices 0)) (hsize : ∀ n, (P n).size ≤ q)
    (f : ℕ → ℝ → ℂ) (g : ℝ → ℂ)
    (hf : ∀ n, ContDiff ℝ order (f n)) (hg : ContDiff ℝ order g)
    (hderiv : TendstoLocallyUniformly (fun n => iteratedDeriv order (f n))
      (iteratedDeriv order g) atTop)
    (hdata : Tendsto (fun n => (P n).dataNorm (S n) (f n)) atTop (𝓝 0)) :
    iteratedDeriv order g x = 0 := by
  have hnodes : Tendsto (fun n i => S n (indices i)) atTop (𝓝 (fun _ => x)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    simpa only [hcollision i] using hcoords (indices i)
  have hsmall : Tendsto (fun n => analyticDividedDifference
      (finiteNodeSequence (fun i => S n (indices i))) order (f n)) atTop (𝓝 0) := by
    apply squeeze_zero_norm'
      (a := fun n => boundedClusterNewtonBound q ((q : ℝ) * H) *
        (P n).dataNorm (S n) (f n))
    · filter_upwards [eventually_collided_indices_mem_sourceBlock indices hcollision
        hbits hsep hd P] with n hn
      exact (P n).norm_subgroup_le (hS n) (hinjective n) (hsize n) indices hn (f n)
        ⟨order, by omega⟩
    · simpa only [mul_zero] using hdata.const_mul (boundedClusterNewtonBound q ((q : ℝ) * H))
  have hlimit := tendsto_analyticDividedDifference_of_tendstoLocallyUniformly_iteratedDeriv
    order (fun n i => S n (indices i)) (fun _ => x) f g hf hg hnodes hderiv
  rw [analyticDividedDifference_finite_repeated_node_of_contDiff x order hg] at hlimit
  have hjet := tendsto_nhds_unique hlimit hsmall
  exact (smul_eq_zero.mp hjet).resolve_left (by positivity)

/-- The actual cardinality of each indexed limit fiber is a lower bound for
the vanishing-jet multiplicity, derived from the entire full-group data. -/
theorem indexedMultiset_jets_of_sourceBlock_data
    {q : ℕ} {d H : ℝ} {S : ℕ → ℤ → ℝ} {B : ℕ → ℤ → Bool}
    {s : ℤ → ℝ} {b : ℤ → Bool}
    (hS : ∀ n, IndexedMultisetGeometry q d H (S n))
    (hinjective : ∀ n, Function.Injective (S n)) (hd : 0 < d)
    (hcoords : ∀ j, Tendsto (fun n => S n j) atTop (𝓝 (s j)))
    (hbits : ∀ j, ∀ᶠ n in atTop, B n j = b j)
    (hsep : ∀ n, IndexedGroupSeparation (S n) (B n) d)
    (P : ∀ n anchor, IndexedSourceBlock (B n) anchor)
    (hsize : ∀ n anchor, (P n anchor).size ≤ q)
    {F : ℕ → ℂ → ℂ} {G : ℂ → ℂ}
    (hF : ∀ n, Differentiable ℂ (F n)) (hG : Differentiable ℂ G)
    (hconv : TendstoLocallyUniformlyOn F G atTop univ)
    (hdata : ∀ anchor, Tendsto (fun n =>
      (P n anchor).dataNorm (S n) (fun x : ℝ => F n (x : ℂ))) atTop (𝓝 0)) :
    ∀ x : ℝ, ∀ j < indexedMultisetMultiplicity s x, iteratedDeriv j G (x : ℂ) = 0 := by
  classical
  intro x j hj
  have hs := IndexedMultisetGeometry.of_pointwise_tendsto hS hcoords
  let : Fintype ↥{i : ℤ | s i = x} := (hs.finite_fiber hd x).fintype
  have hcard : Fintype.card (Fin (j + 1)) ≤ Fintype.card ↥{i : ℤ | s i = x} := by
    rw [Fintype.card_fin]
    rw [Set.fintypeCard_eq_ncard]
    exact Nat.succ_le_of_lt hj
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  let indices : Fin (j + 1) ↪ ℤ := e.trans (Function.Embedding.subtype _)
  have hcollision (i : Fin (j + 1)) : s (indices i) = x := (e i).property
  have h := iteratedDeriv_eq_zero_of_collided_sourceBlock_data hS hinjective hd hcoords
    hbits (indexedGroupSeparation_of_pointwise_tendsto hsep hcoords hbits) indices hcollision
    (fun n => P n (indices 0)) (fun n => hsize n (indices 0))
    (fun n (x : ℝ) => F n (x : ℂ)) (fun x : ℝ => G (x : ℂ))
    (fun n => contDiff_comp_ofReal_of_entire (hF n) j)
    (contDiff_comp_ofReal_of_entire hG j)
    (tendstoLocallyUniformly_real_iteratedDeriv_of_entire hF hG hconv j) (hdata (indices 0))
  simpa only [iteratedDeriv_comp_ofReal_of_entire hG] using h

end

end MeyerGeneralProblem
