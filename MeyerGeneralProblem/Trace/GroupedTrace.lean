module

public import MeyerGeneralProblem.Interpolation.HermiteGenocchiHigher
public import MeyerGeneralProblem.Carrier.ClusterDecomposition
public import MeyerGeneralProblem.Carrier.SignedSquareCarrier
public import MeyerGeneralProblem.Trace.Presentation
public import MeyerGeneralProblem.Endpoint.IntrinsicFixedOrder
public import Mathlib.LinearAlgebra.Matrix.Block
import all Mathlib.LinearAlgebra.Matrix.Block

@[expose] public section

/-!
# Exact finite-cluster grouped traces

Actual distinct nodes use barycentric Newton weights on initial segments.
The induced finite change of coordinates is invertible, but no uniform
conditioning or infinite Bessel bound is inferred from that fact. Grouped
Dirac atoms carry a single nonzero normalization per cluster. Repeated-node
analytic divided differences remain a separate derivative-jet construction.
-/

namespace MeyerGeneralProblem

noncomputable section

open Finset Polynomial

section FiniteAlgebra

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Barycentric initial-segment weight, extended by zero past the segment. -/
def groupedNewtonWeight {n : ℕ} (nodes : Fin n → K) (j i : Fin n) : K :=
  if i ≤ j then Lagrange.nodalWeight (Iic j) nodes i else 0

/-- Matrix of the initial divided-difference functionals on point values. -/
def groupedNewtonMatrix {n : ℕ} (nodes : Fin n → K) : Matrix (Fin n) (Fin n) K :=
  Matrix.of (groupedNewtonWeight nodes)

/-- Initial-segment divided-difference weights are lower triangular. -/
theorem groupedNewtonMatrix_lowerTriangular {n : ℕ} (nodes : Fin n → K) :
    (groupedNewtonMatrix nodes).IsLowerTriangular := by
  intro i j hij
  change i < j at hij
  simp [groupedNewtonMatrix, groupedNewtonWeight, not_le_of_gt hij]

/-- The diagonal is the reciprocal product of the preceding node gaps. -/
theorem groupedNewtonMatrix_diag {n : ℕ} (nodes : Fin n → K) (j : Fin n) :
    groupedNewtonMatrix nodes j j = ∏ i ∈ Iio j, (nodes j - nodes i)⁻¹ := by
  simp only [groupedNewtonMatrix, Matrix.of_apply, groupedNewtonWeight,
    le_refl, ↓reduceIte, Lagrange.nodalWeight]
  congr 1
  ext i
  simp only [mem_erase, mem_Iic, mem_Iio]
  exact ⟨fun h => lt_of_le_of_ne h.2 h.1, fun h => ⟨h.ne, h.le⟩⟩

/-- Distinct nodes give a nonzero determinant; no quantitative inverse bound
is asserted. -/
theorem groupedNewtonMatrix_det_ne_zero {n : ℕ} (nodes : Fin n → K)
    (hnodes : Function.Injective nodes) : (groupedNewtonMatrix nodes).det ≠ 0 := by
  rw [Matrix.det_of_isLowerTriangular _ (groupedNewtonMatrix_lowerTriangular nodes)]
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  rw [groupedNewtonMatrix_diag]
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  exact inv_ne_zero (sub_ne_zero.mpr (hnodes.ne (Finset.mem_Iio.mp hi).ne.symm))

/-- The explicit invertible barycentric coordinate map on a finite cluster. -/
def groupedNewtonValuesEquiv {n : ℕ} (nodes : Fin n → K)
    (hnodes : Function.Injective nodes) : (Fin n → K) ≃ₗ[K] (Fin n → K) :=
  Matrix.toLinearEquiv' (groupedNewtonMatrix nodes)
    (Matrix.invertibleOfIsUnitDet _ (isUnit_iff_ne_zero.mpr
      (groupedNewtonMatrix_det_ne_zero nodes hnodes)))

private theorem eval_newtonBasisPolynomial_of_lt {n : ℕ} (nodes : Fin n → K)
    {i k : Fin n} (hik : i < k) : (newtonBasisPolynomial nodes k).eval (nodes i) = 0 := by
  rw [eval_newtonBasisPolynomial]
  apply Finset.prod_eq_zero (Finset.mem_Iio.mpr hik)
  exact sub_self _

def groupedNewtonPrefix {n : ℕ} (nodes : Fin n → K) (c : Fin n → K)
    (j : Fin n) : K[X] := ∑ k ∈ Iic j, Polynomial.C (c k) * newtonBasisPolynomial nodes k

private theorem groupedNewtonPrefix_degree {n : ℕ} (nodes : Fin n → K)
    (c : Fin n → K) (j : Fin n) :
    (groupedNewtonPrefix nodes c j).degree < (j.val + 1 : ℕ) := by
  apply Polynomial.mem_degreeLT.mp
  apply Submodule.sum_mem
  intro k hk
  rw [← Polynomial.smul_eq_C_mul]
  apply Submodule.smul_mem
  apply Polynomial.mem_degreeLT.mpr
  apply (Polynomial.natDegree_lt_iff_degree_lt
    (monic_newtonBasisPolynomial nodes k).ne_zero).mp
  rw [natDegree_newtonBasisPolynomial]
  have hkj : k ≤ j := Finset.mem_Iic.mp hk
  exact Nat.lt_succ_of_le hkj

private theorem groupedNewtonPrefix_coeff {n : ℕ} (nodes : Fin n → K)
    (c : Fin n → K) (j : Fin n) : (groupedNewtonPrefix nodes c j).coeff j = c j := by
  simp only [groupedNewtonPrefix, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul]
  rw [Finset.sum_eq_single j]
  · rw [← natDegree_newtonBasisPolynomial nodes j,
      (monic_newtonBasisPolynomial nodes j).coeff_natDegree, mul_one]
  · intro k hk hkj
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt, mul_zero]
    rw [natDegree_newtonBasisPolynomial]
    exact (show k < j from lt_of_le_of_ne (Finset.mem_Iic.mp hk) hkj)
  · simp

private theorem groupedNewtonPrefix_eval {n : ℕ} (nodes : Fin n → K)
    (hnodes : Function.Injective nodes) (values : Fin n → K)
    (j i : Fin n) (hij : i ≤ j) :
    (groupedNewtonPrefix nodes (dividedDifferences nodes hnodes values) j).eval (nodes i) =
      values i := by
  rw [← eval_newtonInterpolantFromValues_at_node nodes hnodes values i,
    newtonInterpolantFromValues_eq_sum]
  simp only [groupedNewtonPrefix, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro k _ hk
  have hik : i < k := hij.trans_lt (lt_of_not_ge (by simpa only [mem_Iic] using hk))
  rw [eval_newtonBasisPolynomial_of_lt nodes hik, mul_zero]

/-- The explicit source barycentric sum equals the existing Newton prefix
coordinate. This pins both the prefix convention and all denominators. -/
theorem dividedDifferences_eq_groupedNewtonWeights {n : ℕ} (nodes : Fin n → K)
    (hnodes : Function.Injective nodes) (values : Fin n → K) (j : Fin n) :
    dividedDifferences nodes hnodes values j =
      ∑ i, groupedNewtonWeight nodes j i * values i := by
  have h := Lagrange.coeff_eq_sum (s := Iic j) hnodes.injOn
    (P := groupedNewtonPrefix nodes (dividedDifferences nodes hnodes values) j)
    (by simpa only [Fin.card_Iic] using
      groupedNewtonPrefix_degree nodes (dividedDifferences nodes hnodes values) j)
  rw [Fin.card_Iic, Nat.add_sub_cancel, groupedNewtonPrefix_coeff] at h
  rw [h]
  simp only [groupedNewtonWeight, ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  have hfilter : (Finset.univ.filter fun i : Fin n => i ≤ j) = Iic j := by ext; simp
  rw [hfilter]
  apply Finset.sum_congr rfl
  intro i hi
  rw [groupedNewtonPrefix_eval nodes hnodes values j i (Finset.mem_Iic.mp hi)]
  simp only [Lagrange.nodalWeight, ← Finset.prod_inv_distrib, div_eq_mul_inv, mul_comm]

/-- The explicit barycentric matrix is exactly the earlier values-to-Newton
equivalence, not merely another invertible family of traces. -/
theorem groupedNewtonValuesEquiv_eq {n : ℕ} (nodes : Fin n → K)
    (hnodes : Function.Injective nodes) :
    groupedNewtonValuesEquiv nodes hnodes =
      valuesEquivDividedDifferencesOfInjective nodes hnodes := by
  apply LinearEquiv.ext
  intro values
  funext j
  have hmap : (groupedNewtonValuesEquiv nodes hnodes).toLinearMap =
      (groupedNewtonMatrix nodes).mulVecLin := Matrix.toLinearEquiv'_apply _ _
  rw [show groupedNewtonValuesEquiv nodes hnodes values j =
      ((groupedNewtonMatrix nodes).mulVecLin values) j from congrFun
        (LinearMap.congr_fun hmap values) j]
  exact (dividedDifferences_eq_groupedNewtonWeights nodes hnodes values j).symm

/-- The atom corresponding to one actual barycentric prefix functional. -/
def groupedFiniteAtom {n : ℕ} (nodes : Fin n → K) (v : Fin n → V) (j : Fin n) : V :=
  ∑ i, groupedNewtonWeight nodes j i • v i

/-- Finite synthesis in grouped coordinates is point synthesis after the
transpose barycentric coordinate change. -/
theorem groupedFiniteAtom_synthesis {n : ℕ} (nodes : Fin n → K) (v : Fin n → V) :
    Fintype.linearCombination K (groupedFiniteAtom nodes v) =
      (Fintype.linearCombination K v).comp
        (Matrix.mulVecLin (groupedNewtonMatrix nodes).transpose) := by
  ext c
  simp only [Fintype.linearCombination_apply, groupedFiniteAtom, Finset.smul_sum,
    smul_smul, LinearMap.comp_apply, Matrix.mulVecLin_apply, Matrix.mulVec,
    dotProduct, Matrix.transpose_apply, groupedNewtonMatrix, Matrix.of_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm]

/-- The finite grouped synthesis has exactly the same algebraic range as
point synthesis, even when the atoms themselves are dependent. -/
theorem groupedFiniteAtom_synthesis_range {n : ℕ} (nodes : Fin n → K)
    (hnodes : Function.Injective nodes) (v : Fin n → V) :
    (Fintype.linearCombination K (groupedFiniteAtom nodes v)).range =
      (Fintype.linearCombination K v).range := by
  rw [groupedFiniteAtom_synthesis]
  apply LinearMap.range_comp_of_range_eq_top
  apply LinearMap.range_eq_top.mpr
  let e := Matrix.toLinearEquiv' (groupedNewtonMatrix nodes).transpose
    (Matrix.invertibleOfIsUnitDet _ (isUnit_iff_ne_zero.mpr (by
      rw [Matrix.det_transpose]
      exact groupedNewtonMatrix_det_ne_zero nodes hnodes)))
  have he : e.toLinearMap = (groupedNewtonMatrix nodes).transpose.mulVecLin :=
    Matrix.toLinearEquiv'_apply _ _
  rw [← he]
  exact e.surjective

/-- Exact equality of the actual per-cluster algebraic spans. -/
theorem groupedFiniteAtom_span {n : ℕ} (nodes : Fin n → K)
    (hnodes : Function.Injective nodes) (v : Fin n → V) :
    Submodule.span K (Set.range (groupedFiniteAtom nodes v)) =
      Submodule.span K (Set.range v) := by
  rw [← Fintype.range_linearCombination, ← Fintype.range_linearCombination]
  exact groupedFiniteAtom_synthesis_range nodes hnodes v

/-- A singleton grouped functional is exactly the original point functional. -/
@[simp]
theorem groupedFiniteAtom_singleton (nodes : Fin 1 → K) (v : Fin 1 → V) :
    groupedFiniteAtom nodes v 0 = v 0 := by
  unfold groupedFiniteAtom
  rw [Fin.sum_univ_one]
  change groupedNewtonMatrix nodes 0 0 • v 0 = v 0
  rw [groupedNewtonMatrix_diag, show Iio (0 : Fin 1) = ∅ by decide]
  simp

end FiniteAlgebra

section CanonicalClusters

/-- Quotient index of the exact short-gap connected components. -/
abbrev CanonicalClusterIndex (S : LocallyFiniteCarrier) (d : ℝ) :=
  Quotient (clusterSetoid S d)

namespace BoundedClusterOrder

variable {S : LocallyFiniteCarrier} {d : ℝ} {q : ℕ} (horder : BoundedClusterOrder S d q)

/-- The finite set of points in an exact canonical cluster. -/
def clusterFinset (C : CanonicalClusterIndex S d) : Finset S.subtype :=
  (horder.clusterClass_finite_card_le C.out).1.toFinset

/-- Number of distinct actual points in a canonical cluster. -/
abbrev clusterSize (C : CanonicalClusterIndex S d) : ℕ := (horder.clusterFinset C).card

/-- Canonical clusters are enumerated in strictly increasing real order. -/
def orderedClusterNode (C : CanonicalClusterIndex S d) :
    Fin (horder.clusterSize C) ↪o S.subtype :=
  (horder.clusterFinset C).orderEmbOfFin rfl

/-- The ordered enumeration has exactly the connected class as its range. -/
theorem range_orderedClusterNode (C : CanonicalClusterIndex S d) :
    Set.range (horder.orderedClusterNode C) = clusterClass S d C.out := by
  exact ((horder.clusterFinset C).range_orderEmbOfFin rfl).trans
    (Set.Finite.coe_toFinset _)

/-- Every canonical cluster is nonempty. -/
theorem clusterSize_pos (C : CanonicalClusterIndex S d) : 0 < horder.clusterSize C := by
  apply Finset.card_pos.mpr
  refine ⟨C.out, ?_⟩
  simp only [clusterFinset, Set.Finite.mem_toFinset]
  exact mem_clusterClass_self S d C.out

/-- Enumeration preserves the proved cluster-order bound. -/
theorem clusterSize_le (C : CanonicalClusterIndex S d) : horder.clusterSize C ≤ q := by
  have h := (horder.clusterClass_finite_card_le C.out).2
  rw [Set.ncard_eq_toFinset_card _ (horder.clusterClass_finite_card_le C.out).1] at h
  exact h

/-- An enumerated node belongs to precisely its declared quotient class. -/
theorem orderedClusterNode_class (C : CanonicalClusterIndex S d)
    (i : Fin (horder.clusterSize C)) :
    Quotient.mk (clusterSetoid S d) (horder.orderedClusterNode C i) = C := by
  have hi : horder.orderedClusterNode C i ∈ clusterClass S d C.out := by
    rw [← horder.range_orderedClusterNode C]
    exact ⟨i, rfl⟩
  exact (Quotient.sound hi).symm.trans C.out_eq

/-- The disjoint union of canonical finite enumerations covers each carrier
point once, with no multiplicity change. -/
theorem orderedClusterNode_bijective : Function.Bijective
    (fun x : Σ C : CanonicalClusterIndex S d, Fin (horder.clusterSize C) =>
      horder.orderedClusterNode x.1 x.2) := by
  constructor
  · rintro ⟨C, i⟩ ⟨D, j⟩ heq
    change horder.orderedClusterNode C i = horder.orderedClusterNode D j at heq
    have hCD : C = D := by
      rw [← horder.orderedClusterNode_class C i, ← horder.orderedClusterNode_class D j, heq]
    subst D
    have hij : i = j := (horder.orderedClusterNode C).injective heq
    subst j
    rfl
  · intro x
    let C : CanonicalClusterIndex S d := Quotient.mk (clusterSetoid S d) x
    have hx : x ∈ clusterClass S d C.out :=
      @Quotient.mk_out _ (clusterSetoid S d) x
    rw [← horder.range_orderedClusterNode C] at hx
    obtain ⟨i, hi⟩ := hx
    exact ⟨⟨C, i⟩, hi⟩

end BoundedClusterOrder

/-- Signed-square coordinates give an exact equivalence of carrier point
types; its inverse is used only on actual image points. -/
def LocallyFiniteCarrier.signedSquareSubtypeEquiv (S : LocallyFiniteCarrier) :
    S.subtype ≃ S.signedSquareImage.subtype :=
  Equiv.ofBijective (fun x => ⟨signedSquare x, ⟨x, x.property, rfl⟩⟩) (by
    constructor
    · intro x y hxy
      apply Subtype.ext
      exact signedSquare_injective (congrArg Subtype.val hxy)
    · rintro ⟨s, x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩)

/-- A grouping records actual distinct carrier points and exact coverage.
Its finite data do not assert any infinite-dimensional conditioning. -/
structure OrderedCarrierGrouping (S : LocallyFiniteCarrier) (κ : Type*) where
  /-- Number of actual points in each finite group. -/
  size : κ → ℕ
  size_pos : ∀ C, 0 < size C
  /-- The actual carrier nodes, in increasing signed-square order. -/
  point : ∀ C, Fin (size C) → S.subtype
  strictMono : ∀ C, StrictMono (fun i => signedSquare (point C i))
  bijective : Function.Bijective (fun x : Σ C, Fin (size C) => point x.1 x.2)

/-- Bounded cluster order supplies a grouping by the exact connected classes
of the signed-square image, not by an arbitrary re-partition. -/
def canonicalSignedSquareGrouping (S : LocallyFiniteCarrier) {d : ℝ} {q : ℕ}
    (horder : BoundedClusterOrder S.signedSquareImage d q) :
    OrderedCarrierGrouping S (CanonicalClusterIndex S.signedSquareImage d) where
  size := horder.clusterSize
  size_pos := horder.clusterSize_pos
  point C i := S.signedSquareSubtypeEquiv.symm (horder.orderedClusterNode C i)
  strictMono C := by
    have he (i : Fin (horder.clusterSize C)) :
        signedSquare (S.signedSquareSubtypeEquiv.symm (horder.orderedClusterNode C i)) =
          (horder.orderedClusterNode C i : ℝ) :=
      congrArg Subtype.val (S.signedSquareSubtypeEquiv.apply_symm_apply _)
    intro i j hij
    dsimp only
    rw [he, he]
    exact (horder.orderedClusterNode C).strictMono hij
  bijective := S.signedSquareSubtypeEquiv.symm.bijective.comp horder.orderedClusterNode_bijective

end CanonicalClusters

private theorem span_range_nonzero_smul {K V ι : Type*} [Field K]
    [AddCommGroup V] [Module K V] (v : ι → V) (a : ι → K) (ha : ∀ i, a i ≠ 0) :
    Submodule.span K (Set.range (fun i => a i • v i)) = Submodule.span K (Set.range v) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    have h := (Submodule.span K (Set.range (fun i => a i • v i))).smul_mem (a i)⁻¹
      (Submodule.subset_span (show a i • v i ∈ Set.range (fun i => a i • v i) from ⟨i, rfl⟩))
    rw [smul_smul, inv_mul_cancel₀ (ha i), one_smul] at h
    exact h

namespace OrderedCarrierGrouping

variable {S : LocallyFiniteCarrier} {κ : Type*} (G : OrderedCarrierGrouping S κ)

/-- The double index of actual clusters and their initial segments. -/
abbrev Index := Σ C : κ, Fin (G.size C)

/-- The physical point of smallest modulus in a cluster, as in the retained
single-chain normalization. Ties are harmless and resolved by choice. -/
def anchor (C : κ) : Fin (G.size C) := by
  let : Nonempty (Fin (G.size C)) := ⟨⟨0, G.size_pos C⟩⟩
  exact (Finite.exists_min (fun i => |(G.point C i : ℝ)|)).choose

/-- The selected normalization point really has smallest physical modulus. -/
theorem anchor_min (C : κ) (i : Fin (G.size C)) :
    |(G.point C (G.anchor C) : ℝ)| ≤ |(G.point C i : ℝ)| := by
  let : Nonempty (Fin (G.size C)) := ⟨⟨0, G.size_pos C⟩⟩
  exact (Finite.exists_min (fun i => |(G.point C i : ℝ)|)).choose_spec i

/-- Complex signed-square nodes for the actual finite cluster. -/
def nodes (C : κ) (i : Fin (G.size C)) : ℂ := signedSquare (G.point C i)

/-- No nodes repeat in an actual grouped Dirac family. -/
theorem nodes_injective (C : κ) : Function.Injective (G.nodes C) :=
  Complex.ofReal_injective.comp (G.strictMono C).injective

/-- The one-per-cluster normalization is the actual negative-scale norm of
the Dirac at the smallest-modulus physical point. -/
def weight (m : ℕ) (hm : 1 ≤ m) (C : κ) : ℝ :=
  ‖hermitePointMass m hm (G.point C (G.anchor C))‖

/-- Every chain normalization is genuinely positive. -/
theorem weight_pos (m : ℕ) (hm : 1 ≤ m) (C : κ) : 0 < G.weight m hm C :=
  norm_pos_iff.mpr (hermitePointMass_ne_zero m hm _)

/-- The unnormalized grouped trace is the exact barycentric combination of
genuine Dirac vectors, with no derivative jets inserted. -/
def rawAtom (m : ℕ) (hm : 1 ≤ m) (C : κ) (j : Fin (G.size C)) :
    HermiteScale (-(m : ℤ)) :=
  groupedFiniteAtom (G.nodes C) (fun i => hermitePointMass m hm (G.point C i)) j

/-- The source-normalized grouped Dirac atom, using one common weight for
the entire finite cluster. -/
def atom (m : ℕ) (hm : 1 ≤ m) (x : G.Index) : HermiteScale (-(m : ℤ)) :=
  ((G.weight m hm x.1)⁻¹ : ℂ) • G.rawAtom m hm x.1 x.2

/-- Exact conversion to the existing normalized Dirac atoms. Each point's
norm must be restored before applying the one-chain normalization. -/
theorem atom_eq_sum_normalized (m : ℕ) (hm : 1 ≤ m) (C : κ) (j : Fin (G.size C)) :
    G.atom m hm ⟨C, j⟩ = ∑ i,
      ((G.weight m hm C)⁻¹ * groupedNewtonWeight (G.nodes C) j i *
        (‖hermitePointMass m hm (G.point C i)‖ : ℂ)) •
          normalizedHermitePointMass m hm (G.point C i) := by
  simp only [atom, rawAtom, groupedFiniteAtom, Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro i _
  have hne : (‖hermitePointMass m hm (G.point C i)‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hermitePointMass_ne_zero m hm _))
  simp only [normalizedHermitePointMass, Complex.ofReal_inv, smul_smul]
  congr 1
  field_simp

/-- On every Schwartz test, grouped realization is precisely the initial
divided difference of the physical test values, divided by the chain norm. -/
theorem atom_distribution_apply (m : ℕ) (hm : 1 ≤ m) (C : κ) (j : Fin (G.size C))
    (f : SchwartzMap ℝ ℂ) :
    hermiteScaleDistribution m (G.atom m hm ⟨C, j⟩) f =
      (G.weight m hm C)⁻¹ * dividedDifferences (G.nodes C) (G.nodes_injective C)
        (fun i => f (G.point C i)) j := by
  rw [dividedDifferences_eq_groupedNewtonWeights]
  change (hermiteScaleDistributionCLM m (G.atom m hm ⟨C, j⟩)) f = _
  simp only [atom, rawAtom, groupedFiniteAtom, map_smul, map_sum,
    _root_.sum_apply, smul_apply, smul_eq_mul, hermiteScaleDistributionCLM_apply,
    hermitePointMass_represents_delta, pointMass_apply, Complex.ofReal_inv]

/-- On each actual finite cluster, normalized grouped and normalized point
atoms generate exactly the same algebraic span. -/
theorem atom_cluster_span (m : ℕ) (hm : 1 ≤ m) (C : κ) :
    Submodule.span ℂ (Set.range (fun j => G.atom m hm ⟨C, j⟩)) =
      Submodule.span ℂ (Set.range (fun i : Fin (G.size C) =>
        normalizedHermitePointMass m hm (G.point C i))) := by
  rw [show (fun j => G.atom m hm ⟨C, j⟩) =
      (fun j => ((G.weight m hm C)⁻¹ : ℂ) • G.rawAtom m hm C j) from rfl]
  rw [span_range_nonzero_smul _ _ (fun _ => by
    exact inv_ne_zero (Complex.ofReal_ne_zero.mpr (G.weight_pos m hm C).ne'))]
  change Submodule.span ℂ (Set.range (groupedFiniteAtom (G.nodes C)
    (fun i => hermitePointMass m hm (G.point C i)))) = _
  rw [groupedFiniteAtom_span (G.nodes C) (G.nodes_injective C)]
  symm
  exact span_range_nonzero_smul _ _ (fun i =>
    Complex.ofReal_ne_zero.mpr (inv_ne_zero
      (norm_ne_zero_iff.mpr (hermitePointMass_ne_zero m hm (G.point C i)))))

/-- Exact finite synthesis range equality includes the source chain weights;
it does not require independent Dirac vectors or an infinite synthesis bound. -/
theorem atom_cluster_synthesis_range (m : ℕ) (hm : 1 ≤ m) (C : κ) :
    (Fintype.linearCombination ℂ (fun j => G.atom m hm ⟨C, j⟩)).range =
      (Fintype.linearCombination ℂ (fun i : Fin (G.size C) =>
        normalizedHermitePointMass m hm (G.point C i))).range := by
  rw [Fintype.range_linearCombination, Fintype.range_linearCombination]
  exact G.atom_cluster_span m hm C

/-- The full grouped family has exactly the point family's algebraic span;
this uses the actual one-time carrier coverage and the proved cluster spans. -/
theorem atom_span (m : ℕ) (hm : 1 ≤ m) :
    Submodule.span ℂ (Set.range (G.atom m hm)) =
      Submodule.span ℂ (Set.range (locallyFiniteCarrierHermitePointMass m hm S)) := by
  have hrange : Set.range (fun x : G.Index =>
      normalizedHermitePointMass m hm (G.point x.1 x.2)) =
      Set.range (locallyFiniteCarrierHermitePointMass m hm S) := by
    ext u
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨G.point x.1 x.2, rfl⟩
    · rintro ⟨x, rfl⟩
      obtain ⟨y, hy⟩ := G.bijective.surjective x
      exact ⟨y, congrArg (locallyFiniteCarrierHermitePointMass m hm S) hy⟩
  calc
    _ = ⨆ C : κ, Submodule.span ℂ (Set.range (fun j => G.atom m hm ⟨C, j⟩)) := by
      rw [Set.range_sigma_eq_iUnion_range, Submodule.span_iUnion]
    _ = ⨆ C : κ, Submodule.span ℂ (Set.range (fun i : Fin (G.size C) =>
        normalizedHermitePointMass m hm (G.point C i))) := by
      congr 1
      funext C
      exact G.atom_cluster_span m hm C
    _ = Submodule.span ℂ (Set.range (fun x : G.Index =>
        normalizedHermitePointMass m hm (G.point x.1 x.2))) := by
      rw [Set.range_sigma_eq_iUnion_range, Submodule.span_iUnion]
    _ = _ := congrArg (Submodule.span ℂ) hrange

/-- Closure preserves exact span equality without any Bessel or lower-Gram
assumption. Thus grouped traces generate the genuine intrinsic support. -/
theorem atom_closedSpan (m : ℕ) (hm : 1 ≤ m) :
    atomicSupportSubspace (G.atom m hm) = (fixedOrderPhysicalSupport S m hm).toSubmodule := by
  unfold atomicSupportSubspace
  rw [G.atom_span m hm]
  exact locallyFiniteAtomicSupportSubspace_eq_supportedHermiteMeasureSubspace m hm S

/-- A grouped trace presentation is constructed only after supplying genuine
infinite Bessel data and a strictly positive actual Gram. Its range equality
is proved from the source-ranged finite algebra, not included as an assumption. -/
def tracePresentation (m : ℕ) (hm : 1 ≤ m) (B : BesselAnalysis (G.atom m hm))
    (hG : IsStrictlyPositive (coefficientGram B.synthesis)) :
    TracePresentation (fixedOrderPhysicalSupport S m hm) G.Index := by
  classical
  refine { system := ⟨G.atom m hm, B⟩
           gram_strictlyPositive := hG
           synthesis_range_eq := ?_ }
  change B.synthesis.range = _
  rw [synthesis_range_eq_atomicSupportSubspace B.synthesis hG]
  have heq : (fun i : G.Index => B.synthesis (coefficientAtom i)) = G.atom m hm :=
    funext B.synthesis_coefficientAtom
  rw [heq, G.atom_closedSpan m hm]

end OrderedCarrierGrouping

/-- A repeated-node jet trace is a derivative evaluation with its exact
factorial normalization. It is not a combination of coincident raw Diracs. -/
def groupedJetTrace (a : ℝ) (order : ℕ) (f : SchwartzMap ℝ ℂ) : ℂ :=
  (1 / (order.factorial : ℝ)) • iteratedDeriv order (fun x => f x) a

/-- The analytic compactification at a fully repeated signed-square node
uses derivative jets, separately from the actual distinct-node atoms. -/
theorem analyticGroupedTrace_repeated_node (a : ℝ) (order : ℕ)
    (f : SchwartzMap ℝ ℂ) :
    analyticDividedDifference (fun _ => a) order (fun x => f x) =
      groupedJetTrace a order f :=
  analyticDividedDifference_repeated_node_of_contDiff a order (f.smooth _)

/-- Analytic trace values are jointly continuous through node collisions.
This does not assert Hilbert-valued differentiability of the Dirac family. -/
theorem continuous_analyticGroupedTrace_nodes (order : ℕ) (f : SchwartzMap ℝ ℂ) :
    Continuous (fun nodes : Fin (order + 1) → ℝ =>
      analyticDividedDifference (finiteNodeSequence nodes) order (fun x => f x)) :=
  continuous_analyticDividedDifference_nodes order (f.smooth _)

end

end MeyerGeneralProblem
