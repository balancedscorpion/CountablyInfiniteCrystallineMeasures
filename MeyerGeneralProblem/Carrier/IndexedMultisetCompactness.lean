module

public import MeyerGeneralProblem.Carrier.TwoSided
public import MeyerGeneralProblem.Carrier.LocallyFinite
public import Mathlib.Topology.Sequences
import all Mathlib.Topology.Sequences
public import Mathlib.Topology.Instances.Real.Lemmas
import all Mathlib.Topology.Instances.Real.Lemmas

@[expose] public section

/-!
# Compactness of geometrically controlled indexed multisets

Integer indices are retained when coordinates collide. The input consists of
concrete order, anchor, adjacent-gap and q-step separation inequalities; it does
not assert sampling, uniqueness, or a compactness conclusion.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace MeyerGeneralProblem

/-- Concrete geometry of an anchored ordered multiset. The sequence may have
repeated entries, but a positive q-step separation bounds every multiplicity. -/
structure IndexedMultisetGeometry (q : ℕ) (d H : ℝ) (s : ℤ → ℝ) : Prop where
  /-- Coordinates respect the integer order. -/
  monotone : Monotone s
  /-- The index immediately before zero lies on the nonpositive side. -/
  anchor_neg : s (-1) ≤ 0
  /-- The zero index lies on the nonnegative side. -/
  anchor_pos : 0 ≤ s 0
  /-- Adjacent coordinates have a common upper gap. -/
  adjacent : ∀ j, s (j + 1) ≤ s j + H
  /-- Every q-step span has the stated positive lower bound. -/
  separated : ∀ j, d ≤ s (j + q) - s j

namespace IndexedMultisetGeometry

variable {q : ℕ} {d H : ℝ} {s : ℤ → ℝ}

/-- Monotonicity and the adjacent upper bound force `H` to be nonnegative. -/
theorem upperGap_nonneg (h : IndexedMultisetGeometry q d H s) : 0 ≤ H := by
  have := h.monotone (show (0 : ℤ) ≤ 0 + 1 by omega)
  have := h.adjacent 0
  linarith

/-- Iterating the adjacent-gap inequality gives an explicit upper displacement. -/
theorem add_nat_upper (h : IndexedMultisetGeometry q d H s) (i : ℤ) (n : ℕ) :
    s (i + n) ≤ s i + n * H := by
  induction n with
  | zero => simp
  | succ n ih =>
    have := h.adjacent (i + n)
    simp only [Nat.cast_add, Nat.cast_one, ← add_assoc]
    nlinarith

/-- Iterating the q-step separation gives a uniform lower displacement. -/
theorem add_mul_lower (h : IndexedMultisetGeometry q d H s) (i : ℤ) (n : ℕ) :
    s i + n * d ≤ s (i + n * q) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have := h.separated (i + n * q)
    push_cast
    have heq : i + (n + 1 : ℤ) * q = i + n * q + q := by ring
    rw [heq]
    nlinarith

/-- Each indexed coordinate lies in a compact interval independent of the
particular sequence having this geometry. -/
theorem coordinate_abs_le (h : IndexedMultisetGeometry q d H s) (j : ℤ) :
    |s j| ≤ (j.natAbs + 1 : ℝ) * H := by
  have hH := h.upperGap_nonneg
  have h0 : s 0 ≤ H := by
    have := h.adjacent (-1)
    simp only [neg_add_cancel] at this
    linarith [h.anchor_neg]
  cases j with
  | ofNat n =>
    have hl := h.monotone (show (0 : ℤ) ≤ n by omega)
    have hu := h.add_nat_upper 0 n
    simp only [zero_add] at hu
    change |s (n : ℤ)| ≤ ((n : ℝ) + 1) * H
    rw [abs_le]
    constructor <;> nlinarith [h.anchor_pos]
  | negSucc n =>
    have hu := h.monotone (show Int.negSucc n ≤ -1 by omega)
    have hl := h.add_nat_upper (Int.negSucc n) (n + 1)
    have hz : Int.negSucc n + (n + 1 : ℕ) = 0 := by omega
    rw [hz] at hl
    simp only [Int.natAbs_negSucc, Nat.cast_succ]
    rw [abs_le]
    push_cast at hl
    constructor <;> nlinarith [h.anchor_pos, h.anchor_neg]

/-- A fixed spatial window contains only indices in one explicit common finite
integer interval, uniformly over all sequences with the same geometry. -/
theorem index_localization (h : IndexedMultisetGeometry q d H s) {N : ℕ} {R : ℝ}
    (hNR : R < N * d) {j : ℤ} (hj : |s j| ≤ R) :
    -(N * q : ℤ) ≤ j ∧ j ≤ N * q := by
  have hlower := h.add_mul_lower 0 N
  simp only [zero_add] at hlower
  have hupper := h.add_mul_lower (-1 - N * q) N
  have heq : (-1 - (N : ℤ) * q) + N * q = -1 := by ring
  rw [heq] at hupper
  have hbounds := abs_le.mp hj
  constructor
  · by_contra hneg
    have hjle : j ≤ -1 - (N : ℤ) * q := by omega
    have := h.monotone hjle
    linarith [h.anchor_neg]
  · by_contra hpos
    have hjge : (N : ℤ) * q ≤ j := by omega
    have := h.monotone hjge
    linarith [h.anchor_pos]

/-- Positive q-step separation makes every bounded coordinate preimage finite. -/
theorem finite_indices_abs_le (h : IndexedMultisetGeometry q d H s) (hd : 0 < d) (R : ℝ) :
    {j : ℤ | |s j| ≤ R}.Finite := by
  obtain ⟨N, hN⟩ := exists_nat_gt (R / d)
  have hNR : R < N * d := (div_lt_iff₀ hd).mp hN
  exact (Set.finite_Icc (-(N * q : ℤ)) (N * q)).subset
    (fun j hj => h.index_localization hNR hj)

/-- All the geometric inequalities survive pointwise convergence. -/
theorem of_pointwise_tendsto {S : ℕ → ℤ → ℝ}
    (hS : ∀ n, IndexedMultisetGeometry q d H (S n))
    (hconv : ∀ j, Tendsto (fun n => S n j) atTop (𝓝 (s j))) :
    IndexedMultisetGeometry q d H s := by
  constructor
  · intro i j hij
    exact le_of_tendsto_of_tendsto (hconv i) (hconv j)
      (Eventually.of_forall fun n => (hS n).monotone hij)
  · exact le_of_tendsto (hconv (-1)) (Eventually.of_forall fun n => (hS n).anchor_neg)
  · exact ge_of_tendsto (hconv 0) (Eventually.of_forall fun n => (hS n).anchor_pos)
  · intro j
    exact le_of_tendsto_of_tendsto (hconv (j + 1)) ((hconv j).add_const H)
      (Eventually.of_forall fun n => (hS n).adjacent j)
  · intro j
    exact ge_of_tendsto ((hconv (j + q)).sub (hconv j))
      (Eventually.of_forall fun n => (hS n).separated j)

end IndexedMultisetGeometry

/-- The genuine multiplicity of a coordinate, counted by its integer-index
fiber. Under positive q-step geometry this fiber is finite and has size at most q. -/
noncomputable def indexedMultisetMultiplicity (s : ℤ → ℝ) (x : ℝ) : ℕ :=
  Set.ncard {j | s j = x}

namespace IndexedMultisetGeometry

variable {q : ℕ} {d H : ℝ} {s : ℤ → ℝ}

/-- Every index fiber is finite under positive q-step separation. -/
theorem finite_fiber (h : IndexedMultisetGeometry q d H s) (hd : 0 < d) (x : ℝ) :
    {j | s j = x}.Finite := by
  apply (h.finite_indices_abs_le hd |x|).subset
  intro j hj
  change s j = x at hj
  change |s j| ≤ |x|
  rw [hj]

/-- The actual range of the indexed multiset is a locally finite real carrier. -/
noncomputable def toLocallyFiniteCarrier (h : IndexedMultisetGeometry q d H s) (hd : 0 < d) :
    LocallyFiniteCarrier where
  carrier := Set.range s
  finite_inter_Icc a b := by
    apply ((h.finite_indices_abs_le hd (max |a| |b|)).image s).subset
    rintro x ⟨⟨j, rfl⟩, hlo, hhi⟩
    refine ⟨j, ?_, rfl⟩
    change |s j| ≤ max |a| |b|
    apply abs_le.mpr
    exact ⟨(neg_le_neg (le_max_left _ _)).trans ((neg_abs_le a).trans hlo),
      hhi.trans ((le_abs_self b).trans (le_max_right _ _))⟩

/-- The range carrier is exactly the range, without dropping repeated-index
information from the separately retained multiplicity. -/
@[simp] theorem mem_toLocallyFiniteCarrier
    (h : IndexedMultisetGeometry q d H s) (hd : 0 < d) (x : ℝ) :
    x ∈ (h.toLocallyFiniteCarrier hd).carrier ↔ ∃ j, s j = x := Iff.rfl

/-- A fiber contains at most q indices; hence collisions cannot create an
uncontrolled multiplicity. -/
theorem multiplicity_le (h : IndexedMultisetGeometry q d H s) (hd : 0 < d) (x : ℝ) :
    indexedMultisetMultiplicity s x ≤ q := by
  classical
  have hf := h.finite_fiber hd x
  let T := hf.toFinset
  have hmem {j : ℤ} : j ∈ T ↔ s j = x := by simp [T]
  rw [indexedMultisetMultiplicity, Set.ncard_eq_toFinset_card _ hf]
  change T.card ≤ q
  by_cases hne : T.Nonempty
  · let i := T.min' hne
    have hi : i ∈ T := Finset.min'_mem T hne
    have hsubset : T ⊆ Finset.Ico i (i + q) := by
      intro j hj
      refine Finset.mem_Ico.mpr ⟨T.min'_le j hj, ?_⟩
      by_contra hjlt
      have horder := h.monotone (le_of_not_gt hjlt)
      have hsep := h.separated i
      rw [hmem.mp hj] at horder
      rw [hmem.mp hi] at hsep
      linarith
    have hcard := Finset.card_le_card hsubset
    simpa [Int.card_Ico] using hcard
  · simp [Finset.not_nonempty_iff_eq_empty.mp hne]

end IndexedMultisetGeometry

/-- One subsequence converges at every integer coordinate and stabilizes every
Boolean group-boundary coordinate. The limit retains the concrete geometry. -/
theorem exists_indexedMultiset_subsequence
    {q : ℕ} {d H : ℝ} (S : ℕ → ℤ → ℝ) (B : ℕ → ℤ → Bool)
    (hS : ∀ n, IndexedMultisetGeometry q d H (S n)) :
    ∃ (φ : ℕ → ℕ) (s : ℤ → ℝ) (b : ℤ → Bool), StrictMono φ ∧
      (∀ j, Tendsto (fun n => S (φ n) j) atTop (𝓝 (s j))) ∧
      (∀ j, ∀ᶠ n in atTop, B (φ n) j = b j) ∧
      IndexedMultisetGeometry q d H s := by
  let K : ℤ → Set (ℝ × Bool) := fun j =>
    Icc (-((j.natAbs + 1 : ℝ) * H)) ((j.natAbs + 1 : ℝ) * H) ×ˢ univ
  have hK : IsCompact {p : ℤ → ℝ × Bool | ∀ j, p j ∈ K j} :=
    isCompact_pi_infinite (fun _ => isCompact_Icc.prod isCompact_univ)
  obtain ⟨p, _, φ, hφ, hconv⟩ := hK.tendsto_subseq
    (x := fun n j => (S n j, B n j)) (fun n j =>
      ⟨abs_le.mp ((hS n).coordinate_abs_le j), mem_univ _⟩)
  have hcoords (j : ℤ) : Tendsto (fun n => S (φ n) j) atTop (𝓝 (p j).1) :=
    (continuous_fst.tendsto (p j)).comp (hconv.apply_nhds j)
  have hbits (j : ℤ) : ∀ᶠ n in atTop, B (φ n) j = (p j).2 := by
    have ht : Tendsto (fun n => B (φ n) j) atTop (𝓝 (p j).2) :=
      (continuous_snd.tendsto (p j)).comp (hconv.apply_nhds j)
    rw [nhds_discrete Bool, tendsto_pure] at ht
    exact ht
  exact ⟨φ, fun j => (p j).1, fun j => (p j).2, hφ, hcoords, hbits,
    IndexedMultisetGeometry.of_pointwise_tendsto (fun n => hS (φ n)) hcoords⟩

/-- Pointwise stabilization of boundary bits stabilizes every finite local
boundary pattern along the same subsequence. -/
theorem eventually_indexedMultiset_boundary_pattern
    {B : ℕ → ℤ → Bool} {b : ℤ → Bool}
    (hB : ∀ j, ∀ᶠ n in atTop, B n j = b j) (I : Finset ℤ) :
    ∀ᶠ n in atTop, ∀ j ∈ I, B n j = b j :=
  (eventually_all_finset I).mpr (fun j _ => hB j)

/-- Real separation across any declared boundary between two indexed nodes.
This records actual source-group ancestry, separately from q-step geometry. -/
def IndexedGroupSeparation (s : ℤ → ℝ) (b : ℤ → Bool) (d : ℝ) : Prop :=
  ∀ i j : ℤ, (∃ k, i < k ∧ k ≤ j ∧ b k = true) → d ≤ s j - s i

/-- Actual separation across source-group boundaries survives the simultaneous
coordinate and boundary-pattern extraction. -/
theorem indexedGroupSeparation_of_pointwise_tendsto
    {S : ℕ → ℤ → ℝ} {B : ℕ → ℤ → Bool} {s : ℤ → ℝ} {b : ℤ → Bool} {d : ℝ}
    (hS : ∀ n, IndexedGroupSeparation (S n) (B n) d)
    (hcoords : ∀ j, Tendsto (fun n => S n j) atTop (𝓝 (s j)))
    (hbits : ∀ j, ∀ᶠ n in atTop, B n j = b j) : IndexedGroupSeparation s b d := by
  intro i j hboundary
  obtain ⟨k, hik, hkj, hbk⟩ := hboundary
  apply ge_of_tendsto ((hcoords j).sub (hcoords i))
  filter_upwards [hbits k] with n hn
  exact hS n i j ⟨k, hik, hkj, hn.trans hbk⟩

/-- Colliding limit coordinates cannot have a source-group boundary between
their indices. This conclusion does not infer any jet from point values. -/
theorem no_boundary_between_equal_coordinates
    {s : ℤ → ℝ} {b : ℤ → Bool} {d : ℝ}
    (hsep : IndexedGroupSeparation s b d) (hd : 0 < d) {i j : ℤ} (heq : s i = s j) :
    ¬ ∃ k, i < k ∧ k ≤ j ∧ b k = true := by
  intro hb
  have := hsep i j hb
  rw [heq, sub_self] at this
  linarith

/-- The existence of a source boundary in every q-index block survives
pointwise stabilization of the Boolean coordinates. -/
theorem indexed_boundary_every_q_steps_of_eventual_eq
    {B : ℕ → ℤ → Bool} {b : ℤ → Bool} {q : ℕ}
    (hB : ∀ j, ∀ᶠ n in atTop, B n j = b j)
    (hblocks : ∀ (n : ℕ) (i : ℤ), ∃ k ∈ Finset.Ioc i (i + q), B n k = true) (i : ℤ) :
    ∃ k ∈ Finset.Ioc i (i + q), b k = true := by
  obtain ⟨n, hn⟩ := (eventually_indexedMultiset_boundary_pattern hB
    (Finset.Ioc i (i + q))).exists
  obtain ⟨k, hk, hBk⟩ := hblocks n i
  exact ⟨k, hk, (hn k hk).symm.trans hBk⟩

/-- Equal limit coordinates belong to one source group eventually, using the
retained finite Boolean boundary pattern, not a raw point-value argument. -/
theorem eventually_no_source_boundary_of_equal_coordinates
    {B : ℕ → ℤ → Bool} {b : ℤ → Bool} {s : ℤ → ℝ} {d : ℝ}
    (hB : ∀ j, ∀ᶠ n in atTop, B n j = b j)
    (hsep : IndexedGroupSeparation s b d) (hd : 0 < d) {i j : ℤ} (heq : s i = s j) :
    ∀ᶠ n in atTop, ¬ ∃ k, i < k ∧ k ≤ j ∧ B n k = true := by
  filter_upwards [eventually_indexedMultiset_boundary_pattern hB (Finset.Ioc i j)] with n hn
  rintro ⟨k, hik, hkj, hk⟩
  exact no_boundary_between_equal_coordinates hsep hd heq
    ⟨k, hik, hkj, (hn k (Finset.mem_Ioc.mpr ⟨hik, hkj⟩)).symm.trans hk⟩

end MeyerGeneralProblem
