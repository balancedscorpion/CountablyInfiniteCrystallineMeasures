module

public import MeyerGeneralProblem.Carrier.IndexedMultisetCompactness
public import MeyerGeneralProblem.Carrier.ClusterDecomposition
public import MeyerGeneralProblem.Sampling.BernsteinZeroDensity
public import Mathlib.Data.Int.LeastGreatest
import all Mathlib.Data.Int.LeastGreatest

@[expose] public section

/-!
# Exact multiset counts and their preservation under extraction

Index fibers recover the multiplicity-weighted carrier count exactly. Finite
index localization ensures that source-window witnesses cannot escape through
the integer index when the real coordinates converge.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace MeyerGeneralProblem

/-- The actual number of integer indices whose coordinates lie in `(a,b)`. -/
noncomputable def indexedMultisetIntervalCount (s : ℤ → ℝ) (a b : ℝ) : ℕ :=
  Set.ncard {j | a < s j ∧ s j < b}

/-- Every bounded open spatial window contains only finitely many indices. -/
theorem IndexedMultisetGeometry.finite_indices_Ioo
    {q : ℕ} {d H : ℝ} {s : ℤ → ℝ}
    (h : IndexedMultisetGeometry q d H s) (hd : 0 < d) (a b : ℝ) :
    {j | a < s j ∧ s j < b}.Finite := by
  apply (h.finite_indices_abs_le hd (max |a| |b|)).subset
  intro j hj
  change a < s j ∧ s j < b at hj
  change |s j| ≤ max |a| |b|
  exact abs_le.mpr
    ⟨(neg_le_neg (le_max_left _ _)).trans ((neg_abs_le a).trans hj.1.le),
      hj.2.le.trans ((le_abs_self b).trans (le_max_right _ _))⟩

/-- Counting the integer indices equals counting the support points with their
actual index-fiber multiplicities. This identity retains collisions exactly. -/
theorem indexedMultisetIntervalCount_eq_weightedRealZeroCount
    {q : ℕ} {d H : ℝ} {s : ℤ → ℝ}
    (h : IndexedMultisetGeometry q d H s) (hd : 0 < d) (R : ℝ) :
    indexedMultisetIntervalCount s (-R) R =
      weightedRealZeroCount (h.toLocallyFiniteCarrier hd) (indexedMultisetMultiplicity s) R := by
  classical
  let I := (h.finite_indices_Ioo hd (-R) R).toFinset
  let V := ((h.toLocallyFiniteCarrier hd).finite_inter_Ioo (-R) R).toFinset
  have hI {j : ℤ} : j ∈ I ↔ -R < s j ∧ s j < R := by simp [I]
  have hV {x : ℝ} : x ∈ V ↔ (∃ j, s j = x) ∧ -R < x ∧ x < R := by simp [V]
  have hmap : (I : Set ℤ).MapsTo s V := by
    intro j hj
    exact hV.mpr ⟨⟨j, rfl⟩, hI.mp hj⟩
  change {j | -R < s j ∧ s j < R}.ncard = ∑ x ∈ V, indexedMultisetMultiplicity s x
  rw [Set.ncard_eq_toFinset_card _ (h.finite_indices_Ioo hd (-R) R)]
  change I.card = _
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  apply Finset.sum_congr rfl
  intro x hx
  rw [indexedMultisetMultiplicity, Set.ncard_eq_toFinset_card _ (h.finite_fiber hd x)]
  congr 1
  ext j
  simp only [Finset.mem_filter, hI, Set.Finite.mem_toFinset, mem_ofPred_eq]
  exact ⟨fun hj => hj.2, fun hj => ⟨by simpa only [hj] using (hV.mp hx).2, hj⟩⟩

/-- With positive spatial slack, every source index in the smaller window
belongs to the limit window eventually. Uniform index localization is essential
here: the witnesses cannot drift to unbounded integer indices. -/
theorem eventually_indexedMultiset_window_subset
    {q : ℕ} {d H : ℝ} {S : ℕ → ℤ → ℝ} {s : ℤ → ℝ}
    (hS : ∀ n, IndexedMultisetGeometry q d H (S n)) (hd : 0 < d)
    (hconv : ∀ j, Tendsto (fun n => S n j) atTop (𝓝 (s j)))
    (a b : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      {j | a + ε < S n j ∧ S n j < b - ε} ⊆ {j | a < s j ∧ s j < b} := by
  classical
  let R := max |a + ε| |b - ε|
  obtain ⟨N, hN⟩ := exists_nat_gt (R / d)
  have hNR : R < N * d := (div_lt_iff₀ hd).mp hN
  let I : Finset ℤ := Finset.Icc (-(N * q : ℤ)) (N * q)
  have hlocal : ∀ j ∈ I, ∀ᶠ n in atTop,
      (a + ε < S n j ∧ S n j < b - ε) → a < s j ∧ s j < b := by
    intro j _
    by_cases hj : a < s j ∧ s j < b
    · exact Eventually.of_forall (fun _ _ => hj)
    · by_cases hlo : a < s j
      · have hb : b ≤ s j := le_of_not_gt (fun hhi => hj ⟨hlo, hhi⟩)
        have hevent : ∀ᶠ n in atTop, b - ε < S n j :=
          (hconv j).eventually (Ioi_mem_nhds (by linarith))
        filter_upwards [hevent] with n hn
        intro hwindow
        linarith [hwindow.2]
      · have ha : s j ≤ a := le_of_not_gt hlo
        have hevent : ∀ᶠ n in atTop, S n j < a + ε :=
          (hconv j).eventually (Iio_mem_nhds (by linarith))
        filter_upwards [hevent] with n hn
        intro hwindow
        linarith [hwindow.1]
  filter_upwards [(eventually_all_finset I).mpr hlocal] with n hn
  intro j hj
  change a + ε < S n j ∧ S n j < b - ε at hj
  have hjR : |S n j| ≤ R := abs_le.mpr
    ⟨(neg_le_neg (le_max_left _ _)).trans ((neg_abs_le _).trans hj.1.le),
      hj.2.le.trans ((le_abs_self _).trans (le_max_right _ _))⟩
  have hjI : j ∈ I := Finset.mem_Icc.mpr ((hS n).index_localization hNR hjR)
  exact hn j hjI hj

/-- The genuine source-window count is eventually bounded by the genuine limit
count in every positively enlarged window. -/
theorem eventually_indexedMultisetIntervalCount_le
    {q : ℕ} {d H : ℝ} {S : ℕ → ℤ → ℝ} {s : ℤ → ℝ}
    (hS : ∀ n, IndexedMultisetGeometry q d H (S n)) (hd : 0 < d)
    (hconv : ∀ j, Tendsto (fun n => S n j) atTop (𝓝 (s j)))
    (a b : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, indexedMultisetIntervalCount (S n) (a + ε) (b - ε) ≤
      indexedMultisetIntervalCount s a b := by
  have hlim := IndexedMultisetGeometry.of_pointwise_tendsto hS hconv
  filter_upwards [eventually_indexedMultiset_window_subset hS hd hconv a b hε] with n hn
  exact Set.ncard_le_ncard hn (hlim.finite_indices_Ioo hd a b)

/-- A strict radial density margin survives extraction as an actual weighted
carrier count. A one-unit endpoint slack is absorbed by any smaller density
coefficient, uniformly for all sufficiently large radii. -/
theorem weightedRealZeroCount_lower_of_pointwise_tendsto
    {q : ℕ} {d H ρ ρ' r₀ : ℝ} {S : ℕ → ℤ → ℝ} {s : ℤ → ℝ}
    (hS : ∀ n, IndexedMultisetGeometry q d H (S n))
    (hs : IndexedMultisetGeometry q d H s) (hd : 0 < d)
    (hconv : ∀ j, Tendsto (fun n => S n j) atTop (𝓝 (s j)))
    (hρ : ρ' < ρ) (hr₀ : 0 < r₀)
    (hcounts : ∀ n R, r₀ ≤ R →
      2 * ρ * R ≤ (indexedMultisetIntervalCount (S n) (-R) R : ℝ)) :
    ∃ r₁ > 0, ∀ R ≥ r₁,
      2 * ρ' * R ≤ (weightedRealZeroCount (hs.toLocallyFiniteCarrier hd)
        (indexedMultisetMultiplicity s) R : ℝ) := by
  refine ⟨max (r₀ + 1) (ρ / (ρ - ρ') + 1),
    lt_of_lt_of_le (by linarith) (le_max_left _ _), ?_⟩
  intro R hR
  have hRr : r₀ + 1 ≤ R := (le_max_left _ _).trans hR
  have hRρ : ρ / (ρ - ρ') + 1 ≤ R := (le_max_right _ _).trans hR
  have hmargin : ρ ≤ (ρ - ρ') * R := by
    have := (div_le_iff₀ (sub_pos.mpr hρ)).mp
      (show ρ / (ρ - ρ') ≤ R by linarith)
    nlinarith
  obtain ⟨n, hn⟩ := (eventually_indexedMultisetIntervalCount_le hS hd hconv
    (-R) R (show (0 : ℝ) < 1 by norm_num)).exists
  have hstart : -R + 1 = -(R - 1) := by ring
  rw [hstart, indexedMultisetIntervalCount_eq_weightedRealZeroCount hs hd R] at hn
  have hsrc := hcounts n (R - 1) (by linarith)
  have hcast : (indexedMultisetIntervalCount (S n) (-(R - 1)) (R - 1) : ℝ) ≤
      (weightedRealZeroCount (hs.toLocallyFiniteCarrier hd)
        (indexedMultisetMultiplicity s) R : ℝ) := by exact_mod_cast hn
  nlinarith

/-- Bounded cluster order for an actual ordered carrier implies the closed
q-step span bound; no minimum gap between individual nodes is imposed. -/
theorem TwoSidedCarrier.qstep_separated_of_boundedClusterOrder
    (Λ : TwoSidedCarrier) {d : ℝ} {q : ℕ}
    (hcluster : BoundedClusterOrder Λ.toLocallyFinite d q) (j : ℤ) :
    d ≤ Λ (j + q) - Λ j := by
  by_contra hspan
  have hspan' : Λ (j + q) - Λ j < d := lt_of_not_ge hspan
  let x : Fin (q + 1) → ℝ := fun i => Λ (j + i.val)
  have hxmono : StrictMono x := by
    intro i k hik
    exact Λ.strictMono (by omega)
  have hxmem : ∀ i, x i ∈ Λ.toLocallyFinite.carrier :=
    fun i => ⟨j + i.val, rfl⟩
  have hlo (i : Fin (q + 1)) : Λ j ≤ x i := Λ.strictMono.monotone (by omega)
  have hhi (i : Fin (q + 1)) : x i ≤ Λ (j + q) := Λ.strictMono.monotone (by omega)
  have hshort : ∀ i : Fin q, x i.succ - x i.castSucc < d := by
    intro i
    have := hlo i.castSucc
    have := hhi i.succ
    linarith
  have := hcluster q x hxmono hxmem hshort
  omega

/-- Positive lower uniform density gives a common adjacent-gap upper bound for
the actual ordered carrier, rather than assuming that bound in the extraction. -/
theorem TwoSidedCarrier.exists_adjacent_upper_of_uniformLowerDensityGT
    (Λ : TwoSidedCarrier) {c : ℝ} (hc : 0 ≤ c)
    (hD : UniformLowerDensityGT Λ.toLocallyFinite c) :
    ∃ H > 0, ∀ j, Λ (j + 1) ≤ Λ j + H := by
  obtain ⟨ε, hε, H, hH, hbound⟩ := hD
  refine ⟨H, hH, ?_⟩
  intro j
  by_contra hgap
  have hgap' : Λ j + H < Λ (j + 1) := lt_of_not_ge hgap
  have hgapPoint : Λ.point j + H < Λ.point (j + 1) := hgap'
  let a := (Λ j + Λ (j + 1) - H) / 2
  have hzero : windowCount Λ.toLocallyFinite a H = 0 := by
    apply (Λ.toLocallyFinite.windowCount_eq_zero_iff a H).mpr
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro x ⟨⟨k, rfl⟩, hlo, hhi⟩
    have hjk : j < k := Λ.strictMono.lt_iff_lt.mp (by dsimp [a] at hlo; linarith)
    have hkj : k < j + 1 := Λ.strictMono.lt_iff_lt.mp (by dsimp [a] at hhi; linarith)
    omega
  have h := hbound H le_rfl a
  rw [hzero, Nat.cast_zero] at h
  have hpos := mul_pos (add_pos_of_nonneg_of_pos hc hε) hH
  linarith

/-- Every real translation has an integer reindexing whose zero coordinate
straddles the origin. This uses both genuine escaping tails of the carrier. -/
theorem TwoSidedCarrier.exists_straddling_index (Λ : TwoSidedCarrier) (t : ℝ) :
    ∃ k : ℤ, Λ (k - 1) ≤ t ∧ t ≤ Λ k := by
  obtain ⟨lo, hlo⟩ := (Λ.eventually_point_le (t - 1)).exists
  obtain ⟨hi, hhi⟩ := (Λ.eventually_point_ge t).exists
  have hbdd : ∃ b : ℤ, ∀ j : ℤ, t ≤ Λ j → b ≤ j := by
    refine ⟨lo, ?_⟩
    intro j hj
    by_contra h
    have hm : Λ j ≤ Λ lo := Λ.strictMono.monotone (le_of_not_ge h)
    linarith
  obtain ⟨k, hk, hleast⟩ := Int.exists_least_of_bdd hbdd ⟨hi, hhi⟩
  refine ⟨k, ?_, hk⟩
  by_contra h
  have := hleast (k - 1) (le_of_not_ge h)
  omega

/-- The actual bounded-cluster and lower-density hypotheses produce uniform
geometry for every translated, reindexed carrier. Thus the compactness inputs
are derived for this concrete class rather than left as extra certificates. -/
theorem TwoSidedCarrier.exists_uniform_indexedMultisetGeometry
    (Λ : TwoSidedCarrier) {d c : ℝ} {q : ℕ} (hc : 0 ≤ c)
    (hcluster : BoundedClusterOrder Λ.toLocallyFinite d q)
    (hD : UniformLowerDensityGT Λ.toLocallyFinite c) :
    ∃ H > 0, ∀ t : ℝ, ∃ k : ℤ,
      IndexedMultisetGeometry q d H (fun j => Λ (j + k) - t) := by
  obtain ⟨H, hH, hupper⟩ := Λ.exists_adjacent_upper_of_uniformLowerDensityGT hc hD
  refine ⟨H, hH, ?_⟩
  intro t
  obtain ⟨k, hneg, hpos⟩ := Λ.exists_straddling_index t
  refine ⟨k, ?_⟩
  constructor
  · intro i j hij
    exact sub_le_sub_right (Λ.strictMono.monotone (by omega)) t
  · have heq : -1 + k = k - 1 := by omega
    rw [heq]
    linarith
  · simpa only [zero_add, sub_nonneg] using hpos
  · intro j
    have hu := hupper (j + k)
    have heq : j + 1 + k = j + k + 1 := by omega
    change Λ (j + 1 + k) - t ≤ (Λ (j + k) - t) + H
    rw [heq]
    linarith
  · intro j
    have hs := Λ.qstep_separated_of_boundedClusterOrder hcluster (j + k)
    have heq : j + (q : ℤ) + k = j + k + q := by omega
    change d ≤ (Λ (j + q + k) - t) - (Λ (j + k) - t)
    rw [heq]
    linarith

/-- Translation and integer reindexing identify actual index-window counts
with the original carrier's translated open-window count. -/
theorem TwoSidedCarrier.translated_indexedMultisetIntervalCount_eq_ncard
    (Λ : TwoSidedCarrier) (t : ℝ) (k : ℤ) (a b : ℝ) :
    indexedMultisetIntervalCount (fun j => Λ (j + k) - t) a b =
      (Λ.toLocallyFinite.carrier ∩ Ioo (a + t) (b + t)).ncard := by
  unfold indexedMultisetIntervalCount
  apply Set.ncard_congr (fun j _ => Λ (j + k))
  · intro j hj
    change a < Λ (j + k) - t ∧ Λ (j + k) - t < b at hj
    exact ⟨⟨j + k, rfl⟩, by linarith [hj.1], by linarith [hj.2]⟩
  · intro i j _ _ hij
    have := Λ.strictMono.injective hij
    omega
  · rintro x ⟨⟨j, rfl⟩, hlo, hhi⟩
    refine ⟨j - k, ?_, ?_⟩
    · change a < Λ (j - k + k) - t ∧ Λ (j - k + k) - t < b
      rw [sub_add_cancel]
      constructor <;> linarith
    · simp only [sub_add_cancel]

/-- The original lower uniform density yields a common strict radial count
for every translated and reindexed carrier. No count-preservation assumption
is left in this concrete source-class adapter. -/
theorem TwoSidedCarrier.exists_uniform_translated_radial_count
    (Λ : TwoSidedCarrier) {c : ℝ} (hD : UniformLowerDensityGT Λ.toLocallyFinite c) :
    ∃ ρ > c, ∃ r₀ > 0, ∀ (t : ℝ) (k : ℤ) (R : ℝ), r₀ ≤ R →
      2 * ρ * R ≤ (indexedMultisetIntervalCount (fun j => Λ (j + k) - t) (-R) R : ℝ) := by
  obtain ⟨ε, hε, L₀, hL₀, hbound⟩ := hD
  refine ⟨c + ε / 2, by linarith, max (L₀ + 2) (2 * (c + ε) / ε + 1),
    lt_of_lt_of_le (by linarith) (le_max_left _ _), ?_⟩
  intro t k R hR
  have hRL : L₀ + 2 ≤ R := (le_max_left _ _).trans hR
  have hRE : 2 * (c + ε) / ε + 1 ≤ R := (le_max_right _ _).trans hR
  have hεR : 2 * (c + ε) ≤ ε * R := by
    have := (div_le_iff₀ hε).mp (show 2 * (c + ε) / ε ≤ R by linarith)
    nlinarith
  rw [Λ.translated_indexedMultisetIntervalCount_eq_ncard t k (-R) R]
  have hsubset : Λ.toLocallyFinite.carrier ∩ Ico (-R + t + 1)
      (-R + t + 1 + (2 * R - 2)) ⊆
      Λ.toLocallyFinite.carrier ∩ Ioo (-R + t) (R + t) := by
    intro x hx
    exact ⟨hx.1, by linarith [hx.2.1], by linarith [hx.2.2]⟩
  have hcard := Set.ncard_le_ncard hsubset
    (Λ.toLocallyFinite.finite_inter_Ioo (-R + t) (R + t))
  have hcast : (windowCount Λ.toLocallyFinite (-R + t + 1) (2 * R - 2) : ℝ) ≤
      ((Λ.toLocallyFinite.carrier ∩ Ioo (-R + t) (R + t)).ncard : ℝ) := by
    exact_mod_cast hcard
  have hwindow := hbound (2 * R - 2) (by linarith) (-R + t + 1)
  nlinarith

/-- The actual chain boundary before index `j`: its preceding gap is at least
the cluster scale. Equality at the scale is a boundary, as in the source model. -/
noncomputable def TwoSidedCarrier.clusterBoundary (Λ : TwoSidedCarrier) (d : ℝ)
    (k j : ℤ) : Bool :=
  decide (d ≤ Λ (j + k) - Λ (j - 1 + k))

/-- Actual chain-boundary bits certify separation across distinct source
groups after every real translation and integer reindexing. -/
theorem TwoSidedCarrier.clusterBoundary_groupSeparation
    (Λ : TwoSidedCarrier) (d t : ℝ) (k : ℤ) :
    IndexedGroupSeparation (fun j => Λ (j + k) - t) (Λ.clusterBoundary d k) d := by
  rintro i j ⟨l, hil, hlj, hb⟩
  have hgap : d ≤ Λ (l + k) - Λ (l - 1 + k) := of_decide_eq_true hb
  have hlo : Λ (i + k) ≤ Λ (l - 1 + k) := Λ.strictMono.monotone (by omega)
  have hhi : Λ (l + k) ≤ Λ (j + k) := Λ.strictMono.monotone (by omega)
  change d ≤ (Λ (j + k) - t) - (Λ (i + k) - t)
  linarith

/-- Bounded cluster order forces an actual boundary in every q-index block.
These are the source-group bits retained by simultaneous extraction. -/
theorem TwoSidedCarrier.clusterBoundary_every_q_steps
    (Λ : TwoSidedCarrier) {d : ℝ} {q : ℕ}
    (hcluster : BoundedClusterOrder Λ.toLocallyFinite d q) (k i : ℤ) :
    ∃ j ∈ Finset.Ioc i (i + q), Λ.clusterBoundary d k j = true := by
  by_contra hnone
  let x : Fin (q + 1) → ℝ := fun j => Λ (i + j.val + k)
  have hxmono : StrictMono x := by
    intro a b hab
    exact Λ.strictMono (by omega)
  have hxmem : ∀ j, x j ∈ Λ.toLocallyFinite.carrier :=
    fun j => ⟨i + j.val + k, rfl⟩
  have hshort : ∀ j : Fin q, x j.succ - x j.castSucc < d := by
    intro j
    let l : ℤ := i + j.val + 1
    have hl : l ∈ Finset.Ioc i (i + q) := Finset.mem_Ioc.mpr ⟨by dsimp [l]; omega,
      by dsimp [l]; omega⟩
    have hgap : Λ (l + k) - Λ (l - 1 + k) < d := by
      apply lt_of_not_ge
      intro hge
      exact hnone ⟨l, hl, by simpa only [TwoSidedCarrier.clusterBoundary, decide_eq_true_eq] using hge⟩
    have hidx : l - 1 = i + j.val := by dsimp [l]; omega
    rw [hidx] at hgap
    simpa only [x, Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one, l, add_assoc]
      using hgap
  have := hcluster q x hxmono hxmem hshort
  omega

end MeyerGeneralProblem
