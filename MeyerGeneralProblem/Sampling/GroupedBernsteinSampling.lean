module

public import MeyerGeneralProblem.Sampling.GroupedBernsteinUniqueness
public import MeyerGeneralProblem.Sampling.GroupedFiniteFloor

@[expose] public section

/-!
# Uniform Bernstein sampling on the actual translated geometric class

The origin floor becomes a sup bound only after translating both the entire
function and its actual source groups, with an integer reindexing at the new
origin. The quantitative count bound is uniform in the real translation.
No per-carrier sampling constant is promoted to a class-uniform constant.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set Filter
open scoped Topology BigOperators

namespace IndexedSourceBlock

/-- Every actual block has size at most q when the boundary pattern has a
boundary in every q-index interval. -/
theorem size_le_of_boundary_every_q_steps {b : ℤ → Bool} {anchor : ℤ} {q : ℕ}
    (P : IndexedSourceBlock b anchor)
    (hboundary : ∀ i : ℤ, ∃ k ∈ Finset.Ioc i (i + q), b k = true) : P.size ≤ q := by
  by_contra h
  obtain ⟨k, hk, hbk⟩ := hboundary P.first
  have hk' := Finset.mem_Ioc.mp hk
  have hf := P.interior k hk'.1 (by omega)
  rw [hbk] at hf
  contradiction

/-- Shift the integer enumeration of an actual source block. Its full node
set, endpoint boundaries and absence of interior boundaries are preserved. -/
def reindex {b : ℤ → Bool} {anchor : ℤ} (k : ℤ)
    (P : IndexedSourceBlock b (anchor + k)) :
    IndexedSourceBlock (fun j => b (j + k)) anchor where
  first := P.first - k
  size := P.size
  anchor_mem := by have := P.anchor_mem; constructor <;> omega
  left_boundary := by simpa only [sub_add_cancel] using P.left_boundary
  right_boundary := by
    have heq : P.first - k + P.size + k = P.first + P.size := by omega
    simpa only [heq] using P.right_boundary
  interior := by
    intro j hlo hhi
    exact P.interior (j + k) (by omega) (by omega)

/-- Reindexing retains each original node exactly, not merely its range. -/
theorem reindex_index {b : ℤ → Bool} {anchor : ℤ} (k : ℤ)
    (P : IndexedSourceBlock b (anchor + k)) (j : Fin P.size) :
    (P.reindex k).index j + k = P.index j := by
  change P.first - k + (j : ℤ) + k = P.first + (j : ℤ)
  ring

/-- Translation and scalar normalization act on genuine full-group data by
the exact scalar norm. Group sizes and prefix orders are unchanged. -/
theorem dataNorm_reindex_translate {b : ℤ → Bool} {anchor : ℤ} (k : ℤ)
    (P : IndexedSourceBlock b (anchor + k)) (s : ℤ → ℝ) (f : ℝ → ℂ)
    (t : ℝ) (c : ℂ) :
    (P.reindex k).dataNorm (fun j => s (j + k) - t)
        (fun x => c * f (x + t)) = ‖c‖ * P.dataNorm s f := by
  unfold dataNorm
  change (∑ j : Fin P.size, ‖analyticDividedDifference
      (finiteNodeSequence (fun i : Fin P.size => s ((P.reindex k).index i + k) - t)) j
      (fun x => c * f (x + t))‖) = _
  simp only [reindex_index k P, analyticDividedDifference_const_mul_complex, norm_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  congr 2
  exact analyticDividedDifference_finite_recenter (fun i => s (P.index i)) j f t

end IndexedSourceBlock

/-- Genuine separation across source-group boundaries survives real
translation and integer reindexing with exactly the same separation constant. -/
theorem indexedGroupSeparation_translate_reindex {s : ℤ → ℝ} {b : ℤ → Bool} {d : ℝ}
    (hsep : IndexedGroupSeparation s b d) (t : ℝ) (k : ℤ) :
    IndexedGroupSeparation (fun j => s (j + k) - t) (fun j => b (j + k)) d := by
  rintro i j ⟨l, hil, hlj, hbl⟩
  have h := hsep (i + k) (j + k) ⟨l + k, by omega, by omega, hbl⟩
  linarith

/-- An entire exponential-type bound is stable under actual real translation
and constant multiplication. Its radial constants may change; its type does not. -/
theorem exponentialType_const_mul_real_translate {F : ℂ → ℂ} {τ : ℝ}
    (hτ : 0 ≤ τ)
    (htype : ∀ ε > 0, ∃ C > 0, ∀ z,
      ‖F z‖ ≤ C * Real.exp ((τ + ε) * ‖z‖)) (t : ℝ) (c : ℂ) :
    ∀ ε > 0, ∃ C > 0, ∀ z,
      ‖c * F (z + (t : ℂ))‖ ≤ C * Real.exp ((τ + ε) * ‖z‖) := by
  intro ε hε
  obtain ⟨C, hC, hbound⟩ := htype ε hε
  refine ⟨(‖c‖ + 1) * C * Real.exp ((τ + ε) * ‖(t : ℂ)‖), by positivity, ?_⟩
  intro z
  calc
    ‖c * F (z + (t : ℂ))‖ = ‖c‖ * ‖F (z + (t : ℂ))‖ := norm_mul _ _
    _ ≤ (‖c‖ + 1) * (C * Real.exp ((τ + ε) * ‖z + (t : ℂ)‖)) :=
      mul_le_mul (by linarith) (hbound _) (norm_nonneg _) (by positivity)
    _ ≤ (‖c‖ + 1) * (C * Real.exp ((τ + ε) * (‖z‖ + ‖(t : ℂ)‖))) := by
      gcongr
      exact norm_add_le _ _
    _ = _ := by rw [mul_add, Real.exp_add]; ring

/-- The same adjacent-gap and q-step constants work at every real origin
after choosing the actual straddling integer index of a two-sided carrier. -/
theorem TwoSidedCarrier.exists_reanchored_indexedMultisetGeometry
    (Λ : TwoSidedCarrier) {q : ℕ} {d H : ℝ}
    (hupper : ∀ j, Λ (j + 1) ≤ Λ j + H)
    (hstep : ∀ j, d ≤ Λ (j + q) - Λ j) (t : ℝ) :
    ∃ k : ℤ, IndexedMultisetGeometry q d H (fun j => Λ (j + k) - t) := by
  obtain ⟨k, hneg, hpos⟩ := Λ.exists_straddling_index t
  refine ⟨k, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · intro i j hij
    exact sub_le_sub_right (Λ.strictMono.monotone (by omega)) t
  · have heq : -1 + k = k - 1 := by omega
    change Λ (-1 + k) - t ≤ 0
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
    have hs := hstep (j + k)
    have heq : j + (q : ℤ) + k = j + k + q := by omega
    change d ≤ (Λ (j + q + k) - t) - (Λ (j + k) - t)
    rw [heq]
    linarith

/-- A common positive translated radial count lower bound forces a common
adjacent-gap upper bound. Thus the compactness constant is derived uniformly
from the quantitative class, not selected separately for each carrier. -/
theorem TwoSidedCarrier.adjacent_gap_le_of_translated_count
    (Λ : TwoSidedCarrier) {ρ r₀ : ℝ} (hρ : 0 < ρ) (hr₀ : 0 < r₀)
    (hcounts : ∀ t R, r₀ ≤ R → 2 * ρ * R ≤
      ((Λ.toLocallyFinite.carrier ∩ Ioo (t - R) (t + R)).ncard : ℝ)) (j : ℤ) :
    Λ (j + 1) ≤ Λ j + 2 * r₀ := by
  have hc := hcounts (Λ j + r₀) r₀ le_rfl
  have hpositive : 0 < ((Λ.toLocallyFinite.carrier ∩
      Ioo (Λ j + r₀ - r₀) (Λ j + r₀ + r₀)).ncard : ℝ) :=
    (by positivity : (0 : ℝ) < 2 * ρ * r₀).trans_le hc
  have hne : (Λ.toLocallyFinite.carrier ∩
      Ioo (Λ j + r₀ - r₀) (Λ j + r₀ + r₀)).ncard ≠ 0 := by
    intro hz
    simp only [hz, Nat.cast_zero, lt_self_iff_false] at hpositive
  obtain ⟨y, ⟨⟨k, rfl⟩, hlo, hhi⟩⟩ := Set.nonempty_of_ncard_ne_zero hne
  change Λ j + r₀ - r₀ < Λ k at hlo
  have hlow : Λ j < Λ k := by linarith
  have hjk : j < k := Λ.strictMono.lt_iff_lt.mp hlow
  have hmono : Λ (j + 1) ≤ Λ k := Λ.strictMono.monotone (by omega)
  have hhigh : Λ k < Λ j + r₀ + r₀ := hhi
  linarith

/-- Genuine sup-norm sampling, uniformly over every carrier in the displayed
quantitative class. `D` bounds actual full-group data, not a presumed sampling
operator. The resulting constant is chosen before the carrier and function. -/
theorem exists_uniform_grouped_bernstein_sup_bound
    {q : ℕ} {d H τ ρ r₀ : ℝ} (hd : 0 < d) (hτ : 0 ≤ τ)
    (hρ : τ / Real.pi < ρ) (hr₀ : 0 < r₀) :
    ∃ A > 0, ∀ (Λ : TwoSidedCarrier) (b : ℤ → Bool)
      (P : ∀ anchor, IndexedSourceBlock b anchor),
      (∀ j, Λ (j + 1) ≤ Λ j + H) →
      (∀ j, d ≤ Λ (j + q) - Λ j) →
      IndexedGroupSeparation Λ b d → (∀ anchor, (P anchor).size ≤ q) →
      (∀ t R, r₀ ≤ R → 2 * ρ * R ≤
        ((Λ.toLocallyFinite.carrier ∩ Ioo (t - R) (t + R)).ncard : ℝ)) →
      ∀ (F : ℂ → ℂ), Differentiable ℂ F →
      (∀ ε > 0, ∃ C > 0, ∀ z, ‖F z‖ ≤ C * Real.exp ((τ + ε) * ‖z‖)) →
      BddAbove (Set.range (fun x : ℝ => ‖F (x : ℂ)‖)) →
      ∀ D : ℝ, 0 ≤ D →
      (∀ anchor, (P anchor).dataNorm Λ (fun x : ℝ => F (x : ℂ)) ≤ D) →
      ∀ x : ℝ, ‖F (x : ℂ)‖ ≤ A * D := by
  obtain ⟨ε, hε, hfloor⟩ := exists_uniform_grouped_bernstein_origin_floor
    (q := q) (H := H) hd hτ hρ hr₀
  refine ⟨ε⁻¹, inv_pos.mpr hε, ?_⟩
  intro Λ b P hupper hstep hsep hsize hcounts F hF htype hbounded D hD hdata x
  let N := sSup (Set.range (fun t : ℝ => ‖F (t : ℂ)‖))
  have hNbound (t : ℝ) : ‖F (t : ℂ)‖ ≤ N := le_csSup hbounded (mem_range_self t)
  have hNnonneg : 0 ≤ N := (norm_nonneg _).trans (hNbound 0)
  by_cases hNzero : N = 0
  · exact (hNbound x).trans (by rw [hNzero]; positivity)
  have hNpos : 0 < N := lt_of_le_of_ne hNnonneg (Ne.symm hNzero)
  obtain ⟨_, ⟨t, rfl⟩, ht⟩ := exists_lt_of_lt_csSup
    (Set.range_nonempty (fun t : ℝ => ‖F (t : ℂ)‖)) (half_lt_self hNpos)
  obtain ⟨k, hgeom⟩ := Λ.exists_reanchored_indexedMultisetGeometry hupper hstep t
  let c : ℂ := ((N⁻¹ : ℝ) : ℂ)
  have hc : ‖c‖ = N⁻¹ := by
    change ‖((N⁻¹ : ℝ) : ℂ)‖ = N⁻¹
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hNpos)]
  have hnormalized (u : ℝ) : ‖c * F ((u : ℂ) + (t : ℂ))‖ ≤ 1 := by
    rw [norm_mul, hc]
    calc
      _ ≤ N⁻¹ * N := mul_le_mul_of_nonneg_left
        (by simpa only [Complex.ofReal_add] using hNbound (u + t)) (inv_nonneg.mpr hNnonneg)
      _ = 1 := inv_mul_cancel₀ hNzero
  have horigin : (1 / 2 : ℝ) ≤ ‖c * F ((0 : ℂ) + (t : ℂ))‖ := by
    rw [zero_add, norm_mul, hc]
    have hmul := mul_le_mul_of_nonneg_left ht.le (inv_nonneg.mpr hNnonneg)
    have hhalf : N⁻¹ * (N / 2) = (1 / 2 : ℝ) := by field_simp
    rwa [hhalf] at hmul
  have hinj : Function.Injective (fun j : ℤ => Λ (j + k) - t) := by
    intro i j hij
    have heq : Λ (i + k) - t = Λ (j + k) - t := hij
    have h := Λ.strictMono.injective (sub_left_injective heq)
    omega
  have hF' : Differentiable ℂ (fun z => c * F (z + (t : ℂ))) := by fun_prop
  have hcounts' (R : ℝ) (hR : r₀ ≤ R) : 2 * ρ * R ≤
      (indexedMultisetIntervalCount (fun j => Λ (j + k) - t) (-R) R : ℝ) := by
    rw [Λ.translated_indexedMultisetIntervalCount_eq_ncard]
    simpa only [sub_eq_add_neg, add_comm] using hcounts t R hR
  obtain ⟨anchor, hanchor⟩ := hfloor (fun j => Λ (j + k) - t) (fun j => b (j + k))
    (fun a => (P (a + k)).reindex k) (fun z => c * F (z + (t : ℂ)))
    hgeom hinj (indexedGroupSeparation_translate_reindex hsep t k)
    (fun a => hsize (a + k)) hF'
    (exponentialType_const_mul_real_translate hτ htype t c) hnormalized horigin hcounts'
  have heq : (fun u : ℝ => c * F ((u : ℂ) + (t : ℂ))) =
      fun u : ℝ => c * (fun v : ℝ => F (v : ℂ)) (u + t) := by
    simp only [Complex.ofReal_add]
  rw [heq, IndexedSourceBlock.dataNorm_reindex_translate k (P (anchor + k))
    Λ (fun v : ℝ => F (v : ℂ)) t c, hc] at hanchor
  have hεD : ε ≤ N⁻¹ * D := hanchor.trans
    (mul_le_mul_of_nonneg_left (hdata (anchor + k)) (inv_nonneg.mpr hNnonneg))
  have hND : N ≤ ε⁻¹ * D := by
    have hmul := mul_le_mul_of_nonneg_right hεD hNnonneg
    have hcancel : (N⁻¹ * D) * N = D := by field_simp
    rw [hcancel] at hmul
    rw [mul_comm ε⁻¹ D]
    apply (le_mul_inv_iff₀ hε).mpr
    simpa only [mul_comm] using hmul
  exact (hNbound x).trans hND

/-- The source-faithful class-uniform Bernstein sup estimate for bounded
clusters. All source groups are actual strict-gap chain blocks. A common
translated count lower bound supplies every compactness constant; full prefix
data of individual order, not an assumed sampling inequality, bound the result. -/
theorem exists_uniform_clustered_bernstein_sup_bound
    {q : ℕ} {d τ ρ r₀ : ℝ} (hd : 0 < d) (hτ : 0 ≤ τ)
    (hρ : τ / Real.pi < ρ) (hr₀ : 0 < r₀) :
    ∃ A > 0, ∀ (Λ : TwoSidedCarrier), BoundedClusterOrder Λ.toLocallyFinite d q →
      (∀ t R, r₀ ≤ R → 2 * ρ * R ≤
        ((Λ.toLocallyFinite.carrier ∩ Ioo (t - R) (t + R)).ncard : ℝ)) →
      ∀ (P : ∀ anchor, IndexedSourceBlock (Λ.clusterBoundary d 0) anchor)
        (F : ℂ → ℂ), Differentiable ℂ F →
      (∀ ε > 0, ∃ C > 0, ∀ z, ‖F z‖ ≤ C * Real.exp ((τ + ε) * ‖z‖)) →
      BddAbove (Set.range (fun x : ℝ => ‖F (x : ℂ)‖)) →
      ∀ D : ℝ, 0 ≤ D →
      (∀ anchor (j : Fin (P anchor).size),
        ‖analyticDividedDifference
          (finiteNodeSequence (fun i => Λ ((P anchor).index i))) j
          (fun x : ℝ => F (x : ℂ))‖ ≤ D) →
      ∀ x : ℝ, ‖F (x : ℂ)‖ ≤ A * D := by
  obtain ⟨A, hA, hbound⟩ := exists_uniform_grouped_bernstein_sup_bound
    (q := q) (H := 2 * r₀) hd hτ hρ hr₀
  refine ⟨A * (q : ℝ) + 1, by positivity, ?_⟩
  intro Λ hcluster hcounts P F hF htype hbounded D hD hdata x
  have hρpos : 0 < ρ := (div_nonneg hτ Real.pi_pos.le).trans_lt hρ
  have hsize (anchor : ℤ) : (P anchor).size ≤ q :=
    (P anchor).size_le_of_boundary_every_q_steps
      (Λ.clusterBoundary_every_q_steps hcluster 0)
  have hsep : IndexedGroupSeparation Λ (Λ.clusterBoundary d 0) d := by
    simpa only [add_zero, sub_zero] using Λ.clusterBoundary_groupSeparation d 0 0
  have h := hbound Λ (Λ.clusterBoundary d 0) P
    (Λ.adjacent_gap_le_of_translated_count hρpos hr₀ hcounts)
    (Λ.qstep_separated_of_boundedClusterOrder hcluster) hsep hsize hcounts
    F hF htype hbounded ((q : ℝ) * D) (mul_nonneg (Nat.cast_nonneg q) hD) (by
      intro anchor
      unfold IndexedSourceBlock.dataNorm
      calc
        _ ≤ ∑ _j : Fin (P anchor).size, D := Finset.sum_le_sum (fun j _ => hdata anchor j)
        _ = ((P anchor).size : ℝ) * D := by simp
        _ ≤ (q : ℝ) * D := mul_le_mul_of_nonneg_right (by exact_mod_cast hsize anchor) hD) x
  exact h.trans (by nlinarith)

/-- The retained block-count inequality supplies one radial threshold for
the entire class at every strict density below `N / B`. Endpoint convention
is the same open interval used in the actual indexed-count bridge. -/
theorem uniform_translated_radial_count_of_block_count
    (N : ℕ) {B ρ : ℝ} (hρ : ρ < (N : ℝ) / B) :
    ∃ r₀ > 0, ∀ (Λ : TwoSidedCarrier),
      (∀ t R, 0 < R → (N : ℝ) * ((⌊2 * R / B⌋ : ℝ) - 2) ≤
        ((Λ.toLocallyFinite.carrier ∩ Ioo (t - R) (t + R)).ncard : ℝ)) →
      ∀ t R, r₀ ≤ R → 2 * ρ * R ≤
        ((Λ.toLocallyFinite.carrier ∩ Ioo (t - R) (t + R)).ncard : ℝ) := by
  let δ := (N : ℝ) / B - ρ
  have hδ : 0 < δ := sub_pos.mpr hρ
  refine ⟨3 * (N : ℝ) / (2 * δ) + 1, by positivity, ?_⟩
  intro Λ hblock t R hR
  have hRpos : 0 < R := (by positivity : (0 : ℝ) < 3 * (N : ℝ) / (2 * δ) + 1).trans_le hR
  have hδR : 3 * (N : ℝ) ≤ R * (2 * δ) :=
    (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * δ)).mp (by linarith)
  have hfloor := Int.sub_one_lt_floor (2 * R / B)
  have hmul := mul_le_mul_of_nonneg_left hfloor.le (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  have hblock' := hblock t R hRpos
  have heq : (N : ℝ) * (2 * R / B) = 2 * ((N : ℝ) / B) * R := by ring
  dsimp [δ] at hδR
  nlinarith

/-- The retained `K(q,d,B,N)` block-count hypothesis gives genuine uniform
Bernstein sup sampling at every angular type strictly below `π N / B`.
The constant is chosen before the carrier, groups and function. -/
theorem exists_uniform_clustered_bernstein_sup_bound_of_block_count
    {q N : ℕ} {d B τ : ℝ} (hd : 0 < d) (hτ : 0 ≤ τ)
    (hgap : τ / Real.pi < (N : ℝ) / B) :
    ∃ A > 0, ∀ (Λ : TwoSidedCarrier), BoundedClusterOrder Λ.toLocallyFinite d q →
      (∀ t R, 0 < R → (N : ℝ) * ((⌊2 * R / B⌋ : ℝ) - 2) ≤
        ((Λ.toLocallyFinite.carrier ∩ Ioo (t - R) (t + R)).ncard : ℝ)) →
      ∀ (P : ∀ anchor, IndexedSourceBlock (Λ.clusterBoundary d 0) anchor)
        (F : ℂ → ℂ), Differentiable ℂ F →
      (∀ ε > 0, ∃ C > 0, ∀ z, ‖F z‖ ≤ C * Real.exp ((τ + ε) * ‖z‖)) →
      BddAbove (Set.range (fun x : ℝ => ‖F (x : ℂ)‖)) →
      ∀ D : ℝ, 0 ≤ D →
      (∀ anchor (j : Fin (P anchor).size),
        ‖analyticDividedDifference
          (finiteNodeSequence (fun i => Λ ((P anchor).index i))) j
          (fun x : ℝ => F (x : ℂ))‖ ≤ D) →
      ∀ x : ℝ, ‖F (x : ℂ)‖ ≤ A * D := by
  obtain ⟨ρ, hρlow, hρhigh⟩ := exists_between hgap
  obtain ⟨r₀, hr₀, hcount⟩ := uniform_translated_radial_count_of_block_count N hρhigh
  obtain ⟨A, hA, hbound⟩ := exists_uniform_clustered_bernstein_sup_bound
    (q := q) hd hτ hρlow hr₀
  exact ⟨A, hA, fun Λ hcluster hblock => hbound Λ hcluster (hcount Λ hblock)⟩

end

end MeyerGeneralProblem
