module

public import MeyerGeneralProblem.Cardinal.Adaptive.PhaseGeometry
public import Mathlib.Data.Nat.Log
import all Mathlib.Data.Nat.Log
public import Mathlib.Data.Set.Card
import all Mathlib.Data.Set.Card
public import Mathlib.Data.Int.Interval
import all Mathlib.Data.Int.Interval

@[expose] public section

/-!
# Quantitative counts for actual adaptive blocks

Cell thresholds bound the number of eligible phase labels. This bounds the
actual atom count even if the parametrization is not injective. Reciprocal
scale bounds then give a logarithmic bound on the number of blocks that meet
a compact interval, under the original exponential gap schedule.
-/

namespace MeyerGeneralProblem.Adaptive

noncomputable section

/-- Every eligible phase label is at most twice its cell index in absolute value. -/
theorem phaseIndex_le_twice_cell {R : ℕ} (j : ℕ+) (n : ℤ)
    (hcell : cellThreshold R j ≤ n.natAbs) : (j : ℕ) ≤ 2 * n.natAbs := by
  unfold cellThreshold headLength at hcell
  split_ifs at hcell <;> omega

/-- Finite label catalogue for cells up to N and their possible phase indices. -/
def blockCatalogueLabels (N : ℕ) : Finset (ℕ × Bool × ℤ) :=
  (Finset.Icc 1 (2 * N)) ×ˢ
    ((Finset.univ : Finset Bool) ×ˢ (Finset.Icc (-(N : ℤ)) (N : ℤ)))

/-- Decode the finite catalogue by the original phase formula. -/
def blockCatalogueAtom (P R : ℕ) (q : ℕ × Bool × ℤ) : ℝ :=
  (q.2.2 : ℝ) + signedPhase q.2.1 (blockPhase P R ⟨max q.1 1, by omega⟩)

/-- Catalogue points may include atoms outside the interval; this only enlarges the bound. -/
def blockCataloguePoints (P R N : ℕ) : Finset ℝ := by
  classical
  exact (blockCatalogueLabels N).image (blockCatalogueAtom P R)

/-- The catalogue contains at most two signs for each phase and integer cell. -/
theorem blockCatalogueLabels_card (N : ℕ) :
    (blockCatalogueLabels N).card = 4 * N * (2 * N + 1) := by
  have hi : ((N : ℤ) + 1 - -(N : ℤ)).toNat = 2 * N + 1 := by omega
  simp only [blockCatalogueLabels, Finset.card_product, Nat.card_Icc,
    Finset.card_univ, Fintype.card_bool, Int.card_Icc, hi]
  simp only [Nat.add_sub_cancel]
  ring

/-- The original cell schedule places every atom in a uniformly bounded catalogue. -/
theorem blockSet_Icc_subset_catalogue {P R : ℕ} (hP : 1 ≤ P) (hR : 1 ≤ R)
    (r : ℝ) :
    blockSet P R ∩ Set.Icc (-r) r ⊆
      (blockCataloguePoints P R ⌈r + 1 / 2⌉₊ : Set ℝ) := by
  classical
  rintro x ⟨⟨j, positive, n, hn, hx⟩, hxa, hxb⟩
  have hxabs : |x| ≤ r := abs_le.mpr ⟨hxa, hxb⟩
  have hphase := abs_signedPhase_lt_half hP hR j positive
  have hnreal : |(n : ℝ)| < r + 1 / 2 := by
    have htri := abs_sub_le (n : ℝ) x 0
    rw [hx] at htri
    simp only [sub_add_cancel_left, sub_zero, abs_neg] at htri
    rw [← hx] at htri
    linarith
  have hnreal' : |(n : ℝ)| ≤ (⌈r + 1 / 2⌉₊ : ℝ) :=
    hnreal.le.trans (Nat.le_ceil _)
  have hnabs : n.natAbs ≤ ⌈r + 1 / 2⌉₊ := by
    have hc : (n.natAbs : ℝ) ≤ (⌈r + 1 / 2⌉₊ : ℝ) := by simpa using hnreal'
    exact_mod_cast hc
  have hjbound : (j : ℕ) ≤ 2 * ⌈r + 1 / 2⌉₊ :=
    (phaseIndex_le_twice_cell j n hn).trans (Nat.mul_le_mul_left 2 hnabs)
  have hncells : -(⌈r + 1 / 2⌉₊ : ℤ) ≤ n ∧ n ≤ (⌈r + 1 / 2⌉₊ : ℤ) := by
    obtain ⟨hlo, hhi⟩ := abs_le.mp hnreal'
    constructor
    · exact_mod_cast hlo
    · exact_mod_cast hhi
  have hq : ((j : ℕ), positive, n) ∈ blockCatalogueLabels ⌈r + 1 / 2⌉₊ := by
    simp only [blockCatalogueLabels, Finset.mem_product, Finset.mem_Icc,
      Finset.mem_univ, true_and]
    exact ⟨⟨j.pos, hjbound⟩, hncells⟩
  apply Finset.mem_image.mpr
  refine ⟨((j : ℕ), positive, n), hq, ?_⟩
  have hjrec : (⟨max (j : ℕ) 1, by omega⟩ : ℕ+) = j := by
    apply Subtype.ext
    exact Nat.max_eq_left j.pos
  change (n : ℝ) + signedPhase positive (blockPhase P R _) = x
  rw [hjrec]
  exact hx.symm

/-- Uniform quadratic actual-atom bound, independent of the order and gap parameters. -/
theorem blockSet_Icc_ncard_le {P R : ℕ} (hP : 1 ≤ P) (hR : 1 ≤ R)
    (r : ℝ) (hr : 0 ≤ r) :
    ((blockSet P R ∩ Set.Icc (-r) r).ncard : ℝ) ≤ 32 * (1 + r) ^ 2 := by
  classical
  let N := ⌈r + 1 / 2⌉₊
  have hcat : (blockSet P R ∩ Set.Icc (-r) r).ncard ≤ 4 * N * (2 * N + 1) := by
    calc
      _ ≤ (blockCataloguePoints P R N).card := by
        simpa only [Set.ncard_coe_finset] using Set.ncard_le_ncard (blockSet_Icc_subset_catalogue hP hR r)
          (Finset.finite_toSet _)
      _ ≤ (blockCatalogueLabels N).card := Finset.card_image_le
      _ = _ := blockCatalogueLabels_card N
  have hceil : (N : ℝ) < r + 1 / 2 + 1 := Nat.ceil_lt_add_one (by linarith)
  have hnonneg : (0 : ℝ) ≤ N := by positivity
  have hcast : ((blockSet P R ∩ Set.Icc (-r) r).ncard : ℝ) ≤
      4 * (N : ℝ) * (2 * (N : ℝ) + 1) := by exact_mod_cast hcat
  have hsq : (N : ℝ) ^ 2 ≤ (r + 3 / 2) ^ 2 := by nlinarith
  nlinarith [sq_nonneg r]

/-- Natural block indices with at least one actual reciprocal atom in the window. -/
def meetingBlockIndices (R : ℕ+ → ℕ) (s : ℕ+ → ℝ) (r : ℝ) : Set ℕ :=
  {i | ∃ hi : 0 < i, ∃ σ : ReciprocalSign,
    (sectorSet R s (⟨i, hi⟩, σ) ∩ Set.Icc (-r) r).Nonempty}

/-- A block meeting the compact window has logarithmically bounded index. -/
theorem meetingBlockIndices_subset_log (R : ℕ+ → ℕ) (s : ℕ+ → ℝ)
    (hR : ∀ i : ℕ+, 2 ^ (i : ℕ) ≤ R i) (hs : ∀ i, s i ∈ Set.Icc (1 : ℝ) 2)
    (r : ℝ) : meetingBlockIndices R s r ⊆ Set.Icc 1 (Nat.log 2 ⌈2*r + 1⌉₊) := by
  rintro i ⟨hi, σ, x, hx, hxa, hxb⟩
  have hgrowth := linearGap_of_exponential R hR
  have hgap := sectorSet_central_gap R s (fun j => j.pos.trans_le (hgrowth j)) hs
    (⟨i, hi⟩, σ) hx
  have hxabs : |x| ≤ r := abs_le.mpr ⟨hxa, hxb⟩
  have hRreal : ((2 ^ i : ℕ) : ℝ) ≤ R ⟨i, hi⟩ := by exact_mod_cast hR ⟨i, hi⟩
  have hceil := Nat.le_ceil (2*r + 1)
  have hpow : 2 ^ i ≤ ⌈2*r + 1⌉₊ := by
    have hreal : ((2 ^ i : ℕ) : ℝ) ≤ (⌈2*r + 1⌉₊ : ℝ) := by linarith
    exact_mod_cast hreal
  exact ⟨hi, Nat.le_log_of_pow_le (by decide) hpow⟩

/-- The number of distinct blocks meeting a window is bounded by a base-two logarithm. -/
theorem meetingBlockIndices_ncard_le (R : ℕ+ → ℕ) (s : ℕ+ → ℝ)
    (hR : ∀ i : ℕ+, 2 ^ (i : ℕ) ≤ R i) (hs : ∀ i, s i ∈ Set.Icc (1 : ℝ) 2)
    (r : ℝ) : (meetingBlockIndices R s r).ncard ≤ Nat.log 2 ⌈2*r + 1⌉₊ := by
  have h := Set.ncard_le_ncard (meetingBlockIndices_subset_log R s hR hs r)
    (Set.finite_Icc _ _)
  simpa [← Finset.coe_Icc, Nat.card_Icc] using h

end
end MeyerGeneralProblem.Adaptive
