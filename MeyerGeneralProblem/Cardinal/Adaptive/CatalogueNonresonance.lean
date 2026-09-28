module

public import MeyerGeneralProblem.Cardinal.Adaptive.ReciprocalLaurentPolynomial
public import MeyerGeneralProblem.Cardinal.Adaptive.PhaseCounts
public import Mathlib.Analysis.SpecificLimits.Basic
import all Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-!
# Actual finite-prefix comparison catalogues

The first M scale coordinates and one arbitrary originating sector fit into
M+1 distinct coordinates. This module retains the exact accepted exponent
2(M+1)(2M+6) for the later dyadic comparison argument.
-/

namespace MeyerGeneralProblem.Adaptive
noncomputable section
open MeasureTheory Set
open scoped ENNReal

/-- The accepted §4 distance exponent, without weakening its quadratic dimension dependence. -/
def catalogueDistanceExponent (M : ℕ) : ℕ := 2*(M+1)*(2*M+6)

/-- A positive scale index from the finite prefix. -/
def prefixScaleIndex {M : ℕ} (i : Fin M) : ℕ+ := ⟨i.val+1, Nat.succ_pos _⟩

/-- A coordinate beyond the whole prefix, chosen to equal the origin when it is a future sector. -/
def additionalScaleIndex (M : ℕ) (origin : ℕ+) : ℕ+ := ⟨max (M+1) origin.val, by omega⟩

/-- Exact M+1 distinct scale coordinates covering the prefix and any given origin. -/
def comparisonCoordinates (M : ℕ) (origin : ℕ+) : Fin (M+1) → ℕ+ :=
  Fin.lastCases (additionalScaleIndex M origin) prefixScaleIndex

@[simp] theorem comparisonCoordinates_castSucc {M : ℕ} (origin : ℕ+) (i : Fin M) :
    comparisonCoordinates M origin i.castSucc = prefixScaleIndex i := by
  simp [comparisonCoordinates]

@[simp] theorem comparisonCoordinates_last (M : ℕ) (origin : ℕ+) :
    comparisonCoordinates M origin (Fin.last M) = additionalScaleIndex M origin := by
  simp [comparisonCoordinates]

theorem comparisonCoordinates_injective (M : ℕ) (origin : ℕ+) :
    Function.Injective (comparisonCoordinates M origin) := by
  intro i j h
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => rfl
    | cast j =>
      simp only [comparisonCoordinates_last, comparisonCoordinates_castSucc] at h
      have hv := congrArg Subtype.val h
      dsimp [additionalScaleIndex, prefixScaleIndex] at hv
      omega
  | cast i =>
    induction j using Fin.lastCases with
    | last =>
      simp only [comparisonCoordinates_last, comparisonCoordinates_castSucc] at h
      have hv := congrArg Subtype.val h
      dsimp [additionalScaleIndex, prefixScaleIndex] at hv
      omega
    | cast j =>
      simp only [comparisonCoordinates_castSucc] at h
      have hv := congrArg Subtype.val h
      dsimp [prefixScaleIndex] at hv
      have hij : i = j := Fin.ext (by omega)
      exact congrArg Fin.castSucc hij

/-- The exact slot occupied by the originating sector in the independent coordinate family. -/
def originCoordinate (M : ℕ) (origin : ℕ+) : Fin (M+1) :=
  if h : origin.val ≤ M then ⟨origin.val-1, by have := origin.pos; omega⟩ else Fin.last M

theorem comparisonCoordinates_origin (M : ℕ) (origin : ℕ+) :
    comparisonCoordinates M origin (originCoordinate M origin) = origin := by
  unfold originCoordinate
  split_ifs with h
  · have heq : (⟨origin.val-1, by have := origin.pos; omega⟩ : Fin (M+1)) =
        (⟨origin.val-1, by have := origin.pos; omega⟩ : Fin M).castSucc := rfl
    rw [heq, comparisonCoordinates_castSucc]
    apply Subtype.ext
    change origin.val-1+1 = origin.val
    have := origin.pos
    omega
  · rw [comparisonCoordinates_last]
    apply Subtype.ext
    change max (M+1) origin.val = origin.val
    omega

/-- Extending a finite shift family by zero in the additional coordinate creates no extra shift. -/
def extendPrefixShifts {M : ℕ} (k : Fin M × ReciprocalSign → ℤ) :
    Fin (M+1) × ReciprocalSign → ℤ := fun label =>
  Fin.lastCases 0 (fun i => k (i, label.2)) label.1

@[simp] theorem extendPrefixShifts_castSucc {M : ℕ} (k : Fin M × ReciprocalSign → ℤ)
    (i : Fin M) (σ : ReciprocalSign) : extendPrefixShifts k (i.castSucc, σ) = k (i, σ) := by
  simp [extendPrefixShifts]

@[simp] theorem extendPrefixShifts_last {M : ℕ} (k : Fin M × ReciprocalSign → ℤ)
    (σ : ReciprocalSign) : extendPrefixShifts k (Fin.last M, σ) = 0 := by
  simp [extendPrefixShifts]

/-- Exact shift evaluation after extension to the independent comparison coordinates. -/
theorem extendPrefixShifts_eval {M : ℕ} (k : Fin M × ReciprocalSign → ℤ)
    (origin : ℕ+) (s : ℕ+ → ℝ) :
    reciprocalLaurentValue (fun i => (extendPrefixShifts k (i, .forward) : ℝ))
      (fun i => (extendPrefixShifts k (i, .reciprocal) : ℝ))
      (fun i => s (comparisonCoordinates M origin i)) =
    reciprocalLaurentValue (fun i => (k (i, .forward) : ℝ))
      (fun i => (k (i, .reciprocal) : ℝ)) (fun i => s (prefixScaleIndex i)) := by
  unfold reciprocalLaurentValue
  rw [Fin.sum_univ_castSucc]
  simp

/-- The literal original full-sequence comparison with a finite-prefix Fourier shift. -/
def prefixComparisonValue {M : ℕ} (target : Fin M × ReciprocalSign) (origin : Label)
    (n n' : ℤ) (β β' : ℝ) (k : Fin M × ReciprocalSign → ℤ) (s : ℕ+ → ℝ) : ℝ :=
  scaleFactor target.2 (s (prefixScaleIndex target.1))*((n : ℝ)+β) -
    labelScale s origin*((n' : ℝ)+β') -
      reciprocalLaurentValue (fun i => (k (i, .forward) : ℝ))
        (fun i => (k (i, .reciprocal) : ℝ)) (fun i => s (prefixScaleIndex i))

/-- The full original comparison is represented by exactly M+1 independent coordinates. -/
theorem prefixComparisonValue_eq_catalogue {M : ℕ} (target : Fin M × ReciprocalSign)
    (origin : Label) (n n' : ℤ) (β β' : ℝ) (k : Fin M × ReciprocalSign → ℤ) (s : ℕ+ → ℝ) :
    prefixComparisonValue target origin n n' β β' k s =
      catalogueComparisonValue (target.1.castSucc, target.2)
        (originCoordinate M origin.1, origin.2) n n' β β' (extendPrefixShifts k)
        (fun i => s (comparisonCoordinates M origin.1 i)) := by
  simp [prefixComparisonValue, catalogueComparisonValue, extendPrefixShifts_eval,
    comparisonCoordinates_origin, labelScale_eq_scaleFactor]

/-- Local equality of source labels is exactly equality of the original full-sequence labels. -/
theorem comparison_origin_label_eq_iff {M : ℕ} (target : Fin M × ReciprocalSign) (origin : Label) :
    (originCoordinate M origin.1, origin.2) = (target.1.castSucc, target.2) ↔
      origin = (prefixScaleIndex target.1, target.2) := by
  constructor
  · intro h
    have hi := congrArg (fun b : Fin (M+1) × ReciprocalSign =>
      (comparisonCoordinates M origin.1 b.1, b.2)) h
    simpa only [comparisonCoordinates_origin, comparisonCoordinates_castSucc] using hi
  · intro h
    apply Prod.ext
    · apply comparisonCoordinates_injective M origin.1
      simpa only [comparisonCoordinates_origin, comparisonCoordinates_castSucc] using congrArg Prod.fst h
    · exact congrArg (fun b : Label => b.2) h

/-- Expected identity on the original first-M shifts and original sector labels. -/
def ExpectedPrefixComparison {M : ℕ} (target : Fin M × ReciprocalSign) (origin : Label)
    (n n' : ℤ) (β β' : ℝ) (k : Fin M × ReciprocalSign → ℤ) : Prop :=
  origin = (prefixScaleIndex target.1, target.2) ∧ β' = β ∧
    k target = n-n' ∧ ∀ label, label ≠ target → k label = 0

/-- Coordinate extension preserves precisely the source's expected comparisons. -/
theorem expectedPrefixComparison_iff {M : ℕ} (target : Fin M × ReciprocalSign) (origin : Label)
    (n n' : ℤ) (β β' : ℝ) (k : Fin M × ReciprocalSign → ℤ) :
    ExpectedCatalogueComparison (target.1.castSucc, target.2)
      (originCoordinate M origin.1, origin.2) n n' β β' (extendPrefixShifts k) ↔
      ExpectedPrefixComparison target origin n n' β β' k := by
  unfold ExpectedCatalogueComparison ExpectedPrefixComparison
  rw [comparison_origin_label_eq_iff, extendPrefixShifts_castSucc]
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  constructor
  · intro h ⟨i, σ⟩ hne
    have hne' : (i.castSucc, σ) ≠ (target.1.castSucc, target.2) := by
      intro heq
      apply hne
      exact Prod.ext ((Fin.castSucc_injective M) (congrArg Prod.fst heq))
        (congrArg (fun b : Fin (M+1) × ReciprocalSign => b.2) heq)
    simpa only [extendPrefixShifts_castSucc] using h (i.castSucc, σ) hne'
  · intro h ⟨i, σ⟩ hne
    induction i using Fin.lastCases with
    | last => exact extendPrefixShifts_last k σ
    | cast i =>
      rw [extendPrefixShifts_castSucc]
      apply h (i, σ)
      intro heq
      apply hne
      exact congrArg (fun b : Fin M × ReciprocalSign => (b.1.castSucc, b.2)) heq

/-- Actual prefix comparisons inherit the bound using M+1 genuinely distinct coordinates. -/
theorem exists_actual_prefix_comparison_sublevel_bound (M : ℕ) (R : Fin M → ℕ)
    (hR : ∀ i, 1 ≤ R i) :
    ∃ d : ℝ, 0 < d ∧ ∀ target : Fin M × ReciprocalSign, ∀ j : Fin M, ∀ positive : Bool,
      ∀ origin : Label, ∀ n n' : ℤ, ∀ β' : ℝ, ∀ k : Fin M × ReciprocalSign → ℤ,
      (origin = (prefixScaleIndex target.1, target.2) → β' ∈ phaseSet (target.1.val+1) (R target.1)) →
      ¬ ExpectedPrefixComparison target origin n n' (prefixCataloguePhase R (target.1, j, positive)) β' k →
      ∀ u : ℝ, 0 < u →
      scaleProbability {s | |prefixComparisonValue target origin n n'
        (prefixCataloguePhase R (target.1, j, positive)) β' k s| < u} ≤
      min 1 (ENNReal.ofReal (16*((M+1 : ℕ) : ℝ)*((2^(M+1)*u)/min d 1)^
        ((1 : ℝ)/(2*((M+1 : ℕ) : ℝ))))) := by
  obtain ⟨d, hd, h⟩ := exists_prefix_catalogue_comparison_sublevel_bound M R hR
  refine ⟨d, hd, ?_⟩
  intro target j positive origin n n' β' k horigin hbad u hu
  have h := h (target.1, j, positive) (comparisonCoordinates M origin.1)
    (comparisonCoordinates_injective M origin.1) (target.1.castSucc, target.2)
    (originCoordinate M origin.1, origin.2) n n' β' (extendPrefixShifts k)
    (fun heq => horigin ((comparison_origin_label_eq_iff target origin).mp heq))
    (fun hex => hbad ((expectedPrefixComparison_iff target origin n n' _ β' k).mp hex)) u hu
  simpa only [← prefixComparisonValue_eq_catalogue] using h

/-- A finite deterministic origin catalogue: block index, reciprocal sign, phase label, sign and cell. -/
def originCatalogueLabels (r : ℝ) : Finset (ℕ × ReciprocalSign × ℕ × Bool × ℤ) :=
  (Finset.Icc 1 (Nat.log 2 ⌈2*r+1⌉₊)) ×ˢ
    ((Finset.univ : Finset ReciprocalSign) ×ˢ blockCatalogueLabels ⌈2*r+1/2⌉₊)

/-- Exact size of the origin catalogue, independent of every gap and scale value. -/
theorem originCatalogueLabels_card (r : ℝ) :
    (originCatalogueLabels r).card =
      8 * (Nat.log 2 ⌈2*r+1⌉₊) * ⌈2*r+1/2⌉₊ * (2*⌈2*r+1/2⌉₊+1) := by
  have hsign : Fintype.card ReciprocalSign = 2 := by decide
  simp only [originCatalogueLabels, Finset.card_product, Nat.card_Icc, Nat.add_sub_cancel,
    Finset.card_univ, hsign, blockCatalogueLabels_card]
  ring

/-- Decode an origin using the actual sector scale and original phase definition. -/
def originCatalogueValue (R : ℕ+ → ℕ) (s : ℕ+ → ℝ)
    (o : ℕ × ReciprocalSign × ℕ × Bool × ℤ) : ℝ :=
  let i : ℕ+ := ⟨max o.1 1, by omega⟩
  labelScale s (i, o.2.1) * blockCatalogueAtom i (R i) o.2.2

/-- Every actual origin in a bounded window occurs in the gap-independent finite catalogue. -/
theorem sectorSet_subset_originCatalogue (R : ℕ+ → ℕ) (s : ℕ+ → ℝ)
    (hR : ∀ i : ℕ+, 2^(i : ℕ) ≤ R i) (hs : ∀ i, s i ∈ Icc (1 : ℝ) 2)
    (origin : Label) (r : ℝ) {x : ℝ}
    (hx : x ∈ sectorSet R s origin) (hxr : |x| ≤ r) :
    ∃ o ∈ originCatalogueLabels r,
      o.1 = origin.1.val ∧ o.2.1 = origin.2 ∧ originCatalogueValue R s o = x := by
  have hindex := meetingBlockIndices_subset_log R s hR hs r
    (show origin.1.val ∈ meetingBlockIndices R s r from
      ⟨origin.1.pos, origin.2, x, hx, abs_le.mp hxr⟩)
  obtain ⟨y, hy, hxy⟩ := hx
  have hscale := labelScale_mem_Icc s hs origin
  have hyabs : |y| ≤ 2*r := by
    have habs : |x| = labelScale s origin * |y| := by
      rw [← hxy, abs_mul, abs_of_nonneg (by linarith [hscale.1])]
    have := abs_nonneg y
    nlinarith [hscale.1]
  have hgap := linearGap_of_exponential R hR
  have hpoint := blockSet_Icc_subset_catalogue origin.1.pos
    (origin.1.pos.trans_le (hgap origin.1)) (2*r) ⟨hy, abs_le.mp hyabs⟩
  obtain ⟨v, hv, hvy⟩ := Finset.mem_image.mp hpoint
  refine ⟨(origin.1.val, origin.2, v), ?_, rfl, rfl, ?_⟩
  · simp only [originCatalogueLabels, Finset.mem_product, Finset.mem_Icc, Finset.mem_univ, true_and]
    exact ⟨hindex, hv⟩
  · have hi : (⟨max origin.1.val 1, by omega⟩ : ℕ+) = origin.1 := by
      apply Subtype.ext
      exact max_eq_left origin.1.pos
    simp only [originCatalogueValue, hi]
    rw [hvy]
    exact hxy

/-- Integer Fourier-shift tuples in a finite box, with exactly 2M reciprocal coordinates. -/
def prefixShiftCatalogue (M L : ℕ) : Finset (Fin M × ReciprocalSign → ℤ) :=
  Fintype.piFinset (fun _ => Finset.Icc (-(L : ℤ)) (L : ℤ))

theorem prefixShiftCatalogue_card (M L : ℕ) :
    (prefixShiftCatalogue M L).card = (2*L+1)^(2*M) := by
  have hsign : Fintype.card ReciprocalSign = 2 := by decide
  have hi : ((L : ℤ)+1+(L : ℤ)).toNat = 2*L+1 := by omega
  simp [prefixShiftCatalogue, Fintype.card_piFinset, Int.card_Icc, hi, hsign, mul_comm]

/-- A fixed source-compatible radius containing every origin that can approach a truncated target. -/
def comparisonOriginRadius (M L : ℕ) : ℕ := 6*(M+1)*(L+1)

/-- Actual prefix Fourier shifts have linear size in the truncation parameter. -/
theorem prefix_shift_abs_le (M L : ℕ) (k : Fin M × ReciprocalSign → ℤ)
    (hk : k ∈ prefixShiftCatalogue M L) (s : ℕ+ → ℝ) (hs : ∀ i, s i ∈ Icc (1 : ℝ) 2) :
    |reciprocalLaurentValue (fun i => (k (i, .forward) : ℝ))
      (fun i => (k (i, .reciprocal) : ℝ)) (fun i => s (prefixScaleIndex i))| ≤ 4*M*L := by
  have hkbound : ∀ label, |(k label : ℝ)| ≤ L := by
    intro label
    have hmem := Fintype.mem_piFinset.mp hk label
    have hint : -(L : ℤ) ≤ k label ∧ k label ≤ L := Finset.mem_Icc.mp hmem
    exact_mod_cast (abs_le.mpr hint)
  have hscale : ∀ i : Fin M, |s (prefixScaleIndex i)| ≤ 2 ∧ |(s (prefixScaleIndex i))⁻¹| ≤ 2 := by
    intro i
    have hf := labelScale_mem_Icc s hs (prefixScaleIndex i, .forward)
    have hr := labelScale_mem_Icc s hs (prefixScaleIndex i, .reciprocal)
    change s (prefixScaleIndex i) ∈ Icc (1/2 : ℝ) 2 at hf
    change (s (prefixScaleIndex i))⁻¹ ∈ Icc (1/2 : ℝ) 2 at hr
    constructor
    · rw [abs_of_nonneg (by linarith [hf.1])]; exact hf.2
    · rw [abs_of_nonneg (by linarith [hr.1])]; exact hr.2
  unfold reciprocalLaurentValue
  calc
    _ ≤ ∑ i : Fin M, |(k (i, .forward) : ℝ)*s (prefixScaleIndex i) +
        (k (i, .reciprocal) : ℝ)*(s (prefixScaleIndex i))⁻¹| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Fin M, (4 : ℝ)*L := by
      apply Finset.sum_le_sum
      intro i hi
      have ha := mul_le_mul (hkbound (i, .forward)) (hscale i).1 (abs_nonneg _) (by positivity : (0 : ℝ) ≤ L)
      have hb := mul_le_mul (hkbound (i, .reciprocal)) (hscale i).2 (abs_nonneg _) (by positivity : (0 : ℝ) ≤ L)
      have htri := abs_add_le ((k (i, .forward) : ℝ)*s (prefixScaleIndex i))
        ((k (i, .reciprocal) : ℝ)*(s (prefixScaleIndex i))⁻¹)
      rw [abs_mul, abs_mul] at htri
      linarith
    _ = 4*M*L := by simp; ring

/-- Any origin within distance one of a shifted catalogue target lies in the explicit bounded window. -/
theorem approaching_origin_abs_le (M L : ℕ) (target : Fin M × ReciprocalSign)
    (n : ℤ) (hn : |n| ≤ M) (β : ℝ) (hβ : |β| < 1/2)
    (k : Fin M × ReciprocalSign → ℤ) (hk : k ∈ prefixShiftCatalogue M L)
    (s : ℕ+ → ℝ) (hs : ∀ i, s i ∈ Icc (1 : ℝ) 2) (x : ℝ)
    (hnear : |scaleFactor target.2 (s (prefixScaleIndex target.1))*((n : ℝ)+β) - x -
      reciprocalLaurentValue (fun i => (k (i, .forward) : ℝ))
        (fun i => (k (i, .reciprocal) : ℝ)) (fun i => s (prefixScaleIndex i))| < 1) :
    |x| ≤ comparisonOriginRadius M L := by
  let shift := reciprocalLaurentValue (fun i => (k (i, .forward) : ℝ))
    (fun i => (k (i, .reciprocal) : ℝ)) (fun i => s (prefixScaleIndex i))
  let z := scaleFactor target.2 (s (prefixScaleIndex target.1))*((n : ℝ)+β)
  have hnreal : |(n : ℝ)| ≤ M := by exact_mod_cast hn
  have hscale := labelScale_mem_Icc s hs (prefixScaleIndex target.1, target.2)
  rw [labelScale_eq_scaleFactor] at hscale
  have hz : |z| ≤ 2*M+1 := by
    dsimp [z]
    rw [abs_mul, abs_of_nonneg (by linarith [hscale.1])]
    have hsum : |(n : ℝ)+β| ≤ (M : ℝ)+1/2 :=
      (abs_add_le _ _).trans (by linarith)
    have hmul := mul_le_mul hscale.2 hsum (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
    linarith
  have hshift : |shift| ≤ 4*M*L := prefix_shift_abs_le M L k hk s hs
  have heq : x = z-shift-(z-x-shift) := by ring
  have htri : |x| ≤ |z|+|shift|+|z-x-shift| := by
    calc
      |x| = |z-shift-(z-x-shift)| := congrArg abs heq
      _ ≤ |z-shift|+|z-x-shift| := abs_sub _ _
      _ ≤ |z|+|shift|+|z-x-shift| := add_le_add (abs_sub _ _) le_rfl
  change |z-x-shift| < 1 at hnear
  dsimp [comparisonOriginRadius]
  push_cast
  nlinarith [show (0 : ℝ) ≤ M by positivity, show (0 : ℝ) ≤ L by positivity]

/-- Finite catalogue of all target labels, signs and integer cells used at a fixed prefix stage. -/
def prefixTargetCatalogue (M : ℕ) : Finset (Fin M × Fin M × Bool × ReciprocalSign × ℤ) :=
  Finset.univ ×ˢ (Finset.univ ×ˢ (Finset.univ ×ˢ
    (Finset.univ ×ˢ Finset.Icc (-(M : ℤ)) (M : ℤ))))

theorem prefixTargetCatalogue_card (M : ℕ) :
    (prefixTargetCatalogue M).card = 4*M^2*(2*M+1) := by
  have hsign : Fintype.card ReciprocalSign = 2 := by decide
  have hi : ((M : ℤ)+1- -(M : ℤ)).toNat = 2*M+1 := by omega
  simp only [prefixTargetCatalogue, Finset.card_product, Finset.card_univ, Fintype.card_fin,
    Fintype.card_bool, hsign, Int.card_Icc, hi]
  ring

/-- All actual truncation comparisons sit in this explicit finite product catalogue. -/
def comparisonCatalogue (M L : ℕ) :=
  prefixTargetCatalogue M ×ˢ (prefixShiftCatalogue M L ×ˢ
    originCatalogueLabels (comparisonOriginRadius M L))

/-- Exact finite comparison count; radius, logarithm and shift dimension remain explicit. -/
theorem comparisonCatalogue_card (M L : ℕ) :
    (comparisonCatalogue M L).card =
      (4*M^2*(2*M+1)) * ((2*L+1)^(2*M) *
        (8*(Nat.log 2 ⌈2*(comparisonOriginRadius M L : ℝ)+1⌉₊)*
          ⌈2*(comparisonOriginRadius M L : ℝ)+1/2⌉₊*
          (2*⌈2*(comparisonOriginRadius M L : ℝ)+1/2⌉₊+1))) := by
  rw [comparisonCatalogue, Finset.card_product, Finset.card_product,
    prefixTargetCatalogue_card, prefixShiftCatalogue_card, originCatalogueLabels_card]

/-- The concrete parameter type of a comparison in the explicit finite catalogue. -/
abbrev ComparisonDescriptor (M : ℕ) :=
  (Fin M × Fin M × Bool × ReciprocalSign × ℤ) ×
    (Fin M × ReciprocalSign → ℤ) × (ℕ × ReciprocalSign × ℕ × Bool × ℤ)

/-- Positive originating block index decoded from the catalogue. -/
def descriptorOriginIndex {M : ℕ} (c : ComparisonDescriptor M) : ℕ+ :=
  ⟨max c.2.2.1 1, by omega⟩

/-- The actual origin phase in one catalogue comparison. -/
def descriptorOriginPhase {M : ℕ} (R : ℕ+ → ℕ) (c : ComparisonDescriptor M) : ℝ :=
  signedPhase c.2.2.2.2.2.1 (blockPhase (descriptorOriginIndex c) (R (descriptorOriginIndex c))
    ⟨max c.2.2.2.2.1 1, by omega⟩)

/-- Original source comparison decoded from a finite catalogue entry. -/
def descriptorComparisonValue {M : ℕ} (R : ℕ+ → ℕ) (c : ComparisonDescriptor M)
    (s : ℕ+ → ℝ) : ℝ :=
  prefixComparisonValue (c.1.1, c.1.2.2.2.1) (descriptorOriginIndex c, c.2.2.2.1)
    c.1.2.2.2.2 c.2.2.2.2.2.2
    (prefixCataloguePhase (fun i => R (prefixScaleIndex i)) (c.1.1, c.1.2.1, c.1.2.2.1))
    (descriptorOriginPhase R c) c.2.1 s

/-- Expected identity for the actual catalogue entry. -/
def descriptorExpected {M : ℕ} (R : ℕ+ → ℕ) (c : ComparisonDescriptor M) : Prop :=
  ExpectedPrefixComparison (c.1.1, c.1.2.2.2.1) (descriptorOriginIndex c, c.2.2.2.1)
    c.1.2.2.2.2 c.2.2.2.2.2.2
    (prefixCataloguePhase (fun i => R (prefixScaleIndex i)) (c.1.1, c.1.2.1, c.1.2.2.1))
    (descriptorOriginPhase R c) c.2.1

/-- Only unexpected actual comparisons count as bad events. -/
def descriptorBadEvent {M : ℕ} (R : ℕ+ → ℕ) (c : ComparisonDescriptor M) (u : ℝ) :
    Set (ℕ+ → ℝ) := {s | ¬ descriptorExpected R c ∧ |descriptorComparisonValue R c s| < u}

/-- The actual finite union of bad events at truncation L. -/
def catalogueBadEvent (R : ℕ+ → ℕ) (M L : ℕ) (u : ℝ) : Set (ℕ+ → ℝ) :=
  ⋃ c ∈ comparisonCatalogue M L, descriptorBadEvent R c u

/-- One common actual bound for all decoded entries, derived from the first M gaps only. -/
theorem exists_descriptor_sublevel_bound (M : ℕ) (R₀ : Fin M → ℕ) (hR₀ : ∀ i, 1 ≤ R₀ i) :
    ∃ d : ℝ, 0 < d ∧ ∀ R : ℕ+ → ℕ, (∀ i, R (prefixScaleIndex i) = R₀ i) →
      ∀ c : ComparisonDescriptor M, ∀ u : ℝ, 0 < u →
      scaleProbability (descriptorBadEvent R c u) ≤
        ENNReal.ofReal (16*((M+1 : ℕ) : ℝ)*((2^(M+1)*u)/min d 1)^
          ((1 : ℝ)/(2*((M+1 : ℕ) : ℝ)))) := by
  obtain ⟨d, hd, h⟩ := exists_actual_prefix_comparison_sublevel_bound M R₀ hR₀
  refine ⟨d, hd, ?_⟩
  intro R hext c u hu
  by_cases hex : descriptorExpected R c
  · have hempty : descriptorBadEvent R c u = ∅ := by ext s; simp [descriptorBadEvent, hex]
    simp only [hempty, measure_empty]
    exact bot_le
  · have horigin : (descriptorOriginIndex c, c.2.2.2.1) =
        (prefixScaleIndex c.1.1, c.1.2.2.2.1) →
        descriptorOriginPhase R c ∈ phaseSet (c.1.1.val+1) (R₀ c.1.1) := by
      intro heq
      have hi := congrArg (fun l : Label => l.1) heq
      change descriptorOriginIndex c = prefixScaleIndex c.1.1 at hi
      change signedPhase c.2.2.2.2.2.1 (blockPhase (descriptorOriginIndex c).val
        (R (descriptorOriginIndex c)) (⟨max c.2.2.2.2.1 1, by omega⟩ : ℕ+)) ∈ _
      rw [hi, hext]
      exact ⟨⟨max c.2.2.2.2.1 1, by omega⟩, c.2.2.2.2.2.1, rfl⟩
    have hRfun : (fun i => R (prefixScaleIndex i)) = R₀ := funext hext
    have hbound := h (c.1.1, c.1.2.2.2.1) c.1.2.1 c.1.2.2.1
      (descriptorOriginIndex c, c.2.2.2.1) c.1.2.2.2.2 c.2.2.2.2.2.2
      (descriptorOriginPhase R c) c.2.1 horigin
      (by simpa only [descriptorExpected, hRfun] using hex) u hu
    exact (measure_mono (show descriptorBadEvent R c u ⊆
      {s | |descriptorComparisonValue R c s| < u} from fun _ hs => hs.2)).trans
      (by simpa only [descriptorComparisonValue, hRfun] using hbound.trans (min_le_right _ _))

/-- Concrete catalogue union bound, uniform over every deterministic completion of the prefix. -/
theorem exists_catalogue_union_bound (M : ℕ) (R₀ : Fin M → ℕ) (hR₀ : ∀ i, 1 ≤ R₀ i) :
    ∃ d : ℝ, 0 < d ∧ ∀ R : ℕ+ → ℕ, (∀ i, R (prefixScaleIndex i) = R₀ i) →
      ∀ L : ℕ, ∀ u : ℝ, 0 < u →
      scaleProbability (catalogueBadEvent R M L u) ≤
        (comparisonCatalogue M L).card * ENNReal.ofReal (16*((M+1 : ℕ) : ℝ)*
          ((2^(M+1)*u)/min d 1)^((1 : ℝ)/(2*((M+1 : ℕ) : ℝ)))) := by
  obtain ⟨d, hd, h⟩ := exists_descriptor_sublevel_bound M R₀ hR₀
  refine ⟨d, hd, ?_⟩
  intro R hext L u hu
  calc
    _ ≤ ∑ c ∈ comparisonCatalogue M L, scaleProbability (descriptorBadEvent R c u) :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ _c ∈ comparisonCatalogue M L, ENNReal.ofReal (16*((M+1 : ℕ) : ℝ)*
        ((2^(M+1)*u)/min d 1)^((1 : ℝ)/(2*((M+1 : ℕ) : ℝ)))) :=
      Finset.sum_le_sum (fun c _ => h R hext c u hu)
    _ = _ := by simp

/-- A convenient cubic majorant of the sharper logarithmic origin count. -/
theorem originCatalogueLabels_card_le (T : ℕ) :
    (originCatalogueLabels (T : ℝ)).card ≤ 128*(T+1)^3 := by
  have hceil : ⌈2*(T : ℝ)+1⌉₊ = 2*T+1 := by
    have heq : 2*(T : ℝ)+1 = ((2*T+1 : ℕ) : ℝ) := by push_cast; ring
    rw [heq, Nat.ceil_natCast]
  have hN : ⌈2*(T : ℝ)+1/2⌉₊ ≤ 2*T+1 := by
    apply Nat.ceil_le.mpr
    push_cast
    linarith
  rw [originCatalogueLabels_card, hceil]
  calc
    _ ≤ 8*(2*T+1)*(2*T+1)*(2*(2*T+1)+1) := by
      gcongr
      exact Nat.log_le_self _ _
    _ ≤ 8*(2*(T+1))*(2*(T+1))*(4*(T+1)) := by gcongr <;> omega
    _ = 128*(T+1)^3 := by ring

/-- An explicit dimension-only count constant, independent of scale/gap data. -/
def catalogueCountConstant (M : ℕ) : ℕ :=
  (4*M^2*(2*M+1))*2^(2*M)*128*(7*(M+1))^3

/-- The actual finite comparison count has polynomial order 2M+3. -/
theorem comparisonCatalogue_card_le (M L : ℕ) :
    (comparisonCatalogue M L).card ≤ catalogueCountConstant M*(L+1)^(2*M+3) := by
  have hr : comparisonOriginRadius M L+1 ≤ 7*(M+1)*(L+1) := by
    dsimp [comparisonOriginRadius]
    nlinarith [Nat.zero_le (M*L)]
  have hshift : (2*L+1)^(2*M) ≤ (2*(L+1))^(2*M) := by
    apply Nat.pow_le_pow_left
    omega
  rw [comparisonCatalogue, Finset.card_product, Finset.card_product,
    prefixTargetCatalogue_card, prefixShiftCatalogue_card]
  calc
    _ ≤ (4*M^2*(2*M+1))*((2*(L+1))^(2*M)*(128*(7*(M+1)*(L+1))^3)) := by
      gcongr
      exact originCatalogueLabels_card_le _ |>.trans (by gcongr)
    _ = catalogueCountConstant M*(L+1)^(2*M+3) := by
      simp only [catalogueCountConstant, mul_pow, pow_add]
      ring

/-- The accepted distance power leaves three summable powers after the crude comparison count. -/
theorem catalogueDistanceExponent_balance (M : ℕ) :
    (catalogueDistanceExponent M : ℝ) / (2*((M+1 : ℕ) : ℝ)) - (2*M+3) = 3 := by
  unfold catalogueDistanceExponent
  push_cast
  have hm : (M : ℝ)+1 ≠ 0 := by positivity
  field_simp
  ring

/-- A positive power threshold parametrized for the exact accepted distance exponent. -/
def cataloguePowerThreshold (M : ℕ) (d t : ℝ) (L : ℕ) : ℝ :=
  (min d 1 / 2^(M+1)) * (t / (L+1 : ℕ)^(2*M+6))^(2*(M+1))

/-- This threshold is precisely a fixed positive constant times the accepted inverse power. -/
theorem cataloguePowerThreshold_eq (M L : ℕ) (d t : ℝ) :
    cataloguePowerThreshold M d t L =
      ((min d 1 / 2^(M+1))*t^(2*(M+1))) / (L+1 : ℕ)^(catalogueDistanceExponent M) := by
  unfold cataloguePowerThreshold catalogueDistanceExponent
  rw [div_pow, ← pow_mul]
  have heq : (2*M+6)*(2*(M+1)) = 2*(M+1)*(2*M+6) := Nat.mul_comm _ _
  rw [heq]
  ring

/-- Exact fractional-power simplification in the genuine catalogue probability bound. -/
theorem cataloguePowerThreshold_rate (M L : ℕ) (d t : ℝ) (hd : 0 < d) (ht : 0 < t) :
    ((2^(M+1)*cataloguePowerThreshold M d t L)/min d 1)^((1 : ℝ)/(2*((M+1 : ℕ) : ℝ))) =
      t / (L+1 : ℕ)^(2*M+6) := by
  have hD : min d 1 ≠ 0 := ne_of_gt (lt_min hd (by norm_num))
  have heq : (2^(M+1)*cataloguePowerThreshold M d t L)/min d 1 =
      (t / (L+1 : ℕ)^(2*M+6))^(2*(M+1)) := by
    unfold cataloguePowerThreshold
    field_simp
  rw [heq, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity : 0 ≤ t / (L+1 : ℕ)^(2*M+6))]
  have hexp : ((2*(M+1) : ℕ) : ℝ)*((1 : ℝ)/(2*((M+1 : ℕ) : ℝ))) = 1 := by
    push_cast
    have hm : (M : ℝ)+1 ≠ 0 := by positivity
    field_simp
  rw [hexp, Real.rpow_one]

/-- Actual truncated catalogue probability decays cubically at the accepted threshold. -/
theorem exists_catalogue_cubic_bound (M : ℕ) (R₀ : Fin M → ℕ) (hR₀ : ∀ i, 1 ≤ R₀ i) :
    ∃ d : ℝ, 0 < d ∧ ∀ R : ℕ+ → ℕ, (∀ i, R (prefixScaleIndex i) = R₀ i) →
      ∀ L : ℕ, ∀ t : ℝ, 0 < t →
      scaleProbability (catalogueBadEvent R M L (cataloguePowerThreshold M d t L)) ≤
        ENNReal.ofReal ((catalogueCountConstant M : ℝ)*16*(M+1)*t / (L+1 : ℕ)^3) := by
  obtain ⟨d, hd, h⟩ := exists_catalogue_union_bound M R₀ hR₀
  refine ⟨d, hd, ?_⟩
  intro R hext L t ht
  have hu : 0 < cataloguePowerThreshold M d t L := by
    unfold cataloguePowerThreshold
    have hD := lt_min hd (by norm_num : (0 : ℝ) < 1)
    positivity
  have hbound := h R hext L (cataloguePowerThreshold M d t L) hu
  rw [cataloguePowerThreshold_rate M L d t hd ht] at hbound
  have hcard : ((comparisonCatalogue M L).card : ℝ) ≤
      catalogueCountConstant M*(L+1 : ℕ)^(2*M+3) := by exact_mod_cast comparisonCatalogue_card_le M L
  calc
    _ ≤ (comparisonCatalogue M L).card * ENNReal.ofReal
        (16*((M+1 : ℕ) : ℝ)*(t/(L+1 : ℕ)^(2*M+6))) := hbound
    _ = ENNReal.ofReal (((comparisonCatalogue M L).card : ℝ)*
        (16*((M+1 : ℕ) : ℝ)*(t/(L+1 : ℕ)^(2*M+6)))) := by
      symm
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal ((catalogueCountConstant M*(L+1 : ℕ)^(2*M+3))*
        (16*((M+1 : ℕ) : ℝ)*(t/(L+1 : ℕ)^(2*M+6)))) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcard (by positivity))
    _ = _ := by
      congr 1
      have hexp : 2*M+6 = (2*M+3)+3 := by omega
      rw [hexp, pow_add]
      push_cast
      field_simp
      ring

/-- Union of the actual bad catalogues over the source's dyadic truncation scales. -/
def dyadicCatalogueBadEvent (R : ℕ+ → ℕ) (M : ℕ) (c : ℝ) : Set (ℕ+ → ℝ) :=
  ⋃ n : ℕ, catalogueBadEvent R M (2^n) (c / (2^n+1 : ℕ)^(catalogueDistanceExponent M))

/-- The actual dyadic union has a summable bound with constants fixed by the finite prefix. -/
theorem exists_dyadic_catalogue_bound (M : ℕ) (R₀ : Fin M → ℕ) (hR₀ : ∀ i, 1 ≤ R₀ i) :
    ∃ d : ℝ, 0 < d ∧ ∀ R : ℕ+ → ℕ, (∀ i, R (prefixScaleIndex i) = R₀ i) →
      ∀ t : ℝ, 0 < t →
      scaleProbability (dyadicCatalogueBadEvent R M ((min d 1/2^(M+1))*t^(2*(M+1)))) ≤
        ENNReal.ofReal (2*((catalogueCountConstant M : ℝ)*16*(M+1))*t) := by
  obtain ⟨d, hd, h⟩ := exists_catalogue_cubic_bound M R₀ hR₀
  refine ⟨d, hd, ?_⟩
  intro R hext t ht
  let K : ℝ := (catalogueCountConstant M : ℝ)*16*(M+1)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hterm : ∀ n : ℕ,
      scaleProbability (catalogueBadEvent R M (2^n)
        (((min d 1/2^(M+1))*t^(2*(M+1))) / (2^n+1 : ℕ)^(catalogueDistanceExponent M))) ≤
      ENNReal.ofReal ((K*t)*((1 : ℝ)/2)^n) := by
    intro n
    have hb := h R hext (2^n) t ht
    rw [cataloguePowerThreshold_eq] at hb
    apply hb.trans
    apply ENNReal.ofReal_le_ofReal
    have hden : (2 : ℝ)^n ≤ ((2^n+1 : ℕ) : ℝ)^3 := by
      push_cast
      have hpos : 0 ≤ (2 : ℝ)^n := by positivity
      have hcube : 0 ≤ ((2 : ℝ)^n)^3 := by positivity
      nlinarith [sq_nonneg ((2 : ℝ)^n)]
    calc
      _ ≤ (K*t)/(2 : ℝ)^n := div_le_div_of_nonneg_left (mul_nonneg hK ht.le) (by positivity) hden
      _ = (K*t)*((1 : ℝ)/2)^n := by rw [div_pow, one_pow]; ring
  calc
    _ ≤ ∑' n : ℕ, scaleProbability (catalogueBadEvent R M (2^n)
        (((min d 1/2^(M+1))*t^(2*(M+1))) / (2^n+1 : ℕ)^(catalogueDistanceExponent M))) :=
      measure_iUnion_le _
    _ ≤ ∑' n : ℕ, ENNReal.ofReal ((K*t)*((1 : ℝ)/2)^n) := ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal (2*K*t) := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
        (summable_geometric_two.mul_left (K*t)), tsum_mul_left, tsum_geometric_two]
      congr 1
      ring

/-- A single prefix-only positive distance constant attains any prescribed failure budget. -/
theorem exists_prefix_nonresonance_failure_bound (M : ℕ) (R₀ : Fin M → ℕ)
    (hR₀ : ∀ i, 1 ≤ R₀ i) (ε : ℝ) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ R : ℕ+ → ℕ,
      (∀ i, R (prefixScaleIndex i) = R₀ i) →
      scaleProbability (dyadicCatalogueBadEvent R M c) ≤ ENNReal.ofReal ε := by
  obtain ⟨d, hd, h⟩ := exists_dyadic_catalogue_bound M R₀ hR₀
  let K : ℝ := (catalogueCountConstant M : ℝ)*16*(M+1)
  let t : ℝ := min ε 1 / (2*K+1)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have ht : 0 < t := div_pos (lt_min hε (by norm_num)) (by positivity)
  have ht1 : t ≤ 1 := by
    apply (div_le_iff₀ (by positivity : 0 < 2*K+1)).mpr
    have := min_le_right ε 1
    linarith
  let c : ℝ := (min d 1/2^(M+1))*t^(2*(M+1))
  have hc : 0 < c := by
    dsimp [c]
    have := lt_min hd (by norm_num : (0 : ℝ) < 1)
    positivity
  have hc1 : c ≤ 1 := by
    have hpow : t^(2*(M+1)) ≤ 1 := pow_le_one₀ ht.le ht1
    have hD : min d 1/2^(M+1) ≤ 1 := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2^(M+1))).mpr
      have htwo : (1 : ℝ) ≤ 2^(M+1) := one_le_pow₀ (by norm_num)
      have := min_le_right d 1
      linarith
    dsimp [c]
    nlinarith [show 0 ≤ min d 1/2^(M+1) by have := lt_min hd (by norm_num : (0 : ℝ) < 1); positivity]
  refine ⟨c, hc, hc1, ?_⟩
  intro R hext
  apply (h R hext t ht).trans
  apply ENNReal.ofReal_le_ofReal
  have heq : t*(2*K+1) = min ε 1 := by dsimp [t]; field_simp
  have := min_le_left ε 1
  change 2*K*t ≤ ε
  nlinarith

/-- The exact failure budget used at prefix stage M in the accepted construction. -/
theorem exists_prefix_nonresonance_stage_bound (M : ℕ) (R₀ : Fin M → ℕ)
    (hR₀ : ∀ i, 1 ≤ R₀ i) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ R : ℕ+ → ℕ,
      (∀ i, R (prefixScaleIndex i) = R₀ i) →
      scaleProbability (dyadicCatalogueBadEvent R M c) ≤ ENNReal.ofReal ((2 : ℝ)^(-(M+4 : ℤ))) :=
  exists_prefix_nonresonance_failure_bound M R₀ hR₀ _ (by positivity)

/-- The literal labels of every retained atom lie in the finite origin catalogue. -/
theorem actual_origin_descriptor_mem (R : ℕ+ → ℕ) (s : ℕ+ → ℝ)
    (hR : ∀ i : ℕ+, 2^(i : ℕ) ≤ R i) (hs : ∀ i, s i ∈ Icc (1 : ℝ) 2)
    (origin : Label) (j : ℕ+) (positive : Bool) (n : ℤ)
    (hcell : cellThreshold (R origin.1) j ≤ n.natAbs) (r : ℝ)
    (hxr : |labelScale s origin*((n : ℝ)+signedPhase positive (blockPhase origin.1 (R origin.1) j))| ≤ r) :
    (origin.1.val, origin.2, j.val, positive, n) ∈ originCatalogueLabels r := by
  let y := (n : ℝ)+signedPhase positive (blockPhase origin.1 (R origin.1) j)
  let x := labelScale s origin*y
  have hx : x ∈ sectorSet R s origin := ⟨y, ⟨j, positive, n, hcell, rfl⟩, rfl⟩
  have hindex := meetingBlockIndices_subset_log R s hR hs r
    (show origin.1.val ∈ meetingBlockIndices R s r from
      ⟨origin.1.pos, origin.2, x, hx, abs_le.mp hxr⟩)
  have hgrowth := linearGap_of_exponential R hR
  have hphase := abs_signedPhase_lt_half origin.1.pos
    (origin.1.pos.trans_le (hgrowth origin.1)) j positive
  have hscale := labelScale_mem_Icc s hs origin
  have hyabs : |y| ≤ 2*r := by
    have habs : |x| = labelScale s origin * |y| := by
      dsimp [x]
      rw [abs_mul, abs_of_nonneg (by linarith [hscale.1])]
    have hxr' : |x| ≤ r := hxr
    nlinarith [hscale.1, abs_nonneg y]
  have hnreal : |(n : ℝ)| < 2*r+1/2 := by
    have htri := abs_sub y (signedPhase positive (blockPhase origin.1 (R origin.1) j))
    have heq : y-signedPhase positive (blockPhase origin.1 (R origin.1) j) = n := by dsimp [y]; ring
    rw [heq] at htri
    linarith
  have hnreal' : |(n : ℝ)| ≤ (⌈2*r+1/2⌉₊ : ℝ) := hnreal.le.trans (Nat.le_ceil _)
  have hnabs : n.natAbs ≤ ⌈2*r+1/2⌉₊ := by
    have hcast : (n.natAbs : ℝ) ≤ (⌈2*r+1/2⌉₊ : ℝ) := by simpa using hnreal'
    exact_mod_cast hcast
  have hj := (phaseIndex_le_twice_cell j n hcell).trans (Nat.mul_le_mul_left 2 hnabs)
  have hncells : -(⌈2*r+1/2⌉₊ : ℤ) ≤ n ∧ n ≤ (⌈2*r+1/2⌉₊ : ℤ) := by
    obtain ⟨hlo, hhi⟩ := abs_le.mp hnreal'
    exact ⟨by exact_mod_cast hlo, by exact_mod_cast hhi⟩
  simp only [originCatalogueLabels, blockCatalogueLabels, Finset.mem_product,
    Finset.mem_Icc, Finset.mem_univ, true_and]
  exact ⟨hindex, ⟨⟨j.pos, hj⟩, hncells⟩⟩

/-- Every genuinely small, unexpected source comparison occurs in the enumerated bad event. -/
theorem actual_bad_comparison_mem_catalogue (R : ℕ+ → ℕ) (M L : ℕ)
    (hR : ∀ i : ℕ+, 2^(i : ℕ) ≤ R i) (s : ℕ+ → ℝ) (hs : ∀ i, s i ∈ Icc (1 : ℝ) 2)
    (target : Fin M × ReciprocalSign) (j : Fin M) (positive : Bool) (n : ℤ) (hn : |n| ≤ M)
    (origin : Label) (j' : ℕ+) (positive' : Bool) (n' : ℤ)
    (hcell : cellThreshold (R origin.1) j' ≤ n'.natAbs)
    (k : Fin M × ReciprocalSign → ℤ) (hk : k ∈ prefixShiftCatalogue M L)
    (u : ℝ) (hu : u ≤ 1)
    (hbad : ¬ ExpectedPrefixComparison target origin n n'
      (prefixCataloguePhase (fun i => R (prefixScaleIndex i)) (target.1, j, positive))
      (signedPhase positive' (blockPhase origin.1 (R origin.1) j')) k)
    (hsmall : |prefixComparisonValue target origin n n'
      (prefixCataloguePhase (fun i => R (prefixScaleIndex i)) (target.1, j, positive))
      (signedPhase positive' (blockPhase origin.1 (R origin.1) j')) k s| < u) :
    s ∈ catalogueBadEvent R M L u := by
  let β := prefixCataloguePhase (fun i => R (prefixScaleIndex i)) (target.1, j, positive)
  let β' := signedPhase positive' (blockPhase origin.1 (R origin.1) j')
  have hgrowth := linearGap_of_exponential R hR
  have hβ : |β| < 1/2 := abs_signedPhase_lt_half (Nat.succ_le_succ (Nat.zero_le _))
    ((prefixScaleIndex target.1).pos.trans_le (hgrowth _)) _ _
  have hnear : |scaleFactor target.2 (s (prefixScaleIndex target.1))*((n : ℝ)+β) -
      labelScale s origin*((n' : ℝ)+β') - reciprocalLaurentValue
        (fun i => (k (i, .forward) : ℝ)) (fun i => (k (i, .reciprocal) : ℝ))
        (fun i => s (prefixScaleIndex i))| < 1 := hsmall.trans_le hu
  have hr := approaching_origin_abs_le M L target n hn β hβ k hk s hs _ hnear
  have ho := actual_origin_descriptor_mem R s hR hs origin j' positive' n' hcell _ hr
  let c : ComparisonDescriptor M :=
    ((target.1, j, positive, target.2, n), k, (origin.1.val, origin.2, j'.val, positive', n'))
  have hc : c ∈ comparisonCatalogue M L := by
    simp only [comparisonCatalogue, c, Finset.mem_product]
    refine ⟨?_, hk, ho⟩
    simpa only [prefixTargetCatalogue, Finset.mem_product, Finset.mem_univ, true_and,
      Finset.mem_Icc] using abs_le.mp hn
  have hi : descriptorOriginIndex c = origin.1 := by
    apply Subtype.ext
    exact max_eq_left origin.1.pos
  have hj' : (⟨max j'.val 1, by omega⟩ : ℕ+) = j' := by
    apply Subtype.ext
    exact max_eq_left j'.pos
  have hphase : descriptorOriginPhase R c = β' := by
    change signedPhase positive' (blockPhase (descriptorOriginIndex c).val
      (R (descriptorOriginIndex c)) (⟨max j'.val 1, by omega⟩ : ℕ+)) = β'
    rw [hi, hj']
  apply Set.mem_iUnion.mpr
  refine ⟨c, Set.mem_iUnion.mpr ⟨hc, ?_⟩⟩
  change ¬ descriptorExpected R c ∧ |descriptorComparisonValue R c s| < u
  simpa only [descriptorExpected, descriptorComparisonValue, hi, hphase] using And.intro hbad hsmall

/-- Full actual comparison inequalities on a fixed scale sequence at every dyadic truncation. -/
def ActualPrefixNonresonance (R : ℕ+ → ℕ) (M : ℕ) (c : ℝ) (s : ℕ+ → ℝ) : Prop :=
  ∀ ℓ : ℕ, ∀ target : Fin M × ReciprocalSign, ∀ j : Fin M, ∀ positive : Bool,
    ∀ n : ℤ, |n| ≤ M → ∀ origin : Label, ∀ j' : ℕ+, ∀ positive' : Bool, ∀ n' : ℤ,
    cellThreshold (R origin.1) j' ≤ n'.natAbs →
    ∀ k : Fin M × ReciprocalSign → ℤ, k ∈ prefixShiftCatalogue M (2^ℓ) →
    ¬ ExpectedPrefixComparison target origin n n'
      (prefixCataloguePhase (fun i => R (prefixScaleIndex i)) (target.1, j, positive))
      (signedPhase positive' (blockPhase origin.1 (R origin.1) j')) k →
    c / (2^ℓ+1 : ℕ)^(catalogueDistanceExponent M) ≤
      |prefixComparisonValue target origin n n'
        (prefixCataloguePhase (fun i => R (prefixScaleIndex i)) (target.1, j, positive))
        (signedPhase positive' (blockPhase origin.1 (R origin.1) j')) k s|

/-- The complement of the actual countable bad-event union gives all required source comparisons. -/
theorem actualPrefixNonresonance_of_not_bad (R : ℕ+ → ℕ) (M : ℕ)
    (hR : ∀ i : ℕ+, 2^(i : ℕ) ≤ R i) (c : ℝ) (_hc : 0 < c) (hc1 : c ≤ 1)
    (s : ℕ+ → ℝ) (hs : ∀ i, s i ∈ Icc (1 : ℝ) 2)
    (hgood : s ∉ dyadicCatalogueBadEvent R M c) : ActualPrefixNonresonance R M c s := by
  intro ℓ target j positive n hn origin j' positive' n' hcell k hk hbad
  by_contra hlt
  have hsmall := lt_of_not_ge hlt
  have hule : c / (2^ℓ+1 : ℕ)^(catalogueDistanceExponent M) ≤ 1 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (2^ℓ+1 : ℕ)^(catalogueDistanceExponent M))).mpr
    have hbase : (1 : ℝ) ≤ (2^ℓ+1 : ℕ) := by exact_mod_cast (show (1 : ℕ) ≤ 2^ℓ+1 from Nat.succ_le_succ (Nat.zero_le _))
    have := one_le_pow₀ (n := catalogueDistanceExponent M) hbase
    linarith
  have hmem := actual_bad_comparison_mem_catalogue R M (2^ℓ) hR s hs target j positive n hn
    origin j' positive' n' hcell k hk _ hule hbad hsmall
  exact hgood (Set.mem_iUnion.mpr ⟨ℓ, hmem⟩)

/-- Actual source nonresonance with the prescribed failure budget and prefix-only radius constant. -/
theorem exists_actual_prefix_nonresonance (M : ℕ) (R₀ : Fin M → ℕ) (hR₀ : ∀ i, 1 ≤ R₀ i) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ R : ℕ+ → ℕ,
      (∀ i, R (prefixScaleIndex i) = R₀ i) → (∀ i : ℕ+, 2^(i : ℕ) ≤ R i) →
      scaleProbability {s | ¬ ActualPrefixNonresonance R M c s} ≤
        ENNReal.ofReal ((2 : ℝ)^(-(M+4 : ℤ))) := by
  obtain ⟨c, hc, hc1, h⟩ := exists_prefix_nonresonance_stage_bound M R₀ hR₀
  refine ⟨c, hc, hc1, ?_⟩
  intro R hext hR
  apply (show scaleProbability {s | ¬ ActualPrefixNonresonance R M c s} ≤
    scaleProbability (dyadicCatalogueBadEvent R M c) from ?_).trans (h R hext)
  apply measure_mono_ae
  filter_upwards [ae_all_scales_mem] with s hs
  intro hnot
  by_contra hgood
  exact hnot (actualPrefixNonresonance_of_not_bad R M hR c hc hc1 s hs hgood)

/-- Good-event probability form of the same literal source comparisons. -/
theorem exists_actual_prefix_good_event (M : ℕ) (R₀ : Fin M → ℕ) (hR₀ : ∀ i, 1 ≤ R₀ i) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ R : ℕ+ → ℕ,
      (∀ i, R (prefixScaleIndex i) = R₀ i) → (∀ i : ℕ+, 2^(i : ℕ) ≤ R i) →
      1 - ENNReal.ofReal ((2 : ℝ)^(-(M+4 : ℤ))) ≤
        scaleProbability {s | ActualPrefixNonresonance R M c s} := by
  obtain ⟨c, hc, hc1, h⟩ := exists_actual_prefix_nonresonance M R₀ hR₀
  refine ⟨c, hc, hc1, ?_⟩
  intro R hext hR
  apply tsub_le_iff_right.mpr
  calc
    1 = scaleProbability (Set.univ : Set (ℕ+ → ℝ)) := measure_univ.symm
    _ = scaleProbability ({s | ActualPrefixNonresonance R M c s} ∪
        {s | ¬ ActualPrefixNonresonance R M c s}) := by congr 1; ext s; simp only [Set.mem_univ, Set.mem_union, Set.mem_ofPred_eq, true_iff]; exact Classical.em _
    _ ≤ scaleProbability {s | ActualPrefixNonresonance R M c s} +
        scaleProbability {s | ¬ ActualPrefixNonresonance R M c s} := measure_union_le _ _
    _ ≤ _ := add_le_add le_rfl (h R hext hR)

end
end MeyerGeneralProblem.Adaptive
