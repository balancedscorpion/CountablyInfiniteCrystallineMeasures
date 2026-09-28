module

public import MeyerGeneralProblem.Cardinal.Adaptive.Definitions
public import MeyerGeneralProblem.Carrier.LocallyFinite
public import MeyerGeneralProblem.Carrier.Dilation
public import MeyerGeneralProblem.Distribution.EscapingCombCarriers

@[expose] public section

/-!
# Geometry of the actual adaptive reciprocal carrier

The formulas are those of the accepted high-order surgery and adaptive
exhaustion sources. These results concern actual atoms, not full periodic
closures, and make no assertion about construction or exhaustion of Meyer
sources. The original cell schedule is retained in local-finiteness proofs.
-/

namespace MeyerGeneralProblem.Adaptive

noncomputable section

/-- A positive central gap has a nonempty matched head. -/
theorem headLength_pos {R : ℕ} (hR : 1 ≤ R) : 0 < headLength R := by
  unfold headLength
  omega

/-- The rapid-tail base is strictly larger than one at positive native order. -/
theorem rapidBase_one_lt {P : ℕ} (hP : 1 ≤ P) : 1 < rapidBase P := by
  have hP' : (0 : ℝ) < P := by exact_mod_cast hP
  unfold rapidBase
  have hpos : (0 : ℝ) < 1 / (6 * (P : ℝ)) := by positivity
  linarith

/-- The fixed rapid scale exceeds one for a positive gap. -/
theorem rapidScale_one_lt {R : ℕ} (hR : 1 ≤ R) : 1 < rapidScale R := by
  have hhead : (1 : ℝ) ≤ headLength R := by exact_mod_cast headLength_pos hR
  unfold rapidScale
  nlinarith

/-- The original rapid exponent has positive decay at positive parameters. -/
theorem rapidDecay_pos {P R : ℕ} (hP : 1 ≤ P) (hR : 1 ≤ R) :
    0 < rapidDecay P R := by
  have hP' : (0 : ℝ) < P := by exact_mod_cast hP
  exact mul_pos (by positivity) (Real.log_pos (rapidScale_one_lt hR))

/-- Every rapid distance is strictly positive and at most its original prefactor. -/
theorem rapidDistance_bounds {P R : ℕ} (hP : 1 ≤ P) (hR : 1 ≤ R) (i : ℕ) :
    0 < rapidDistance P R i ∧ rapidDistance P R i ≤ 1 / 16 := by
  have hb : 0 < rapidBase P := lt_trans zero_lt_one (rapidBase_one_lt hP)
  have hd : 0 < rapidDecay P R := rapidDecay_pos hP hR
  have he : Real.exp (-(rapidDecay P R) * rapidBase P ^ i) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hd.le) (pow_nonneg hb.le _)
  unfold rapidDistance
  constructor
  · positivity
  · linarith

/-- Both head and tail phases lie strictly inside the positive half-cell. -/
theorem blockPhase_mem_Ioo {P R : ℕ} (hP : 1 ≤ P) (hR : 1 ≤ R) (j : ℕ+) :
    blockPhase P R j ∈ Set.Ioo (0 : ℝ) (1 / 2) := by
  have hh : (0 : ℝ) < headLength R := by exact_mod_cast headLength_pos hR
  have hj : (1 : ℝ) ≤ (j : ℕ) := by exact_mod_cast j.pos
  unfold blockPhase
  split_ifs with h
  · have hjh : ((j : ℕ) : ℝ) ≤ headLength R := by exact_mod_cast h
    constructor
    · apply div_pos <;> linarith
    · apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 4 * headLength R)).mpr
      linarith
  · obtain ⟨hpos, hle⟩ := rapidDistance_bounds hP hR ((j : ℕ) - headLength R)
    constructor <;> linarith

/-- The signed phase remains strictly within half a cell of its integer centre. -/
theorem abs_signedPhase_lt_half {P R : ℕ} (hP : 1 ≤ P) (hR : 1 ≤ R)
    (j : ℕ+) (positive : Bool) :
    |signedPhase positive (blockPhase P R j)| < 1 / 2 := by
  have h := blockPhase_mem_Ioo hP hR j
  cases positive <;> simpa only [signedPhase, Bool.false_eq_true, ite_false,
    ite_true, abs_neg, abs_of_pos h.1] using h.2

/-- All admissible head and tail cells lie outside the central gap. -/
theorem gap_le_cellThreshold {R : ℕ} (hR : 1 ≤ R) (j : ℕ+) :
    R ≤ cellThreshold R j := by
  unfold cellThreshold headLength
  split_ifs <;> omega

/-- Every actual atom lies beyond the strict original central half-cell gap. -/
theorem blockSet_central_gap {P R : ℕ} (hP : 1 ≤ P) (hR : 1 ≤ R)
    {x : ℝ} (hx : x ∈ blockSet P R) : (R : ℝ) - 1 / 2 < |x| := by
  rcases hx with ⟨j, positive, n, hn, rfl⟩
  have hRnat : R ≤ n.natAbs := (gap_le_cellThreshold hR j).trans hn
  have hRreal : (R : ℝ) ≤ |(n : ℝ)| := by
    simpa using (show (R : ℝ) ≤ (n.natAbs : ℝ) by exact_mod_cast hRnat)
  have hphase := abs_signedPhase_lt_half hP hR j positive
  have hrev := abs_sub_le (n : ℝ)
    ((n : ℝ) + signedPhase positive (blockPhase P R j)) 0
  simp only [sub_add_cancel_left, sub_zero, abs_neg] at hrev
  linarith

/-- A bounded interval meets only finitely many actual scheduled atoms. -/
theorem blockSet_finite_inter_Icc {P R : ℕ} (hP : 1 ≤ P) (hR : 1 ≤ R)
    (a b : ℝ) : (blockSet P R ∩ Set.Icc a b).Finite := by
  obtain ⟨N : ℕ, hN⟩ := exists_nat_gt (max |a| |b| + 1)
  let K : ℕ := max (headLength R) N
  let f : ℕ × Bool × ℤ → ℝ := fun q =>
    (q.2.2 : ℝ) + signedPhase q.2.1 (blockPhase P R ⟨max q.1 1, by omega⟩)
  have hfinite : ((Set.Icc 1 K) ×ˢ ((Set.univ : Set Bool) ×ˢ
      Set.Icc (-(N : ℤ)) (N : ℤ))).Finite :=
    (Set.finite_Icc 1 K).prod (Set.finite_univ.prod (Set.finite_Icc _ _))
  apply (hfinite.image f).subset
  rintro x ⟨⟨j, positive, n, hn, hx⟩, hxa, hxb⟩
  have hxabs : |x| ≤ max |a| |b| := by
    apply abs_le.mpr
    constructor
    · have ha := neg_abs_le a
      have hamax := le_max_left |a| |b|
      linarith
    · exact hxb.trans ((le_abs_self b).trans (le_max_right |a| |b|))
  have hphase := abs_signedPhase_lt_half hP hR j positive
  have hnreal : |(n : ℝ)| < N := by
    have htri := abs_sub_le (n : ℝ) x 0
    rw [hx] at htri
    simp only [sub_add_cancel_left, sub_zero, abs_neg] at htri
    rw [← hx] at htri
    linarith
  have hnabs : n.natAbs ≤ N := by
    have hnreal' : |(n : ℝ)| ≤ N := hnreal.le
    have hc : (n.natAbs : ℝ) ≤ N := by simpa using hnreal'
    exact_mod_cast hc
  have hjK : (j : ℕ) ≤ K := by
    by_cases hjhead : (j : ℕ) ≤ headLength R
    · exact hjhead.trans (Nat.le_max_left _ _)
    · have hjn : (j : ℕ) ≤ n.natAbs := by simpa [cellThreshold, hjhead] using hn
      exact (hjn.trans hnabs).trans (Nat.le_max_right _ _)
  refine ⟨((j : ℕ), positive, n), ⟨⟨j.pos, hjK⟩, Set.mem_univ _, ?_⟩, ?_⟩
  · have hnle : |(n : ℝ)| ≤ N := hnreal.le
    obtain ⟨hlo, hhi⟩ := abs_le.mp hnle
    constructor
    · exact_mod_cast hlo
    · exact_mod_cast hhi
  · have hjrec : (⟨max (j : ℕ) 1, by omega⟩ : ℕ+) = j := by
      apply Subtype.ext
      exact Nat.max_eq_left j.pos
    change (n : ℝ) + signedPhase positive (blockPhase P R _) = x
    rw [hjrec]
    exact hx.symm

/-- The literal scheduled block, packaged as a genuine locally finite carrier. -/
def blockCarrier (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) : LocallyFiniteCarrier where
  carrier := blockSet P R
  finite_inter_Icc := blockSet_finite_inter_Icc hP hR

@[simp] theorem blockCarrier_carrier (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) :
    (blockCarrier P R hP hR).carrier = blockSet P R := rfl

/-- Both reciprocal scales lie in the compact scale interval used by the proof. -/
theorem labelScale_mem_Icc (s : ℕ+ → ℝ) (hs : ∀ i, s i ∈ Set.Icc (1 : ℝ) 2)
    (b : Label) : labelScale s b ∈ Set.Icc (1 / 2 : ℝ) 2 := by
  rcases b with ⟨i, σ⟩
  obtain ⟨hlo, hhi⟩ := hs i
  have hp : 0 < s i := lt_of_lt_of_le zero_lt_one hlo
  cases σ with
  | forward =>
      change 1 / 2 ≤ s i ∧ s i ≤ 2
      constructor <;> linarith
  | reciprocal =>
      change 1 / 2 ≤ (s i)⁻¹ ∧ (s i)⁻¹ ≤ 2
      rw [inv_eq_one_div]
      constructor
      · apply (le_div_iff₀ hp).mpr
        linarith
      · apply (div_le_iff₀ hp).mpr
        linarith

/-- Every actual reciprocal scale is positive. -/
theorem labelScale_pos (s : ℕ+ → ℝ) (hs : ∀ i, s i ∈ Set.Icc (1 : ℝ) 2)
    (b : Label) : 0 < labelScale s b :=
  lt_of_lt_of_le (by norm_num) (labelScale_mem_Icc s hs b).1

/-- Each literal reciprocal sector is locally finite. -/
def sectorCarrier (R : ℕ+ → ℕ) (s : ℕ+ → ℝ)
    (hR : ∀ i, 1 ≤ R i) (hs : ∀ i, s i ∈ Set.Icc (1 : ℝ) 2)
    (b : Label) : LocallyFiniteCarrier :=
  (blockCarrier b.1 (R b.1) b.1.pos (hR b.1)).dilate (labelScale s b)
    (labelScale_pos s hs b)

@[simp] theorem sectorCarrier_carrier (R : ℕ+ → ℕ) (s : ℕ+ → ℝ)
    (hR : ∀ i, 1 ≤ R i) (hs : ∀ i, s i ∈ Set.Icc (1 : ℝ) 2) (b : Label) :
    (sectorCarrier R s hR hs b).carrier = sectorSet R s b := rfl

/-- A uniform lower scale bound preserves an escaping central gap. -/
theorem sectorSet_central_gap (R : ℕ+ → ℕ) (s : ℕ+ → ℝ)
    (hR : ∀ i, 1 ≤ R i) (hs : ∀ i, s i ∈ Set.Icc (1 : ℝ) 2)
    (b : Label) {x : ℝ} (hx : x ∈ sectorSet R s b) :
    ((R b.1 : ℝ) - 1 / 2) / 2 < |x| := by
  rcases hx with ⟨y, hy, rfl⟩
  have hygap := blockSet_central_gap b.1.pos (hR b.1) hy
  have hscale := (labelScale_mem_Icc s hs b).1
  have hprod := mul_le_mul_of_nonneg_right hscale (abs_nonneg y)
  rw [abs_mul, abs_of_pos (labelScale_pos s hs b)]
  nlinarith

/-- The two actual directions of one block, before forming the escaping union. -/
def reciprocalBlockCarrier (R : ℕ+ → ℕ) (s : ℕ+ → ℝ)
    (hR : ∀ i, 1 ≤ R i) (hs : ∀ i, s i ∈ Set.Icc (1 : ℝ) 2)
    (i : ℕ+) : LocallyFiniteCarrier :=
  (sectorCarrier R s hR hs (i, .forward)).union
    (sectorCarrier R s hR hs (i, .reciprocal))

/-- Linear growth of the gap already suffices for local finiteness of the union. -/
theorem reciprocalBlockCarrier_escape (R : ℕ+ → ℕ) (s : ℕ+ → ℝ)
    (hR : ∀ i : ℕ+, (i : ℕ) ≤ R i) (hs : ∀ i, s i ∈ Set.Icc (1 : ℝ) 2) :
    ∀ a b : ℝ, ∃ N : ℕ, ∀ t, N ≤ t →
      (reciprocalBlockCarrier R s (fun i => i.pos.trans_le (hR i)) hs
        ⟨t+1, Nat.succ_pos t⟩).carrier ∩ Set.Icc a b = ∅ := by
  intro a b
  obtain ⟨N : ℕ, hN⟩ := exists_nat_gt (2 * max |a| |b| + 1)
  refine ⟨N, ?_⟩
  intro t ht
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro x ⟨hx, hxa, hxb⟩
  have hxabs : |x| ≤ max |a| |b| := by
    apply abs_le.mpr
    constructor
    · have ha := neg_abs_le a
      have hamax := le_max_left |a| |b|
      linarith
    · exact hxb.trans ((le_abs_self b).trans (le_max_right |a| |b|))
  have hgap : ((R ⟨t+1, Nat.succ_pos t⟩ : ℝ) - 1 / 2) / 2 < |x| := by
    rcases hx with hx | hx
    · exact sectorSet_central_gap R s (fun i => i.pos.trans_le (hR i)) hs
        (⟨t+1, Nat.succ_pos t⟩, .forward) hx
    · exact sectorSet_central_gap R s (fun i => i.pos.trans_le (hR i)) hs
        (⟨t+1, Nat.succ_pos t⟩, .reciprocal) hx
  have htR : (t : ℝ) + 1 ≤ R ⟨t+1, Nat.succ_pos t⟩ := by
    exact_mod_cast hR ⟨t+1, Nat.succ_pos t⟩
  have hNt : (N : ℝ) ≤ t := by exact_mod_cast ht
  linarith

/-- The actual complete reciprocal carrier, constructed without a success certificate. -/
def adaptiveCarrier (R : ℕ+ → ℕ) (s : ℕ+ → ℝ)
    (hR : ∀ i : ℕ+, (i : ℕ) ≤ R i) (hs : ∀ i, s i ∈ Set.Icc (1 : ℝ) 2) :
    LocallyFiniteCarrier :=
  LocallyFiniteCarrier.escapingUnion
    (fun t => reciprocalBlockCarrier R s (fun i => i.pos.trans_le (hR i)) hs
      ⟨t+1, Nat.succ_pos t⟩) (reciprocalBlockCarrier_escape R s hR hs)

/-- The locally finite constructor has exactly the original actual union formula. -/
@[simp] theorem adaptiveCarrier_carrier (R : ℕ+ → ℕ) (s : ℕ+ → ℝ)
    (hR : ∀ i : ℕ+, (i : ℕ) ≤ R i) (hs : ∀ i, s i ∈ Set.Icc (1 : ℝ) 2) :
    (adaptiveCarrier R s hR hs).carrier = carrierSet R s := by
  ext x
  change (x ∈ ⋃ t : ℕ, (reciprocalBlockCarrier R s
    (fun i => i.pos.trans_le (hR i)) hs ⟨t+1, Nat.succ_pos t⟩).carrier) ↔
      x ∈ carrierSet R s
  rw [Set.mem_iUnion]
  constructor
  · rintro ⟨t, ht⟩
    rcases ht with ht | ht
    · exact Set.mem_iUnion.mpr ⟨(⟨t+1, Nat.succ_pos t⟩, .forward), ht⟩
    · exact Set.mem_iUnion.mpr ⟨(⟨t+1, Nat.succ_pos t⟩, .reciprocal), ht⟩
  · intro hx
    obtain ⟨⟨i, σ⟩, hi⟩ := Set.mem_iUnion.mp hx
    have heq : (⟨(i : ℕ)-1+1, by have := i.pos; omega⟩ : ℕ+) = i := by
      apply Subtype.ext
      change (i : ℕ) - 1 + 1 = (i : ℕ)
      have := i.pos
      omega
    refine ⟨(i : ℕ)-1, ?_⟩
    rw [heq]
    cases σ with
    | forward => exact Or.inl hi
    | reciprocal => exact Or.inr hi

/-- The stronger exponential gap schedule in the adaptive proof supplies linear escape. -/
theorem linearGap_of_exponential (R : ℕ+ → ℕ)
    (hR : ∀ i : ℕ+, 2 ^ (i : ℕ) ≤ R i) : ∀ i : ℕ+, (i : ℕ) ≤ R i := by
  have hpow : ∀ n : ℕ, n ≤ 2 ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have hpos : 0 < 2 ^ n := by positivity
        rw [pow_succ]
        omega
  intro i
  exact (hpow i).trans (hR i)

/-- The unclosed signed phase set is countable, directly from its labels. -/
theorem phaseSet_countable (P R : ℕ) : (phaseSet P R).Countable := by
  apply (Set.countable_range (fun q : ℕ+ × Bool =>
    signedPhase q.2 (blockPhase P R q.1))).mono
  rintro β ⟨j, positive, rfl⟩
  exact Set.mem_range.mpr ⟨(j, positive), rfl⟩

/-- The explicit periodic phase set, including its seam, remains countable. -/
theorem periodicPhaseSet_countable (P R : ℕ) : (periodicPhaseSet P R).Countable := by
  have hcount : (⋃ n : ℤ, (fun β : ℝ => (n : ℝ) + β) ''
      (phaseSet P R ∪ {1 / 2})).Countable :=
    Set.countable_iUnion fun n =>
      ((phaseSet_countable P R).union (Set.countable_singleton _)).image _
  apply hcount.mono
  rintro x ⟨n, β, hβ, rfl⟩
  exact Set.mem_iUnion.mpr ⟨n, β, hβ, rfl⟩

/-- In particular the constructed actual union is locally finite on every interval. -/
theorem carrierSet_finite_inter_Icc (R : ℕ+ → ℕ) (s : ℕ+ → ℝ)
    (hR : ∀ i : ℕ+, 2 ^ (i : ℕ) ≤ R i) (hs : ∀ i, s i ∈ Set.Icc (1 : ℝ) 2)
    (a b : ℝ) : (carrierSet R s ∩ Set.Icc a b).Finite := by
  rw [← adaptiveCarrier_carrier R s (linearGap_of_exponential R hR) hs]
  exact (adaptiveCarrier R s (linearGap_of_exponential R hR) hs).finite_inter_Icc a b

end
end MeyerGeneralProblem.Adaptive
