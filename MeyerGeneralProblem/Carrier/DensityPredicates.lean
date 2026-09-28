module

public import MeyerGeneralProblem.Carrier.LocallyFinite

@[expose] public section

/-!
# Half-open window counts and strict uniform-density predicates

All source windows use the convention `[a, a + L)`.  The strict predicates
are deliberately stated using positive real window lengths, an explicit
positive density margin, and a positive eventual length threshold.  Numerical
`ℝ≥0∞` densities and their liminf/limsup equivalences belong in the subsequent
uniform-density layer.
-/

namespace MeyerGeneralProblem

/-- The number of carrier nodes in the half-open real window `[a, a + L)`. -/
noncomputable def windowCount (S : LocallyFiniteCarrier) (a L : ℝ) : ℕ :=
  Set.ncard (S.carrier ∩ Set.Ico a (a + L))

namespace LocallyFiniteCarrier

variable (S : LocallyFiniteCarrier)

/-- The set counted by `windowCount` is finite for every real length, including
nonpositive lengths. -/
theorem finite_window (a L : ℝ) :
    (S.carrier ∩ Set.Ico a (a + L)).Finite :=
  S.finite_inter_Ico a (a + L)

theorem windowCount_eq_toFinset_card (a L : ℝ) :
    windowCount S a L = (S.finite_window a L).toFinset.card :=
  Set.ncard_eq_toFinset_card _ (S.finite_window a L)

theorem windowCount_eq_zero_iff (a L : ℝ) :
    windowCount S a L = 0 ↔ S.carrier ∩ Set.Ico a (a + L) = ∅ :=
  Set.ncard_eq_zero (S.finite_window a L)

@[simp]
theorem windowCount_of_nonpos {a L : ℝ} (hL : L ≤ 0) :
    windowCount S a L = 0 := by
  unfold windowCount
  rw [Set.Ico_eq_empty (by linarith), Set.inter_empty, Set.ncard_empty]

/-- Enlarging the carrier cannot decrease a window count. -/
theorem windowCount_mono_carrier {S T : LocallyFiniteCarrier}
    (hST : S.carrier ⊆ T.carrier) (a L : ℝ) :
    windowCount S a L ≤ windowCount T a L := by
  apply Set.ncard_le_ncard _ (T.finite_window a L)
  intro x hx
  exact ⟨hST hx.1, hx.2⟩

/-- Enlarging a window to the right cannot decrease its count. -/
theorem windowCount_mono_length {a L M : ℝ} (hLM : L ≤ M) :
    windowCount S a L ≤ windowCount S a M := by
  apply Set.ncard_le_ncard _ (S.finite_window a M)
  intro x hx
  exact ⟨hx.1, hx.2.1, hx.2.2.trans_le (by linarith)⟩

/-- Adjacent nonnegative half-open windows count additively, with no boundary
double counting. -/
theorem windowCount_add (a L M : ℝ) (hL : 0 ≤ L) (hM : 0 ≤ M) :
    windowCount S a (L + M) = windowCount S a L + windowCount S (a + L) M := by
  have hleft : a ≤ a + L := by linarith
  have hright : a + L ≤ a + L + M := by linarith
  have hinterval :
      Set.Ico a (a + L) ∪ Set.Ico (a + L) (a + L + M) =
        Set.Ico a (a + L + M) :=
    Set.Ico_union_Ico_eq_Ico hleft hright
  have hdisjoint :
      Disjoint (S.carrier ∩ Set.Ico a (a + L))
        (S.carrier ∩ Set.Ico (a + L) (a + L + M)) := by
    rw [Set.disjoint_left]
    intro x hxleft hxright
    exact (not_lt_of_ge hxright.2.1) hxleft.2.2
  unfold windowCount
  rw [show a + (L + M) = a + L + M by ring]
  rw [← hinterval, Set.inter_union_distrib_left,
    Set.ncard_union_eq hdisjoint (S.finite_window a L)
      (S.finite_window (a + L) M)]

end LocallyFiniteCarrier

/-- Uniform lower window growth strictly above `c`, in the exact half-open
source convention and with positive real window lengths. -/
def UniformLowerDensityGT (S : LocallyFiniteCarrier) (c : ℝ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∃ L₀ : ℝ, 0 < L₀ ∧
    ∀ L : ℝ, L₀ ≤ L → ∀ a : ℝ,
      (c + ε) * L ≤ (windowCount S a L : ℝ)

/-- Uniform upper window growth strictly below `c`, in the exact half-open
source convention and with positive real window lengths. -/
def UniformUpperDensityLT (S : LocallyFiniteCarrier) (c : ℝ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∃ L₀ : ℝ, 0 < L₀ ∧
    ∀ L : ℝ, L₀ ≤ L → ∀ a : ℝ,
      (windowCount S a L : ℝ) ≤ (c - ε) * L

namespace UniformLowerDensityGT

/-- The strict lower-density predicate is monotone under carrier inclusion. -/
theorem mono_carrier {S T : LocallyFiniteCarrier} {c : ℝ}
    (hST : S.carrier ⊆ T.carrier) (hS : UniformLowerDensityGT S c) :
    UniformLowerDensityGT T c := by
  rcases hS with ⟨ε, hε, L₀, hL₀, hbound⟩
  refine ⟨ε, hε, L₀, hL₀, fun L hL a ↦ ?_⟩
  exact (hbound L hL a).trans (by
    exact_mod_cast LocallyFiniteCarrier.windowCount_mono_carrier hST a L)

/-- A lower bound above a larger threshold is also above any smaller one. -/
theorem antitone_threshold {S : LocallyFiniteCarrier} {c d : ℝ}
    (hcd : c ≤ d) (hS : UniformLowerDensityGT S d) :
    UniformLowerDensityGT S c := by
  rcases hS with ⟨ε, hε, L₀, hL₀, hbound⟩
  refine ⟨ε, hε, L₀, hL₀, fun L hL a ↦ ?_⟩
  calc
    (c + ε) * L ≤ (d + ε) * L := by
      exact mul_le_mul_of_nonneg_right (by linarith) (hL₀.le.trans hL)
    _ ≤ (windowCount S a L : ℝ) := hbound L hL a

end UniformLowerDensityGT

namespace UniformUpperDensityLT

/-- The strict upper-density predicate is antitone under carrier inclusion. -/
theorem antitone_carrier {S T : LocallyFiniteCarrier} {c : ℝ}
    (hST : S.carrier ⊆ T.carrier) (hT : UniformUpperDensityLT T c) :
    UniformUpperDensityLT S c := by
  rcases hT with ⟨ε, hε, L₀, hL₀, hbound⟩
  refine ⟨ε, hε, L₀, hL₀, fun L hL a ↦ ?_⟩
  have hcount : (windowCount S a L : ℝ) ≤ (windowCount T a L : ℝ) := by
    exact_mod_cast LocallyFiniteCarrier.windowCount_mono_carrier hST a L
  exact hcount.trans (hbound L hL a)

/-- An upper bound below a smaller threshold is also below any larger one. -/
theorem mono_threshold {S : LocallyFiniteCarrier} {c d : ℝ}
    (hcd : c ≤ d) (hS : UniformUpperDensityLT S c) :
    UniformUpperDensityLT S d := by
  rcases hS with ⟨ε, hε, L₀, hL₀, hbound⟩
  refine ⟨ε, hε, L₀, hL₀, fun L hL a ↦ ?_⟩
  calc
    (windowCount S a L : ℝ) ≤ (c - ε) * L := hbound L hL a
    _ ≤ (d - ε) * L := by
      exact mul_le_mul_of_nonneg_right (sub_le_sub_right hcd ε) (hL₀.le.trans hL)

end UniformUpperDensityLT

namespace LocallyFiniteCarrier

variable (S : LocallyFiniteCarrier)

/-- A carrier bounded below cannot have strict positive uniform lower density. -/
theorem not_uniformLowerDensityGT_of_bddBelow
    (hS : BddBelow S.carrier) {c : ℝ} (hc : 0 ≤ c) :
    ¬ UniformLowerDensityGT S c := by
  rintro ⟨ε, hε, L₀, hL₀, hbound⟩
  obtain ⟨b, hb⟩ := hS
  have hzero : windowCount S (b - L₀ - 1) L₀ = 0 := by
    apply (S.windowCount_eq_zero_iff (b - L₀ - 1) L₀).2
    apply Set.not_nonempty_iff_eq_empty.mp
    rintro ⟨x, hxS, hxwindow⟩
    have hbx : b ≤ x := hb hxS
    linarith [hxwindow.2]
  have hineq := hbound L₀ le_rfl (b - L₀ - 1)
  rw [hzero, Nat.cast_zero] at hineq
  have hpos : 0 < (c + ε) * L₀ :=
    mul_pos (add_pos_of_nonneg_of_pos hc hε) hL₀
  linarith

/-- A carrier bounded above cannot have strict positive uniform lower density. -/
theorem not_uniformLowerDensityGT_of_bddAbove
    (hS : BddAbove S.carrier) {c : ℝ} (hc : 0 ≤ c) :
    ¬ UniformLowerDensityGT S c := by
  rintro ⟨ε, hε, L₀, hL₀, hbound⟩
  obtain ⟨b, hb⟩ := hS
  have hzero : windowCount S (b + 1) L₀ = 0 := by
    apply (S.windowCount_eq_zero_iff (b + 1) L₀).2
    apply Set.not_nonempty_iff_eq_empty.mp
    rintro ⟨x, hxS, hxwindow⟩
    have hxb : x ≤ b := hb hxS
    linarith [hxwindow.1]
  have hineq := hbound L₀ le_rfl (b + 1)
  rw [hzero, Nat.cast_zero] at hineq
  have hpos : 0 < (c + ε) * L₀ :=
    mul_pos (add_pos_of_nonneg_of_pos hc hε) hL₀
  linarith

/-- In particular, finite carriers cannot have strict positive uniform lower
density. -/
theorem not_uniformLowerDensityGT_of_finite
    (hS : S.carrier.Finite) {c : ℝ} (hc : 0 ≤ c) :
    ¬ UniformLowerDensityGT S c :=
  S.not_uniformLowerDensityGT_of_bddAbove hS.bddAbove hc

/-- Every finite carrier has strict upper density below every positive
threshold in the working predicate. -/
theorem uniformUpperDensityLT_of_finite
    (hS : S.carrier.Finite) {c : ℝ} (hc : 0 < c) :
    UniformUpperDensityLT S c := by
  let N : ℝ := S.carrier.ncard
  refine ⟨c / 2, half_pos hc, max 1 (2 * N / c),
    lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro L hL a
  have hcountNat : windowCount S a L ≤ S.carrier.ncard := by
    apply Set.ncard_le_ncard Set.inter_subset_left hS
  have hcount : (windowCount S a L : ℝ) ≤ N := by
    dsimp [N]
    exact_mod_cast hcountNat
  have hratio : 2 * N / c ≤ L := (le_max_right _ _).trans hL
  calc
    (windowCount S a L : ℝ) ≤ N := hcount
    _ = (c / 2) * (2 * N / c) := by
      field_simp
    _ ≤ (c / 2) * L := mul_le_mul_of_nonneg_left hratio (half_pos hc).le
    _ = (c - c / 2) * L := by ring

/-- Empty carriers have zero window counts. -/
theorem windowCount_eq_zero_of_carrier_eq_empty
    (hS : S.carrier = ∅) (a L : ℝ) : windowCount S a L = 0 := by
  unfold windowCount
  rw [hS, Set.empty_inter, Set.ncard_empty]

/-- Empty carriers cannot have strict positive uniform lower density. -/
theorem not_uniformLowerDensityGT_of_carrier_eq_empty
    (hS : S.carrier = ∅) {c : ℝ} (hc : 0 ≤ c) :
    ¬ UniformLowerDensityGT S c := by
  apply S.not_uniformLowerDensityGT_of_finite
  · rw [hS]
    exact Set.finite_empty
  · exact hc

/-- Empty carriers satisfy every positive strict uniform upper bound. -/
theorem uniformUpperDensityLT_of_carrier_eq_empty
    (hS : S.carrier = ∅) {c : ℝ} (hc : 0 < c) :
    UniformUpperDensityLT S c := by
  apply S.uniformUpperDensityLT_of_finite
  · rw [hS]
    exact Set.finite_empty
  · exact hc

end LocallyFiniteCarrier

end MeyerGeneralProblem
