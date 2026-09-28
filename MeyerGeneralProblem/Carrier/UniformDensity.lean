module

public import MeyerGeneralProblem.Carrier.DensityPredicates
public import Mathlib.Order.Filter.ENNReal
import all Mathlib.Order.Filter.ENNReal

@[expose] public section

/-!
# Numerical uniform Beurling densities

The normalized source profiles take their infimum or supremum over all
half-open real windows of a fixed positive length.  Their `liminf` and
`limsup` at real `atTop` are `ℝ≥0∞`-valued, so infinite upper density is
retained rather than truncated to a real number.
-/

namespace MeyerGeneralProblem

open Filter

private theorem ennreal_isBoundedUnder_ge {α : Type*}
    (f : Filter α) (u : α → ENNReal) :
    f.IsBoundedUnder (fun x y : ENNReal ↦ x ≥ y) u :=
  Filter.isBoundedUnder_of ⟨0, fun _ ↦ bot_le⟩

private theorem ennreal_isBoundedUnder_le {α : Type*}
    (f : Filter α) (u : α → ENNReal) :
    f.IsBoundedUnder (fun x y : ENNReal ↦ x ≤ y) u :=
  Filter.isBoundedUnder_of ⟨⊤, fun _ ↦ le_top⟩

/-- The lower normalized half-open window-count profile.  The value at a
nonpositive length is set to zero; this branch is invisible at `atTop`. -/
noncomputable def lowerUniformDensityProfile
    (S : LocallyFiniteCarrier) (L : ℝ) : ENNReal :=
  if 0 < L then
    ⨅ a : ℝ, (windowCount S a L : ENNReal) / ENNReal.ofReal L
  else 0

/-- The upper normalized half-open window-count profile.  The value at a
nonpositive length is set to zero; this branch is invisible at `atTop`. -/
noncomputable def upperUniformDensityProfile
    (S : LocallyFiniteCarrier) (L : ℝ) : ENNReal :=
  if 0 < L then
    ⨆ a : ℝ, (windowCount S a L : ENNReal) / ENNReal.ofReal L
  else 0

/-- Lower uniform Beurling density in the half-open source convention. -/
noncomputable def lowerUniformBeurlingDensity
    (S : LocallyFiniteCarrier) : ENNReal :=
  Filter.liminf (lowerUniformDensityProfile S) Filter.atTop

/-- Upper uniform Beurling density in the half-open source convention. -/
noncomputable def upperUniformBeurlingDensity
    (S : LocallyFiniteCarrier) : ENNReal :=
  Filter.limsup (upperUniformDensityProfile S) Filter.atTop

namespace LocallyFiniteCarrier

variable (S : LocallyFiniteCarrier)

@[simp]
theorem lowerUniformDensityProfile_of_nonpos {L : ℝ} (hL : L ≤ 0) :
    lowerUniformDensityProfile S L = 0 := by
  simp [lowerUniformDensityProfile, hL]

@[simp]
theorem upperUniformDensityProfile_of_nonpos {L : ℝ} (hL : L ≤ 0) :
    upperUniformDensityProfile S L = 0 := by
  simp [upperUniformDensityProfile, hL]

theorem lowerUniformDensityProfile_of_pos {L : ℝ} (hL : 0 < L) :
    lowerUniformDensityProfile S L =
      ⨅ a : ℝ, (windowCount S a L : ENNReal) / ENNReal.ofReal L := by
  simp [lowerUniformDensityProfile, hL]

theorem upperUniformDensityProfile_of_pos {L : ℝ} (hL : 0 < L) :
    upperUniformDensityProfile S L =
      ⨆ a : ℝ, (windowCount S a L : ENNReal) / ENNReal.ofReal L := by
  simp [upperUniformDensityProfile, hL]

/-- Real lower count estimates are exactly ENNReal normalized-ratio
estimates at positive lengths. -/
theorem ofReal_le_count_div_iff {a L r : ℝ} (hr : 0 ≤ r) (hL : 0 < L) :
    ENNReal.ofReal r ≤ (windowCount S a L : ENNReal) / ENNReal.ofReal L ↔
      r * L ≤ (windowCount S a L : ℝ) := by
  rw [ENNReal.le_div_iff_mul_le
    (Or.inl (ENNReal.ofReal_pos.mpr hL).ne')
    (Or.inl ENNReal.ofReal_ne_top), ← ENNReal.ofReal_mul hr,
    ← ENNReal.ofReal_natCast,
    ENNReal.ofReal_le_ofReal_iff (Nat.cast_nonneg (windowCount S a L))]

/-- Real upper count estimates are exactly ENNReal normalized-ratio
estimates at positive lengths. -/
theorem count_div_le_ofReal_iff {a L r : ℝ} (hr : 0 ≤ r) (hL : 0 < L) :
    (windowCount S a L : ENNReal) / ENNReal.ofReal L ≤ ENNReal.ofReal r ↔
      (windowCount S a L : ℝ) ≤ r * L := by
  rw [ENNReal.div_le_iff (ENNReal.ofReal_pos.mpr hL).ne'
    ENNReal.ofReal_ne_top, ← ENNReal.ofReal_mul hr,
    ← ENNReal.ofReal_natCast,
    ENNReal.ofReal_le_ofReal_iff (mul_nonneg hr hL.le)]

theorem ofReal_le_lowerUniformDensityProfile_iff {L r : ℝ}
    (hr : 0 ≤ r) (hL : 0 < L) :
    ENNReal.ofReal r ≤ lowerUniformDensityProfile S L ↔
      ∀ a : ℝ, r * L ≤ (windowCount S a L : ℝ) := by
  rw [S.lowerUniformDensityProfile_of_pos hL]
  constructor
  · intro h a
    apply (S.ofReal_le_count_div_iff hr hL).1
    exact h.trans (iInf_le _ a)
  · intro h
    exact le_iInf fun a ↦ (S.ofReal_le_count_div_iff hr hL).2 (h a)

theorem upperUniformDensityProfile_le_ofReal_iff {L r : ℝ}
    (hr : 0 ≤ r) (hL : 0 < L) :
    upperUniformDensityProfile S L ≤ ENNReal.ofReal r ↔
      ∀ a : ℝ, (windowCount S a L : ℝ) ≤ r * L := by
  rw [S.upperUniformDensityProfile_of_pos hL]
  constructor
  · intro h a
    apply (S.count_div_le_ofReal_iff hr hL).1
    exact (le_iSup (fun b : ℝ ↦
      (windowCount S b L : ENNReal) / ENNReal.ofReal L) a).trans h
  · intro h
    exact iSup_le fun a ↦ (S.count_div_le_ofReal_iff hr hL).2 (h a)

/-- Lower profiles are monotone under carrier inclusion. -/
theorem lowerUniformDensityProfile_mono {S T : LocallyFiniteCarrier}
    (hST : S.carrier ⊆ T.carrier) (L : ℝ) :
    lowerUniformDensityProfile S L ≤ lowerUniformDensityProfile T L := by
  by_cases hL : 0 < L
  · rw [S.lowerUniformDensityProfile_of_pos hL,
      T.lowerUniformDensityProfile_of_pos hL]
    apply iInf_mono
    intro a
    apply ENNReal.div_le_div_right
    exact_mod_cast LocallyFiniteCarrier.windowCount_mono_carrier hST a L
  · simp [lowerUniformDensityProfile, hL]

/-- Upper profiles are monotone under carrier inclusion. -/
theorem upperUniformDensityProfile_mono {S T : LocallyFiniteCarrier}
    (hST : S.carrier ⊆ T.carrier) (L : ℝ) :
    upperUniformDensityProfile S L ≤ upperUniformDensityProfile T L := by
  by_cases hL : 0 < L
  · rw [S.upperUniformDensityProfile_of_pos hL,
      T.upperUniformDensityProfile_of_pos hL]
    apply iSup_mono
    intro a
    apply ENNReal.div_le_div_right
    exact_mod_cast LocallyFiniteCarrier.windowCount_mono_carrier hST a L
  · simp [upperUniformDensityProfile, hL]

/-- At each positive length, the lower profile does not exceed the upper
profile. -/
theorem lowerUniformDensityProfile_le_upperUniformDensityProfile (L : ℝ) :
    lowerUniformDensityProfile S L ≤ upperUniformDensityProfile S L := by
  by_cases hL : 0 < L
  · rw [S.lowerUniformDensityProfile_of_pos hL,
      S.upperUniformDensityProfile_of_pos hL]
    exact (iInf_le (fun a : ℝ ↦
      (windowCount S a L : ENNReal) / ENNReal.ofReal L) 0).trans
      (le_iSup (fun a : ℝ ↦
        (windowCount S a L : ENNReal) / ENNReal.ofReal L) 0)
  · simp [lowerUniformDensityProfile, upperUniformDensityProfile, hL]

end LocallyFiniteCarrier

/-- Lower uniform Beurling density is monotone under carrier inclusion. -/
theorem lowerDensity_mono {S T : LocallyFiniteCarrier}
    (hST : S.carrier ⊆ T.carrier) :
    lowerUniformBeurlingDensity S ≤ lowerUniformBeurlingDensity T := by
  exact Filter.liminf_le_liminf
    (Filter.Eventually.of_forall
      (LocallyFiniteCarrier.lowerUniformDensityProfile_mono hST))
    (ennreal_isBoundedUnder_ge Filter.atTop (lowerUniformDensityProfile S))
    ((ennreal_isBoundedUnder_le Filter.atTop
      (lowerUniformDensityProfile T)).isCoboundedUnder_ge)

/-- Upper uniform Beurling density is monotone under carrier inclusion. -/
theorem upperDensity_mono {S T : LocallyFiniteCarrier}
    (hST : S.carrier ⊆ T.carrier) :
    upperUniformBeurlingDensity S ≤ upperUniformBeurlingDensity T := by
  exact Filter.limsup_le_limsup
    (Filter.Eventually.of_forall
      (LocallyFiniteCarrier.upperUniformDensityProfile_mono hST))
    ((ennreal_isBoundedUnder_ge Filter.atTop
      (upperUniformDensityProfile S)).isCoboundedUnder_le)
    (ennreal_isBoundedUnder_le Filter.atTop (upperUniformDensityProfile T))

/-- Lower uniform density never exceeds upper uniform density. -/
theorem lowerDensity_le_upperDensity (S : LocallyFiniteCarrier) :
    lowerUniformBeurlingDensity S ≤ upperUniformBeurlingDensity S := by
  exact Filter.liminf_le_limsup_of_frequently_le
    (Filter.Frequently.of_forall
      (S.lowerUniformDensityProfile_le_upperUniformDensityProfile))
    (ennreal_isBoundedUnder_ge Filter.atTop (lowerUniformDensityProfile S))
    (ennreal_isBoundedUnder_le Filter.atTop (upperUniformDensityProfile S))

/-- The strict real-margin lower predicate agrees with strict numerical lower
density at nonnegative thresholds. -/
theorem uniformLowerDensityGT_iff_lt_lowerUniformBeurlingDensity
    (S : LocallyFiniteCarrier) {c : ℝ} (hc : 0 ≤ c) :
    UniformLowerDensityGT S c ↔
      ENNReal.ofReal c < lowerUniformBeurlingDensity S := by
  constructor
  · rintro ⟨ε, hε, L₀, hL₀, hbound⟩
    have hr : 0 ≤ c + ε := (add_pos_of_nonneg_of_pos hc hε).le
    have heventually :
        ∀ᶠ L : ℝ in Filter.atTop,
          ENNReal.ofReal (c + ε) ≤ lowerUniformDensityProfile S L := by
      apply Filter.eventually_atTop.2
      refine ⟨L₀, fun L hL ↦ ?_⟩
      apply (S.ofReal_le_lowerUniformDensityProfile_iff hr (hL₀.trans_le hL)).2
      exact hbound L hL
    have hliminf :
        ENNReal.ofReal (c + ε) ≤ lowerUniformBeurlingDensity S := by
      exact Filter.le_liminf_of_le
        ((ennreal_isBoundedUnder_le Filter.atTop
          (lowerUniformDensityProfile S)).isCoboundedUnder_ge)
        heventually
    exact (ENNReal.ofReal_lt_ofReal_iff (add_pos_of_nonneg_of_pos hc hε)).2
      (by linarith) |>.trans_le hliminf
  · intro hdensity
    obtain ⟨z, hcz, hzdensity⟩ := exists_between hdensity
    have hz_top : z ≠ (⊤ : ENNReal) := ne_of_lt (hzdensity.trans_le le_top)
    let r : ℝ := z.toReal
    have hcr : c < r := by
      dsimp [r]
      have := (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top hz_top).2 hcz
      simpa [ENNReal.toReal_ofReal hc] using this
    have heventually :
        ∀ᶠ L : ℝ in Filter.atTop, z < lowerUniformDensityProfile S L :=
      Filter.eventually_lt_of_lt_liminf hzdensity
        (ennreal_isBoundedUnder_ge Filter.atTop (lowerUniformDensityProfile S))
    obtain ⟨B, hB⟩ := Filter.eventually_atTop.1 heventually
    refine ⟨r - c, sub_pos.mpr hcr, max 1 B,
      lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
    intro L hL a
    have hBL : B ≤ L := (le_max_right _ _).trans hL
    have hLpos : 0 < L :=
      lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hL)
    have hprofile : ENNReal.ofReal r ≤ lowerUniformDensityProfile S L := by
      rw [ENNReal.ofReal_toReal hz_top]
      exact (hB L hBL).le
    have hreal :=
      (S.ofReal_le_lowerUniformDensityProfile_iff ENNReal.toReal_nonneg hLpos).1
        hprofile a
    convert hreal using 1
    ring

/-- The strict real-margin upper predicate agrees with strict numerical upper
density at nonnegative thresholds. -/
theorem uniformUpperDensityLT_iff_upperUniformBeurlingDensity_lt
    (S : LocallyFiniteCarrier) {c : ℝ} (hc : 0 ≤ c) :
    UniformUpperDensityLT S c ↔
      upperUniformBeurlingDensity S < ENNReal.ofReal c := by
  constructor
  · rintro ⟨ε, hε, L₀, hL₀, hbound⟩
    have hr : 0 ≤ c - ε := by
      have hsample := hbound L₀ le_rfl 0
      have hcount : 0 ≤ (windowCount S 0 L₀ : ℝ) := Nat.cast_nonneg _
      nlinarith
    have heventually :
        ∀ᶠ L : ℝ in Filter.atTop,
          upperUniformDensityProfile S L ≤ ENNReal.ofReal (c - ε) := by
      apply Filter.eventually_atTop.2
      refine ⟨L₀, fun L hL ↦ ?_⟩
      apply (S.upperUniformDensityProfile_le_ofReal_iff hr (hL₀.trans_le hL)).2
      exact hbound L hL
    have hlimsup :
        upperUniformBeurlingDensity S ≤ ENNReal.ofReal (c - ε) := by
      exact Filter.limsup_le_of_le
        ((ennreal_isBoundedUnder_ge Filter.atTop
          (upperUniformDensityProfile S)).isCoboundedUnder_le)
        heventually
    have hcpos : 0 < c := by linarith
    exact hlimsup.trans_lt
      ((ENNReal.ofReal_lt_ofReal_iff hcpos).2 (by linarith))
  · intro hdensity
    obtain ⟨z, hdensityz, hzc⟩ := exists_between hdensity
    have hz_top : z ≠ (⊤ : ENNReal) := ne_of_lt (hzc.trans_le le_top)
    let r : ℝ := z.toReal
    have hrc : r < c := by
      dsimp [r]
      have := (ENNReal.toReal_lt_toReal hz_top ENNReal.ofReal_ne_top).2 hzc
      simpa [ENNReal.toReal_ofReal hc] using this
    have heventually :
        ∀ᶠ L : ℝ in Filter.atTop, upperUniformDensityProfile S L < z :=
      Filter.eventually_lt_of_limsup_lt hdensityz
        (ennreal_isBoundedUnder_le Filter.atTop (upperUniformDensityProfile S))
    obtain ⟨B, hB⟩ := Filter.eventually_atTop.1 heventually
    refine ⟨c - r, sub_pos.mpr hrc, max 1 B,
      lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
    intro L hL a
    have hBL : B ≤ L := (le_max_right _ _).trans hL
    have hLpos : 0 < L :=
      lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hL)
    have hprofile : upperUniformDensityProfile S L ≤ ENNReal.ofReal r := by
      rw [ENNReal.ofReal_toReal hz_top]
      exact (hB L hBL).le
    have hreal :=
      (S.upperUniformDensityProfile_le_ofReal_iff ENNReal.toReal_nonneg hLpos).1
        hprofile a
    convert hreal using 1
    ring

/-- Threshold-one form used by the supercritical route. -/
theorem uniformLowerDensityGT_one_iff (S : LocallyFiniteCarrier) :
    UniformLowerDensityGT S 1 ↔ 1 < lowerUniformBeurlingDensity S := by
  simpa using
    (uniformLowerDensityGT_iff_lt_lowerUniformBeurlingDensity S
      (c := 1) (by norm_num))

/-- Threshold-one form used by the subcritical route. -/
theorem uniformUpperDensityLT_one_iff (S : LocallyFiniteCarrier) :
    UniformUpperDensityLT S 1 ↔ upperUniformBeurlingDensity S < 1 := by
  simpa using
    (uniformUpperDensityLT_iff_upperUniformBeurlingDensity_lt S
      (c := 1) (by norm_num))

theorem uniformLowerDensityGT_one_of_one_lt
    {S : LocallyFiniteCarrier} (h : 1 < lowerUniformBeurlingDensity S) :
    UniformLowerDensityGT S 1 :=
  (uniformLowerDensityGT_one_iff S).2 h

theorem uniformUpperDensityLT_one_of_lt_one
    {S : LocallyFiniteCarrier} (h : upperUniformBeurlingDensity S < 1) :
    UniformUpperDensityLT S 1 :=
  (uniformUpperDensityLT_one_iff S).2 h

/-- A carrier bounded below has zero lower uniform Beurling density. -/
theorem lowerDensity_zero_of_boundedBelow
    (S : LocallyFiniteCarrier) (hS : BddBelow S.carrier) :
    lowerUniformBeurlingDensity S = 0 := by
  apply le_antisymm
  · by_contra hnot
    have hpos : (0 : ENNReal) < lowerUniformBeurlingDensity S :=
      lt_of_not_ge hnot
    have hstrict : UniformLowerDensityGT S 0 :=
      (uniformLowerDensityGT_iff_lt_lowerUniformBeurlingDensity S
        (c := 0) (by norm_num)).2 (by simpa using hpos)
    exact S.not_uniformLowerDensityGT_of_bddBelow hS (c := 0) (by norm_num) hstrict
  · exact bot_le

/-- A carrier bounded above has zero lower uniform Beurling density. -/
theorem lowerDensity_zero_of_boundedAbove
    (S : LocallyFiniteCarrier) (hS : BddAbove S.carrier) :
    lowerUniformBeurlingDensity S = 0 := by
  apply le_antisymm
  · by_contra hnot
    have hpos : (0 : ENNReal) < lowerUniformBeurlingDensity S :=
      lt_of_not_ge hnot
    have hstrict : UniformLowerDensityGT S 0 :=
      (uniformLowerDensityGT_iff_lt_lowerUniformBeurlingDensity S
        (c := 0) (by norm_num)).2 (by simpa using hpos)
    exact S.not_uniformLowerDensityGT_of_bddAbove hS (c := 0) (by norm_num) hstrict
  · exact bot_le

end MeyerGeneralProblem
