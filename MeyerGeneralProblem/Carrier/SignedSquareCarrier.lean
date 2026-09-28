module

public import MeyerGeneralProblem.Carrier.Indexed
public import MeyerGeneralProblem.Carrier.SignedSquare

@[expose] public section

/-!
# Locally finite carriers in signed-square coordinates

The signed-square map is injective and proper on the real line.  Consequently
it sends every extensional locally finite carrier to another locally finite
carrier, without introducing multiplicity.
-/

namespace MeyerGeneralProblem

/-- Named injectivity theorem for the signed-square coordinate. -/
theorem signedSquare_injective : Function.Injective signedSquare :=
  signedSquare_strictMono.injective

/-- Signed-square images have the same cardinality as their source sets. -/
@[simp]
theorem ncard_signedSquare_image (T : Set ℝ) :
    (signedSquare '' T).ncard = T.ncard :=
  Set.ncard_image_of_injective T signedSquare_injective

/-- The inverse image of a bounded signed-square interval lies in an explicit
bounded physical interval. -/
theorem mem_Icc_of_signedSquare_mem_Icc {x a b : ℝ}
    (hx : signedSquare x ∈ Set.Icc a b) :
    x ∈ Set.Icc (-(max |a| |b| + 1)) (max |a| |b| + 1) := by
  have hsquare : |x| ^ 2 ≤ max |a| |b| := by
    rw [← abs_signedSquare]
    exact abs_le_max_abs_abs hx.1 hx.2
  have hmax : 0 ≤ max |a| |b| :=
    le_trans (abs_nonneg a) (le_max_left _ _)
  have habs : |x| ≤ max |a| |b| + 1 := by
    by_contra hnot
    have hlarge : max |a| |b| + 1 < |x| := lt_of_not_ge hnot
    have hone : 1 ≤ |x| := by linarith
    have hmul : 0 ≤ |x| * (|x| - 1) :=
      mul_nonneg (abs_nonneg x) (sub_nonneg.mpr hone)
    nlinarith
  exact (abs_le.mp habs)

/-- Signed-square images of locally finite carriers remain locally finite. -/
theorem LocallyFiniteCarrier.finite_signedSquare_image_inter_Icc
    (S : LocallyFiniteCarrier) (a b : ℝ) :
    (signedSquare '' S.carrier ∩ Set.Icc a b).Finite := by
  let R : ℝ := max |a| |b| + 1
  apply ((S.finite_inter_Icc (-R) R).image signedSquare).subset
  rintro y ⟨⟨x, hxS, rfl⟩, hxIcc⟩
  exact ⟨x, ⟨hxS, mem_Icc_of_signedSquare_mem_Icc hxIcc⟩, rfl⟩

namespace LocallyFiniteCarrier

/-- The extensional signed-square image of a locally finite carrier. -/
def signedSquareImage (S : LocallyFiniteCarrier) : LocallyFiniteCarrier where
  carrier := signedSquare '' S.carrier
  finite_inter_Icc := S.finite_signedSquare_image_inter_Icc

@[simp]
theorem signedSquareImage_carrier (S : LocallyFiniteCarrier) :
    S.signedSquareImage.carrier = signedSquare '' S.carrier := rfl

@[simp]
theorem signedSquareImage_carrier_eq_range (S : LocallyFiniteCarrier) :
    S.signedSquareImage.carrier = Set.range (signedSquare ∘ S.toIndexedSubtype) := by
  rw [signedSquareImage_carrier, Set.image_eq_range]
  rfl

@[simp]
theorem mem_signedSquareImage_carrier (S : LocallyFiniteCarrier) {s : ℝ} :
    s ∈ S.signedSquareImage.carrier ↔ ∃ x ∈ S.carrier, signedSquare x = s := by
  rfl

/-- Intersecting a signed-square image with a set counts exactly the source
points whose signed square lies in that set. -/
theorem ncard_signedSquareImage_inter (S : LocallyFiniteCarrier) (A : Set ℝ) :
    (S.signedSquareImage.carrier ∩ A).ncard =
      (S.carrier ∩ signedSquare ⁻¹' A).ncard := by
  rw [signedSquareImage_carrier, ← Set.image_inter_preimage,
    ncard_signedSquare_image]

end LocallyFiniteCarrier

namespace TwoSidedCarrier

/-- The signed-square image of an ordered two-sided carrier, viewed
extensionally. -/
def signedSquareCarrier (Λ : TwoSidedCarrier) : LocallyFiniteCarrier :=
  Λ.toLocallyFinite.signedSquareImage

@[simp]
theorem signedSquareCarrier_carrier (Λ : TwoSidedCarrier) :
    Λ.signedSquareCarrier.carrier = signedSquare '' Set.range Λ := rfl

@[simp]
theorem signedSquareCarrier_carrier_eq_range (Λ : TwoSidedCarrier) :
    Λ.signedSquareCarrier.carrier = Set.range (signedSquare ∘ Λ) := by
  rw [signedSquareCarrier_carrier, Set.range_comp]

@[simp]
theorem mem_signedSquareCarrier (Λ : TwoSidedCarrier) {s : ℝ} :
    s ∈ Λ.signedSquareCarrier.carrier ↔ ∃ j : ℤ, signedSquare (Λ j) = s := by
  rw [signedSquareCarrier_carrier_eq_range]
  rfl

/-- The signed-square indexing remains injective. -/
theorem signedSquare_comp_injective (Λ : TwoSidedCarrier) :
    Function.Injective (signedSquare ∘ Λ) :=
  signedSquare_injective.comp Λ.strictMono.injective

end TwoSidedCarrier

end MeyerGeneralProblem
