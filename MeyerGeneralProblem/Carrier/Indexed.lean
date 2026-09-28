module

public import MeyerGeneralProblem.Carrier.LocallyFinite

@[expose] public section

/-!
# Indexed locally finite carriers

An `IndexedCarrier` carries a chosen countable, injective parametrisation.  It
is the coordinate-level companion of the extensional `LocallyFiniteCarrier`.
-/

namespace MeyerGeneralProblem

/-- A countably indexed, injective parametrisation with locally finite range. -/
structure IndexedCarrier (ι : Type*) [Countable ι] where
  /-- The physical carrier point at an index. -/
  point : ι → ℝ
  /-- Distinct indices give distinct physical nodes. -/
  injective : Function.Injective point
  /-- The range has finite intersection with every closed bounded interval. -/
  locallyFinite_range : ∀ a b : ℝ, (Set.range point ∩ Set.Icc a b).Finite

namespace IndexedCarrier

variable {ι : Type*} [Countable ι]

instance : FunLike (IndexedCarrier ι) ι ℝ where
  coe := IndexedCarrier.point
  coe_injective := by
    intro Λ Γ h
    cases Λ
    cases Γ
    simp_all

variable (Λ : IndexedCarrier ι)

@[simp]
theorem coe_apply (i : ι) : Λ i = Λ.point i := rfl

theorem point_ne_point {i j : ι} (hij : i ≠ j) : Λ i ≠ Λ j :=
  Λ.injective.ne hij

/-- Forget the chosen indexing and retain only the extensional range. -/
def toLocallyFinite : LocallyFiniteCarrier where
  carrier := Set.range Λ
  finite_inter_Icc := Λ.locallyFinite_range

@[simp]
theorem toLocallyFinite_carrier : Λ.toLocallyFinite.carrier = Set.range Λ := rfl

/-- Restrict an indexed carrier to a subtype of its index set. -/
def restrict (I : Set ι) : IndexedCarrier I where
  point i := Λ i.1
  injective := fun i j hij ↦ Subtype.ext (Λ.injective hij)
  locallyFinite_range a b := by
    apply (Λ.locallyFinite_range a b).subset
    rintro x ⟨⟨i, rfl⟩, hx⟩
    exact ⟨⟨i.1, rfl⟩, hx⟩

@[simp]
theorem restrict_apply (I : Set ι) (i : I) : Λ.restrict I i = Λ i.1 := rfl

end IndexedCarrier

namespace LocallyFiniteCarrier

/-- The canonical indexed presentation whose index type is the carrier subtype. -/
def toIndexedSubtype (S : LocallyFiniteCarrier) : IndexedCarrier S.subtype where
  point := Subtype.val
  injective := Subtype.val_injective
  locallyFinite_range a b := by
    rw [show Set.range (fun x : S.subtype ↦ (x : ℝ)) = S.carrier from Subtype.range_val]
    exact S.finite_inter_Icc a b

@[simp]
theorem toIndexedSubtype_apply (S : LocallyFiniteCarrier) (x : S.subtype) :
    S.toIndexedSubtype x = x := rfl

@[simp]
theorem range_toIndexedSubtype (S : LocallyFiniteCarrier) :
    Set.range S.toIndexedSubtype = S.carrier := by
  exact Subtype.range_val

@[simp]
theorem toIndexedSubtype_toLocallyFinite_carrier (S : LocallyFiniteCarrier) :
    S.toIndexedSubtype.toLocallyFinite.carrier = S.carrier :=
  S.range_toIndexedSubtype

end LocallyFiniteCarrier

namespace TwoSidedCarrier

/-- The existing ordered two-sided carrier viewed as an indexed carrier. -/
def toIndexed (Λ : TwoSidedCarrier) : IndexedCarrier ℤ where
  point := Λ
  injective := Λ.strictMono.injective
  locallyFinite_range := Λ.finite_carrier_inter_Icc

@[simp]
theorem toIndexed_apply (Λ : TwoSidedCarrier) (j : ℤ) : Λ.toIndexed j = Λ j := rfl

@[simp]
theorem toIndexed_toLocallyFinite_carrier (Λ : TwoSidedCarrier) :
    Λ.toIndexed.toLocallyFinite.carrier = Λ.toLocallyFinite.carrier := rfl

end TwoSidedCarrier

end MeyerGeneralProblem
