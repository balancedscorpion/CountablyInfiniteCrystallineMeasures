module

public import MeyerGeneralProblem.Distribution.MeyerSpace

@[expose] public section

/-!
# Same-container transport for actual locally atomic distributions

The finite union of two locally finite supports is a genuine common carrier.
Local atomicity transports by the proved Schwartz-annihilator equivalence.
Canonical isolation coefficients agree on an included support.
-/

namespace MeyerGeneralProblem

noncomputable section

/-- The actual set union remains locally finite on every compact interval. -/
def LocallyFiniteCarrier.union (S U : LocallyFiniteCarrier) : LocallyFiniteCarrier where
  carrier := S.carrier ∪ U.carrier
  finite_inter_Icc a b := by
    rw [Set.union_inter_distrib_right]
    exact (S.finite_inter_Icc a b).union (U.finite_inter_Icc a b)

/-- The common carrier is exactly the union, without new accumulation points. -/
theorem LocallyFiniteCarrier.union_carrier (S U : LocallyFiniteCarrier) :
    (S.union U).carrier = S.carrier ∪ U.carrier := rfl

/-- The natural inclusion of actual points into an enlarged carrier. -/
def LocallyFiniteCarrier.inclusion {S U : LocallyFiniteCarrier}
    (hSU : S.carrier ⊆ U.carrier) : S.subtype ↪ U.subtype where
  toFun x := ⟨x.val, hSU x.property⟩
  inj' _ _ h := Subtype.ext (congrArg (fun z : U.subtype => (z:ℝ)) h)

/-- The inclusion preserves the real coordinate exactly. -/
theorem LocallyFiniteCarrier.inclusion_val {S U : LocallyFiniteCarrier}
    (hSU : S.carrier ⊆ U.carrier) (x : S.subtype) :
    ((LocallyFiniteCarrier.inclusion hSU x : U.subtype) : ℝ) = (x:ℝ) := rfl

/-- Actual local atomicity survives enlargement of a locally finite carrier. -/
theorem hasLocallyAtomicAction_of_carrier_subset {S U : LocallyFiniteCarrier}
    (hSU : S.carrier ⊆ U.carrier) (T : TemperedDistribution ℝ ℂ)
    (hT : HasLocallyAtomicAction S T) : HasLocallyAtomicAction U T := by
  rw [← atomicOnCarrier_iff_hasLocallyAtomicAction]
  intro f hf
  exact hasLocallyAtomicAction_atomicOnCarrier S T hT f (fun x hx => hf x (hSU hx))

/-- On an actually atomic support, both carrier choices recover exactly
the same canonical coefficient, even though their isolating bumps differ. -/
theorem isolationAction_eq_of_carrier_subset {S U : LocallyFiniteCarrier}
    (hSU : S.carrier ⊆ U.carrier) (T : TemperedDistribution ℝ ℂ)
    (hT : HasLocallyAtomicAction S T) (x : S.subtype) :
    T (U.isolationSchwartz (LocallyFiniteCarrier.inclusion hSU x)) =
      T (S.isolationSchwartz x) := by
  have hvanish : SchwartzVanishesOn S
      (U.isolationSchwartz (LocallyFiniteCarrier.inclusion hSU x) - S.isolationSchwartz x) := by
    intro y hy
    let yS : S.subtype := ⟨y,hy⟩
    change U.isolationSchwartz (LocallyFiniteCarrier.inclusion hSU x)
      (LocallyFiniteCarrier.inclusion hSU yS) - S.isolationSchwartz x yS = 0
    rw [U.isolationSchwartz_apply_subtype, S.isolationSchwartz_apply_subtype]
    simp only [EmbeddingLike.apply_eq_iff_eq]
    simp
  have h := hasLocallyAtomicAction_atomicOnCarrier S T hT _ hvanish
  simpa only [map_sub, sub_eq_zero] using h

end

end MeyerGeneralProblem
