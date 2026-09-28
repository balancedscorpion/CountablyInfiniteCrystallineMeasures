module

public import MeyerGeneralProblem.Carrier.GeneralIsolation
public import MeyerGeneralProblem.Distribution.ClosedSubmoduleAnnihilator

@[expose] public section

/-!
# Atomic action on an extensional locally finite carrier

`AtomicOnCarrier S T` is the global, intrinsic condition that `T` annihilates
the full Schwartz vanishing ideal of `S`.  `HasLocallyAtomicAction S T` is an
independent local condition: it quantifies a coefficient at every carrier
point and requires an exact finite atomic formula for each compactly supported
Schwartz test.

The global condition implies the local formula, and local coefficients are
uniquely recovered by isolating Schwartz bumps.  The converse for arbitrary
Schwartz tests additionally requires density of compactly supported smooth
functions in the Schwartz topology; it is not folded into either definition.
-/

open scoped SchwartzMap

namespace MeyerGeneralProblem

noncomputable section

/-- A tempered distribution is order-zero supported on `S` when it
annihilates every Schwartz function vanishing on the whole carrier. -/
def AtomicOnCarrier (S : LocallyFiniteCarrier)
    (T : TemperedDistribution ℝ ℂ) : Prop :=
  ∀ f : SchwartzMap ℝ ℂ, SchwartzVanishesOn S f → T f = 0

@[simp]
theorem atomicOnCarrier_iff_mem_schwartzAnnihilator
    (S : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ) :
    AtomicOnCarrier S T ↔
      T ∈ schwartzAnnihilator (schwartzVanishingSubmodule S) :=
  Iff.rfl

/-- A coefficient family gives the local atomic action of `T` on `S` if
every compactly supported Schwartz test has an exact finite atomic formula,
with the finite set containing every carrier point where the test is nonzero. -/
def IsLocallyAtomicCoefficientFamily
    (S : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ)
    (a : S.subtype → ℂ) : Prop :=
  ∀ f : SchwartzMap ℝ ℂ, HasCompactSupport f →
    ∃ E : Finset S.subtype,
      (∀ x : S.subtype, x ∉ E → f x = 0) ∧
      T f = ∑ x ∈ E, a x * f x

/-- A tempered distribution has a locally finite atomic action on `S` if it
admits a carrier-indexed coefficient family satisfying the compact-test
finite-sum formula. -/
def HasLocallyAtomicAction
    (S : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ) : Prop :=
  ∃ a : S.subtype → ℂ, IsLocallyAtomicCoefficientFamily S T a

/-- A compactly supported Schwartz test is nonzero at only finitely many
points of an extensional locally finite carrier. -/
theorem LocallyFiniteCarrier.exists_finite_nonzero_values_of_hasCompactSupport
    (S : LocallyFiniteCarrier) (f : SchwartzMap ℝ ℂ)
    (hf : HasCompactSupport f) :
    ∃ E : Finset S.subtype, ∀ x : S.subtype, x ∉ E → f x = 0 := by
  obtain ⟨R, hR⟩ :=
    (Metric.isBounded_iff_subset_ball 0).mp hf.isBounded
  let A : Set S.subtype :=
    Subtype.val ⁻¹' (S.carrier ∩ Set.Icc (-R) R)
  have hA : A.Finite :=
    (S.finite_inter_Icc (-R) R).preimage
      (Set.injOn_of_injective Subtype.val_injective)
  refine ⟨hA.toFinset, ?_⟩
  intro x hx
  by_contra hne
  have hsupp : (x : ℝ) ∈ Function.support f := hne
  have htsupp : (x : ℝ) ∈ tsupport f := subset_tsupport f hsupp
  have hball := hR htsupp
  have habs : |(x : ℝ)| < R := by
    simpa [Real.dist_eq] using hball
  have hxA : x ∈ A := by
    exact ⟨x.property, le_of_lt (neg_lt_of_abs_lt habs),
      le_of_lt (lt_of_abs_lt habs)⟩
  exact hx (hA.mem_toFinset.mpr hxA)

/-- The isolating Schwartz bump is compactly supported. -/
theorem LocallyFiniteCarrier.isolationSchwartz_hasCompactSupport
    (S : LocallyFiniteCarrier) (x : S.subtype) :
    HasCompactSupport (S.isolationSchwartz x) := by
  change HasCompactSupport
    (fun y : ℝ => ((S.isolationBump x y : ℝ) : ℂ))
  exact (S.isolationBump x).hasCompactSupport.comp_left
    (show ((0 : ℝ) : ℂ) = 0 by norm_num)

/-- The global vanishing-ideal condition supplies the canonical local atomic
coefficient family `x ↦ T (isolationSchwartz x)`. -/
theorem atomicOnCarrier_isLocallyAtomicCoefficientFamily
    (S : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier S T) :
    IsLocallyAtomicCoefficientFamily S T
      (fun x => T (S.isolationSchwartz x)) := by
  intro f hf
  obtain ⟨E, hE⟩ :=
    S.exists_finite_nonzero_values_of_hasCompactSupport f hf
  refine ⟨E, hE, ?_⟩
  let g : SchwartzMap ℝ ℂ :=
    f - ∑ x ∈ E, f x • S.isolationSchwartz x
  have hg : SchwartzVanishesOn S g := by
    intro y hy
    let yS : S.subtype := ⟨y, hy⟩
    change f y - (∑ x ∈ E, f x • S.isolationSchwartz x) y = 0
    rw [sub_eq_zero]
    simp only [_root_.sum_apply, smul_apply, smul_eq_mul]
    by_cases hyE : yS ∈ E
    · rw [Finset.sum_eq_single yS]
      · rw [S.isolationSchwartz_self, mul_one]
      · intro x hx hxy
        have hyx : yS ≠ x := Ne.symm hxy
        change f x * S.isolationSchwartz x yS = 0
        rw [S.isolationSchwartz_apply_subtype]
        simp [hyx]
      · exact fun hnot => (hnot hyE).elim
    · rw [Finset.sum_eq_zero]
      · exact hE yS hyE
      · intro x hx
        have hyx : yS ≠ x := fun h => hyE (h ▸ hx)
        change f x * S.isolationSchwartz x yS = 0
        rw [S.isolationSchwartz_apply_subtype]
        simp [hyx]
  have hzero : T g = 0 := hT g hg
  dsimp only [g] at hzero
  rw [map_sub, map_sum] at hzero
  simp only [map_smul, smul_eq_mul, sub_eq_zero] at hzero
  simpa only [mul_comm] using hzero

/-- Global atomicity implies the independently quantified compact-test local
atomic action. -/
theorem atomicOnCarrier_hasLocallyAtomicAction
    (S : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier S T) :
    HasLocallyAtomicAction S T :=
  ⟨fun x => T (S.isolationSchwartz x),
    atomicOnCarrier_isLocallyAtomicCoefficientFamily S T hT⟩

/-- Every local atomic coefficient is recovered by applying the distribution
to the corresponding isolating Schwartz bump. -/
theorem locallyAtomicCoefficient_eq_isolationAction
    (S : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ)
    (a : S.subtype → ℂ)
    (ha : IsLocallyAtomicCoefficientFamily S T a) (x : S.subtype) :
    a x = T (S.isolationSchwartz x) := by
  obtain ⟨E, hE, hsum⟩ :=
    ha (S.isolationSchwartz x) (S.isolationSchwartz_hasCompactSupport x)
  have hxE : x ∈ E := by
    by_contra hx
    have := hE x hx
    rw [S.isolationSchwartz_self] at this
    norm_num at this
  rw [hsum, Finset.sum_eq_single x]
  · rw [S.isolationSchwartz_self, mul_one]
  · intro y hy hyx
    rw [S.isolationSchwartz_apply_subtype]
    simp [hyx]
  · exact fun hx => (hx hxE).elim

/-- A local atomic action has at most one carrier coefficient family. -/
theorem locallyAtomicCoefficientFamily_unique
    (S : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ)
    {a b : S.subtype → ℂ}
    (ha : IsLocallyAtomicCoefficientFamily S T a)
    (hb : IsLocallyAtomicCoefficientFamily S T b) :
    a = b := by
  funext x
  rw [locallyAtomicCoefficient_eq_isolationAction S T a ha x,
    locallyAtomicCoefficient_eq_isolationAction S T b hb x]

/-- The local formula annihilates compactly supported Schwartz tests which
vanish on the carrier. -/
theorem hasLocallyAtomicAction_apply_eq_zero_of_hasCompactSupport
    (S : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ)
    (hT : HasLocallyAtomicAction S T)
    (f : SchwartzMap ℝ ℂ) (hfc : HasCompactSupport f)
    (hf : SchwartzVanishesOn S f) :
    T f = 0 := by
  obtain ⟨a, ha⟩ := hT
  obtain ⟨E, hE, hsum⟩ := ha f hfc
  rw [hsum]
  apply Finset.sum_eq_zero
  intro x hx
  rw [hf x x.property, mul_zero]

end

end MeyerGeneralProblem
