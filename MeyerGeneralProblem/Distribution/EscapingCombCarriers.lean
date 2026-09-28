module

public import MeyerGeneralProblem.Distribution.ConvolvedMotifCoefficients
public import MeyerGeneralProblem.Distribution.PeriodicFourierHoleBlock
public import MeyerGeneralProblem.Distribution.IrrationalCombCosets
public import MeyerGeneralProblem.Distribution.CarrierUnion

@[expose] public section

/-!
# Locally finite unions of escaping actual comb supports

Only nonzero periodic coefficient supports and their finite motif translates
are unioned. The finite Fourier hole equations imply an explicit escape bound,
independent of motif depth. This constructs carriers, not an infinite sum of
distributions, and does not assert tempering or local atomicity of such a sum.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set
open scoped SchwartzMap FourierTransform

/-- A countable union is locally finite when only finitely many constituent
carriers meet each compact interval. No uniform separation is required. -/
def LocallyFiniteCarrier.escapingUnion (S : ℕ → LocallyFiniteCarrier)
    (hescape : ∀ a b : ℝ, ∃ N : ℕ, ∀ t, N ≤ t →
      (S t).carrier ∩ Icc a b = ∅) : LocallyFiniteCarrier where
  carrier := ⋃ t, (S t).carrier
  finite_inter_Icc a b := by
    obtain ⟨N,hN⟩ := hescape a b
    apply (Set.finite_iUnion fun i : Fin N => (S i).finite_inter_Icc a b).subset
    rintro x ⟨hx,hxI⟩
    obtain ⟨t,ht⟩ := Set.mem_iUnion.mp hx
    by_cases h : t < N
    · exact Set.mem_iUnion.mpr ⟨⟨t,h⟩,ht,hxI⟩
    · have : x ∈ (S t).carrier ∩ Icc a b := ⟨ht,hxI⟩
      rw [hN t (Nat.le_of_not_gt h)] at this
      exact this.elim

/-- The escaping union retains precisely the union of the given carriers. -/
theorem LocallyFiniteCarrier.escapingUnion_carrier (S : ℕ → LocallyFiniteCarrier)
    (hescape : ∀ a b : ℝ, ∃ N : ℕ, ∀ t, N ≤ t →
      (S t).carrier ∩ Icc a b = ∅) :
    (LocallyFiniteCarrier.escapingUnion S hescape).carrier = ⋃ t, (S t).carrier := rfl

/-- Each original carrier embeds in the genuine escaping union. -/
theorem LocallyFiniteCarrier.subset_escapingUnion (S : ℕ → LocallyFiniteCarrier)
    (hescape : ∀ a b : ℝ, ∃ N : ℕ, ∀ t, N ≤ t →
      (S t).carrier ∩ Icc a b = ∅) (t : ℕ) :
    (S t).carrier ⊆ (LocallyFiniteCarrier.escapingUnion S hescape).carrier :=
  Set.subset_iUnion (fun t => (S t).carrier) t

/-- Symmetric compact-interval escape suffices for the full locally finite
carrier interface, including intervals with arbitrary signed endpoints. -/
theorem escaping_inter_Icc_of_symmetric (S : ℕ → LocallyFiniteCarrier)
    (hescape : ∀ R : ℝ, ∃ N : ℕ, ∀ t, N ≤ t →
      (S t).carrier ∩ Icc (-R) R = ∅) :
    ∀ a b : ℝ, ∃ N : ℕ, ∀ t, N ≤ t → (S t).carrier ∩ Icc a b = ∅ := by
  intro a b
  obtain ⟨N,hN⟩ := hescape (max |a| |b|)
  refine ⟨N,fun t ht => Set.eq_empty_iff_forall_notMem.mpr ?_⟩
  rintro x ⟨hx,hlo,hhi⟩
  have hax : -max |a| |b| ≤ x := by
    have := neg_abs_le a
    have := le_max_left |a| |b|
    linarith
  have hxb : x ≤ max |a| |b| := le_trans hhi (le_trans (le_abs_self b) (le_max_right _ _))
  have hmem : x ∈ (S t).carrier ∩ Icc (-max |a| |b|) (max |a| |b|) := ⟨hx,hax,hxb⟩
  rw [hN t ht] at hmem
  exact hmem.elim

/-- The actual finite motif support inherits the source hole with a fixed
loss independent of the number of motif digits and of any internal gaps. -/
theorem convolvedMotifCarrier_abs_lower (m n : ℕ) [NeZero m]
    {c : ZMod (m*m) → ℂ} {ζ : ℂ} (hc : squareCyclicDFT m c = ζ • c)
    (hz : ∀ j : Fin (squareCyclicCentralZeroCount m), c (j.val : ZMod (m*m)) = 0)
    {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ : γ ≤ 1/4)
    {x : ℝ} (hx : x ∈ (convolvedMotifCarrier m n c γ).carrier) :
    (m : ℝ)/4-2 ≤ |x| := by
  obtain ⟨d,y,hy,rfl⟩ := Set.mem_iUnion.mp hx
  have hm : 1 ≤ (m : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne m)
  have hp := baseFiveMotifPosition_mem m n (Nat.pos_of_ne_zero (NeZero.ne m)) d
  have hp1 : baseFiveMotifPosition m n d ≤ 1/4 := by
    have hdiv : 1/(4*(m : ℝ)) ≤ (1 : ℝ)/4 := by
      apply (div_le_div_iff₀ (by positivity) (by norm_num)).mpr
      linarith
    exact le_trans hp.2.le hdiv
  have hshift : |γ+baseFiveMotifPosition m n d| ≤ 1 := by
    rw [abs_of_nonneg (add_nonneg hγ0 hp.1)]
    linarith
  have hsource := squarePeriodicCombSupport_abs_lower m hc hz hy
  have htriangle := abs_sub (γ+baseFiveMotifPosition m n d+y) (γ+baseFiveMotifPosition m n d)
  simp only [add_sub_cancel_left] at htriangle
  linarith

/-- An explicit depth-independent escape threshold for the actual physical
finite-convolution carrier; the bound uses no full fine-lattice union. -/
theorem convolvedMotifCarrier_inter_Icc_eq_empty (m n : ℕ) [NeZero m]
    {c : ZMod (m*m) → ℂ} {ζ : ℂ} (hc : squareCyclicDFT m c = ζ • c)
    (hz : ∀ j : Fin (squareCyclicCentralZeroCount m), c (j.val : ZMod (m*m)) = 0)
    {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ : γ ≤ 1/4) (R : ℝ)
    (hm : 4*R+8 < (m : ℝ)) :
    (convolvedMotifCarrier m n c γ).carrier ∩ Icc (-R) R = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro x ⟨hx,hR⟩
  have hlo := convolvedMotifCarrier_abs_lower m n hc hz hγ0 hγ hx
  have hhi : |x| ≤ R := abs_le.mpr hR
  linarith

/-- The actual Fourier transform of each finite convolved eigencomb remains
locally atomic on its original nonzero coefficient support. The symbol may
delete coefficients, so equality of nonzero supports is not asserted. -/
theorem convolvedMotifDistribution_fourier_hasLocallyAtomicAction (m n : ℕ) [NeZero m]
    {c : ZMod (m*m) → ℂ} {ζ : ℂ} (hc : squareCyclicDFT m c = ζ • c)
    (γ : ℝ) (z : ℂ) :
    HasLocallyAtomicAction (squarePeriodicCombSupport m c)
      (𝓕 (convolvedMotifDistribution m n c γ z)) := by
  have hM := squarePeriodicComb_mem_distributionalMeyerSpace m c ζ hc
  have hF := (mem_distributionalMeyerSpace_iff _ _).mp hM
  exact hasLocallyAtomicAction_fourier_finiteCombConvolution _ _ hF.2 _ _

/-- Genuine finite Fourier hole data at size `t+4`. Existence is proved
below from the finite Fourier theorem; these are not analytic certificates. -/
structure EscapingCombHoleData (t : ℕ) where
  /-- The actual fourth-root eigensector. -/
  sector : Fin 4
  /-- Original periodic coefficients. -/
  coefficient : ZMod ((t+4)*(t+4)) → ℂ
  /-- A genuine unit coefficient in the first period. -/
  unitResidue : ZMod ((t+4)*(t+4))
  /-- The chosen coefficient is exactly one. -/
  unit_coefficient : coefficient unitResidue = 1
  /-- Every original coefficient has norm at most one. -/
  coefficient_norm : ∀ j, ‖coefficient j‖ ≤ 1
  /-- The actual normalized finite Fourier eigenrelation. -/
  fourier_eigen : squareCyclicDFT (t+4) coefficient = fourthRootValue sector • coefficient
  /-- Actual initial zero coefficients, whose reflected zeros follow from Fourier. -/
  initial_zero : ∀ j : Fin (squareCyclicCentralZeroCount (t+4)),
    coefficient (j.val : ZMod ((t+4)*(t+4))) = 0

/-- Every size in the escaping family has actual normalized finite hole data. -/
theorem nonempty_escapingCombHoleData (t : ℕ) : Nonempty (EscapingCombHoleData t) := by
  obtain ⟨a,c,r,hr,hbound,he,hz⟩ := exists_squareCyclicDFT_centralHole_vector (t+4)
  exact ⟨⟨a,c,r,hr,hbound,he,hz⟩⟩

/-- A choice of actual proved finite hole vectors, with no extra hypothesis. -/
def canonicalEscapingCombHoleData (t : ℕ) : EscapingCombHoleData t :=
  Classical.choice (nonempty_escapingCombHoleData t)

/-- The physical carrier of one actual finite convolved hole block. -/
def EscapingCombHoleData.physicalCarrier {t : ℕ} (d : EscapingCombHoleData t)
    (n : ℕ) : LocallyFiniteCarrier :=
  convolvedMotifCarrier (t+4) n d.coefficient (irrationalCombOffset (t+4))

/-- The original nonzero coefficient support contains the Fourier support
after any finite motif convolution. It is not the full fine lattice. -/
def EscapingCombHoleData.fourierCarrier {t : ℕ} (d : EscapingCombHoleData t) :
    LocallyFiniteCarrier := squarePeriodicCombSupport (t+4) d.coefficient

/-- The physical support of a block misses the given compact interval at
an explicit size threshold, uniformly in its finite motif depth. -/
theorem EscapingCombHoleData.physicalCarrier_escape {t : ℕ} (d : EscapingCombHoleData t)
    (n : ℕ) (R : ℝ) (ht : 4*R+8 < ((t+4 : ℕ) : ℝ)) :
    (d.physicalCarrier n).carrier ∩ Icc (-R) R = ∅ :=
  convolvedMotifCarrier_inter_Icc_eq_empty (t+4) n d.fourier_eigen d.initial_zero
    (irrationalCombOffset_pos _).le (irrationalCombOffset_lt_quarter _).le R ht

/-- The original Fourier carrier also escapes, with the sharper source
threshold retained separately from the physical translation loss. -/
theorem EscapingCombHoleData.fourierCarrier_escape {t : ℕ} (d : EscapingCombHoleData t)
    (R : ℝ) (ht : 4*R+4 < ((t+4 : ℕ) : ℝ)) :
    d.fourierCarrier.carrier ∩ Icc (-R) R = ∅ :=
  squarePeriodicCombSupport_inter_Icc_eq_empty (t+4) d.fourier_eigen d.initial_zero R ht

/-- Arbitrary choices of the proved finite hole vectors and arbitrary
finite motif depths satisfy actual eventual physical support escape. -/
theorem escapingComb_physical_inter_Icc (d : ∀ t, EscapingCombHoleData t)
    (depth : ℕ → ℕ) :
    ∀ a b : ℝ, ∃ N : ℕ, ∀ t, N ≤ t →
      ((d t).physicalCarrier (depth t)).carrier ∩ Icc a b = ∅ := by
  apply escaping_inter_Icc_of_symmetric
  intro R
  obtain ⟨N,hN⟩ := exists_nat_gt (4*R+8)
  refine ⟨N,fun t ht => (d t).physicalCarrier_escape (depth t) R ?_⟩
  have hNt : (N : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  push_cast
  linarith

/-- The original nonzero Fourier carriers satisfy actual eventual compact
escape, without taking the union of any full fine lattices. -/
theorem escapingComb_fourier_inter_Icc (d : ∀ t, EscapingCombHoleData t) :
    ∀ a b : ℝ, ∃ N : ℕ, ∀ t, N ≤ t →
      (d t).fourierCarrier.carrier ∩ Icc a b = ∅ := by
  apply escaping_inter_Icc_of_symmetric
  intro R
  obtain ⟨N,hN⟩ := exists_nat_gt (4*R+4)
  refine ⟨N,fun t ht => (d t).fourierCarrier_escape R ?_⟩
  have hNt : (N : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  push_cast
  linarith

/-- The countable union of actual convolved physical support containers
is locally finite, for arbitrary finite motif depths. -/
def escapingPhysicalCombCarrier (d : ∀ t, EscapingCombHoleData t)
    (depth : ℕ → ℕ) : LocallyFiniteCarrier :=
  LocallyFiniteCarrier.escapingUnion (fun t => (d t).physicalCarrier (depth t))
    (escapingComb_physical_inter_Icc d depth)

/-- The countable union of original nonzero Fourier support containers is
locally finite by the actual finite Fourier central holes. -/
def escapingFourierCombCarrier (d : ∀ t, EscapingCombHoleData t) : LocallyFiniteCarrier :=
  LocallyFiniteCarrier.escapingUnion (fun t => (d t).fourierCarrier)
    (escapingComb_fourier_inter_Icc d)

/-- A single genuine locally finite carrier contains both physical and
Fourier-side block carriers. No infinite distribution sum is defined here. -/
def escapingCombCarrier (d : ∀ t, EscapingCombHoleData t) (depth : ℕ → ℕ) :
    LocallyFiniteCarrier := (escapingPhysicalCombCarrier d depth).union (escapingFourierCombCarrier d)

/-- Exact membership in the physical union, retaining its finite-block origin. -/
theorem mem_escapingPhysicalCombCarrier (d : ∀ t, EscapingCombHoleData t)
    (depth : ℕ → ℕ) (x : ℝ) :
    x ∈ (escapingPhysicalCombCarrier d depth).carrier ↔
      ∃ t, x ∈ ((d t).physicalCarrier (depth t)).carrier := Set.mem_iUnion

/-- Exact membership in the Fourier union uses original nonzero coefficient supports. -/
theorem mem_escapingFourierCombCarrier (d : ∀ t, EscapingCombHoleData t) (x : ℝ) :
    x ∈ (escapingFourierCombCarrier d).carrier ↔ ∃ t, x ∈ (d t).fourierCarrier.carrier :=
  Set.mem_iUnion

/-- Every actual physical block carrier is included in the common locally finite union. -/
theorem EscapingCombHoleData.physicalCarrier_subset_common
    (d : ∀ t, EscapingCombHoleData t) (depth : ℕ → ℕ) (t : ℕ) :
    ((d t).physicalCarrier (depth t)).carrier ⊆ (escapingCombCarrier d depth).carrier := by
  intro x hx
  exact Or.inl (Set.mem_iUnion.mpr ⟨t,hx⟩)

/-- Every original Fourier block carrier is included in the common locally finite union. -/
theorem EscapingCombHoleData.fourierCarrier_subset_common
    (d : ∀ t, EscapingCombHoleData t) (depth : ℕ → ℕ) (t : ℕ) :
    (d t).fourierCarrier.carrier ⊆ (escapingCombCarrier d depth).carrier := by
  intro x hx
  exact Or.inr (Set.mem_iUnion.mpr ⟨t,hx⟩)

/-- Each finite convolved block has actual physical local atomic action on
the common carrier. This statement does not exchange any infinite sums. -/
theorem escapingCombCarrier_block_hasLocallyAtomicAction
    (d : ∀ t, EscapingCombHoleData t) (depth : ℕ → ℕ) (t : ℕ) (z : ℂ) :
    HasLocallyAtomicAction (escapingCombCarrier d depth)
      (convolvedMotifDistribution (t+4) (depth t) (d t).coefficient
        (irrationalCombOffset (t+4)) z) :=
  hasLocallyAtomicAction_of_carrier_subset
    (EscapingCombHoleData.physicalCarrier_subset_common d depth t) _
    (convolvedMotifDistribution_hasLocallyAtomicAction _ _ _ _ _)

/-- Each actual Fourier-transformed finite block stays on the common
carrier, by exact finite convolution and finite Fourier eigenrelations. -/
theorem escapingCombCarrier_fourier_block_hasLocallyAtomicAction
    (d : ∀ t, EscapingCombHoleData t) (depth : ℕ → ℕ) (t : ℕ) (z : ℂ) :
    HasLocallyAtomicAction (escapingCombCarrier d depth)
      (𝓕 (convolvedMotifDistribution (t+4) (depth t) (d t).coefficient
        (irrationalCombOffset (t+4)) z)) :=
  hasLocallyAtomicAction_of_carrier_subset
    (EscapingCombHoleData.fourierCarrier_subset_common d depth t) _
    (convolvedMotifDistribution_fourier_hasLocallyAtomicAction _ _ (d t).fourier_eigen _ _)

/-- Canonical, unconditionally constructed common carriers exist for every
depth sequence, from the proved finite hole vectors and actual support escape. -/
def canonicalEscapingCombCarrier (depth : ℕ → ℕ) : LocallyFiniteCarrier :=
  escapingCombCarrier canonicalEscapingCombHoleData depth

/-- The finite blocks lie in the genuine common distributional Meyer
space; only individual already-defined tempered distributions occur here. -/
theorem escapingCombCarrier_block_mem_distributionalMeyerSpace
    (d : ∀ t, EscapingCombHoleData t) (depth : ℕ → ℕ) (t : ℕ) (z : ℂ) :
    convolvedMotifDistribution (t+4) (depth t) (d t).coefficient
      (irrationalCombOffset (t+4)) z ∈ DistributionalMeyerSpace (escapingCombCarrier d depth) :=
  (mem_distributionalMeyerSpace_iff _ _).mpr
    ⟨escapingCombCarrier_block_hasLocallyAtomicAction d depth t z,
      escapingCombCarrier_fourier_block_hasLocallyAtomicAction d depth t z⟩

/-- Every actual physical motif atom belongs to its prescribed irrational
rational coset, using rationality of the finite motif and fine lattice. -/
theorem EscapingCombHoleData.physicalCarrier_subset_coset {t : ℕ}
    (d : EscapingCombHoleData t) (n : ℕ) :
    (d.physicalCarrier n).carrier ⊆ irrationalCombCoset (t+4) := by
  intro x hx
  obtain ⟨w,y,hy,rfl⟩ := Set.mem_iUnion.mp hx
  obtain ⟨q,hq⟩ := baseFiveMotifPosition_rational (t+4) n w
  obtain ⟨r,hr⟩ := squarePeriodicCombSupport_rational (t+4) d.coefficient y hy
  refine ⟨q+r,?_⟩
  dsimp only
  rw [Rat.cast_add,hq,hr]
  exact (add_assoc _ _ _).symm

/-- Distinct actual physical blocks are disjoint, regardless of their
chosen finite hole vectors or motif depths. No affine independence is assumed. -/
theorem escapingComb_physicalCarriers_pairwiseDisjoint
    (d : ∀ t, EscapingCombHoleData t) (depth : ℕ → ℕ) :
    Pairwise (fun s t => Disjoint ((d s).physicalCarrier (depth s)).carrier
      ((d t).physicalCarrier (depth t)).carrier) := by
  intro s t hst
  apply (disjoint_irrationalCombCosets (show s+4 ≠ t+4 from fun h => hst (Nat.add_right_cancel h))).mono
  · exact (d s).physicalCarrier_subset_coset (depth s)
  · exact (d t).physicalCarrier_subset_coset (depth t)

end

end MeyerGeneralProblem
