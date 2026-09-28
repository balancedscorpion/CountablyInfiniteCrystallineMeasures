module

public import MeyerGeneralProblem.Distribution.FiniteCombConvolutionSupport
public import Mathlib.NumberTheory.Real.Irrational
import all Mathlib.NumberTheory.Real.Irrational

@[expose] public section

/-!
# Actual irrational offsets separating rational comb cosets

The explicit offsets √2/(10(m+1)) lie in (0,1/4). Their pairwise
differences are nonzero rational multiples of √2, so their rational
cosets are disjoint. Rational fine-lattice and finite-convolution
supports lie in these cosets after translation. The rational cosets
themselves are not asserted to be locally finite.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set SchwartzMap
open scoped SchwartzMap FourierTransform

/-- The explicit small irrational offset assigned to the mth comb block. -/
def irrationalCombOffset (m : ℕ) : ℝ := Real.sqrt 2/(10*((m:ℝ)+1))

/-- Every actual offset is strictly positive, including the zero index. -/
theorem irrationalCombOffset_pos (m : ℕ) : 0 < irrationalCombOffset m := by
  unfold irrationalCombOffset
  positivity

/-- Every actual offset lies strictly below one quarter, with no large-index premise. -/
theorem irrationalCombOffset_lt_quarter (m : ℕ) : irrationalCombOffset m<1/4 := by
  unfold irrationalCombOffset
  apply (div_lt_iff₀ (by positivity : (0:ℝ)<10*((m:ℝ)+1))).mpr
  have hm : (0:ℝ)≤m := Nat.cast_nonneg m
  have hs : Real.sqrt 2<2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2),Real.sqrt_nonneg (2:ℝ)]
  nlinarith

def offsetRationalFactor (m : ℕ) : ℚ := 1/(10*((m:ℚ)+1))

private theorem offsetRationalFactor_injective : Function.Injective offsetRationalFactor := by
  intro m n h
  unfold offsetRationalFactor at h
  rw [one_div,one_div,inv_inj] at h
  have hc : (m:ℚ)=(n:ℚ) := by linarith
  exact_mod_cast hc

private theorem irrationalCombOffset_eq_factor (m : ℕ) :
    irrationalCombOffset m=(offsetRationalFactor m:ℝ)*Real.sqrt 2 := by
  unfold irrationalCombOffset offsetRationalFactor
  push_cast
  ring

/-- Distinct offsets have irrational difference, proved from a nonzero
rational factor rather than an assumed independence condition. -/
theorem irrational_irrationalCombOffset_sub {m n : ℕ} (hmn : m≠n) :
    Irrational (irrationalCombOffset m-irrationalCombOffset n) := by
  have hfactor : offsetRationalFactor m-offsetRationalFactor n≠0 :=
    sub_ne_zero.mpr (fun h => hmn (offsetRationalFactor_injective h))
  rw [irrationalCombOffset_eq_factor,irrationalCombOffset_eq_factor,← sub_mul,← Rat.cast_sub]
  exact irrational_sqrt_two.ratCast_mul hfactor

/-- Actual offsets remain distinct after arbitrary rational translations. -/
theorem irrationalCombOffset_add_rat_ne {m n : ℕ} (hmn : m≠n) (q r : ℚ) :
    irrationalCombOffset m+(q:ℝ)≠irrationalCombOffset n+(r:ℝ) := by
  intro h
  apply irrational_irrationalCombOffset_sub hmn
  refine ⟨r-q,?_⟩
  push_cast
  linarith

/-- Both the block index and its rational displacement are recovered from
the actual real point in the explicit family of irrational cosets. -/
theorem irrationalCombOffset_add_rat_injective :
    Function.Injective (fun p : ℕ × ℚ => irrationalCombOffset p.1+(p.2:ℝ)) := by
  rintro ⟨m,q⟩ ⟨n,r⟩ h
  have hmn : m=n := by
    by_contra hmn
    exact irrationalCombOffset_add_rat_ne hmn q r h
  subst n
  apply Prod.ext
  · rfl
  · exact_mod_cast add_left_cancel h

/-- The actual rational coset containing one block's shifted rational atoms.
This ambient set is not presented as a locally finite carrier. -/
def irrationalCombCoset (m : ℕ) : Set ℝ :=
  Set.range (fun q : ℚ => irrationalCombOffset m+(q:ℝ))

/-- Distinct explicit offsets determine disjoint actual rational cosets. -/
theorem disjoint_irrationalCombCosets {m n : ℕ} (hmn : m≠n) :
    Disjoint (irrationalCombCoset m) (irrationalCombCoset n) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨q,hq⟩ ⟨r,hr⟩
  exact irrationalCombOffset_add_rat_ne hmn q r (hq.trans hr.symm)

/-- Pairwise disjointness of all explicit rational cosets. -/
theorem irrationalCombCosets_pairwiseDisjoint :
    Pairwise (fun m n : ℕ => Disjoint (irrationalCombCoset m) (irrationalCombCoset n)) :=
  fun _ _ h => disjoint_irrationalCombCosets h

/-- Any actual supports lying in distinct explicit cosets are disjoint. -/
theorem disjoint_of_subset_irrationalCombCosets {m n : ℕ} (hmn : m≠n)
    {A B : Set ℝ} (hA : A⊆irrationalCombCoset m) (hB : B⊆irrationalCombCoset n) :
    Disjoint A B := (disjoint_irrationalCombCosets hmn).mono hA hB

/-- A rational shift followed by any rational fine-lattice displacement
lies in the actual offset coset; positivity of the lattice size is not needed here. -/
theorem shifted_rational_lattice_mem_irrationalCombCoset
    (m k : ℕ) (q : ℚ) (j : ℤ) :
    irrationalCombOffset m+(q:ℝ)+(j:ℝ)/(k:ℝ) ∈ irrationalCombCoset m := by
  refine ⟨q+(j:ℚ)/(k:ℚ),?_⟩
  push_cast
  ring

/-- Rational shifts of fine-lattice points belonging to different blocks
cannot collide, with their actual scales and integer indices retained. -/
theorem shifted_rational_lattice_ne {m n : ℕ} (hmn : m≠n)
    (k l : ℕ) (q r : ℚ) (j h : ℤ) :
    irrationalCombOffset m+(q:ℝ)+(j:ℝ)/(k:ℝ)≠
      irrationalCombOffset n+(r:ℝ)+(h:ℝ)/(l:ℝ) := by
  have he := irrationalCombOffset_add_rat_ne hmn
    (q+(j:ℚ)/(k:ℚ)) (r+(h:ℚ)/(l:ℚ))
  simpa only [Rat.cast_add,Rat.cast_div,Rat.cast_intCast,Rat.cast_natCast,← add_assoc] using he

/-- Translation of an actual rational carrier lands in the prescribed coset. -/
theorem translatedCarrier_subset_irrationalCombCoset (m : ℕ) (S : LocallyFiniteCarrier)
    (hS : ∀ x ∈ S.carrier, ∃ q : ℚ, (q:ℝ)=x) :
    (S.translate (irrationalCombOffset m)).carrier⊆irrationalCombCoset m := by
  rintro x ⟨y,hy,rfl⟩
  obtain ⟨q,hq⟩ := hS y hy
  refine ⟨q,?_⟩
  change irrationalCombOffset m+(q:ℝ)=irrationalCombOffset m+y
  rw [hq]

/-- Actual nonzero-coefficient periodic-comb support is rational, not just
contained in an abstract equinumerous copy of the rational lattice. -/
theorem squarePeriodicCombSupport_rational (k : ℕ) [NeZero k]
    (w : ZMod (k*k) → ℂ) :
    ∀ x ∈ (squarePeriodicCombSupport k w).carrier, ∃ q : ℚ, (q:ℝ)=x := by
  rintro x ⟨j,rfl,_⟩
  refine ⟨(j:ℚ)/(k:ℚ),?_⟩
  push_cast
  rfl

/-- Actual finite rational motif shifts preserve rational support before
the explicit irrational block translation. -/
theorem finiteConvolutionCarrier_translate_subset_irrationalCombCoset
    {ι : Type*} [Fintype ι] (m : ℕ) (S : LocallyFiniteCarrier) (a : ι → ℝ)
    (hS : ∀ x ∈ S.carrier, ∃ q : ℚ, (q:ℝ)=x)
    (ha : ∀ i, ∃ q : ℚ, (q:ℝ)=a i) :
    ((finiteCombConvolutionCarrier S a).translate (irrationalCombOffset m)).carrier⊆
      irrationalCombCoset m := by
  apply translatedCarrier_subset_irrationalCombCoset
  intro x hx
  obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hx
  obtain ⟨y,hy,rfl⟩ := hi
  obtain ⟨q,hq⟩ := ha i
  obtain ⟨r,hr⟩ := hS y hy
  refine ⟨q+r,?_⟩
  rw [Rat.cast_add,hq,hr]

/-- The actual periodic comb convolved with any finite rational motif and
translated by its prescribed offset lies in the corresponding rational coset. -/
theorem periodicFiniteConvolutionCarrier_subset_irrationalCombCoset
    {ι : Type*} [Fintype ι] (m k : ℕ) [NeZero k]
    (w : ZMod (k*k) → ℂ) (a : ι → ℝ) (ha : ∀ i, ∃ q : ℚ, (q:ℝ)=a i) :
    ((finiteCombConvolutionCarrier (squarePeriodicCombSupport k w) a).translate
      (irrationalCombOffset m)).carrier⊆irrationalCombCoset m :=
  finiteConvolutionCarrier_translate_subset_irrationalCombCoset m _ a
    (squarePeriodicCombSupport_rational k w) ha

end

end MeyerGeneralProblem
