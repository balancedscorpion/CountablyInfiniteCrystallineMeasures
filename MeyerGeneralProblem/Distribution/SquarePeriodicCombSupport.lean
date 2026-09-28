module

public import MeyerGeneralProblem.Distribution.SquarePeriodicComb

@[expose] public section

/-!
# Actual nonzero support and faithful lifting of periodic combs

The full fine lattice is used only as an isolation-test carrier. The
support carrier of a coefficient comb discards every zero coefficient;
its genuine local atomicity and coefficient recovery are proved directly.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set SchwartzMap
open scoped SchwartzMap FourierTransform

variable (m : ℕ) [NeZero m]

/-- The full lattice of spacing 1/m, used to construct isolation tests. -/
def squareCombLattice : LocallyFiniteCarrier where
  carrier := Set.range (fun n : ℤ => (n:ℝ)/(m:ℝ))
  finite_inter_Icc a b := by
    have hm : (0:ℝ)<m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
    apply ((Set.finite_Icc ⌈a*m⌉ ⌊b*m⌋).image
      (fun n : ℤ => (n:ℝ)/(m:ℝ))).subset
    rintro x ⟨⟨n,rfl⟩,hlo,hhi⟩
    exact ⟨n,⟨Int.ceil_le.mpr ((le_div_iff₀ hm).mp hlo),
      Int.le_floor.mpr ((div_le_iff₀ hm).mp hhi)⟩,rfl⟩

/-- The actual nonzero-coefficient carrier, not the union of full lattices. -/
def squarePeriodicCombSupport (w : ZMod (m*m) → ℂ) : LocallyFiniteCarrier :=
  (squareCombLattice m).restrict
    {x | ∃ n : ℤ, x=(n:ℝ)/(m:ℝ) ∧ w (n : ZMod (m*m))≠0}
    (by rintro x ⟨n,rfl,_⟩; exact ⟨n,rfl⟩)

/-- A point belongs exactly when a genuine nonzero coefficient occurs there. -/
theorem mem_squarePeriodicCombSupport (w : ZMod (m*m) → ℂ) (x : ℝ) :
    x ∈ (squarePeriodicCombSupport m w).carrier ↔
      ∃ n : ℤ, x=(n:ℝ)/(m:ℝ) ∧ w (n : ZMod (m*m))≠0 := Iff.rfl

/-- Vanishing on the actual nonzero coefficient support annihilates the
original absolutely convergent comb, including all zero coefficients. -/
theorem squarePeriodicComb_atomicOnCarrier (w : ZMod (m*m) → ℂ) :
    AtomicOnCarrier (squarePeriodicCombSupport m w) (squarePeriodicComb m w) := by
  intro f hf
  rw [squarePeriodicComb_apply]
  have hz : ∀ n : ℤ, w (n : ZMod (m*m))*f ((n:ℝ)/(m:ℝ))=0 := by
    intro n
    by_cases hn : w (n : ZMod (m*m))=0
    · rw [hn,zero_mul]
    · rw [hf _ ⟨n,rfl,hn⟩,mul_zero]
  simp only [hz,tsum_zero]

/-- The independent finite local-atomic formula holds on the exact support. -/
theorem squarePeriodicComb_hasLocallyAtomicAction (w : ZMod (m*m) → ℂ) :
    HasLocallyAtomicAction (squarePeriodicCombSupport m w) (squarePeriodicComb m w) :=
  atomicOnCarrier_hasLocallyAtomicAction _ _ (squarePeriodicComb_atomicOnCarrier m w)

/-- Genuine compact Schwartz isolation tests recover every original lattice
coefficient, so Fourier lifting cannot erase a nonzero finite vector. -/
theorem squarePeriodicComb_isolation_apply (w : ZMod (m*m) → ℂ) (n : ℤ) :
    squarePeriodicComb m w ((squareCombLattice m).isolationSchwartz
      ⟨(n:ℝ)/(m:ℝ),⟨n,rfl⟩⟩)=w (n : ZMod (m*m)) := by
  have hm : (m:ℝ)≠0 := by exact_mod_cast NeZero.ne m
  rw [squarePeriodicComb_apply]
  rw [tsum_eq_single n]
  · rw [(squareCombLattice m).isolationSchwartz_self,mul_one]
  · intro j hj
    rw [(squareCombLattice m).isolationSchwartz_of_mem_of_ne _ ⟨j,rfl⟩,mul_zero]
    intro h
    have hcast : (j:ℝ)=(n:ℝ) := (div_left_inj' hm).mp h
    exact hj (by exact_mod_cast hcast)

/-- The actual comb lift is injective on the finite coefficient space. -/
theorem squarePeriodicComb_injective : Function.Injective (squarePeriodicComb m) := by
  intro v w h
  funext k
  have he := congrArg (fun T : TemperedDistribution ℝ ℂ =>
    T ((squareCombLattice m).isolationSchwartz
      ⟨((k.val:ℤ):ℝ)/(m:ℝ),⟨(k.val:ℤ),rfl⟩⟩)) h
  rw [squarePeriodicComb_isolation_apply,squarePeriodicComb_isolation_apply] at he
  simpa only [Int.cast_natCast,ZMod.natCast_zmod_val] using he

/-- A nonzero original coefficient vector produces a nonzero distribution. -/
theorem squarePeriodicComb_ne_zero {w : ZMod (m*m) → ℂ} (hw : w≠0) :
    squarePeriodicComb m w≠0 := by
  intro h
  apply hw
  apply squarePeriodicComb_injective m
  rw [h]
  ext f
  simp [squarePeriodicComb_apply]

/-- A Fourier eigenvector yields a genuine Meyer distribution on its
actual nonzero coefficient support, with its eigenvalue retained. -/
theorem squarePeriodicComb_mem_distributionalMeyerSpace
    (w : ZMod (m*m) → ℂ) (z : ℂ)
    (hw : (m:ℂ)⁻¹ • ZMod.dft w=z • w) :
    squarePeriodicComb m w ∈ DistributionalMeyerSpace (squarePeriodicCombSupport m w) := by
  rw [mem_distributionalMeyerSpace_iff]
  refine ⟨squarePeriodicComb_hasLocallyAtomicAction m w,?_⟩
  rw [fourier_squarePeriodicComb_of_dft_eigen m w z hw]
  apply atomicOnCarrier_hasLocallyAtomicAction
  intro f hf
  simp only [smul_apply,squarePeriodicComb_atomicOnCarrier m w f hf,smul_zero]

end

end MeyerGeneralProblem
