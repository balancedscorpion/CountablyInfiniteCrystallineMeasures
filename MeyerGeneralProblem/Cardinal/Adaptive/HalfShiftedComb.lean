module

public import MeyerGeneralProblem.Distribution.FiniteCombConvolution
public import MeyerGeneralProblem.Cardinal.Adaptive.HalfShiftedFourierMinor

@[expose] public section

/-!
# Whole half-shifted antiperiodic combs

Actual translation and dilation of the half-character integer comb produce
the whole distributions in `HIGH_ORDER_GAP_SURGERY.md` §2. Their complete
Fourier action retains both half shifts and the reciprocal Jacobian. These
are whole infinite combs, before imposing any finite physical/Fourier holes.
-/

namespace MeyerGeneralProblem.Adaptive

noncomputable section

open Set SchwartzMap
open scoped SchwartzMap FourierTransform

/-- The actual half-shifted grid point of index m and spacing `1/(2k)`. -/
def halfShiftedGridPoint (k : ℕ) (m : ℤ) : ℝ :=
  ((m : ℝ) + 1/2) / (2 * (k : ℝ))

theorem twice_cast_pos {k : ℕ} (hk : 1 ≤ k) : 0 < 2 * (k : ℝ) := by
  have : (0 : ℝ) < k := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hk
  positivity

/-- The half-character equals the integer power of -1 for both signs of n. -/
theorem halfInteger_character (n : ℤ) :
    fourier n ((1/2 : ℝ) : UnitAddCircle) = (-1 : ℂ)^n := by
  rw [fourier_coe_apply, ← Complex.exp_pi_mul_I, ← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

/-- The whole antiperiodic comb on `x_m + 2kℤ`, defined as an actual tempered
distribution through continuous Schwartz pullbacks. -/
def halfShiftedComb (k : ℕ) (hk : 1 ≤ k) (m : ℤ) : TemperedDistribution ℝ ℂ :=
  combDistributionTranslation (halfShiftedGridPoint k m)
    (combDistributionDilation (2*(k : ℝ)) (ne_of_gt (twice_cast_pos hk))
      (modulatedIntegerComb (1/2)))

/-- Exact complete physical action, with every positive and negative cell. -/
theorem halfShiftedComb_apply (k : ℕ) (hk : 1 ≤ k) (m : ℤ)
    (f : SchwartzMap ℝ ℂ) :
    halfShiftedComb k hk m f =
      ∑' n : ℤ, (-1 : ℂ)^n * f (halfShiftedGridPoint k m + 2*(k : ℝ)*n) := by
  simp only [halfShiftedComb, combDistributionTranslation_apply,
    combDistributionDilation_apply, modulatedIntegerComb_apply,
    combSchwartzDilation_apply, combSchwartzTranslation_apply, halfInteger_character]

/-- Exact full Fourier action of one shifted antiperiodic comb. The
normalization is the reciprocal lattice spacing, with a negative phase. -/
theorem fourier_halfShiftedComb_apply (k : ℕ) (hk : 1 ≤ k) (m : ℤ)
    (f : SchwartzMap ℝ ℂ) :
    𝓕 (halfShiftedComb k hk m) f = (1 / (2*(k : ℂ))) *
      ∑' s : ℤ, Complex.exp (-2 * (Real.pi : ℂ) * Complex.I *
        ((m : ℂ)+1/2) * ((s : ℂ)+1/2) / (4*(k : ℂ)^2)) *
          f (halfShiftedGridPoint k s) := by
  have hkpos := twice_cast_pos hk
  simp only [halfShiftedComb, fourier_combDistributionTranslation,
    fourier_combDistributionDilation, fourier_modulatedIntegerComb,
    map_smul, smul_apply, combDistributionModulation_apply,
    combDistributionDilation_apply, shiftedIntegerComb_apply,
    combSchwartzDilation_apply, combSchwartzModulation_apply,
    abs_of_pos hkpos, Complex.ofReal_inv, Complex.ofReal_mul,
    Complex.ofReal_ofNat, Complex.ofReal_natCast, smul_eq_mul, one_div]
  congr 1
  apply tsum_congr
  intro s
  rw [combModulationCharacter_eq_exp]
  have hpoint : (2*(k : ℝ))⁻¹ * (1/2 + (s : ℝ)) = halfShiftedGridPoint k s := by
    unfold halfShiftedGridPoint
    ring
  simp only [one_div] at hpoint
  rw [hpoint]
  congr 1
  congr 1
  unfold halfShiftedGridPoint
  push_cast
  ring

/-- The full Fourier phase at the two half-shifted grid indices. -/
def halfShiftedFourierPhase (k : ℕ) (m s : ℤ) : ℂ :=
  Complex.exp (-2 * (Real.pi : ℂ) * Complex.I *
    ((m : ℂ)+1/2) * ((s : ℂ)+1/2) / (4*(k : ℂ)^2))

/-- The matrix phase is exactly the negative modulation character at the
actual reciprocal grid point. -/
theorem halfShiftedFourierPhase_eq_character (k : ℕ) (m s : ℤ) :
    halfShiftedFourierPhase k m s =
      combModulationCharacter (-halfShiftedGridPoint k m) (halfShiftedGridPoint k s) := by
  rw [combModulationCharacter_eq_exp]
  unfold halfShiftedFourierPhase halfShiftedGridPoint
  congr 1
  push_cast
  ring

/-- Every full transformed-comb series is absolutely summable on Schwartz
tests; no infinite Fourier cell is omitted. -/
theorem summable_halfShiftedFourierPhase (k : ℕ) (hk : 1 ≤ k) (m : ℤ)
    (f : SchwartzMap ℝ ℂ) :
    Summable (fun s : ℤ => halfShiftedFourierPhase k m s *
      f (halfShiftedGridPoint k s)) := by
  have h := summable_weightedInteger_samples
    (fun s : ℤ => halfShiftedFourierPhase k m s) (B := 1) (by norm_num)
    (by intro s; rw [halfShiftedFourierPhase_eq_character, norm_combModulationCharacter])
    (combSchwartzTranslation (1/2)
      (combSchwartzDilation (2*(k : ℝ))⁻¹
        (inv_ne_zero (ne_of_gt (twice_cast_pos hk))) f))
  convert h using 1
  funext s
  rw [combSchwartzTranslation_apply, combSchwartzDilation_apply]
  congr 1
  unfold halfShiftedGridPoint
  ring_nf

/-- Any finite family of whole shifted antiperiodic combs. A consecutive
fundamental block is a later permissible choice of the finite index set. -/
def halfShiftedCombFamily (k : ℕ) (hk : 1 ≤ k) (I : Finset ℤ) (c : ℤ → ℂ) :
    TemperedDistribution ℝ ℂ :=
  ∑ m ∈ I, c m • halfShiftedComb k hk m

/-- The complete Fourier coefficient formula for a finite combination of
whole antiperiodic combs, as an absolutely convergent distributional action. -/
theorem fourier_halfShiftedCombFamily_apply (k : ℕ) (hk : 1 ≤ k)
    (I : Finset ℤ) (c : ℤ → ℂ) (f : SchwartzMap ℝ ℂ) :
    𝓕 (halfShiftedCombFamily k hk I c) f = (1/(2*(k : ℂ))) *
      ∑' s : ℤ, (∑ m ∈ I, c m * halfShiftedFourierPhase k m s) *
        f (halfShiftedGridPoint k s) := by
  have hs (m : ℤ) : Summable (fun s : ℤ => c m *
      (halfShiftedFourierPhase k m s * f (halfShiftedGridPoint k s))) :=
    (summable_halfShiftedFourierPhase k hk m f).mul_left (c m)
  simp only [halfShiftedCombFamily, FourierTransform.fourier_sum, FourierTransform.fourier_smul, sum_apply, smul_apply,
    smul_eq_mul, fourier_halfShiftedComb_apply]
  change (∑ m ∈ I, c m * ((1/(2*(k : ℂ))) *
    ∑' s : ℤ, halfShiftedFourierPhase k m s * f (halfShiftedGridPoint k s))) = _
  calc
    _ = (1/(2*(k : ℂ))) * (∑ m ∈ I, c m *
        ∑' s : ℤ, halfShiftedFourierPhase k m s * f (halfShiftedGridPoint k s)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _
      ring
    _ = (1/(2*(k : ℂ))) * ∑' s : ℤ,
        (∑ m ∈ I, c m * halfShiftedFourierPhase k m s) * f (halfShiftedGridPoint k s) := by
      congr 1
      simp_rw [Finset.sum_mul, mul_assoc]
      rw [Summable.tsum_finsetSum (fun m _ => hs m)]
      simp only [tsum_mul_left]

/-- The complete physical support of one antiperiodic comb, before holes. -/
def halfShiftedCombCarrier (k : ℕ) (hk : 1 ≤ k) (m : ℤ) : LocallyFiniteCarrier where
  carrier := Set.range (fun n : ℤ => halfShiftedGridPoint k m + 2*(k : ℝ)*n)
  finite_inter_Icc a b := by
    have hp := twice_cast_pos hk
    apply ((Set.finite_Icc ⌈(a-halfShiftedGridPoint k m)/(2*(k : ℝ))⌉
      ⌊(b-halfShiftedGridPoint k m)/(2*(k : ℝ))⌋).image
      (fun n : ℤ => halfShiftedGridPoint k m + 2*(k : ℝ)*n)).subset
    rintro x ⟨⟨n,rfl⟩,hlo,hhi⟩
    refine ⟨n,⟨Int.ceil_le.mpr ?_,Int.le_floor.mpr ?_⟩,rfl⟩
    · apply (div_le_iff₀ hp).mpr
      linarith
    · apply (le_div_iff₀ hp).mpr
      linarith

/-- The reciprocal half-shifted grid is an actual locally finite carrier. -/
def halfShiftedGridCarrier (k : ℕ) (hk : 1 ≤ k) : LocallyFiniteCarrier where
  carrier := Set.range (halfShiftedGridPoint k)
  finite_inter_Icc a b := by
    have hp := twice_cast_pos hk
    apply ((Set.finite_Icc ⌈a*(2*(k : ℝ))-1/2⌉ ⌊b*(2*(k : ℝ))-1/2⌋).image
      (halfShiftedGridPoint k)).subset
    rintro x ⟨⟨n,rfl⟩,hlo,hhi⟩
    refine ⟨n,⟨Int.ceil_le.mpr ?_,Int.le_floor.mpr ?_⟩,rfl⟩
    · have h := (le_div_iff₀ hp).mp hlo
      linarith
    · have h := (div_le_iff₀ hp).mp hhi
      linarith

/-- Physical atomicity is proved from the whole comb action. -/
theorem halfShiftedComb_atomicOnCarrier (k : ℕ) (hk : 1 ≤ k) (m : ℤ) :
    AtomicOnCarrier (halfShiftedCombCarrier k hk m) (halfShiftedComb k hk m) := by
  intro f hf
  rw [halfShiftedComb_apply]
  simp only [hf _ ⟨_,rfl⟩, mul_zero, tsum_zero]

/-- The whole Fourier transform is value-only on the reciprocal shifted grid. -/
theorem fourier_halfShiftedComb_atomicOnCarrier (k : ℕ) (hk : 1 ≤ k) (m : ℤ) :
    AtomicOnCarrier (halfShiftedGridCarrier k hk) (𝓕 (halfShiftedComb k hk m)) := by
  intro f hf
  rw [fourier_halfShiftedComb_apply]
  simp only [hf _ ⟨_,rfl⟩, mul_zero, tsum_zero]

/-- Shifting the grid index by the exact modulus moves one whole comb cell. -/
theorem halfShiftedGridPoint_add_modulus (k : ℕ) (hk : 1 ≤ k) (m n : ℤ) :
    halfShiftedGridPoint k (m + (4*(k : ℤ)^2)*n) =
      halfShiftedGridPoint k m + 2*(k : ℝ)*n := by
  have hn : (k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_zero_of_lt (lt_of_lt_of_le Nat.zero_lt_one hk))
  unfold halfShiftedGridPoint
  push_cast
  field_simp
  ring

/-- The physical comb is also value-only on the complete half-shifted grid. -/
theorem halfShiftedComb_atomicOnGrid (k : ℕ) (hk : 1 ≤ k) (m : ℤ) :
    AtomicOnCarrier (halfShiftedGridCarrier k hk) (halfShiftedComb k hk m) := by
  intro f hf
  rw [halfShiftedComb_apply]
  have hzero (n : ℤ) : f (halfShiftedGridPoint k m + 2*(k : ℝ)*n) = 0 :=
    hf _ ⟨m + (4*(k : ℤ)^2)*n, halfShiftedGridPoint_add_modulus k hk m n⟩
  simp only [hzero, mul_zero, tsum_zero]

/-- The whole comb's physical record is locally a finite value-only sum. -/
theorem halfShiftedComb_hasLocallyAtomicAction (k : ℕ) (hk : 1 ≤ k) (m : ℤ) :
    HasLocallyAtomicAction (halfShiftedGridCarrier k hk) (halfShiftedComb k hk m) :=
  atomicOnCarrier_hasLocallyAtomicAction _ _ (halfShiftedComb_atomicOnGrid k hk m)

/-- The complete transformed record has the same independently defined local
value-only property, on the actual discrete reciprocal grid. -/
theorem fourier_halfShiftedComb_hasLocallyAtomicAction (k : ℕ) (hk : 1 ≤ k) (m : ℤ) :
    HasLocallyAtomicAction (halfShiftedGridCarrier k hk) (𝓕 (halfShiftedComb k hk m)) :=
  atomicOnCarrier_hasLocallyAtomicAction _ _ (fourier_halfShiftedComb_atomicOnCarrier k hk m)

/-- The consecutive finite matrix is exactly the corresponding normalized
coefficient submatrix of the whole comb Fourier formula. -/
theorem halfShiftedComb_coefficient_eq_minor (k : ℕ) (r c : Fin (2*k^2)) :
    (1/(2*(k : ℂ))) * halfShiftedFourierPhase k
      ((k : ℤ)^2 + c) (-(k : ℤ)^2 + r) = halfShiftedFourierMinor k r c := by
  rw [halfShiftedFourierMinor_apply]
  unfold halfShiftedFourierPhase
  push_cast
  rfl

/-- The complete Fourier coefficient sequence is antiperiodic at exactly
`4*k^2`; this includes all positive and negative integer indices. -/
theorem halfShiftedFourierPhase_add_modulus (k : ℕ) (hk : 1 ≤ k) (m s : ℤ) :
    halfShiftedFourierPhase k m (s + 4*(k : ℤ)^2) =
      -halfShiftedFourierPhase k m s := by
  have hn : (k : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_zero_of_lt (lt_of_lt_of_le Nat.zero_lt_one hk))
  unfold halfShiftedFourierPhase
  have he : -2 * (Real.pi : ℂ) * Complex.I * ((m : ℂ)+1/2) *
      (((s + 4*(k : ℤ)^2 : ℤ) : ℂ)+1/2) / (4*(k : ℂ)^2) =
      (-2 * (Real.pi : ℂ) * Complex.I * ((m : ℂ)+1/2) *
        ((s : ℂ)+1/2) / (4*(k : ℂ)^2)) +
          ((-m : ℤ) : ℂ) * (2*(Real.pi : ℂ)*Complex.I) -
            ((Real.pi : ℂ)*Complex.I) := by
    push_cast
    field_simp
    ring
  rw [he, Complex.exp_sub, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I,
    Complex.exp_pi_mul_I]
  ring

end

end MeyerGeneralProblem.Adaptive
