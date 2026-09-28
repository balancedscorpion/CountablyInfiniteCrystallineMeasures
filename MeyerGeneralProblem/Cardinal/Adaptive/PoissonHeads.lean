module

public import MeyerGeneralProblem.Cardinal.Adaptive.HalfShiftedComb
public import MeyerGeneralProblem.Distribution.CompactSchwartzDensity

@[expose] public section

/-! # Actual coordinates of whole antiperiodic heads

Coordinates are obtained by applying the distributions to isolating Schwartz
tests on the complete grid. No coordinate certificate is assumed.
-/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open scoped SchwartzMap FourierTransform

/-- A consecutive fundamental block of exactly `4k²` grid indices. -/
def headIndex (k : ℕ) (i : Fin (4*k^2)) : ℤ := -(k : ℤ)^2 + i

/-- The Schwartz test extracting the actual coefficient at a grid point. -/
def gridCoefficientTest (k : ℕ) (hk : 1 ≤ k) (m : ℤ) : SchwartzMap ℝ ℂ :=
  (halfShiftedGridCarrier k hk).isolationSchwartz
    ⟨halfShiftedGridPoint k m, ⟨m,rfl⟩⟩

theorem halfShiftedGridPoint_injective (k : ℕ) (hk : 1 ≤ k) :
    Function.Injective (halfShiftedGridPoint k) := by
  intro m n h
  have hn : (2*(k : ℝ)) ≠ 0 := by positivity
  have he := (div_left_inj' hn).mp h
  have : (m : ℝ) = n := by linarith
  exact_mod_cast this

@[simp] theorem gridCoefficientTest_apply (k : ℕ) (hk : 1 ≤ k) (m n : ℤ) :
    gridCoefficientTest k hk m (halfShiftedGridPoint k n) = if n = m then 1 else 0 := by
  unfold gridCoefficientTest
  by_cases h : n = m
  · subst n
    rw [ite_eq_left rfl]
    exact (halfShiftedGridCarrier k hk).isolationSchwartz_self _
  · rw [ite_eq_right h]
    apply LocallyFiniteCarrier.isolationSchwartz_of_mem_of_ne
      (halfShiftedGridCarrier k hk) _ ⟨n,rfl⟩
      (fun he => h (halfShiftedGridPoint_injective k hk he))

/-- Actual physical coefficient evaluation, defined on every distribution. -/
def gridCoefficient (k : ℕ) (hk : 1 ≤ k) (m : ℤ) :
    TemperedDistribution ℝ ℂ →ₗ[ℂ] ℂ where
  toFun T := T (gridCoefficientTest k hk m)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem headIndex_cell_injective (k : ℕ) (hk : 1 ≤ k)
    (i j : Fin (4*k^2)) (n l : ℤ)
    (h : headIndex k i + (4*(k : ℤ)^2)*n =
      headIndex k j + (4*(k : ℤ)^2)*l) : i = j ∧ n = l := by
  have hi0 : (0 : ℤ) ≤ i := Int.natCast_nonneg _
  have hj0 : (0 : ℤ) ≤ j := Int.natCast_nonneg _
  have hi : (i : ℤ) < 4*(k : ℤ)^2 := by exact_mod_cast i.isLt
  have hj : (j : ℤ) < 4*(k : ℤ)^2 := by exact_mod_cast j.isLt
  have hp : (0 : ℤ) < 4*(k : ℤ)^2 := by positivity
  unfold headIndex at h
  have hnl : n = l := by
    rcases lt_trichotomy n l with hlt|he|hgt
    · have : n + 1 ≤ l := by omega
      nlinarith
    · exact he
    · have : l + 1 ≤ n := by omega
      nlinarith
  constructor
  · apply Fin.ext
    have : (i : ℤ) = j := by nlinarith [hnl]
    exact_mod_cast this
  · exact hnl

/-- Every full comb has exactly its expected coefficients in every cell. -/
theorem gridCoefficient_halfShiftedComb (k : ℕ) (hk : 1 ≤ k)
    (i j : Fin (4*k^2)) (l : ℤ) :
    gridCoefficient k hk (headIndex k j + (4*(k : ℤ)^2)*l)
      (halfShiftedComb k hk (headIndex k i)) =
        if i = j then (-1 : ℂ)^l else 0 := by
  change halfShiftedComb k hk (headIndex k i) (gridCoefficientTest k hk _) = _
  rw [halfShiftedComb_apply]
  simp_rw [← halfShiftedGridPoint_add_modulus k hk, gridCoefficientTest_apply]
  by_cases hij : i = j
  · subst j
    rw [ite_eq_left rfl, tsum_eq_single l]
    · simp
    · intro n hn
      have hne : headIndex k i + 4*(k : ℤ)^2*n ≠
          headIndex k i + 4*(k : ℤ)^2*l := by
        intro h
        exact hn (headIndex_cell_injective k hk i i n l h).2
      simp [hne]
  · rw [ite_eq_right hij]
    have hz : ∀ n : ℤ, (-1 : ℂ)^n *
        (if headIndex k i + 4*(k : ℤ)^2*n =
          headIndex k j + 4*(k : ℤ)^2*l then (1 : ℂ) else 0) = 0 := by
      intro n
      have hne : headIndex k i + 4*(k : ℤ)^2*n ≠
          headIndex k j + 4*(k : ℤ)^2*l := by
        intro h
        exact hij (headIndex_cell_injective k hk i j n l h).1
      simp [hne]
    simp only [hz, tsum_zero]

/-- Synthesis of every finite linear combination of the whole infinite combs. -/
def poissonHeadSynthesis (k : ℕ) (hk : 1 ≤ k) :
    (Fin (4*k^2) → ℂ) →ₗ[ℂ] TemperedDistribution ℝ ℂ where
  toFun c := ∑ i, c i • halfShiftedComb k hk (headIndex k i)
  map_add' c d := by
    ext f
    simp only [_root_.add_apply, sum_apply, smul_apply, smul_eq_mul, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' a c := by simp [Finset.smul_sum, smul_smul]

/-- Complete physical coefficients, obtained from actual tests. -/
theorem gridCoefficient_poissonHeadSynthesis (k : ℕ) (hk : 1 ≤ k)
    (c : Fin (4*k^2) → ℂ) (j : Fin (4*k^2)) (l : ℤ) :
    gridCoefficient k hk (headIndex k j + (4*(k : ℤ)^2)*l)
      (poissonHeadSynthesis k hk c) = (-1 : ℂ)^l * c j := by
  change gridCoefficient k hk _ (∑ i, c i • halfShiftedComb k hk (headIndex k i)) = _
  simp only [map_sum, map_smul, gridCoefficient_halfShiftedComb, smul_eq_mul]
  simp [mul_comm]

theorem poissonHeadSynthesis_injective (k : ℕ) (hk : 1 ≤ k) :
    Function.Injective (poissonHeadSynthesis k hk) := by
  intro c d h
  funext j
  have he := congrArg (gridCoefficient k hk (headIndex k j + (4*(k : ℤ)^2)*0)) h
  simpa only [gridCoefficient_poissonHeadSynthesis, zpow_zero, one_mul] using he

/-- The whole finite-dimensional head as a subspace of actual distributions. -/
def poissonHeadSpace (k : ℕ) (hk : 1 ≤ k) : Submodule ℂ (TemperedDistribution ℝ ℂ) :=
  (poissonHeadSynthesis k hk).range

/-- A genuine bijection with the entire defined head space, proved by physical
coefficient extraction and surjectivity onto all whole finite combinations. -/
def poissonHeadEquiv (k : ℕ) (hk : 1 ≤ k) :
    (Fin (4*k^2) → ℂ) ≃ₗ[ℂ] poissonHeadSpace k hk :=
  LinearEquiv.ofInjective (poissonHeadSynthesis k hk) (poissonHeadSynthesis_injective k hk)


/-- Actual Fourier coefficients of a whole comb, extracted with compact tests. -/
theorem gridCoefficient_fourier_halfShiftedComb (k : ℕ) (hk : 1 ≤ k) (m s : ℤ) :
    gridCoefficient k hk s (𝓕 (halfShiftedComb k hk m)) =
      (1/(2*(k : ℂ))) * halfShiftedFourierPhase k m s := by
  change 𝓕 (halfShiftedComb k hk m) (gridCoefficientTest k hk s) = _
  rw [fourier_halfShiftedComb_apply]
  simp_rw [gridCoefficientTest_apply]
  rw [tsum_eq_single s]
  · simp [halfShiftedFourierPhase]
  · intro b hb
    simp [hb]

/-- The Fourier observation map reads the actual transformed distribution. -/
def gridFourierCoefficient (k : ℕ) (hk : 1 ≤ k) (s : ℤ) :
    TemperedDistribution ℝ ℂ →ₗ[ℂ] ℂ where
  toFun T := gridCoefficient k hk s (𝓕 T)
  map_add' T U := by simp [FourierTransform.fourier_add]
  map_smul' c T := by simp [FourierTransform.fourier_smul]

/-- Fourier coordinates of every whole head combination, not a formal DFT assumption. -/
theorem gridFourierCoefficient_poissonHeadSynthesis (k : ℕ) (hk : 1 ≤ k)
    (c : Fin (4*k^2) → ℂ) (s : ℤ) :
    gridFourierCoefficient k hk s (poissonHeadSynthesis k hk c) =
      ∑ i, ((1/(2*(k : ℂ))) * halfShiftedFourierPhase k (headIndex k i) s) * c i := by
  change gridFourierCoefficient k hk s (∑ i, c i • halfShiftedComb k hk (headIndex k i)) = _
  simp only [map_sum, map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  change c i * gridCoefficient k hk s (𝓕 (halfShiftedComb k hk (headIndex k i))) = _
  rw [gridCoefficient_fourier_halfShiftedComb]
  ring

/-- Atomicity of every physical head source. -/
theorem poissonHeadSynthesis_atomic (k : ℕ) (hk : 1 ≤ k) (c : Fin (4*k^2) → ℂ) :
    AtomicOnCarrier (halfShiftedGridCarrier k hk) (poissonHeadSynthesis k hk c) := by
  intro f hf
  change (∑ i, c i • halfShiftedComb k hk (headIndex k i)) f = 0
  simp only [sum_apply, smul_apply, smul_eq_mul,
    halfShiftedComb_atomicOnGrid k hk _ f hf, mul_zero, Finset.sum_const_zero]

/-- Atomicity of the complete Fourier record of every head source. -/
theorem fourier_poissonHeadSynthesis_atomic (k : ℕ) (hk : 1 ≤ k) (c : Fin (4*k^2) → ℂ) :
    AtomicOnCarrier (halfShiftedGridCarrier k hk) (𝓕 (poissonHeadSynthesis k hk c)) := by
  intro f hf
  change 𝓕 (∑ i, c i • halfShiftedComb k hk (headIndex k i)) f = 0
  simp only [FourierTransform.fourier_sum, FourierTransform.fourier_smul,
    sum_apply, smul_apply, smul_eq_mul,
    fourier_halfShiftedComb_atomicOnCarrier k hk _ f hf, mul_zero, Finset.sum_const_zero]

/-- Coefficient observations determine a whole atomic tempered distribution:
the final passage from compact tests uses full Schwartz cutoff density. -/
theorem gridCoefficient_ext (k : ℕ) (hk : 1 ≤ k)
    {T U : TemperedDistribution ℝ ℂ}
    (hT : AtomicOnCarrier (halfShiftedGridCarrier k hk) T)
    (hU : AtomicOnCarrier (halfShiftedGridCarrier k hk) U)
    (h : ∀ m : ℤ, gridCoefficient k hk m T = gridCoefficient k hk m U) : T = U := by
  let S := halfShiftedGridCarrier k hk
  have hTU : AtomicOnCarrier S (T-U) := by
    intro f hf
    change T f - U f = 0
    rw [hT f hf, hU f hf, sub_self]
  have hc (x : S.subtype) : (T-U) (S.isolationSchwartz x) = 0 := by
    obtain ⟨m,hm⟩ := x.property
    have hx : x = ⟨halfShiftedGridPoint k m,⟨m,rfl⟩⟩ := Subtype.ext hm.symm
    subst x
    exact sub_eq_zero.mpr (h m)
  have hcompact (f : SchwartzMap ℝ ℂ) (hf : HasCompactSupport f) : (T-U) f = 0 := by
    obtain ⟨E,_,he⟩ := atomicOnCarrier_isLocallyAtomicCoefficientFamily S (T-U) hTU f hf
    rw [he]
    simp only [hc, zero_mul, Finset.sum_const_zero]
  ext f
  have hlimit := ((T-U).continuous.tendsto f).comp (compactSchwartzApproximation_tendsto f)
  have hzero : Filter.Tendsto (fun N : ℕ => (T-U) (compactSchwartzApproximation N f))
      Filter.atTop (nhds (0 : ℂ)) := by
    simp only [hcompact _ (compactSchwartzApproximation_hasCompactSupport _ _)]
    exact tendsto_const_nhds
  have he : (T-U) f = 0 := tendsto_nhds_unique hlimit hzero
  exact sub_eq_zero.mp he


/-- Every integer grid index belongs to one fundamental block cell. -/
theorem exists_headIndex_cell (k : ℕ) (hk : 1 ≤ k) (m : ℤ) :
    ∃ (i : Fin (4*k^2)) (n : ℤ), m = headIndex k i + 4*(k : ℤ)^2*n := by
  have hp : (0 : ℤ) < 4*(k : ℤ)^2 := by positivity
  let r := (m+(k : ℤ)^2) % (4*(k : ℤ)^2)
  have hr0 : 0 ≤ r := Int.emod_nonneg _ (ne_of_gt hp)
  have hrlt : r < 4*(k : ℤ)^2 := Int.emod_lt_of_pos _ hp
  let i : Fin (4*k^2) := ⟨r.toNat, (Int.toNat_lt hr0).mpr (by exact_mod_cast hrlt)⟩
  refine ⟨i, (m+(k : ℤ)^2)/(4*(k : ℤ)^2), ?_⟩
  have hir : (i : ℤ) = r := Int.toNat_of_nonneg hr0
  have he := Int.emod_add_mul_ediv (m+(k : ℤ)^2) (4*(k : ℤ)^2)
  dsimp [headIndex]
  rw [hir]
  dsimp [r]
  nlinarith

/-- Intrinsic complete atomic antiperiodic head condition. It quantifies all
integer coefficients of an actual tempered distribution, not chosen data. -/
def IsAntiperiodicHead (k : ℕ) (hk : 1 ≤ k) (T : TemperedDistribution ℝ ℂ) : Prop :=
  AtomicOnCarrier (halfShiftedGridCarrier k hk) T ∧
    ∀ m n : ℤ, gridCoefficient k hk (m+4*(k : ℤ)^2*n) T =
      (-1 : ℂ)^n * gridCoefficient k hk m T

theorem poissonHeadSynthesis_isAntiperiodic (k : ℕ) (hk : 1 ≤ k)
    (c : Fin (4*k^2) → ℂ) : IsAntiperiodicHead k hk (poissonHeadSynthesis k hk c) := by
  refine ⟨poissonHeadSynthesis_atomic k hk c, ?_⟩
  intro m n
  obtain ⟨i,l,rfl⟩ := exists_headIndex_cell k hk m
  have he : headIndex k i + 4*(k : ℤ)^2*l + 4*(k : ℤ)^2*n =
      headIndex k i + 4*(k : ℤ)^2*(l+n) := by ring
  rw [he, gridCoefficient_poissonHeadSynthesis, gridCoefficient_poissonHeadSynthesis,
    zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
  ring

/-- Exhaustion of all intrinsic atomic antiperiodic sources, using their own
physical coefficients. No Fourier record or convergence certificate is assumed. -/
theorem antiperiodicHead_eq_synthesis (k : ℕ) (hk : 1 ≤ k)
    (T : TemperedDistribution ℝ ℂ) (hT : IsAntiperiodicHead k hk T) :
    T = poissonHeadSynthesis k hk (fun i => gridCoefficient k hk (headIndex k i) T) := by
  apply gridCoefficient_ext k hk hT.1 (poissonHeadSynthesis_atomic k hk _)
  intro m
  obtain ⟨i,n,rfl⟩ := exists_headIndex_cell k hk m
  rw [hT.2, gridCoefficient_poissonHeadSynthesis]

/-- The finite head range is precisely the complete intrinsic antiperiodic
atomic source class; this equivalence includes both directions. -/
theorem mem_poissonHeadSpace_iff (k : ℕ) (hk : 1 ≤ k) (T : TemperedDistribution ℝ ℂ) :
    T ∈ poissonHeadSpace k hk ↔ IsAntiperiodicHead k hk T := by
  constructor
  · rintro ⟨c,rfl⟩
    exact poissonHeadSynthesis_isAntiperiodic k hk c
  · intro h
    exact ⟨_, (antiperiodicHead_eq_synthesis k hk T h).symm⟩


private theorem grid_modulation_character (k : ℕ) (hk : 1 ≤ k) (n s : ℤ) :
    combModulationCharacter (2*(k : ℝ)*n) (halfShiftedGridPoint k s) = (-1 : ℂ)^n := by
  have hn : (k : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_zero_of_lt (lt_of_lt_of_le Nat.zero_lt_one hk)
  rw [combModulationCharacter_eq_exp]
  unfold halfShiftedGridPoint
  have he : 2*(Real.pi : ℂ)*Complex.I*((2*(k : ℝ)*(n : ℝ) : ℝ) : ℂ)*
      ((((s : ℝ)+1/2)/(2*(k : ℝ)) : ℝ) : ℂ) =
      ((n*s : ℤ) : ℂ)*(2*(Real.pi : ℂ)*Complex.I) +
      (n : ℂ)*((Real.pi : ℂ)*Complex.I) := by
    push_cast
    field_simp
  rw [he, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I,
    Complex.exp_int_mul, Complex.exp_pi_mul_I, one_mul]

/-- Fourier atomicity on the whole grid forces the actual translation
eigenvalue at every integer multiple of the complete head period. -/
theorem translate_grid_atomic_fourier (k : ℕ) (hk : 1 ≤ k)
    (T : TemperedDistribution ℝ ℂ)
    (hF : AtomicOnCarrier (halfShiftedGridCarrier k hk) (𝓕 T)) (n : ℤ) :
    combDistributionTranslation (-(2*(k : ℝ)*n)) T = (-1 : ℂ)^n • T := by
  have he : 𝓕 (combDistributionTranslation (-(2*(k : ℝ)*n)) T) =
      𝓕 ((-1 : ℂ)^n • T) := by
    rw [fourier_combDistributionTranslation, neg_neg, FourierTransform.fourier_smul]
    ext f
    change (𝓕 T) (combSchwartzModulation (2*(k : ℝ)*n) f) = (-1 : ℂ)^n * (𝓕 T) f
    apply sub_eq_zero.mp
    have hs : (-1 : ℂ)^n * (𝓕 T) f = (𝓕 T) ((-1 : ℂ)^n • f) := by simp
    rw [hs, ← map_sub]
    apply hF
    rintro x ⟨s,rfl⟩
    simp only [_root_.sub_apply, combSchwartzModulation_apply, grid_modulation_character k hk,
      _root_.smul_apply, smul_eq_mul, sub_self]
  have hi := congrArg (fun S : TemperedDistribution ℝ ℂ => 𝓕⁻ S) he
  simpa only [FourierTransform.fourierInv_fourier_eq] using hi

/-- Translation of an actual atomic source shifts its extracted grid
coefficients, proved by comparing the isolating tests on the entire carrier. -/
theorem gridCoefficient_translate (k : ℕ) (hk : 1 ≤ k)
    (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier (halfShiftedGridCarrier k hk) T) (m n : ℤ) :
    gridCoefficient k hk m (combDistributionTranslation (-(2*(k : ℝ)*n)) T) =
      gridCoefficient k hk (m+4*(k : ℤ)^2*n) T := by
  change T (combSchwartzTranslation (-(2*(k : ℝ)*n)) (gridCoefficientTest k hk m)) =
    T (gridCoefficientTest k hk (m+4*(k : ℤ)^2*n))
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply hT
  rintro x ⟨s,rfl⟩
  have hp : -(2*(k : ℝ)*n) + halfShiftedGridPoint k s =
      halfShiftedGridPoint k (s+4*(k : ℤ)^2*(-n)) := by
    rw [halfShiftedGridPoint_add_modulus k hk]
    push_cast
    ring
  simp only [_root_.sub_apply, combSchwartzTranslation_apply, hp, gridCoefficientTest_apply]
  have he : s+4*(k : ℤ)^2*(-n) = m ↔ s = m+4*(k : ℤ)^2*n := by
    constructor <;> intro h <;> nlinarith
  simp only [he, sub_self]

/-- Complete finite-cap exhaustion for the matched half-grid: both entire
value-only records force the intrinsic antiperiodic coefficient law. -/
theorem atomic_grid_pair_isAntiperiodicHead (k : ℕ) (hk : 1 ≤ k)
    (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier (halfShiftedGridCarrier k hk) T)
    (hF : AtomicOnCarrier (halfShiftedGridCarrier k hk) (𝓕 T)) : IsAntiperiodicHead k hk T := by
  refine ⟨hT, ?_⟩
  intro m n
  rw [← gridCoefficient_translate k hk T hT m n, translate_grid_atomic_fourier k hk T hF n,
    map_smul, smul_eq_mul]

/-- The whole head equals the COMPLETE physical/Fourier atomic source space
on the two matched half-grids. This is exhaustion, not just containment. -/
theorem mem_poissonHeadSpace_iff_atomic_pair (k : ℕ) (hk : 1 ≤ k)
    (T : TemperedDistribution ℝ ℂ) :
    T ∈ poissonHeadSpace k hk ↔
      AtomicOnCarrier (halfShiftedGridCarrier k hk) T ∧
      AtomicOnCarrier (halfShiftedGridCarrier k hk) (𝓕 T) := by
  constructor
  · rintro ⟨c,rfl⟩
    exact ⟨poissonHeadSynthesis_atomic k hk c, fourier_poissonHeadSynthesis_atomic k hk c⟩
  · rintro ⟨hT,hF⟩
    exact (mem_poissonHeadSpace_iff k hk T).mpr (atomic_grid_pair_isAntiperiodicHead k hk T hT hF)


instance poissonHeadSpace_finiteDimensional (k : ℕ) (hk : 1 ≤ k) :
    FiniteDimensional ℂ (poissonHeadSpace k hk) :=
  (poissonHeadEquiv k hk).finiteDimensional

/-- The dimension count is for the complete actual double-grid source space. -/
theorem poissonHeadSpace_finrank (k : ℕ) (hk : 1 ≤ k) :
    Module.finrank ℂ (poissonHeadSpace k hk) = 4*k^2 := by
  rw [← (poissonHeadEquiv k hk).finrank_eq, Module.finrank_pi, Fintype.card_fin]

end
end MeyerGeneralProblem.Adaptive
