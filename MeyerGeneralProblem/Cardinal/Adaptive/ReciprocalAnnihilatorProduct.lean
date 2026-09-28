module

public import MeyerGeneralProblem.Cardinal.Adaptive.FiniteFourierProducts
public import MeyerGeneralProblem.Distribution.AtomicOnCarrier

@[expose] public section

/-! # Actual finite-stage reciprocal annihilator

The product uses both scales s and its reciprocal for each chosen block.
Its complete Fourier series is indexed by exactly twice the number of blocks.
-/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open Function
open scoped BigOperators ContDiff FourierTransform

/-- Actual paired product G_M, including both reciprocal directions. -/
def reciprocalAnnihilatorProduct (M : ℕ) (P R : Fin M → ℕ)
    (hP : ∀ j, 1 ≤ P j) (hR : ∀ j, 1 ≤ R j) (s : Fin M → ℝ) (x : ℝ) : ℂ :=
  ∏ j, complexPhaseAnnihilator (P j) (R j) (hP j) (hR j) (s j*x) *
    complexPhaseAnnihilator (P j) (R j) (hP j) (hR j) ((s j)⁻¹*x)

/-- The two real frequencies for every factor, with no independence assumed. -/
def reciprocalProductScales (M : ℕ) (s : Fin M → ℝ) : Fin (M+M) → ℝ :=
  Fin.addCases s (fun j => (s j)⁻¹)

/-- Duplicate the chosen annihilator family across the two reciprocal arms. -/
def reciprocalProductFunctions (M : ℕ) (P R : Fin M → ℕ)
    (hP : ∀ j, 1 ≤ P j) (hR : ∀ j, 1 ≤ R j) : Fin (M+M) → ℝ → ℂ :=
  Fin.addCases (fun j => complexPhaseAnnihilator (P j) (R j) (hP j) (hR j))
    (fun j => complexPhaseAnnihilator (P j) (R j) (hP j) (hR j))

theorem reciprocalProductFunctions_smooth (M : ℕ) (P R : Fin M → ℕ)
    (hP : ∀ j, 1 ≤ P j) (hR : ∀ j, 1 ≤ R j) (j : Fin (M+M)) :
    ContDiff ℝ ∞ (reciprocalProductFunctions M P R hP hR j) := by
  induction j using Fin.addCases with
  | left j => simpa only [reciprocalProductFunctions, Fin.addCases_left, Fin.addCases_right] using complexPhaseAnnihilator_smooth (P j) (R j) (hP j) (hR j)
  | right j => simpa only [reciprocalProductFunctions, Fin.addCases_left, Fin.addCases_right] using complexPhaseAnnihilator_smooth (P j) (R j) (hP j) (hR j)

theorem reciprocalProductFunctions_periodic (M : ℕ) (P R : Fin M → ℕ)
    (hP : ∀ j, 1 ≤ P j) (hR : ∀ j, 1 ≤ R j) (j : Fin (M+M)) :
    Periodic (reciprocalProductFunctions M P R hP hR j) 1 := by
  induction j using Fin.addCases with
  | left j => simpa only [reciprocalProductFunctions, Fin.addCases_left, Fin.addCases_right] using complexPhaseAnnihilator_periodic (P j) (R j) (hP j) (hR j)
  | right j => simpa only [reciprocalProductFunctions, Fin.addCases_left, Fin.addCases_right] using complexPhaseAnnihilator_periodic (P j) (R j) (hP j) (hR j)

theorem reciprocalProductScales_bound (M : ℕ) (s : Fin M → ℝ)
    (hs : ∀ j, s j ∈ Set.Icc 1 2) (j : Fin (M+M)) :
    |reciprocalProductScales M s j| ≤ 2 := by
  induction j using Fin.addCases with
  | left j => simpa [reciprocalProductScales, abs_of_nonneg (le_trans (by norm_num) (hs j).1)] using (hs j).2
  | right j =>
    have hj : 0 < s j := lt_of_lt_of_le zero_lt_one (hs j).1
    have hi : (s j)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (hs j).1
    simpa only [reciprocalProductScales, Fin.addCases_right,
      abs_of_pos (inv_pos.mpr hj)] using hi.trans (by norm_num)

theorem reciprocalAnnihilatorProduct_eq (M : ℕ) (P R : Fin M → ℕ)
    (hP : ∀ j, 1 ≤ P j) (hR : ∀ j, 1 ≤ R j) (s : Fin M → ℝ) (x : ℝ) :
    reciprocalAnnihilatorProduct M P R hP hR s x =
      ∏ j, reciprocalProductFunctions M P R hP hR j (reciprocalProductScales M s j*x) := by
  simp only [reciprocalAnnihilatorProduct, reciprocalProductFunctions,
    reciprocalProductScales, Fin.prod_univ_add, Fin.addCases_left, Fin.addCases_right,
    Finset.prod_mul_distrib]

/-- Exact full Fourier translation series for G_M on a whole native source. -/
theorem reciprocalAnnihilatorProduct_fourier_hasSum (M m : ℕ) (P R : Fin M → ℕ)
    (hP : ∀ j, 1 ≤ P j) (hR : ∀ j, 1 ≤ R j) (s : Fin M → ℝ)
    (hs : ∀ j, s j ∈ Set.Icc 1 2) (T : HermiteScale (-(m:ℤ))) :
    HasSum (fun k : Fin (M+M) → ℤ =>
      (∏ j, periodicCoefficient (reciprocalProductFunctions M P R hP hR j)
        (reciprocalProductFunctions_smooth M P R hP hR j) (k j)) •
      combDistributionTranslation (∑ j, reciprocalProductScales M s j*(k j:ℝ))
        (𝓕 (hermiteScaleDistribution m T)))
      (𝓕 (TemperedDistribution.smulLeftCLM ℂ (reciprocalAnnihilatorProduct M P R hP hR s)
        (hermiteScaleDistribution m T))) := by
  have he := funext (reciprocalAnnihilatorProduct_eq M P R hP hR s)
  rw [he]
  exact finite_periodic_product_fourier_hasSum (M+M) m _
    (reciprocalProductFunctions_smooth M P R hP hR)
    (reciprocalProductFunctions_periodic M P R hP hR) _
    (reciprocalProductScales_bound M s hs) T

/-- Exact full inverse-Fourier translation series for G_M on a whole native source. -/
theorem reciprocalAnnihilatorProduct_fourierInv_hasSum (M m : ℕ) (P R : Fin M → ℕ)
    (hP : ∀ j, 1 ≤ P j) (hR : ∀ j, 1 ≤ R j) (s : Fin M → ℝ)
    (hs : ∀ j, s j ∈ Set.Icc 1 2) (T : HermiteScale (-(m:ℤ))) :
    HasSum (fun k : Fin (M+M) → ℤ =>
      (∏ j, periodicCoefficient (reciprocalProductFunctions M P R hP hR j)
        (reciprocalProductFunctions_smooth M P R hP hR j) (k j)) •
      combDistributionTranslation (-(∑ j, reciprocalProductScales M s j*(k j:ℝ)))
        (𝓕⁻ (hermiteScaleDistribution m T)))
      (𝓕⁻ (TemperedDistribution.smulLeftCLM ℂ (reciprocalAnnihilatorProduct M P R hP hR s)
        (hermiteScaleDistribution m T))) := by
  have he := funext (reciprocalAnnihilatorProduct_eq M P R hP hR s)
  rw [he]
  exact finite_periodic_product_fourierInv_hasSum (M+M) m _
    (reciprocalProductFunctions_smooth M P R hP hR)
    (reciprocalProductFunctions_periodic M P R hP hR) _
    (reciprocalProductScales_bound M s hs) T

/-- Each actual physical phase in either reciprocal direction is killed. -/
theorem reciprocalAnnihilatorProduct_zero (M : ℕ) (P R : Fin M → ℕ)
    (hP : ∀ j, 1 ≤ P j) (hR : ∀ j, 1 ≤ R j) (s : Fin M → ℝ)
    (j : Fin M) (x : ℝ)
    (hx : s j*x ∈ periodicPhaseSet (P j) (R j) ∨
      (s j)⁻¹*x ∈ periodicPhaseSet (P j) (R j)) :
    reciprocalAnnihilatorProduct M P R hP hR s x = 0 := by
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  rcases hx with hx | hx
  · apply mul_eq_zero_of_left
    change (phaseAnnihilator (P j) (R j) (hP j) (hR j) (s j*x) : ℂ) = 0
    rw [((phaseAnnihilator_spec (P j) (R j) (hP j) (hR j)).2.2.2.1 _).mpr hx]
    rfl
  · apply mul_eq_zero_of_right
    change (phaseAnnihilator (P j) (R j) (hP j) (hR j) ((s j)⁻¹*x) : ℂ) = 0
    rw [((phaseAnnihilator_spec (P j) (R j) (hP j) (hR j)).2.2.2.1 _).mpr hx]
    rfl

/-- Both actual reciprocal physical block carriers, including every rapid
tail cell, are killed by their corresponding factor. -/
theorem reciprocalAnnihilatorProduct_zero_on_blocks (M : ℕ) (P R : Fin M → ℕ)
    (hP : ∀ j, 1 ≤ P j) (hR : ∀ j, 1 ≤ R j) (s : Fin M → ℝ)
    (j : Fin M) (hs : s j ≠ 0) (x : ℝ)
    (hx : x ∈ ((fun y => (s j)⁻¹*y) '' blockSet (P j) (R j)) ∨
      x ∈ ((fun y => s j*y) '' blockSet (P j) (R j))) :
    reciprocalAnnihilatorProduct M P R hP hR s x = 0 := by
  apply reciprocalAnnihilatorProduct_zero M P R hP hR s j x
  rcases hx with ⟨y,hy,rfl⟩ | ⟨y,hy,rfl⟩
  · left
    simpa only [← mul_assoc, mul_inv_cancel₀ hs, one_mul] using
      blockSet_subset_periodicPhaseSet (P j) (R j) hy
  · right
    simpa only [← mul_assoc, inv_mul_cancel₀ hs, one_mul] using
      blockSet_subset_periodicPhaseSet (P j) (R j) hy

theorem reciprocalAnnihilatorProduct_hasTemperateGrowth (M : ℕ) (P R : Fin M → ℕ)
    (hP : ∀ j, 1 ≤ P j) (hR : ∀ j, 1 ≤ R j) (s : Fin M → ℝ) :
    (reciprocalAnnihilatorProduct M P R hP hR s).HasTemperateGrowth := by
  rw [funext (reciprocalAnnihilatorProduct_eq M P R hP hR s)]
  exact finite_periodic_product_hasTemperateGrowth (M+M) _
    (reciprocalProductFunctions_smooth M P R hP hR)
    (reciprocalProductFunctions_periodic M P R hP hR) _

/-- Actual value-only atomic sources on the covered phases are annihilated as
whole distributions, rather than merely having some displayed coefficients zero. -/
theorem reciprocalAnnihilatorProduct_kills_atomic (M : ℕ) (P R : Fin M → ℕ)
    (hP : ∀ j, 1 ≤ P j) (hR : ∀ j, 1 ≤ R j) (s : Fin M → ℝ)
    (S : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ) (hT : AtomicOnCarrier S T)
    (hcover : ∀ x ∈ S.carrier, ∃ j : Fin M,
      s j*x ∈ periodicPhaseSet (P j) (R j) ∨ (s j)⁻¹*x ∈ periodicPhaseSet (P j) (R j)) :
    TemperedDistribution.smulLeftCLM ℂ (reciprocalAnnihilatorProduct M P R hP hR s) T = 0 := by
  ext f
  rw [TemperedDistribution.smulLeftCLM_apply_apply]
  apply hT
  intro x hx
  obtain ⟨j,hj⟩ := hcover x hx
  rw [SchwartzMap.smulLeftCLM_apply_apply
    (reciprocalAnnihilatorProduct_hasTemperateGrowth M P R hP hR s),
    reciprocalAnnihilatorProduct_zero M P R hP hR s j x hj, zero_smul]

end
end MeyerGeneralProblem.Adaptive
