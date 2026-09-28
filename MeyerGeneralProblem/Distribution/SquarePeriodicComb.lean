module

public import MeyerGeneralProblem.Distribution.PeriodicCombResidues

@[expose] public section

/-!
# Square-periodic combs and the normalized finite DFT

For a positive integer m, the original coefficient sequence has period
m² and physical spacing 1/m. Its actual distributional Fourier transform
is the same physical comb with coefficient vector (1/m) DFT(c).
-/

namespace MeyerGeneralProblem

noncomputable section

open Set SchwartzMap
open scoped SchwartzMap FourierTransform

variable (m : ℕ) [NeZero m]

/-- The actual m²-periodic coefficient comb at physical spacing 1/m. -/
def squarePeriodicComb (w : ZMod (m*m) → ℂ) : TemperedDistribution ℝ ℂ :=
  scaledPeriodicComb (m:ℝ)⁻¹ (inv_ne_zero (by exact_mod_cast NeZero.ne m)) w

/-- The square-periodic comb acts by its original physical coefficient sum. -/
theorem squarePeriodicComb_apply (w : ZMod (m*m) → ℂ) (f : SchwartzMap ℝ ℂ) :
    squarePeriodicComb m w f=∑' n : ℤ, w (n : ZMod (m*m))*f ((n:ℝ)/(m:ℝ)) := by
  simp only [squarePeriodicComb,scaledPeriodicComb_apply,div_eq_mul_inv,mul_comm]

/-- Scalar multiplication of the original finite coefficient vector is
actual scalar multiplication of the associated tempered distribution. -/
theorem squarePeriodicComb_smul (c : ℂ) (w : ZMod (m*m) → ℂ) :
    squarePeriodicComb m (c • w)=c • squarePeriodicComb m w := by
  ext f
  simp only [squarePeriodicComb_apply,smul_apply,Pi.smul_apply,smul_eq_mul,mul_assoc]
  exact tsum_mul_left

/-- Addition of original coefficient vectors is actual distribution addition. -/
theorem squarePeriodicComb_add (v w : ZMod (m*m) → ℂ) :
    squarePeriodicComb m (v+w)=squarePeriodicComb m v+squarePeriodicComb m w := by
  ext f
  simp only [squarePeriodicComb,scaledPeriodicComb,combDistributionDilation_apply,
    periodicIntegerComb_apply,Pi.add_apply,add_mul,_root_.add_apply]
  apply Summable.tsum_add
  · exact summable_weightedInteger_samples _
      (Finset.sum_nonneg fun k _ => norm_nonneg (v k))
      (norm_periodicCombCoefficient_le v) _
  · exact summable_weightedInteger_samples _
      (Finset.sum_nonneg fun k _ => norm_nonneg (w k))
      (norm_periodicCombCoefficient_le w) _

/-- The exact Fourier identity for the original square-periodic comb,
with the physical scale unchanged and the factor 1/m proved. -/
theorem fourier_squarePeriodicComb (w : ZMod (m*m) → ℂ) :
    𝓕 (squarePeriodicComb m w)=squarePeriodicComb m ((m:ℂ)⁻¹ • ZMod.dft w) := by
  have hmR : (m:ℝ)≠0 := by exact_mod_cast NeZero.ne m
  have hmC : (m:ℂ)≠0 := by exact_mod_cast NeZero.ne m
  have hscale : (m:ℝ)/((m*m:ℕ):ℝ)=(m:ℝ)⁻¹ := by
    push_cast
    field_simp
  have hcoset := scaledPeriodicComb_eq_residue_sum (N := m*m) (m:ℝ) hmR (ZMod.dft w)
  simp only [hscale] at hcoset
  rw [squarePeriodicComb_smul,squarePeriodicComb,fourier_scaledPeriodicComb]
  simp only [inv_inv]
  rw [← hcoset]
  congr 1
  rw [abs_inv,inv_inv,abs_of_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m))]
  push_cast
  field_simp

/-- A genuine normalized finite-DFT eigenvector lifts to a Fourier
eigendistribution without any Poisson or Fourier identity hypothesis. -/
theorem fourier_squarePeriodicComb_of_dft_eigen (w : ZMod (m*m) → ℂ) (z : ℂ)
    (hw : (m:ℂ)⁻¹ • ZMod.dft w=z • w) :
    𝓕 (squarePeriodicComb m w)=z • squarePeriodicComb m w := by
  rw [fourier_squarePeriodicComb,hw,squarePeriodicComb_smul]

end

end MeyerGeneralProblem
