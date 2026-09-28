module

public import MeyerGeneralProblem.Distribution.ShiftedIntegerComb
public import Mathlib.Analysis.Fourier.ZMod
import all Mathlib.Analysis.Fourier.ZMod

@[expose] public section

/-!
# Finite-periodic weighted Dirac combs and their exact Fourier transforms

The comb is defined by its actual integer coefficient sequence. Finite
Fourier inversion identifies it with a finite sum of modulated combs;
Poisson summation then gives its transform as a finite sum of shifted
combs, with the exact reciprocal-period normalization.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set SchwartzMap
open scoped SchwartzMap FourierTransform

variable {N : ℕ} [NeZero N]

/-- The finite coefficient ℓ¹ bound, used only to build the genuine functional. -/
def periodicCombCoefficientBound (w : ZMod N → ℂ) : ℝ := ∑ k, ‖w k‖

/-- Every periodic sample coefficient lies below the explicit finite bound. -/
theorem norm_periodicCombCoefficient_le (w : ZMod N → ℂ) (n : ℤ) :
    ‖w (n : ZMod N)‖ ≤ periodicCombCoefficientBound w :=
  Finset.single_le_sum (fun k _ => norm_nonneg (w k)) (Finset.mem_univ _)

/-- The actual integer Dirac comb with coefficient w at the residue class of n. -/
def periodicIntegerComb (w : ZMod N → ℂ) : TemperedDistribution ℝ ℂ :=
  weightedIntegerComb (fun n => w (n : ZMod N)) (periodicCombCoefficientBound w)
    (Finset.sum_nonneg fun k _ => norm_nonneg (w k)) (norm_periodicCombCoefficient_le w)

/-- Exact absolutely convergent action of the finite-periodic comb. -/
theorem periodicIntegerComb_apply (w : ZMod N → ℂ) (f : SchwartzMap ℝ ℂ) :
    periodicIntegerComb w f=∑' n : ℤ, w (n : ZMod N)*f (n:ℝ) := rfl

/-- Finite standard characters agree with the actual circle character at k/N. -/
theorem periodicComb_stdAddChar_eq_fourier (k : ZMod N) (n : ℤ) :
    ZMod.stdAddChar (k*(n : ZMod N))=fourier n ((k.val/(N:ℝ) : ℝ) : UnitAddCircle) := by
  have heq : k*(n : ZMod N)=((k.val:ℤ)*n : ℤ) := by simp
  rw [heq,ZMod.stdAddChar_coe,fourier_coe_apply]
  push_cast
  congr 1
  ring

/-- Proved finite Fourier inversion reconstructs every original integer weight. -/
theorem periodicCombCoefficient_eq_inverseDFT (w : ZMod N → ℂ) (n : ℤ) :
    w (n : ZMod N)=(N:ℂ)⁻¹*
      ∑ k : ZMod N, ZMod.dft w k*fourier n ((k.val/(N:ℝ) : ℝ) : UnitAddCircle) := by
  have h := congrArg (fun v : ZMod N → ℂ => v (n : ZMod N)) (ZMod.dft.symm_apply_apply w)
  rw [ZMod.invDFT_apply] at h
  simpa only [smul_eq_mul,periodicComb_stdAddChar_eq_fourier,mul_comm] using h.symm

/-- Actual finite modulated-comb sums evaluate by interchanging a finite sum
with absolutely convergent Schwartz sample sums. -/
theorem finite_modulatedIntegerComb_sum_apply {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (c : ι → ℂ) (f : SchwartzMap ℝ ℂ) :
    (∑ k, c k • modulatedIntegerComb (a k)) f =
      ∑' n : ℤ, (∑ k, c k*fourier n (a k : UnitAddCircle))*f (n:ℝ) := by
  classical
  simp only [_root_.sum_apply,smul_apply,modulatedIntegerComb_apply,smul_eq_mul,Finset.sum_mul]
  simp_rw [← tsum_mul_left,mul_assoc]
  exact (Summable.tsum_finsetSum (s := Finset.univ) (fun k _ =>
    (summable_weightedInteger_samples (fun n => fourier n (a k : UnitAddCircle))
      (by norm_num : (0:ℝ)≤1) (norm_combCharacter_le_one (a k)) f).mul_left (c k))).symm

/-- The original periodic coefficient comb equals its finite modulation
expansion, by genuine finite Fourier inversion, not by definition. -/
theorem periodicIntegerComb_eq_modulated_sum (w : ZMod N → ℂ) :
    periodicIntegerComb w=(N:ℂ)⁻¹ •
      ∑ k : ZMod N, ZMod.dft w k • modulatedIntegerComb (k.val/(N:ℝ)) := by
  ext f
  rw [periodicIntegerComb_apply,smul_apply,finite_modulatedIntegerComb_sum_apply]
  simp only [smul_eq_mul]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [periodicCombCoefficient_eq_inverseDFT w n]
  ring

/-- Exact distributional Fourier transform of arbitrary finite-periodic
integer coefficients, including the reciprocal-period DFT normalization. -/
theorem fourier_periodicIntegerComb (w : ZMod N → ℂ) :
    𝓕 (periodicIntegerComb w)=(N:ℂ)⁻¹ •
      ∑ k : ZMod N, ZMod.dft w k • shiftedIntegerComb (k.val/(N:ℝ)) := by
  rw [periodicIntegerComb_eq_modulated_sum]
  change temperedFourierLinearMap _=_
  simp only [map_smul,map_sum,temperedFourierLinearMap_apply,fourier_modulatedIntegerComb]

/-- The periodic weighted comb has actual local atomic action on ℤ. -/
theorem periodicIntegerComb_hasLocallyAtomicAction (w : ZMod N → ℂ) :
    HasLocallyAtomicAction integerCombCarrier (periodicIntegerComb w) :=
  weightedIntegerComb_hasLocallyAtomicAction _ _ _ _

end

end MeyerGeneralProblem
