module

public import MeyerGeneralProblem.Distribution.CombScaling

@[expose] public section

/-!
# Actual periodic-comb residue decomposition

The integer sum is reindexed by the genuine quotient-and-remainder
equivalence, with absolute summability retained. This identifies periodic
weights on a fine lattice with the finite sum of their coarse cosets.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set SchwartzMap
open scoped SchwartzMap FourierTransform

variable {N : ℕ} [NeZero N]

/-- The actual quotient-and-residue equivalence for integer lattice nodes. -/
def combResidueEquiv (N : ℕ) [NeZero N] : ℤ ≃ ZMod N × ℤ :=
  (Int.divModEquiv N).trans
    ((Equiv.prodCongr (Equiv.refl ℤ) (ZMod.finEquiv N).toEquiv).trans
      (Equiv.prodComm ℤ (ZMod N)))

/-- Reconstruction of an integer from its genuine residue and quotient. -/
theorem combResidueEquiv_symm_apply (k : ZMod N) (n : ℤ) :
    (combResidueEquiv N).symm (k,n)=n*N+k.val := by
  cases N with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ N => rfl

/-- The reconstructed integer has precisely the original finite residue. -/
theorem combResidueEquiv_symm_cast (k : ZMod N) (n : ℤ) :
    ((combResidueEquiv N).symm (k,n) : ZMod N)=k := by
  rw [combResidueEquiv_symm_apply]
  simp

/-- Exact finite-coset decomposition of the original periodic fine-lattice
comb, proved by absolutely convergent integer reindexing. -/
theorem scaledPeriodicComb_eq_residue_sum (a : ℝ) (ha : a ≠ 0)
    (w : ZMod N → ℂ) :
    scaledPeriodicComb (a/(N:ℝ)) (div_ne_zero ha (by exact_mod_cast NeZero.ne N)) w=
      ∑ k : ZMod N, w k • combDistributionDilation a ha
        (shiftedIntegerComb (k.val/(N:ℝ))) := by
  ext f
  rw [scaledPeriodicComb_apply]
  have hN : (N:ℝ)≠0 := by exact_mod_cast NeZero.ne N
  have hsum : Summable (fun n : ℤ => w (n : ZMod N)*f (a/(N:ℝ)*n)) := by
    simpa only [combSchwartzDilation_apply] using
      summable_weightedInteger_samples (fun n => w (n : ZMod N))
        (Finset.sum_nonneg fun k _ => norm_nonneg (w k))
        (norm_periodicCombCoefficient_le w)
        (combSchwartzDilation (a/(N:ℝ)) (div_ne_zero ha hN) f)
  rw [← (combResidueEquiv N).symm.tsum_eq
    (fun n : ℤ => w (n : ZMod N)*f (a/(N:ℝ)*n))]
  have hp := ((combResidueEquiv N).symm.summable_iff.mpr hsum).tsum_prod
  simp only [Function.comp_apply] at hp
  rw [hp]
  simp only [_root_.sum_apply,smul_apply,combDistributionDilation_apply,
    shiftedIntegerComb_apply,combSchwartzDilation_apply,smul_eq_mul]
  simp only [tsum_fintype]
  apply Finset.sum_congr rfl
  intro k _
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [combResidueEquiv_symm_cast,combResidueEquiv_symm_apply]
  congr 2
  push_cast
  field_simp
  ring

end

end MeyerGeneralProblem
