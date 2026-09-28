module

public import MeyerGeneralProblem.Distribution.SquareCyclicFourier
public import MeyerGeneralProblem.Distribution.SquarePeriodicCombSupport

@[expose] public section

/-!
# Actual Fourier eigencombs with escaping support holes

Finite Fourier orbit constraints and the proved Poisson lifting construct
genuine nonzero locally atomic eigendistributions. Their actual coefficient
support escapes every fixed compact interval as the positive size grows.
This finite-block construction is not yet an infinite non-strong witness.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set
open scoped SchwartzMap FourierTransform

/-- The actual nonzero coefficient support avoids the prescribed growing
open hole, by the genuine finite Fourier equation and its reflected zeros. -/
theorem squarePeriodicCombSupport_abs_lower (m : ℕ) [NeZero m]
    {c : ZMod (m*m) → ℂ} {ζ : ℂ} (hc : squareCyclicDFT m c = ζ • c)
    (hz : ∀ j : Fin (squareCyclicCentralZeroCount m), c (j.val : ZMod (m*m)) = 0)
    {x : ℝ} (hx : x ∈ (squarePeriodicCombSupport m c).carrier) :
    (m:ℝ)/4-1 ≤ |x| := by
  obtain ⟨j,rfl,hj⟩ := hx
  by_contra h
  exact hj (squareCyclicDFT_physical_hole m hc hz (lt_of_not_ge h))

/-- Actual supports, not full fine lattices, leave every fixed compact
interval once the block size exceeds an explicit linear threshold. -/
theorem squarePeriodicCombSupport_inter_Icc_eq_empty (m : ℕ) [NeZero m]
    {c : ZMod (m*m) → ℂ} {ζ : ℂ} (hc : squareCyclicDFT m c = ζ • c)
    (hz : ∀ j : Fin (squareCyclicCentralZeroCount m), c (j.val : ZMod (m*m)) = 0)
    (R : ℝ) (hm : 4*R+4 < (m:ℝ)) :
    (squarePeriodicCombSupport m c).carrier ∩ Icc (-R) R = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro x ⟨hx,hR⟩
  have hlo := squarePeriodicCombSupport_abs_lower m hc hz hx
  have hhi : |x| ≤ R := abs_le.mpr hR
  linarith

/-- For every positive size there is an actual unit-normalized Fourier
eigencomb, with bounded original coefficients and a genuine unit atom in
the first physical period, on its exact nonzero locally finite support.
No Poisson, support, Fourier, or nonzeroness certificate is assumed. -/
theorem exists_squarePeriodicComb_centralHole (m : ℕ) [NeZero m] :
    ∃ (a : Fin 4) (c : ZMod (m*m) → ℂ) (r : ZMod (m*m)),
      c r = 1 ∧ (∀ j, ‖c j‖ ≤ 1) ∧
      squarePeriodicComb m c ≠ 0 ∧
      𝓕 (squarePeriodicComb m c) = fourthRootValue a • squarePeriodicComb m c ∧
      squarePeriodicComb m c ∈ DistributionalMeyerSpace (squarePeriodicCombSupport m c) ∧
      ((r.val:ℝ)/(m:ℝ) ∈ (squarePeriodicCombSupport m c).carrier ∩ Ico 0 (m:ℝ)) ∧
      (∀ x ∈ (squarePeriodicCombSupport m c).carrier, (m:ℝ)/4-1 ≤ |x|) := by
  obtain ⟨a,c,r,hr,hbound,he,hz⟩ := exists_squareCyclicDFT_centralHole_vector m
  have hc : c ≠ 0 := by
    intro h
    have := congrFun h r
    rw [hr] at this
    norm_num at this
  have he' : (m:ℂ)⁻¹ • ZMod.dft c = fourthRootValue a • c := he
  refine ⟨a,c,r,hr,hbound,squarePeriodicComb_ne_zero m hc,
    fourier_squarePeriodicComb_of_dft_eigen m c _ he',
    squarePeriodicComb_mem_distributionalMeyerSpace m c _ he',?_,?_⟩
  · refine ⟨?_,squareCyclic_residue_mem_first_period m r⟩
    refine ⟨(r.val:ℤ),by simp,?_⟩
    simp [hr]
  · intro x hx
    exact squarePeriodicCombSupport_abs_lower m he hz hx

end

end MeyerGeneralProblem
