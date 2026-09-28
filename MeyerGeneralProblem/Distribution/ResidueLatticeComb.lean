module

public import MeyerGeneralProblem.Distribution.CombScaling

@[expose] public section

/-!
# Exact Fourier transform of a scaled residue-class comb

The comb supported at mk+r/m is defined by actual distributional dilation
and translation. Its transform retains the reciprocal scale, the factor
1/m and the negative Fourier phase. The m=2,r=1 regression is explicit.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set SchwartzMap
open scoped SchwartzMap FourierTransform

variable (m : ℕ) [NeZero m]

/-- The actual residue-class comb on the nodes mk+r/m. -/
def residueLatticeComb (r : ℤ) : TemperedDistribution ℝ ℂ :=
  combDistributionDilation (m:ℝ) (by exact_mod_cast NeZero.ne m)
    (shiftedIntegerComb ((r:ℝ)/((m:ℝ)*(m:ℝ))))

/-- The residue comb evaluates at its actual coarse-lattice nodes. -/
theorem residueLatticeComb_apply (r : ℤ) (f : SchwartzMap ℝ ℂ) :
    residueLatticeComb m r f=∑' k : ℤ, f ((m:ℝ)*k+(r:ℝ)/(m:ℝ)) := by
  have hm : (m:ℝ)≠0 := by exact_mod_cast NeZero.ne m
  simp only [residueLatticeComb,combDistributionDilation_apply,shiftedIntegerComb_apply,
    combSchwartzDilation_apply]
  apply tsum_congr
  intro k
  congr 1
  field_simp
  ring

/-- The actual residue-class lattice is locally finite. -/
def residueLatticeCombCarrier (r : ℤ) : LocallyFiniteCarrier where
  carrier := Set.range (fun n : ℤ => (m:ℝ)*n+(r:ℝ)/(m:ℝ))
  finite_inter_Icc a b := by
    have hm : (0:ℝ)<m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
    apply ((Set.finite_Icc ⌈(a-(r:ℝ)/m)/m⌉ ⌊(b-(r:ℝ)/m)/m⌋).image
      (fun n : ℤ => (m:ℝ)*n+(r:ℝ)/(m:ℝ))).subset
    rintro x ⟨⟨n,rfl⟩,hlo,hhi⟩
    refine ⟨n,⟨Int.ceil_le.mpr ?_,Int.le_floor.mpr ?_⟩,rfl⟩
    · apply (div_le_iff₀ hm).mpr
      nlinarith
    · apply (le_div_iff₀ hm).mpr
      nlinarith

/-- The coarse residue comb annihilates the full Schwartz vanishing ideal
of its actual affine lattice. -/
theorem residueLatticeComb_atomicOnCarrier (r : ℤ) :
    AtomicOnCarrier (residueLatticeCombCarrier m r) (residueLatticeComb m r) := by
  intro f hf
  rw [residueLatticeComb_apply]
  simp only [hf _ ⟨_,rfl⟩,tsum_zero]

/-- The residue comb has the independently defined finite local atomic action. -/
theorem residueLatticeComb_hasLocallyAtomicAction (r : ℤ) :
    HasLocallyAtomicAction (residueLatticeCombCarrier m r) (residueLatticeComb m r) :=
  atomicOnCarrier_hasLocallyAtomicAction _ _ (residueLatticeComb_atomicOnCarrier m r)

/-- Exact Fourier residue identity: coefficient 1/m, reciprocal lattice
spacing 1/m and the negative character at r/m². -/
theorem fourier_residueLatticeComb_apply (r : ℤ) (f : SchwartzMap ℝ ℂ) :
    𝓕 (residueLatticeComb m r) f=(m:ℂ)⁻¹ *
      ∑' l : ℤ, fourier l ((-((r:ℝ)/((m:ℝ)*(m:ℝ))):ℝ):UnitAddCircle)*
        f ((l:ℝ)/(m:ℝ)) := by
  have hm : (0:ℝ)<m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  simp only [residueLatticeComb,fourier_combDistributionDilation,fourier_shiftedIntegerComb,
    smul_apply,combDistributionDilation_apply,modulatedIntegerComb_apply,
    combSchwartzDilation_apply,abs_of_pos hm,Complex.ofReal_inv,Complex.ofReal_natCast,
    smul_eq_mul]
  congr 2
  funext l
  simp only [div_eq_mul_inv,mul_comm]

/-- The negative quarter character is exactly the full integer power of -i. -/
theorem comb_negative_quarter_character (l : ℤ) :
    fourier l ((-(1/4:ℝ):ℝ):UnitAddCircle)=(-Complex.I)^l := by
  rw [fourier_coe_apply]
  have he : Complex.exp (-(Real.pi:ℂ)/2*Complex.I)=-Complex.I := by
    rw [neg_div,neg_mul,Complex.exp_neg,Complex.exp_pi_div_two_mul_I]
    simp
  rw [← he,← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

/-- Sign/scale regression: m=2,r=1 transforms to half the comb at l/2
with coefficient (-i)^l, for all positive and negative integer l. -/
theorem fourier_residueLatticeComb_two_one (f : SchwartzMap ℝ ℂ) :
    𝓕 (residueLatticeComb 2 1) f=(1/2:ℂ)*
      ∑' l : ℤ, (-Complex.I)^l*f ((l:ℝ)/2) := by
  rw [fourier_residueLatticeComb_apply]
  norm_num only [Nat.cast_ofNat,Int.cast_one,show (2:ℝ)*2=4 by norm_num,
    show (-(1:ℝ)/4)=-(1/4:ℝ) by ring]
  simp only [comb_negative_quarter_character]

end

end MeyerGeneralProblem
