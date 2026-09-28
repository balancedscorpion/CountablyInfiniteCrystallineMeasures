module

public import MeyerGeneralProblem.Cardinal.Adaptive.CompactFourierTaylor

@[expose] public section

/-! # Pointwise identity of the complete native Zak gauge test series -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open scoped FourierTransform

private theorem central_cell_other_large (x : ℝ) (n m : ℤ)
    (hx : |x-(n : ℝ)| ≤ 1/2) (hm : m ≠ n) : 1/2 ≤ |x-(m : ℝ)| := by
  have hnm : (n-m : ℤ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hm)
  have hnat : 1 ≤ (n-m).natAbs := Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hnm)
  have hnorm : (1 : ℝ) ≤ |(n : ℝ)-(m : ℝ)| := by
    have hi : (1 : ℤ) ≤ ((n-m).natAbs : ℤ) := Int.ofNat_le.mpr hnat
    rw [Int.natCast_natAbs] at hi
    exact_mod_cast hi
  have htri := abs_sub_le (n : ℝ) x (m : ℝ)
  rw [abs_sub_comm (n : ℝ) x] at htri
  linarith

/-- On a closed central cell even its boundary has the exact single-packet
formula: all adjacent boundary values vanish by the genuine compact support. -/
theorem zakSchwartzTranspose_on_closed_cell (f g : SchwartzMap ℝ ℂ)
    (hf : ∀ y : ℝ, 1/2 ≤ |y| → f y=0) (n : ℤ) (x : ℝ)
    (hx : |x-(n : ℝ)| ≤ 1/2) :
    zakSchwartzTranspose g f x=(𝓕 g) (n : ℝ)*f (x-(n : ℝ)) := by
  rw [zakSchwartzTranspose_apply]
  apply tsum_eq_single n
  intro m hm
  rw [hf _ (central_cell_other_large x n m hx hm),mul_zero]

/-- Reflection-periodization has the matching exact physical packet. -/
theorem zakReflectedPeriodization_reflection_on_cell (f : SchwartzMap ℝ ℂ)
    (hf : ∀ y : ℝ, 1/2 ≤ |y| → f y=0) (n : ℤ) (x : ℝ)
    (hx : |x-(n : ℝ)| ≤ 1/2) :
    zakReflectedPeriodization (schwartzReflectionCLM f) x=f (x-(n : ℝ)) := by
  rw [zakReflectedPeriodization,zakPeriodizedTestFunction_eq_tsum,tsum_eq_single n]
  · rw [schwartzReflectionCLM_apply]
    congr 1
    ring
  · intro m hm
    rw [schwartzReflectionCLM_apply]
    rw [show -(-x+(m : ℝ))=x-(m : ℝ) by ring]
    exact hf _ (central_cell_other_large x n m hx hm)

/-- The Fourier transform of the actual transpose has the complete smooth
periodized product, preserving the original Fourier normalization. -/
theorem fourier_zakSchwartzTranspose (f g : SchwartzMap ℝ ℂ) (x : ℝ) :
    𝓕 (zakSchwartzTranspose g f) x=zakReflectedPeriodization g x*(𝓕 f) x := by
  change 𝓕 (𝓕⁻ (SchwartzMap.smulLeftCLM ℂ (zakReflectedPeriodization g) (𝓕 f))) x=_
  rw [FourierTransform.fourier_fourierInv_eq,SchwartzMap.smulLeftCLM_apply_apply
    (zakReflectedPeriodization_temperate g),smul_eq_mul]

/-- The entire exponential Taylor series of genuine Zak test packets is
pointwise exactly the reflected Fourier transpose. Both infinite indices are
retained; compact cell localization justifies the exact scalar summation. -/
theorem zakGaugeTestSeries_pointwise (f g : SchwartzMap ℝ ℂ)
    (hf : ∀ y : ℝ, 1/2 ≤ |y| → f y=0)
    (hg : ∀ y : ℝ, 1/2 ≤ |y| → g y=0) (x : ℝ) :
    𝓕 (zakSchwartzTranspose (schwartzReflectionCLM f) g) x=
      ∑' r : ℕ, ((-2*(Real.pi : ℂ)*Complex.I)^r/(r.factorial : ℂ))*
        zakSchwartzTranspose (mixedSchwartz r 0 g) (mixedSchwartz r 0 f) x := by
  let n : ℤ := ⌊x+1/2⌋
  have hx : |x-(n : ℝ)| ≤ 1/2 := by
    have h1 := Int.floor_le (x+1/2)
    have h2 := Int.lt_floor_add_one (x+1/2)
    dsimp only [n]
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hf' (r : ℕ) : ∀ y : ℝ, 1/2 ≤ |y| → mixedSchwartz r 0 f y=0 := by
    intro y hy
    simp only [mixedSchwartz_apply,iteratedDeriv_zero,hf y hy,mul_zero]
  rw [fourier_zakSchwartzTranspose,zakReflectedPeriodization_reflection_on_cell f hf n x hx]
  have ht := compact_fourier_taylor g (fun y hy => hg y (by linarith)) (n : ℝ) (x-(n : ℝ))
  rw [show (n : ℝ)+(x-(n : ℝ))=x by ring] at ht
  rw [ht,← tsum_mul_left]
  apply tsum_congr
  intro r
  rw [zakSchwartzTranspose_on_closed_cell _ _ (hf' r) n x hx,mixedSchwartz_apply,iteratedDeriv_zero]
  simp only [Complex.ofReal_sub,mul_pow]
  ring

end
end MeyerGeneralProblem.Adaptive
