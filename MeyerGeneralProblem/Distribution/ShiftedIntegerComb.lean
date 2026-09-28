module

public import MeyerGeneralProblem.Distribution.IntegerComb
public import MeyerGeneralProblem.FourierNormalization

@[expose] public section

/-!
# Shifted and modulated integer combs

Translation is a genuine continuous pullback on Schwartz space.
Schwartz Poisson summation proves both Fourier identities with the
repository sign convention. Local atomicity retains the actual supports.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set SchwartzMap
open scoped SchwartzMap FourierTransform

/-- Translation pullback as a continuous complex-linear Schwartz map. -/
def combSchwartzTranslation (a : ℝ) : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
  SchwartzMap.compCLMOfAntilipschitz ℂ (g := fun x : ℝ => a+x)
    (by fun_prop) (show Isometry (fun x : ℝ => a+x) from by intro x y; simp).antilipschitz

/-- Exact evaluation of the Schwartz translation pullback. -/
theorem combSchwartzTranslation_apply (a : ℝ) (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    combSchwartzTranslation a f x=f (a+x) := rfl

/-- The actual comb on the affine lattice a+ℤ. -/
def shiftedIntegerComb (a : ℝ) : TemperedDistribution ℝ ℂ :=
  PointwiseConvergenceCLM.precomp ℂ (combSchwartzTranslation a) integerComb

/-- Exact absolutely convergent action of the shifted comb. -/
theorem shiftedIntegerComb_apply (a : ℝ) (f : SchwartzMap ℝ ℂ) :
    shiftedIntegerComb a f=∑' n : ℤ, f (a+n) := by
  change integerComb (combSchwartzTranslation a f)=_
  rw [integerComb_apply]
  rfl

/-- Unit-circle character coefficients are bounded independently of the integer. -/
theorem norm_combCharacter_le_one (a : ℝ) (n : ℤ) :
    ‖fourier n (a : UnitAddCircle)‖ ≤ 1 :=
  (ContinuousMap.norm_coe_le_norm _ _).trans (by rw [fourier_norm])

/-- The actual integer comb weighted by the positive Fourier character. -/
def modulatedIntegerComb (a : ℝ) : TemperedDistribution ℝ ℂ :=
  weightedIntegerComb (fun n => fourier n (a : UnitAddCircle)) 1
    (by norm_num) (norm_combCharacter_le_one a)

/-- Exact action of the modulated comb with its original character weights. -/
theorem modulatedIntegerComb_apply (a : ℝ) (f : SchwartzMap ℝ ℂ) :
    modulatedIntegerComb a f=∑' n : ℤ, fourier n (a : UnitAddCircle)*f (n:ℝ) := rfl

/-- Poisson summation sends positive modulation to positive lattice translation. -/
theorem fourier_modulatedIntegerComb (a : ℝ) : 𝓕 (modulatedIntegerComb a)=shiftedIntegerComb a := by
  ext f
  rw [TemperedDistribution.fourier_apply,modulatedIntegerComb_apply,shiftedIntegerComb_apply]
  simpa only [mul_comm] using (f.tsum_eq_tsum_fourier a).symm

/-- Reflection changes the modulation sign without changing the integer support. -/
theorem reflection_modulatedIntegerComb (a : ℝ) :
    temperedReflectionCLM (modulatedIntegerComb a)=modulatedIntegerComb (-a) := by
  ext f
  simp only [temperedReflectionCLM_apply,modulatedIntegerComb_apply,schwartzReflectionCLM_apply]
  rw [← (Equiv.neg ℤ).tsum_eq (fun n : ℤ => fourier n (a : UnitAddCircle)*f (-(n:ℝ)))]
  apply tsum_congr
  intro n
  simp only [Equiv.neg_apply,Int.cast_neg,neg_neg]
  congr 1
  rw [fourier_coe_apply,fourier_coe_apply]
  congr 1
  push_cast
  ring

/-- Translation of the comb transforms to the negative modulation, with
the sign forced by the actual square-Fourier reflection identity. -/
theorem fourier_shiftedIntegerComb (a : ℝ) : 𝓕 (shiftedIntegerComb a)=modulatedIntegerComb (-a) := by
  rw [← fourier_modulatedIntegerComb,fourier_sq_eq_reflection,reflection_modulatedIntegerComb]

/-- The affine integer support is locally finite. -/
def shiftedIntegerCombCarrier (a : ℝ) : LocallyFiniteCarrier where
  carrier := Set.range (fun n : ℤ => a+(n:ℝ))
  finite_inter_Icc x y := by
    apply ((Set.finite_Icc ⌈x-a⌉ ⌊y-a⌋).image (fun n : ℤ => a+(n:ℝ))).subset
    rintro z ⟨⟨n,rfl⟩,hlo,hhi⟩
    refine ⟨n,⟨Int.ceil_le.mpr ?_,Int.le_floor.mpr ?_⟩,rfl⟩ <;> linarith

/-- The shifted comb annihilates the full ideal of its actual affine support. -/
theorem shiftedIntegerComb_atomicOnCarrier (a : ℝ) :
    AtomicOnCarrier (shiftedIntegerCombCarrier a) (shiftedIntegerComb a) := by
  intro f hf
  rw [shiftedIntegerComb_apply]
  simp only [hf _ ⟨_,rfl⟩,tsum_zero]

/-- The shifted comb has the independently defined finite local atomic action. -/
theorem shiftedIntegerComb_hasLocallyAtomicAction (a : ℝ) :
    HasLocallyAtomicAction (shiftedIntegerCombCarrier a) (shiftedIntegerComb a) :=
  atomicOnCarrier_hasLocallyAtomicAction _ _ (shiftedIntegerComb_atomicOnCarrier a)

/-- Modulation retains the actual integer atomic support. -/
theorem modulatedIntegerComb_atomicOnCarrier (a : ℝ) :
    AtomicOnCarrier integerCombCarrier (modulatedIntegerComb a) :=
  weightedIntegerComb_atomicOnCarrier _ _ _ _

end

end MeyerGeneralProblem
