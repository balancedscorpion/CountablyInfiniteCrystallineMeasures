module

public import MeyerGeneralProblem.Cardinal.Adaptive.EndpointRapidMoments
public import MeyerGeneralProblem.Cardinal.Adaptive.HalfNewtonCoordinates

@[expose] public section

/-! Literal finite endpoint evaluation of the actual compact HalfNewton coordinates. -/

noncomputable section
open scoped BigOperators FourierTransform

namespace MeyerGeneralProblem.Adaptive

private theorem central_test_translate_zero (f : SchwartzMap ℝ ℂ)
    (hf : ∀ x : ℝ, 1/2 ≤ |x| → f x=0) (a : ℝ) (ha : |a| < 1/2)
    (n : ℤ) (hn : n ≠ 0) : f (a+n)=0 := by
  apply hf
  have hn1 : (1:ℝ) ≤ |(n:ℝ)| := by exact_mod_cast Int.one_le_abs hn
  have hh := abs_sub (a+(n:ℝ)) a
  rw [show a+(n:ℝ)-a=n by ring] at hh
  linarith

/-- The complete Poisson source on a translated compact central test has one
actual surviving integer cell, with its full character coefficient. -/
theorem wholePoissonSource_central_translation (a b : ℝ) (ha : |a| < 1/2)
    (f : SchwartzMap ℝ ℂ) (hf : ∀ x : ℝ, 1/2 ≤ |x| → f x=0) (m : ℤ) :
    wholePoissonSource a b (combSchwartzTranslation (-(m:ℝ)) f) = criticalCharacter m b*f a := by
  rw [wholePoissonSource_apply,tsum_eq_single m]
  · simp only [combSchwartzTranslation_apply]
    rw [show -(m:ℝ)+(a+m)=a by ring]
  · intro n hn
    simp only [combSchwartzTranslation_apply]
    have hz := central_test_translate_zero f hf a ha (n-m) (sub_ne_zero.mpr hn)
    have he : -(m:ℝ)+(a+n)=a+(n-m : ℤ) := by push_cast; ring
    rw [he,hz,mul_zero]

/-- Actual whole Zak pairing of a complete Poisson source with strict central
tests is exactly point evaluation at its two representatives. -/
theorem zakTensorAction_wholePoisson_central (a b : ℝ) (ha : |a| < 1/2) (hb : |b| < 1/2)
    (f g : SchwartzMap ℝ ℂ)
    (hf : ∀ x : ℝ, 1/2 ≤ |x| → f x=0) (hg : ∀ x : ℝ, 1/2 ≤ |x| → g x=0) :
    zakTensorAction (wholePoissonSource a b) f g=f a*g b := by
  unfold zakTensorAction
  simp_rw [wholePoissonSource_central_translation a b ha f hf,← mul_assoc]
  rw [tsum_mul_right]
  have he (n : ℤ) : criticalCharacter n b=combModulationCharacter (n:ℝ) b := by
    rw [criticalCharacter,combModulationCharacter_eq_exp]
    push_cast
    rfl
  simp_rw [he]
  change zakPeriodizedTestFunction g b*f a = _
  rw [zakPeriodizedTestFunction_eq_tsum,tsum_eq_single 0]
  · simp only [Int.cast_zero,add_zero,mul_comm]
  · intro n hn
    exact central_test_translate_zero g hg b hb n hn

/-- The literal half-coordinate convention has a linear character weight.
This identifies the exact factor and does not conflate it with a quadratic gauge. -/
theorem halfNewtonBilinear_wholePoisson_central (a b : ℝ) (ha : |a| < 1/2) (hb : |b| < 1/2)
    (f g : SchwartzMap ℝ ℂ)
    (hf : ∀ x : ℝ, 1/2 ≤ |x| → f x=0) (hg : ∀ x : ℝ, 1/2 ≤ |x| → g x=0) :
    halfNewtonBilinear (wholePoissonSource a b) f g=
      (combModulationCharacter (1/2) a*combModulationCharacter (-1/2) b)*(f a*g b) := by
  unfold halfNewtonBilinear
  rw [zakTensorAction_wholePoisson_central a b ha hb]
  · simp only [combSchwartzModulation_apply]
    ring
  · intro x hx
    rw [combSchwartzModulation_apply,hf x hx,mul_zero]
  · intro x hx
    rw [combSchwartzModulation_apply,hg x hx,mul_zero]

/-- Every actual compact Newton test has the strict central support needed
by the complete finite Poisson pairing. -/
theorem halfNewtonTest_central_zero (ε : ℕ+ → ℝ) (i : ℕ) (e : Bool) (x : ℝ)
    (hx : 1/2 ≤ |x|) : halfNewtonTest ε i e x=0 := by
  rw [halfNewtonTest_apply,zakCentralCutoff_zero x hx,zero_mul]

/-- Literal unnormalised HalfNewton coordinates of a single actual Poisson
source at small representatives. The normalization remains separate. -/
theorem halfNewtonCoordinate_wholePoisson_central (ε δ : ℕ+ → ℝ) (a b : ℝ)
    (ha : |a| ≤ 1/4) (hb : |b| ≤ 1/4) (i j : ℕ) (e d : Bool) :
    halfNewtonCoordinate ε δ (wholePoissonSource a b) i e j d =
      (combModulationCharacter (1/2) a*combModulationCharacter (-1/2) b)*
        (halfNewtonFunction ε i e a*halfNewtonFunction δ j d b) := by
  unfold halfNewtonCoordinate
  rw [halfNewtonBilinear_wholePoisson_central a b (by linarith) (by linarith)
    (halfNewtonTest ε i e) (halfNewtonTest δ j d)
    (halfNewtonTest_central_zero ε i e) (halfNewtonTest_central_zero δ j d)]
  rw [halfNewtonTest_apply,halfNewtonTest_apply,zakCentralCutoff_one a ha,zakCentralCutoff_one b hb]
  simp only [one_mul]

end MeyerGeneralProblem.Adaptive
