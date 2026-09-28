module

public import MeyerGeneralProblem.Cardinal.Adaptive.ZakGaugeKernel
public import MeyerGeneralProblem.Cardinal.Adaptive.HalfNewtonGauge

@[expose] public section

/-! # The complete analytic gauge equals the actual whole Fourier companion -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open scoped FourierTransform

/-- The entire positive-native gauge sum is exactly the true reflected Fourier
transpose, at the same original order. -/
theorem halfNewtonGaugeTestTerm_hasSum_actual (p : ℕ) (f g : SchwartzMap ℝ ℂ)
    (r : ℝ) (hr : r < 1/2) (hf : ∀ x, r ≤ |x| → f x=0) (hg : ∀ x, r ≤ |x| → g x=0) :
    HasSum (halfNewtonGaugeTestTerm p f g)
      (schwartzToHermiteScale p (𝓕 (zakSchwartzTranspose (schwartzReflectionCLM f) g))) := by
  let v (d : ℕ) : SchwartzMap ℝ ℂ := halfNewtonGaugeCoefficient d •
    zakSchwartzTranspose (mixedSchwartz d 0 g) (mixedSchwartz d 0 f)
  have hn : Summable (fun d => ‖schwartzToHermiteScale p (v d)‖) := by
    simpa only [v,map_smul,halfNewtonGaugeTestTerm] using
      halfNewtonGaugeTestTerm_norm_summable p f g r hr hf hg
  have hu (x : ℝ) : 𝓕 (zakSchwartzTranspose (schwartzReflectionCLM f) g) x=∑' d, v d x := by
    simpa only [v,_root_.smul_apply,smul_eq_mul,halfNewtonGaugeCoefficient] using
      zakGaugeTestSeries_pointwise f g (fun y hy => hf y (by linarith))
        (fun y hy => hg y (by linarith)) x
  have h := hasSum_native_schwartz_of_pointwise p v
    (𝓕 (zakSchwartzTranspose (schwartzReflectionCLM f) g)) hn hu
  change HasSum (fun d => halfNewtonGaugeCoefficient d •schwartzToHermiteScale p
    (zakSchwartzTranspose (mixedSchwartz d 0 g) (mixedSchwartz d 0 f))) _
  simpa only [v,map_smul] using h

/-- Every whole original distribution obeys the actual Zak Fourier gauge
identity. Absolute native convergence supplies the infinite interchange. -/
theorem zakGaugeSeries_eq_fourier (T : TemperedDistribution ℝ ℂ) (f g : SchwartzMap ℝ ℂ)
    (r : ℝ) (hr : r < 1/2) (hf : ∀ x, r ≤ |x| → f x=0) (hg : ∀ x, r ≤ |x| → g x=0) :
    (∑' d : ℕ, halfNewtonGaugeCoefficient d *
      zakTensorAction T (mixedSchwartz d 0 f) (mixedSchwartz d 0 g))=
      zakTensorAction (𝓕 T) g (schwartzReflectionCLM f) := by
  obtain ⟨p,u,hu⟩ := exists_hermiteScale_representation T
  have h := (hermiteScalePairingLeftCLM p u).hasSum (halfNewtonGaugeTestTerm_hasSum_actual p f g r hr hf hg)
  simp only [halfNewtonGaugeTestTerm,map_smul,smul_eq_mul,hermiteScalePairingLeftCLM_apply,
    ← hermiteScaleDistribution_apply,hu,zakSchwartzTranspose_realizes] at h
  have he : T (𝓕 (zakSchwartzTranspose (schwartzReflectionCLM f) g))=
      zakTensorAction (𝓕 T) g (schwartzReflectionCLM f) := by
    rw [← zakSchwartzTranspose_realizes,TemperedDistribution.fourier_apply]
  rw [he] at h
  exact h.tsum_eq

private theorem monomial_modulation_commute (d : ℕ) (a : ℝ) (f : SchwartzMap ℝ ℂ) :
    mixedSchwartz d 0 (combSchwartzModulation a f)=combSchwartzModulation a (mixedSchwartz d 0 f) := by
  ext x
  simp only [mixedSchwartz_apply,iteratedDeriv_zero,combSchwartzModulation_apply]
  ring

/-- The literal complete analytic exp(-2 pi i x y) Taylor gauge of the actual
half-Weyl source is its genuine rotated Fourier companion, including every
characteristic sign. No support or array representation is supplied. -/
theorem halfNewtonGaugeBilinear_eq_FourierBilinear (T : TemperedDistribution ℝ ℂ)
    (f g : SchwartzMap ℝ ℂ) (r : ℝ) (hr : r < 1/2)
    (hf : ∀ x, r ≤ |x| → f x=0) (hg : ∀ x, r ≤ |x| → g x=0) :
    halfNewtonGaugeBilinear (halfWeylDistributionCLM T) f g=halfNewtonFourierBilinear T f g := by
  have hs (a : ℝ) (v : SchwartzMap ℝ ℂ) (hv : ∀ x, r ≤ |x| → v x=0) :
      ∀ x, r ≤ |x| → combSchwartzModulation a v x=0 := by
    intro x hx
    rw [combSchwartzModulation_apply,hv x hx,mul_zero]
  have h := zakGaugeSeries_eq_fourier (halfWeylDistributionCLM T)
    (combSchwartzModulation (1/2) f) (combSchwartzModulation (-1/2) g) r hr (hs _ _ hf) (hs _ _ hg)
  have he : schwartzReflectionCLM (combSchwartzModulation (1/2) f)=
      combSchwartzModulation (-1/2) (schwartzReflectionCLM f) := by
    ext x
    simp only [schwartzReflectionCLM_apply,combSchwartzModulation_apply]
    congr 1
    simp only [combModulationCharacter_eq_exp]
    congr 1
    push_cast
    ring
  rw [he] at h
  simpa only [halfNewtonGaugeBilinear,halfNewtonBilinear,monomial_modulation_commute,
    halfNewtonFourierBilinear_eq_fourier_Zak] using h

end
end MeyerGeneralProblem.Adaptive
