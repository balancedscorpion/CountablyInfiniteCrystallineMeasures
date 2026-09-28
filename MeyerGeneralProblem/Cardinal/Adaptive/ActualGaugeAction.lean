module

public import MeyerGeneralProblem.Cardinal.Adaptive.ActualCoordinateAction
public import MeyerGeneralProblem.Cardinal.Adaptive.HalfNewtonGauge

@[expose] public section

/-! # The complete bounded gauge acts on actual whole source moments -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section

/-- All monomial powers preserve a literal compact chart support. -/
theorem mixedSchwartz_monomial_support (φ : SchwartzMap ℝ ℂ) (b : ℝ)
    (hφ : ∀ x, b ≤ |x| → φ x=0) (d : ℕ) :
    ∀ x, b ≤ |x| → mixedSchwartz d 0 φ x=0 := by
  intro x hx
  rw [mixedSchwartz_apply,iteratedDeriv_zero,hφ x hx,mul_zero]

/-- Repeated coordinate multiplication is the exact higher monomial test. -/
theorem mixedSchwartz_monomial_succ (φ : SchwartzMap ℝ ℂ) (d : ℕ) :
    mixedSchwartz 1 0 (mixedSchwartz d 0 φ)=mixedSchwartz (d+1) 0 φ := by
  ext x
  simp only [mixedSchwartz_apply,iteratedDeriv_zero,pow_one,pow_succ]
  ring

/-- Every monomial can be moved to the compact chart factor. -/
theorem schwartzChartProduct_monomial (φ f : SchwartzMap ℝ ℂ) (d : ℕ) :
    schwartzChartProduct (mixedSchwartz d 0 φ) f=mixedSchwartz d 0 (schwartzChartProduct φ f) := by
  ext x
  simp only [mixedSchwartz_apply,iteratedDeriv_zero,schwartzChartProduct_apply]
  ring

/-- Exact normalized moments of a whole distribution against two chart factors. -/
def chartNewtonReading (N : ℕ → Bool → ℕ → Bool → ℂ) (ε δ : ℕ+ → ℝ) (T : TemperedDistribution ℝ ℂ)
    (φ ψ : SchwartzMap ℝ ℂ) (i : ℕ) (e : Bool) (j : ℕ) (f : Bool) : ℂ :=
  N i e j f * halfNewtonBilinear T
    (schwartzChartProduct φ (halfNewtonTest ε i e))
    (schwartzChartProduct ψ (halfNewtonTest δ j f))

/-- Actual coordinate actions suffice to identify every term of the whole
operator exponential with its original distributional Taylor term. -/
theorem actualGaugeAction_of_coordinates (N : ℕ → Bool → ℕ → Bool → ℂ) (ε δ : ℕ+ → ℝ) (T : TemperedDistribution ℝ ℂ)
    (X Y : SeamMomentArray →L[ℂ] SeamMomentArray) (b : ℝ) (hb : b < 1/2)
    (hX : ∀ (φ ψ : SchwartzMap ℝ ℂ), (∀ x, b ≤ |x| → φ x=0) →
      ∀ (u : SeamMomentArray), (∀ i e j f, u ((i,e),(j,f))=chartNewtonReading N ε δ T φ ψ i e j f) →
      ∀ i e j f, X u ((i,e),(j,f))=chartNewtonReading N ε δ T (mixedSchwartz 1 0 φ) ψ i e j f)
    (hY : ∀ (φ ψ : SchwartzMap ℝ ℂ), (∀ x, b ≤ |x| → ψ x=0) →
      ∀ (u : SeamMomentArray), (∀ i e j f, u ((i,e),(j,f))=chartNewtonReading N ε δ T φ ψ i e j f) →
      ∀ i e j f, Y u ((i,e),(j,f))=chartNewtonReading N ε δ T φ (mixedSchwartz 1 0 ψ) i e j f)
    (φ ψ : SchwartzMap ℝ ℂ) (hφ : ∀ x, b ≤ |x| → φ x=0) (hψ : ∀ x, b ≤ |x| → ψ x=0)
    (u : SeamMomentArray) (hu : ∀ i e j f, u ((i,e),(j,f))=chartNewtonReading N ε δ T φ ψ i e j f)
    (i j : ℕ) (e f : Bool) :
    NormedSpace.exp ((-2*Real.pi*Complex.I) •(X*Y)) u ((i,e),(j,f))=
      N i e j f*halfNewtonGaugeBilinear T
        (schwartzChartProduct φ (halfNewtonTest ε i e))
        (schwartzChartProduct ψ (halfNewtonTest δ j f)) := by
  have hp : ∀ d i e j f, (((X*Y)^d) u) ((i,e),(j,f))=
      chartNewtonReading N ε δ T (mixedSchwartz d 0 φ) (mixedSchwartz d 0 ψ) i e j f := by
    intro d
    induction d with
    | zero =>
      have hz (g : SchwartzMap ℝ ℂ) : mixedSchwartz 0 0 g=g := by
        ext x; simp only [mixedSchwartz_apply,iteratedDeriv_zero,pow_zero,one_mul]
      simpa only [pow_zero,ContinuousLinearMap.one_apply,ContinuousLinearMap.id_apply,hz] using hu
    | succ d ih =>
      have hy := hY (mixedSchwartz d 0 φ) (mixedSchwartz d 0 ψ)
        (mixedSchwartz_monomial_support ψ b hψ d) (((X*Y)^d) u) ih
      have hx := hX (mixedSchwartz d 0 φ) (mixedSchwartz 1 0 (mixedSchwartz d 0 ψ))
        (mixedSchwartz_monomial_support φ b hφ d) (Y (((X*Y)^d) u)) hy
      simpa only [pow_succ',ContinuousLinearMap.mul_apply,mixedSchwartz_monomial_succ] using hx
  have hs := (lp.evalCLM ℂ (fun _ : SeamMomentIndex => ℂ) 2 ((i,e),(j,f))).hasSum
    ((ContinuousLinearMap.apply ℂ SeamMomentArray u).hasSum
      (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) ((-2*Real.pi*Complex.I) •(X*Y))))
  have ht : HasSum (fun d : ℕ => N i e j f *
      (halfNewtonGaugeCoefficient d*halfNewtonBilinear T
        (mixedSchwartz d 0 (schwartzChartProduct φ (halfNewtonTest ε i e)))
        (mixedSchwartz d 0 (schwartzChartProduct ψ (halfNewtonTest δ j f)))))
      (N i e j f*halfNewtonGaugeBilinear T
        (schwartzChartProduct φ (halfNewtonTest ε i e))
        (schwartzChartProduct ψ (halfNewtonTest δ j f))) := by
    obtain ⟨p,v,hv⟩ := exists_hermiteScale_representation T
    rw [←hv]
    exact (halfNewtonGaugeBilinear_hasSum p v _ _ b hb
      (by intro x hx; rw [schwartzChartProduct_apply,hφ x hx,zero_mul])
      (by intro x hx; rw [schwartzChartProduct_apply,hψ x hx,zero_mul])).mul_left _
  have he (d : ℕ) : ((d.factorial:ℂ)⁻¹ • (((-2*Real.pi*Complex.I) •(X*Y))^d)) u ((i,e),(j,f))=
      N i e j f*(halfNewtonGaugeCoefficient d*halfNewtonBilinear T
        (mixedSchwartz d 0 (schwartzChartProduct φ (halfNewtonTest ε i e)))
        (mixedSchwartz d 0 (schwartzChartProduct ψ (halfNewtonTest δ j f)))) := by
    rw [smul_pow,smul_smul]
    change ((d.factorial:ℂ)⁻¹ *(-2*Real.pi*Complex.I)^d)*(((X*Y)^d) u ((i,e),(j,f)))=_
    rw [hp]
    simp only [chartNewtonReading,schwartzChartProduct_monomial,halfNewtonGaugeCoefficient,div_eq_mul_inv]
    ring
  change HasSum (fun d : ℕ => ((d.factorial:ℂ)⁻¹ • (((-2*Real.pi*Complex.I) •(X*Y))^d)) u ((i,e),(j,f))) _ at hs
  simp only [he] at hs
  exact hs.unique ht

/-- The actual full constant-normalization gauge is exactly the original
whole distributional gauge on compact chart moments. No operator-action
assumption remains: both coordinates are the literal sine/arcsine operators. -/
theorem seamGauge_chart_action (ε δ : ℕ+ → ℝ)
    (K L : ℝ) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (ha : ∀ i, ‖criticalNewtonNode (ε ⟨i+1,by omega⟩)‖ ≤ K)
    (hb : ∀ i, ‖criticalNewtonNode (δ ⟨i+1,by omega⟩)‖ ≤ L)
    (T : TemperedDistribution ℝ ℂ) (φ ψ : SchwartzMap ℝ ℂ)
    (b : ℝ) (hpos : 0 < b) (hsmall : b < 1/8)
    (hφ : ∀ x, b ≤ |x| → φ x=0) (hψ : ∀ x, b ≤ |x| → ψ x=0)
    (u : SeamMomentArray)
    (hu : ∀ i e j f, u ((i,e),(j,f))=chartNewtonReading halfNewtonNormalization ε δ T φ ψ i e j f)
    (hS : ‖(seamSineRow (1/64) (1/4096) (fun n => criticalNewtonNode (ε ⟨n+1,by omega⟩)) K hK ha)*
      (seamSineRow (1/64) (1/4096) (fun n => criticalNewtonNode (ε ⟨n+1,by omega⟩)) K hK ha)‖ < 1)
    (hT : ‖(seamSineRow (1/64) (1/4096) (fun n => criticalNewtonNode (δ ⟨n+1,by omega⟩)) L hL hb)*
      (seamSineRow (1/64) (1/4096) (fun n => criticalNewtonNode (δ ⟨n+1,by omega⟩)) L hL hb)‖ < 1)
    (i j : ℕ) (e f : Bool) :
    NormedSpace.exp (seamGaugeGenerator
      (seamSineRow (1/64) (1/4096) (fun n => criticalNewtonNode (ε ⟨n+1,by omega⟩)) K hK ha)
      (seamSineColumn (1/64) (1/4096) (fun n => criticalNewtonNode (δ ⟨n+1,by omega⟩)) L hL hb)) u ((i,e),(j,f))=
      halfNewtonNormalization i e j f*halfNewtonGaugeBilinear T
        (schwartzChartProduct φ (halfNewtonTest ε i e))
        (schwartzChartProduct ψ (halfNewtonTest δ j f)) := by
  apply actualGaugeAction_of_coordinates halfNewtonNormalization ε δ T _ _ b (by linarith)
    _ _ φ ψ hφ hψ u hu i j e f
  · intro φ ψ hφ u hu i e j f
    exact seamCoordinateRow_chart_bilinear_action ε δ K hK ha T φ ψ b hpos hsmall hφ u hu hS i j e f
  · intro φ ψ hψ u hu i e j f
    exact seamCoordinateColumn_chart_bilinear_action ε δ L hL hb T φ ψ b hpos hsmall hψ u hu hT i j e f

end
end MeyerGeneralProblem.Adaptive
