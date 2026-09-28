module

public import MeyerGeneralProblem.Cardinal.Adaptive.ZakIntegerCovariance
public import MeyerGeneralProblem.Cardinal.Adaptive.NativeFourierMultiplication

@[expose] public section

/-! # Actual periodized Schwartz tests for the whole Zak Fourier transpose -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open scoped FourierTransform ContDiff

def characterSlope (a : ℝ) : ℂ := 2*(Real.pi : ℂ)*Complex.I*(a : ℂ)

private theorem character_hasDerivAt (a x : ℝ) :
    HasDerivAt (combModulationCharacter a)
      (characterSlope a*combModulationCharacter a x) x := by
  have h := ((Complex.ofRealCLM.hasFDerivAt (x := x)).hasDerivAt.const_mul (characterSlope a)).cexp
  have he : combModulationCharacter a=(fun y : ℝ => Complex.exp (characterSlope a*(y : ℂ))) := by
    funext y
    exact combModulationCharacter_eq_exp a y
  rw [he]
  simpa only [Complex.ofRealCLM_apply,Complex.ofReal_one,mul_one,one_mul,mul_comm] using h

private theorem character_iteratedDeriv (a : ℝ) (k : ℕ) :
    iteratedDeriv k (combModulationCharacter a)=
      fun x => (characterSlope a)^k*combModulationCharacter a x := by
  induction k with
  | zero => simp only [iteratedDeriv_zero,pow_zero,one_mul]
  | succ k ih =>
    rw [iteratedDeriv_succ,ih]
    funext x
    rw [deriv_const_mul_field]
    rw [(character_hasDerivAt a x).deriv,pow_succ]
    ring

private theorem norm_characterSlope (a : ℝ) : ‖characterSlope a‖=2*Real.pi*|a| := by
  simp only [characterSlope,norm_mul,RCLike.norm_ofNat,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos Real.pi_pos,Complex.norm_I,mul_one]

/-- The genuine Schwartz periodization is defined by its complete Fourier
series, whose smoothness and physical Poisson formula are proved below. -/
def zakPeriodizedTestFunction (g : SchwartzMap ℝ ℂ) (x : ℝ) : ℂ :=
  ∑' n : ℤ, (𝓕 g) (n : ℝ)*combModulationCharacter (n : ℝ) x

private theorem periodized_derivative_majorant (g : SchwartzMap ℝ ℂ) (k : ℕ) (n : ℤ) (x : ℝ) :
    ‖iteratedFDeriv ℝ k (fun y => (𝓕 g) (n : ℝ)*combModulationCharacter (n : ℝ) y) x‖ ≤
      (2*Real.pi)^k*((1+|(n : ℝ)|)^k*‖(𝓕 g) (n : ℝ)‖) := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,iteratedDeriv_const_mul_field,
    character_iteratedDeriv,norm_mul,norm_mul,norm_pow,norm_characterSlope,
    norm_combModulationCharacter,mul_one,mul_pow]
  have h : |(n : ℝ)|^k ≤ (1+|(n : ℝ)|)^k :=
    pow_le_pow_left₀ (abs_nonneg _) (by linarith) k
  calc
    _ ≤ ‖(𝓕 g) (n : ℝ)‖*((2*Real.pi)^k*(1+|(n : ℝ)|)^k) := by gcongr
    _ = _ := by ring

/-- Every derivative series converges uniformly, so the complete periodized
Schwartz function is smooth without choosing an ordering of integer terms. -/
theorem zakPeriodizedTestFunction_contDiff (g : SchwartzMap ℝ ℂ) :
    ContDiff ℝ ∞ (zakPeriodizedTestFunction g) := by
  have hf (n : ℤ) : ContDiff ℝ ∞
      (fun x : ℝ => (𝓕 g) (n : ℝ)*combModulationCharacter (n : ℝ) x) :=
    contDiff_const.mul (contDiff_combModulationCharacter (n : ℝ) ⊤)
  change ContDiff ℝ ∞ (fun x : ℝ => ∑' n : ℤ,
    (𝓕 g) (n : ℝ)*combModulationCharacter (n : ℝ) x)
  apply contDiff_tsum hf
    (v := fun k (n : ℤ) => (2*Real.pi)^k*((1+|(n : ℝ)|)^k*‖(𝓕 g) (n : ℝ)‖))
  · intro k _
    exact (summable_weighted_schwartz_int_samples (𝓕 g) k).mul_left _
  · intro k n x _
    exact periodized_derivative_majorant g k n x

/-- The complete periodization is exactly unit-periodic. -/
theorem zakPeriodizedTestFunction_periodic (g : SchwartzMap ℝ ℂ) :
    Function.Periodic (zakPeriodizedTestFunction g) 1 := by
  intro x
  unfold zakPeriodizedTestFunction
  apply tsum_congr
  intro n
  congr 1
  change (Real.fourierChar ((n : ℝ)*(x+1)) : ℂ)=(Real.fourierChar ((n : ℝ)*x) : ℂ)
  rw [mul_add,AddChar.map_add_eq_mul,Circle.coe_mul]
  have hn : (Real.fourierChar (n : ℝ) : ℂ)=1 := by
    simpa only [combModulationCharacter,Int.cast_one,mul_one] using combModulationCharacter_int_int n 1
  simp only [mul_one,hn]

/-- Smooth periodicity gives genuine temperate growth for the whole series. -/
theorem zakPeriodizedTestFunction_temperate (g : SchwartzMap ℝ ℂ) :
    (zakPeriodizedTestFunction g).HasTemperateGrowth :=
  smooth_periodic_hasTemperateGrowth _ (zakPeriodizedTestFunction_contDiff g)
    (zakPeriodizedTestFunction_periodic g)

/-- Poisson summation identifies the actual Fourier-defined function with the
complete physical periodization of the original Schwartz test. -/
theorem zakPeriodizedTestFunction_eq_tsum (g : SchwartzMap ℝ ℂ) (x : ℝ) :
    zakPeriodizedTestFunction g x=∑' n : ℤ, g (x+(n : ℝ)) := by
  rw [g.tsum_eq_tsum_fourier x]
  unfold zakPeriodizedTestFunction
  apply tsum_congr
  intro n
  congr 1
  rw [fourier_coe_apply,combModulationCharacter_eq_exp]
  congr 1
  push_cast
  ring


/-- The reflected physical periodization required by the negative Zak Fourier
phase; reflection is retained in the actual smooth multiplier. -/
def zakReflectedPeriodization (g : SchwartzMap ℝ ℂ) (x : ℝ) : ℂ :=
  zakPeriodizedTestFunction g (-x)

/-- The reflected periodization is a genuine temperate multiplier. -/
theorem zakReflectedPeriodization_temperate (g : SchwartzMap ℝ ℂ) :
    (zakReflectedPeriodization g).HasTemperateGrowth :=
  (zakPeriodizedTestFunction_temperate g).comp Function.HasTemperateGrowth.id'.neg

/-- Exact reflected Fourier expansion, with all integer frequencies. -/
theorem zakReflectedPeriodization_expansion (g : SchwartzMap ℝ ℂ) (x : ℝ) :
    zakReflectedPeriodization g x=∑' n : ℤ,
      (𝓕 g) (n : ℝ)*combModulationCharacter (-(n : ℝ)) x := by
  unfold zakReflectedPeriodization zakPeriodizedTestFunction
  apply tsum_congr
  intro n
  congr 1
  simp only [combModulationCharacter,mul_neg,neg_mul]

/-- The Fourier-source Zak slice is the Fourier transform of multiplication by
the actual reflected periodization. The full native series theorem justifies
interchanging the whole source with the infinite integer sum. -/
theorem zakPhysicalSlice_fourier (T : TemperedDistribution ℝ ℂ) (g : SchwartzMap ℝ ℂ) :
    zakPhysicalSlice (𝓕 T) g=
      𝓕 (TemperedDistribution.smulLeftCLM ℂ (zakReflectedPeriodization g) T) := by
  obtain ⟨p,u,hu⟩ := exists_hermiteScale_representation T
  have hs := hasSum_distribution_modulation p (fun n : ℤ => (𝓕 g) (n : ℝ))
    (fun n : ℤ => -(n : ℝ))
    (by simpa only [abs_neg] using summable_weighted_schwartz_int_samples (𝓕 g) (2*p))
    (zakReflectedPeriodization g) (zakReflectedPeriodization_temperate g)
    (zakReflectedPeriodization_expansion g) u
  rw [hu] at hs
  ext f
  have he := (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ (𝓕 f)).hasSum hs
  simp only [map_smul,smul_eq_mul,PointwiseConvergenceCLM.evalCLM_apply] at he
  rw [zakPhysicalSlice_apply,TemperedDistribution.fourier_apply]
  calc
    _ = ∑' n : ℤ, (𝓕 g) (n : ℝ)*combDistributionModulation (-(n : ℝ)) T (𝓕 f) := by
      unfold zakTensorAction
      apply tsum_congr
      intro n
      congr 1
      rw [TemperedDistribution.fourier_apply,combDistributionModulation_apply]
      congr 1
      ext x
      rw [fourier_combSchwartzTranslation,combSchwartzModulation_apply]
    _ = _ := he.tsum_eq


/-- Fourier transformation in the physical test variable of the actual Zak
family equals multiplication of the actual Fourier source by the complete
periodized second test. This determines the second support condition. -/
theorem fourier_zakPhysicalSlice (T : TemperedDistribution ℝ ℂ) (g : SchwartzMap ℝ ℂ) :
    𝓕 (zakPhysicalSlice T g)=
      TemperedDistribution.smulLeftCLM ℂ (zakPeriodizedTestFunction g) (𝓕 T) := by
  obtain ⟨p,u,hu⟩ := exists_hermiteScale_representation (𝓕 T)
  have hexp (x : ℝ) : zakPeriodizedTestFunction g x=∑' n : ℤ,
      (𝓕 g) (n : ℝ)*combModulationCharacter (n : ℝ) x := rfl
  have hs := hasSum_distribution_modulation p (fun n : ℤ => (𝓕 g) (n : ℝ))
    (fun n : ℤ => (n : ℝ)) (by simpa only using summable_weighted_schwartz_int_samples (𝓕 g) (2*p))
    (zakPeriodizedTestFunction g) (zakPeriodizedTestFunction_temperate g) hexp u
  rw [hu] at hs
  ext f
  have he := (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ f).hasSum hs
  simp only [map_smul,smul_eq_mul,PointwiseConvergenceCLM.evalCLM_apply] at he
  rw [TemperedDistribution.fourier_apply,zakPhysicalSlice_apply]
  calc
    _ = ∑' n : ℤ, (𝓕 g) (n : ℝ)*combDistributionModulation (n : ℝ) (𝓕 T) f := by
      unfold zakTensorAction
      apply tsum_congr
      intro n
      congr 1
      rw [combDistributionModulation_apply,TemperedDistribution.fourier_apply]
      have hh := fourier_combSchwartzModulation_neg (-(n : ℝ)) f
      simp only [neg_neg] at hh
      rw [hh]
    _ = _ := he.tsum_eq

/-- A complete Fourier carrier annihilates every physical Zak slice whose
second test vanishes on all translated carrier points. This is an actual
whole-source consequence, without a two-variable support certificate. -/
theorem zakPhysicalSlice_zero_of_spectral_vanishing (S : LocallyFiniteCarrier)
    (T : TemperedDistribution ℝ ℂ) (hT : AtomicOnCarrier S (𝓕 T))
    (g : SchwartzMap ℝ ℂ) (hg : ∀ (n : ℤ) (x : ℝ), x ∈ S.carrier → g (x+(n : ℝ))=0) :
    zakPhysicalSlice T g=0 := by
  have hz : TemperedDistribution.smulLeftCLM ℂ (zakPeriodizedTestFunction g) (𝓕 T)=0 := by
    ext f
    rw [TemperedDistribution.smulLeftCLM_apply_apply]
    apply hT
    intro x hx
    rw [SchwartzMap.smulLeftCLM_apply_apply (zakPeriodizedTestFunction_temperate g),smul_eq_mul,
      zakPeriodizedTestFunction_eq_tsum]
    simp only [hg _ x hx,tsum_zero,zero_mul]
  have he : 𝓕 (zakPhysicalSlice T g)=0 := by rw [fourier_zakPhysicalSlice,hz]
  have hi := congrArg (fun U : TemperedDistribution ℝ ℂ => 𝓕⁻ U) he
  rw [FourierTransform.fourierInv_fourier_eq] at hi
  simpa using hi


/-- The actual Schwartz transpose of the Zak action on a separated test is
Fourier-conjugated multiplication by the proved reflected periodization. -/
def zakSchwartzTranspose (g : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
  (FourierTransform.fourierInvCLM ℂ (SchwartzMap ℝ ℂ)).comp
    ((SchwartzMap.smulLeftCLM ℂ (zakReflectedPeriodization g)).comp
      (FourierTransform.fourierCLM ℂ (SchwartzMap ℝ ℂ)))

/-- The actual Schwartz transpose represents the complete Zak tensor action
against every original tempered distribution. -/
theorem zakSchwartzTranspose_realizes (T : TemperedDistribution ℝ ℂ)
    (f g : SchwartzMap ℝ ℂ) :
    T (zakSchwartzTranspose g f)=zakTensorAction T f g := by
  have he := congrArg (fun U : TemperedDistribution ℝ ℂ => U f)
    (zakPhysicalSlice_fourier (𝓕⁻ T) g)
  rw [FourierTransform.fourier_fourierInv_eq,zakPhysicalSlice_apply,
    TemperedDistribution.fourier_apply,TemperedDistribution.smulLeftCLM_apply_apply,
    TemperedDistribution.fourierInv_apply] at he
  exact he.symm

/-- Pointwise the constructed Schwartz transpose is the complete translated
packet series. This identity is proved from whole-source realization, using
actual point masses, rather than asserted as formal Schwartz convergence. -/
theorem zakSchwartzTranspose_apply (f g : SchwartzMap ℝ ℂ) (x : ℝ) :
    zakSchwartzTranspose g f x=∑' n : ℤ, (𝓕 g) (n : ℝ)*f (x-(n : ℝ)) := by
  have he := zakSchwartzTranspose_realizes (pointMass x) f g
  simpa only [pointMass_apply,zakTensorAction,combSchwartzTranslation_apply,sub_eq_add_neg,add_comm]
    using he

end
end MeyerGeneralProblem.Adaptive
