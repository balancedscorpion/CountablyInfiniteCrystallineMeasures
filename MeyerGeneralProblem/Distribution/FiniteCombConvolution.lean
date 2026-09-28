module

public import MeyerGeneralProblem.Distribution.SquarePeriodicCombSupport
public import MeyerGeneralProblem.Distribution.ResidueLatticeComb

@[expose] public section

/-!
# Actual finite atomic convolution and Fourier multiplication

Translation and modulation are genuine continuous linear operators on
tempered distributions. The Schwartz modulation is constructed from
continuous Fourier maps and proved to multiply by the actual smooth
character. The finite convolution formula uses no infinite interchange.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set SchwartzMap MeasureTheory
open scoped SchwartzMap FourierTransform

/-- The actual positive Fourier character at a physical real point. -/
def combModulationCharacter (a x : ℝ) : ℂ := (Real.fourierChar (a*x) : ℂ)

/-- Exact exponential and sign convention for the physical character. -/
theorem combModulationCharacter_eq_exp (a x : ℝ) :
    combModulationCharacter a x=Complex.exp (2*Real.pi*Complex.I*(a:ℂ)*(x:ℂ)) := by
  rw [combModulationCharacter,Real.fourierChar_apply]
  congr 1
  push_cast
  ring

/-- Physical modulation characters are genuinely smooth of every finite order. -/
theorem contDiff_combModulationCharacter (a : ℝ) (n : ℕ∞) :
    ContDiff ℝ n (combModulationCharacter a) := by
  change ContDiff ℝ n (fun x => combModulationCharacter a x)
  simp only [combModulationCharacter_eq_exp]
  exact Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff)

/-- The modulus of the character is exactly one on the full real line. -/
theorem norm_combModulationCharacter (a x : ℝ) : ‖combModulationCharacter a x‖=1 :=
  Circle.norm_coe _

/-- The actual Fourier integral converts Schwartz translation to positive
character multiplication, with the sign fixed by change of variables. -/
theorem fourier_combSchwartzTranslation (a : ℝ) (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    𝓕 (combSchwartzTranslation a f) x=combModulationCharacter a x*𝓕 f x := by
  have h := congrFun (Fourier.fourierIntegral_comp_add_right Real.fourierChar
    (volume : Measure ℝ) (f : ℝ → ℂ) a) x
  change (∫ v : ℝ, (Real.fourierChar (-(v*x)):ℂ) • f (v+a))=
    (Real.fourierChar (a*x):ℂ) • ∫ v : ℝ, (Real.fourierChar (-(v*x)):ℂ) • f v at h
  simpa only [SchwartzMap.fourier_coe,Real.fourier_real_eq,
    combSchwartzTranslation_apply,combModulationCharacter,Circle.smul_def,
    smul_eq_mul,add_comm] using h

/-- Continuous Schwartz modulation, with its actual pointwise multiplication
law proved below, rather than assumed as a multiplier hypothesis. -/
def combSchwartzModulation (a : ℝ) : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
  FourierTransform.fourierCLM ℂ (SchwartzMap ℝ ℂ) ∘L combSchwartzTranslation a ∘L
    FourierTransform.fourierInvCLM ℂ (SchwartzMap ℝ ℂ)

/-- The continuous modulation map multiplies by the actual smooth exponential. -/
theorem combSchwartzModulation_apply (a : ℝ) (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    combSchwartzModulation a f x=combModulationCharacter a x*f x := by
  change 𝓕 (combSchwartzTranslation a (𝓕⁻ f)) x=_
  rw [fourier_combSchwartzTranslation,FourierTransform.fourier_fourierInv_eq]

/-- Fourier of negative Schwartz modulation is actual positive translation. -/
theorem fourier_combSchwartzModulation_neg (a : ℝ) (f : SchwartzMap ℝ ℂ) :
    𝓕 (combSchwartzModulation (-a) f)=combSchwartzTranslation a (𝓕 f) := by
  ext x
  simp only [SchwartzMap.fourier_coe,Real.fourier_real_eq_integral_exp_smul,
    combSchwartzModulation_apply,combSchwartzTranslation_apply,
    combModulationCharacter_eq_exp,smul_eq_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [← mul_assoc,← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- Actual pushforward translation of tempered distributions. -/
def combDistributionTranslation (a : ℝ) :
    TemperedDistribution ℝ ℂ →L[ℂ] TemperedDistribution ℝ ℂ :=
  PointwiseConvergenceCLM.precomp ℂ (combSchwartzTranslation a)

/-- Translation acts on test functions by the actual shifted pullback. -/
theorem combDistributionTranslation_apply (a : ℝ) (T : TemperedDistribution ℝ ℂ)
    (f : SchwartzMap ℝ ℂ) :
    combDistributionTranslation a T f=T (combSchwartzTranslation a f) := rfl

/-- Genuine multiplication of a tempered distribution by the smooth character. -/
def combDistributionModulation (a : ℝ) :
    TemperedDistribution ℝ ℂ →L[ℂ] TemperedDistribution ℝ ℂ :=
  PointwiseConvergenceCLM.precomp ℂ (combSchwartzModulation a)

/-- Distributional character multiplication is the actual Schwartz product action. -/
theorem combDistributionModulation_apply (a : ℝ) (T : TemperedDistribution ℝ ℂ)
    (f : SchwartzMap ℝ ℂ) :
    combDistributionModulation a T f=T (combSchwartzModulation a f) := rfl

/-- Fourier of actual distribution translation is negative character
multiplication of the Fourier transform, for every tempered distribution. -/
theorem fourier_combDistributionTranslation (a : ℝ) (T : TemperedDistribution ℝ ℂ) :
    𝓕 (combDistributionTranslation a T)=combDistributionModulation (-a) (𝓕 T) := by
  ext f
  simp only [TemperedDistribution.fourier_apply,combDistributionTranslation_apply,
    combDistributionModulation_apply,fourier_combSchwartzModulation_neg]

/-- Actual finite atomic convolution, as a finite sum of translation CLMs. -/
def finiteCombConvolution {ι : Type*} [Fintype ι] (a : ι → ℝ) (c : ι → ℂ) :
    TemperedDistribution ℝ ℂ →L[ℂ] TemperedDistribution ℝ ℂ :=
  ∑ i, c i • combDistributionTranslation (a i)

/-- Exact finite translation formula for the convolution operator. -/
theorem finiteCombConvolution_apply {ι : Type*} [Fintype ι] (a : ι → ℝ) (c : ι → ℂ)
    (T : TemperedDistribution ℝ ℂ) :
    finiteCombConvolution a c T=∑ i, c i • combDistributionTranslation (a i) T := by
  simp only [finiteCombConvolution,_root_.sum_apply,_root_.smul_apply]

/-- Exact test-function action of finite convolution; no infinite sum is exchanged. -/
theorem finiteCombConvolution_apply_test {ι : Type*} [Fintype ι] (a : ι → ℝ) (c : ι → ℂ)
    (T : TemperedDistribution ℝ ℂ) (f : SchwartzMap ℝ ℂ) :
    finiteCombConvolution a c T f=∑ i, c i*T (combSchwartzTranslation (a i) f) := by
  simp only [finiteCombConvolution_apply,_root_.sum_apply,smul_apply,
    combDistributionTranslation_apply,smul_eq_mul]

/-- Actual Fourier multiplication identity for finite atomic convolution. -/
theorem fourier_finiteCombConvolution {ι : Type*} [Fintype ι] (a : ι → ℝ) (c : ι → ℂ)
    (T : TemperedDistribution ℝ ℂ) :
    𝓕 (finiteCombConvolution a c T)=
      ∑ i, c i • combDistributionModulation (-a i) (𝓕 T) := by
  rw [finiteCombConvolution_apply]
  change temperedFourierLinearMap _=_
  simp only [map_sum,map_smul,temperedFourierLinearMap_apply,
    fourier_combDistributionTranslation]

/-- The actual finite negative-phase Fourier symbol of the atomic motif. -/
def finiteCombFourierSymbol {ι : Type*} [Fintype ι] (a : ι → ℝ) (c : ι → ℂ) (x : ℝ) : ℂ :=
  ∑ i, c i*combModulationCharacter (-a i) x

/-- The finite Fourier symbol is bounded by the motif's actual coefficient sum. -/
theorem norm_finiteCombFourierSymbol_le {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (c : ι → ℂ) (x : ℝ) :
    ‖finiteCombFourierSymbol a c x‖≤∑ i, ‖c i‖ := by
  unfold finiteCombFourierSymbol
  exact (norm_sum_le _ _).trans (by simp only [norm_mul,norm_combModulationCharacter,mul_one]; rfl)

/-- Continuous Schwartz multiplication by the actual finite Fourier symbol. -/
def finiteCombSchwartzSymbol {ι : Type*} [Fintype ι] (a : ι → ℝ) (c : ι → ℂ) :
    SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
  ∑ i, c i • combSchwartzModulation (-a i)

/-- The continuous finite-symbol map has the genuine pointwise multiplication law. -/
theorem finiteCombSchwartzSymbol_apply {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (c : ι → ℂ) (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    finiteCombSchwartzSymbol a c f x=finiteCombFourierSymbol a c x*f x := by
  simp only [finiteCombSchwartzSymbol,_root_.sum_apply,_root_.smul_apply,
    combSchwartzModulation_apply,smul_eq_mul,finiteCombFourierSymbol,Finset.sum_mul,mul_assoc]

/-- The Fourier transform of finite atomic convolution is multiplication
by one actual finite smooth symbol, stated on genuine Schwartz tests. -/
theorem fourier_finiteCombConvolution_apply_test {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (c : ι → ℂ) (T : TemperedDistribution ℝ ℂ) (f : SchwartzMap ℝ ℂ) :
    𝓕 (finiteCombConvolution a c T) f=𝓕 T (finiteCombSchwartzSymbol a c f) := by
  rw [fourier_finiteCombConvolution]
  simp only [_root_.sum_apply,_root_.smul_apply,combDistributionModulation_apply,
    finiteCombSchwartzSymbol,map_sum,map_smul]

/-- Finite convolution evaluates at the actual shifted fine-lattice nodes
of the original square-periodic comb. -/
theorem finiteCombConvolution_squarePeriodicComb_apply
    {ι : Type*} [Fintype ι] (a : ι → ℝ) (c : ι → ℂ)
    (m : ℕ) [NeZero m] (w : ZMod (m*m) → ℂ) (f : SchwartzMap ℝ ℂ) :
    finiteCombConvolution a c (squarePeriodicComb m w) f=
      ∑ i, c i*(∑' n : ℤ, w (n : ZMod (m*m))*f (a i+(n:ℝ)/(m:ℝ))) := by
  simp only [finiteCombConvolution_apply_test,squarePeriodicComb_apply,
    combSchwartzTranslation_apply]

/-- The actual Fourier-side coefficient formula on the unchanged fine
lattice, including both the normalized DFT and the complete motif symbol. -/
theorem fourier_finiteCombConvolution_squarePeriodicComb_apply
    {ι : Type*} [Fintype ι] (a : ι → ℝ) (c : ι → ℂ)
    (m : ℕ) [NeZero m] (w : ZMod (m*m) → ℂ) (f : SchwartzMap ℝ ℂ) :
    𝓕 (finiteCombConvolution a c (squarePeriodicComb m w)) f=
      ∑' n : ℤ, ((m:ℂ)⁻¹*ZMod.dft w (n : ZMod (m*m)))*
        finiteCombFourierSymbol a c ((n:ℝ)/(m:ℝ))*f ((n:ℝ)/(m:ℝ)) := by
  rw [fourier_finiteCombConvolution_apply_test,fourier_squarePeriodicComb,
    squarePeriodicComb_apply]
  simp only [Pi.smul_apply,smul_eq_mul,finiteCombSchwartzSymbol_apply,mul_assoc]

/-- Signed-translation regression on the exact m=2,r=1 residue comb:
the reciprocal-lattice coefficient retains both (-i)^l and the negative
translation character, for every real shift and every integer l. -/
theorem fourier_translated_residueLatticeComb_two_one (a : ℝ) (f : SchwartzMap ℝ ℂ) :
    𝓕 (combDistributionTranslation a (residueLatticeComb 2 1)) f=
      (1/2:ℂ)*∑' l : ℤ, (-Complex.I)^l*
        combModulationCharacter (-a) ((l:ℝ)/2)*f ((l:ℝ)/2) := by
  rw [fourier_combDistributionTranslation,combDistributionModulation_apply,
    fourier_residueLatticeComb_two_one]
  simp only [combSchwartzModulation_apply,mul_assoc]

end

end MeyerGeneralProblem
