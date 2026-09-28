module

public import MeyerGeneralProblem.Distribution.FiniteCombConvolution

@[expose] public section

/-!
# Local atomicity under finite convolution and character multiplication

Translations and finite unions preserve local finiteness. The finite
union is only a support container: no equality with nonzero support is
claimed when different translated atoms can cancel. Modulation changes
each genuine local coefficient by the actual character value.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set SchwartzMap
open scoped SchwartzMap FourierTransform

/-- The actual translated locally finite carrier. -/
def LocallyFiniteCarrier.translate (S : LocallyFiniteCarrier) (a : ℝ) : LocallyFiniteCarrier where
  carrier := (fun x : ℝ => a+x) '' S.carrier
  finite_inter_Icc x y := by
    apply ((S.finite_inter_Icc (x-a) (y-a)).image (fun z : ℝ => a+z)).subset
    rintro z ⟨⟨w,hw,rfl⟩,hlo,hhi⟩
    refine ⟨w,⟨hw,?_,?_⟩,rfl⟩ <;> linarith

/-- Membership in a translated carrier retains the original physical point. -/
theorem LocallyFiniteCarrier.mem_translate (S : LocallyFiniteCarrier) (a x : ℝ) :
    x ∈ (S.translate a).carrier ↔ ∃ y ∈ S.carrier, a+y=x := Iff.rfl

/-- The actual finite union of translated supports is locally finite. -/
def finiteCombConvolutionCarrier {ι : Type*} [Fintype ι]
    (S : LocallyFiniteCarrier) (a : ι → ℝ) : LocallyFiniteCarrier where
  carrier := ⋃ i, (S.translate (a i)).carrier
  finite_inter_Icc x y := by
    rw [Set.iUnion_inter]
    exact Set.finite_iUnion fun i => (S.translate (a i)).finite_inter_Icc x y

/-- Every translated atom lies in the genuine finite union container. -/
theorem mem_finiteCombConvolutionCarrier {ι : Type*} [Fintype ι]
    (S : LocallyFiniteCarrier) (a : ι → ℝ) (i : ι) {x : ℝ} (hx : x ∈ S.carrier) :
    a i+x ∈ (finiteCombConvolutionCarrier S a).carrier :=
  Set.mem_iUnion.mpr ⟨i,⟨x,hx,rfl⟩⟩

/-- Distributional translation preserves actual atomicity on the translated support. -/
theorem atomicOnCarrier_combDistributionTranslation (S : LocallyFiniteCarrier)
    (T : TemperedDistribution ℝ ℂ) (hT : AtomicOnCarrier S T) (a : ℝ) :
    AtomicOnCarrier (S.translate a) (combDistributionTranslation a T) := by
  intro f hf
  rw [combDistributionTranslation_apply]
  apply hT
  intro x hx
  exact hf _ ⟨x,hx,rfl⟩

/-- Character multiplication preserves local atomicity on the original support. -/
theorem atomicOnCarrier_combDistributionModulation (S : LocallyFiniteCarrier)
    (T : TemperedDistribution ℝ ℂ) (hT : AtomicOnCarrier S T) (a : ℝ) :
    AtomicOnCarrier S (combDistributionModulation a T) := by
  intro f hf
  rw [combDistributionModulation_apply]
  apply hT
  intro x hx
  rw [combSchwartzModulation_apply,hf x hx,mul_zero]

/-- Finite atomic convolution has genuine local atomic action on the
finite translated support container; cancellation is not excluded. -/
theorem hasLocallyAtomicAction_finiteCombConvolution
    {ι : Type*} [Fintype ι] (S : LocallyFiniteCarrier)
    (T : TemperedDistribution ℝ ℂ) (hT : HasLocallyAtomicAction S T)
    (a : ι → ℝ) (c : ι → ℂ) :
    HasLocallyAtomicAction (finiteCombConvolutionCarrier S a) (finiteCombConvolution a c T) := by
  apply atomicOnCarrier_hasLocallyAtomicAction
  intro f hf
  rw [finiteCombConvolution_apply_test]
  apply Finset.sum_eq_zero
  intro i _
  rw [hasLocallyAtomicAction_atomicOnCarrier S T hT]
  · exact mul_zero _
  · intro x hx
    exact hf _ (mem_finiteCombConvolutionCarrier S a i hx)

/-- A locally atomic Fourier transform stays on its original carrier
after multiplication by the finite Fourier symbol of a convolution. -/
theorem hasLocallyAtomicAction_fourier_finiteCombConvolution
    {ι : Type*} [Fintype ι] (S : LocallyFiniteCarrier)
    (T : TemperedDistribution ℝ ℂ) (hT : HasLocallyAtomicAction S (𝓕 T))
    (a : ι → ℝ) (c : ι → ℂ) :
    HasLocallyAtomicAction S (𝓕 (finiteCombConvolution a c T)) := by
  apply atomicOnCarrier_hasLocallyAtomicAction
  intro f hf
  rw [fourier_finiteCombConvolution_apply_test]
  apply hasLocallyAtomicAction_atomicOnCarrier S (𝓕 T) hT
  intro x hx
  rw [finiteCombSchwartzSymbol_apply,hf x hx,mul_zero]

/-- Actual local coefficient recovery under modulation, proved using
the full Schwartz vanishing ideal and genuine isolation tests. -/
theorem combDistributionModulation_isolation_apply (S : LocallyFiniteCarrier)
    (T : TemperedDistribution ℝ ℂ) (hT : HasLocallyAtomicAction S T)
    (a : ℝ) (x : S.subtype) :
    combDistributionModulation a T (S.isolationSchwartz x)=
      combModulationCharacter a x*T (S.isolationSchwartz x) := by
  have hz : SchwartzVanishesOn S
      (combSchwartzModulation a (S.isolationSchwartz x)-
        combModulationCharacter a x • S.isolationSchwartz x) := by
    intro y hy
    change combSchwartzModulation a (S.isolationSchwartz x) y-
      (combModulationCharacter a x • S.isolationSchwartz x) y=0
    rw [combSchwartzModulation_apply,smul_apply,smul_eq_mul]
    by_cases hxy : y=(x:ℝ)
    · rw [hxy,sub_self]
    · rw [S.isolationSchwartz_of_mem_of_ne x hy hxy,mul_zero,mul_zero,sub_self]
  have he := hasLocallyAtomicAction_atomicOnCarrier S T hT _ hz
  simpa only [map_sub,map_smul,smul_eq_mul,sub_eq_zero,
    combDistributionModulation_apply] using he

/-- Exact canonical Fourier-side coefficient after finite convolution:
the complete motif symbol multiplies the original local Fourier coefficient. -/
theorem fourier_finiteCombConvolution_isolation_apply
    {ι : Type*} [Fintype ι] (S : LocallyFiniteCarrier)
    (T : TemperedDistribution ℝ ℂ) (hT : HasLocallyAtomicAction S (𝓕 T))
    (a : ι → ℝ) (c : ι → ℂ) (x : S.subtype) :
    𝓕 (finiteCombConvolution a c T) (S.isolationSchwartz x)=
      finiteCombFourierSymbol a c x*𝓕 T (S.isolationSchwartz x) := by
  rw [fourier_finiteCombConvolution]
  simp only [_root_.sum_apply,smul_apply,smul_eq_mul,
    combDistributionModulation_isolation_apply S (𝓕 T) hT,
    finiteCombFourierSymbol,Finset.sum_mul,mul_assoc]

end

end MeyerGeneralProblem
