module

public import MeyerGeneralProblem.Cardinal.Adaptive.HalfWeylSource
public import MeyerGeneralProblem.Hermite.Exhaustion

@[expose] public section

/-! # Actual whole Zak action on separated Schwartz tests -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open scoped FourierTransform BigOperators

/-- Polynomially weighted integer samples of an actual Schwartz function have
a summable fixed integer-decay majorant. -/
theorem weighted_schwartz_int_sample_le (f : SchwartzMap ℝ ℂ) (r : ℕ) (n : ℤ) :
    (1+|(n : ℝ)|)^r*‖f (n : ℝ)‖ ≤
      (2^(r+2)*(Finset.Iic (r+2,0)).sup (schwartzSeminormFamily ℂ ℝ ℂ) f)*integerCombDecay n := by
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ)
    (m := (r+2,0)) (k := r+2) (n := 0) le_rfl le_rfl f (n : ℝ)
  simp only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] at h
  have hpos : 0<(1+|(n : ℝ)|)^2 := by positivity
  rw [integerCombDecay,inv_pow,← div_eq_mul_inv,le_div_iff₀ hpos]
  convert! h using 1
  rw [pow_add]
  ring

/-- Every polynomially weighted integer Schwartz sample sequence is summable. -/
theorem summable_weighted_schwartz_int_samples (f : SchwartzMap ℝ ℂ) (r : ℕ) :
    Summable (fun n : ℤ => (1+|(n : ℝ)|)^r*‖f (n : ℝ)‖) := by
  apply Summable.of_nonneg_of_le (fun n => by positivity)
    (weighted_schwartz_int_sample_le f r)
  exact summable_integerCombDecay.mul_left _

/-- An original tempered distribution acts polynomially on the whole family
of translates of one Schwartz test, with a proved original-native bound. -/
theorem tempered_test_translation_polynomial_bound (T : TemperedDistribution ℝ ℂ)
    (f : SchwartzMap ℝ ℂ) :
    ∃ (p : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ a : ℝ,
      ‖T (combSchwartzTranslation a f)‖ ≤ C*(1+|a|)^(2*p) := by
  obtain ⟨p,u,hu⟩ := exists_hermiteScale_representation T
  obtain ⟨C,hC,hbound⟩ := exists_hermite_translation_bound p
  refine ⟨p,‖u‖*C*‖schwartzToHermiteScale p f‖,by positivity,?_⟩
  intro a
  rw [← hu,hermiteScaleDistribution_apply]
  have h := (norm_hermiteScalePairing_le (p : ℤ) u
    (schwartzToHermiteScale p (combSchwartzTranslation a f))).trans
      (mul_le_mul_of_nonneg_left (hbound a f) (norm_nonneg u))
  simpa only [mul_assoc,mul_left_comm,mul_comm] using h

/-- Absolute convergence of the original whole-source Zak test series.
No ordering of phase coefficients or separate phase tempering is used. -/
theorem summable_zakTensorAction (T : TemperedDistribution ℝ ℂ)
    (f g : SchwartzMap ℝ ℂ) :
    Summable (fun n : ℤ => (𝓕 g) (n : ℝ)*T (combSchwartzTranslation (-(n : ℝ)) f)) := by
  obtain ⟨p,C,hC,hbound⟩ := tempered_test_translation_polynomial_bound T f
  apply Summable.of_norm_bounded
    ((summable_weighted_schwartz_int_samples (𝓕 g) (2*p)).mul_left C)
  intro n
  rw [norm_mul]
  have h := mul_le_mul_of_nonneg_left (hbound (-(n : ℝ))) (norm_nonneg ((𝓕 g) (n : ℝ)))
  simpa only [abs_neg,mul_assoc,mul_left_comm,mul_comm] using h

/-- The actual distributional Zak action on a separated Schwartz test f(x)g(y),
with the original negative Fourier phase and complete translated source. -/
def zakTensorAction (T : TemperedDistribution ℝ ℂ) (f g : SchwartzMap ℝ ℂ) : ℂ :=
  ∑' n : ℤ, (𝓕 g) (n : ℝ)*T (combSchwartzTranslation (-(n : ℝ)) f)

/-- Whole-source linearity of the absolutely convergent Zak test action. -/
theorem zakTensorAction_add_source (T U : TemperedDistribution ℝ ℂ) (f g : SchwartzMap ℝ ℂ) :
    zakTensorAction (T+U) f g=zakTensorAction T f g+zakTensorAction U f g := by
  simp only [zakTensorAction,_root_.add_apply,mul_add]
  exact (summable_zakTensorAction T f g).tsum_add (summable_zakTensorAction U f g)

/-- The first test variable retains exact complex linearity. -/
theorem zakTensorAction_add_left (T : TemperedDistribution ℝ ℂ) (f h g : SchwartzMap ℝ ℂ) :
    zakTensorAction T (f+h) g=zakTensorAction T f g+zakTensorAction T h g := by
  simp only [zakTensorAction,map_add,mul_add]
  exact (summable_zakTensorAction T f g).tsum_add (summable_zakTensorAction T h g)

/-- The second test variable retains exact complex linearity. -/
theorem zakTensorAction_add_right (T : TemperedDistribution ℝ ℂ) (f g h : SchwartzMap ℝ ℂ) :
    zakTensorAction T f (g+h)=zakTensorAction T f g+zakTensorAction T f h := by
  simp only [zakTensorAction,FourierTransform.fourier_add,_root_.add_apply,add_mul]
  exact (summable_zakTensorAction T f g).tsum_add (summable_zakTensorAction T f h)


/-- The frequency probe is an actual Schwartz function whose Fourier samples
select one whole integer translate, with the original Fourier normalization. -/
def zakFrequencyProbe (m : ℤ) : SchwartzMap ℝ ℂ :=
  𝓕⁻ ((shiftedIntegerCombCarrier 0).isolationSchwartz
    ⟨(m : ℝ),⟨m,by simp⟩⟩)

/-- Exact cardinal Fourier samples of the constructed Schwartz frequency probe. -/
theorem zakFrequencyProbe_fourier (m n : ℤ) :
    (𝓕 (zakFrequencyProbe m)) (n : ℝ)=if n=m then 1 else 0 := by
  rw [zakFrequencyProbe,FourierTransform.fourier_fourierInv_eq]
  by_cases h : n=m
  · subst n
    rw [LocallyFiniteCarrier.isolationSchwartz_self]
    simp
  · rw [ite_eq_right h]
    apply LocallyFiniteCarrier.isolationSchwartz_of_mem_of_ne
    · exact ⟨n,by simp⟩
    · change (n : ℝ) ≠ (m : ℝ)
      exact_mod_cast h

/-- The whole tensor action recovers each translated original Schwartz test. -/
theorem zakTensorAction_frequency_probe (T : TemperedDistribution ℝ ℂ)
    (f : SchwartzMap ℝ ℂ) (m : ℤ) :
    zakTensorAction T f (zakFrequencyProbe m)=T (combSchwartzTranslation (-(m : ℝ)) f) := by
  simp [zakTensorAction,zakFrequencyProbe_fourier]

/-- The zero-frequency probe recovers the entire original distribution. -/
theorem zakTensorAction_frequency_zero (T : TemperedDistribution ℝ ℂ) (f : SchwartzMap ℝ ℂ) :
    zakTensorAction T f (zakFrequencyProbe 0)=T f := by
  rw [zakTensorAction_frequency_probe]
  congr 1
  ext x
  simp only [combSchwartzTranslation_apply,Int.cast_zero,neg_zero,zero_add]

/-- Faithfulness is proved on whole original sources, including arbitrary
non-atomic distributions; no moment-representation hypothesis is imposed. -/
theorem zakTensorAction_faithful (T : TemperedDistribution ℝ ℂ)
    (hT : ∀ f g : SchwartzMap ℝ ℂ, zakTensorAction T f g=0) : T=0 := by
  ext f
  have h := hT f (zakFrequencyProbe 0)
  rwa [zakTensorAction_frequency_zero] at h

/-- Complex homogeneity in the whole original source. -/
theorem zakTensorAction_smul_source (a : ℂ) (T : TemperedDistribution ℝ ℂ) (f g : SchwartzMap ℝ ℂ) :
    zakTensorAction (a •T) f g=a*zakTensorAction T f g := by
  simp only [zakTensorAction,_root_.smul_apply,smul_eq_mul]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  ring

/-- Complex homogeneity in the first actual Schwartz test. -/
theorem zakTensorAction_smul_left (a : ℂ) (T : TemperedDistribution ℝ ℂ) (f g : SchwartzMap ℝ ℂ) :
    zakTensorAction T (a •f) g=a*zakTensorAction T f g := by
  simp only [zakTensorAction,map_smul,smul_eq_mul]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  ring

/-- Complex homogeneity in the second actual Schwartz test. -/
theorem zakTensorAction_smul_right (a : ℂ) (T : TemperedDistribution ℝ ℂ) (f g : SchwartzMap ℝ ℂ) :
    zakTensorAction T f (a •g)=a*zakTensorAction T f g := by
  have he : 𝓕 (a •g)=a •𝓕 g := map_smul (FourierTransform.fourierCLM ℂ (SchwartzMap ℝ ℂ)) a g
  simp only [zakTensorAction,he,_root_.smul_apply,smul_eq_mul]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  ring


/-- The faithful whole tensor action satisfies a proved original-native bound,
with a fixed finite Fourier-side Schwartz seminorm and no phase constants. -/
theorem zakTensorAction_native_bound (p : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : HermiteScale (-(p : ℤ))) (f g : SchwartzMap ℝ ℂ),
      ‖zakTensorAction (hermiteScaleDistributionCLM p T) f g‖ ≤
        C*‖T‖*‖schwartzToHermiteScale p f‖*
          (Finset.Iic (2*p+2,0)).sup (schwartzSeminormFamily ℂ ℝ ℂ) (𝓕 g) := by
  obtain ⟨C,hC,hbound⟩ := exists_hermite_translation_bound p
  let D : ℝ := ∑' n : ℤ, integerCombDecay n
  have hD : 0 ≤ D := tsum_nonneg fun n => by unfold integerCombDecay; positivity
  refine ⟨C*2^(2*p+2)*D+1,by positivity,?_⟩
  intro T f g
  let S := (Finset.Iic (2*p+2,0)).sup (schwartzSeminormFamily ℂ ℝ ℂ) (𝓕 g)
  have hS : 0 ≤ S := apply_nonneg _ _
  have hterm (n : ℤ) :
      ‖(𝓕 g) (n : ℝ)*(hermiteScaleDistributionCLM p T)
        (combSchwartzTranslation (-(n : ℝ)) f)‖ ≤
        (‖T‖*C*‖schwartzToHermiteScale p f‖*(2^(2*p+2)*S))*integerCombDecay n := by
    rw [norm_mul]
    rw [hermiteScaleDistributionCLM_apply,hermiteScaleDistribution_apply]
    have ht := (norm_hermiteScalePairing_le (p : ℤ) T
      (schwartzToHermiteScale p (combSchwartzTranslation (-(n : ℝ)) f))).trans
        (mul_le_mul_of_nonneg_left (hbound (-(n : ℝ)) f) (norm_nonneg T))
    calc
      _ ≤ ‖(𝓕 g) (n : ℝ)‖*(‖T‖*(C*(1+|(n : ℝ)|)^(2*p)*‖schwartzToHermiteScale p f‖)) := by
        simpa only [abs_neg] using mul_le_mul_of_nonneg_left ht (norm_nonneg ((𝓕 g) (n : ℝ)))
      _ = (‖T‖*C*‖schwartzToHermiteScale p f‖)*
          ((1+|(n : ℝ)|)^(2*p)*‖(𝓕 g) (n : ℝ)‖) := by ring
      _ ≤ (‖T‖*C*‖schwartzToHermiteScale p f‖)*((2^(2*p+2)*S)*integerCombDecay n) :=
        mul_le_mul_of_nonneg_left (weighted_schwartz_int_sample_le (𝓕 g) (2*p) n) (by positivity)
      _ = _ := by ring
  have hs := summable_zakTensorAction (hermiteScaleDistributionCLM p T) f g
  calc
    _ ≤ ∑' n : ℤ, ‖(𝓕 g) (n : ℝ)*(hermiteScaleDistributionCLM p T)
        (combSchwartzTranslation (-(n : ℝ)) f)‖ := by
      exact norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' n : ℤ, (‖T‖*C*‖schwartzToHermiteScale p f‖*(2^(2*p+2)*S))*integerCombDecay n :=
      by
        exact hs.norm.tsum_le_tsum hterm (summable_integerCombDecay.mul_left _)
    _ = (C*2^(2*p+2)*D)*‖T‖*‖schwartzToHermiteScale p f‖*S := by
      rw [tsum_mul_left]
      dsimp [D]
      ring
    _ ≤ _ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (show C*2^(2*p+2)*D ≤ C*2^(2*p+2)*D+1 from le_add_of_nonneg_right zero_le_one)
          (norm_nonneg T)) (norm_nonneg _)) hS


/-- The Fourier-precomposed tensor action is a genuine continuous Schwartz
functional, constructed using the original-native bound. -/
def zakFourierSlice (T : TemperedDistribution ℝ ℂ) (f : SchwartzMap ℝ ℂ) :
    TemperedDistribution ℝ ℂ :=
  SchwartzMap.mkCLMtoNormedSpace (fun g => zakTensorAction T f (𝓕⁻ g))
    (fun g h => by
      have he : 𝓕⁻ (g+h)=𝓕⁻ g+𝓕⁻ h := map_add
        (FourierTransform.fourierInvCLM ℂ (SchwartzMap ℝ ℂ)) g h
      rw [he,zakTensorAction_add_right])
    (fun a g => by
      have he : 𝓕⁻ (a •g)=a •𝓕⁻ g := map_smul
        (FourierTransform.fourierInvCLM ℂ (SchwartzMap ℝ ℂ)) a g
      rw [he,zakTensorAction_smul_right]
      rfl)
    (by
      obtain ⟨p,u,hu⟩ := exists_hermiteScale_representation T
      obtain ⟨C,hC,hbound⟩ := zakTensorAction_native_bound p
      refine ⟨Finset.Iic (2*p+2,0),C*‖u‖*‖schwartzToHermiteScale p f‖,by positivity,?_⟩
      intro g
      have h := hbound u f (𝓕⁻ g)
      rw [hermiteScaleDistributionCLM_apply,hu,FourierTransform.fourier_fourierInv_eq] at h
      exact h)

/-- For every physical Schwartz test, the Zak action is an actual tempered
frequency distribution, with no moment or phase-separation hypothesis. -/
def zakTensorSlice (T : TemperedDistribution ℝ ℂ) (f : SchwartzMap ℝ ℂ) :
    TemperedDistribution ℝ ℂ :=
  (zakFourierSlice T f).comp (FourierTransform.fourierCLM ℂ (SchwartzMap ℝ ℂ))

/-- The constructed frequency distribution is precisely the complete convergent
Zak tensor series with the original Fourier phase. -/
theorem zakTensorSlice_apply (T : TemperedDistribution ℝ ℂ) (f g : SchwartzMap ℝ ℂ) :
    zakTensorSlice T f g=zakTensorAction T f g := by
  change zakTensorAction T f (𝓕⁻ (𝓕 g))=_
  rw [FourierTransform.fourierInv_fourier_eq]

/-- The family of actual frequency distributions retains the entire original
source; this statement also detects non-atomic sources and derivative jets. -/
theorem zakTensorSlice_faithful (T : TemperedDistribution ℝ ℂ)
    (hT : ∀ f : SchwartzMap ℝ ℂ, zakTensorSlice T f=0) : T=0 := by
  apply zakTensorAction_faithful
  intro f g
  rw [← zakTensorSlice_apply,hT f]
  rfl

/-- If a test vanishes at every translated carrier point, its actual Zak
frequency distribution is zero. This proves the physical support implication
for the whole source, including all infinite phases together. -/
theorem zakTensorSlice_zero_of_translated_vanishing (S : LocallyFiniteCarrier)
    (T : TemperedDistribution ℝ ℂ) (hT : AtomicOnCarrier S T)
    (f : SchwartzMap ℝ ℂ) (hf : ∀ (n : ℤ) (x : ℝ), x ∈ S.carrier → f (x-(n : ℝ))=0) :
    zakTensorSlice T f=0 := by
  ext g
  rw [zakTensorSlice_apply]
  change (∑' n : ℤ, (𝓕 g) (n : ℝ)*T (combSchwartzTranslation (-(n : ℝ)) f))=0
  have hz (n : ℤ) : T (combSchwartzTranslation (-(n : ℝ)) f)=0 := hT _ (by
    intro x hx
    simpa only [combSchwartzTranslation_apply,sub_eq_add_neg,add_comm] using hf n x hx)
  simp only [hz,mul_zero,tsum_zero]

end
end MeyerGeneralProblem.Adaptive
