module

public import MeyerGeneralProblem.Distribution.MeyerSpace
public import Mathlib.Analysis.Fourier.PoissonSummation
import all Mathlib.Analysis.Fourier.PoissonSummation

@[expose] public section

/-!
# Genuine integer Dirac combs

Bounded integer weights define continuous Schwartz functionals by an
explicit summable seminorm majorant. The unweighted integer comb is fixed
by the actual distributional Fourier transform, by the library's proved
Schwartz Poisson summation theorem. No strictness witness is asserted.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set SchwartzMap
open scoped SchwartzMap FourierTransform

/-- A fixed summable majorant for integer samples of Schwartz tests. -/
def integerCombDecay (n : ℤ) : ℝ := (1+|(n:ℝ)|)⁻¹^2

/-- The sample majorant is summable, including its nonsingular central term. -/
theorem summable_integerCombDecay : Summable integerCombDecay := by
  rw [summable_int_iff_summable_nat_and_neg]
  have h : Summable (fun n : ℕ => ((n:ℝ)+1)⁻¹^2) := by
    simpa only [Nat.cast_add,Nat.cast_one,one_div,inv_pow] using
      (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1<2))
  constructor <;> simpa [integerCombDecay,abs_of_nonneg,add_comm] using h

/-- Actual integer samples are bounded by one fixed finite Schwartz seminorm. -/
theorem norm_schwartz_int_sample_le (f : SchwartzMap ℝ ℂ) (n : ℤ) :
    ‖f (n:ℝ)‖ ≤
      (4*(Finset.Iic (2,0)).sup (schwartzSeminormFamily ℂ ℝ ℂ) f)*integerCombDecay n := by
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ)
    (m := (2,0)) (k := 2) (n := 0) le_rfl le_rfl f (n:ℝ)
  have hpos : 0 < (1+|(n:ℝ)|)^2 := by positivity
  rw [integerCombDecay,inv_pow]
  rw [← div_eq_mul_inv,le_div_iff₀ hpos]
  convert! h using 1 <;>
    norm_num [Real.norm_eq_abs,norm_iteratedFDeriv_zero,schwartzSeminormFamily,mul_comm]
  rfl

/-- Every bounded integer coefficient family acts absolutely summably on
each actual Schwartz test. -/
theorem summable_weightedInteger_samples (w : ℤ → ℂ) {B : ℝ}
    (hB : 0 ≤ B) (hw : ∀ n, ‖w n‖ ≤ B) (f : SchwartzMap ℝ ℂ) :
    Summable (fun n : ℤ => w n*f (n:ℝ)) := by
  apply Summable.of_norm_bounded (summable_integerCombDecay.mul_left
    (B*(4*(Finset.Iic (2,0)).sup (schwartzSeminormFamily ℂ ℝ ℂ) f)))
  intro n
  rw [norm_mul]
  exact (mul_le_mul (hw n) (norm_schwartz_int_sample_le f n) (norm_nonneg _) hB).trans_eq (by ring)

/-- The actual infinite weighted sample sum has a uniform Schwartz seminorm bound. -/
theorem norm_weightedInteger_sum_le (w : ℤ → ℂ) {B : ℝ}
    (hB : 0 ≤ B) (hw : ∀ n, ‖w n‖ ≤ B) (f : SchwartzMap ℝ ℂ) :
    ‖∑' n : ℤ, w n*f (n:ℝ)‖ ≤
      (B*4*(∑' n, integerCombDecay n))*
        (Finset.Iic (2,0)).sup (schwartzSeminormFamily ℂ ℝ ℂ) f := by
  have hsum := summable_weightedInteger_samples w hB hw f
  calc
    _ ≤ ∑' n : ℤ, ‖w n*f (n:ℝ)‖ := norm_tsum_le_tsum_norm hsum.norm
    _ ≤ ∑' n : ℤ, (B*(4*(Finset.Iic (2,0)).sup (schwartzSeminormFamily ℂ ℝ ℂ) f))*
        integerCombDecay n := hsum.norm.tsum_le_tsum
      (fun n => by
        rw [norm_mul]
        exact (mul_le_mul (hw n) (norm_schwartz_int_sample_le f n) (norm_nonneg _) hB).trans_eq (by ring))
      (summable_integerCombDecay.mul_left _)
    _ = _ := by rw [tsum_mul_left]; ring

/-- The genuine bounded-weight integer sampling functional on Schwartz space. -/
def weightedIntegerCombCLM (w : ℤ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hw : ∀ n, ‖w n‖ ≤ B) : SchwartzMap ℝ ℂ →L[ℂ] ℂ :=
  SchwartzMap.mkCLMtoNormedSpace
    (fun f => ∑' n : ℤ, w n*f (n:ℝ))
    (fun f g => by
      simp only [add_apply,mul_add]
      exact Summable.tsum_add (summable_weightedInteger_samples w hB hw f)
        (summable_weightedInteger_samples w hB hw g))
    (fun c f => by
      simp only [smul_apply,smul_eq_mul,RingHom.id_apply]
      simp_rw [show ∀ n : ℤ, w n*(c*f (n:ℝ))=c*(w n*f (n:ℝ)) by intro n; ring]
      exact tsum_mul_left)
    ⟨Finset.Iic (2,0),B*4*(∑' n, integerCombDecay n),by
      have hs : 0 ≤ ∑' n, integerCombDecay n := tsum_nonneg (fun _ => sq_nonneg _)
      positivity,norm_weightedInteger_sum_le w hB hw⟩

/-- A bounded weighted integer Dirac comb as an actual tempered distribution. -/
def weightedIntegerComb (w : ℤ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hw : ∀ n, ‖w n‖ ≤ B) : TemperedDistribution ℝ ℂ :=
  ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ)
    (SchwartzMap ℝ ℂ) ℂ (weightedIntegerCombCLM w B hB hw)

/-- The tempered functional evaluates to the genuine absolutely convergent sum. -/
theorem weightedIntegerComb_apply (w : ℤ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hw : ∀ n, ‖w n‖ ≤ B) (f : SchwartzMap ℝ ℂ) :
    weightedIntegerComb w B hB hw f=∑' n : ℤ, w n*f (n:ℝ) := rfl

/-- The classical unweighted integer comb, with unit coefficient at every integer. -/
def integerComb : TemperedDistribution ℝ ℂ :=
  weightedIntegerComb (fun _ => 1) 1 (by norm_num) (by intro n; norm_num)

/-- Exact action of the classical integer comb. -/
theorem integerComb_apply (f : SchwartzMap ℝ ℂ) :
    integerComb f=∑' n : ℤ, f (n:ℝ) := by
  simp only [integerComb,weightedIntegerComb_apply,one_mul]

/-- The integer support as an extensional locally finite carrier. -/
def integerCombCarrier : LocallyFiniteCarrier where
  carrier := Set.range (fun n : ℤ => (n:ℝ))
  finite_inter_Icc a b := by
    apply ((Set.finite_Icc ⌈a⌉ ⌊b⌋).image (fun n : ℤ => (n:ℝ))).subset
    rintro x ⟨⟨n,rfl⟩,hlo,hhi⟩
    exact ⟨n,⟨Int.ceil_le.mpr hlo,Int.le_floor.mpr hhi⟩,rfl⟩

/-- Every integer lies in the actual support carrier. -/
theorem int_mem_integerCombCarrier (n : ℤ) : (n:ℝ) ∈ integerCombCarrier.carrier := ⟨n,rfl⟩

/-- Bounded-weight combs annihilate the complete Schwartz vanishing ideal. -/
theorem weightedIntegerComb_atomicOnCarrier (w : ℤ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hw : ∀ n, ‖w n‖ ≤ B) :
    AtomicOnCarrier integerCombCarrier (weightedIntegerComb w B hB hw) := by
  intro f hf
  rw [weightedIntegerComb_apply]
  simp only [hf _ (int_mem_integerCombCarrier _),mul_zero,tsum_zero]

/-- The local finite atomic formula follows for every compact Schwartz test. -/
theorem weightedIntegerComb_hasLocallyAtomicAction (w : ℤ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hw : ∀ n, ‖w n‖ ≤ B) :
    HasLocallyAtomicAction integerCombCarrier (weightedIntegerComb w B hB hw) :=
  atomicOnCarrier_hasLocallyAtomicAction _ _ (weightedIntegerComb_atomicOnCarrier w B hB hw)

/-- Poisson summation identifies the actual Fourier transform of the
integer comb, with exactly the repository's Fourier normalization. -/
theorem fourier_integerComb : 𝓕 integerComb=integerComb := by
  ext f
  rw [TemperedDistribution.fourier_apply,integerComb_apply,integerComb_apply]
  have h := f.tsum_eq_tsum_fourier 0
  simpa using h.symm

/-- The integer comb belongs to the genuine distributional Meyer space
on its integer support, without replacing that space by a spectral model. -/
theorem integerComb_mem_distributionalMeyerSpace :
    integerComb ∈ DistributionalMeyerSpace integerCombCarrier := by
  rw [mem_distributionalMeyerSpace_iff]
  have h := weightedIntegerComb_hasLocallyAtomicAction (fun _ => (1:ℂ)) 1 (by norm_num)
    (by intro n; norm_num)
  exact ⟨h,by rw [fourier_integerComb]; exact h⟩

end

end MeyerGeneralProblem
