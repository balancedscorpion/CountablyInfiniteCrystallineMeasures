module

public import MeyerGeneralProblem.Cardinal.Adaptive.OriginalMixedNorms
public import MeyerGeneralProblem.Cardinal.Adaptive.NativeDualOperators
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import all Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

@[expose] public section

/-! # Actual smooth multipliers in original Hermite norms -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open MeasureTheory

private theorem schwartz_lpNorm (f : SchwartzMap ℝ ℂ) :
    lpNorm (f : ℝ → ℂ) 2 volume = ‖f.toLp 2 volume‖ := by
  rw [SchwartzMap.norm_toLp, toReal_eLpNorm]

/-- A finite pointwise sum of Schwartz norm majorants bounds the actual L2 norm. -/
theorem schwartz_norm_toLp_le_weighted_sum {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (hc : ∀ i ∈ s, 0 ≤ c i) (u : SchwartzMap ℝ ℂ) (v : ι → SchwartzMap ℝ ℂ)
    (h : ∀ x, ‖u x‖ ≤ ∑ i ∈ s, c i * ‖v i x‖) :
    ‖u.toLp 2 volume‖ ≤ ∑ i ∈ s, c i * ‖(v i).toLp 2 volume‖ := by
  let g : ι → ℝ → ℝ := fun i x => c i * ‖v i x‖
  have hg (i : ι) : MemLp (g i) 2 volume :=
    ((v i).memLp 2 volume).norm.const_mul (c i)
  have hgs : MemLp (∑ i ∈ s, g i) 2 volume := by
    convert memLp_finsetSum s (fun i hi => hg i) using 1
    ext x
    simp
  have hmono := lpNorm_mono_real hgs (f := (u : ℝ → ℂ))
    (by intro x; simpa only [Finset.sum_apply, g] using h x)
  rw [schwartz_lpNorm] at hmono
  apply hmono.trans ((lpNorm_sum_le (fun i hi => hg i) (by norm_num)).trans_eq ?_)
  apply Finset.sum_congr rfl
  intro i hi
  change lpNorm ((c i) • (fun x : ℝ => ‖v i x‖)) 2 volume = _
  rw [lpNorm_const_smul, lpNorm_norm ((v i).memLp 2 volume).aestronglyMeasurable,
    schwartz_lpNorm]
  change ‖c i‖ * _ = _
  rw [Real.norm_eq_abs, abs_of_nonneg (hc i hi)]

private theorem mixed_multiplier_pointwise (j k d : ℕ) (A : ℝ) (_hA : 0 ≤ A)
    (χ : ℝ → ℂ) (hχ : χ.HasTemperateGrowth)
    (hbound : ∀ r ≤ k, ∀ x, ‖iteratedDeriv r χ x‖ ≤ A*(1+|x|)^d)
    (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    ‖mixedSchwartz j k (SchwartzMap.smulLeftCLM ℂ χ f) x‖ ≤
      ∑ z ∈ (Finset.range (k+1)).product (Finset.range (d+1)),
        ((k.choose z.1:ℝ)*(d.choose z.2:ℝ)*A) * ‖mixedSchwartz (j+z.2) (k-z.1) f x‖ := by
  have he : (SchwartzMap.smulLeftCLM ℂ χ f : ℝ → ℂ) = χ * (f : ℝ → ℂ) := by
    ext y
    simp only [SchwartzMap.smulLeftCLM_apply_apply hχ, Pi.mul_apply, smul_eq_mul]
  rw [mixedSchwartz_apply, he, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    iteratedDeriv_mul (hχ.1.of_le (by simp)).contDiffAt (f.smooth k).contDiffAt]
  have hsum := norm_sum_le (Finset.range (k+1))
    (fun i => (k.choose i:ℂ)*iteratedDeriv i χ x*iteratedDeriv (k-i) (f : ℝ → ℂ) x)
  apply (mul_le_mul_of_nonneg_left hsum (by positivity)).trans
  simp only [norm_mul, Complex.norm_natCast]
  rw [Finset.product_eq_sprod, Finset.sum_product]
  calc
    _ ≤ |x|^j * ∑ i ∈ Finset.range (k+1),
        (k.choose i:ℝ)*(A*(1+|x|)^d)*‖iteratedDeriv (k-i) (f : ℝ → ℂ) x‖ := by
      gcongr with i hi
      exact hbound i (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi) x
    _ = _ := by
      simp only [mixedSchwartz_apply, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, pow_add]
      rw [add_comm (1:ℝ), add_pow]
      simp only [one_pow, mul_one, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro l hl
      ring

/-- Polynomial derivative growth gives an explicit original-order loss.
The bound is uniform over all multipliers with the specified derivative
majorant, and does not depend on a support or a selected finite family. -/
theorem exists_native_polynomial_multiplier_bound (p q d : ℕ)
    (hdegree : 2*p+d ≤ 2*q) (A : ℝ) (hA : 0 ≤ A) :
    ∃ B : ℝ, 0 < B ∧ ∀ (χ : ℝ → ℂ) (_hχ : χ.HasTemperateGrowth),
      (∀ r ≤ 2*p, ∀ x, ‖iteratedDeriv r χ x‖ ≤ A*(1+|x|)^d) →
      ∀ f : SchwartzMap ℝ ℂ,
        ‖schwartzToHermiteScale p (SchwartzMap.smulLeftCLM ℂ χ f)‖ ≤
          B * ‖schwartzToHermiteScale q f‖ := by
  obtain ⟨C,hC,hforward⟩ := exists_mixedL2Sum_le_hermite_norm q
  obtain ⟨D,hD,hreverse⟩ := exists_hermite_norm_le_mixedL2Sum p
  let K (j k : ℕ) : ℝ := ∑ z ∈ (Finset.range (k+1)).product (Finset.range (d+1)),
    ((k.choose z.1:ℝ)*(d.choose z.2:ℝ)*A)*C
  have hK (j k : ℕ) : 0 ≤ K j k := by dsimp [K]; positivity
  let E : ℝ := ∑ z ∈ mixedIndices (2*p), K z.1 z.2
  have hE : 0 ≤ E := Finset.sum_nonneg (fun z hz => hK z.1 z.2)
  refine ⟨D*E+1, by positivity, ?_⟩
  intro χ hχ hbound f
  have hsingle (j k : ℕ) (hjk : j+k ≤ 2*q) :
      ‖(mixedSchwartz j k f).toLp 2 volume‖ ≤ C*‖schwartzToHermiteScale q f‖ := by
    exact (Finset.single_le_sum (s := mixedIndices (2*q)) (a := (j,k))
      (f := fun z : ℕ × ℕ => ‖(mixedSchwartz z.1 z.2 f).toLp 2 volume‖)
      (fun z hz => norm_nonneg _) ((mem_mixedIndices (2*q) j k).mpr hjk)).trans (hforward f)
  have hout (j k : ℕ) (hjk : j+k ≤ 2*p) :
      ‖(mixedSchwartz j k (SchwartzMap.smulLeftCLM ℂ χ f)).toLp 2 volume‖ ≤
        K j k * ‖schwartzToHermiteScale q f‖ := by
    have h := schwartz_norm_toLp_le_weighted_sum ((Finset.range (k+1)).product (Finset.range (d+1)))
      (fun z => (k.choose z.1:ℝ)*(d.choose z.2:ℝ)*A) (fun z hz => by positivity)
      (mixedSchwartz j k (SchwartzMap.smulLeftCLM ℂ χ f))
      (fun z => mixedSchwartz (j+z.2) (k-z.1) f)
      (mixed_multiplier_pointwise j k d A hA χ hχ (fun r hr => hbound r (by omega)) f)
    apply h.trans
    calc
      _ ≤ ∑ z ∈ (Finset.range (k+1)).product (Finset.range (d+1)),
          ((k.choose z.1:ℝ)*(d.choose z.2:ℝ)*A) * (C*‖schwartzToHermiteScale q f‖) := by
        apply Finset.sum_le_sum
        intro z hz
        have hz' : z.1 ≤ k ∧ z.2 ≤ d := by
          simpa only [Finset.product_eq_sprod, Finset.mem_product, Finset.mem_range, Nat.lt_succ_iff] using hz
        exact mul_le_mul_of_nonneg_left (hsingle (j+z.2) (k-z.1) (by omega)) (by positivity)
      _ = K j k * ‖schwartzToHermiteScale q f‖ := by simp only [K, Finset.sum_mul, mul_assoc]
  have hsum : mixedL2Sum (2*p) (SchwartzMap.smulLeftCLM ℂ χ f) ≤
      E * ‖schwartzToHermiteScale q f‖ := by
    unfold mixedL2Sum
    dsimp only [E]
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro z hz
    exact hout z.1 z.2 ((mem_mixedIndices (2*p) z.1 z.2).mp hz)
  have h := (hreverse (SchwartzMap.smulLeftCLM ℂ χ f)).trans
    (mul_le_mul_of_nonneg_left hsum hD.le)
  nlinarith [norm_nonneg (schwartzToHermiteScale q f)]

/-- Uniformly bounded derivatives through order `2*p` give an actual
same-order multiplier on the original positive Hermite scale. -/
theorem exists_native_bounded_multiplier_bound (p : ℕ) (A : ℝ) (hA : 0 ≤ A) :
    ∃ B : ℝ, 0 < B ∧ ∀ (χ : ℝ → ℂ) (_hχ : χ.HasTemperateGrowth),
      (∀ r ≤ 2*p, ∀ x, ‖iteratedDeriv r χ x‖ ≤ A) →
      ∀ f : SchwartzMap ℝ ℂ,
        ‖schwartzToHermiteScale p (SchwartzMap.smulLeftCLM ℂ χ f)‖ ≤
          B * ‖schwartzToHermiteScale p f‖ := by
  simpa only [pow_zero, mul_one] using
    exists_native_polynomial_multiplier_bound p p 0 (by omega) A hA

/-- The fixed growth budget `10*p` through derivative order `2*p` costs
exactly the advertised safe input order `6*p`. -/
theorem exists_native_sixfold_multiplier_bound (p : ℕ) (A : ℝ) (hA : 0 ≤ A) :
    ∃ B : ℝ, 0 < B ∧ ∀ (χ : ℝ → ℂ) (_hχ : χ.HasTemperateGrowth),
      (∀ r ≤ 2*p, ∀ x, ‖iteratedDeriv r χ x‖ ≤ A*(1+|x|)^(10*p)) →
      ∀ f : SchwartzMap ℝ ℂ,
        ‖schwartzToHermiteScale p (SchwartzMap.smulLeftCLM ℂ χ f)‖ ≤
          B * ‖schwartzToHermiteScale (6*p) f‖ :=
  exists_native_polynomial_multiplier_bound p (6*p) (10*p) (by omega) A hA


/-- A finite collection of derivative-dependent constants gives a single
uniform degree-`10*p` majorant for the selector growth law `5*r`. -/
theorem selector_derivative_majorant (p : ℕ) (C : ℕ → ℝ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ χ : ℝ → ℂ,
      (∀ r ≤ 2*p, ∀ x, ‖iteratedDeriv r χ x‖ ≤ C r*(1+|x|)^(5*r)) →
      ∀ r ≤ 2*p, ∀ x, ‖iteratedDeriv r χ x‖ ≤ A*(1+|x|)^(10*p) := by
  let A : ℝ := ∑ r ∈ Finset.range (2*p+1), |C r|
  have hA : 0 ≤ A := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  refine ⟨A,hA,?_⟩
  intro χ hb r hr x
  have hC : C r ≤ A := (le_abs_self _).trans
    (Finset.single_le_sum (s := Finset.range (2*p+1)) (a := r)
      (f := fun t => |C t|) (fun _ _ => abs_nonneg _) (Finset.mem_range.mpr (by omega)))
  have hp : (1+|x|)^(5*r) ≤ (1+|x|)^(10*p) := by
    apply pow_le_pow_right₀ (by linarith [abs_nonneg x])
    omega
  exact (hb r hr x).trans ((mul_le_mul_of_nonneg_right hC (by positivity)).trans
    (mul_le_mul_of_nonneg_left hp hA))

/-- The selector derivative law with fixed constants `C r` yields a single
bound on the actual test multiplier from original order `6*p` to order `p`,
uniform in every selector satisfying those bounds. -/
theorem exists_native_selector_multiplier_bound (p : ℕ) (C : ℕ → ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ (χ : ℝ → ℂ), χ.HasTemperateGrowth →
      (∀ r ≤ 2*p, ∀ x, ‖iteratedDeriv r χ x‖ ≤ C r*(1+|x|)^(5*r)) →
      ∀ f : SchwartzMap ℝ ℂ,
        ‖schwartzToHermiteScale p (SchwartzMap.smulLeftCLM ℂ χ f)‖ ≤
          B * ‖schwartzToHermiteScale (6*p) f‖ := by
  obtain ⟨A,hA,hmajor⟩ := selector_derivative_majorant p C
  obtain ⟨B,hB,hbound⟩ := exists_native_sixfold_multiplier_bound p A hA
  exact ⟨B,hB,fun χ hχ hb => hbound χ hχ (hmajor χ hb)⟩

private theorem mixed_multiplier_indexed_pointwise (j k : ℕ) (d : ℕ → ℕ) (A : ℕ → ℝ)
    (χ : ℝ → ℂ) (hχ : χ.HasTemperateGrowth)
    (hbound : ∀ r ≤ k, ∀ x, ‖iteratedDeriv r χ x‖ ≤ A r*(1+|x|)^(d r))
    (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    ‖mixedSchwartz j k (SchwartzMap.smulLeftCLM ℂ χ f) x‖ ≤
      ∑ z ∈ (Finset.range (k+1)).sigma (fun r => Finset.range (d r+1)),
        ((k.choose z.1:ℝ)*((d z.1).choose z.2:ℝ)*A z.1) * ‖mixedSchwartz (j+z.2) (k-z.1) f x‖ := by
  have he : (SchwartzMap.smulLeftCLM ℂ χ f : ℝ → ℂ) = χ * (f : ℝ → ℂ) := by
    ext y
    simp only [SchwartzMap.smulLeftCLM_apply_apply hχ, Pi.mul_apply, smul_eq_mul]
  rw [mixedSchwartz_apply, he, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    iteratedDeriv_mul (hχ.1.of_le (by simp)).contDiffAt (f.smooth k).contDiffAt]
  have hsum := norm_sum_le (Finset.range (k+1))
    (fun i => (k.choose i:ℂ)*iteratedDeriv i χ x*iteratedDeriv (k-i) (f : ℝ → ℂ) x)
  apply (mul_le_mul_of_nonneg_left hsum (by positivity)).trans
  simp only [norm_mul, Complex.norm_natCast]
  rw [Finset.sum_sigma]
  calc
    _ ≤ |x|^j * ∑ i ∈ Finset.range (k+1),
        (k.choose i:ℝ)*(A i*(1+|x|)^(d i))*‖iteratedDeriv (k-i) (f : ℝ → ℂ) x‖ := by
      gcongr with i hi
      exact hbound i (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi) x
    _ = _ := by
      simp only [mixedSchwartz_apply, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, pow_add]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [add_comm (1:ℝ), add_pow]
      simp only [one_pow, mul_one, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro l hl
      ring

/-- Polynomial derivative growth gives an explicit original-order loss.
The bound is uniform over all multipliers with the specified derivative
majorant, and does not depend on a support or a selected finite family. -/
theorem exists_native_indexed_multiplier_bound (p q : ℕ) (d : ℕ → ℕ)
    (hdegree : ∀ j k r : ℕ, j+k ≤ 2*p → r ≤ k → j+(k-r)+d r ≤ 2*q)
    (A : ℕ → ℝ) (hA : ∀ r, 0 ≤ A r) :
    ∃ B : ℝ, 0 < B ∧ ∀ (χ : ℝ → ℂ) (_hχ : χ.HasTemperateGrowth),
      (∀ r ≤ 2*p, ∀ x, ‖iteratedDeriv r χ x‖ ≤ A r*(1+|x|)^(d r)) →
      ∀ f : SchwartzMap ℝ ℂ,
        ‖schwartzToHermiteScale p (SchwartzMap.smulLeftCLM ℂ χ f)‖ ≤
          B * ‖schwartzToHermiteScale q f‖ := by
  obtain ⟨C,hC,hforward⟩ := exists_mixedL2Sum_le_hermite_norm q
  obtain ⟨D,hD,hreverse⟩ := exists_hermite_norm_le_mixedL2Sum p
  let K (j k : ℕ) : ℝ := ∑ z ∈ (Finset.range (k+1)).sigma (fun r => Finset.range (d r+1)),
    ((k.choose z.1:ℝ)*((d z.1).choose z.2:ℝ)*A z.1)*C
  have hK (j k : ℕ) : 0 ≤ K j k := by
    apply Finset.sum_nonneg
    intro z hz
    exact mul_nonneg (mul_nonneg (by positivity) (hA z.1)) hC.le
  let E : ℝ := ∑ z ∈ mixedIndices (2*p), K z.1 z.2
  have hE : 0 ≤ E := Finset.sum_nonneg (fun z hz => hK z.1 z.2)
  refine ⟨D*E+1, by positivity, ?_⟩
  intro χ hχ hbound f
  have hsingle (j k : ℕ) (hjk : j+k ≤ 2*q) :
      ‖(mixedSchwartz j k f).toLp 2 volume‖ ≤ C*‖schwartzToHermiteScale q f‖ := by
    exact (Finset.single_le_sum (s := mixedIndices (2*q)) (a := (j,k))
      (f := fun z : ℕ × ℕ => ‖(mixedSchwartz z.1 z.2 f).toLp 2 volume‖)
      (fun z hz => norm_nonneg _) ((mem_mixedIndices (2*q) j k).mpr hjk)).trans (hforward f)
  have hout (j k : ℕ) (hjk : j+k ≤ 2*p) :
      ‖(mixedSchwartz j k (SchwartzMap.smulLeftCLM ℂ χ f)).toLp 2 volume‖ ≤
        K j k * ‖schwartzToHermiteScale q f‖ := by
    have h := schwartz_norm_toLp_le_weighted_sum ((Finset.range (k+1)).sigma (fun r => Finset.range (d r+1)))
      (fun z => (k.choose z.1:ℝ)*((d z.1).choose z.2:ℝ)*A z.1) (fun z hz => mul_nonneg (by positivity) (hA z.1))
      (mixedSchwartz j k (SchwartzMap.smulLeftCLM ℂ χ f))
      (fun z => mixedSchwartz (j+z.2) (k-z.1) f)
      (mixed_multiplier_indexed_pointwise j k d A χ hχ (fun r hr => hbound r (by omega)) f)
    apply h.trans
    calc
      _ ≤ ∑ z ∈ (Finset.range (k+1)).sigma (fun r => Finset.range (d r+1)),
          ((k.choose z.1:ℝ)*((d z.1).choose z.2:ℝ)*A z.1) * (C*‖schwartzToHermiteScale q f‖) := by
        apply Finset.sum_le_sum
        intro z hz
        have hz' : z.1 ≤ k ∧ z.2 ≤ d z.1 := by
          simpa only [Finset.mem_sigma, Finset.mem_range, Nat.lt_succ_iff] using hz
        exact mul_le_mul_of_nonneg_left (hsingle (j+z.2) (k-z.1) (by have := hdegree j k z.1 hjk hz'.1; omega))
          (mul_nonneg (by positivity) (hA z.1))
      _ = K j k * ‖schwartzToHermiteScale q f‖ := by simp only [K, Finset.sum_mul, mul_assoc]
  have hsum : mixedL2Sum (2*p) (SchwartzMap.smulLeftCLM ℂ χ f) ≤
      E * ‖schwartzToHermiteScale q f‖ := by
    unfold mixedL2Sum
    dsimp only [E]
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro z hz
    exact hout z.1 z.2 ((mem_mixedIndices (2*p) z.1 z.2).mp hz)
  have h := (hreverse (SchwartzMap.smulLeftCLM ℂ χ f)).trans
    (mul_le_mul_of_nonneg_left hsum hD.le)
  nlinarith [norm_nonneg (schwartzToHermiteScale q f)]


/-- The accepted selector growth `6*r` preserves the sixfold native loss:
the Leibniz term has weight `j+(k-r)+6*r = j+k+5*r`. -/
theorem exists_native_selector_six_growth_bound (p : ℕ) (C : ℕ → ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ (χ : ℝ → ℂ), χ.HasTemperateGrowth →
      (∀ r ≤ 2*p, ∀ x, ‖iteratedDeriv r χ x‖ ≤ C r*(1+|x|)^(6*r)) →
      ∀ f : SchwartzMap ℝ ℂ,
        ‖schwartzToHermiteScale p (SchwartzMap.smulLeftCLM ℂ χ f)‖ ≤
          B * ‖schwartzToHermiteScale (6*p) f‖ := by
  obtain ⟨B,hB,hbound⟩ := exists_native_indexed_multiplier_bound p (6*p)
    (fun r => 6*r) (by intro j k r hjk hr; omega) (fun r => |C r|) (fun r => abs_nonneg _)
  refine ⟨B,hB,fun χ hχ hb => hbound χ hχ ?_⟩
  intro r hr x
  exact (hb r hr x).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))

end
end MeyerGeneralProblem.Adaptive
