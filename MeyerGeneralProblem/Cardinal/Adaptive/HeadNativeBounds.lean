module

public import MeyerGeneralProblem.Cardinal.Adaptive.OriginalMixedNorms
public import MeyerGeneralProblem.Cardinal.Adaptive.NativeDualOperators
public import MeyerGeneralProblem.Cardinal.Adaptive.PoissonHeads
public import MeyerGeneralProblem.Sampling.GroupedSpectralGap

@[expose] public section

/-! # Sharp original negative-order membership for actual Poisson heads -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open MeasureTheory

private theorem lattice_separated (a b : ℝ) (ha : 0 < a) (i j : ℤ) (hij : i ≠ j) :
    a ≤ |(b+a*i)-(b+a*j)| := by
  have h : (1:ℝ) ≤ |(i:ℝ)-(j:ℝ)| := by
    exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hij)
  have he : (b+a*i)-(b+a*j) = a*((i:ℝ)-j) := by ring
  rw [he, abs_mul, abs_of_pos ha]
  nlinarith

private theorem finite_lattice_sq_bound (a b : ℝ) (ha : 0 < a)
    (f : SchwartzMap ℝ ℂ) (s : Finset ℤ) :
    ∑ n ∈ s, ‖f (b+a*n)‖^2 ≤
      2*a⁻¹ * ‖f.toLp 2 volume‖^2 + a * ‖(SchwartzMap.derivCLM ℂ ℂ f).toLp 2 volume‖^2 := by
  have h := sum_norm_sq_le_globalSobolev (fun n : {n // n ∈ s} => b+a*(n:ℤ))
    f (SchwartzMap.derivCLM ℂ ℂ f)
    (fun t => f.hasDerivAt t) (SchwartzMap.derivCLM ℂ ℂ f).continuous
    (f.memLp 2 volume) ((SchwartzMap.derivCLM ℂ ℂ f).memLp 2 volume) ha
    (fun i j hij => lattice_separated a b ha i j (by exact fun he => hij (Subtype.ext he)))
  rw [Finset.sum_coe_sort s (fun n : ℤ => ‖f (b+a*n)‖^2)] at h
  exact h

private theorem finite_lattice_weighted_bound (a b : ℝ) (ha : 0 < a)
    (f : SchwartzMap ℝ ℂ) (s : Finset ℤ) :
    ∑ n ∈ s, ((1+|(n:ℝ)|)*‖f (b+a*n)‖)^2 ≤
      2 * (2*a⁻¹ * ‖f.toLp 2 volume‖^2 + a * ‖(SchwartzMap.derivCLM ℂ ℂ f).toLp 2 volume‖^2) +
      2*a⁻¹^2 * (2*a⁻¹ * ‖(coordinateMultiplicationCLM f - (b:ℂ) • f).toLp 2 volume‖^2 +
        a * ‖(SchwartzMap.derivCLM ℂ ℂ (coordinateMultiplicationCLM f - (b:ℂ) • f)).toLp 2 volume‖^2) := by
  let g := coordinateMultiplicationCLM f - (b:ℂ) • f
  have hg (n : ℤ) : ‖g (b+a*n)‖ = a * |(n:ℝ)| * ‖f (b+a*n)‖ := by
    have he : g (b+a*n) = ((a:ℂ)*(n:ℂ))*f (b+a*n) := by
      simp only [g, sub_apply, coordinateMultiplicationCLM_apply, smul_apply, smul_eq_mul,
        Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_intCast]
      ring
    rw [he, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
    simp
  have hpoint (n : ℤ) : ((1+|(n:ℝ)|)*‖f (b+a*n)‖)^2 ≤
      2*‖f (b+a*n)‖^2 + 2*a⁻¹^2*‖g (b+a*n)‖^2 := by
    rw [hg]
    have hi : a⁻¹^2 * (a * |(n:ℝ)| * ‖f (b+a*n)‖)^2 =
        (|(n:ℝ)| * ‖f (b+a*n)‖)^2 := by field_simp
    nlinarith [sq_nonneg (‖f (b+a*n)‖-|(n:ℝ)| *‖f (b+a*n)‖)]
  have hsum := Finset.sum_le_sum (fun n (_ : n ∈ s) => hpoint n)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  exact hsum.trans (add_le_add
    (mul_le_mul_of_nonneg_left (finite_lattice_sq_bound a b ha f s) (by norm_num))
    (mul_le_mul_of_nonneg_left (finite_lattice_sq_bound a b ha g s) (by positivity)))

private theorem exists_weighted_lattice_hermite_bound (a b : ℝ) (ha : 0 < a) :
    ∃ B : ℝ, 0 < B ∧ ∀ (f : SchwartzMap ℝ ℂ) (s : Finset ℤ),
      ∑ n ∈ s, ((1+|(n:ℝ)|)*‖f (b+a*n)‖)^2 ≤ B * ‖schwartzToHermiteScale 1 f‖^2 := by
  obtain ⟨C,hC,hbound⟩ := exists_mixedL2Sum_le_hermite_norm 1
  have hsingle (j k : ℕ) (hjk : j+k ≤ 2) (f : SchwartzMap ℝ ℂ) :
      ‖(mixedSchwartz j k f).toLp 2 volume‖ ≤ C * ‖schwartzToHermiteScale 1 f‖ := by
    have h := Finset.single_le_sum (s := mixedIndices 2) (a := (j,k))
      (f := fun z : ℕ × ℕ => ‖(mixedSchwartz z.1 z.2 f).toLp 2 volume‖)
      (fun z hz => norm_nonneg _) ((mem_mixedIndices 2 j k).mpr hjk)
    exact h.trans (hbound f)
  let K := 2*(2*a⁻¹*C^2+a*C^2) +
    2*a⁻¹^2*(2*a⁻¹*((1+|b|)*C)^2+a*((2+|b|)*C)^2)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K+1, by linarith, ?_⟩
  intro f s
  let H := ‖schwartzToHermiteScale 1 f‖
  have hf : ‖f.toLp 2 volume‖ ≤ C*H := by
    simpa only [mixedSchwartz, Function.iterate_zero_apply] using hsingle 0 0 (by omega) f
  have hd : ‖(SchwartzMap.derivCLM ℂ ℂ f).toLp 2 volume‖ ≤ C*H := by
    simpa only [mixedSchwartz, Function.iterate_zero_apply, Function.iterate_one] using hsingle 0 1 (by omega) f
  have hx : ‖(coordinateMultiplicationCLM f).toLp 2 volume‖ ≤ C*H := by
    simpa only [mixedSchwartz, Function.iterate_zero_apply, Function.iterate_one] using hsingle 1 0 (by omega) f
  have hxd : ‖(coordinateMultiplicationCLM (SchwartzMap.derivCLM ℂ ℂ f)).toLp 2 volume‖ ≤ C*H := by
    simpa only [mixedSchwartz, Function.iterate_one] using hsingle 1 1 (by omega) f
  let g := coordinateMultiplicationCLM f - (b:ℂ) • f
  have hg : ‖g.toLp 2 volume‖ ≤ ((1+|b|)*C)*H := by
    change ‖SchwartzMap.toLpCLM ℂ ℂ 2 volume (coordinateMultiplicationCLM f-(b:ℂ) • f)‖ ≤ _
    rw [map_sub, map_smul]
    have h := norm_sub_le (SchwartzMap.toLpCLM ℂ ℂ 2 volume (coordinateMultiplicationCLM f))
      ((b:ℂ) • SchwartzMap.toLpCLM ℂ ℂ 2 volume f)
    simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs] at h
    have hm := mul_le_mul_of_nonneg_left hf (abs_nonneg b)
    change ‖g.toLp 2 volume‖ ≤ _
    change ‖g.toLp 2 volume‖ ≤ ‖(coordinateMultiplicationCLM f).toLp 2 volume‖ + |b| *‖f.toLp 2 volume‖ at h
    nlinarith
  have hdg : ‖(SchwartzMap.derivCLM ℂ ℂ g).toLp 2 volume‖ ≤ ((2+|b|)*C)*H := by
    have he : SchwartzMap.derivCLM ℂ ℂ g = f + coordinateMultiplicationCLM (SchwartzMap.derivCLM ℂ ℂ f) -
        (b:ℂ) • SchwartzMap.derivCLM ℂ ℂ f := by
      simp only [g, map_sub, map_smul, derivative_coordinateMultiplication]
    rw [he]
    change ‖SchwartzMap.toLpCLM ℂ ℂ 2 volume
      (f + coordinateMultiplicationCLM (SchwartzMap.derivCLM ℂ ℂ f) - (b:ℂ) • SchwartzMap.derivCLM ℂ ℂ f)‖ ≤ _
    rw [map_sub, map_add, map_smul]
    have h := (norm_sub_le
      (SchwartzMap.toLpCLM ℂ ℂ 2 volume f + SchwartzMap.toLpCLM ℂ ℂ 2 volume
        (coordinateMultiplicationCLM (SchwartzMap.derivCLM ℂ ℂ f)))
      ((b:ℂ) • SchwartzMap.toLpCLM ℂ ℂ 2 volume (SchwartzMap.derivCLM ℂ ℂ f))).trans
        (add_le_add (norm_add_le _ _) le_rfl)
    simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs] at h
    have hm := mul_le_mul_of_nonneg_left hd (abs_nonneg b)
    exact h.trans (by change ‖f.toLp 2 volume‖ +
      ‖(coordinateMultiplicationCLM (SchwartzMap.derivCLM ℂ ℂ f)).toLp 2 volume‖ +
      |b| *‖(SchwartzMap.derivCLM ℂ ℂ f).toLp 2 volume‖ ≤ _; nlinarith)
  have hf2 := pow_le_pow_left₀ (norm_nonneg _) hf 2
  have hd2 := pow_le_pow_left₀ (norm_nonneg _) hd 2
  have hg2 := pow_le_pow_left₀ (norm_nonneg _) hg 2
  have hdg2 := pow_le_pow_left₀ (norm_nonneg _) hdg 2
  have h := finite_lattice_weighted_bound a b ha f s
  have hb : ∑ n ∈ s, ((1+|(n:ℝ)|)*‖f (b+a*n)‖)^2 ≤ K*H^2 := by
    apply h.trans
    calc
      _ ≤ 2*(2*a⁻¹*(C*H)^2+a*(C*H)^2) +
        2*a⁻¹^2*(2*a⁻¹*(((1+|b|)*C)*H)^2+a*(((2+|b|)*C)*H)^2) := by
          gcongr
      _ = K*H^2 := by dsimp [K]; ring
  exact hb.trans (by dsimp only [H]; nlinarith [sq_nonneg ‖schwartzToHermiteScale 1 f‖])

/-- Every fixed positive-spacing affine lattice has an absolute sampling
bound in the original first Hermite norm. -/
theorem exists_lattice_absolute_hermite_one_bound (a b : ℝ) (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : SchwartzMap ℝ ℂ,
      Summable (fun n : ℤ => ‖f (b+a*n)‖) ∧
        (∑' n : ℤ, ‖f (b+a*n)‖) ≤ C * ‖schwartzToHermiteScale 1 f‖ := by
  obtain ⟨B,hB,hbound⟩ := exists_weighted_lattice_hermite_bound a b ha
  let S := ∑' n : ℤ, integerCombDecay n
  have hS : 0 ≤ S := tsum_nonneg (fun n => by dsimp [integerCombDecay]; positivity)
  refine ⟨S+B+1, by linarith, ?_⟩
  intro f
  have hfinite (s : Finset ℤ) : ∑ n ∈ s, ‖f (b+a*n)‖ ≤
      (S+B+1) * ‖schwartzToHermiteScale 1 f‖ := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq s
      (fun n : ℤ => (1+|(n:ℝ)|)⁻¹) (fun n : ℤ => (1+|(n:ℝ)|)*‖f (b+a*n)‖)
    have he (n : ℤ) : (1+|(n:ℝ)|)⁻¹*((1+|(n:ℝ)|)*‖f (b+a*n)‖) = ‖f (b+a*n)‖ := by
      rw [← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
    simp_rw [he] at hcs
    have hs : ∑ n ∈ s, (1+|(n:ℝ)|)⁻¹^2 ≤ S :=
      Summable.sum_le_tsum s (fun n hn => by positivity) summable_integerCombDecay
    have hsq : (∑ n ∈ s, ‖f (b+a*n)‖)^2 ≤ S*(B*‖schwartzToHermiteScale 1 f‖^2) :=
      hcs.trans (mul_le_mul hs (hbound f s)
        (Finset.sum_nonneg (fun n hn => sq_nonneg _)) hS)
    have hSB : S*B ≤ (S+B+1)^2 := by nlinarith [sq_nonneg (S-B)]
    have hm := mul_le_mul_of_nonneg_right hSB (sq_nonneg ‖schwartzToHermiteScale 1 f‖)
    have hsq' : (∑ n ∈ s, ‖f (b+a*n)‖)^2 ≤
        ((S+B+1)*‖schwartzToHermiteScale 1 f‖)^2 := hsq.trans (by nlinarith [hm])
    exact (sq_le_sq₀ (Finset.sum_nonneg (fun n hn => norm_nonneg _)) (by positivity)).mp hsq'
  have hs := summable_of_sum_le (fun n : ℤ => norm_nonneg (f (b+a*n))) hfinite
  exact ⟨hs, hs.tsum_le_of_sum_le hfinite⟩

/-- The complete actual half-shifted antiperiodic comb has a sharp first-order
original Hermite bound. Constants may depend on its fixed lattice and shift. -/
theorem exists_halfShiftedComb_hermite_one_bound (k : ℕ) (hk : 1 ≤ k) (m : ℤ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : SchwartzMap ℝ ℂ,
      ‖halfShiftedComb k hk m f‖ ≤ C * ‖schwartzToHermiteScale 1 f‖ := by
  have ha : 0 < 2*(k:ℝ) := by
    have : (0:ℝ)<k := by exact_mod_cast hk
    positivity
  obtain ⟨C,hC,hbound⟩ := exists_lattice_absolute_hermite_one_bound
    (2*(k:ℝ)) (halfShiftedGridPoint k m) ha
  refine ⟨C,hC,?_⟩
  intro f
  rw [halfShiftedComb_apply]
  have hn (n : ℤ) : ‖(-1:ℂ)^n * f (halfShiftedGridPoint k m+2*(k:ℝ)*n)‖ =
      ‖f (halfShiftedGridPoint k m+2*(k:ℝ)*n)‖ := by simp only [norm_mul, norm_zpow, norm_neg, norm_one, one_zpow, one_mul]
  have hs : Summable (fun n : ℤ => ‖(-1:ℂ)^n * f (halfShiftedGridPoint k m+2*(k:ℝ)*n)‖) := by
    simp_rw [hn]
    exact (hbound f).1
  have h := norm_tsum_le_tsum_norm hs
  simp_rw [hn] at h
  exact h.trans (hbound f).2

/-- Any genuine tempered distribution bounded in an original positive Hermite
norm is realized in the corresponding negative scale. The extension is made
from the dense Schwartz image, and Riesz duality uses the bilinear convention. -/
theorem exists_native_representation_of_bound (m : ℕ) (T : TemperedDistribution ℝ ℂ)
    (hT : ∃ C : ℝ, ∀ f : SchwartzMap ℝ ℂ,
      ‖T f‖ ≤ C * ‖schwartzToHermiteScale m f‖) :
    ∃ u : HermiteScale (-(m:ℤ)), hermiteScaleDistribution m u = T := by
  let A : HermiteScale (m:ℤ) →L[ℂ] ℂ := T.toLinearMap.extendOfNorm (schwartzToHermiteScale m).toLinearMap
  let v := (InnerProductSpace.toDual ℂ (HermiteScale (m:ℤ))).symm A
  refine ⟨star v, ?_⟩
  ext f
  rw [hermiteScaleDistribution_apply]
  have hp (u : HermiteScale (m:ℤ)) : hermiteScalePairing (m:ℤ) (star v) u = inner ℂ v u := by
    rw [hermiteScalePairing, lp.inner_eq_tsum]
    apply tsum_congr
    intro n
    simp [RCLike.inner_apply, mul_comm]
  rw [hp]
  exact InnerProductSpace.toDual_symm_apply.trans
    (LinearMap.extendOfNorm_eq (schwartzToHermiteScale_denseRange m) hT f)


/-- Whole-distribution realization of every actual half-shifted comb at
negative original order one. -/
theorem halfShiftedComb_has_native_one_representation (k : ℕ) (hk : 1 ≤ k) (m : ℤ) :
    ∃ u : HermiteScale (-1), hermiteScaleDistribution 1 u = halfShiftedComb k hk m := by
  obtain ⟨C,hC,hbound⟩ := exists_halfShiftedComb_hermite_one_bound k hk m
  exact exists_native_representation_of_bound 1 _ ⟨C,hbound⟩

/-- Every actual finite Poisson head lies in the image of the original
negative Hermite scale of order one. -/
theorem poissonHeadSpace_le_native_one_range (k : ℕ) (hk : 1 ≤ k) :
    poissonHeadSpace k hk ≤ (hermiteScaleDistributionCLM 1).toLinearMap.range := by
  rintro T ⟨c,rfl⟩
  change (∑ i : Fin (4*k^2), c i • halfShiftedComb k hk (headIndex k i)) ∈ _
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.smul_mem
  exact halfShiftedComb_has_native_one_representation k hk (headIndex k i)

end
end MeyerGeneralProblem.Adaptive
