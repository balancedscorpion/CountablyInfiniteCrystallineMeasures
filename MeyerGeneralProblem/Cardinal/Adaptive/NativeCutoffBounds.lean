module

public import MeyerGeneralProblem.Cardinal.Adaptive.NativeMultipliers
public import MeyerGeneralProblem.Distribution.CompactSchwartzDensity

@[expose] public section

/-! # Inverse-radius cutoff errors in original Hermite norms -/

namespace MeyerGeneralProblem.Adaptive
noncomputable section
open MeasureTheory

private theorem cutoff_error_weight_bound (N : ℕ) (x : ℝ) :
    ‖scaledCompactSchwartzCutoff N x - 1‖ ≤ 2*compactSchwartzCutoffScale N*|x| := by
  have hscale := (compactSchwartzCutoffScale_pos N).le
  by_cases hx : |x| ≤ (N:ℝ)+1
  · rw [scaledCompactSchwartzCutoff_eq_one N hx,sub_self,norm_zero]
    positivity
  · have hh : 1 ≤ compactSchwartzCutoffScale N*|x| := by
      rw [compactSchwartzCutoffScale,inv_mul_eq_div]
      exact (le_div_iff₀ (by positivity : (0:ℝ) < (N:ℝ)+1)).mpr (by simpa only [one_mul] using (le_of_not_ge hx))
    have hb := norm_scaledCompactSchwartzCutoff_sub_one_le_two N x
    nlinarith

def cutoffCoefficient (k r : ℕ) : ℝ :=
  (k.choose r:ℝ)*(if r=0 then 2 else SchwartzMap.seminorm ℂ 0 r compactSchwartzCutoff)

private theorem cutoffCoefficient_nonneg (k r : ℕ) : 0 ≤ cutoffCoefficient k r := by
  unfold cutoffCoefficient
  apply mul_nonneg (by positivity)
  split_ifs <;> positivity

private theorem mixed_cutoff_error_pointwise (N j k : ℕ) (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    ‖mixedSchwartz j k (compactSchwartzApproximation N f-f) x‖ ≤
      ∑ r ∈ Finset.range (k+1), (compactSchwartzCutoffScale N*cutoffCoefficient k r)*
        ‖mixedSchwartz (j+if r=0 then 1 else 0) (k-r) f x‖ := by
  rw [mixedSchwartz_apply, norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,
    iteratedDeriv_compactSchwartzApproximation_sub]
  apply (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity : 0 ≤ |x|^j)).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r hr
  simp only [norm_mul,Complex.norm_natCast,mixedSchwartz_apply,norm_pow,
    Complex.norm_real,Real.norm_eq_abs]
  by_cases hz : r=0
  · subst r
    simp only [cutoffCoefficient,ite_true,Nat.choose_zero_right,Nat.cast_one,one_mul,
      iteratedDeriv_zero,Nat.sub_zero,pow_succ]
    have h := mul_le_mul_of_nonneg_right (cutoff_error_weight_bound N x)
      (by positivity : 0 ≤ |x|^j*‖iteratedDeriv k (f : ℝ → ℂ) x‖)
    nlinarith
  · simp only [cutoffCoefficient,hz,ite_false,Nat.add_zero]
    have h := mul_le_mul_of_nonneg_right
      (norm_iteratedDeriv_scaledCompactSchwartzCutoff_sub_one_le N r hz x)
      (by positivity : 0 ≤ |x|^j*(k.choose r:ℝ)*‖iteratedDeriv (k-r) (f : ℝ → ℂ) x‖)
    nlinarith

/-- One additional original Hermite order uniformly pays the expanding
cutoff error, with the explicit inverse-radius rate. -/
theorem exists_native_cutoff_error_bound (p : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ (N : ℕ) (f : SchwartzMap ℝ ℂ),
      ‖schwartzToHermiteScale p (f-compactSchwartzApproximation N f)‖ ≤
        compactSchwartzCutoffScale N*B*‖schwartzToHermiteScale (p+1) f‖ := by
  obtain ⟨C,hC,hforward⟩ := exists_mixedL2Sum_le_hermite_norm (p+1)
  obtain ⟨D,hD,hreverse⟩ := exists_hermite_norm_le_mixedL2Sum p
  let K (k : ℕ) : ℝ := ∑ r ∈ Finset.range (k+1), cutoffCoefficient k r*C
  have hK (k : ℕ) : 0 ≤ K k := Finset.sum_nonneg (fun r _ =>
    mul_nonneg (cutoffCoefficient_nonneg k r) hC.le)
  let E : ℝ := ∑ z ∈ mixedIndices (2*p), K z.2
  have hE : 0 ≤ E := Finset.sum_nonneg (fun z _ => hK z.2)
  refine ⟨D*E+1,by positivity,fun N f => ?_⟩
  have hsingle (j k : ℕ) (hjk : j+k ≤ 2*(p+1)) :
      ‖(mixedSchwartz j k f).toLp 2 volume‖ ≤ C*‖schwartzToHermiteScale (p+1) f‖ :=
    (Finset.single_le_sum (s := mixedIndices (2*(p+1))) (a := (j,k))
      (f := fun z : ℕ × ℕ => ‖(mixedSchwartz z.1 z.2 f).toLp 2 volume‖)
      (fun z _ => norm_nonneg _) ((mem_mixedIndices _ j k).mpr hjk)).trans (hforward f)
  have hterm (j k : ℕ) (hjk : j+k ≤ 2*p) :
      ‖(mixedSchwartz j k (compactSchwartzApproximation N f-f)).toLp 2 volume‖ ≤
        compactSchwartzCutoffScale N*K k*‖schwartzToHermiteScale (p+1) f‖ := by
    have h := schwartz_norm_toLp_le_weighted_sum (Finset.range (k+1))
      (fun r => compactSchwartzCutoffScale N*cutoffCoefficient k r)
      (fun r _ => mul_nonneg (compactSchwartzCutoffScale_pos N).le (cutoffCoefficient_nonneg k r))
      (mixedSchwartz j k (compactSchwartzApproximation N f-f))
      (fun r => mixedSchwartz (j+if r=0 then 1 else 0) (k-r) f)
      (mixed_cutoff_error_pointwise N j k f)
    apply h.trans
    calc
      _ ≤ ∑ r ∈ Finset.range (k+1), (compactSchwartzCutoffScale N*cutoffCoefficient k r)*
          (C*‖schwartzToHermiteScale (p+1) f‖) := by
        apply Finset.sum_le_sum
        intro r hr
        have hd : j+(if r=0 then 1 else 0)+(k-r) ≤ 2*(p+1) := by split_ifs <;> omega
        exact mul_le_mul_of_nonneg_left (hsingle _ _ hd)
          (mul_nonneg (compactSchwartzCutoffScale_pos N).le (cutoffCoefficient_nonneg k r))
      _ = _ := by simp only [K,Finset.mul_sum,Finset.sum_mul,mul_assoc]
  have hs : mixedL2Sum (2*p) (compactSchwartzApproximation N f-f) ≤
      compactSchwartzCutoffScale N*E*‖schwartzToHermiteScale (p+1) f‖ := by
    unfold mixedL2Sum
    simp only [E,Finset.mul_sum,Finset.sum_mul]
    apply Finset.sum_le_sum
    intro z hz
    exact hterm z.1 z.2 ((mem_mixedIndices _ _ _).mp hz)
  have h := (hreverse (compactSchwartzApproximation N f-f)).trans
    (mul_le_mul_of_nonneg_left hs hD.le)
  rw [map_sub,norm_sub_rev,← map_sub] at h
  nlinarith [mul_nonneg (compactSchwartzCutoffScale_pos N).le (norm_nonneg (schwartzToHermiteScale (p+1) f))]

end
end MeyerGeneralProblem.Adaptive
