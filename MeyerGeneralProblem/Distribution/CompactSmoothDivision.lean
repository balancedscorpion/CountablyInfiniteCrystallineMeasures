module

public import MeyerGeneralProblem.Distribution.CompactSchwartzDensity
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
import all Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
import all Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.DSlope
import all Mathlib.Analysis.Calculus.DSlope
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import all Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

/-!
# Actual smooth removable division on compact Schwartz tests

The derivative integral constructs a smooth divided difference. No division
operator or regularity of a removable quotient is assumed as structure data.
This is the local analytic input to cancellation-preserving atomic recovery.
-/

namespace MeyerGeneralProblem

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff Convolution

/-- Integration over a fixed compact parameter interval preserves smoothness.
The proof expresses the integral as an actual parameterized convolution. -/
theorem contDiff_unitIntervalIntegral {H : ℝ → ℝ → ℂ}
    (hH : ContDiff ℝ ∞ (Function.uncurry H)) :
    ContDiff ℝ ∞ (fun x => ∫ t in (0 : ℝ)..1, H x t) := by
  let w : ℝ → ℝ := (Icc (0 : ℝ) 1).indicator (fun _ => 1)
  let g : ℝ → ℝ → ℂ := fun x t => compactSchwartzCutoff t * H x (-t)
  have hw : Integrable w := by
    apply (integrable_indicator_iff measurableSet_Icc).2
    exact continuous_const.integrableOn_Icc
  have hg : ContDiff ℝ ∞ (Function.uncurry g) := by
    exact ((compactSchwartzCutoff.smooth (⊤ : ℕ∞)).comp contDiff_snd).mul
      (hH.comp (contDiff_fst.prodMk contDiff_snd.neg))
  have hc : ContDiff ℝ ∞ (fun x => (w ⋆[ContinuousLinearMap.lsmul ℝ ℝ] g x) 0) := by
    rw [← contDiffOn_univ]
    apply contDiffOn_convolution_right_with_param_comp
      (k := Icc (-2 : ℝ) 2)
      (ContinuousLinearMap.lsmul ℝ ℝ) contDiffOn_const isOpen_univ isCompact_Icc
    · intro x t _ ht
      have ht' : 2 ≤ |t| := by
        have h := not_and_or.mp ht
        rcases h with h | h <;> simp only [not_le] at h
        · exact le_trans (by linarith) (neg_le_abs t)
        · exact le_trans h.le (le_abs_self t)
      have hz : compactSchwartzCutoff t = 0 := by
        change (compactSchwartzCutoffBump t : ℂ) = 0
        rw [compactSchwartzCutoffBump.zero_of_le_dist]
        · simp
        · simpa [compactSchwartzCutoffBump, Real.dist_eq] using ht'
      dsimp only [g]
      rw [hz, zero_mul]
    · exact hw.locallyIntegrable
    · exact hg.contDiffOn
  have he (x : ℝ) : (w ⋆[ContinuousLinearMap.lsmul ℝ ℝ] g x) 0 =
      ∫ t in (0 : ℝ)..1, H x t := by
    rw [convolution_def]
    have hp : (fun t => (w t) • g x (0-t)) =
        (Icc (0 : ℝ) 1).indicator (H x) := by
      funext t
      by_cases ht : t ∈ Icc (0 : ℝ) 1
      · have hb : compactSchwartzCutoff (-t) = 1 :=
          compactSchwartzCutoff_eq_one (by simpa [abs_neg, abs_of_nonneg ht.1] using ht.2)
        simp only [w, g, indicator_of_mem ht, zero_sub, neg_neg, one_smul]
        rw [hb, one_mul]
      · simp [w, ht]
    simp only [ContinuousLinearMap.lsmul_apply] at ⊢
    rw [hp, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  simpa only [he] using hc

/-- The derivative-integral divided difference, with its removable value
already defined at the center. -/
def smoothDividedDifference (f : ℝ → ℂ) (z x : ℝ) : ℂ :=
  ∫ t in (0 : ℝ)..1, deriv f (z + t * (x-z))

/-- Smoothness is derived by compact-parameter integration. -/
theorem contDiff_smoothDividedDifference {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (z : ℝ) :
    ContDiff ℝ ∞ (smoothDividedDifference f z) := by
  apply contDiff_unitIntervalIntegral
  exact (contDiff_infty_iff_deriv.mp hf).2.comp (by fun_prop)

/-- Multiplication by the vanished linear factor recovers the exact
numerator difference, including the point of removable division. -/
theorem sub_mul_smoothDividedDifference {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (z x : ℝ) :
    ((x-z : ℝ) : ℂ) * smoothDividedDifference f z x = f x - f z := by
  have hd : Differentiable ℝ f := (contDiff_infty_iff_deriv.mp hf).1
  have hc : Continuous (deriv f) := (contDiff_infty_iff_deriv.mp hf).2.continuous
  have h := intervalIntegral.integral_unitInterval_deriv_eq_sub
    (z₀ := z) (z₁ := x-z)
    (hc.comp (show Continuous (fun t : ℝ => z + t • (x-z)) by fun_prop)).continuousOn
    (fun t _ => (hd _).hasDerivAt)
  simpa [smoothDividedDifference, smul_eq_mul, Complex.real_smul] using h

/-- The removable value is the actual derivative. -/
theorem smoothDividedDifference_self (f : ℝ → ℂ) (z : ℝ) :
    smoothDividedDifference f z z = deriv f z := by
  simp [smoothDividedDifference]

/-- A uniform zeroth-seminorm estimate for the genuine divided difference.
The one input derivative is explicit and is not removed by a same-order claim. -/
theorem norm_smoothDividedDifference_le (ψ : SchwartzMap ℝ ℂ) (z x : ℝ) :
    ‖smoothDividedDifference ψ z x‖ ≤ SchwartzMap.seminorm ℂ 0 1 ψ := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (C := SchwartzMap.seminorm ℂ 0 1 ψ)
    (f := fun t => deriv ψ (z+t*(x-z))) (fun t _ => by
      simpa only [pow_zero, one_mul, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
        iteratedDeriv_one] using ψ.le_seminorm ℂ 0 1 (z+t*(x-z)))
  simpa [smoothDividedDifference] using h

/-- Pointwise division with the actual derivative ratio at a simple zero. -/
def removableQuotient (ψ f : ℝ → ℂ) (x : ℝ) : ℂ :=
  if f x = 0 then deriv ψ x / deriv f x else ψ x / f x

/-- Division at simple real zeros is smooth when the numerator vanishes
at those zeros. This proves removable smoothness, rather than assuming it. -/
theorem contDiff_removableQuotient {ψ f : ℝ → ℂ}
    (hψ : ContDiff ℝ ∞ ψ) (hf : ContDiff ℝ ∞ f)
    (hsimple : ∀ z, f z = 0 → deriv f z ≠ 0)
    (hzero : ∀ z, f z = 0 → ψ z = 0) :
    ContDiff ℝ ∞ (removableQuotient ψ f) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : f z = 0
  · let Dψ := smoothDividedDifference ψ z
    let Df := smoothDividedDifference f z
    have hDψ : ContDiff ℝ ∞ Dψ := contDiff_smoothDividedDifference hψ z
    have hDf : ContDiff ℝ ∞ Df := contDiff_smoothDividedDifference hf z
    have hDf0 : Df z ≠ 0 := by
      simpa [Df, smoothDividedDifference_self] using hsimple z hz
    have hnear : ∀ᶠ x in 𝓝 z, Df x ≠ 0 :=
      hDf.continuous.continuousAt.eventually_ne hDf0
    have heq : removableQuotient ψ f =ᶠ[𝓝 z] (fun x => Dψ x * (Df x)⁻¹) := by
      filter_upwards [hnear] with x hx
      by_cases hxz : x = z
      · subst x
        simp [removableQuotient, hz, Dψ, Df, smoothDividedDifference_self, div_eq_mul_inv]
      · have hsub : ((x-z : ℝ) : ℂ) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr hxz
        have hfprod : ((x-z : ℝ) : ℂ) * Df x = f x := by
          simpa only [hz, sub_zero] using sub_mul_smoothDividedDifference hf z x
        have hψprod : ((x-z : ℝ) : ℂ) * Dψ x = ψ x := by
          simpa only [hzero z hz, sub_zero] using sub_mul_smoothDividedDifference hψ z x
        have hfx : f x ≠ 0 := by rw [← hfprod]; exact mul_ne_zero hsub hx
        rw [removableQuotient, if_neg hfx, ← hψprod, ← hfprod]
        field_simp
    exact (hDψ.contDiffAt.mul (hDf.contDiffAt.inv hDf0)).congr_of_eventuallyEq heq
  · have hnear : ∀ᶠ x in 𝓝 z, f x ≠ 0 := hf.continuous.continuousAt.eventually_ne hz
    have heq : removableQuotient ψ f =ᶠ[𝓝 z] (fun x => ψ x * (f x)⁻¹) := by
      filter_upwards [hnear] with x hx
      simp only [removableQuotient, if_neg hx, div_eq_mul_inv]
    exact (hψ.contDiffAt.mul (hf.contDiffAt.inv hz)).congr_of_eventuallyEq heq

/-- The removable quotient is an exact factorization at every point. -/
theorem mul_removableQuotient {ψ f : ℝ → ℂ}
    (hzero : ∀ z, f z = 0 → ψ z = 0) (x : ℝ) :
    f x * removableQuotient ψ f x = ψ x := by
  by_cases hx : f x = 0
  · simp [removableQuotient, hx, hzero x hx]
  · simp [removableQuotient, hx, mul_div_cancel₀]

/-- Removable division preserves compact support. At a zero of the
denominator outside the numerator support, its derivative is also zero. -/
theorem support_removableQuotient_subset {ψ f : ℝ → ℂ} :
    Function.support (removableQuotient ψ f) ⊆ tsupport ψ := by
  intro x hx
  by_contra hxs
  have hψx : ψ x = 0 := image_eq_zero_of_notMem_tsupport hxs
  have hψd : deriv ψ x = 0 := by
    have hn : ∀ᶠ y in 𝓝 x, y ∉ tsupport ψ :=
      (isClosed_tsupport ψ).isOpen_compl.mem_nhds hxs
    have heq : ψ =ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [hn] with y hy
      exact image_eq_zero_of_notMem_tsupport hy
    rw [heq.deriv_eq]
    simp
  exact hx (by simp [removableQuotient, hψx, hψd])

/-- Every compact Schwartz numerator vanishing at all simple zeros has an
actual compact Schwartz quotient, with an exact pointwise multiplication
identity. No estimate on reciprocal values at other carrier nodes is used. -/
def compactSchwartzDivision (ψ : SchwartzMap ℝ ℂ) (hψ : HasCompactSupport ψ)
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hsimple : ∀ z, f z = 0 → deriv f z ≠ 0)
    (hzero : ∀ z, f z = 0 → ψ z = 0) : SchwartzMap ℝ ℂ :=
  (HasCompactSupport.intro hψ (fun x hx =>
    not_not.mp (fun h => hx (support_removableQuotient_subset h)))).toSchwartzMap
    (contDiff_removableQuotient (ψ.smooth (⊤ : ℕ∞)) hf hsimple hzero)

/-- Exact evaluation of the constructed compact Schwartz quotient. -/
theorem compactSchwartzDivision_apply (ψ : SchwartzMap ℝ ℂ) (hψ : HasCompactSupport ψ)
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hsimple : ∀ z, f z = 0 → deriv f z ≠ 0)
    (hzero : ∀ z, f z = 0 → ψ z = 0) (x : ℝ) :
    compactSchwartzDivision ψ hψ f hf hsimple hzero x = removableQuotient ψ f x := rfl

/-- The actual quotient has compact support contained in the original
numerator support closure. -/
theorem compactSchwartzDivision_hasCompactSupport
    (ψ : SchwartzMap ℝ ℂ) (hψ : HasCompactSupport ψ)
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hsimple : ∀ z, f z = 0 → deriv f z ≠ 0)
    (hzero : ∀ z, f z = 0 → ψ z = 0) :
    HasCompactSupport (compactSchwartzDivision ψ hψ f hf hsimple hzero) := by
  exact HasCompactSupport.intro hψ (fun x hx =>
    not_not.mp (fun h => hx (support_removableQuotient_subset h)))

end
end MeyerGeneralProblem
