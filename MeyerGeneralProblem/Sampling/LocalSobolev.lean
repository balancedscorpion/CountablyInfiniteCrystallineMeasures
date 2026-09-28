module

public import MeyerGeneralProblem.Sampling.UpperLargeSieve
public import Mathlib.Analysis.InnerProductSpace.Calculus
import all Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.MeasureTheory.Integral.Average
import all Mathlib.MeasureTheory.Integral.Average

@[expose] public section

/-!
# Local one-dimensional Sobolev sampling

This module proves the point-evaluation estimate used by the irregular
Fourier-rectangle argument.  The constants retain the sampling scale: the
zeroth-order energy costs `δ⁻¹`, while the derivative energy costs `δ`.
-/

namespace MeyerGeneralProblem

open MeasureTheory

noncomputable section

-- Keep the real normed-space structure on `ℂ` definitionally aligned with
-- the continuous-linear-map calculus used by the Fourier phase module.
/-- The standard complex normed additive group, fixed locally so real
calculus instances elaborate definitionally consistently. -/
local instance : NormedAddCommGroup ℂ := Complex.instNormedAddCommGroup

/-- A point value is controlled by the `L²` energies of a complex-valued
function and its derivative on the centered interval of length `δ`. -/
theorem norm_sq_le_localSobolev
    (f f' : ℝ → ℂ)
    (hf : ∀ t, HasDerivAt f (f' t) t)
    (hf' : Continuous f')
    {x δ : ℝ} (hδ : 0 < δ) :
    ‖f x‖ ^ 2 ≤
      2 * δ⁻¹ *
          (∫ t : ℝ in Set.Icc (x - δ / 2) (x + δ / 2), ‖f t‖ ^ 2) +
        δ *
          (∫ t : ℝ in Set.Icc (x - δ / 2) (x + δ / 2), ‖f' t‖ ^ 2) := by
  let I : Set ℝ := Set.Icc (x - δ / 2) (x + δ / 2)
  let F : ℝ → ℝ := fun t => ‖f t‖ ^ 2
  let G : ℝ → ℝ := fun t => ‖f' t‖ ^ 2
  let D : ℝ → ℝ := fun t => 2 * inner ℝ (f t) (f' t)
  let H : ℝ → ℝ := fun t => δ⁻¹ * F t + δ * G t
  have hcontf : Continuous f := continuous_iff_continuousAt.mpr fun t =>
    (hf t).continuousAt
  have hcontF : Continuous F := hcontf.norm.pow 2
  have hcontG : Continuous G := hf'.norm.pow 2
  have hcontD : Continuous D := by
    dsimp only [D]
    fun_prop
  have hcontH : Continuous H := by
    dsimp only [H]
    fun_prop
  have hIlen : x + δ / 2 - (x - δ / 2) = δ := by ring
  have hImeasure : volume I = ENNReal.ofReal δ := by
    dsimp only [I]
    rw [Real.volume_Icc, hIlen]
  have hμ : volume.restrict I ≠ 0 := by
    intro hzero
    have hmeasureZero : volume I = 0 := Measure.restrict_eq_zero.mp hzero
    rw [hImeasure] at hmeasureZero
    exact (ne_of_gt (ENNReal.ofReal_pos.mpr hδ)) hmeasureZero
  have hFint : Integrable F (volume.restrict I) := by
    exact ContinuousOn.integrableOn_compact isCompact_Icc hcontF.continuousOn
  have hcompl : (volume.restrict I) Iᶜ = 0 := by
    rw [Measure.restrict_apply measurableSet_Icc.compl,
      Set.compl_inter_self, measure_empty]
  obtain ⟨t, htI, htavg⟩ :=
    exists_notMem_null_le_average hμ hFint hcompl
  have ht : t ∈ I := by simpa only [Set.mem_compl_iff, not_not] using htI
  have hmeasureReal : (volume.restrict I).real Set.univ = δ := by
    rw [measureReal_restrict_apply_univ, measureReal_def, hImeasure,
      ENNReal.toReal_ofReal hδ.le]
  have htmean : F t ≤ δ⁻¹ * ∫ z : ℝ in I, F z := by
    rw [average_eq, hmeasureReal] at htavg
    simpa only [smul_eq_mul] using htavg
  have hDderiv (z : ℝ) : HasDerivAt F (D z) z := by
    simpa only [F, D] using (hf z).norm_sq
  have hderiv : deriv F = D := by
    funext z
    exact (hDderiv z).deriv
  have hFTC (a b : ℝ) : (∫ z : ℝ in a..b, D z) = F b - F a := by
    exact intervalIntegral.integral_deriv_eq_sub' F hderiv
      (fun z _ => (hDderiv z).differentiableAt) hcontD.continuousOn
  have hDle (z : ℝ) : ‖D z‖ ≤ H z := by
    have hinner := abs_real_inner_le_norm (f z) (f' z)
    have hyoung :
        2 * ‖f' z‖ * ‖f z‖ ≤
          δ * ‖f' z‖ ^ 2 + δ⁻¹ * ‖f z‖ ^ 2 :=
      two_mul_le_add_mul_sq hδ
    dsimp only [D, H, F, G]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    calc
      2 * |inner ℝ (f z) (f' z)| ≤ 2 * (‖f z‖ * ‖f' z‖) := by
        gcongr
      _ = 2 * ‖f' z‖ * ‖f z‖ := by ring
      _ ≤ δ * ‖f' z‖ ^ 2 + δ⁻¹ * ‖f z‖ ^ 2 := hyoung
      _ = δ⁻¹ * ‖f z‖ ^ 2 + δ * ‖f' z‖ ^ 2 := by ring
  have hHnonneg (z : ℝ) : 0 ≤ H z := by
    dsimp only [H, F, G]
    positivity
  have hlocal (z : ℝ) (hz : z ∈ I) : |F x - F z| ≤ ∫ w : ℝ in I, H w := by
    have hzlo : x - δ / 2 ≤ z := hz.1
    have hzhi : z ≤ x + δ / 2 := hz.2
    by_cases hzx : z ≤ x
    · have hnorm : ‖∫ w : ℝ in z..x, D w‖ ≤ ∫ w : ℝ in z..x, H w :=
        intervalIntegral.norm_integral_le_of_norm_le hzx
          (ae_of_all _ fun w _ => hDle w)
          hcontH.continuousOn.intervalIntegrable
      rw [hFTC] at hnorm
      have hsub : Set.Ioc z x ⊆ I := by
        intro w hw
        constructor <;> linarith [hw.1, hw.2]
      have hmono : (∫ w : ℝ in z..x, H w) ≤ ∫ w : ℝ in I, H w := by
        rw [intervalIntegral.integral_of_le hzx]
        exact setIntegral_mono_set
          (ContinuousOn.integrableOn_compact isCompact_Icc hcontH.continuousOn)
          (ae_of_all _ fun w => hHnonneg w)
          (ae_of_all _ hsub)
      rw [Real.norm_eq_abs] at hnorm
      exact hnorm.trans hmono
    · have hxz : x ≤ z := le_of_not_ge hzx
      have hnorm : ‖∫ w : ℝ in x..z, D w‖ ≤ ∫ w : ℝ in x..z, H w :=
        intervalIntegral.norm_integral_le_of_norm_le hxz
          (ae_of_all _ fun w _ => hDle w)
          hcontH.continuousOn.intervalIntegrable
      rw [hFTC] at hnorm
      have hsub : Set.Ioc x z ⊆ I := by
        intro w hw
        constructor <;> linarith [hw.1, hw.2]
      have hmono : (∫ w : ℝ in x..z, H w) ≤ ∫ w : ℝ in I, H w := by
        rw [intervalIntegral.integral_of_le hxz]
        exact setIntegral_mono_set
          (ContinuousOn.integrableOn_compact isCompact_Icc hcontH.continuousOn)
          (ae_of_all _ fun w => hHnonneg w)
          (ae_of_all _ hsub)
      rw [Real.norm_eq_abs, abs_sub_comm] at hnorm
      exact hnorm.trans hmono
  have hxle : F x ≤ F t + ∫ z : ℝ in I, H z := by
    linarith [le_abs_self (F x - F t), hlocal t ht]
  have hHint : (∫ z : ℝ in I, H z) =
      δ⁻¹ * (∫ z : ℝ in I, F z) +
        δ * (∫ z : ℝ in I, G z) := by
    dsimp only [H]
    rw [integral_add, integral_const_mul, integral_const_mul]
    · exact (ContinuousOn.integrableOn_compact isCompact_Icc
        hcontF.continuousOn).const_mul _
    · exact (ContinuousOn.integrableOn_compact isCompact_Icc
        hcontG.continuousOn).const_mul _
  dsimp only [F, G, I] at htmean hxle hHint ⊢
  rw [hHint] at hxle
  linarith

/-- Summed local Sobolev estimate on a finite separated sampling family.
The local half-open intervals are disjoint, so their energies embed into one
interval enlarged by `δ / 2` at each endpoint. -/
theorem sum_norm_sq_le_localSobolev
    {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (f f' : ℝ → ℂ)
    (hf : ∀ t, HasDerivAt f (f' t) t)
    (hf' : Continuous f')
    {δ lo hi : ℝ} (hδ : 0 < δ)
    (hsep : ∀ i j, i ≠ j → δ ≤ |x i - x j|)
    (hlo : ∀ i, lo ≤ x i) (hhi : ∀ i, x i ≤ hi) :
    (∑ i, ‖f (x i)‖ ^ 2) ≤
      2 * δ⁻¹ *
          (∫ t : ℝ in Set.Icc (lo - δ / 2) (hi + δ / 2), ‖f t‖ ^ 2) +
        δ *
          (∫ t : ℝ in Set.Icc (lo - δ / 2) (hi + δ / 2), ‖f' t‖ ^ 2) := by
  let J : ι → Set ℝ := fun i =>
    Set.Ioc (x i - δ / 2) (x i + δ / 2)
  let K : Set ℝ := Set.Icc (lo - δ / 2) (hi + δ / 2)
  let F : ℝ → ℝ := fun t => ‖f t‖ ^ 2
  let G : ℝ → ℝ := fun t => ‖f' t‖ ^ 2
  have hcontf : Continuous f := continuous_iff_continuousAt.mpr fun t =>
    (hf t).continuousAt
  have hcontF : Continuous F := hcontf.norm.pow 2
  have hcontG : Continuous G := hf'.norm.pow 2
  have hdisj : Pairwise (Function.onFun Disjoint J) := by
    intro i j hij
    change Disjoint (J i) (J j)
    rw [Set.disjoint_left]
    intro z hzi hzj
    have hgap := hsep i j hij
    by_cases hixj : x i ≤ x j
    · rw [abs_of_nonpos (sub_nonpos.mpr hixj)] at hgap
      linarith [hzi.2, hzj.1]
    · have hjxi : x j ≤ x i := le_of_not_ge hixj
      rw [abs_of_nonneg (sub_nonneg.mpr hjxi)] at hgap
      linarith [hzi.1, hzj.2]
  have hJK : (⋃ i, J i) ⊆ K := by
    apply Set.iUnion_subset
    intro i z hz
    constructor
    · dsimp only [J] at hz
      linarith [hlo i, hz.1]
    · dsimp only [J] at hz
      linarith [hhi i, hz.2]
  have hsumF :
      (∑ i, ∫ t : ℝ in Set.Icc (x i - δ / 2) (x i + δ / 2), F t) ≤
        ∫ t : ℝ in K, F t := by
    simp_rw [integral_Icc_eq_integral_Ioc]
    rw [← integral_iUnion_fintype (fun i => measurableSet_Ioc)
      hdisj (fun i => ContinuousOn.integrableOn_compact isCompact_Icc
        hcontF.continuousOn |>.mono_set (by exact Set.Ioc_subset_Icc_self))]
    exact setIntegral_mono_set
      (ContinuousOn.integrableOn_compact isCompact_Icc hcontF.continuousOn)
      (ae_of_all _ fun t => sq_nonneg ‖f t‖)
      (ae_of_all _ hJK)
  have hsumG :
      (∑ i, ∫ t : ℝ in Set.Icc (x i - δ / 2) (x i + δ / 2), G t) ≤
        ∫ t : ℝ in K, G t := by
    simp_rw [integral_Icc_eq_integral_Ioc]
    rw [← integral_iUnion_fintype (fun i => measurableSet_Ioc)
      hdisj (fun i => ContinuousOn.integrableOn_compact isCompact_Icc
        hcontG.continuousOn |>.mono_set (by exact Set.Ioc_subset_Icc_self))]
    exact setIntegral_mono_set
      (ContinuousOn.integrableOn_compact isCompact_Icc hcontG.continuousOn)
      (ae_of_all _ fun t => sq_nonneg ‖f' t‖)
      (ae_of_all _ hJK)
  calc
    (∑ i, ‖f (x i)‖ ^ 2) ≤
        ∑ i, (2 * δ⁻¹ *
            (∫ t : ℝ in Set.Icc (x i - δ / 2) (x i + δ / 2), F t) +
          δ *
            (∫ t : ℝ in Set.Icc (x i - δ / 2) (x i + δ / 2), G t)) := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [F, G] using norm_sq_le_localSobolev f f' hf hf' hδ
    _ = 2 * δ⁻¹ *
          (∑ i, ∫ t : ℝ in Set.Icc (x i - δ / 2) (x i + δ / 2), F t) +
        δ *
          (∑ i, ∫ t : ℝ in Set.Icc (x i - δ / 2) (x i + δ / 2), G t) := by
      simp only [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ 2 * δ⁻¹ * (∫ t : ℝ in K, F t) +
        δ * (∫ t : ℝ in K, G t) := by
      gcongr
    _ = 2 * δ⁻¹ *
          (∫ t : ℝ in Set.Icc (lo - δ / 2) (hi + δ / 2), ‖f t‖ ^ 2) +
        δ *
          (∫ t : ℝ in Set.Icc (lo - δ / 2) (hi + δ / 2), ‖f' t‖ ^ 2) := by
      rfl

end

end MeyerGeneralProblem
