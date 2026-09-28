module

public import MeyerGeneralProblem.Cardinal.Adaptive.FiniteSmoothPartition
public import MeyerGeneralProblem.Cardinal.Adaptive.TranslatedTestTailBudget
public import MeyerGeneralProblem.Cardinal.Adaptive.NativeDualOperators
public import Mathlib.Analysis.Calculus.MeanValue
import all Mathlib.Analysis.Calculus.MeanValue

@[expose] public section

/-! # Fixed-order errors for physical phase translations

Compact tests with bounded derivatives control actual original Hermite norms.
A change of physical phase costs one additional test derivative, with constants
chosen before the test and the source. The derivative order does not grow with
stage or the number of partition pieces.
-/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open Set

/-- Homogeneous version of the actual finite-regularity compact-test bound. -/
theorem exists_compact_finite_regularity_native_bound_mul (q : ℕ) (H : ℝ) (hH : 0 ≤ H) :
    ∃ B : ℝ, 0 < B ∧ ∀ f : SchwartzMap ℝ ℂ,
      tsupport f ⊆ Icc (-H) H → ∀ A : ℝ, 0 ≤ A →
      (∀ r ≤ 2*q, ∀ x, ‖iteratedDeriv r (f : ℝ → ℂ) x‖ ≤ A) →
      ‖schwartzToHermiteScale q f‖ ≤ B*A := by
  obtain ⟨B,hB,hbound⟩ := exists_compact_finite_regularity_native_bound q H hH
  refine ⟨B,hB,fun f hs A hA hf => ?_⟩
  rcases eq_or_lt_of_le hA with hzero | hpos
  · have he : f = 0 := by
      ext x
      have h := hf 0 (by omega) x
      simpa only [iteratedDeriv_zero, ← hzero, norm_le_zero_iff, zero_apply] using h
    simp [he, ← hzero]
  · let g : SchwartzMap ℝ ℂ := (A : ℂ)⁻¹ • f
    have hgs : tsupport g ⊆ Icc (-H) H :=
      (tsupport_smul_subset_right (fun _ : ℝ => (A : ℂ)⁻¹) (f : ℝ → ℂ)).trans hs
    have hgd : ∀ r ≤ 2*q, ∀ x, ‖iteratedDeriv r (g : ℝ → ℂ) x‖ ≤ 1 := by
      intro r hr x
      change ‖iteratedDeriv r ((A : ℂ)⁻¹ • (f : ℝ → ℂ)) x‖ ≤ 1
      rw [iteratedDeriv_const_smul_field, norm_smul, norm_inv, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hpos]
      exact (inv_mul_le_iff₀ hpos).mpr (by simpa using hf r hr x)
    have hb := hbound g hgs hgd
    change ‖schwartzToHermiteScale q ((A : ℂ)⁻¹ • f)‖ ≤ B at hb
    rw [map_smul, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos] at hb
    exact (inv_mul_le_iff₀ hpos).mp hb |>.trans_eq (mul_comm A B)

/-- The true derivative of a translated test is Lipschitz in its physical phase. -/
theorem translated_iteratedDeriv_sub_bound (f : SchwartzMap ℝ ℂ) (r : ℕ)
    (A : ℝ) (hf : ∀ x, ‖iteratedDeriv (r+1) (f : ℝ → ℂ) x‖ ≤ A) (a b x : ℝ) :
    ‖iteratedDeriv r (combSchwartzTranslation a f : ℝ → ℂ) x -
      iteratedDeriv r (combSchwartzTranslation b f : ℝ → ℂ) x‖ ≤ A*|a-b| := by
  have hd : Differentiable ℝ (iteratedDeriv r (f : ℝ → ℂ)) :=
    (f.smooth (r+1)).differentiable_iteratedDeriv' r
  have hb := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun y (_ : y ∈ (univ : Set ℝ)) => hd y)
    (fun y (_ : y ∈ (univ : Set ℝ)) => by simpa only [← iteratedDeriv_succ] using hf y)
    convex_univ (mem_univ (b+x)) (mem_univ (a+x))
  change ‖iteratedDeriv r (fun y => f (a+y)) x -
    iteratedDeriv r (fun y => f (b+y)) x‖ ≤ _
  simpa only [iteratedDeriv_comp_const_add, Real.norm_eq_abs, add_sub_add_right_eq_sub] using hb

/-- A compactly supported test stays in a uniformly padded interval under bounded translation. -/
theorem translated_test_tsupport_subset (f : SchwartzMap ℝ ℂ) (H S a : ℝ)
    (hs : tsupport f ⊆ Icc (-H) H) (ha : |a| ≤ S) :
    tsupport (combSchwartzTranslation a f) ⊆ Icc (-(H+S)) (H+S) := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  have hf : a+x ∈ tsupport f := subset_closure (by simpa only
    [Function.mem_support, combSchwartzTranslation_apply] using hx)
  have hb := hs hf
  have hab := abs_le.mp ha
  constructor <;> linarith [hb.1,hb.2,hab.1,hab.2]

/-- Actual translation differences have a first-order physical phase error in H_q,
using only 2q+1 test derivatives on one fixed compact interval. -/
theorem exists_compact_translation_error_bound (q : ℕ) (H S : ℝ)
    (hH : 0 ≤ H) (hS : 0 ≤ S) :
    ∃ B : ℝ, 0 < B ∧ ∀ f : SchwartzMap ℝ ℂ,
      tsupport f ⊆ Icc (-H) H → ∀ A : ℝ, 0 ≤ A →
      (∀ r ≤ 2*q+1, ∀ x, ‖iteratedDeriv r (f : ℝ → ℂ) x‖ ≤ A) →
      ∀ a b : ℝ, |a| ≤ S → |b| ≤ S →
      ‖schwartzToHermiteScale q (combSchwartzTranslation a f - combSchwartzTranslation b f)‖ ≤
        B*A*|a-b| := by
  obtain ⟨B,hB,hbound⟩ := exists_compact_finite_regularity_native_bound_mul q (H+S) (add_nonneg hH hS)
  refine ⟨B,hB,fun f hs A hA hf a b ha hb => ?_⟩
  have hsupport : tsupport (combSchwartzTranslation a f - combSchwartzTranslation b f) ⊆
      Icc (-(H+S)) (H+S) := by
    apply closure_minimal _ isClosed_Icc
    intro x hx
    by_contra hn
    have hna : x ∉ tsupport (combSchwartzTranslation a f) := fun h =>
      hn (translated_test_tsupport_subset f H S a hs ha h)
    have hnb : x ∉ tsupport (combSchwartzTranslation b f) := fun h =>
      hn (translated_test_tsupport_subset f H S b hs hb h)
    exact hx (by simp only [sub_apply,image_eq_zero_of_notMem_tsupport hna,
      image_eq_zero_of_notMem_tsupport hnb,sub_self])
  have hderiv : ∀ r ≤ 2*q, ∀ x,
      ‖iteratedDeriv r (combSchwartzTranslation a f - combSchwartzTranslation b f : ℝ → ℂ) x‖ ≤ A*|a-b| := by
    intro r hr x
    rw [iteratedDeriv_sub ((combSchwartzTranslation a f).smooth r).contDiffAt
      ((combSchwartzTranslation b f).smooth r).contDiffAt]
    exact translated_iteratedDeriv_sub_bound f r A (hf (r+1) (by omega)) a b x
  simpa only [mul_assoc] using hbound _ hsupport (A*|a-b|) (mul_nonneg hA (abs_nonneg _)) hderiv

/-- Dualizing the genuine test estimate gives the physical phase error for every original source. -/
theorem exists_native_phase_pairing_error_bound (q : ℕ) (H S : ℝ)
    (hH : 0 ≤ H) (hS : 0 ≤ S) :
    ∃ B : ℝ, 0 < B ∧ ∀ f : SchwartzMap ℝ ℂ,
      tsupport f ⊆ Icc (-H) H → ∀ A : ℝ, 0 ≤ A →
      (∀ r ≤ 2*q+1, ∀ x, ‖iteratedDeriv r (f : ℝ → ℂ) x‖ ≤ A) →
      ∀ a b : ℝ, |a| ≤ S → |b| ≤ S → ∀ T : HermiteScale (-(q : ℤ)),
      ‖combDistributionTranslation a (hermiteScaleDistribution q T) f -
        combDistributionTranslation b (hermiteScaleDistribution q T) f‖ ≤ B * A * |a-b| * ‖T‖ := by
  obtain ⟨B,hB,hbound⟩ := exists_compact_translation_error_bound q H S hH hS
  refine ⟨B,hB,fun f hs A hA hf a b ha hb T => ?_⟩
  rw [combDistributionTranslation_apply,combDistributionTranslation_apply,← map_sub,
    hermiteScaleDistribution_apply]
  exact (norm_hermiteScalePairing_le (q : ℤ) T _).trans
    ((mul_le_mul_of_nonneg_left (hbound f hs A hA hf a b ha hb) (norm_nonneg T)).trans_eq (mul_comm _ _))

/-- Multiplication by one actual Schwartz piece preserves a fixed derivative bound. -/
theorem exists_piece_finite_derivative_bound (ζ : SchwartzMap ℝ ℂ) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : SchwartzMap ℝ ℂ, ∀ A : ℝ, 0 ≤ A →
      (∀ r ≤ n, ∀ x, ‖iteratedDeriv r (f : ℝ → ℂ) x‖ ≤ A) →
      ∀ r ≤ n, ∀ x,
        ‖iteratedDeriv r (SchwartzMap.smulLeftCLM ℂ ζ f : ℝ → ℂ) x‖ ≤ C*A := by
  classical
  let B (r : ℕ) : ℝ := ∑ i ∈ Finset.range (r+1),
    (r.choose i : ℝ) * SchwartzMap.seminorm ℂ 0 i ζ
  have hB r : 0 ≤ B r := by dsimp [B]; positivity
  let C : ℝ := 1 + ∑ r ∈ Finset.range (n+1), B r
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,fun f A hA hf r hr x => ?_⟩
  have he : (SchwartzMap.smulLeftCLM ℂ ζ f : ℝ → ℂ) = (ζ : ℝ → ℂ) * (f : ℝ → ℂ) := by
    ext y
    simp only [SchwartzMap.smulLeftCLM_apply_apply ζ.hasTemperateGrowth,Pi.mul_apply,smul_eq_mul]
  rw [he,iteratedDeriv_mul (ζ.smooth r).contDiffAt (f.smooth r).contDiffAt]
  have hsum := norm_sum_le (Finset.range (r+1))
    (fun i => (r.choose i : ℂ) * iteratedDeriv i (ζ : ℝ → ℂ) x * iteratedDeriv (r-i) (f : ℝ → ℂ) x)
  apply hsum.trans
  simp only [norm_mul,Complex.norm_natCast]
  have ht : (∑ i ∈ Finset.range (r+1),
      (r.choose i : ℝ) * ‖iteratedDeriv i (ζ : ℝ → ℂ) x‖ *
      ‖iteratedDeriv (r-i) (f : ℝ → ℂ) x‖) ≤ B r*A := by
    dsimp only [B]
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i hi
    have hz : ‖iteratedDeriv i (ζ : ℝ → ℂ) x‖ ≤ SchwartzMap.seminorm ℂ 0 i ζ := by
      simpa only [pow_zero,one_mul] using SchwartzMap.le_seminorm' ℂ 0 i ζ x
    gcongr
    exact hf (r-i) (by omega) x
  have hb : B r ≤ C := by
    have h := Finset.single_le_sum (fun j _ => hB j) (Finset.mem_range.mpr (by omega : r < n+1))
    change B r ≤ 1 + ∑ j ∈ Finset.range (n+1), B j
    linarith
  exact ht.trans (mul_le_mul_of_nonneg_right hb hA)

/-- The physical phase error for an actual compact partition piece, with all constants
fixed before the test and the negative-scale source. -/
theorem exists_piece_phase_pairing_error_bound (q : ℕ) (ζ : SchwartzMap ℝ ℂ)
    (H S : ℝ) (hH : 0 ≤ H) (hS : 0 ≤ S) :
    ∃ B : ℝ, 0 < B ∧ ∀ f : SchwartzMap ℝ ℂ,
      tsupport f ⊆ Icc (-H) H → ∀ A : ℝ, 0 ≤ A →
      (∀ r ≤ 2*q+1, ∀ x, ‖iteratedDeriv r (f : ℝ → ℂ) x‖ ≤ A) →
      ∀ a b : ℝ, |a| ≤ S → |b| ≤ S → ∀ T : HermiteScale (-(q : ℤ)),
      let v := SchwartzMap.smulLeftCLM ℂ ζ f
      ‖combDistributionTranslation a (hermiteScaleDistribution q T) v -
        combDistributionTranslation b (hermiteScaleDistribution q T) v‖ ≤ B * A * |a-b| * ‖T‖ := by
  obtain ⟨B,hB,hbound⟩ := exists_native_phase_pairing_error_bound q H S hH hS
  obtain ⟨C,hC,hpiece⟩ := exists_piece_finite_derivative_bound ζ (2*q+1)
  refine ⟨B*C,mul_pos hB hC,fun f hs A hA hf a b ha hb T => ?_⟩
  have hvs : tsupport (SchwartzMap.smulLeftCLM ℂ ζ f) ⊆ Icc (-H) H := by
    have he : (SchwartzMap.smulLeftCLM ℂ ζ f : ℝ → ℂ) = (ζ : ℝ → ℂ) • (f : ℝ → ℂ) := by
      ext x
      exact SchwartzMap.smulLeftCLM_apply_apply ζ.hasTemperateGrowth f x
    rw [he]
    exact (tsupport_smul_subset_right (ζ : ℝ → ℂ) (f : ℝ → ℂ)).trans hs
  have he := hbound _ hvs (C*A) (mul_nonneg hC.le hA) (hpiece f A hA hf) a b ha hb T
  simpa only [mul_assoc] using he

/-- One source-independent constant handles the whole actual finite partition at the
fixed input regularity Kp; q may be any output order at most Qp. -/
theorem exists_partition_phase_pairing_error_bound (p q N : ℕ) (hq : q ≤ liftOrder p)
    (ζ : Fin N → SchwartzMap ℝ ℂ) (H S : ℝ) (hH : 0 ≤ H) (hS : 0 ≤ S) :
    ∃ B : ℝ, 0 < B ∧ ∀ i, ∀ f : SchwartzMap ℝ ℂ,
      tsupport f ⊆ Icc (-H) H → ∀ A : ℝ, 0 ≤ A →
      (∀ r ≤ testOrder p, ∀ x, ‖iteratedDeriv r (f : ℝ → ℂ) x‖ ≤ A) →
      ∀ a b : ℝ, |a| ≤ S → |b| ≤ S → ∀ T : HermiteScale (-(q : ℤ)),
      let v := SchwartzMap.smulLeftCLM ℂ (ζ i) f
      ‖combDistributionTranslation a (hermiteScaleDistribution q T) v -
        combDistributionTranslation b (hermiteScaleDistribution q T) v‖ ≤ B * A * |a-b| * ‖T‖ := by
  classical
  choose C hC hbound using fun i => exists_piece_phase_pairing_error_bound q (ζ i) H S hH hS
  have hCsum : 0 ≤ ∑ i, C i := Finset.sum_nonneg (fun i _ => (hC i).le)
  refine ⟨1+∑ i, C i,by positivity,fun i f hs A hA hf a b ha hb T => ?_⟩
  have hr : 2*q+1 ≤ testOrder p := by unfold testOrder; omega
  have he := hbound i f hs A hA (fun r hr' => hf r (hr'.trans hr)) a b ha hb T
  apply he.trans
  gcongr
  exact (Finset.single_le_sum (fun j _ => (hC j).le) (Finset.mem_univ i)).trans (by linarith)

/-- The phase error summed over every partition piece and label still uses exactly
Kp test derivatives and the original coefficient norms. -/
theorem exists_partition_sum_phase_error_bound (p q N L : ℕ) (hq : q ≤ liftOrder p)
    (ζ : Fin N → SchwartzMap ℝ ℂ) (H S : ℝ) (hH : 0 ≤ H) (hS : 0 ≤ S) :
    ∃ B : ℝ, 0 < B ∧ ∀ f : SchwartzMap ℝ ℂ,
      tsupport f ⊆ Icc (-H) H → ∀ A : ℝ, 0 ≤ A →
      (∀ r ≤ testOrder p, ∀ x, ‖iteratedDeriv r (f : ℝ → ℂ) x‖ ≤ A) →
      ∀ η : ℝ, 0 ≤ η → ∀ a b : Fin N → Fin L → ℝ,
      (∀ i j, |a i j| ≤ S) → (∀ i j, |b i j| ≤ S) →
      (∀ i j, |a i j-b i j| ≤ η) → ∀ T : Fin L → HermiteScale (-(q : ℤ)),
      ‖∑ i, ∑ j,
        (combDistributionTranslation (a i j) (hermiteScaleDistribution q (T j))
          (SchwartzMap.smulLeftCLM ℂ (ζ i) f) -
        combDistributionTranslation (b i j) (hermiteScaleDistribution q (T j))
          (SchwartzMap.smulLeftCLM ℂ (ζ i) f))‖ ≤ B * A * η * ∑ j, ‖T j‖ := by
  obtain ⟨C,hC,hbound⟩ := exists_partition_phase_pairing_error_bound p q N hq ζ H S hH hS
  refine ⟨((N : ℝ)+1)*C,by positivity,fun f hs A hA hf η hη a b ha hb hab T => ?_⟩
  have hpoint i j :
      ‖combDistributionTranslation (a i j) (hermiteScaleDistribution q (T j))
          (SchwartzMap.smulLeftCLM ℂ (ζ i) f) -
        combDistributionTranslation (b i j) (hermiteScaleDistribution q (T j))
          (SchwartzMap.smulLeftCLM ℂ (ζ i) f)‖ ≤ C * A * η * ‖T j‖ := by
    apply (hbound i f hs A hA hf _ _ (ha i j) (hb i j) (T j)).trans
    gcongr
    exact hab i j
  calc
    _ ≤ ∑ i, ∑ j, C * A * η * ‖T j‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro i _
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ => hpoint i j))
    _ = (N : ℝ)*(C*A*η*(∑ j, ‖T j‖)) := by
      simp only [← Finset.mul_sum,Finset.sum_const,
        Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      ring
    _ ≤ (((N : ℝ)+1)*C)*A*η*(∑ j, ‖T j‖) := by
      have hsum : 0 ≤ ∑ j, ‖T j‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
      nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hC.le hA) hη) hsum]

end
end MeyerGeneralProblem.Adaptive
