module

public import MeyerGeneralProblem.Cardinal.Adaptive.FiniteClosureSeparation
public import Mathlib.Geometry.Manifold.PartitionOfUnity
import all Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import all Mathlib.Analysis.Distribution.SchwartzSpace.Basic

@[expose] public section

/-!
# Actual finite compact Schwartz partitions

A deterministic compact interval and a positive piece scale produce a finite
smooth partition. All functions are complex Schwartz maps with real nonnegative
values, compact supports in the padded interval, and strictly small diameters.
-/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open Set
open scoped Manifold ContDiff

set_option maxHeartbeats 800000 in
/-- A deterministic finite compact Schwartz partition with exact support, sum and diameter laws. -/
theorem exists_finite_schwartz_partition (M ρ : ℝ) (hρ : 0 < ρ) :
    ∃ N : ℕ, ∃ ζ : Fin N → SchwartzMap ℝ ℂ,
      (∀ i, HasCompactSupport (ζ i)) ∧
      (∀ i, tsupport (ζ i) ⊆ Icc (-M-1) (M+1)) ∧
      (∀ i, ∀ x ∈ tsupport (ζ i), ∀ y ∈ tsupport (ζ i), |x-y| < ρ) ∧
      (∀ x ∈ Icc (-M) M, ∑ i, ζ i x = 1) ∧
      (∀ i x, (ζ i x).im = 0 ∧ 0 ≤ (ζ i x).re) ∧
      (∀ x, ∑ i, (ζ i x).re ≤ 1) := by
  classical
  let δ : ℝ := min (ρ/4) (1/2)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδρ : δ ≤ ρ/4 := min_le_left _ _
  have hδ1 : δ ≤ 1/2 := min_le_right _ _
  let U : Icc (-M) M → Set ℝ := fun x => Metric.ball x.val δ
  have hcover : Icc (-M) M ⊆ ⋃ x : Icc (-M) M, U x := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x,hx⟩, Metric.mem_ball_self hδ⟩
  obtain ⟨F,hF⟩ := isCompact_Icc.elim_finite_subcover U (fun _ => Metric.isOpen_ball) hcover
  have hcoverF : Icc (-M) M ⊆ ⋃ i : F, U i.val := by
    intro x hx
    have h := hF hx
    simp only [mem_iUnion] at h ⊢
    obtain ⟨i,hi,hxi⟩ := h
    exact ⟨⟨i,hi⟩,hxi⟩
  obtain ⟨f,hf⟩ := SmoothPartitionOfUnity.exists_isSubordinate (I := 𝓘(ℝ,ℝ))
    isClosed_Icc (fun i : F => U i.val) (fun _ => Metric.isOpen_ball) hcoverF
  have hcompact (i : F) : HasCompactSupport (f i) :=
    (isCompact_closedBall i.val.val δ).of_isClosed_subset (isClosed_tsupport (f i))
      ((hf i).trans Metric.ball_subset_closedBall)
  have hsmooth (i : F) : ContDiff ℝ ∞ (f i) := contMDiff_iff_contDiff.mp (f i).contMDiff
  let q : F → SchwartzMap ℝ ℂ := fun i =>
    ((hcompact i).comp_left (show Complex.ofRealCLM (0 : ℝ) = 0 from rfl)).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp (hsmooth i))
  have hqval (i : F) (x : ℝ) : q i x = (f i x : ℂ) := rfl
  have hqcompact (i : F) : HasCompactSupport (q i) := by
    change HasCompactSupport (Complex.ofRealCLM ∘ f i)
    exact (hcompact i).comp_left rfl
  have hqsupport (i : F) : tsupport (q i) ⊆ U i.val := by
    change tsupport (Complex.ofRealCLM ∘ f i) ⊆ U i.val
    exact (tsupport_comp_subset rfl _).trans (hf i)
  let e : Fin (Fintype.card F) ≃ F := (Fintype.equivFin F).symm
  refine ⟨Fintype.card F,fun i => q (e i),?_,?_,?_,?_,?_,?_⟩
  · exact fun i => hqcompact (e i)
  · intro i x hx
    have hxi : |x-(e i).val.val| < δ := by
      simpa only [U, Metric.mem_ball, Real.dist_eq] using hqsupport (e i) hx
    have hc := (e i).val.property
    have hbounds := abs_lt.mp hxi
    constructor <;> linarith [hc.1,hc.2]
  · intro i x hx y hy
    have hx' : |x-(e i).val.val| < δ := by
      simpa only [U, Metric.mem_ball, Real.dist_eq] using hqsupport (e i) hx
    have hy' : |(e i).val.val-y| < δ := by
      simpa only [U, Metric.mem_ball, Real.dist_eq, abs_sub_comm] using hqsupport (e i) hy
    have htri := abs_sub_le x (e i).val.val y
    linarith
  · intro x hx
    change (∑ i, q (e i) x) = 1
    rw [e.sum_comp (fun i => q i x)]
    simp only [hqval, ← Complex.ofReal_sum]
    have hf1 := f.sum_eq_one hx
    rw [finsum_eq_sum_of_fintype] at hf1
    rw [hf1]
    rfl
  · intro i x
    rw [hqval]
    exact ⟨rfl,f.nonneg _ _⟩
  · intro x
    change (∑ i, (q (e i) x).re) ≤ 1
    rw [e.sum_comp (fun i => (q i x).re)]
    simp only [hqval, Complex.ofReal_re]
    have h := f.sum_le_one x
    rwa [finsum_eq_sum_of_fintype] at h

/-- Every finite Schwartz family has a common positive bound through a fixed derivative order. -/
theorem finite_schwartz_derivative_bound {N : ℕ} (ζ : Fin N → SchwartzMap ℝ ℂ) (r : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ i n, n ≤ r → ∀ x, ‖iteratedDeriv n (ζ i) x‖ ≤ C := by
  classical
  let A : Fin N → ℝ := fun i => ∑ n ∈ Finset.range (r+1), SchwartzMap.seminorm ℝ 0 n (ζ i)
  have hA i : 0 ≤ A i := Finset.sum_nonneg (fun n _ => apply_nonneg _ _)
  refine ⟨1 + ∑ i, A i, by positivity, ?_⟩
  intro i n hn x
  have h₁ : ‖iteratedDeriv n (ζ i) x‖ ≤ SchwartzMap.seminorm ℝ 0 n (ζ i) := by
    simpa only [pow_zero, one_mul] using SchwartzMap.le_seminorm' ℝ 0 n (ζ i) x
  have h₂ : SchwartzMap.seminorm ℝ 0 n (ζ i) ≤ A i :=
    Finset.single_le_sum (fun j _ => apply_nonneg _ _) (Finset.mem_range.mpr (by omega))
  have h₃ : A i ≤ ∑ j, A j := Finset.single_le_sum (fun j _ => hA j) (Finset.mem_univ i)
  linarith

/-- A small supported partition piece has at most one local periodic-closure label. -/
theorem schwartz_piece_meets_at_most_one_closure (M ρ γ : ℝ) (hργ : ρ ≤ γ)
    (R : ℕ+ → ℕ) (F : Finset Label) (s : ℕ+ → ℝ)
    (hgood : s ∉ finitePeriodicCloseEvent R F (M+2) γ) (ζ : SchwartzMap ℝ ℂ)
    (hsupport : tsupport ζ ⊆ Icc (-M-1) (M+1))
    (hsmall : ∀ x ∈ tsupport ζ, ∀ y ∈ tsupport ζ, |x-y| < ρ) :
    ∀ b ∈ F, ∀ d ∈ F, (tsupport ζ ∩ physicalPeriodicSet R s b).Nonempty →
      (tsupport ζ ∩ physicalPeriodicSet R s d).Nonempty → b = d := by
  apply small_piece_meets_at_most_one_closure R F (M+2) γ s hgood (tsupport ζ)
  · intro x hx
    have h := hsupport hx
    exact abs_le.mpr ⟨by linarith [h.1], by linarith [h.2]⟩
  · exact fun x hx y hy => (hsmall x hx y hy).trans_le hργ

end
end MeyerGeneralProblem.Adaptive
