module

public import MeyerGeneralProblem.Cardinal.Adaptive.NativeDiscreteJets
public import MeyerGeneralProblem.Cardinal.Adaptive.PeriodicDescent
public import Mathlib.Geometry.Manifold.PartitionOfUnity
import all Mathlib.Geometry.Manifold.PartitionOfUnity

@[expose] public section

/-! # Compact-test locality for whole tempered distributions -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open Set
open scoped Manifold ContDiff Topology

set_option maxHeartbeats 800000 in
/-- Local vanishing on a neighborhood of each point of a compact test's support
implies vanishing on the whole test, by an actual finite smooth partition. -/
theorem distribution_eq_zero_of_local_vanishing (U : TemperedDistribution ℝ ℂ)
    (f : SchwartzMap ℝ ℂ) (hf : HasCompactSupport (f : ℝ → ℂ))
    (hlocal : ∀ x ∈ tsupport f, ∃ O : Set ℝ, IsOpen O ∧ x ∈ O ∧ DistributionVanishesOn O U) :
    U f = 0 := by
  classical
  choose O hopen hmem hzero using (fun x : tsupport f => hlocal x x.property)
  let V : tsupport f → Set ℝ := fun x => O x ∩ Metric.ball x.val 1
  have hVopen x : IsOpen (V x) := (hopen x).inter Metric.isOpen_ball
  have hcover : tsupport f ⊆ ⋃ x : tsupport f, V x := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x,hx⟩,hmem _,Metric.mem_ball_self zero_lt_one⟩
  obtain ⟨F,hF⟩ := hf.elim_finite_subcover V hVopen hcover
  have hcoverF : tsupport f ⊆ ⋃ i : F, V i.val := by
    intro x hx
    have h := hF hx
    simp only [mem_iUnion] at h ⊢
    obtain ⟨i,hi,hxi⟩ := h
    exact ⟨⟨i,hi⟩,hxi⟩
  obtain ⟨ζ,hζ⟩ := SmoothPartitionOfUnity.exists_isSubordinate (I := 𝓘(ℝ,ℝ))
    (isClosed_tsupport _) (fun i : F => V i.val) (fun i => hVopen i.val) hcoverF
  have hcompact (i : F) : HasCompactSupport (ζ i) :=
    (isCompact_closedBall i.val.val 1).of_isClosed_subset (isClosed_tsupport _)
      ((hζ i).trans (inter_subset_right.trans Metric.ball_subset_closedBall))
  have hsmooth (i : F) : ContDiff ℝ ∞ (ζ i) := contMDiff_iff_contDiff.mp (ζ i).contMDiff
  let q : F → SchwartzMap ℝ ℂ := fun i =>
    ((hcompact i).comp_left (show Complex.ofRealCLM (0:ℝ)=0 from rfl)).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp (hsmooth i))
  have hqval (i : F) (x : ℝ) : q i x = (ζ i x : ℂ) := rfl
  have hqsupport (i : F) : tsupport (q i) ⊆ O i.val := by
    change tsupport (Complex.ofRealCLM ∘ ζ i) ⊆ O i.val
    exact (tsupport_comp_subset rfl _).trans ((hζ i).trans inter_subset_left)
  let g : F → SchwartzMap ℝ ℂ := fun i => SchwartzMap.smulLeftCLM ℂ (q i) f
  have hgcompact (i : F) : HasCompactSupport (g i : ℝ → ℂ) := by
    convert! hf.mul_left (f := fun x => q i x) using 1
    ext x
    simp only [g,SchwartzMap.smulLeftCLM_apply_apply (q i).hasTemperateGrowth,smul_eq_mul,Pi.mul_apply]
  have hgsupport (i : F) : tsupport (g i) ⊆ O i.val := by
    apply (closure_mono (show Function.support (g i) ⊆ Function.support (q i) from ?_)).trans
      (hqsupport i)
    · intro x hx
      contrapose! hx
      simp only [Function.mem_support,not_not] at hx ⊢
      simp only [g,SchwartzMap.smulLeftCLM_apply_apply (q i).hasTemperateGrowth,hx,zero_smul]
  have he : ∑ i, g i = f := by
    ext x
    simp only [_root_.sum_apply,g,SchwartzMap.smulLeftCLM_apply_apply (q _).hasTemperateGrowth,
      smul_eq_mul,← Finset.sum_mul,hqval,← Complex.ofReal_sum]
    by_cases hx : f x=0
    · simp [hx]
    · have h1 := ζ.sum_eq_one (subset_tsupport f hx)
      rw [finsum_eq_sum_of_fintype] at h1
      rw [h1,Complex.ofReal_one,one_mul]
  rw [← he,map_sum]
  exact Finset.sum_eq_zero fun i _ => hzero i.val _ (hgcompact i) (hgsupport i)

/-- Pointwise local vanishing off a set proves ordinary distributional support
on that set, including when the original carrier has accumulation points. -/
theorem supportedOn_of_local_vanishing (C : Set ℝ) (U : TemperedDistribution ℝ ℂ)
    (hlocal : ∀ x ∉ C, ∃ O : Set ℝ, IsOpen O ∧ x ∈ O ∧ DistributionVanishesOn O U) :
    DistributionSupportedOn C U := by
  intro f hf hz
  apply distribution_eq_zero_of_local_vanishing U f hf
  intro x hx
  apply hlocal x
  intro hxc
  exact (notMem_tsupport_iff_eventuallyEq.mpr (hz x hxc)) hx

end
end MeyerGeneralProblem.Adaptive
