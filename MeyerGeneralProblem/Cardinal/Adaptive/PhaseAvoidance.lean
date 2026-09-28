module

public import MeyerGeneralProblem.Cardinal.Adaptive.PrefixGeometryParameters
public import MeyerGeneralProblem.Cardinal.Adaptive.PeriodicAnnihilators
public import MeyerGeneralProblem.Cardinal.Adaptive.StagePhaseParameters
public import Mathlib.Topology.MetricSpace.Thickening
import all Mathlib.Topology.MetricSpace.Thickening

@[expose] public section

/-! # Actual support avoidance by the two physical phase choices

The finite test piece is translated into the explicit zero gap of every other
periodic closure. The distinguished label uses a compact avoidance margin.
Every period is the literal reciprocal physical scale, and all seams remain.
-/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open Set

/-- The closed support of actual Schwartz translation is the corresponding preimage. -/
theorem translated_test_tsupport (h : ℝ) (f : SchwartzMap ℝ ℂ) :
    tsupport (combSchwartzTranslation h f) = (fun x : ℝ => h+x) ⁻¹' tsupport f := by
  have he : (combSchwartzTranslation h f : ℝ → ℂ) =
      (f : ℝ → ℂ) ∘ Homeomorph.addLeft h := rfl
  rw [he,tsupport_comp_eq_preimage]
  rfl

/-- A compact test outside a closed set has a uniform positive physical phase margin. -/
theorem compact_test_avoidance_margin (C : Set ℝ) (hC : IsClosed C)
    (f : SchwartzMap ℝ ℂ) (hf : HasCompactSupport f) (hs : tsupport f ⊆ Cᶜ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ tsupport f, ∀ y : ℝ, |y-x| < δ → y ∉ C := by
  obtain ⟨δ,hδ,hsub⟩ := hf.exists_thickening_subset_open hC.isOpen_compl hs
  refine ⟨δ,hδ,fun x hx y hy => ?_⟩
  exact hsub (Metric.mem_thickening_iff.mpr ⟨x,hx,by simpa only [Real.dist_eq] using hy⟩)

/-- Every integer physical period preserves the actual complete closure. -/
theorem physicalPeriodicSet_add_period_iff (R : ℕ+ → ℕ) (s : ℕ+ → ℝ) (b : Label)
    (x : ℝ) (n : ℤ) :
    x+(n:ℝ)*(labelScale s b)⁻¹ ∈ physicalPeriodicSet R s b ↔ x ∈ physicalPeriodicSet R s b := by
  have hadd (z : ℤ) {y : ℝ} (hy : y ∈ physicalPeriodicSet R s b) :
      y+(z:ℝ)*(labelScale s b)⁻¹ ∈ physicalPeriodicSet R s b := by
    obtain ⟨a,ha,rfl⟩ := hy
    refine ⟨a+z,(periodicPhaseSet_add_int_iff b.1 (R b.1) a z).mpr ha,?_⟩
    ring
  constructor
  · intro h
    have hn := hadd (-n) h
    simpa only [Int.cast_neg,neg_mul,add_neg_cancel_right] using hn
  · exact hadd n

/-- A piece smaller than the head gap avoids a sector when its center is the
prescribed phase, including the actual integer-period error of a torus net. -/
theorem translated_small_piece_avoids_closure (R : ℕ+ → ℕ) (s : ℕ+ → ℝ)
    (hR : ∀ i, 1 ≤ R i) (hs : ∀ i, s i ∈ Icc (1:ℝ) 2) (b : Label)
    (g : SchwartzMap ℝ ℂ) (ρ η c h : ℝ) (_hρ : 0 < ρ)
    (hsmall : ∀ x ∈ tsupport g, ∀ y ∈ tsupport g, |x-y| < ρ)
    (hc : c ∈ tsupport g) (hrho : ρ < 1/(100*(headLength (R b.1):ℝ)))
    (hη : η ≤ ρ/10) (n : ℤ)
    (happrox : |h-c-(n:ℝ)*(2/labelScale s b)| < η) :
    tsupport (combSchwartzTranslation h g) ⊆ (physicalPeriodicSet R s b)ᶜ := by
  intro x hx hxC
  have hxg : h+x ∈ tsupport g := by simpa only [translated_test_tsupport,mem_preimage] using hx
  have hyC := (physicalPeriodicSet_add_period_iff R s b x (2*n)).mpr hxC
  have hk : 0 < (headLength (R b.1):ℝ) := by exact_mod_cast headLength_pos (hR b.1)
  have hgap : ρ+η < 1/(8*(headLength (R b.1):ℝ)) := by
    have hr := (lt_div_iff₀ (by positivity : (0:ℝ)<100*(headLength (R b.1):ℝ))).mp hrho
    have he := mul_le_mul_of_nonneg_right hη hk.le
    apply (lt_div_iff₀ (by positivity : (0:ℝ)<8*(headLength (R b.1):ℝ))).mpr
    nlinarith
  have hdiam := hsmall (h+x) hxg c hc
  have heq : x+((2*n:ℤ):ℝ)*(labelScale s b)⁻¹ =
      (h+x-c) - (h-c-(n:ℝ)*(2/labelScale s b)) := by
    push_cast
    simp only [div_eq_mul_inv]
    ring
  have htri := abs_sub (h+x-c) (h-c-(n:ℝ)*(2/labelScale s b))
  have hlow := physicalPeriodicSet_head_gap R s hR hs b hyC
  rw [heq] at hlow
  linarith

/-- Integer multiples of the distinguished period preserve avoidance of its own
closure; only the remaining small physical phase error uses compactness. -/
theorem translated_piece_avoids_own_closure (R : ℕ+ → ℕ) (s : ℕ+ → ℝ) (b : Label)
    (f g : SchwartzMap ℝ ℂ) (hsupport : tsupport g ⊆ tsupport f)
    (δ h : ℝ) (hmargin : ∀ x ∈ tsupport f, ∀ y : ℝ, |y-x| < δ → y ∉ physicalPeriodicSet R s b)
    (m n : ℤ) (happrox : |h-(m:ℝ)*(labelScale s b)⁻¹-(n:ℝ)*(2/labelScale s b)| < δ) :
    tsupport (combSchwartzTranslation h g) ⊆ (physicalPeriodicSet R s b)ᶜ := by
  intro x hx hxC
  have hxf : h+x ∈ tsupport f := hsupport (by simpa only [translated_test_tsupport,mem_preimage] using hx)
  have hyC := (physicalPeriodicSet_add_period_iff R s b x (m+2*n)).mpr hxC
  have heq : (x+((m+2*n:ℤ):ℝ)*(labelScale s b)⁻¹)-(h+x) =
      -(h-(m:ℝ)*(labelScale s b)⁻¹-(n:ℝ)*(2/labelScale s b)) := by
    push_cast
    simp only [div_eq_mul_inv]
    ring
  apply hmargin (h+x) hxf _ _ hyC
  rw [heq,abs_neg]
  exact happrox

/-- Each literal reciprocal physical period stays in the compact interval [1/2,2]. -/
theorem physical_period_mem_Icc (s : ℕ+ → ℝ) (hs : ∀ i, s i ∈ Icc (1:ℝ) 2) (b : Label) :
    (labelScale s b)⁻¹ ∈ Icc (1/2:ℝ) 2 := by
  have ht := labelScale_mem_Icc s hs b
  have hp : 0 < labelScale s b := by linarith [ht.1]
  constructor
  · rw [inv_eq_one_div,le_div_iff₀ hp]
    linarith [ht.2]
  · rw [inv_eq_one_div,div_le_iff₀ hp]
    linarith [ht.1]

/-- Desired physical phases: the piece center for every other label, and either
zero or one antiperiod for the distinguished label. -/
def pieceTargetPhase {M : ℕ} (s : ℕ+ → ℝ) (target : Fin M × ReciprocalSign)
    (c : ℝ) (flip : Bool) (b : Fin M × ReciprocalSign) : ℝ :=
  if b = target then (if flip then (labelScale s (prefixScaleIndex target.1,target.2))⁻¹ else 0) else c

/-- The desired phases are bounded before any torus time is chosen. -/
theorem pieceTargetPhase_abs_le {M : ℕ} (s : ℕ+ → ℝ) (hs : ∀ i, s i ∈ Icc (1:ℝ) 2)
    (target : Fin M × ReciprocalSign) (c S : ℝ) (hS : 0 ≤ S) (hc : |c| ≤ S)
    (flip : Bool) (b : Fin M × ReciprocalSign) : |pieceTargetPhase s target c flip b| ≤ S+2 := by
  unfold pieceTargetPhase
  split_ifs
  · have hp := physical_period_mem_Icc s hs (prefixScaleIndex target.1,target.2)
    rw [abs_of_pos (by linarith [hp.1])]
    linarith [hp.2]
  · simpa only [abs_zero] using (by linarith : (0:ℝ) ≤ S+2)
  · linarith

/-- One of the two actual torus phase choices yields a translated test avoiding
all first-M physical closures, with every integer phase error retained. -/
theorem exists_piece_avoiding_translation (M : ℕ) (R : ℕ+ → ℕ) (s : ℕ+ → ℝ)
    (hR : ∀ i, 1 ≤ R i) (hs : ∀ i, s i ∈ Icc (1:ℝ) 2)
    (target : Fin M × ReciprocalSign) (f g : SchwartzMap ℝ ℂ)
    (hsupport : tsupport g ⊆ tsupport f) (ρ η δ c H₀ H₁ : ℝ) (hρ : 0 < ρ) (hη : 0 < η)
    (hηρ : η ≤ ρ/10) (hηδ : η ≤ δ)
    (hsmall : ∀ x ∈ tsupport g, ∀ y ∈ tsupport g, |x-y| < ρ) (hc : c ∈ tsupport g)
    (hrho : ∀ i : Fin M, ρ < 1/(100*(headLength (R (prefixScaleIndex i)):ℝ)))
    (hmargin : ∀ x ∈ tsupport f, ∀ y : ℝ, |y-x| < δ →
      y ∉ physicalPeriodicSet R s (prefixScaleIndex target.1,target.2))
    (hnet : s ∈ prefixSegmentNetEvent M H₀ H₁ (η/4)) (flip : Bool) :
    ∃ h : ℝ, H₀ ≤ h ∧ h ≤ H₁ ∧ ∃ n : (Fin M × ReciprocalSign) → ℤ,
      (∀ b, |h-pieceTargetPhase s target c flip b-(n b:ℝ)*(2/labelScale s (prefixScaleIndex b.1,b.2))| < η) ∧
      ∀ b : Fin M × ReciprocalSign,
        tsupport (combSchwartzTranslation h g) ⊆ (physicalPeriodicSet R s (prefixScaleIndex b.1,b.2))ᶜ := by
  classical
  obtain ⟨h,hh₀,hh₁,hphase⟩ := prefix_net_supplies_physical_phases M s hs H₀ H₁ η hη hnet
    (pieceTargetPhase s target c flip)
  choose n hn using hphase
  refine ⟨h,hh₀,hh₁,n,hn,?_⟩
  intro b
  by_cases hb : b = target
  · subst b
    apply translated_piece_avoids_own_closure R s (prefixScaleIndex target.1,target.2) f g hsupport δ h hmargin
      (if flip then 1 else 0) (n target)
    have ht := (hn target).trans_le hηδ
    cases flip <;> simpa only [pieceTargetPhase,ite_true,Bool.false_eq_true,ite_false,
      Int.cast_zero,Int.cast_one,zero_mul,one_mul,sub_zero] using ht
  · apply translated_small_piece_avoids_closure R s hR hs (prefixScaleIndex b.1,b.2)
      g ρ η c h hρ hsmall hc (hrho b.1) hηρ (n b)
    simpa only [pieceTargetPhase,hb,ite_false] using hn b

/-- Empty pieces require no arbitrary support point: a zero center and the same
actual net give witnesses. Nonempty pieces choose their center inside the test window. -/
theorem exists_piece_avoiding_translation_bounded (M : ℕ) (R : ℕ+ → ℕ) (s : ℕ+ → ℝ)
    (hR : ∀ i, 1 ≤ R i) (hs : ∀ i, s i ∈ Icc (1:ℝ) 2)
    (target : Fin M × ReciprocalSign) (f g : SchwartzMap ℝ ℂ)
    (hsupport : tsupport g ⊆ tsupport f) (S : ℝ) (hS : 0 ≤ S)
    (hfS : tsupport f ⊆ Icc (-S) S) (ρ η δ H₀ H₁ : ℝ) (hρ : 0 < ρ) (hη : 0 < η)
    (hηρ : η ≤ ρ/10) (hηδ : η ≤ δ)
    (hsmall : ∀ x ∈ tsupport g, ∀ y ∈ tsupport g, |x-y| < ρ)
    (hrho : ∀ i : Fin M, ρ < 1/(100*(headLength (R (prefixScaleIndex i)):ℝ)))
    (hmargin : ∀ x ∈ tsupport f, ∀ y : ℝ, |y-x| < δ →
      y ∉ physicalPeriodicSet R s (prefixScaleIndex target.1,target.2))
    (hnet : s ∈ prefixSegmentNetEvent M H₀ H₁ (η/4)) (flip : Bool) :
    ∃ c h : ℝ, |c| ≤ S ∧ H₀ ≤ h ∧ h ≤ H₁ ∧ ∃ n : (Fin M × ReciprocalSign) → ℤ,
      (∀ b, |h-pieceTargetPhase s target c flip b-(n b:ℝ)*(2/labelScale s (prefixScaleIndex b.1,b.2))| < η) ∧
      ∀ b : Fin M × ReciprocalSign,
        tsupport (combSchwartzTranslation h g) ⊆ (physicalPeriodicSet R s (prefixScaleIndex b.1,b.2))ᶜ := by
  classical
  by_cases hg : (tsupport g).Nonempty
  · obtain ⟨c,hc⟩ := hg
    obtain ⟨h,hh₀,hh₁,n,hn,havoid⟩ := exists_piece_avoiding_translation M R s hR hs target
      f g hsupport ρ η δ c H₀ H₁ hρ hη hηρ hηδ hsmall hc hrho hmargin hnet flip
    exact ⟨c,h,abs_le.mpr (hfS (hsupport hc)),hh₀,hh₁,n,hn,havoid⟩
  · obtain ⟨h,hh₀,hh₁,hphase⟩ := prefix_net_supplies_physical_phases M s hs H₀ H₁ η hη hnet
      (pieceTargetPhase s target 0 flip)
    choose n hn using hphase
    refine ⟨0,h,by simpa only [abs_zero] using hS,hh₀,hh₁,n,hn,?_⟩
    intro b x hx
    exact (hg ⟨h+x,by simpa only [translated_test_tsupport,mem_preimage] using hx⟩).elim

/-- The integer-period reduction used by the error estimate is a bounded real
representative, and its distribution translate is exactly the original translate. -/
theorem physical_phase_representative (s : ℕ+ → ℝ) (b : Label) (U : TemperedDistribution ℝ ℂ)
    (hU : combDistributionTranslation (labelScale s b)⁻¹ U = -U)
    (h a η S : ℝ) (n : ℤ) (ha : |a| ≤ S)
    (happrox : |h-a-(n:ℝ)*(2/labelScale s b)| < η) :
    |h-(n:ℝ)*(2/labelScale s b)-a| < η ∧
    |h-(n:ℝ)*(2/labelScale s b)| ≤ S+η ∧
    combDistributionTranslation (h-(n:ℝ)*(2/labelScale s b)) U = combDistributionTranslation h U := by
  have he : h-(n:ℝ)*(2/labelScale s b)-a = h-a-(n:ℝ)*(2/labelScale s b) := by ring
  have herr : |h-(n:ℝ)*(2/labelScale s b)-a| < η := by simpa only [he] using happrox
  refine ⟨herr,?_,?_⟩
  · have htri := abs_add_le (h-(n:ℝ)*(2/labelScale s b)-a) a
    rw [sub_add_cancel] at htri
    linarith
  · convert antiperiodic_translation_sub_integer_period (labelScale s b)⁻¹ U hU h n using 1
    simp only [div_eq_mul_inv]

/-- The two literal desired-phase sums differ only in the distinguished coefficient,
which changes sign by its whole antiperiodicity. -/
theorem pieceTargetPhase_flip_identity {M : ℕ} (s : ℕ+ → ℝ)
    (target : Fin M × ReciprocalSign) (c : ℝ)
    (U : (Fin M × ReciprocalSign) → TemperedDistribution ℝ ℂ)
    (hU : combDistributionTranslation (labelScale s (prefixScaleIndex target.1,target.2))⁻¹
      (U target) = -U target) (f : SchwartzMap ℝ ℂ) :
    (∑ b, combDistributionTranslation (pieceTargetPhase s target c false b) (U b) f) -
      (∑ b, combDistributionTranslation (pieceTargetPhase s target c true b) (U b) f) = 2*U target f := by
  classical
  have hzero : combDistributionTranslation 0 (U target) f = U target f := by
    rw [combDistributionTranslation_apply]
    congr 1
    ext x
    simp only [combSchwartzTranslation_apply,zero_add]
  rw [← Finset.sum_sub_distrib,Finset.sum_eq_single target]
  · simp only [pieceTargetPhase,ite_true,Bool.false_eq_true,ite_false,hzero,hU,neg_apply]
    ring
  · intro b _ hb
    simp only [pieceTargetPhase,hb,ite_false,sub_self]
  · intro hb
    exact (hb (Finset.mem_univ _)).elim

/-- A pointwise partition of unity reconstructs the actual Schwartz test exactly. -/
theorem sum_partition_tests_eq {N : ℕ} (ζ : Fin N → SchwartzMap ℝ ℂ) (f : SchwartzMap ℝ ℂ)
    (hζ : ∀ x ∈ tsupport f, ∑ i, ζ i x = 1) :
    (∑ i, SchwartzMap.smulLeftCLM ℂ (ζ i) f) = f := by
  ext x
  simp only [sum_apply,SchwartzMap.smulLeftCLM_apply_apply (SchwartzMap.hasTemperateGrowth _),smul_eq_mul]
  by_cases hx : x ∈ tsupport f
  · rw [← Finset.sum_mul,hζ x hx,one_mul]
  · simp only [image_eq_zero_of_notMem_tsupport hx,mul_zero,Finset.sum_const_zero]

/-- Summing the two phase choices over all pieces recovers twice the original
distinguished pairing, without any infinite sum or support assumption on other labels. -/
theorem partition_phase_flip_identity {M N : ℕ} (s : ℕ+ → ℝ)
    (target : Fin M × ReciprocalSign) (c : Fin N → ℝ)
    (U : (Fin M × ReciprocalSign) → TemperedDistribution ℝ ℂ)
    (hU : combDistributionTranslation (labelScale s (prefixScaleIndex target.1,target.2))⁻¹
      (U target) = -U target) (ζ : Fin N → SchwartzMap ℝ ℂ) (f : SchwartzMap ℝ ℂ)
    (hζ : ∀ x ∈ tsupport f, ∑ i, ζ i x = 1) :
    (∑ i, ∑ b, combDistributionTranslation (pieceTargetPhase s target (c i) false b) (U b)
      (SchwartzMap.smulLeftCLM ℂ (ζ i) f)) -
      (∑ i, ∑ b, combDistributionTranslation (pieceTargetPhase s target (c i) true b) (U b)
        (SchwartzMap.smulLeftCLM ℂ (ζ i) f)) = 2*U target f := by
  rw [← Finset.sum_sub_distrib]
  simp_rw [pieceTargetPhase_flip_identity s target _ U hU]
  rw [← Finset.mul_sum,← map_sum,sum_partition_tests_eq ζ f hζ]

/-- Bounds for the two finite phase sums bound the distinguished pairing itself. -/
theorem norm_le_of_two_phase_bounds {a b z : ℂ} {ε : ℝ}
    (heq : a-b = 2*z) (ha : ‖a‖ ≤ ε) (hb : ‖b‖ ≤ ε) : ‖z‖ ≤ ε := by
  have h := (norm_sub_le a b).trans (add_le_add ha hb)
  rw [heq,norm_mul] at h
  norm_num at h
  linarith

end
end MeyerGeneralProblem.Adaptive
