module

public import MeyerGeneralProblem.Cardinal.Adaptive.StageJetIsolation

@[expose] public section

/-! # Exact value-only readings of the original source by shrinking jet probes -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open Filter
open scoped Topology

/-- The original source mass at an arbitrary real point, extended by zero off
its actual locally finite carrier. -/
def originalPointMass (S : LocallyFiniteCarrier) (U : TemperedDistribution ℝ ℂ) (a : ℝ) : ℂ :=
  by
  classical
  exact if h : a ∈ S.carrier then U (S.isolationSchwartz ⟨a,h⟩) else 0

/-- An atomic source reads only the actual mass if a test vanishes at every
other carrier point. This is a whole Schwartz identity. -/
theorem atomic_pairing_single_point (S : LocallyFiniteCarrier) (U : TemperedDistribution ℝ ℂ)
    (hU : AtomicOnCarrier S U) (a : ℝ) (f : SchwartzMap ℝ ℂ)
    (hf : ∀ x ∈ S.carrier, x ≠ a → f x=0) :
    U f = originalPointMass S U a * f a := by
  classical
  by_cases ha : a ∈ S.carrier
  · have hz := hU (f-f a • S.isolationSchwartz ⟨a,ha⟩) (by
      intro x hx
      simp only [_root_.sub_apply,smul_apply,smul_eq_mul]
      by_cases he : x=a
      · subst x
        rw [S.isolationSchwartz_self,mul_one,sub_self]
      · rw [hf x hx he,S.isolationSchwartz_of_mem_of_ne _ hx he,mul_zero,sub_self])
    rw [map_sub,map_smul,smul_eq_mul] at hz
    rw [originalPointMass,dite_eq_left ha]
    exact (sub_eq_zero.mp hz).trans (mul_comm _ _)
  · rw [originalPointMass,dite_eq_right ha,zero_mul]
    exact hU f (fun x hx => hf x hx (fun he => ha (he ▸ hx)))

/-- Local finiteness supplies a positive isolation radius at any point, including
points absent from the carrier. -/
theorem exists_point_carrier_gap (S : LocallyFiniteCarrier) (a : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ S.carrier, x ≠ a → δ ≤ |x-a| := by
  by_cases ha : a ∈ S.carrier
  · refine ⟨S.isolationRadius ⟨a,ha⟩,S.isolationRadius_pos _,?_⟩
    intro x hx hxa
    simpa only [Real.dist_eq] using S.isolationRadius_le_dist ⟨a,ha⟩ hx hxa
  · obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp (S.carrier_isClosed.isOpen_compl.mem_nhds ha)
    refine ⟨δ,hδ,fun x hx _ => ?_⟩
    apply le_of_not_gt
    intro h
    exact hball (by simpa only [Metric.mem_ball,Real.dist_eq] using h) hx

/-- A normalized probe reads the actual value mass for order zero and exactly
zero for every positive jet order, once it fits the original carrier gap. -/
theorem atomic_fixedJetProbe_reading (S : LocallyFiniteCarrier) (U : TemperedDistribution ℝ ℂ)
    (hU : AtomicOnCarrier S U) (a δ : ℝ) (hδ : 0 < δ)
    (hgap : ∀ x ∈ S.carrier, x ≠ a → δ/2 ≤ |x-a|) (r : ℕ) :
    U (localJetProbe fixedProbeTemplate δ hδ r a) = if r=0 then originalPointMass S U a else 0 := by
  rw [atomic_pairing_single_point S U hU a _ (by
    intro x hx hxa
    rw [localJetProbe_apply]
    have hz : fixedProbeTemplate ((x-a)/δ) = 0 := by
      apply fixedProbeTemplate_eq_zero
      rw [abs_div,abs_of_pos hδ]
      apply (le_div_iff₀ hδ).mpr
      have h := hgap x hx hxa
      linarith
    rw [hz,mul_zero])]
  have hval := localJetProbe_derivative_center fixedProbeTemplate fixedProbeTemplate_eventually_one δ hδ r 0 a
  simp only [iteratedDeriv_zero] at hval
  rw [hval]
  by_cases hr : r=0
  · simp [hr]
  · simp [hr,Ne.symm hr]

/-- The actual predetermined stage probes eventually read the original source's
mass or zero derivative, at every fixed real point and every jet order. -/
theorem atomic_actualStage_probe_eventually (S : LocallyFiniteCarrier) (U : TemperedDistribution ℝ ℂ)
    (hU : AtomicOnCarrier S U) (a : ℝ) (r : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      U (localJetProbe fixedProbeTemplate (actualStage fixedProbeTemplate n).jetRadius
        (actualStage fixedProbeTemplate n).jetRadius_pos r a) =
          if r=0 then originalPointMass S U a else 0 := by
  obtain ⟨δ,hδ,hgap⟩ := exists_point_carrier_gap S a
  filter_upwards [actualStage_jetRadius_eventually_le fixedProbeTemplate δ hδ] with n hn
  apply atomic_fixedJetProbe_reading S U hU a _ _ (fun x hx hxa => ?_) r
  have hh := hgap x hx hxa
  have hp := (actualStage fixedProbeTemplate n).jetRadius_pos
  linarith

end
end MeyerGeneralProblem.Adaptive
