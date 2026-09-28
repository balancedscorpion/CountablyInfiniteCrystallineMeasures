module

public import MeyerGeneralProblem.Cardinal.Adaptive.LocalJetRecovery

@[expose] public section

/-! # Isolating one whole source piece with the actual stage jet probes -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open scoped FourierTransform

/-- Each other prefix closure misses the complete support of a stage jet probe
centered on the distinguished closure. This includes every derivative order. -/
theorem actualStage_other_closure_probe_zero (s : ℕ+ → ℝ)
    (hs : ActualGoodScale fixedProbeTemplate s) (n : ℕ) (b d : Label)
    (hb : b ∈ finitePrefixLabels (n+1)) (hd : d ∈ finitePrefixLabels (n+1)) (hbd : b ≠ d)
    (y : ℝ) (hy : y ∈ physicalPeriodicSet constructedGaps s b) (hyn : |y| ≤ (n+1:ℝ))
    (U : TemperedDistribution ℝ ℂ) (hU : DistributionSupportedOn (physicalPeriodicSet constructedGaps s d) U)
    (r : ℕ) :
    U (localJetProbe fixedProbeTemplate (actualStage fixedProbeTemplate n).jetRadius
      (actualStage fixedProbeTemplate n).jetRadius_pos r y) = 0 := by
  let C := actualStage fixedProbeTemplate n
  have hδγ : C.jetRadius ≤ C.closureGap/10 := min_le_left _ _
  have hδ1 : C.jetRadius ≤ 1 := by
    have hmin : C.jetRadius ≤ 1/(((n+1:ℕ):ℝ)) := min_le_right _ _
    have hd : 1/(((n+1:ℕ):ℝ)) ≤ 1 := by
      apply (div_le_iff₀ (by positivity : (0:ℝ)<(n+1:ℕ))).mpr
      simp only [one_mul]
      exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))
    exact hmin.trans hd
  apply (supportedOn_iff_vanishesOn_compl _ _).mp hU _
    (fixedJetProbe_hasCompactSupport _ _ _ _)
  intro x hx hxd
  have hxy := fixedJetProbe_support y C.jetRadius C.jetRadius_pos r hx
  rw [Metric.mem_closedBall,Real.dist_eq] at hxy
  have hxabs : |x| ≤ (n+1:ℝ)+2 := by
    have htri := abs_add_le (x-y) y
    rw [sub_add_cancel] at htri
    linarith
  have hgap := hs.closure_separation fixedProbeTemplate s n b hb d hd hbd y hy x hxd
    (by linarith) hxabs
  rw [abs_sub_comm y x] at hgap
  have hγ := C.closureGap_pos
  change C.closureGap ≤ |x-y| at hgap
  linarith

/-- The exact finite source identity reduces a stage probe to its one selected
piece and the original future piece, before any limit or infinite sum. -/
theorem finite_split_stage_probe_identity (s : ℕ+ → ℝ)
    (hs : ActualGoodScale fixedProbeTemplate s) (n : ℕ) (b : Label)
    (hb : b ∈ finitePrefixLabels (n+1)) (y : ℝ)
    (hy : y ∈ physicalPeriodicSet constructedGaps s b) (hyn : |y| ≤ (n+1:ℝ))
    (U : Label → TemperedDistribution ℝ ℂ) (V T : TemperedDistribution ℝ ℂ)
    (hU : ∀ d ∈ finitePrefixLabels (n+1), DistributionSupportedOn (physicalPeriodicSet constructedGaps s d) (U d))
    (hsplit : (∑ d ∈ finitePrefixLabels (n+1), U d)+V=T) (r : ℕ) :
    let f := localJetProbe fixedProbeTemplate (actualStage fixedProbeTemplate n).jetRadius
      (actualStage fixedProbeTemplate n).jetRadius_pos r y
    U b f - T f = -V f := by
  classical
  dsimp only
  let f := localJetProbe fixedProbeTemplate (actualStage fixedProbeTemplate n).jetRadius
    (actualStage fixedProbeTemplate n).jetRadius_pos r y
  have he := congrArg (fun W : TemperedDistribution ℝ ℂ => W f) hsplit
  simp only [_root_.add_apply,_root_.sum_apply] at he
  have hz : (∑ d ∈ finitePrefixLabels (n+1), U d f) = U b f := by
    apply Finset.sum_eq_single b
    · intro d hd hdb
      exact actualStage_other_closure_probe_zero s hs n b d hb hd (Ne.symm hdb) y hy hyn (U d) (hU d hd) r
    · exact fun hn => False.elim (hn hb)
  rw [hz] at he
  change U b f-T f = -V f
  linear_combination he

/-- After the physical support theorem, budgetJ applies directly to the exact
constructed spectral pieces and the original source, at every admitted stage. -/
theorem actualSourcePiece_stage_probe_error (s : ℕ+ → ℝ)
    (hs : ActualGoodScale fixedProbeTemplate s) (σ : ℝ) (hσ : 0 < σ) (p n : ℕ)
    (hp : p ≤ n+1)
    (hsep : ∀ b d : Label, b ≠ d → ∀ x ∈ sectorSet constructedGaps s b,
      ∀ y ∈ sectorSet constructedGaps s d, σ/(1+|x|+|y|)^6 ≤ |x-y|)
    (L : LocallyFiniteCarrier) (hL : L.carrier ⊆ carrierSet constructedGaps s)
    (T : HermiteScale (-(p:ℤ))) (hT : AtomicOnCarrier L (𝓕 (hermiteScaleDistribution p T)))
    (hphysical : ∀ d ∈ finitePrefixLabels (n+1), DistributionSupportedOn
      (physicalPeriodicSet constructedGaps s d)
      (hermiteScaleDistribution (6*p) (nativeSourcePiece σ hσ p constructedGaps s {d} T)))
    (b : Label) (hb : b ∈ finitePrefixLabels (n+1)) (y : ℝ)
    (hy : y ∈ physicalPeriodicSet constructedGaps s b) (hyn : |y| ≤ (n+1:ℝ))
    (r : ℕ) (hr : r ≤ 12*p) :
    let f := localJetProbe fixedProbeTemplate (actualStage fixedProbeTemplate n).jetRadius
      (actualStage fixedProbeTemplate n).jetRadius_pos r y
    ‖hermiteScaleDistribution (6*p) (nativeSourcePiece σ hσ p constructedGaps s {b} T) f -
        hermiteScaleDistribution p T f‖ ≤ (2:ℝ)^(-((n+1:ℕ):ℤ))*
      ‖nativeSourcePiece σ hσ p constructedGaps s (↑(finitePrefixLabels (n+1)) : Set Label)ᶜ T‖ := by
  dsimp only
  rw [finite_split_stage_probe_identity s hs n b hb y hy hyn _ _ _ hphysical
    (nativeSourcePiece_finite_split σ hσ p constructedGaps s hsep L hL T hT _) r,norm_neg]
  apply actualStage_jet_future_pairing_bound fixedProbeTemplate n p r hp hr _
    (actualSourcePiece_future_support fixedProbeTemplate s hs σ hσ p n hsep L hL T hT) y
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg _
  linarith

end
end MeyerGeneralProblem.Adaptive
