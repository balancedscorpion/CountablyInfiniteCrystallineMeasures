module

public import MeyerGeneralProblem.Cardinal.Adaptive.FinitePhaseDescent

@[expose] public section

/-! # Fixed-order stage limits for actual top-coefficient support -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open Set Filter
open scoped Topology FourierTransform

/-- The literal stage dyadic error tends to zero. -/
theorem tendsto_stage_dyadic_zero :
    Tendsto (fun n : ℕ => (2:ℝ)^(-((n+1:ℕ):ℤ))) atTop (𝓝 0) := by
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 2⁻¹)
    (by norm_num : (2:ℝ)⁻¹ < 1)).comp (tendsto_add_atTop_nat 1)
  simpa only [Function.comp_def,inv_pow,← zpow_neg_coe_of_pos (2:ℝ) (Nat.succ_pos _)] using ht

/-- A fixed pairing bounded by an eventually vanishing dyadic budget is zero. -/
theorem eq_zero_of_eventually_norm_le_stage_dyadic (z : ℂ) (B : ℝ)
    (hz : ∀ᶠ n : ℕ in atTop, ‖z‖ ≤ (2:ℝ)^(-((n+1:ℕ):ℤ))*B) : z=0 := by
  have ht : Tendsto (fun n : ℕ => (2:ℝ)^(-((n+1:ℕ):ℤ))*B) atTop (𝓝 0) := by
    simpa only [zero_mul] using tendsto_stage_dyadic_zero.mul_const B
  exact norm_eq_zero.mp (le_antisymm (ge_of_tendsto ht hz) (norm_nonneg z))

/-- The actual selected phase tolerances tend to zero by their deterministic cap. -/
theorem tendsto_actualStage_phaseTolerance_zero (ψ : SchwartzMap ℝ ℂ) :
    Tendsto (fun n => (actualStage ψ n).phaseTolerance) atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ => 1/(n+1:ℝ)) atTop (𝓝 0) := by
    have hn : Tendsto (fun n : ℕ => (n:ℝ)+1) atTop atTop := by
      have hn := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop).comp (tendsto_add_atTop_nat 1)
      simpa only [Function.comp_def,Nat.cast_add,Nat.cast_one] using hn
    simpa only [Function.comp_def,one_div] using tendsto_inv_atTop_zero.comp hn
  apply squeeze_zero (fun n => (actualStage ψ n).phaseTolerance_pos.le) _ ht
  intro n
  simpa only [PNat.mk_coe,Nat.cast_add,Nat.cast_one] using (actualStage_laws ψ n).phase_stage

/-- Every compact test fits a fixed natural symmetric window. -/
theorem exists_nat_compact_test_window (f : SchwartzMap ℝ ℂ) (hf : HasCompactSupport f) :
    ∃ N : ℕ, tsupport f ⊆ Icc (-(N:ℝ)) (N:ℝ) := by
  obtain ⟨R,hR⟩ := (Metric.isBounded_iff_subset_ball (0:ℝ)).mp hf.isBounded
  obtain ⟨N,hN⟩ := exists_nat_gt R
  refine ⟨N,fun x hx => abs_le.mp ?_⟩
  have hxR : |x| < R := by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using hR hx
  exact (hxR.trans hN).le

/-- Uniformly bounded whole coefficients and actual finite splits give zero top
pairing for every normalized compact test outside its own physical closure. -/
theorem top_coefficient_pairing_zero_normalized (ψ : SchwartzMap ℝ ℂ) (s : ℕ+ → ℝ)
    (hs : ActualGoodScale ψ s) (p D : ℕ) (hD : D ≤ 12*p)
    (V : Label → Fin (D+1) → HermiteScale (-((liftOrder p):ℤ)))
    (hV : ∀ b r, combDistributionTranslation (labelScale s b)⁻¹
      (hermiteScaleDistribution (liftOrder p) (V b r)) = -hermiteScaleDistribution (liftOrder p) (V b r))
    (B : ℝ) (hB : 0 ≤ B) (hnorm : ∀ b r, ‖V b r‖ ≤ B)
    (pieces : Label → TemperedDistribution ℝ ℂ) (T : TemperedDistribution ℝ ℂ)
    (future : ℕ → HermiteScale (-((6*p:ℕ):ℤ))) (BF : ℝ) (hBF : ∀ n, ‖future n‖ ≤ BF)
    (hfuture : ∀ n, DistributionSupportedOn {x : ℝ | (actualGaps ψ (n+1):ℝ)/3 < |x|}
      (𝓕 (hermiteScaleDistribution (6*p) (future n))))
    (hsplit : ∀ n, (∑ b : Fin (n+1) × ReciprocalSign, pieces (prefixScaleIndex b.1,b.2)) +
      hermiteScaleDistribution (6*p) (future n) = T)
    (hlocal : ∀ b : Label, DistributionVanishesOn (physicalPeriodicSet (actualPositiveGaps ψ) s b)ᶜ
      (pieces b-∑ r, monomialDistribution r.val (hermiteScaleDistribution (liftOrder p) (V b r))))
    (L : LocallyFiniteCarrier) (hL : L.carrier ⊆ carrierSet (actualPositiveGaps ψ) s)
    (hT : AtomicOnCarrier L T) (target : Label) (f : SchwartzMap ℝ ℂ)
    (hfc : HasCompactSupport f) (hf : tsupport f ⊆ (physicalPeriodicSet (actualPositiveGaps ψ) s target)ᶜ)
    (hfA : ∀ r ≤ testOrder p, ∀ x, ‖iteratedDeriv r (f : ℝ → ℂ) x‖ ≤ 1) :
    hermiteScaleDistribution (liftOrder p) (V target ⟨D,Nat.lt_succ_self D⟩) f = 0 := by
  obtain ⟨δ,hδ,hmargin⟩ := compact_test_avoidance_margin _
    (physicalPeriodicSet_isClosed _ s (actualPositiveGaps_pos ψ) hs.1.1 target) f hfc hf
  obtain ⟨N,hN⟩ := exists_nat_compact_test_window f hfc
  apply eq_zero_of_eventually_norm_le_stage_dyadic _ (2*B+BF)
  filter_upwards [eventually_ge_atTop (max N (max p target.1.val)),
    (tendsto_actualStage_phaseTolerance_zero ψ).eventually_lt_const hδ] with n hn heta
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hnp : p ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hnt : target.1.val ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  let i : Fin (n+1) := ⟨target.1.val-1,by have := target.1.pos; omega⟩
  have hi : prefixScaleIndex i = target.1 := by
    apply Subtype.ext
    change target.1.val-1+1=target.1.val
    have := target.1.pos
    omega
  have hwindow : tsupport f ⊆ Icc (-(n+1:ℝ)) (n+1:ℝ) := by
    intro x hx
    have hxN := hN hx
    have hreal : (N:ℝ) ≤ n := by exact_mod_cast hnN
    constructor <;> linarith [hxN.1,hxN.2]
  have hstage := actualStage_top_coefficient_pairing_bound ψ s hs n p D (by omega) hD
    (fun b => V (prefixScaleIndex b.1,b.2)) (fun b r => hV _ r) B hB (fun b r => hnorm _ r)
    (fun b => pieces (prefixScaleIndex b.1,b.2)) T (future n) (hfuture n) (hsplit n)
    (fun b => hlocal _) L hL hT (i,target.2) f hwindow hfA δ heta.le
    (by simpa only [hi] using hmargin)
  have ht : hermiteScaleDistribution (liftOrder p) (V (prefixScaleIndex i,target.2) ⟨D,Nat.lt_succ_self D⟩) f =
      hermiteScaleDistribution (liftOrder p) (V target ⟨D,Nat.lt_succ_self D⟩) f := by rw [hi]
  rw [ht] at hstage
  exact hstage.trans (mul_le_mul_of_nonneg_left (by linarith [hBF n]) (by positivity))

/-- Any fixed finite derivative class can be normalized by a nonzero scalar. -/
theorem exists_unit_derivative_rescaling (f : SchwartzMap ℝ ℂ) (K : ℕ) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ r ≤ K, ∀ x, ‖iteratedDeriv r ((c • f : SchwartzMap ℝ ℂ) : ℝ → ℂ) x‖ ≤ 1 := by
  obtain ⟨A,hA,hder⟩ := finite_schwartz_derivative_bound (fun _ : Fin 1 => f) K
  refine ⟨((A⁻¹:ℝ):ℂ),by exact_mod_cast inv_ne_zero hA.ne',?_⟩
  intro r hr x
  change ‖iteratedDeriv r (((A⁻¹:ℝ):ℂ) • (f : ℝ → ℂ)) x‖ ≤ 1
  rw [iteratedDeriv_const_smul_field,norm_smul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hA)]
  calc
    _ ≤ A⁻¹*A := mul_le_mul_of_nonneg_left (hder 0 r hr x) (inv_pos.mpr hA).le
    _ = 1 := inv_mul_cancel₀ hA.ne'

/-- Testing against the normalized fixed derivative class suffices for literal
local distributional vanishing. This rescales each test, not the stage choices. -/
theorem distributionVanishesOn_of_unit_derivative_tests (O : Set ℝ) (K : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : ∀ f : SchwartzMap ℝ ℂ, HasCompactSupport f → tsupport f ⊆ O →
      (∀ r ≤ K, ∀ x, ‖iteratedDeriv r (f : ℝ → ℂ) x‖ ≤ 1) → T f = 0) :
    DistributionVanishesOn O T := by
  intro f hfc hf
  obtain ⟨c,hc,hder⟩ := exists_unit_derivative_rescaling f K
  have hsupport : tsupport (c • f : SchwartzMap ℝ ℂ) ⊆ tsupport f :=
    tsupport_smul_subset_right (fun _ : ℝ => c) (f : ℝ → ℂ)
  have hcompact : HasCompactSupport (c • f : SchwartzMap ℝ ℂ) :=
    hfc.of_isClosed_subset (isClosed_tsupport _) hsupport
  have hzero := hT (c • f) hcompact (hsupport.trans hf) hder
  rw [map_smul] at hzero
  exact (smul_eq_zero.mp hzero).resolve_left hc

/-- The top whole coefficient is supported on its own actual physical closure,
under the literal finite splitting and local lift conclusions at fixed order. -/
theorem top_coefficient_vanishesOffClosure (ψ : SchwartzMap ℝ ℂ) (s : ℕ+ → ℝ)
    (hs : ActualGoodScale ψ s) (p D : ℕ) (hD : D ≤ 12*p)
    (V : Label → Fin (D+1) → HermiteScale (-((liftOrder p):ℤ)))
    (hV : ∀ b r, combDistributionTranslation (labelScale s b)⁻¹
      (hermiteScaleDistribution (liftOrder p) (V b r)) = -hermiteScaleDistribution (liftOrder p) (V b r))
    (B : ℝ) (hB : 0 ≤ B) (hnorm : ∀ b r, ‖V b r‖ ≤ B)
    (pieces : Label → TemperedDistribution ℝ ℂ) (T : TemperedDistribution ℝ ℂ)
    (future : ℕ → HermiteScale (-((6*p:ℕ):ℤ))) (BF : ℝ) (hBF : ∀ n, ‖future n‖ ≤ BF)
    (hfuture : ∀ n, DistributionSupportedOn {x : ℝ | (actualGaps ψ (n+1):ℝ)/3 < |x|}
      (𝓕 (hermiteScaleDistribution (6*p) (future n))))
    (hsplit : ∀ n, (∑ b : Fin (n+1) × ReciprocalSign, pieces (prefixScaleIndex b.1,b.2)) +
      hermiteScaleDistribution (6*p) (future n) = T)
    (hlocal : ∀ b : Label, DistributionVanishesOn (physicalPeriodicSet (actualPositiveGaps ψ) s b)ᶜ
      (pieces b-∑ r, monomialDistribution r.val (hermiteScaleDistribution (liftOrder p) (V b r))))
    (L : LocallyFiniteCarrier) (hL : L.carrier ⊆ carrierSet (actualPositiveGaps ψ) s)
    (hT : AtomicOnCarrier L T) (target : Label) :
    DistributionVanishesOn (physicalPeriodicSet (actualPositiveGaps ψ) s target)ᶜ
      (hermiteScaleDistribution (liftOrder p) (V target ⟨D,Nat.lt_succ_self D⟩)) := by
  apply distributionVanishesOn_of_unit_derivative_tests _ (testOrder p)
  intro f hfc hf hfA
  exact top_coefficient_pairing_zero_normalized ψ s hs p D hD V hV B hB hnorm pieces T future BF hBF
    hfuture hsplit hlocal L hL hT target f hfc hf hfA

end
end MeyerGeneralProblem.Adaptive
