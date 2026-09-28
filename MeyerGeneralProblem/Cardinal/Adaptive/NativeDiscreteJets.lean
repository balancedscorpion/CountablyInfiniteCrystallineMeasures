module

public import MeyerGeneralProblem.Cardinal.Adaptive.NativePointJets

@[expose] public section

/-! Ordinary discrete support yields actual bounded-degree native jets. -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff

/-- Ordinary support on a set, requiring neighborhood vanishing of compact tests. -/
def DistributionSupportedOn (S : Set ℝ) (U : TemperedDistribution ℝ ℂ) : Prop :=
  ∀ f : SchwartzMap ℝ ℂ, HasCompactSupport (f : ℝ → ℂ) →
    (∀ a ∈ S, (f : ℝ → ℂ) =ᶠ[𝓝 a] 0) → U f = 0

/-- A fixed Schwartz multiplier acts at the same original negative order. -/
theorem nativeMultiplier_schwartz_realizes (p : ℕ) (χ : SchwartzMap ℝ ℂ)
    (T : HermiteScale (-(p:ℤ))) :
    hermiteScaleDistribution p (nativeMultiplier p p χ T) =
      TemperedDistribution.smulLeftCLM ℂ χ (hermiteScaleDistribution p T) := by
  let A : ℝ := ∑ r ∈ Finset.range (2*p+1), SchwartzMap.seminorm ℂ 0 r χ
  apply nativeMultiplier_realizes p p 0 (by omega) A
    (Finset.sum_nonneg (fun _ _ => apply_nonneg _ _)) χ χ.hasTemperateGrowth
  intro r hr x
  simp only [pow_zero, mul_one]
  have h := χ.le_seminorm ℂ 0 r x
  simp only [pow_zero, one_mul, norm_iteratedFDeriv_eq_norm_iteratedDeriv] at h
  exact h.trans (Finset.single_le_sum (fun _ _ => apply_nonneg _ _)
    (Finset.mem_range.mpr (by omega)))

/-- The actual isolating bump is identically one near its own carrier point. -/
theorem isolationSchwartz_eventually_one (S : LocallyFiniteCarrier) (a : S.subtype) :
    (S.isolationSchwartz a : ℝ → ℂ) =ᶠ[𝓝 (a:ℝ)] 1 := by
  filter_upwards [Metric.ball_mem_nhds (a:ℝ) (S.isolationBump a).rIn_pos] with x hx
  change ((S.isolationBump a x : ℝ):ℂ) = 1
  rw [(S.isolationBump a).one_of_mem_closedBall (Metric.mem_closedBall.mpr (Metric.mem_ball.mp hx).le)]
  norm_num

/-- The strict support margin makes the isolating bump zero near every other carrier point. -/
theorem isolationSchwartz_eventually_zero (S : LocallyFiniteCarrier) (a b : S.subtype)
    (hab : b ≠ a) : (S.isolationSchwartz a : ℝ → ℂ) =ᶠ[𝓝 (b:ℝ)] 0 := by
  have hdist := S.isolationRadius_le_dist a b.property
    (show (b:ℝ) ≠ (a:ℝ) from fun h => hab (Subtype.ext h))
  have hlt : (S.isolationBump a).rOut < dist (b:ℝ) (a:ℝ) := by
    change S.isolationRadius a / 2 < _
    have hp := S.isolationRadius_pos a
    linarith
  have he : ∀ᶠ x in 𝓝 (b:ℝ), (S.isolationBump a).rOut < dist x (a:ℝ) :=
    (isOpen_lt continuous_const (continuous_id.dist continuous_const)).mem_nhds hlt
  filter_upwards [he] with x hx
  change ((S.isolationBump a x : ℝ):ℂ) = 0
  rw [(S.isolationBump a).zero_of_le_dist hx.le]
  norm_num

/-- An actual isolation multiplier turns ordinary carrier support into point support. -/
theorem supportedOn_isolation_supportedAt (S : LocallyFiniteCarrier)
    (U : TemperedDistribution ℝ ℂ) (hU : DistributionSupportedOn S.carrier U)
    (a : S.subtype) : DistributionSupportedAt (a:ℝ)
      (TemperedDistribution.smulLeftCLM ℂ (S.isolationSchwartz a) U) := by
  intro f hf hfa
  rw [TemperedDistribution.smulLeftCLM_apply_apply]
  apply hU
  · convert! hf.mul_left (f := fun x => S.isolationSchwartz a x) using 1
    ext x
    simp only [SchwartzMap.smulLeftCLM_apply_apply (S.isolationSchwartz a).hasTemperateGrowth, smul_eq_mul, Pi.mul_apply]
  · intro b hb
    by_cases he : b = (a:ℝ)
    · subst b
      filter_upwards [hfa] with x hx
      simp only [SchwartzMap.smulLeftCLM_apply_apply (S.isolationSchwartz a).hasTemperateGrowth,
        Pi.zero_apply, hx, smul_zero]
    · have hz := isolationSchwartz_eventually_zero S a ⟨b,hb⟩
        (fun h => he (congrArg Subtype.val h))
      filter_upwards [hz] with x hx
      simp only [SchwartzMap.smulLeftCLM_apply_apply (S.isolationSchwartz a).hasTemperateGrowth,
        Pi.zero_apply, hx, zero_smul]

/-- Actual native carrier-supported distributions have constructed jets of degree at most 2p
at each isolated point. -/
theorem supportedOn_isolation_eq_jets (S : LocallyFiniteCarrier) (p : ℕ)
    (T : HermiteScale (-(p:ℤ)))
    (hT : DistributionSupportedOn S.carrier (hermiteScaleDistribution p T)) (a : S.subtype) :
    TemperedDistribution.smulLeftCLM ℂ (S.isolationSchwartz a) (hermiteScaleDistribution p T) =
      ∑ r ∈ Finset.range (2*p+1),
        ((-1:ℂ)^r * (TemperedDistribution.smulLeftCLM ℂ (S.isolationSchwartz a)
          (hermiteScaleDistribution p T)) (pointJetBasis r a)) • localDiracDerivative r a := by
  have he := nativeMultiplier_schwartz_realizes p (S.isolationSchwartz a) T
  rw [← he]
  exact supportedAt_eq_sum_diracDerivatives p _ a
    (by rw [he]; exact supportedOn_isolation_supportedAt S _ hT a)


/-- A compact test is identically zero near all but finitely many carrier points. -/
theorem exists_finite_neighborhood_support (S : LocallyFiniteCarrier)
    (f : SchwartzMap ℝ ℂ) (hf : HasCompactSupport (f : ℝ → ℂ)) :
    ∃ E : Finset S.subtype, ∀ a : S.subtype, a ∉ E → (f : ℝ → ℂ) =ᶠ[𝓝 (a:ℝ)] 0 := by
  classical
  obtain ⟨R,hR⟩ := (Metric.isBounded_iff_subset_ball 0).mp hf.isBounded
  let A : Set S.subtype := Subtype.val ⁻¹' (S.carrier ∩ Icc (-R) R)
  have hA : A.Finite := (S.finite_inter_Icc (-R) R).preimage
    (Set.injOn_of_injective Subtype.val_injective)
  refine ⟨hA.toFinset, fun a ha => ?_⟩
  have hn : (a:ℝ) ∉ tsupport (f : ℝ → ℂ) := by
    intro hm
    have hb : |(a:ℝ)| < R := by simpa [Real.dist_eq] using hR hm
    exact ha (hA.mem_toFinset.mpr ⟨a.property,
      (neg_lt_of_abs_lt hb).le,(lt_of_abs_lt hb).le⟩)
  have he : ∀ᶠ x in 𝓝 (a:ℝ), x ∈ (tsupport (f : ℝ → ℂ))ᶜ :=
    (isClosed_tsupport (f : ℝ → ℂ)).isOpen_compl.mem_nhds hn
  filter_upwards [he] with x hx
  exact image_eq_zero_of_notMem_tsupport hx

/-- Canonical local jet readings, obtained by multiplying explicit probes with actual isolators. -/
def carrierJetReading (S : LocallyFiniteCarrier) (U : TemperedDistribution ℝ ℂ)
    (a : S.subtype) (r : ℕ) : ℂ :=
  (TemperedDistribution.smulLeftCLM ℂ (S.isolationSchwartz a) U) (pointJetBasis r a)

/-- The isolated compact-test action is the constructed jet reading formula. -/
theorem supportedOn_isolation_compact_formula (S : LocallyFiniteCarrier) (p : ℕ)
    (T : HermiteScale (-(p:ℤ)))
    (hT : DistributionSupportedOn S.carrier (hermiteScaleDistribution p T))
    (a : S.subtype) (f : SchwartzMap ℝ ℂ) (hf : HasCompactSupport (f : ℝ → ℂ)) :
    (hermiteScaleDistribution p T) (SchwartzMap.smulLeftCLM ℂ (S.isolationSchwartz a) f) =
      ∑ r ∈ Finset.range (2*p+1), carrierJetReading S (hermiteScaleDistribution p T) a r *
        iteratedDeriv r (f : ℝ → ℂ) a := by
  have he := nativeMultiplier_schwartz_realizes p (S.isolationSchwartz a) T
  have hpoint : DistributionSupportedAt (a:ℝ)
      (hermiteScaleDistribution p (nativeMultiplier p p (S.isolationSchwartz a) T)) := by
    rw [he]
    exact supportedOn_isolation_supportedAt S _ hT a
  have h := supportedAt_compact_jet_formula p _ a hpoint f hf
  rw [he] at h
  simpa only [carrierJetReading,TemperedDistribution.smulLeftCLM_apply_apply] using! h


/-- A finite sum of actual isolators recovers every compact-test action. -/
theorem supportedOn_finite_localization (S : LocallyFiniteCarrier)
    (U : TemperedDistribution ℝ ℂ) (hU : DistributionSupportedOn S.carrier U)
    (f : SchwartzMap ℝ ℂ) (hf : HasCompactSupport (f : ℝ → ℂ))
    (E : Finset S.subtype)
    (hE : ∀ a : S.subtype, a ∉ E → (f : ℝ → ℂ) =ᶠ[𝓝 (a:ℝ)] 0) :
    U f = ∑ a ∈ E, U (SchwartzMap.smulLeftCLM ℂ (S.isolationSchwartz a) f) := by
  classical
  let g : SchwartzMap ℝ ℂ := ∑ a ∈ E, SchwartzMap.smulLeftCLM ℂ (S.isolationSchwartz a) f
  have hfg : HasCompactSupport (g : ℝ → ℂ) := by
    have hi (a : S.subtype) : HasCompactSupport
        (SchwartzMap.smulLeftCLM ℂ (S.isolationSchwartz a) f : ℝ → ℂ) := by
      convert! hf.mul_left (f := fun x => S.isolationSchwartz a x) using 1
      ext x
      simp only [SchwartzMap.smulLeftCLM_apply_apply (S.isolationSchwartz a).hasTemperateGrowth,
        smul_eq_mul, Pi.mul_apply]
    convert! HasCompactSupport.finset_sum (s := E)
      (f := fun a => (SchwartzMap.smulLeftCLM ℂ (S.isolationSchwartz a) f : ℝ → ℂ))
      (fun a _ => hi a) using 1
    ext x
    simp only [g,_root_.sum_apply,Finset.sum_apply]
  have hz : U (f-g) = 0 := hU (f-g) (hf.sub hfg) (by
    intro b hb
    let bS : S.subtype := ⟨b,hb⟩
    have hi (a : S.subtype) : ∀ᶠ x in 𝓝 b,
        S.isolationSchwartz a x = if a=bS then 1 else 0 := by
      by_cases ha : a=bS
      · subst a
        simpa only [Filter.EventuallyEq, Pi.one_apply, bS, ite_true] using isolationSchwartz_eventually_one S bS
      · simpa only [Filter.EventuallyEq, Pi.zero_apply, bS, ha,ite_false] using isolationSchwartz_eventually_zero S a bS (Ne.symm ha)
    have hall : ∀ᶠ x in 𝓝 b, ∀ a ∈ E, S.isolationSchwartz a x = if a=bS then 1 else 0 :=
      (Finset.eventually_all E).mpr (fun a _ => hi a)
    by_cases hbE : bS ∈ E
    · filter_upwards [hall] with x hx
      simp only [sub_apply,g,_root_.sum_apply,
        SchwartzMap.smulLeftCLM_apply_apply (S.isolationSchwartz _).hasTemperateGrowth, Pi.zero_apply]
      rw [sub_eq_zero]
      symm
      calc
        _ = ∑ a ∈ E, (if a=bS then (1:ℂ) else 0) • f x :=
          Finset.sum_congr rfl (fun a ha => by rw [hx a ha])
        _ = f x := by simp [hbE]
    · filter_upwards [hall,hE bS hbE] with x hx hfx
      simp only [sub_apply,g,_root_.sum_apply,
        SchwartzMap.smulLeftCLM_apply_apply (S.isolationSchwartz _).hasTemperateGrowth,hfx,
        Pi.zero_apply,smul_zero,Finset.sum_const_zero,sub_self])
  rw [map_sub,sub_eq_zero] at hz
  rw [hz]
  exact map_sum U _ E

/-- Ordinary discrete support of an original H_-p source gives an actual finite compact-test
jet formula, with one canonical coefficient family and degree at most 2p. -/
theorem supportedOn_compact_jet_formula (S : LocallyFiniteCarrier) (p : ℕ)
    (T : HermiteScale (-(p:ℤ)))
    (hT : DistributionSupportedOn S.carrier (hermiteScaleDistribution p T))
    (f : SchwartzMap ℝ ℂ) (hf : HasCompactSupport (f : ℝ → ℂ)) :
    ∃ E : Finset S.subtype,
      (∀ a : S.subtype, a ∉ E → (f : ℝ → ℂ) =ᶠ[𝓝 (a:ℝ)] 0) ∧
      hermiteScaleDistribution p T f = ∑ a ∈ E, ∑ r ∈ Finset.range (2*p+1),
        carrierJetReading S (hermiteScaleDistribution p T) a r *
          iteratedDeriv r (f : ℝ → ℂ) a := by
  obtain ⟨E,hE⟩ := exists_finite_neighborhood_support S f hf
  refine ⟨E,hE,?_⟩
  rw [supportedOn_finite_localization S _ hT f hf E hE]
  exact Finset.sum_congr rfl (fun a ha => supportedOn_isolation_compact_formula S p T hT a f hf)


/-- Any genuine isolated Kronecker probe recovers the same canonical jet coefficient. -/
theorem carrierJetReading_eq_of_probe (S : LocallyFiniteCarrier) (p : ℕ)
    (T : HermiteScale (-(p:ℤ)))
    (hT : DistributionSupportedOn S.carrier (hermiteScaleDistribution p T))
    (a : S.subtype) (r : ℕ) (hr : r ≤ 2*p) (f : SchwartzMap ℝ ℂ)
    (hf : HasCompactSupport (f : ℝ → ℂ))
    (hj : ∀ n ≤ 2*p, iteratedDeriv n (f : ℝ → ℂ) a = if n=r then 1 else 0)
    (hz : ∀ b : S.subtype, b ≠ a → (f : ℝ → ℂ) =ᶠ[𝓝 (b:ℝ)] 0) :
    carrierJetReading S (hermiteScaleDistribution p T) a r = hermiteScaleDistribution p T f := by
  classical
  have h := supportedOn_finite_localization S _ hT f hf {a}
    (fun b hb => hz b (by simpa only [Finset.mem_singleton] using hb))
  simp only [Finset.sum_singleton] at h
  rw [supportedOn_isolation_compact_formula S p T hT a f hf] at h
  rw [h]
  symm
  calc
    _ = ∑ n ∈ Finset.range (2*p+1),
        carrierJetReading S (hermiteScaleDistribution p T) a n * (if n=r then 1 else 0) :=
      Finset.sum_congr rfl (fun n hn => by rw [hj n (by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hn))])
    _ = _ := by simp [Finset.mem_range.mpr (show r<2*p+1 by omega)]

/-- Fixed-width actual probes have the original translation growth of degree 2p,
uniformly through any prescribed finite jet degree. -/
theorem exists_localJetProbe_native_polynomial_bound (p N : ℕ) (ψ : SchwartzMap ℝ ℂ)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ r ≤ N, ∀ a : ℝ,
      ‖schwartzToHermiteScale p (localJetProbe ψ δ hδ r a)‖ ≤ C*(1+|a|)^(2*p) := by
  obtain ⟨B,hB,hbound⟩ := exists_hermite_translation_bound p
  let g : ℕ → SchwartzMap ℝ ℂ := fun r => (1/(r.factorial:ℂ)) •
    mixedSchwartz r 0 (combSchwartzDilation δ⁻¹ (inv_ne_zero hδ.ne') ψ)
  let A : ℝ := 1 + ∑ r ∈ Finset.range (N+1), ‖schwartzToHermiteScale p (g r)‖
  have hA : 0 < A := by
    dsimp only [A]
    positivity
  refine ⟨B*A,mul_pos hB hA,fun r hr a => ?_⟩
  have hg : ‖schwartzToHermiteScale p (g r)‖ ≤ A := by
    have hs : ‖schwartzToHermiteScale p (g r)‖ ≤
        ∑ n ∈ Finset.range (N+1), ‖schwartzToHermiteScale p (g n)‖ :=
      Finset.single_le_sum (f := fun n => ‖schwartzToHermiteScale p (g n)‖)
        (fun n _ => norm_nonneg _) (Finset.mem_range.mpr (show r<N+1 by omega))
    dsimp only [A]
    linarith
  have ht := hbound (-a) (g r)
  simp only [abs_neg] at ht
  apply ht.trans
  calc
    _ ≤ B*(1+|a|)^(2*p)*A := mul_le_mul_of_nonneg_left hg (by positivity)
    _ = _ := by ring


/-- A fixed-width compact probe vanishes outside its explicit support radius. -/
theorem localJetProbe_cutoff_zero (δ : ℝ) (hδ : 0 < δ) (r : ℕ) (a x : ℝ)
    (hx : 2*δ ≤ |x-a|) : localJetProbe compactSchwartzCutoff δ hδ r a x = 0 := by
  rw [localJetProbe_apply]
  have hb : compactSchwartzCutoff ((x-a)/δ) = 0 := by
    change ((compactSchwartzCutoffBump ((x-a)/δ) : ℝ):ℂ) = 0
    rw [compactSchwartzCutoffBump.zero_of_le_dist]
    · norm_num
    · change 2 ≤ dist ((x-a)/δ) 0
      rw [Real.dist_eq,sub_zero,abs_div,abs_of_pos hδ]
      exact (le_div_iff₀ hδ).mpr hx
  rw [hb,mul_zero]

/-- Actual fixed-width Kronecker probes have compact support. -/
theorem localJetProbe_cutoff_hasCompactSupport (δ : ℝ) (hδ : 0 < δ) (r : ℕ) (a : ℝ) :
    HasCompactSupport (localJetProbe compactSchwartzCutoff δ hδ r a : ℝ → ℂ) := by
  apply HasCompactSupport.intro (K := Icc (a-2*δ) (a+2*δ)) isCompact_Icc
  intro x hx
  apply localJetProbe_cutoff_zero
  have hh : x < a-2*δ ∨ a+2*δ < x := by simpa only [mem_Icc,not_and_or,not_le] using hx
  rcases hh with hh | hh
  · exact (by linarith : 2*δ ≤ -(x-a)).trans (neg_le_abs _)
  · exact (by linarith : 2*δ ≤ x-a).trans (le_abs_self _)

/-- Positive separation leaves an open zero neighborhood for the compact probe. -/
theorem localJetProbe_cutoff_eventually_zero (δ : ℝ) (hδ : 0 < δ) (r : ℕ) (a b : ℝ)
    (hab : 2*δ < |b-a|) :
    (localJetProbe compactSchwartzCutoff δ hδ r a : ℝ → ℂ) =ᶠ[𝓝 b] 0 := by
  have he : ∀ᶠ x in 𝓝 b, 2*δ < |x-a| :=
    (isOpen_lt continuous_const ((continuous_id.sub continuous_const).abs)).mem_nhds hab
  filter_upwards [he] with x hx
  exact localJetProbe_cutoff_zero δ hδ r a x hx.le

/-- On a uniformly separated carrier, canonical jets are read by actual fixed-width probes. -/
theorem carrierJetReading_eq_fixed_probe (S : LocallyFiniteCarrier) (p : ℕ)
    (T : HermiteScale (-(p:ℤ)))
    (hT : DistributionSupportedOn S.carrier (hermiteScaleDistribution p T))
    (δ : ℝ) (hδ : 0 < δ)
    (hsep : ∀ a b : S.subtype, b ≠ a → 4*δ ≤ |(b:ℝ)-(a:ℝ)|)
    (a : S.subtype) (r : ℕ) (hr : r ≤ 2*p) :
    carrierJetReading S (hermiteScaleDistribution p T) a r =
      hermiteScaleDistribution p T (localJetProbe compactSchwartzCutoff δ hδ r a) := by
  apply carrierJetReading_eq_of_probe S p T hT a r hr _
    (localJetProbe_cutoff_hasCompactSupport δ hδ r a)
  · intro n hn
    apply localJetProbe_derivative_center
    filter_upwards [Metric.ball_mem_nhds (0:ℝ) zero_lt_one] with x hx
    exact compactSchwartzCutoff_eq_one (by simpa [Real.dist_eq] using (Metric.mem_ball.mp hx).le)
  · intro b hb
    apply localJetProbe_cutoff_eventually_zero
    have hh := hsep a b hb
    linarith

/-- All actual native jet coefficients on a uniformly separated carrier have polynomial
size of degree 2p, with a common constant for every point and every jet through 2p. -/
theorem exists_carrierJetReading_polynomial_bound (S : LocallyFiniteCarrier) (p : ℕ)
    (δ : ℝ) (hδ : 0 < δ)
    (hsep : ∀ a b : S.subtype, b ≠ a → 4*δ ≤ |(b:ℝ)-(a:ℝ)|) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : HermiteScale (-(p:ℤ)),
      DistributionSupportedOn S.carrier (hermiteScaleDistribution p T) →
      ∀ a : S.subtype, ∀ r ≤ 2*p,
        ‖carrierJetReading S (hermiteScaleDistribution p T) a r‖ ≤
          C*‖T‖*(1+|(a:ℝ)|)^(2*p) := by
  obtain ⟨C,hC,hbound⟩ := exists_localJetProbe_native_polynomial_bound p (2*p)
    compactSchwartzCutoff δ hδ
  refine ⟨C,hC,fun T hT a r hr => ?_⟩
  rw [carrierJetReading_eq_fixed_probe S p T hT δ hδ hsep a r hr,
    hermiteScaleDistribution_apply]
  calc
    _ ≤ ‖T‖*‖schwartzToHermiteScale p (localJetProbe compactSchwartzCutoff δ hδ r a)‖ :=
      norm_hermiteScalePairing_le (p:ℤ) T _
    _ ≤ ‖T‖*(C*(1+|(a:ℝ)|)^(2*p)) := mul_le_mul_of_nonneg_left (hbound r hr a) (norm_nonneg _)
    _ = _ := by ring


/-- The constructed bounded-degree readings determine the entire native distribution,
including its action on every noncompact Schwartz test. -/
theorem supportedOn_eq_of_carrierJetReading_eq (S : LocallyFiniteCarrier) (p : ℕ)
    (T V : HermiteScale (-(p:ℤ)))
    (hT : DistributionSupportedOn S.carrier (hermiteScaleDistribution p T))
    (hV : DistributionSupportedOn S.carrier (hermiteScaleDistribution p V))
    (he : ∀ a : S.subtype, ∀ r ≤ 2*p,
      carrierJetReading S (hermiteScaleDistribution p T) a r =
        carrierJetReading S (hermiteScaleDistribution p V) a r) :
    hermiteScaleDistribution p T = hermiteScaleDistribution p V := by
  apply distributions_eq_of_compact_test_eq
  intro f hf
  obtain ⟨E,hE⟩ := exists_finite_neighborhood_support S f hf
  rw [supportedOn_finite_localization S _ hT f hf E hE,
    supportedOn_finite_localization S _ hV f hf E hE]
  apply Finset.sum_congr rfl
  intro a ha
  rw [supportedOn_isolation_compact_formula S p T hT a f hf,
    supportedOn_isolation_compact_formula S p V hV a f hf]
  exact Finset.sum_congr rfl (fun r hr => by rw [he a r (by
    have hh := Finset.mem_range.mp hr
    omega)])

end
end MeyerGeneralProblem.Adaptive
