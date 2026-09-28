module

public import MeyerGeneralProblem.Cardinal.Adaptive.FixedProbeTemplate
public import MeyerGeneralProblem.Cardinal.Adaptive.ActualSourceSplitting

@[expose] public section

/-! # Actual future-source estimates from the preselected spatial cutoffs -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open Filter
open scoped Topology FourierTransform

/-- The selected gaps increase, as a consequence of their actual doubling floor. -/
theorem actualGaps_monotone (ψ : SchwartzMap ℝ ℂ) : Monotone (actualGaps ψ) := by
  apply monotone_nat_of_le_succ
  intro n
  have h := (actualGaps_step ψ n).2.1
  omega

/-- The first-M label set has precisely the source's positive-index cutoff. -/
theorem mem_finitePrefixLabels_iff (M : ℕ) (b : Label) :
    b ∈ finitePrefixLabels M ↔ b.1.val ≤ M := by
  classical
  constructor
  · intro hb
    obtain ⟨⟨i,σ⟩,_,he⟩ := Finset.mem_image.mp hb
    have hi := congrArg (fun b : Label => b.1.val) he
    dsimp [prefixScaleIndex] at hi
    omega
  · intro hb
    let i : Fin M := ⟨b.1.val-1,by have := b.1.pos; omega⟩
    apply Finset.mem_image.mpr
    refine ⟨(i,b.2),Finset.mem_univ _,?_⟩
    apply Prod.ext
    · apply Subtype.ext
      change b.1.val-1+1=b.1.val
      have := b.1.pos
      omega
    · rfl

/-- Every omitted label starts beyond the same already selected next gap. -/
theorem actual_future_gap (ψ : SchwartzMap ℝ ℂ) (n : ℕ) (b : Label)
    (hb : b ∉ finitePrefixLabels (n+1)) :
    actualGaps ψ (n+1) ≤ actualPositiveGaps ψ b.1 := by
  have hi : n+1 < b.1.val := lt_of_not_ge (fun h => hb ((mem_finitePrefixLabels_iff _ _).mpr h))
  apply actualGaps_monotone ψ
  omega

/-- A future-supported whole distribution sees exactly the Fourier cutoff error. -/
theorem supported_future_cutoff_eq (U : TemperedDistribution ℝ ℂ) (N : ℕ) (r : ℝ)
    (hU : DistributionSupportedOn {x : ℝ | r/3 < |x|} U)
    (hN : 2*((N:ℝ)+1) ≤ r/3) (f : SchwartzMap ℝ ℂ) :
    U f = U (f-compactSchwartzApproximation N f) := by
  have hz : U (compactSchwartzApproximation N f) = 0 := by
    apply hU _ (compactSchwartzApproximation_hasCompactSupport N f)
    intro a ha
    have he : ∀ᶠ x in 𝓝 a, 2*((N:ℝ)+1) < |x| :=
      (isOpen_lt continuous_const continuous_abs).mem_nhds (hN.trans_lt ha)
    filter_upwards [he] with x hx
    have h := schwartzCutoffError_eq_self N f x hx.le
    simp only [_root_.sub_apply] at h
    exact sub_eq_self.mp h
  rw [map_sub,hz,sub_zero]

/-- The Fourier isometry and whole support turn a paid native cutoff error into
an actual source pairing estimate, without an assumption about physical support. -/
theorem native_future_pairing_bound (q N : ℕ) (U : HermiteScale (-(q:ℤ)))
    (r ε : ℝ) (hU : DistributionSupportedOn {x : ℝ | r/3 < |x|}
      (𝓕 (hermiteScaleDistribution q U))) (hN : 2*((N:ℝ)+1) ≤ r/3)
    (f : SchwartzMap ℝ ℂ)
    (hf : ‖schwartzToHermiteScale q (𝓕⁻ f-compactSchwartzApproximation N (𝓕⁻ f))‖ ≤ ε) :
    ‖hermiteScaleDistribution q U f‖ ≤ ε*‖U‖ := by
  have he : hermiteScaleDistribution q U f =
      (𝓕 (hermiteScaleDistribution q U)) (𝓕⁻ f) := by
    rw [TemperedDistribution.fourier_apply,FourierTransform.fourier_fourierInv_eq]
  rw [he,supported_future_cutoff_eq _ N r hU hN]
  rw [← hermiteFourier_represents_distributionalFourier,hermiteScaleDistribution_apply]
  calc
    _ ≤ ‖hermiteFourier (-(q:ℤ)) U‖ *
        ‖schwartzToHermiteScale q (𝓕⁻ f-compactSchwartzApproximation N (𝓕⁻ f))‖ :=
      norm_hermiteScalePairing_le _ _ _
    _ ≤ ‖U‖*ε := by rw [LinearIsometryEquiv.norm_map]; exact mul_le_mul_of_nonneg_left hf (norm_nonneg U)
    _ = ε*‖U‖ := mul_comm _ _

/-- The actual preselected spatial cutoff lies strictly inside all future sectors. -/
theorem actualStage_cutoff_inside_next_gap (ψ : SchwartzMap ℝ ℂ) (n : ℕ) :
    2*(((actualStage ψ n).spatialCutoff:ℝ)+1) ≤ (actualGaps ψ (n+1):ℝ)/3 := by
  have h := (actualGaps_step ψ n).2.2.2
  have hr : 6*(((actualStage ψ n).spatialCutoff:ℝ)+1) ≤ (actualGaps ψ (n+1):ℝ) := by
    exact_mod_cast h
  linarith

/-- Budget J gives an actual future-source pairing estimate for every prescribed
jet order, uniformly over the complete allowed window of probe centers. -/
theorem actualStage_jet_future_pairing_bound (ψ : SchwartzMap ℝ ℂ) (n p r : ℕ)
    (hp : p ≤ n+1) (hr : r ≤ 12*p) (U : HermiteScale (-((6*p:ℕ):ℤ)))
    (hU : DistributionSupportedOn {x : ℝ | (actualGaps ψ (n+1):ℝ)/3 < |x|}
      (𝓕 (hermiteScaleDistribution (6*p) U)))
    (y : ℝ) (hy : |y| ≤ 2*(n+1:ℝ)+1) :
    ‖hermiteScaleDistribution (6*p) U
      (localJetProbe ψ (actualStage ψ n).jetRadius (actualStage ψ n).jetRadius_pos r y)‖ ≤
        (2:ℝ)^(-((n+1:ℕ):ℤ))*‖U‖ := by
  apply native_future_pairing_bound (6*p) (actualStage ψ n).spatialCutoff U
    (actualGaps ψ (n+1):ℝ) _ hU (actualStage_cutoff_inside_next_gap ψ n)
  have h := (actualStage_laws ψ n).jet_spatial p hp r hr true y (by simpa only [PNat.mk_coe,Nat.cast_add,Nat.cast_one] using hy)
  exact h.le

/-- Budget B controls the actual future pairing of each translated partitioned
test in the fixed prescribed derivative class, with the finite-partition divisor. -/
theorem actualStage_translated_future_pairing_bound (ψ : SchwartzMap ℝ ℂ) (n p : ℕ)
    (hp : p ≤ n+1) (U : HermiteScale (-((6*p:ℕ):ℤ)))
    (hU : DistributionSupportedOn {x : ℝ | (actualGaps ψ (n+1):ℝ)/3 < |x|}
      (𝓕 (hermiteScaleDistribution (6*p) U)))
    (j : Fin (actualStage ψ n).partitionSize) (f : SchwartzMap ℝ ℂ)
    (hf : tsupport f ⊆ Set.Icc (-(2*(n+1:ℝ)+1)) (2*(n+1:ℝ)+1))
    (hderiv : ∀ r ≤ testOrder p, ∀ x, ‖iteratedDeriv r (f : ℝ → ℂ) x‖ ≤ 1)
    (h : ℝ) (hh : |h| ≤ (actualStage ψ n).translationBound) :
    ‖hermiteScaleDistribution (6*p) U
      (combSchwartzTranslation h (SchwartzMap.smulLeftCLM ℂ ((actualStage ψ n).partition j) f))‖ ≤
        ((2:ℝ)^(-((n+1:ℕ):ℤ))/(1+((actualStage ψ n).partitionSize:ℝ)))*‖U‖ := by
  apply native_future_pairing_bound (6*p) (actualStage ψ n).spatialCutoff U
    (actualGaps ψ (n+1):ℝ) _ hU (actualStage_cutoff_inside_next_gap ψ n)
  have hb := (actualStage_laws ψ n).translated_spatial p hp j f (by simpa only [PNat.mk_coe,Nat.cast_add,Nat.cast_one] using hf) hderiv h hh true
  exact hb.le

/-- The exact native source piece has the future support used in both paid
pairing estimates. Its physical support is neither needed nor presumed. -/
theorem actualSourcePiece_future_support (ψ : SchwartzMap ℝ ℂ) (s : ℕ+ → ℝ)
    (hs : ActualGoodScale ψ s) (σ : ℝ) (hσ : 0 < σ) (p n : ℕ)
    (hsep : ∀ b d : Label, b ≠ d → ∀ x ∈ sectorSet (actualPositiveGaps ψ) s b,
      ∀ y ∈ sectorSet (actualPositiveGaps ψ) s d, σ/(1+|x|+|y|)^6 ≤ |x-y|)
    (L : LocallyFiniteCarrier) (hL : L.carrier ⊆ carrierSet (actualPositiveGaps ψ) s)
    (T : HermiteScale (-(p:ℤ))) (hT : AtomicOnCarrier L (𝓕 (hermiteScaleDistribution p T))) :
    DistributionSupportedOn {x : ℝ | (actualGaps ψ (n+1):ℝ)/3 < |x|}
      (𝓕 (hermiteScaleDistribution (6*p) (nativeSourcePiece σ hσ p (actualPositiveGaps ψ) s
        (↑(finitePrefixLabels (n+1)) : Set Label)ᶜ T))) := by
  apply nativeSourcePiece_future_spectral_support σ hσ p _ s (actualPositiveGaps_pos ψ)
    hs.1.1 hsep L hL T hT (finitePrefixLabels (n+1)) _
  · have h := actualGaps_exponential ψ (n+1)
    have h2 : 2 ≤ 2^((n+1)+1) := by
      rw [pow_succ]
      have hp : 1 ≤ 2^(n+1) := one_le_pow₀ (by norm_num)
      omega
    exact_mod_cast h2.trans h
  · intro b hb
    exact_mod_cast actual_future_gap ψ n b hb

end
end MeyerGeneralProblem.Adaptive
