module

public import MeyerGeneralProblem.Sampling.BeurlingBiorthogonal

@[expose] public section

/-!
# Uniform finite interpolation kernels from strict upper density

The actual density-to-colouring reduction, Haraux augmentation, Hilbert
biorthogonal construction, and finite convolution are assembled here.  The
output consists of genuine integrable interpolation kernels with uniform
`L¹` bounds and a strict support margin inside the requested interval.
-/

namespace MeyerGeneralProblem

open MeasureTheory

noncomputable section

/-- A uniformly separated family can be annihilated by an actual supported
kernel normalized at one additional positively separated frequency.  The
mass bound is uniform in the finite family and in that additional frequency. -/
theorem exists_uniform_supported_frequency_separator
    {b r L d : ℝ} (hb : 0 < b) (hr : 0 < r) (hL : 0 < L) (hd : 0 < d)
    (hgap : 1 < 2 * b * L) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (s : Fin n → ℝ),
      PairwiseFrequencySeparated s L → ∀ ω : ℝ, (∀ i, d ≤ |s i - ω|) →
      ∃ ψ : ℝ → ℂ, Integrable ψ ∧ MemLp ψ 2 volume ∧
        Function.support ψ ⊆ Set.Icc (-(b + r)) (b + r) ∧
        FourierTransform.fourier ψ ω = 1 ∧
        (∀ i, FourierTransform.fourier ψ (s i) = 0) ∧
        (∫ t : ℝ, ‖ψ t‖) ^ 2 ≤ C := by
  obtain ⟨A, hA, hbound⟩ :=
    exists_uniform_finite_cosineIngham_insert_frequency hb hr hL hd hgap
  refine ⟨2 * (b + r) / A, by positivity, fun n s hsep ω hω => ?_⟩
  let aug : Fin (n + 1) → ℝ := fun i => @Fin.cases n (fun _ => ℝ) ω s i
  have hlower (c : Fin (n + 1) → ℂ) :
      A * ∑ i, ‖c i‖ ^ 2 ≤ ∫ t : ℝ in Set.Icc (-(b + r)) (b + r),
        ‖gramFourierPolynomial aug c t‖ ^ 2 := by
    have h := hbound n s hsep ω hω (c 0) (fun i => c i.succ)
    have hpoly (t : ℝ) : gramFourierPolynomial aug c t =
        c 0 * gramPhase ω t + gramFourierPolynomial s (fun i => c i.succ) t := by
      unfold gramFourierPolynomial
      rw [Fin.sum_univ_succ]
      rfl
    rw [Fin.sum_univ_succ]
    simpa only [hpoly] using h
  have hkernel :=
    @exists_supported_fourier_biorthogonal_of_lowerBound (n + 1) (b + r)
      (add_pos hb hr) aug A hA hlower
  obtain ⟨ψ, hψint, hψL2, hψsupp, hψfourier, hψnorm⟩ := hkernel
  refine ⟨ψ 0, hψint 0, hψL2 0, hψsupp 0, ?_, ?_, hψnorm 0⟩
  · simpa only [aug, Fin.cases_zero, ite_true] using hψfourier 0 0
  · intro i
    simpa only [aug, Fin.cases_succ, ite_eq_right (Ne.symm (Fin.succ_ne_zero i))] using
      hψfourier 0 i.succ

/-- Convolution assembles actual finite interpolation kernels for a coloured
finite carrier.  The common mass bound is chosen before the finite carrier,
and the support half-width is exactly the sum of the colour budgets. -/
theorem exists_uniform_supported_kernels_of_finite_colouring
    (m : ℕ) {b r L d : ℝ} (hb : 0 < b) (hr : 0 < r) (hL : 0 < L) (hd : 0 < d)
    (hgap : 1 < 2 * b * L) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : Finset ℝ) (colour : F → Fin (m + 1)),
      (∀ x y : F, colour x = colour y → x ≠ y → L ≤ |(x : ℝ) - y|) →
      (∀ x y : F, x ≠ y → d ≤ |(x : ℝ) - y|) →
      ∃ ρ : F → ℝ → ℂ, (∀ x, Integrable (ρ x)) ∧
        (∀ x, Function.support (ρ x) ⊆
          Set.Icc (-((m + 1 : ℕ) * (b + r))) ((m + 1 : ℕ) * (b + r))) ∧
        (∀ x y : F, FourierTransform.fourier (ρ x) y = if x = y then 1 else 0) ∧
        ∀ x, (∫ t : ℝ, ‖ρ x t‖) ^ 2 ≤ C := by
  classical
  obtain ⟨C₀, hC₀, hseparator⟩ := exists_uniform_supported_frequency_separator hb hr hL hd hgap
  refine ⟨C₀ ^ (m + 1), pow_pos hC₀ _, fun F colour hcolour hsep => ?_⟩
  have hone (x : F) (k : Fin (m + 1)) : ∃ ψ : ℝ → ℂ,
      Integrable ψ ∧ Function.support ψ ⊆ Set.Icc (-(b + r)) (b + r) ∧
      FourierTransform.fourier ψ x = 1 ∧
      (∀ y : F, colour y = k → y ≠ x → FourierTransform.fourier ψ y = 0) ∧
      (∫ t : ℝ, ‖ψ t‖) ^ 2 ≤ C₀ := by
    let J := {y : F // colour y = k ∧ y ≠ x}
    let e : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
    let s : Fin (Fintype.card J) → ℝ := fun i => ((e i).val : ℝ)
    have hs : PairwiseFrequencySeparated s L := by
      intro i j hij
      exact hcolour (e i).val (e j).val ((e i).property.1.trans (e j).property.1.symm)
        (fun h => hij (e.injective (Subtype.ext h)))
    have hxsep (i : Fin (Fintype.card J)) : d ≤ |s i - x| :=
      hsep (e i).val x (e i).property.2
    obtain ⟨ψ, hψint, _hψL2, hψsupp, hψx, hψzero, hψnorm⟩ :=
      hseparator _ s hs x hxsep
    refine ⟨ψ, hψint, hψsupp, hψx, ?_, hψnorm⟩
    intro y hy hyx
    let j : J := ⟨y, hy, hyx⟩
    simpa only [s, e.apply_symm_apply] using hψzero (e.symm j)
  choose ψ hψint hψsupp hψone hψzero hψnorm using hone
  let ρ : F → ℝ → ℂ := fun x => finiteFourierKernelConvolution m (ψ x)
  refine ⟨ρ, fun x => integrable_finiteFourierKernelConvolution m (ψ x) (hψint x), ?_, ?_, ?_⟩
  · intro x
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
      support_finiteFourierKernelConvolution_subset m (ψ x) (fun _ => b + r) (hψsupp x)
  · intro x y
    change FourierTransform.fourier (finiteFourierKernelConvolution m (ψ x)) y = _
    rw [fourier_finiteFourierKernelConvolution m (ψ x) (hψint x)]
    by_cases hxy : x = y
    · subst y
      simp only [hψone, Finset.prod_const_one, ite_true]
    · rw [ite_eq_right hxy]
      exact Finset.prod_eq_zero (Finset.mem_univ (colour y))
        (hψzero x (colour y) y rfl (Ne.symm hxy))
  · intro x
    have hmass := integral_norm_finiteFourierKernelConvolution_le m (ψ x) (hψint x)
    have hnonneg (k : Fin (m + 1)) : 0 ≤ ∫ t : ℝ, ‖ψ x k t‖ :=
      integral_nonneg (fun t => norm_nonneg _)
    calc
      _ ≤ (∏ k, ∫ t : ℝ, ‖ψ x k t‖) ^ 2 :=
        (sq_le_sq₀ (integral_nonneg (fun t => norm_nonneg _))
          (Finset.prod_nonneg (fun k hk => hnonneg k))).2 hmass
      _ = ∏ k, (∫ t : ℝ, ‖ψ x k t‖) ^ 2 := (Finset.prod_pow _ _ _).symm
      _ ≤ ∏ _k : Fin (m + 1), C₀ :=
        Finset.prod_le_prod₀ (fun k hk => sq_nonneg _) (fun k hk => hψnorm x k)
      _ = C₀ ^ (m + 1) := by simp

/-- Strict upper uniform Beurling density and positive separation produce
genuine finite interpolation kernels with a common `L¹` bound and support
strictly inside `[-a,a]`.  The support margin is reserved for the final
smoothing step converting uniform interpolation into the lower Riesz bound. -/
theorem exists_uniform_finite_interpolation_kernels_of_upperDensity_lt
    (S : LocallyFiniteCarrier) {a d : ℝ} (ha : 0 < a) (hd : 0 < d)
    (hS : upperUniformBeurlingDensity S < ENNReal.ofReal (2 * a))
    (hsep : ∀ x ∈ S.carrier, ∀ y ∈ S.carrier, x ≠ y → d ≤ |x - y|) :
    ∃ R C : ℝ, 0 < R ∧ R < a ∧ 0 < C ∧
      ∀ (F : Finset ℝ), (∀ x ∈ F, x ∈ S.carrier) →
        ∃ ρ : F → ℝ → ℂ, (∀ x, Integrable (ρ x)) ∧
          (∀ x, Function.support (ρ x) ⊆ Set.Icc (-R) R) ∧
          (∀ x y : F, FourierTransform.fourier (ρ x) y = if x = y then 1 else 0) ∧
          ∀ x, (∫ t : ℝ, ‖ρ x t‖) ^ 2 ≤ C := by
  classical
  obtain ⟨N, hN, L, hL, hratio, hcap⟩ :=
    exists_uniform_windowCap_of_upperDensity_lt S (by positivity : 0 < 2 * a) hS
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
  have hNr : (0 : ℝ) < (m + 1 : ℕ) := by positivity
  have hbudget : 1 / (2 * L) < a / (m + 1 : ℕ) := by
    apply (div_lt_div_iff₀ (by positivity) hNr).2
    nlinarith
  obtain ⟨b, hblo, hbhi⟩ := exists_between hbudget
  have hb : 0 < b := (by positivity : (0 : ℝ) < 1 / (2 * L)).trans hblo
  have hgap : 1 < 2 * b * L := by
    have h := (div_lt_iff₀ (by positivity : 0 < 2 * L)).1 hblo
    nlinarith
  obtain ⟨w, hbw, hwa⟩ := exists_between hbhi
  let r := w - b
  have hr : 0 < r := sub_pos.2 hbw
  have hsum : b + r = w := by dsimp [r]; ring
  obtain ⟨C, hC, hkernels⟩ :=
    exists_uniform_supported_kernels_of_finite_colouring m hb hr hL hd hgap
  refine ⟨(m + 1 : ℕ) * (b + r), C, by positivity, ?_, hC, fun F hF => ?_⟩
  · rw [hsum]
    have h := (lt_div_iff₀ hNr).1 hwa
    nlinarith
  · obtain ⟨colour, hcolour⟩ := exists_finite_colouring_of_uniform_windowCap hN hcap F hF
    exact hkernels F colour hcolour (fun x y hxy =>
      hsep x (hF x x.property) y (hF y y.property) (fun h => hxy (Subtype.ext h)))

end

end MeyerGeneralProblem
