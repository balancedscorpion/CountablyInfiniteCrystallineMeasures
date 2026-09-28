module

public import MeyerGeneralProblem.Cardinal.Adaptive.UniformSchwartzTails

@[expose] public section

/-! # Native tail budgets and exact coefficient readings for local jet probes -/

namespace MeyerGeneralProblem.Adaptive
noncomputable section
open Filter
open scoped Topology BigOperators

/-- A finite union of bounded Schwartz families is bounded with one constant. -/
theorem SchwartzFamilyBounded.finite_union {κ ι : Type*} [Fintype κ]
    (f : κ → ι → SchwartzMap ℝ ℂ) (hf : ∀ a, SchwartzFamilyBounded (f a)) :
    SchwartzFamilyBounded (fun a : κ × ι => f a.1 a.2) := by
  classical
  intro k n
  choose C hC hb using (fun a => hf a k n)
  refine ⟨∑ a, C a,Finset.sum_nonneg (fun a _ => hC a),fun a => ?_⟩
  exact (hb a.1 a.2).trans (Finset.single_le_sum (fun a _ => hC a) (Finset.mem_univ a.1))

/-- Both Fourier signs applied to a bounded family remain a single bounded family. -/
theorem SchwartzFamilyBounded.fourier_signs {ι : Type*} {f : ι → SchwartzMap ℝ ℂ}
    (hf : SchwartzFamilyBounded f) :
    SchwartzFamilyBounded (fun a : Bool × ι => if a.1 then
      FourierTransform.fourierInvCLM ℂ (SchwartzMap ℝ ℂ) (f a.2)
      else FourierTransform.fourierCLM ℂ (SchwartzMap ℝ ℂ) (f a.2)) := by
  apply SchwartzFamilyBounded.finite_union
    (f := fun (b : Bool) i => if b then FourierTransform.fourierInvCLM ℂ (SchwartzMap ℝ ℂ) (f i)
      else FourierTransform.fourierCLM ℂ (SchwartzMap ℝ ℂ) (f i))
  intro b
  cases b
  · exact hf.map (FourierTransform.fourierCLM ℂ (SchwartzMap ℝ ℂ))
  · exact hf.map (FourierTransform.fourierInvCLM ℂ (SchwartzMap ℝ ℂ))

/-- Actual local jet probe with fixed width, factorial normalization and center y. -/
def localJetProbe (ψ : SchwartzMap ℝ ℂ) (δ : ℝ) (hδ : 0 < δ) (r : ℕ) (y : ℝ) :
    SchwartzMap ℝ ℂ :=
  combSchwartzTranslation (-y) ((1/(r.factorial:ℂ)) •
    mixedSchwartz r 0 (combSchwartzDilation δ⁻¹ (inv_ne_zero hδ.ne') ψ))

/-- Exact pointwise formula for the actual Schwartz jet probe. -/
theorem localJetProbe_apply (ψ : SchwartzMap ℝ ℂ) (δ : ℝ) (hδ : 0 < δ)
    (r : ℕ) (y x : ℝ) :
    localJetProbe ψ δ hδ r y x = ((x-y:ℝ):ℂ)^r/(r.factorial:ℂ)*ψ ((x-y)/δ) := by
  simp only [localJetProbe,combSchwartzTranslation_apply,smul_apply,
    mixedSchwartz_apply,iteratedDeriv_zero,combSchwartzDilation_apply,smul_eq_mul]
  have he : δ⁻¹*(-y+x) = (x-y)/δ := by ring
  rw [he]
  push_cast
  ring

/-- Every fixed finite collection of jet orders is bounded in the full Schwartz
topology, uniformly over its complete compact range of centers. -/
theorem schwartzFamilyBounded_localJetProbes (ψ : SchwartzMap ℝ ℂ) (δ H : ℝ)
    (hδ : 0 < δ) (hH : 0 ≤ H) (R : ℕ) :
    SchwartzFamilyBounded (fun a : Fin (R+1) × {y : ℝ // |y| ≤ H} =>
      localJetProbe ψ δ hδ a.1 a.2) := by
  apply SchwartzFamilyBounded.finite_union
    (f := fun (r : Fin (R+1)) (y : {y : ℝ // |y| ≤ H}) => localJetProbe ψ δ hδ r y)
  intro r k n
  obtain ⟨C,hC,hb⟩ := schwartzFamilyBounded_translations
    ((1/(r.val.factorial:ℂ)) • mixedSchwartz r 0
      (combSchwartzDilation δ⁻¹ (inv_ne_zero hδ.ne') ψ)) H hH k n
  exact ⟨C,hC,fun y => hb ⟨-y.val,by simpa only [abs_neg] using y.property⟩⟩

/-- Uniform native spatial cutoff convergence for a whole bounded Schwartz family. -/
theorem SchwartzFamilyBounded.native_spatial_tail {ι : Type*}
    {f : ι → SchwartzMap ℝ ℂ} (hf : SchwartzFamilyBounded f)
    (p : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ i,
      ‖schwartzToHermiteScale p (f i-compactSchwartzApproximation N (f i))‖ < ε := by
  obtain ⟨C,hC,hb⟩ := hf.native_cutoff_bound p
  have ht : Tendsto (fun N => compactSchwartzCutoffScale N*C) atTop (nhds 0) := by
    simpa only [zero_mul] using compactSchwartzCutoffScale_tendsto.mul_const C
  filter_upwards [ht.eventually (eventually_lt_nhds hε)] with N hN
  intro i
  exact (hb N i).trans_lt hN

/-- Budget J: one cutoff pays every order p≤M, every jet r≤12p, all bounded
centers and both Fourier signs in the actual original H_(6p) norm. -/
theorem exists_local_jet_spatial_budget (M : ℕ) (ψ : SchwartzMap ℝ ℂ)
    (δ H ε : ℝ) (hδ : 0 < δ) (hH : 0 ≤ H) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p ≤ M, ∀ r ≤ 12*p, ∀ inverse : Bool,
      ∀ (y : ℝ), |y| ≤ H →
      let f := if inverse then FourierTransform.fourierInvCLM ℂ (SchwartzMap ℝ ℂ)
        (localJetProbe ψ δ hδ r y)
        else FourierTransform.fourierCLM ℂ (SchwartzMap ℝ ℂ) (localJetProbe ψ δ hδ r y)
      ‖schwartzToHermiteScale (6*p) (f-compactSchwartzApproximation N f)‖ < ε := by
  have hf := (schwartzFamilyBounded_localJetProbes ψ δ H hδ hH (12*M)).fourier_signs
  have h := eventually_all.mpr (fun p : Fin (M+1) => hf.native_spatial_tail (6*p.val) ε hε)
  obtain ⟨N₀,hN⟩ := eventually_atTop.mp h
  refine ⟨N₀,fun N hNN p hp r hr inverse y hy => ?_⟩
  exact hN N hNN ⟨p,by omega⟩ (inverse,(⟨r,by omega⟩,⟨y,hy⟩))

/-- An actual derivative of Dirac, defined by iterating distributional differentiation. -/
def localDiracDerivative (r : ℕ) (y : ℝ) : TemperedDistribution ℝ ℂ :=
  (TemperedDistribution.derivCLM ℂ)^[r] (TemperedDistribution.delta y)

/-- The standard sign of a derivative of Dirac on every Schwartz test. -/
theorem localDiracDerivative_apply (r : ℕ) (y : ℝ) (f : SchwartzMap ℝ ℂ) :
    localDiracDerivative r y f = (-1:ℂ)^r*iteratedDeriv r (f : ℝ → ℂ) y := by
  induction r generalizing f with
  | zero => simp [localDiracDerivative,iteratedDeriv_zero]
  | succ r ih =>
    rw [localDiracDerivative,Function.iterate_succ_apply',TemperedDistribution.derivCLM_apply_apply]
    change localDiracDerivative r y (-SchwartzMap.derivCLM ℂ ℂ f) = _
    rw [ih]
    have he : ((-SchwartzMap.derivCLM ℂ ℂ f : SchwartzMap ℝ ℂ) : ℝ → ℂ) =
        fun x => -deriv (f : ℝ → ℂ) x := rfl
    rw [he,iteratedDeriv_fun_neg,← iteratedDeriv_succ',pow_succ]
    ring

private theorem normalized_monomial_jet (r n : ℕ) (y : ℝ) :
    iteratedDeriv n (fun x : ℝ => ((x-y:ℝ):ℂ)^r/(r.factorial:ℂ)) y =
      if n=r then 1 else 0 := by
  have he : (fun x : ℝ => ((x-y:ℝ):ℂ)^r/(r.factorial:ℂ)) =
      (fun x : ℝ => ((x-y)^r/(r.factorial:ℝ)) • (1:ℂ)) := by
    ext x
    simp [Complex.real_smul]
  rw [he,iteratedDeriv_smul_const (by fun_prop)]
  have hr : (fun x : ℝ => (x-y)^r/(r.factorial:ℝ)) =
      (1/(r.factorial:ℝ)) • (fun x : ℝ => (x-y)^r) := by ext x; simp only [Pi.smul_apply,smul_eq_mul]; ring
  rw [hr,iteratedDeriv_const_smul_field]
  have hp := congrFun (iteratedDeriv_comp_sub_const n (fun t : ℝ => t^r) y) y
  rw [hp]
  simp only [sub_self,iteratedDeriv_fun_pow_zero,smul_eq_mul]
  split_ifs with h
  · simp [Nat.factorial_ne_zero]
  · simp

/-- The factorial probe has Kronecker derivative jets at its center, at all orders. -/
theorem localJetProbe_derivative_center (ψ : SchwartzMap ℝ ℂ)
    (hψ : ∀ᶠ x : ℝ in nhds 0, ψ x = 1) (δ : ℝ) (hδ : 0 < δ) (r n : ℕ) (y : ℝ) :
    iteratedDeriv n (localJetProbe ψ δ hδ r y : ℝ → ℂ) y = if n=r then 1 else 0 := by
  have ht : Tendsto (fun x : ℝ => (x-y)/δ) (nhds y) (nhds 0) := by
    have hh : Continuous (fun x : ℝ => (x-y)/δ) := by fun_prop
    simpa only [sub_self,zero_div] using hh.tendsto y
  have he : (localJetProbe ψ δ hδ r y : ℝ → ℂ) =ᶠ[nhds y]
      (fun x : ℝ => ((x-y:ℝ):ℂ)^r/(r.factorial:ℂ)) := by
    filter_upwards [ht.eventually hψ] with x hx
    rw [localJetProbe_apply,hx,mul_one]
  rw [he.iteratedDeriv_eq n,normalized_monomial_jet]

/-- Exact coefficient reading and sign for the true derivative-of-Dirac source. -/
theorem localDiracDerivative_localJetProbe (ψ : SchwartzMap ℝ ℂ)
    (hψ : ∀ᶠ x : ℝ in nhds 0, ψ x = 1) (δ : ℝ) (hδ : 0 < δ) (r n : ℕ) (y : ℝ) :
    localDiracDerivative n y (localJetProbe ψ δ hδ r y) = if n=r then (-1:ℂ)^r else 0 := by
  rw [localDiracDerivative_apply,localJetProbe_derivative_center ψ hψ]
  split_ifs with h
  · simp [h]
  · simp

end
end MeyerGeneralProblem.Adaptive
