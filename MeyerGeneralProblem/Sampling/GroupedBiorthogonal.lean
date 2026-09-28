module

public import MeyerGeneralProblem.Sampling.BeurlingBiorthogonal
public import MeyerGeneralProblem.Sampling.GroupedClusterInsertion

@[expose] public section

/-!
# Supported dual kernels for actual grouped exponential data

Continuous grouped exponentials define genuine vectors in the window Hilbert
space, including at collisions. For actual distinct cluster nodes their
pairings are exactly the analytic Newton data of the negative-sign Fourier
transform. A mixed lower inequality supplies dual kernels with no loss in
the number of exterior frequencies and no inverse internal gap estimate.
-/

namespace MeyerGeneralProblem

open MeasureTheory ComplexConjugate

noncomputable section

/-- The finite Hilbert dual construction is invariant under finite reindexing. -/
theorem exists_fintype_biorthogonal_of_lowerBound
    {ι H : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (v : ι → H) {A : ℝ} (hA : 0 < A)
    (hlower : ∀ c : ι → ℂ, A * ∑ i, ‖c i‖ ^ 2 ≤ ‖∑ i, c i • v i‖ ^ 2) :
    ∃ y : ι → H, (∀ i j, inner ℂ (y i) (v j) = if i = j then 1 else 0) ∧
      ∀ i, ‖y i‖ ≤ (Real.sqrt A)⁻¹ := by
  let e := Fintype.equivFin ι
  obtain ⟨y, hy, hn⟩ := exists_finite_biorthogonal_of_lowerBound
    (fun j => v (e.symm j)) hA (by
      intro c
      simpa only [← e.symm.sum_comp (fun i => ‖c (e i)‖ ^ 2),
        ← e.symm.sum_comp (fun i => c (e i) • v i), e.apply_symm_apply]
        using hlower (fun i => c (e i)))
  refine ⟨fun i => y (e i), ?_, fun i => hn (e i)⟩
  intro i j
  simpa using hy (e i) (e j)

theorem memLp_continuous_window (b : ℝ) (f : ℝ → ℂ) (hf : Continuous f) :
    MemLp f 2 (volume.restrict (Set.Icc (-b) b)) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf.continuousOn
  apply MemLp.of_bound hf.aestronglyMeasurable C
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact hC t ht

/-- A continuous time function as an actual vector on the prescribed window. -/
def continuousFourierWindowVector (b : ℝ) (f : ℝ → ℂ) (hf : Continuous f) :
    FourierWindowSpace b := (memLp_continuous_window b f hf).toLp f

/-- The vector represents precisely its original continuous function. -/
theorem continuousFourierWindowVector_coeFn (b : ℝ) (f : ℝ → ℂ) (hf : Continuous f) :
    (continuousFourierWindowVector b f hf : ℝ → ℂ) =ᵐ[
      volume.restrict (Set.Icc (-b) b)] f := (memLp_continuous_window b f hf).coeFn_toLp

/-- Exact norm-energy identity for any finite continuous family. -/
theorem continuousFourierWindowVector_sum_norm_sq
    {ι : Type*} [Fintype ι] (b : ℝ) (f : ι → ℝ → ℂ) (hf : ∀ i, Continuous (f i))
    (c : ι → ℂ) :
    ‖∑ i, c i • continuousFourierWindowVector b (f i) (hf i)‖ ^ 2 =
      ∫ t : ℝ in Set.Icc (-b) b, ‖∑ i, c i * f i t‖ ^ 2 := by
  rw [fourierWindowSpace_norm_sq]
  apply integral_congr_ae
  have hterms (i : ι) :
      (c i • continuousFourierWindowVector b (f i) (hf i) : FourierWindowSpace b) =ᵐ[
        volume.restrict (Set.Icc (-b) b)] fun t => c i * f i t := by
    filter_upwards [Lp.coeFn_smul (c i) (continuousFourierWindowVector b (f i) (hf i)),
      continuousFourierWindowVector_coeFn b (f i) (hf i)] with t ht hv
    simp only [ht, Pi.smul_apply, smul_eq_mul, hv]
  filter_upwards [Lp.coeFn_finsetSum Finset.univ
    (fun i => c i • continuousFourierWindowVector b (f i) (hf i)),
      Filter.eventually_all.2 hterms] with t ht hi
  simp only [ht, Finset.sum_apply, hi]

/-- Actual grouped window vector, defined also for repeated nodes. -/
def groupedFourierWindowVector {k : ℕ} (b : ℝ) (ω : Fin k → ℝ) (j : Fin k) :
    FourierWindowSpace b := continuousFourierWindowVector b
      (groupedExponentialInitial ω j) (continuous_groupedExponentialInitial ω j)

/-- Real nodes give real barycentric weights, with exact complex conjugation. -/
theorem conj_groupedNewtonWeight_real {k : ℕ} (ω : Fin k → ℝ) (j i : Fin k) :
    conj (groupedNewtonWeight (fun x => (ω x : ℂ)) j i) =
      groupedNewtonWeight (fun x => (ω x : ℂ)) j i := by
  unfold groupedNewtonWeight
  split_ifs <;> simp [Lagrange.nodalWeight, map_prod, map_inv₀, map_sub]

/-- At distinct nodes the actual grouped vector equals the exact barycentric
linear combination. This is only an identity, never a norm estimate. -/
theorem groupedFourierWindowVector_eq_sum {k : ℕ} (b : ℝ) (ω : Fin k → ℝ)
    (hω : Function.Injective ω) (j : Fin k) :
    groupedFourierWindowVector b ω j =
      ∑ i, groupedNewtonWeight (fun x => (ω x : ℂ)) j i • fourierWindowVector b (ω i) := by
  apply Lp.ext
  have ht (i : Fin k) := Lp.coeFn_smul
    (groupedNewtonWeight (fun x => (ω x : ℂ)) j i) (fourierWindowVector b (ω i))
  filter_upwards [continuousFourierWindowVector_coeFn b (groupedExponentialInitial ω j)
      (continuous_groupedExponentialInitial ω j),
    Lp.coeFn_finsetSum Finset.univ
      (fun i => groupedNewtonWeight (fun x => (ω x : ℂ)) j i • fourierWindowVector b (ω i)),
    Filter.eventually_all.2 ht,
    Filter.eventually_all.2 (fun i => fourierWindowVector_coeFn b (ω i))] with t hg hs ht hv
  change (continuousFourierWindowVector b _ _ : ℝ → ℂ) t = _
  simp only [hg, hs, Finset.sum_apply, ht, Pi.smul_apply, smul_eq_mul, hv]
  exact groupedExponentialInitial_eq_groupedNewtonWeights ω hω j t

/-- Exact negative-Fourier Newton data equals pairing with the positive
grouped exponential. No regularity of a representative of the L² vector is needed. -/
theorem analyticDividedDifference_fourierWindowKernel {k : ℕ}
    (b : ℝ) (ω : Fin k → ℝ) (hω : Function.Injective ω)
    (y : FourierWindowSpace b) (j : Fin k) :
    analyticDividedDifference (finiteNodeSequence ω) j
      (FourierTransform.fourier (fourierWindowKernel b y)) =
        inner ℂ (groupedFourierWindowVector b ω j) y := by
  rw [analyticDividedDifference_eq_dividedDifferences ω hω,
    dividedDifferences_eq_groupedNewtonWeights, groupedFourierWindowVector_eq_sum b ω hω,
    sum_inner]
  apply Finset.sum_congr rfl
  intro i hi
  rw [inner_smul_left, conj_groupedNewtonWeight_real, fourier_fourierWindowKernel]

/-- Supported L² kernels dual to the selected cluster, annihilating every
exterior frequency. The only analytic premise is the actual joint lower inequality. -/
theorem exists_supported_grouped_biorthogonal_of_lowerBound
    {n k : ℕ} {b : ℝ} (hb : 0 < b) (s : Fin n → ℝ) (ω : Fin k → ℝ)
    (hω : Function.Injective ω) {A : ℝ} (hA : 0 < A)
    (hlower : ∀ (c : Fin n → ℂ) (a : Fin k → ℂ),
      A * ((∑ i, ‖c i‖ ^ 2) + ∑ j, ‖a j‖ ^ 2) ≤
        ∫ t : ℝ in Set.Icc (-b) b,
          ‖gramFourierPolynomial s c t + groupedExponentialPolynomial ω a t‖ ^ 2) :
    ∃ ψ : Fin k → ℝ → ℂ,
      (∀ i, Integrable (ψ i)) ∧ (∀ i, MemLp (ψ i) 2 volume) ∧
      (∀ i, Function.support (ψ i) ⊆ Set.Icc (-b) b) ∧
      (∀ i j, FourierTransform.fourier (ψ i) (s j) = 0) ∧
      (∀ i j : Fin k, analyticDividedDifference (finiteNodeSequence ω) j
        (FourierTransform.fourier (ψ i)) = if i = j then 1 else 0) ∧
      ∀ i, (∫ t : ℝ, ‖ψ i t‖) ^ 2 ≤ 2 * b / A := by
  classical
  let f : Fin n ⊕ Fin k → ℝ → ℂ := Sum.elim (fun i => gramPhase (s i))
    (fun j => groupedExponentialInitial ω j)
  have hf : ∀ i, Continuous (f i) := by
    intro i
    cases i with
    | inl i => change Continuous (gramPhase (s i)); unfold gramPhase; fun_prop
    | inr j => exact continuous_groupedExponentialInitial ω j
  let v : Fin n ⊕ Fin k → FourierWindowSpace b := fun i =>
    continuousFourierWindowVector b (f i) (hf i)
  have hv₁ (i : Fin n) : v (Sum.inl i) = fourierWindowVector b (s i) := by
    apply Lp.ext
    exact (continuousFourierWindowVector_coeFn b _ _).trans
      (fourierWindowVector_coeFn b (s i)).symm
  have hv₂ (j : Fin k) : v (Sum.inr j) = groupedFourierWindowVector b ω j := rfl
  obtain ⟨y, hy, hn⟩ := exists_fintype_biorthogonal_of_lowerBound v hA (by
    intro c
    rw [continuousFourierWindowVector_sum_norm_sq]
    simpa only [Fintype.sum_sum_type, f, Sum.elim_inl, Sum.elim_inr,
      gramFourierPolynomial, groupedExponentialPolynomial] using
      hlower (fun i => c (Sum.inl i)) (fun j => c (Sum.inr j)))
  refine ⟨fun i => fourierWindowKernel b (y (Sum.inr i)),
    fun i => integrable_fourierWindowKernel b _,
    fun i => memLp_fourierWindowKernel b _,
    fun i => support_fourierWindowKernel_subset b _, ?_, ?_, ?_⟩
  · intro i j
    rw [fourier_fourierWindowKernel, ← hv₁, ← inner_conj_symm, hy]
    simp
  · intro i j
    rw [analyticDividedDifference_fourierWindowKernel b ω hω, ← hv₂,
      ← inner_conj_symm, hy]
    split_ifs <;> simp_all
  · intro i
    have h := integral_norm_fourierWindowKernel_sq_le hb (y (Sum.inr i))
    have hsquare := (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 (hn (Sum.inr i))
    rw [inv_pow, Real.sq_sqrt hA.le] at hsquare
    exact h.trans (by simpa only [div_eq_mul_inv] using
      mul_le_mul_of_nonneg_left hsquare (by positivity : 0 ≤ 2 * b))

end

end MeyerGeneralProblem
