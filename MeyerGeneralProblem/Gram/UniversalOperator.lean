module

public import MeyerGeneralProblem.Sampling.UpperLargeSieve
public import MeyerGeneralProblem.Atomic.BesselSynthesis
public import MeyerGeneralProblem.Gram.CoefficientModel
public import Mathlib.MeasureTheory.Function.L2Space
import all Mathlib.MeasureTheory.Function.L2Space

@[expose] public section

/-!
# Bounded universal Gram operator

The rational density is realized as a square-root-density family in `L²`.
The global upper large-sieve estimate constructs its bounded synthesis and
Gram operator, while the finite cosine-window inequality extends by density
to a uniform Loewner lower bound on the whole coefficient space.
-/

namespace MeyerGeneralProblem

open MeasureTheory ComplexConjugate

noncomputable section

/-- Square-root-density Fourier atom realizing the universal Gram kernel. -/
def universalGramAtomFun (m : ℕ) (t η : ℝ) : ℂ :=
  (Real.sqrt (gramDensity m η) : ℂ) * gramPhase t η

theorem memLp_universalGramAtomFun
    {m : ℕ} (hm : 1 ≤ m) (t : ℝ) :
    MemLp (universalGramAtomFun m t) 2 (volume : Measure ℝ) := by
  apply (memLp_two_iff_integrable_sq_norm (by
    apply Continuous.aestronglyMeasurable
    unfold universalGramAtomFun
    apply Continuous.mul
    · apply Complex.continuous_ofReal.comp
      apply Continuous.sqrt
      unfold gramDensity rawGramDensity
      apply continuous_const.mul
      apply Continuous.rpow_const (by fun_prop)
      intro η
      left
      positivity
    · unfold gramPhase
      fun_prop)).2
  convert integrable_gramDensity hm using 1
  funext η
  unfold universalGramAtomFun
  rw [norm_mul, norm_gramPhase, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (gramDensity_nonneg hm η)]

/-- The universal kernel atom as an actual vector of `L²(ℝ)`. -/
def universalGramAtom (m : ℕ) (hm : 1 ≤ m) (t : ℝ) :
    Lp ℂ 2 (volume : Measure ℝ) :=
  (memLp_universalGramAtomFun hm t).toLp (universalGramAtomFun m t)

/-- The `L²` atoms have exactly the universal kernel as their Gram entries. -/
theorem inner_universalGramAtom
    {m : ℕ} (hm : 1 ≤ m) (s t : ℝ) :
    inner ℂ (universalGramAtom m hm s) (universalGramAtom m hm t) =
      universalGramKernel m (t - s) := by
  rw [MeasureTheory.L2.inner_def, universalGramKernel]
  apply integral_congr_ae
  filter_upwards
    [(memLp_universalGramAtomFun hm s).coeFn_toLp,
      (memLp_universalGramAtomFun hm t).coeFn_toLp] with η hs ht
  unfold universalGramAtom
  rw [hs, ht]
  unfold universalGramAtomFun
  rw [RCLike.inner_apply, map_mul, Complex.conj_ofReal, gramPhase_sub]
  have hsqrt :
      ((Real.sqrt (gramDensity m η) : ℂ) *
          (Real.sqrt (gramDensity m η) : ℂ)) =
        (gramDensity m η : ℂ) := by
    norm_cast
    simpa only [pow_two] using Real.sq_sqrt (gramDensity_nonneg hm η)
  calc
    (Real.sqrt (gramDensity m η) : ℂ) * gramPhase t η *
          ((Real.sqrt (gramDensity m η) : ℂ) * conj (gramPhase s η)) =
        ((Real.sqrt (gramDensity m η) : ℂ) *
          (Real.sqrt (gramDensity m η) : ℂ)) *
            (conj (gramPhase s η) * gramPhase t η) := by ring
    _ = (gramDensity m η : ℂ) *
        (conj (gramPhase s η) * gramPhase t η) := by rw [hsqrt]

/-- The finite Gram form of the universal atoms is the universal kernel
quadratic form on the coefficient support. -/
theorem finsuppGramForm_universalGramAtom
    {ι : Type*} [DecidableEq ι] {m : ℕ} (hm : 1 ≤ m)
    (x : ι → ℝ) (c : ι →₀ ℂ) :
    BesselAnalysis.finsuppGramForm
        (fun i => universalGramAtom m hm (x i)) c =
      c.sum fun j cj => cj * c.sum fun i ci =>
        conj ci * universalGramKernel m (x j - x i) := by
  unfold BesselAnalysis.finsuppGramForm
  apply Finsupp.sum_congr
  intro j hj
  congr 1
  apply Finsupp.sum_congr
  intro i hi
  rw [inner_universalGramAtom]

/-- Uniform finite-support upper Gram estimate for universal atoms indexed by
an arbitrary separated type. -/
theorem finsuppGramForm_universalGramAtom_re_le
    {ι : Type*} [DecidableEq ι] {m : ℕ} (hm : 1 ≤ m)
    {d : ℝ} (hd : 1 < d) (x : ι → ℝ)
    (hsep : ∀ i j, i ≠ j → d ≤ |x i - x j|) (c : ι →₀ ℂ) :
    (BesselAnalysis.finsuppGramForm
        (fun i => universalGramAtom m hm (x i)) c).re ≤
      universalGramLargeSieveConstant m d *
        (c.sum fun _ z => ‖z‖ ^ 2) := by
  let σ := {i : ι // i ∈ c.support}
  let xs : σ → ℝ := fun i => x i
  let cs : σ → ℂ := fun i => c i
  have hsepσ : ∀ i j : σ, i ≠ j → d ≤ |xs i - xs j| := by
    intro i j hij
    apply hsep
    exact Subtype.coe_injective.ne hij
  have hfin := universalGramKernel_quadratic_re_le_of_finite_separated
    hm hd xs hsepσ cs
  rw [finsuppGramForm_universalGramAtom]
  simp only [Finsupp.sum]
  have houter :
      (∑ j ∈ c.support,
          c j * ∑ i ∈ c.support,
            conj (c i) * universalGramKernel m (x j - x i)) =
        ∑ j : σ, c j * ∑ i : σ,
          conj (c i) * universalGramKernel m (x j - x i) := by
    calc
      (∑ j ∈ c.support,
          c j * ∑ i ∈ c.support,
            conj (c i) * universalGramKernel m (x j - x i)) =
          ∑ j ∈ c.support, c j * ∑ i : σ,
            conj (c i) * universalGramKernel m (x j - x i) := by
        apply Finset.sum_congr rfl
        intro j hj
        congr 1
        exact Finset.sum_subtype c.support (fun _ => Iff.rfl)
          (fun i => conj (c i) * universalGramKernel m (x j - x i))
      _ = ∑ j : σ, c j * ∑ i : σ,
          conj (c i) * universalGramKernel m (x j - x i) :=
        Finset.sum_subtype c.support (fun _ => Iff.rfl)
          (fun j => c j * ∑ i : σ,
            conj (c i) * universalGramKernel m (x j - x i))
  rw [houter]
  have henergy :
      (∑ i ∈ c.support, ‖c i‖ ^ 2) = ∑ i : σ, ‖c i‖ ^ 2 :=
    Finset.sum_subtype c.support (fun _ => Iff.rfl)
      (fun i => ‖c i‖ ^ 2)
  rw [henergy]
  dsimp only [xs, cs] at hfin
  calc
    (∑ j : σ, c j * ∑ i : σ,
        conj (c i) * universalGramKernel m (x j - x i)).re =
        (∑ i : σ, ∑ j : σ,
          conj (c i) * c j * universalGramKernel m (x j - x i)).re := by
      congr 1
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ ≤ universalGramLargeSieveConstant m d * ∑ i : σ, ‖c i‖ ^ 2 := hfin

/-- Bessel data for an arbitrary separated universal-kernel family. -/
def universalGramBesselAnalysis
    {ι : Type*} [DecidableEq ι] {m : ℕ} (hm : 1 ≤ m)
    {d : ℝ} (hd : 1 < d) (x : ι → ℝ)
    (hsep : ∀ i j, i ≠ j → d ≤ |x i - x j|) :
    BesselAnalysis (fun i => universalGramAtom m hm (x i)) :=
  BesselAnalysis.of_finsupp_gram_bound
    (fun i => universalGramAtom m hm (x i))
    (Real.sqrt (universalGramLargeSieveConstant m d))
    (Real.sqrt_nonneg _) (by
      intro c
      rw [Real.sq_sqrt (universalGramLargeSieveConstant_nonneg hm d)]
      exact finsuppGramForm_universalGramAtom_re_le hm hd x hsep c)

/-- Synthesis of a separated universal-kernel family. -/
def universalGramSynthesis
    {ι : Type*} [DecidableEq ι] {m : ℕ} (hm : 1 ≤ m)
    {d : ℝ} (hd : 1 < d) (x : ι → ℝ)
    (hsep : ∀ i j, i ≠ j → d ≤ |x i - x j|) :
    CoefficientSpace ι →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  (universalGramBesselAnalysis hm hd x hsep).synthesis

/-- Bounded universal Gram operator for a separated family. -/
def universalGramOperator
    {ι : Type*} [DecidableEq ι] {m : ℕ} (hm : 1 ≤ m)
    {d : ℝ} (hd : 1 < d) (x : ι → ℝ)
    (hsep : ∀ i j, i ≠ j → d ≤ |x i - x j|) :
    CoefficientSpace ι →L[ℂ] CoefficientSpace ι :=
  coefficientGram (universalGramSynthesis hm hd x hsep)

/-- Matrix entries of the bounded universal Gram operator are the universal
kernel values. -/
theorem universalGramOperator_entry
    {ι : Type*} [DecidableEq ι] {m : ℕ} (hm : 1 ≤ m)
    {d : ℝ} (hd : 1 < d) (x : ι → ℝ)
    (hsep : ∀ i j, i ≠ j → d ≤ |x i - x j|) (i j : ι) :
    inner ℂ (coefficientAtom i)
        (universalGramOperator hm hd x hsep (coefficientAtom j)) =
      universalGramKernel m (x j - x i) := by
  rw [universalGramOperator, coefficientGram,
    ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right,
    universalGramSynthesis,
    BesselAnalysis.synthesis_coefficientAtom,
    BesselAnalysis.synthesis_coefficientAtom,
    inner_universalGramAtom]

/-- Uniform finite-support lower Gram estimate for universal atoms indexed by
an arbitrary separated type. -/
theorem universalGramAtom_finsupp_lowerBound
    {ι : Type*} [DecidableEq ι] {a d : ℝ} (ha : 0 < a)
    (had : 1 < 2 * a * d) {m : ℕ} (hm : 1 ≤ m)
    (x : ι → ℝ) (hsep : ∀ i j, i ≠ j → d ≤ |x i - x j|)
    (c : ι →₀ ℂ) :
    universalGramLowerConstant m a d *
        (c.sum fun _ z => ‖z‖ ^ 2) ≤
      (BesselAnalysis.finsuppGramForm
        (fun i => universalGramAtom m hm (x i)) c).re := by
  let σ := {i : ι // i ∈ c.support}
  let xs : σ → ℝ := fun i => x i
  let cs : σ → ℂ := fun i => c i
  have hsepσ : ∀ i j : σ, i ≠ j → d ≤ |xs i - xs j| := by
    intro i j hij
    apply hsep
    exact Subtype.coe_injective.ne hij
  have hfin := universalGramKernel_quadratic_re_ge_of_finite_separated
    ha had hm xs hsepσ cs
  rw [finsuppGramForm_universalGramAtom]
  simp only [Finsupp.sum]
  have houter :
      (∑ j ∈ c.support,
          c j * ∑ i ∈ c.support,
            conj (c i) * universalGramKernel m (x j - x i)) =
        ∑ j : σ, c j * ∑ i : σ,
          conj (c i) * universalGramKernel m (x j - x i) := by
    calc
      (∑ j ∈ c.support,
          c j * ∑ i ∈ c.support,
            conj (c i) * universalGramKernel m (x j - x i)) =
          ∑ j ∈ c.support, c j * ∑ i : σ,
            conj (c i) * universalGramKernel m (x j - x i) := by
        apply Finset.sum_congr rfl
        intro j hj
        congr 1
        exact Finset.sum_subtype c.support (fun _ => Iff.rfl)
          (fun i => conj (c i) * universalGramKernel m (x j - x i))
      _ = ∑ j : σ, c j * ∑ i : σ,
          conj (c i) * universalGramKernel m (x j - x i) :=
        Finset.sum_subtype c.support (fun _ => Iff.rfl)
          (fun j => c j * ∑ i : σ,
            conj (c i) * universalGramKernel m (x j - x i))
  rw [houter]
  have henergy :
      (∑ i ∈ c.support, ‖c i‖ ^ 2) = ∑ i : σ, ‖c i‖ ^ 2 :=
    Finset.sum_subtype c.support (fun _ => Iff.rfl)
      (fun i => ‖c i‖ ^ 2)
  rw [henergy]
  dsimp only [xs, cs] at hfin
  calc
    universalGramLowerConstant m a d * ∑ i : σ, ‖c i‖ ^ 2 ≤
        (∑ i : σ, ∑ j : σ,
          conj (c i) * c j *
            universalGramKernel m (x j - x i)).re := hfin
    _ = (∑ j : σ, c j * ∑ i : σ,
        conj (c i) * universalGramKernel m (x j - x i)).re := by
      congr 1
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring

/-- The bounded universal Gram operator has the uniform Loewner lower floor
delivered by the finite cosine-window argument. -/
theorem universalGramOperator_lowerBound
    {ι : Type*} [DecidableEq ι] {a d : ℝ} (ha : 0 < a)
    (had : 1 < 2 * a * d) (hd : 1 < d) {m : ℕ} (hm : 1 ≤ m)
    (x : ι → ℝ) (hsep : ∀ i j, i ≠ j → d ≤ |x i - x j|) :
    universalGramLowerConstant m a d •
        (1 : CoefficientSpace ι →L[ℂ] CoefficientSpace ι) ≤
      universalGramOperator hm hd x hsep := by
  let B := universalGramBesselAnalysis hm hd x hsep
  let S := B.synthesis
  have hlower (c : CoefficientSpace ι) :
      universalGramLowerConstant m a d * ‖c‖ ^ 2 ≤ ‖S c‖ ^ 2 := by
    apply B.synthesis_norm_sq_lower_of_finsuppGram
    exact universalGramAtom_finsupp_lowerBound ha had hm x hsep
  rw [ContinuousLinearMap.le_def]
  apply ContinuousLinearMap.isPositive_def'.mpr
  constructor
  · apply IsSelfAdjoint.sub
    · exact (ContinuousLinearMap.isPositive_adjoint_comp_self S).isSelfAdjoint
    · apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
      intro u v
      simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.one_apply]
      have hreal (c : ℝ) (w : CoefficientSpace ι) : c • w = (c : ℂ) • w := by
        ext i
        simp only [lp.coeFn_smul, Pi.smul_apply]
        exact RCLike.real_smul_eq_coe_smul (K := ℂ) c (w i)
      rw [hreal, hreal]
      exact (inner_smul_real_left (𝕜 := ℂ) u v _).trans
        (inner_smul_real_right (𝕜 := ℂ) u v _).symm
  · intro c
    change 0 ≤ RCLike.re
      (inner ℂ
        ((coefficientGram S - universalGramLowerConstant m a d • 1) c) c)
    rw [sub_apply, inner_sub_left, map_sub]
    simp only [coefficientGram, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.adjoint_inner_left, one_apply_eq_self, smul_apply]
    rw [← norm_sq_eq_re_inner]
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
    rw [inner_smul_real_left, RCLike.smul_re]
    rw [← norm_sq_eq_re_inner]
    linarith [hlower c]

end

end MeyerGeneralProblem
