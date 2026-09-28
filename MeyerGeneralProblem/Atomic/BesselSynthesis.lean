module

public import MeyerGeneralProblem.Atomic.SupportSubspace
public import Mathlib.Analysis.InnerProductSpace.Adjoint
import all Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Operator.Extend
import all Mathlib.Analysis.Normed.Operator.Extend

@[expose] public section

/-!
# Bessel-family analysis and synthesis

This module packages the analytic content of a Bessel estimate as a continuous
analysis operator into the canonical coefficient space. Its Hilbert adjoint is
then the genuine infinite synthesis operator. The construction records the
coordinate formula, its action on basis atoms, and convergence of the
coefficient series; no summability assertion is hidden in a formal sum.
-/

namespace MeyerGeneralProblem

noncomputable section

open scoped lp

variable {ι H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Bundled Bessel data for a Hilbert-space family. The continuous analysis
map records precisely the analytic square-summability estimate; its `i`th
coordinate is the inner product against the `i`th family vector. -/
structure BesselAnalysis (v : ι → H) where
  /-- The bounded analysis operator into `ℓ²(ι, ℂ)`. -/
  toContinuousLinearMap : H →L[ℂ] CoefficientSpace ι
  /-- Coordinate identification of the analysis operator. -/
  coefficient : ∀ x i, toContinuousLinearMap x i = inner ℂ (v i) x

namespace BesselAnalysis

variable {v : ι → H}

/-- The finite Gram quadratic form of a Hilbert-space family.  Both sums run
over the support of the coefficient vector, so this scalar is defined before
any infinite synthesis operator exists. -/
def finsuppGramForm (v : ι → H) (c : ι →₀ ℂ) : ℂ :=
  c.sum fun j cj ↦
    cj * c.sum fun i ci ↦ starRingEnd ℂ ci * inner ℂ (v i) (v j)

omit [CompleteSpace H] in
/-- The norm of a finite atomic synthesis is exactly its finite Gram
quadratic form. -/
theorem norm_sq_finsupp_linearCombination_eq_gramForm_re
    (v : ι → H) (c : ι →₀ ℂ) :
    ‖Finsupp.linearCombination ℂ v c‖ ^ 2 =
      (finsuppGramForm v c).re := by
  rw [@norm_sq_eq_re_inner ℂ]
  simp only [finsuppGramForm, Finsupp.linearCombination_apply,
    Finsupp.sum_inner, Finsupp.inner_sum, inner_smul_left,
    inner_smul_right]
  rfl

/-- Parseval's identity for a finite linear combination of canonical
coefficient atoms.  Keeping this finite identity explicit lets later Schur
estimates compare atomic synthesis directly with the coefficient norm. -/
theorem norm_sq_finsupp_linearCombination_coefficientAtom
    [DecidableEq ι] (c : ι →₀ ℂ) :
    ‖Finsupp.linearCombination ℂ
        (coefficientAtom : ι → CoefficientSpace ι) c‖ ^ 2 =
      c.sum fun _ z ↦ ‖z‖ ^ 2 := by
  rw [@norm_sq_eq_re_inner ℂ]
  change Complex.re
      (inner ℂ
        (Finsupp.linearCombination ℂ (coefficientHilbertBasis ι) c)
        (Finsupp.linearCombination ℂ (coefficientHilbertBasis ι) c)) = _
  rw [(coefficientHilbertBasis ι).orthonormal.inner_finsupp_eq_sum_left]
  simp [Finsupp.sum, ← Complex.normSq_eq_conj_mul_self,
    Complex.normSq_eq_norm_sq]
  apply Finset.sum_congr rfl
  intro i hi
  norm_cast

/-- Construct Bessel data from the direct analytic statement that the
coefficient function belongs to `ℓ²` and obeys a uniform norm bound.  This is
the packaging step used after a sampling estimate has been proved; it does
not assume a pre-existing bounded analysis operator. -/
def of_norm_bound (v : ι → H) (C : ℝ)
    (hmem : ∀ x : H, Memℓp (fun i ↦ inner ℂ (v i) x) 2)
    (hbound : ∀ x : H,
      ‖(⟨fun i ↦ inner ℂ (v i) x, hmem x⟩ : CoefficientSpace ι)‖ ≤
        C * ‖x‖) :
    BesselAnalysis v where
  toContinuousLinearMap := LinearMap.mkContinuous
    { toFun := fun x ↦
        (⟨fun i ↦ inner ℂ (v i) x, hmem x⟩ : CoefficientSpace ι)
      map_add' := by
        intro x y
        ext i
        exact inner_add_right (v i) x y
      map_smul' := by
        intro c x
        ext i
        exact inner_smul_right (v i) x c }
    C hbound
  coefficient := by
    intro x i
    rfl

/-- Construct Bessel data from the customary squared coefficient estimate.
The summability hypothesis supplies an actual `ℓ²` vector, while the second
hypothesis is its uniform Bessel bound. -/
def of_tsum_norm_sq_le (v : ι → H) (C : ℝ) (hC : 0 ≤ C)
    (hsummable : ∀ x : H,
      Summable (fun i ↦ ‖inner ℂ (v i) x‖ ^ 2))
    (hbound : ∀ x : H,
      ∑' i, ‖inner ℂ (v i) x‖ ^ 2 ≤ C ^ 2 * ‖x‖ ^ 2) :
    BesselAnalysis v := by
  have hmem : ∀ x : H, Memℓp (fun i ↦ inner ℂ (v i) x) 2 := by
    intro x
    rw [memℓp_gen_iff (p := (2 : ENNReal)) (by norm_num)]
    simpa using hsummable x
  apply of_norm_bound v C hmem
  intro x
  let a : CoefficientSpace ι :=
    ⟨fun i ↦ inner ℂ (v i) x, hmem x⟩
  have ha : ‖a‖ ^ 2 = ∑' i, ‖inner ℂ (v i) x‖ ^ 2 := by
    simpa [a] using
      (lp.norm_rpow_eq_tsum
        (p := (2 : ENNReal)) (by norm_num) a)
  have hsquare : ‖a‖ ^ 2 ≤ (C * ‖x‖) ^ 2 := by
    rw [ha]
    nlinarith [hbound x]
  change ‖a‖ ≤ C * ‖x‖
  nlinarith [norm_nonneg a, mul_nonneg hC (norm_nonneg x)]

/-- Construct Bessel data from an upper synthesis inequality on finitely
supported coefficients.  The finite linear combination of coefficient atoms
has dense range in `ℓ²`; `LinearMap.extendOfNorm` therefore produces the
unique bounded synthesis operator, whose adjoint is the required analysis
map. -/
def of_finsupp_synthesis_bound [DecidableEq ι]
    (v : ι → H) (C : ℝ)
    (hbound : ∀ c : ι →₀ ℂ,
      ‖Finsupp.linearCombination ℂ v c‖ ≤
        C * ‖Finsupp.linearCombination ℂ
          (coefficientAtom : ι → CoefficientSpace ι) c‖) :
    BesselAnalysis v := by
  let e : (ι →₀ ℂ) →ₗ[ℂ] CoefficientSpace ι :=
    Finsupp.linearCombination ℂ coefficientAtom
  let f : (ι →₀ ℂ) →ₗ[ℂ] H :=
    Finsupp.linearCombination ℂ v
  have hdense : DenseRange e := by
    change Dense (Set.range e)
    rw [← LinearMap.coe_range]
    rw [Submodule.dense_iff_topologicalClosure_eq_top]
    change (LinearMap.range
      (Finsupp.linearCombination ℂ
        (coefficientAtom : ι → CoefficientSpace ι))).topologicalClosure = ⊤
    rw [Finsupp.range_linearCombination]
    exact coefficientAtom_dense_span
  let S : CoefficientSpace ι →L[ℂ] H := f.extendOfNorm e
  have hS (i : ι) : S (coefficientAtom i) = v i := by
    have he : e (Finsupp.single i 1) = coefficientAtom i := by
      simp [e, Finsupp.linearCombination_single]
    have hf : f (Finsupp.single i 1) = v i := by
      simp [f, Finsupp.linearCombination_single]
    rw [← he]
    change f.extendOfNorm e (e (Finsupp.single i 1)) = v i
    rw [LinearMap.extendOfNorm_eq hdense ⟨C, hbound⟩, hf]
  refine
    { toContinuousLinearMap := S.adjoint
      coefficient := ?_ }
  intro x i
  change (coefficientHilbertBasis ι).repr (S.adjoint x) i = inner ℂ (v i) x
  rw [(coefficientHilbertBasis ι).repr_apply_apply]
  rw [ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ (S (coefficientAtom i)) x = inner ℂ (v i) x
  rw [hS]

/-- Construct Bessel data from a finite Gram-form estimate.  The right-hand
side is the ordinary sum of squared coefficient moduli; finite Parseval turns
it into the squared `ℓ²` norm required by
`of_finsupp_synthesis_bound`. -/
def of_finsupp_norm_sq_bound [DecidableEq ι]
    (v : ι → H) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ c : ι →₀ ℂ,
      ‖Finsupp.linearCombination ℂ v c‖ ^ 2 ≤
        C ^ 2 * (c.sum fun _ z ↦ ‖z‖ ^ 2)) :
    BesselAnalysis v := by
  apply of_finsupp_synthesis_bound v C
  intro c
  have hparseval :=
    norm_sq_finsupp_linearCombination_coefficientAtom c
  have hsquare :
      ‖Finsupp.linearCombination ℂ v c‖ ^ 2 ≤
        (C * ‖Finsupp.linearCombination ℂ
          (coefficientAtom : ι → CoefficientSpace ι) c‖) ^ 2 := by
    rw [mul_pow, hparseval]
    exact hbound c
  nlinarith [norm_nonneg (Finsupp.linearCombination ℂ v c),
    norm_nonneg (Finsupp.linearCombination ℂ
      (coefficientAtom : ι → CoefficientSpace ι) c),
    mul_nonneg hC (norm_nonneg (Finsupp.linearCombination ℂ
      (coefficientAtom : ι → CoefficientSpace ι) c))]

/-- Construct Bessel data from an upper bound on the explicit finite Gram
quadratic form.  This is the scalar interface consumed by kernel estimates. -/
def of_finsupp_gram_bound [DecidableEq ι]
    (v : ι → H) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ c : ι →₀ ℂ,
      (finsuppGramForm v c).re ≤
        C ^ 2 * (c.sum fun _ z ↦ ‖z‖ ^ 2)) :
    BesselAnalysis v := by
  apply of_finsupp_norm_sq_bound v C hC
  intro c
  rw [norm_sq_finsupp_linearCombination_eq_gramForm_re]
  exact hbound c

/-- The synthesis operator of a Bessel family, defined as the Hilbert adjoint
of its analysis operator. -/
def synthesis (B : BesselAnalysis v) : CoefficientSpace ι →L[ℂ] H :=
  B.toContinuousLinearMap.adjoint

/-- Synthesis sends the canonical coefficient atom to the corresponding
family vector. -/
@[simp]
theorem synthesis_coefficientAtom (B : BesselAnalysis v) (i : ι) :
    B.synthesis (coefficientAtom i) = v i := by
  apply ext_inner_right ℂ
  intro x
  rw [synthesis, ContinuousLinearMap.adjoint_inner_left]
  change inner ℂ (coefficientHilbertBasis ι i) (B.toContinuousLinearMap x) = _
  rw [← (coefficientHilbertBasis ι).repr_apply_apply]
  change B.toContinuousLinearMap x i = _
  exact B.coefficient x i

/-- A lower finite Gram estimate for a Bessel family extends from finitely
supported coefficient vectors to all of `ℓ²`. -/
theorem synthesis_norm_sq_lower_of_finsuppGram
    [DecidableEq ι] (B : BesselAnalysis v) (A : ℝ)
    (hA : ∀ c : ι →₀ ℂ,
      A * (c.sum fun _ z => ‖z‖ ^ 2) ≤
        (finsuppGramForm v c).re)
    (c : CoefficientSpace ι) :
    A * ‖c‖ ^ 2 ≤ ‖B.synthesis c‖ ^ 2 := by
  let e : (ι →₀ ℂ) →ₗ[ℂ] CoefficientSpace ι :=
    Finsupp.linearCombination ℂ coefficientAtom
  have hdense : DenseRange e := by
    change Dense (Set.range e)
    rw [← LinearMap.coe_range]
    rw [Submodule.dense_iff_topologicalClosure_eq_top]
    change (LinearMap.range
      (Finsupp.linearCombination ℂ
        (coefficientAtom : ι → CoefficientSpace ι))).topologicalClosure = ⊤
    rw [Finsupp.range_linearCombination]
    exact coefficientAtom_dense_span
  refine DenseRange.induction_on
    (p := fun c : CoefficientSpace ι =>
      A * ‖c‖ ^ 2 ≤ ‖B.synthesis c‖ ^ 2) hdense c ?_ ?_
  · exact isClosed_le
      (continuous_const.mul (continuous_norm.pow 2))
      ((B.synthesis.continuous.norm).pow 2)
  · intro a
    have hmap :
        B.synthesis (e a) = Finsupp.linearCombination ℂ v a := by
      change B.synthesis
          (Finsupp.linearCombination ℂ coefficientAtom a) = _
      have hmap := LinearMap.map_finsupp_linearCombination
        (B.synthesis : CoefficientSpace ι →ₗ[ℂ] H)
        (g := (coefficientAtom : ι → CoefficientSpace ι)) a
      change (B.synthesis : CoefficientSpace ι →ₗ[ℂ] H)
          (Finsupp.linearCombination ℂ coefficientAtom a) = _
      rw [hmap]
      have hv :
          ((B.synthesis : CoefficientSpace ι →ₗ[ℂ] H) ∘
            (coefficientAtom : ι → CoefficientSpace ι)) = v := by
        funext i
        exact synthesis_coefficientAtom B i
      rw [hv]
    rw [hmap, norm_sq_finsupp_linearCombination_coefficientAtom]
    rw [norm_sq_finsupp_linearCombination_eq_gramForm_re]
    exact hA a

/-- Restrict a Bessel family along an injective reindexing.  The new synthesis
bound is inherited from the original synthesis operator, with finite Parseval
showing that extension by zero preserves the coefficient norm. -/
def reindex {κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (B : BesselAnalysis v) (f : κ ↪ ι) :
    BesselAnalysis (fun k => v (f k)) := by
  apply of_finsupp_synthesis_bound
    (fun k => v (f k)) ‖B.synthesis‖
  intro c
  let c' : ι →₀ ℂ := Finsupp.embDomain f c
  have hlin :
      Finsupp.linearCombination ℂ (fun k => v (f k)) c =
        Finsupp.linearCombination ℂ v c' := by
    simp only [Finsupp.linearCombination_apply]
    dsimp only [c']
    rw [Finsupp.sum_embDomain]
  have hcoeffSq :
      ‖Finsupp.linearCombination ℂ
          (coefficientAtom : ι → CoefficientSpace ι) c'‖ ^ 2 =
        ‖Finsupp.linearCombination ℂ
          (coefficientAtom : κ → CoefficientSpace κ) c‖ ^ 2 := by
    rw [norm_sq_finsupp_linearCombination_coefficientAtom,
      norm_sq_finsupp_linearCombination_coefficientAtom]
    dsimp only [c']
    rw [Finsupp.sum_embDomain]
  have hcoeff :
      ‖Finsupp.linearCombination ℂ
          (coefficientAtom : ι → CoefficientSpace ι) c'‖ =
        ‖Finsupp.linearCombination ℂ
          (coefficientAtom : κ → CoefficientSpace κ) c‖ := by
    nlinarith [norm_nonneg (Finsupp.linearCombination ℂ
      (coefficientAtom : ι → CoefficientSpace ι) c'),
      norm_nonneg (Finsupp.linearCombination ℂ
        (coefficientAtom : κ → CoefficientSpace κ) c)]
  have hsynth :
      B.synthesis (Finsupp.linearCombination ℂ
        (coefficientAtom : ι → CoefficientSpace ι) c') =
        Finsupp.linearCombination ℂ v c' := by
    have hmap := LinearMap.map_finsupp_linearCombination
      (B.synthesis : CoefficientSpace ι →ₗ[ℂ] H)
      (g := (coefficientAtom : ι → CoefficientSpace ι)) c'
    change (B.synthesis : CoefficientSpace ι →ₗ[ℂ] H)
        (Finsupp.linearCombination ℂ coefficientAtom c') = _
    rw [hmap]
    have hv :
        ((B.synthesis : CoefficientSpace ι →ₗ[ℂ] H) ∘
          (coefficientAtom : ι → CoefficientSpace ι)) = v := by
      funext i
      exact synthesis_coefficientAtom B i
    rw [hv]
  rw [hlin, ← hsynth]
  exact (B.synthesis.le_opNorm _).trans_eq
    (congrArg (‖B.synthesis‖ * ·) hcoeff)

/-- The coefficient series of a Bessel family converges in the Hilbert-space
norm to its synthesized vector. -/
theorem hasSum_synthesis (B : BesselAnalysis v) (c : CoefficientSpace ι) :
    HasSum (fun i => c i • v i) (B.synthesis c) := by
  have h := (coefficientHilbertBasis ι).hasSum_repr c
  have hmap := B.synthesis.hasSum h
  have hcoeff : ∀ i, (coefficientHilbertBasis ι).repr c i = c i := fun _ => rfl
  simp only [map_smul, hcoeff] at hmap
  change HasSum (fun i => c i • B.synthesis (coefficientAtom i))
    (B.synthesis c) at hmap
  simpa only [synthesis_coefficientAtom] using hmap

/-- Every synthesized vector belongs to the closed span of the Bessel
family. -/
theorem synthesis_mem_atomicSupportSubspace
    (B : BesselAnalysis v) (c : CoefficientSpace ι) :
    B.synthesis c ∈ atomicSupportSubspace v := by
  refine (isClosed_atomicSupportSubspace v).mem_of_tendsto
    (B.hasSum_synthesis c) (Filter.Eventually.of_forall fun s => ?_)
  exact Submodule.sum_mem (atomicSupportSubspace v) fun i hi =>
    (atomicSupportSubspace v).smul_mem (c i)
      (atom_mem_atomicSupportSubspace v i)

/-- Every Bessel synthesis obeys its operator-norm bound. -/
theorem norm_synthesis_le (B : BesselAnalysis v) (c : CoefficientSpace ι) :
    ‖B.synthesis c‖ ≤ ‖B.synthesis‖ * ‖c‖ :=
  B.synthesis.le_opNorm c

/-- The analysis and synthesis operator norms agree. -/
theorem norm_synthesis (B : BesselAnalysis v) :
    ‖B.synthesis‖ = ‖B.toContinuousLinearMap‖ := by
  rw [synthesis, LinearIsometryEquiv.norm_map]

end BesselAnalysis

end

end MeyerGeneralProblem
