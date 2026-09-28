module

public import MeyerGeneralProblem.Sampling.PositiveSeparation
public import MeyerGeneralProblem.Carrier.UniformDensity
public import MeyerGeneralProblem.Endpoint.ExponentialSqueeze
public import MeyerGeneralProblem.Gram.CompactPositivePerturbation

@[expose] public section

/-!
# The finite-window interface for the density-sharp Gram squeeze

This module does not assert Beurling's interpolation theorem.  It defines its
exact finite exponential lower-inequality output and proves the subsequent
infinite universal-Gram floor and normalization cancellation.  The supplied
window inequality is independent of Hermite order and of any Meyer endpoint
conclusion.  A separated cosine-Ingham family is a proved calibration.
-/

namespace MeyerGeneralProblem

open MeasureTheory ComplexConjugate Filter

noncomputable section

/-- A lower Riesz inequality on the actual interval `[-a,a]`, uniformly over
all finite subfamilies without repeated indices.  The exponential convention
is `exp(2 π i s η)`, exactly as in the retained Beurling source. -/
def HasFourierWindowLowerBound {ι : Type*} (s : ι → ℝ) (a A : ℝ) : Prop :=
  ∀ n : ℕ, ∀ e : Fin n → ι, Function.Injective e → ∀ c : Fin n → ℂ,
    A * ∑ i, ‖c i‖ ^ 2 ≤
      ∫ η : ℝ in Set.Icc (-a) a, ‖gramFourierPolynomial (s ∘ e) c η‖ ^ 2

/-- Restriction to an injectively indexed subfamily preserves the same
window and lower constant. -/
theorem HasFourierWindowLowerBound.comp
    {ι κ : Type*} {s : ι → ℝ} {a A : ℝ}
    (h : HasFourierWindowLowerBound s a A) (e : κ → ι) (he : Function.Injective e) :
    HasFourierWindowLowerBound (s ∘ e) a A := by
  intro n f hf c
  exact h n (e ∘ f) (he.comp hf) c

/-- The existing, proved cosine-Ingham inequality instantiates the same
window interface; no separate axiom is needed in the strict-gap case. -/
theorem hasFourierWindowLowerBound_of_cosineIngham
    {ι : Type*} (s : ι → ℝ) {a d : ℝ} (ha : 0 < a) (had : 1 < 2 * a * d)
    (hsep : ∀ i j, i ≠ j → d ≤ |s i - s j|) :
    HasFourierWindowLowerBound s a (cosineInghamFloorFactor a d) := by
  intro n e he c
  exact finite_cosineIngham ha had (s ∘ e)
    (fun i j hij => hsep (e i) (e j) (he.ne hij)) c

/-- The exact universal-Gram floor supplied by a lower window constant. -/
def beurlingWindowGramFloor (m : ℕ) (a A : ℝ) : ℝ :=
  2 * gramNormalization m * A * (1 + 4 * a ^ 2)⁻¹ ^ (2 * m)

theorem beurlingWindowGramFloor_pos {m : ℕ} (hm : 1 ≤ m)
    (a : ℝ) {A : ℝ} (hA : 0 < A) :
    0 < beurlingWindowGramFloor m a A := by
  unfold beurlingWindowGramFloor
  exact mul_pos (mul_pos (mul_pos (by norm_num) (gramNormalization_pos hm)) hA)
    (pow_pos (by positivity) _)

/-- Reindexing the finite source inequality transfers it to the universal
Gram form on an arbitrary finite subtype. -/
theorem HasFourierWindowLowerBound.finite_gram_lowerBound
    {ι κ : Type*} [Fintype κ] {s : ι → ℝ} {a A : ℝ}
    (h : HasFourierWindowLowerBound s a A)
    (e : κ → ι) (he : Function.Injective e)
    {m : ℕ} (hm : 1 ≤ m) (c : κ → ℂ) :
    beurlingWindowGramFloor m a A * ∑ i, ‖c i‖ ^ 2 ≤
      (∑ i, ∑ j, conj (c i) * c j *
        universalGramKernel m (s (e j) - s (e i))).re := by
  let f : κ ≃ Fin (Fintype.card κ) := Fintype.equivFin κ
  have hfin := universalGramKernel_lowerBound_of_windowFloor hm
    (s ∘ e ∘ f.symm) (c ∘ f.symm) a A
    (h _ (e ∘ f.symm) (he.comp f.symm.injective) (c ∘ f.symm))
  dsimp only [Function.comp_def] at hfin
  have hQ :
      (∑ i : Fin (Fintype.card κ), ∑ j : Fin (Fintype.card κ),
        conj (c (f.symm i)) * c (f.symm j) *
          universalGramKernel m (s (e (f.symm j)) - s (e (f.symm i)))) =
      ∑ i : κ, ∑ j : κ, conj (c i) * c j *
        universalGramKernel m (s (e j) - s (e i)) := by
    calc
      _ = ∑ i : Fin (Fintype.card κ), ∑ j : κ,
          conj (c (f.symm i)) * c j *
            universalGramKernel m (s (e j) - s (e (f.symm i))) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact f.symm.sum_comp (fun j : κ =>
          conj (c (f.symm i)) * c j *
            universalGramKernel m (s (e j) - s (e (f.symm i))))
      _ = _ := f.symm.sum_comp (fun i : κ => ∑ j : κ,
        conj (c i) * c j * universalGramKernel m (s (e j) - s (e i)))
  have hE : (∑ i : Fin (Fintype.card κ), ‖c (f.symm i)‖ ^ 2) =
      ∑ i : κ, ‖c i‖ ^ 2 := f.symm.sum_comp (fun i : κ => ‖c i‖ ^ 2)
  rw [hQ, hE] at hfin
  exact hfin

/-- The finite source lower inequality bounds every finitely supported
universal-atom synthesis. -/
theorem HasFourierWindowLowerBound.finsupp_gram_lowerBound
    {ι : Type*} [DecidableEq ι] {s : ι → ℝ} {a A : ℝ}
    (h : HasFourierWindowLowerBound s a A) {m : ℕ} (hm : 1 ≤ m)
    (c : ι →₀ ℂ) :
    beurlingWindowGramFloor m a A * (c.sum fun _ z => ‖z‖ ^ 2) ≤
      (BesselAnalysis.finsuppGramForm
        (fun i => universalGramAtom m hm (s i)) c).re := by
  let σ := {i : ι // i ∈ c.support}
  have hfin := h.finite_gram_lowerBound
    (Subtype.val : σ → ι) Subtype.val_injective hm (fun i : σ => c i)
  rw [finsuppGramForm_universalGramAtom]
  simp only [Finsupp.sum]
  have houter :
      (∑ j ∈ c.support, c j * ∑ i ∈ c.support,
        conj (c i) * universalGramKernel m (s j - s i)) =
      ∑ j : σ, c j * ∑ i : σ, conj (c i) * universalGramKernel m (s j - s i) := by
    calc
      _ = ∑ j ∈ c.support, c j * ∑ i : σ,
          conj (c i) * universalGramKernel m (s j - s i) := by
        apply Finset.sum_congr rfl
        intro j hj
        congr 1
        exact Finset.sum_subtype c.support (fun _ => Iff.rfl) _
      _ = _ := Finset.sum_subtype c.support (fun _ => Iff.rfl) _
  have henergy : (∑ i ∈ c.support, ‖c i‖ ^ 2) = ∑ i : σ, ‖c i‖ ^ 2 :=
    Finset.sum_subtype c.support (fun _ => Iff.rfl) _
  rw [houter, henergy]
  apply hfin.trans_eq
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The finite window inequality gives a lower floor for the full infinite
universal Gram operator constructed under positive separation alone. -/
theorem positiveSeparatedUniversalGramOperator_lowerBound_of_window
    {ι : Type*} [DecidableEq ι] {m : ℕ} (hm : 1 ≤ m)
    (s : ι → ℝ) {d : ℝ} (hd : 0 < d)
    (hsep : ∀ i j, i ≠ j → d ≤ |s i - s j|)
    {a A : ℝ} (hwindow : HasFourierWindowLowerBound s a A) :
    beurlingWindowGramFloor m a A • (1 : CoefficientSpace ι →L[ℂ] CoefficientSpace ι) ≤
      positiveSeparatedUniversalGramOperator hm s hd hsep := by
  let B := positiveSeparatedUniversalGramBesselAnalysis hm s hd hsep
  let S := B.synthesis
  have hlower (c : CoefficientSpace ι) :
      beurlingWindowGramFloor m a A * ‖c‖ ^ 2 ≤ ‖S c‖ ^ 2 := by
    apply B.synthesis_norm_sq_lower_of_finsuppGram
    exact hwindow.finsupp_gram_lowerBound hm
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
    change 0 ≤ RCLike.re (inner ℂ
      ((coefficientGram S - beurlingWindowGramFloor m a A • 1) c) c)
    rw [sub_apply, inner_sub_left, map_sub]
    simp only [coefficientGram, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.adjoint_inner_left, one_apply_eq_self, smul_apply]
    rw [← norm_sq_eq_re_inner, RCLike.real_smul_eq_coe_smul (K := ℂ),
      inner_smul_real_left, RCLike.smul_re, ← norm_sq_eq_re_inner]
    linarith [hlower c]

/-- A positive source lower constant makes the full universal Gram strictly
positive, hence suitable for the existing whitening infrastructure. -/
theorem positiveSeparatedUniversalGramOperator_strictlyPositive_of_window
    {ι : Type*} [DecidableEq ι] [Nontrivial (CoefficientSpace ι)]
    {m : ℕ} (hm : 1 ≤ m) (s : ι → ℝ) {d : ℝ} (hd : 0 < d)
    (hsep : ∀ i j, i ≠ j → d ≤ |s i - s j|)
    {a A : ℝ} (hA : 0 < A) (hwindow : HasFourierWindowLowerBound s a A) :
    IsStrictlyPositive (positiveSeparatedUniversalGramOperator hm s hd hsep) :=
  strictlyPositive_of_positive_scalar_floor _ (beurlingWindowGramFloor_pos hm a hA)
    (positiveSeparatedUniversalGramOperator_lowerBound_of_window hm s hd hsep hwindow)

/-- The purely numerical density hypothesis chooses a legal window.  The
separate interpolation theorem is still needed to produce its lower bound. -/
theorem exists_subcritical_density_window (S : LocallyFiniteCarrier)
    (hS : upperUniformBeurlingDensity S < 1) :
    ∃ a : ℝ, 0 < a ∧ a < 1 / 2 ∧
      upperUniformBeurlingDensity S < ENNReal.ofReal (2 * a) := by
  obtain ⟨z, hSz, hz1⟩ := exists_between hS
  have hztop : z ≠ (⊤ : ENNReal) := ne_of_lt (hz1.trans_le le_top)
  have hr0 : 0 ≤ z.toReal := ENNReal.toReal_nonneg
  have hr1 : z.toReal < 1 := by
    have h := (ENNReal.toReal_lt_toReal hztop ENNReal.one_ne_top).2 hz1
    simpa using h
  refine ⟨(z.toReal + 1) / 4, by positivity, by linarith, ?_⟩
  apply hSz.trans
  calc
    z = ENNReal.ofReal z.toReal := (ENNReal.ofReal_toReal hztop).symm
    _ < ENNReal.ofReal (2 * ((z.toReal + 1) / 4)) :=
      (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by linarith)

/-- The exact ratio after cancelling the common normalization, with a
general positive window constant in place of the cosine-Ingham factor. -/
def beurlingWindowSqueezeRatio (m : ℕ) (C a A : ℝ) : ℝ :=
  (C / (2 * A)) * (m + 1) * (((1 + 4 * a ^ 2) ^ 2) / 4) ^ m

theorem leadingCrossCeiling_eq_beurlingWindowFloor_mul_ratio
    {m : ℕ} (hm : 1 ≤ m) {C a A : ℝ} (hA : A ≠ 0) :
    leadingCrossCeiling m C (gramNormalization m) =
      beurlingWindowGramFloor m a A * beurlingWindowSqueezeRatio m C a A := by
  have hc := (gramNormalization_pos hm).ne'
  have hb : 1 + 4 * a ^ 2 ≠ 0 := by positivity
  unfold leadingCrossCeiling beurlingWindowGramFloor beurlingWindowSqueezeRatio
  rw [div_pow, pow_mul]
  field_simp [hc, hA, hb]
  have hfour : (1 / 4 : ℝ) ^ m * 4 ^ m = 1 := by
    rw [div_eq_mul_inv, one_mul, ← mul_pow, inv_mul_cancel₀ (by norm_num), one_pow]
  have hbpow : (1 + 4 * a ^ 2) ^ 2 ≠ 0 := pow_ne_zero _ hb
  have hden : (1 / (1 + 4 * a ^ 2) ^ 2) ^ m * ((1 + 4 * a ^ 2) ^ 2) ^ m = 1 := by
    rw [div_eq_mul_inv, one_mul, ← mul_pow, inv_mul_cancel₀ hbpow, one_pow]
  calc
    C * (1 / 4) ^ m * 4 ^ m = C := by rw [mul_assoc, hfour, mul_one]
    _ = C * ((1 / (1 + 4 * a ^ 2) ^ 2) ^ m * ((1 + 4 * a ^ 2) ^ 2) ^ m) := by
      rw [hden, mul_one]
    _ = _ := by ring

theorem leadingCrossCeiling_div_beurlingWindowFloor
    {m : ℕ} (hm : 1 ≤ m) {C a A : ℝ} (hA : 0 < A) :
    leadingCrossCeiling m C (gramNormalization m) / beurlingWindowGramFloor m a A =
      beurlingWindowSqueezeRatio m C a A := by
  rw [leadingCrossCeiling_eq_beurlingWindowFloor_mul_ratio hm hA.ne']
  exact mul_div_cancel_left₀ _ (beurlingWindowGramFloor_pos hm a hA).ne'

/-- Every fixed lower window constant is compatible with the eventual
endpoint squeeze whenever its half-width is strictly below one half. -/
theorem eventually_beurlingWindowSqueezeRatio_lt_one
    (C A : ℝ) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1 / 2) :
    ∀ᶠ m : ℕ in atTop, beurlingWindowSqueezeRatio m C a A < 1 := by
  exact (linear_mul_geometric_tendsto_zero (C / (2 * A))
    (((1 + 4 * a ^ 2) ^ 2) / 4)
    (endpointSqueezeBase_nonneg a) (endpointSqueezeBase_lt_one ha0 ha1)).eventually_lt_const
    zero_lt_one

/-- The actual cross-ceiling/Gram-floor quotient is eventually below one
for every positive window lower constant at a subcritical half-width. -/
theorem eventually_leadingCrossCeiling_div_beurlingWindowFloor_lt_one
    (C : ℝ) {a A : ℝ} (hA : 0 < A) (ha0 : 0 ≤ a) (ha1 : a < 1 / 2) :
    ∀ᶠ m : ℕ in atTop, ∀ _hm : 1 ≤ m,
      leadingCrossCeiling m C (gramNormalization m) / beurlingWindowGramFloor m a A < 1 := by
  filter_upwards [eventually_beurlingWindowSqueezeRatio_lt_one C A ha0 ha1] with m hm
  intro hmpos
  rwa [leadingCrossCeiling_div_beurlingWindowFloor hmpos hA]

end

end MeyerGeneralProblem
