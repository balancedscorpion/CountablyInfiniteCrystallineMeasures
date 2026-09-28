module

public import MeyerGeneralProblem.Cardinal.Adaptive.PolynomialSublevel
public import MeyerGeneralProblem.Cardinal.Adaptive.PhaseClosure

@[expose] public section

/-!
# Exact polynomial normalization of reciprocal linear sums

Multiplication by the product of all distinct scale variables gives a literal
multiquadratic polynomial. The forward and reciprocal monomials are pairwise
distinct, so the original coefficients are recovered without cancellation.
-/

namespace MeyerGeneralProblem.Adaptive

noncomputable section
open MeasureTheory Set
open scoped ENNReal

/-- A linear sum in the actual forward and reciprocal scale variables. -/
def reciprocalLaurentValue {q : ℕ} (a b : Fin q → ℝ) (x : Fin q → ℝ) : ℝ :=
  ∑ i, (a i * x i + b i * (x i)⁻¹)

/-- Exponent vector for a forward term after clearing one copy of every denominator. -/
def forwardExponent {q : ℕ} (i : Fin q) : Fin q → Fin 3 := fun j => if j = i then 2 else 1

/-- Exponent vector for a reciprocal term after clearing every denominator. -/
def reciprocalExponent {q : ℕ} (i : Fin q) : Fin q → Fin 3 := fun j => if j = i then 0 else 1

theorem forwardExponent_injective {q : ℕ} : Function.Injective (@forwardExponent q) := by
  intro i j h
  by_contra hij
  have h' := congrFun h i
  simp [forwardExponent, hij] at h'

theorem reciprocalExponent_injective {q : ℕ} : Function.Injective (@reciprocalExponent q) := by
  intro i j h
  by_contra hij
  have h' := congrFun h i
  simp [reciprocalExponent, hij] at h'

theorem forwardExponent_ne_reciprocalExponent {q : ℕ} (i j : Fin q) :
    forwardExponent i ≠ reciprocalExponent j := by
  intro h
  have h' := congrFun h i
  by_cases hij : i = j <;> simp [forwardExponent, reciprocalExponent, hij] at h'

/-- The full finite table of actual polynomial coefficients after denominator clearing. -/
def reciprocalLaurentCoefficients {q : ℕ} (a b : Fin q → ℝ) (k : Fin q → Fin 3) : ℝ :=
  ∑ i, ((if k = forwardExponent i then a i else 0) +
    (if k = reciprocalExponent i then b i else 0))

theorem reciprocalLaurentCoefficients_forward {q : ℕ} (a b : Fin q → ℝ) (i : Fin q) :
    reciprocalLaurentCoefficients a b (forwardExponent i) = a i := by
  simp [reciprocalLaurentCoefficients, forwardExponent_injective.eq_iff,
    forwardExponent_ne_reciprocalExponent]

theorem reciprocalLaurentCoefficients_reciprocal {q : ℕ} (a b : Fin q → ℝ) (i : Fin q) :
    reciprocalLaurentCoefficients a b (reciprocalExponent i) = b i := by
  have hne : ∀ j : Fin q, reciprocalExponent i ≠ forwardExponent j :=
    fun j => (forwardExponent_ne_reciprocalExponent j i).symm
  simp [reciprocalLaurentCoefficients, reciprocalExponent_injective.eq_iff, hne]

/-- No hidden cancellations: the cleared polynomial has zero coefficients exactly for zero input. -/
theorem reciprocalLaurentCoefficients_zero_iff {q : ℕ} (a b : Fin q → ℝ) :
    (∀ k, reciprocalLaurentCoefficients a b k = 0) ↔ (∀ i, a i = 0 ∧ b i = 0) := by
  constructor
  · intro h i
    exact ⟨by simpa only [reciprocalLaurentCoefficients_forward] using h (forwardExponent i),
      by simpa only [reciprocalLaurentCoefficients_reciprocal] using h (reciprocalExponent i)⟩
  · intro h k
    simp [reciprocalLaurentCoefficients, fun i => (h i).1, fun i => (h i).2]

/-- A genuine Laurent coefficient lower bound survives normalization with exactly the same size. -/
theorem reciprocalLaurentCoefficients_large {q : ℕ} (a b : Fin q → ℝ) (d : ℝ)
    (h : (∃ i, d ≤ |a i|) ∨ ∃ i, d ≤ |b i|) :
    ∃ k, d ≤ |reciprocalLaurentCoefficients a b k| := by
  rcases h with ⟨i, hi⟩ | ⟨i, hi⟩
  · exact ⟨forwardExponent i, by simpa only [reciprocalLaurentCoefficients_forward] using hi⟩
  · exact ⟨reciprocalExponent i, by simpa only [reciprocalLaurentCoefficients_reciprocal] using hi⟩

/-- Sparse coefficient evaluation exposes the distinct forward and reciprocal monomials. -/
theorem reciprocalLaurentCoefficients_eval {q : ℕ} (a b : Fin q → ℝ) (x : Fin q → ℝ) :
    multiquadraticValue (reciprocalLaurentCoefficients a b) x =
      ∑ i : Fin q, ((a i * ∏ j : Fin q, x j ^ (forwardExponent i j : ℕ)) +
        (b i * ∏ j : Fin q, x j ^ (reciprocalExponent i j : ℕ))) := by
  unfold multiquadraticValue reciprocalLaurentCoefficients
  simp_rw [Finset.sum_mul, add_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_add_distrib]
  simp

/-- Exact forward monomial after multiplication by every scale. -/
theorem forwardExponent_monomial {q : ℕ} (x : Fin q → ℝ) (i : Fin q) :
    (∏ j, x j ^ (forwardExponent i j : ℕ)) = (∏ j, x j) * x i := by
  classical
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  simp only [forwardExponent, ite_true, Fin.val_two]
  have hprod : (∏ j ∈ Finset.univ.erase i, x j ^ ((if j = i then (2 : Fin 3) else (1 : Fin 3)).val)) =
      ∏ j ∈ Finset.univ.erase i, x j := by
    apply Finset.prod_congr rfl
    intro j hj
    simp [Finset.ne_of_mem_erase hj]
  rw [hprod, ← Finset.mul_prod_erase Finset.univ x (Finset.mem_univ i)]
  ring

/-- Exact reciprocal monomial; nonzero coordinates justify denominator cancellation. -/
theorem reciprocalExponent_monomial {q : ℕ} (x : Fin q → ℝ) (i : Fin q) (hi : x i ≠ 0) :
    (∏ j, x j ^ (reciprocalExponent i j : ℕ)) = (∏ j, x j) * (x i)⁻¹ := by
  classical
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  simp only [reciprocalExponent, ite_true, Fin.val_zero, pow_zero, one_mul]
  have hprod : (∏ j ∈ Finset.univ.erase i, x j ^ ((if j = i then (0 : Fin 3) else (1 : Fin 3)).val)) =
      ∏ j ∈ Finset.univ.erase i, x j := by
    apply Finset.prod_congr rfl
    intro j hj
    simp [Finset.ne_of_mem_erase hj]
  rw [hprod, ← Finset.mul_prod_erase Finset.univ x (Finset.mem_univ i)]
  field_simp

/-- Literal denominator clearing, with no change to the original reciprocal coefficients. -/
theorem reciprocalLaurent_denominator_clearing {q : ℕ} (a b x : Fin q → ℝ)
    (hx : ∀ i, x i ≠ 0) :
    multiquadraticValue (reciprocalLaurentCoefficients a b) x =
      (∏ i, x i) * reciprocalLaurentValue a b x := by
  rw [reciprocalLaurentCoefficients_eval]
  simp_rw [forwardExponent_monomial, reciprocalExponent_monomial x _ (hx _)]
  unfold reciprocalLaurentValue
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- The exact product bounds on the scale cube, including dimension zero. -/
theorem scale_product_mem_Icc {q : ℕ} (x : Fin q → ℝ) (hx : ∀ i, x i ∈ Icc 1 2) :
    (∏ i, x i) ∈ Icc 1 (2^q) := by
  constructor
  · exact Finset.one_le_prod₀ (fun i _ => (hx i).1)
  · calc
      _ ≤ ∏ _ : Fin q, (2 : ℝ) := Finset.prod_le_prod₀ (fun i _ => by linarith [(hx i).1])
        (fun i _ => (hx i).2)
      _ = 2^q := by simp

/-- A small reciprocal sum on the actual cube yields a small cleared polynomial. -/
theorem reciprocalLaurent_sublevel_subset {q : ℕ} (a b x : Fin q → ℝ)
    (hx : ∀ i, x i ∈ Icc 1 2) (u : ℝ) (hu : 0 < u)
    (hsmall : |reciprocalLaurentValue a b x| < u) :
    |multiquadraticValue (reciprocalLaurentCoefficients a b) x| < 2^q*u := by
  have hprod := scale_product_mem_Icc x hx
  rw [reciprocalLaurent_denominator_clearing a b x (fun i => by linarith [(hx i).1]),
    abs_mul, abs_of_nonneg (by linarith [hprod.1] : 0 ≤ ∏ i, x i)]
  exact (mul_lt_mul_of_pos_left hsmall (by linarith [hprod.1])).trans_le
    (mul_le_mul_of_nonneg_right hprod.2 hu.le)

/-- Actual reciprocal Laurent small-ball probability, with the denominator factor explicit. -/
theorem reciprocalLaurent_coordinate_sublevel_le {q : ℕ} (hq : 0 < q)
    (f : Fin q → ℕ+) (hf : Function.Injective f) (a b : Fin q → ℝ)
    (d u : ℝ) (hd : 0 < d) (hu : 0 < u)
    (hc : (∃ i, d ≤ |a i|) ∨ ∃ i, d ≤ |b i|) :
    scaleProbability {s | |reciprocalLaurentValue a b (fun i => s (f i))| < u} ≤
      min 1 (ENNReal.ofReal (16*(q : ℝ)*((2^q*u)/d)^((1 : ℝ)/(2*(q : ℝ))))) := by
  have hmono : scaleProbability {s | |reciprocalLaurentValue a b (fun i => s (f i))| < u} ≤
      scaleProbability {s | |multiquadraticValue (reciprocalLaurentCoefficients a b)
        (fun i => s (f i))| < 2^q*u} := by
    apply measure_mono_ae
    filter_upwards [ae_all_scales_mem] with s hs
    intro hsmall
    exact reciprocalLaurent_sublevel_subset a b _ (fun i => hs (f i)) u hu hsmall
  exact hmono.trans (multiquadratic_coordinate_sublevel_le hq f hf _ d (2^q*u)
    hd (by positivity) (reciprocalLaurentCoefficients_large a b d hc))

/-- Coefficients of one literal target-minus-origin-minus-integer-shift comparison. -/
def catalogueComparisonCoefficient {q : ℕ} (target origin : Fin q × ReciprocalSign)
    (n n' : ℤ) (β β' : ℝ) (k : Fin q × ReciprocalSign → ℤ)
    (label : Fin q × ReciprocalSign) : ℝ :=
  (if label = target then (n : ℝ)+β else 0) -
    (if label = origin then (n' : ℝ)+β' else 0) - (k label : ℝ)

/-- The accepted proof's expected identity, expressed in the actual integer-shift coefficients. -/
def ExpectedCatalogueComparison {q : ℕ} (target origin : Fin q × ReciprocalSign)
    (n n' : ℤ) (β β' : ℝ) (k : Fin q × ReciprocalSign → ℤ) : Prop :=
  origin = target ∧ β' = β ∧ k target = n-n' ∧ ∀ label, label ≠ target → k label = 0

/-- Equality of two signed phases modulo the integers is equality in the central open cell. -/
theorem signed_phases_integer_difference {β β' : ℝ} (hβ : |β| < 1/2) (hβ' : |β'| < 1/2)
    (m : ℤ) (h : β-β' = (m : ℝ)) : m = 0 ∧ β' = β := by
  have habs : |(m : ℝ)| < 1 := by
    rw [← h]
    exact (abs_sub β β').trans_lt (by linarith)
  have hm : |m| < 1 := by exact_mod_cast habs
  have hm0 : m = 0 := by have := abs_lt.mp hm; omega
  exact ⟨hm0, by simp only [hm0, Int.cast_zero] at h; linarith⟩

/-- A nonzero signed phase in the central half-cell cannot be an integer. -/
theorem signed_phase_ne_integer {β : ℝ} (hβ : |β| < 1/2) (hβ0 : β ≠ 0) (m : ℤ) :
    β ≠ (m : ℝ) := by
  intro h
  have hm : |(m : ℝ)| < 1 := by rw [← h]; linarith
  have hm' : |m| < 1 := by exact_mod_cast hm
  have hm0 : m = 0 := by have := abs_lt.mp hm'; omega
  exact hβ0 (by simpa only [hm0, Int.cast_zero] using h)

/-- Exact classification: all comparison coefficients vanish precisely for an expected identity. -/
theorem catalogueComparisonCoefficient_zero_iff {q : ℕ} (target origin : Fin q × ReciprocalSign)
    (n n' : ℤ) (β β' : ℝ) (k : Fin q × ReciprocalSign → ℤ)
    (hβ : |β| < 1/2) (hβ0 : β ≠ 0) (hβ' : |β'| < 1/2) :
    (∀ label, catalogueComparisonCoefficient target origin n n' β β' k label = 0) ↔
      ExpectedCatalogueComparison target origin n n' β β' k := by
  constructor
  · intro h
    have ho : origin = target := by
      by_contra hne
      have ht := h target
      simp only [catalogueComparisonCoefficient, ite_true, Ne.symm hne, ite_false,
        sub_zero] at ht
      apply signed_phase_ne_integer hβ hβ0 (k target - n)
      push_cast
      linarith
    subst origin
    have ht := h target
    simp only [catalogueComparisonCoefficient, ite_true] at ht
    have hdiff : β-β' = ((k target - n + n' : ℤ) : ℝ) := by push_cast; linarith
    obtain ⟨hm, hb⟩ := signed_phases_integer_difference hβ hβ' _ hdiff
    refine ⟨rfl, hb, by omega, ?_⟩
    intro label hlabel
    have hl := h label
    simpa only [catalogueComparisonCoefficient, hlabel, ite_false, sub_self, zero_sub,
      neg_eq_zero, Int.cast_eq_zero] using hl
  · rintro ⟨ho, hb, hkt, hk⟩ label
    subst origin
    subst β'
    by_cases hl : label = target
    · subst label
      simp only [catalogueComparisonCoefficient, ite_true, hkt, Int.cast_sub]
      ring
    · simp [catalogueComparisonCoefficient, hl, hk label hl]

/-- The normalized multiquadratic coefficients have exactly the same expected identities. -/
theorem catalogue_normalized_coefficients_zero_iff {q : ℕ} (target origin : Fin q × ReciprocalSign)
    (n n' : ℤ) (β β' : ℝ) (k : Fin q × ReciprocalSign → ℤ)
    (hβ : |β| < 1/2) (hβ0 : β ≠ 0) (hβ' : |β'| < 1/2) :
    (∀ j, reciprocalLaurentCoefficients
      (fun i => catalogueComparisonCoefficient target origin n n' β β' k (i, .forward))
      (fun i => catalogueComparisonCoefficient target origin n n' β β' k (i, .reciprocal)) j = 0) ↔
      ExpectedCatalogueComparison target origin n n' β β' k := by
  rw [reciprocalLaurentCoefficients_zero_iff, ← catalogueComparisonCoefficient_zero_iff
    target origin n n' β β' k hβ hβ0 hβ']
  constructor
  · intro h ⟨i, σ⟩
    cases σ with
    | forward => exact (h i).1
    | reciprocal => exact (h i).2
  · intro h i
    exact ⟨h (i, .forward), h (i, .reciprocal)⟩

/-- An explicit positive lower bound on distances from a noninteger central phase to integers. -/
theorem signed_phase_integer_distance (β : ℝ) (m : ℤ) :
    min |β| (1-|β|) ≤ |β-(m : ℝ)| := by
  by_cases hm : m = 0
  · simp only [hm, Int.cast_zero, sub_zero]
    exact min_le_left _ _
  · have hmabs : 1 ≤ |m| := by
      have hnonneg := abs_nonneg m
      have hne : |m| ≠ 0 := abs_ne_zero.mpr hm
      omega
    have hmreal : (1 : ℝ) ≤ |(m : ℝ)| := by exact_mod_cast hmabs
    have hrev := abs_add_le (β-(m : ℝ)) (-β)
    have heq : β-(m : ℝ)+ -β = -(m : ℝ) := by ring
    rw [heq, abs_neg, abs_neg] at hrev
    exact (min_le_right _ _).trans (by linarith)

/-- Every actual signed phase is nonzero and lies in the open central half-cell. -/
theorem phaseSet_phase_bounds {P R : ℕ} (hP : 1 ≤ P) (hR : 1 ≤ R)
    {β : ℝ} (hβ : β ∈ phaseSet P R) : |β| < 1/2 ∧ β ≠ 0 := by
  obtain ⟨j, positive, rfl⟩ := hβ
  refine ⟨abs_signedPhase_lt_half hP hR j positive, ?_⟩
  have hp := (blockPhase_mem_Ioo hP hR j).1
  cases positive <;> simp [signedPhase] <;> linarith

/-- Actual signed phases have a positive separation from integers and all other periodic phases. -/
theorem exists_phase_separation {P R : ℕ} (hP : 1 ≤ P) (hR : 1 ≤ R)
    {β : ℝ} (hβ : β ∈ phaseSet P R) :
    ∃ d : ℝ, 0 < d ∧
      (∀ m : ℤ, d ≤ |β-(m : ℝ)|) ∧
      (∀ β' ∈ phaseSet P R, ∀ m : ℤ, (β' ≠ β ∨ m ≠ 0) →
        d ≤ |β-((m : ℝ)+β')|) := by
  obtain ⟨hb, hb0⟩ := phaseSet_phase_bounds hP hR hβ
  have hperiodic : β ∈ periodicPhaseSet P R := ⟨0, β, Or.inl hβ, by simp⟩
  have hseam : ∀ n : ℤ, β ≠ (n : ℝ)+1/2 := by
    intro n hn
    have hnlo : (-1 : ℝ) < n := by have := (abs_lt.mp hb).1; linarith
    have hnhi : (n : ℝ) < 0 := by have := (abs_lt.mp hb).2; linarith
    have hlo : (-1 : ℤ) < n := by exact_mod_cast hnlo
    have hhi : n < 0 := by exact_mod_cast hnhi
    omega
  obtain ⟨U, hU, hUeq⟩ := periodicPhaseSet_point_isolated hP hR hperiodic hseam
  have hβU : β ∈ U := by
    have hmem : β ∈ U ∩ periodicPhaseSet P R := by rw [hUeq]; simp
    exact hmem.1
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU β hβU
  let d := min ε (min |β| (1-|β|))
  have hd : 0 < d := lt_min hε (lt_min (abs_pos.mpr hb0) (by linarith))
  refine ⟨d, hd, ?_, ?_⟩
  · intro m
    exact (min_le_right _ _).trans (signed_phase_integer_distance β m)
  · intro β' hβ' m hne
    have hy : (m : ℝ)+β' ∈ periodicPhaseSet P R := ⟨m, β', Or.inl hβ', rfl⟩
    have hyne : (m : ℝ)+β' ≠ β := by
      intro heq
      obtain ⟨hm, he⟩ := signed_phases_integer_difference hb
        (phaseSet_phase_bounds hP hR hβ').1 m (by linarith)
      rcases hne with h | h
      · exact h he
      · exact h hm
    have hdist : ε ≤ |β-((m : ℝ)+β')| := by
      by_contra hlt
      have hin : (m : ℝ)+β' ∈ Metric.ball β ε := by
        rw [Metric.mem_ball, Real.dist_eq, abs_sub_comm]
        exact lt_of_not_ge hlt
      have hm : (m : ℝ)+β' ∈ ({β} : Set ℝ) := by rw [← hUeq]; exact ⟨hball hin, hy⟩
      exact hyne hm
    exact (min_le_left _ _).trans hdist

/-- A nonzero integer coefficient has magnitude at least one in the original real normalization. -/
theorem one_le_abs_int_cast {m : ℤ} (hm : m ≠ 0) : (1 : ℝ) ≤ |(m : ℝ)| := by
  have h : 1 ≤ |m| := by have := abs_nonneg m; have := abs_ne_zero.mpr hm; omega
  exact_mod_cast h

/-- The catalogue cases preserve a common phase-separation lower bound, uniformly in other labels. -/
theorem catalogueComparisonCoefficient_large {q P R : ℕ}
    (target origin : Fin q × ReciprocalSign) (n n' : ℤ) (β β' : ℝ)
    (k : Fin q × ReciprocalSign → ℤ) (d : ℝ)
    (hdint : ∀ m : ℤ, d ≤ |β-(m : ℝ)|)
    (hdphase : ∀ γ ∈ phaseSet P R, ∀ m : ℤ, (γ ≠ β ∨ m ≠ 0) →
      d ≤ |β-((m : ℝ)+γ)|)
    (horigin : origin = target → β' ∈ phaseSet P R)
    (hbad : ¬ ExpectedCatalogueComparison target origin n n' β β' k) :
    ∃ label, min d 1 ≤ |catalogueComparisonCoefficient target origin n n' β β' k label| := by
  by_cases ho : origin = target
  · subst origin
    by_cases hphase : β' ≠ β ∨ n'+k target-n ≠ 0
    · refine ⟨target, (min_le_left _ _).trans ?_⟩
      have hd := hdphase β' (horigin rfl) (n'+k target-n) hphase
      simp only [catalogueComparisonCoefficient, ite_true]
      convert hd using 1 <;> congr 1 <;> push_cast <;> ring
    · have hb : β' = β := not_not.mp (not_or.mp hphase).1
      have hm : n'+k target-n = 0 := not_not.mp (not_or.mp hphase).2
      have hkt : k target = n-n' := by omega
      have hother : ∃ label, label ≠ target ∧ k label ≠ 0 := by
        by_contra hn
        push Not at hn
        exact hbad ⟨rfl, hb, hkt, hn⟩
      obtain ⟨label, hl, hk⟩ := hother
      refine ⟨label, (min_le_right _ _).trans ?_⟩
      simpa only [catalogueComparisonCoefficient, hl, ite_false, sub_self, zero_sub, abs_neg]
        using one_le_abs_int_cast hk
  · refine ⟨target, (min_le_left _ _).trans ?_⟩
    have hd := hdint (k target-n)
    simp only [catalogueComparisonCoefficient, ite_true, Ne.symm ho, ite_false, sub_zero]
    convert hd using 1 <;> congr 1 <;> push_cast <;> ring

/-- Actual phase geometry supplies a positive coefficient bound independent of every other sector. -/
theorem exists_catalogue_coefficient_lower_bound {P R : ℕ} (hP : 1 ≤ P) (hR : 1 ≤ R)
    {β : ℝ} (hβ : β ∈ phaseSet P R) :
    ∃ d : ℝ, 0 < d ∧ ∀ q : ℕ, ∀ target origin : Fin q × ReciprocalSign,
      ∀ n n' : ℤ, ∀ β' : ℝ, ∀ k : Fin q × ReciprocalSign → ℤ,
      (origin = target → β' ∈ phaseSet P R) →
      ¬ ExpectedCatalogueComparison target origin n n' β β' k →
      ∃ j, min d 1 ≤ |reciprocalLaurentCoefficients
        (fun i => catalogueComparisonCoefficient target origin n n' β β' k (i, .forward))
        (fun i => catalogueComparisonCoefficient target origin n n' β β' k (i, .reciprocal)) j| := by
  obtain ⟨d, hd, hint, hphase⟩ := exists_phase_separation hP hR hβ
  refine ⟨d, hd, ?_⟩
  intro q target origin n n' β' k horigin hbad
  obtain ⟨⟨i, σ⟩, hi⟩ := catalogueComparisonCoefficient_large target origin n n' β β' k d
    hint hphase horigin hbad
  apply reciprocalLaurentCoefficients_large
  cases σ with
  | forward => exact Or.inl ⟨i, hi⟩
  | reciprocal => exact Or.inr ⟨i, hi⟩

/-- The actual target-minus-shifted-origin comparison, before clearing denominators. -/
def catalogueComparisonValue {q : ℕ} (target origin : Fin q × ReciprocalSign)
    (n n' : ℤ) (β β' : ℝ) (k : Fin q × ReciprocalSign → ℤ) (x : Fin q → ℝ) : ℝ :=
  scaleFactor target.2 (x target.1) * ((n : ℝ)+β) -
    scaleFactor origin.2 (x origin.1) * ((n' : ℝ)+β') -
      reciprocalLaurentValue (fun i => (k (i, .forward) : ℝ))
        (fun i => (k (i, .reciprocal) : ℝ)) x

/-- Exact evaluation of the catalogue coefficient table as its original reciprocal comparison. -/
theorem catalogueComparisonCoefficient_eval {q : ℕ} (target origin : Fin q × ReciprocalSign)
    (n n' : ℤ) (β β' : ℝ) (k : Fin q × ReciprocalSign → ℤ) (x : Fin q → ℝ) :
    reciprocalLaurentValue
      (fun i => catalogueComparisonCoefficient target origin n n' β β' k (i, .forward))
      (fun i => catalogueComparisonCoefficient target origin n n' β β' k (i, .reciprocal)) x =
      catalogueComparisonValue target origin n n' β β' k x := by
  rcases target with ⟨ti, ts⟩
  rcases origin with ⟨oi, os⟩
  cases ts <;> cases os <;>
    simp [reciprocalLaurentValue, catalogueComparisonCoefficient, catalogueComparisonValue,
      scaleFactor, sub_mul, add_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib] <;> ring

/-- A finite family of positive constants has a common positive lower bound, also for an empty family. -/
theorem finite_positive_lower_bound {ι : Type*} (s : Finset ι) (v : ι → ℝ)
    (hv : ∀ i ∈ s, 0 < v i) : ∃ d : ℝ, 0 < d ∧ ∀ i ∈ s, d ≤ v i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨d, hd, hds⟩ := ih (fun j hj => hv j (Finset.mem_insert_of_mem hj))
    refine ⟨min (v i) d, lt_min (hv i (Finset.mem_insert_self _ _)) hd, ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (hds j hj)

/-- A finite catalogue of actual phases admits one lower bound using only its own block data. -/
theorem exists_finite_catalogue_phase_separation {ι : Type*} [Fintype ι]
    (P R : ι → ℕ) (β : ι → ℝ) (hP : ∀ i, 1 ≤ P i) (hR : ∀ i, 1 ≤ R i)
    (hβ : ∀ i, β i ∈ phaseSet (P i) (R i)) :
    ∃ d : ℝ, 0 < d ∧ ∀ i,
      (∀ m : ℤ, d ≤ |β i-(m : ℝ)|) ∧
      (∀ γ ∈ phaseSet (P i) (R i), ∀ m : ℤ, (γ ≠ β i ∨ m ≠ 0) →
        d ≤ |β i-((m : ℝ)+γ)|) := by
  classical
  choose v hv hint hphase using fun i => exists_phase_separation (hP i) (hR i) (hβ i)
  obtain ⟨d, hd, hdi⟩ := finite_positive_lower_bound Finset.univ v (by simpa using hv)
  refine ⟨d, hd, fun i => ⟨?_, ?_⟩⟩
  · intro m
    exact (hdi i (Finset.mem_univ _)).trans (hint i m)
  · intro γ hγ m hne
    exact (hdi i (Finset.mem_univ _)).trans (hphase i γ hγ m hne)

/-- Actual finite-catalogue small-ball bounds with a common constant fixed before other sectors. -/
theorem exists_finite_catalogue_comparison_sublevel_bound {ι : Type*} [Fintype ι]
    (P R : ι → ℕ) (β : ι → ℝ) (hP : ∀ i, 1 ≤ P i) (hR : ∀ i, 1 ≤ R i)
    (hβ : ∀ i, β i ∈ phaseSet (P i) (R i)) :
    ∃ d : ℝ, 0 < d ∧ ∀ t, ∀ q : ℕ, 0 < q → ∀ f : Fin q → ℕ+, Function.Injective f →
      ∀ target origin : Fin q × ReciprocalSign, ∀ n n' : ℤ, ∀ β' : ℝ,
      ∀ k : Fin q × ReciprocalSign → ℤ,
      (origin = target → β' ∈ phaseSet (P t) (R t)) →
      ¬ ExpectedCatalogueComparison target origin n n' (β t) β' k →
      ∀ u : ℝ, 0 < u →
      scaleProbability {s | |catalogueComparisonValue target origin n n' (β t) β' k
        (fun i => s (f i))| < u} ≤
      min 1 (ENNReal.ofReal (16*(q : ℝ)*((2^q*u)/min d 1)^((1 : ℝ)/(2*(q : ℝ))))) := by
  obtain ⟨d, hd, hsep⟩ := exists_finite_catalogue_phase_separation P R β hP hR hβ
  refine ⟨d, hd, ?_⟩
  intro t q hq f hf target origin n n' β' k horigin hbad u hu
  obtain ⟨⟨i, σ⟩, hi⟩ := catalogueComparisonCoefficient_large target origin n n' (β t) β' k d
    (hsep t).1 (hsep t).2 horigin hbad
  have hcoef : (∃ i, min d 1 ≤ |catalogueComparisonCoefficient target origin n n' (β t) β' k
      (i, .forward)|) ∨ ∃ i, min d 1 ≤ |catalogueComparisonCoefficient target origin n n' (β t) β' k
        (i, .reciprocal)| := by
    cases σ with
    | forward => exact Or.inl ⟨i, hi⟩
    | reciprocal => exact Or.inr ⟨i, hi⟩
  simpa only [catalogueComparisonCoefficient_eval] using reciprocalLaurent_coordinate_sublevel_le
    hq f hf
    (fun i => catalogueComparisonCoefficient target origin n n' (β t) β' k (i, .forward))
    (fun i => catalogueComparisonCoefficient target origin n n' (β t) β' k (i, .reciprocal))
    (min d 1) u (lt_min hd (by norm_num)) hu hcoef

/-- The exact finite phase catalogue with block and phase indices at most M and both signs. -/
def prefixCataloguePhase {M : ℕ} (R : Fin M → ℕ) (t : Fin M × Fin M × Bool) : ℝ :=
  signedPhase t.2.2 (blockPhase (t.1.val+1) (R t.1) ⟨t.2.1.val+1, Nat.succ_pos _⟩)

/-- Prefix-only separation constants for all actual catalogue phases. -/
theorem exists_prefix_catalogue_comparison_sublevel_bound (M : ℕ) (R : Fin M → ℕ)
    (hR : ∀ i, 1 ≤ R i) :
    ∃ d : ℝ, 0 < d ∧ ∀ t : Fin M × Fin M × Bool,
      ∀ f : Fin (M+1) → ℕ+, Function.Injective f →
      ∀ target origin : Fin (M+1) × ReciprocalSign, ∀ n n' : ℤ, ∀ β' : ℝ,
      ∀ k : Fin (M+1) × ReciprocalSign → ℤ,
      (origin = target → β' ∈ phaseSet (t.1.val+1) (R t.1)) →
      ¬ ExpectedCatalogueComparison target origin n n' (prefixCataloguePhase R t) β' k →
      ∀ u : ℝ, 0 < u →
      scaleProbability {s | |catalogueComparisonValue target origin n n' (prefixCataloguePhase R t) β' k
        (fun i => s (f i))| < u} ≤
      min 1 (ENNReal.ofReal (16*((M+1 : ℕ) : ℝ)*((2^(M+1)*u)/min d 1)^
        ((1 : ℝ)/(2*((M+1 : ℕ) : ℝ))))) := by
  obtain ⟨d, hd, h⟩ := exists_finite_catalogue_comparison_sublevel_bound
    (fun t : Fin M × Fin M × Bool => t.1.val+1) (fun t => R t.1) (prefixCataloguePhase R)
    (fun _ => Nat.succ_le_succ (Nat.zero_le _)) (fun t => hR t.1)
    (fun t => ⟨⟨t.2.1.val+1, Nat.succ_pos _⟩, t.2.2, rfl⟩)
  exact ⟨d, hd, fun t => h t (M+1) (Nat.succ_pos _)⟩

end
end MeyerGeneralProblem.Adaptive
