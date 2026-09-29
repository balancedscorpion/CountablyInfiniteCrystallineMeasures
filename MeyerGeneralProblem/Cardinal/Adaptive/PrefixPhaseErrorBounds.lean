module

public import MeyerGeneralProblem.Cardinal.Adaptive.PhaseAvoidance

@[expose] public section

/-! # Selected analytic constants on the literal reciprocal label prefix

The stage constants were selected on a finite ordinal. This module transports
those same constants, without choosing new ones, to the actual two-label prefix.
-/
namespace MeyerGeneralProblem.Adaptive
noncomputable section

/-- A finite ordinal enumerates exactly both reciprocal labels at every prefix index. -/
def prefixLabelEnumeration (M : ℕ) : Fin (2*M) ≃ (Fin M × ReciprocalSign) :=
  (Fintype.equivFinOfCardEq (by
    rw [Fintype.card_prod,Fintype.card_fin]
    have h : Fintype.card ReciprocalSign = 2 := rfl
    rw [h,Nat.mul_comm])).symm

/-- The already selected leading constant controls the literal reciprocal-label sum. -/
theorem stageLeadingErrorConstant_prefix (p D N M : ℕ) (ζ : Fin N → SchwartzMap ℝ ℂ)
    (H : ℝ) (hH : 0 ≤ H) (H₀ : ℝ) (hH₀ : 1 ≤ H₀) (h : Fin N → ℝ) (hh : ∀ i, H₀ ≤ h i)
    (f : SchwartzMap ℝ ℂ) (hf : tsupport f ⊆ Set.Icc (-H) H) (A : ℝ) (hA : 0 ≤ A)
    (hfA : ∀ n ≤ testOrder p, ∀ x, ‖iteratedDeriv n (f : ℝ → ℂ) x‖ ≤ A)
    (P : (Fin M × ReciprocalSign) → ℝ) (hP : ∀ j, P j ∈ Set.Icc (1/2:ℝ) 2)
    (T : (Fin M × ReciprocalSign) → Fin (D+1) → HermiteScale (-((liftOrder p) : ℤ)))
    (hT : ∀ j r, combDistributionTranslation (P j) (hermiteScaleDistribution (liftOrder p) (T j r)) =
      -hermiteScaleDistribution (liftOrder p) (T j r)) :
    ‖∑ i, ∑ j, ∑ r : Fin (D+1),
      (((-(h i:ℂ))^D)⁻¹ * combDistributionTranslation (h i)
        (monomialDistribution r.val (hermiteScaleDistribution (liftOrder p) (T j r))) (SchwartzMap.smulLeftCLM ℂ (ζ i) f) -
      (if r.val = D then combDistributionTranslation (h i) (hermiteScaleDistribution (liftOrder p) (T j r))
        (SchwartzMap.smulLeftCLM ℂ (ζ i) f) else 0))‖ ≤
      stageLeadingErrorConstant p D N (2*M) ζ H hH*A/H₀*(∑ j, ∑ r, ‖T j r‖) := by
  let e := prefixLabelEnumeration M
  have hb := stageLeadingErrorConstant_spec p D N (2*M) ζ H hH H₀ hH₀ h hh f hf A hA hfA
    (fun j => P (e j)) (fun j => hP (e j)) (fun j => T (e j)) (fun j => hT (e j))
  have hsum (i : Fin N) := e.sum_comp (fun j => ∑ r : Fin (D+1),
    (((-(h i:ℂ))^D)⁻¹ * combDistributionTranslation (h i)
      (monomialDistribution r.val (hermiteScaleDistribution (liftOrder p) (T j r))) (SchwartzMap.smulLeftCLM ℂ (ζ i) f) -
    (if r.val = D then combDistributionTranslation (h i) (hermiteScaleDistribution (liftOrder p) (T j r))
      (SchwartzMap.smulLeftCLM ℂ (ζ i) f) else 0)))
  simp_rw [hsum] at hb
  rw [e.sum_comp (fun j => ∑ r, ‖T j r‖)] at hb
  exact hb

/-- Transport the phase estimate before specializing the Hermite order. -/
theorem phaseErrorConstantAtOrder_prefix (p q N M : ℕ) (hq : q ≤ liftOrder p) (ζ : Fin N → SchwartzMap ℝ ℂ)
    (H S : ℝ) (hH : 0 ≤ H) (hS : 0 ≤ S)
    (f : SchwartzMap ℝ ℂ) (hf : tsupport f ⊆ Set.Icc (-H) H) (A : ℝ) (hA : 0 ≤ A)
    (hfA : ∀ r ≤ testOrder p, ∀ x, ‖iteratedDeriv r (f : ℝ → ℂ) x‖ ≤ A)
    (η : ℝ) (hη : 0 ≤ η) (a b : Fin N → (Fin M × ReciprocalSign) → ℝ)
    (ha : ∀ i j, |a i j| ≤ S) (hb : ∀ i j, |b i j| ≤ S)
    (hab : ∀ i j, |a i j-b i j| ≤ η)
    (T : (Fin M × ReciprocalSign) → HermiteScale (-(q : ℤ))) :
    ‖∑ i, ∑ j,
      (combDistributionTranslation (a i j) (hermiteScaleDistribution q (T j))
        (SchwartzMap.smulLeftCLM ℂ (ζ i) f) -
      combDistributionTranslation (b i j) (hermiteScaleDistribution q (T j))
        (SchwartzMap.smulLeftCLM ℂ (ζ i) f))‖ ≤
      phaseErrorConstantAtOrder p q N (2*M) hq ζ H S hH hS * A * η * ∑ j, ‖T j‖ := by
  let e := prefixLabelEnumeration M
  have hc := phaseErrorConstantAtOrder_spec p q N (2*M) hq ζ H S hH hS f hf A hA hfA η hη
    (fun i j => a i (e j)) (fun i j => b i (e j)) (fun i j => ha i (e j))
    (fun i j => hb i (e j)) (fun i j => hab i (e j)) (fun j => T (e j))
  have hsum (i : Fin N) := e.sum_comp (fun j =>
    combDistributionTranslation (a i j) (hermiteScaleDistribution q (T j))
      (SchwartzMap.smulLeftCLM ℂ (ζ i) f) -
    combDistributionTranslation (b i j) (hermiteScaleDistribution q (T j))
      (SchwartzMap.smulLeftCLM ℂ (ζ i) f))
  simp_rw [hsum] at hc
  rw [e.sum_comp (fun j => ‖T j‖)] at hc
  exact hc

/-- The already selected phase constant controls the literal reciprocal-label sum. -/
theorem stagePhaseErrorConstant_prefix (p N M : ℕ) (ζ : Fin N → SchwartzMap ℝ ℂ)
    (H S : ℝ) (hH : 0 ≤ H) (hS : 0 ≤ S)
    (f : SchwartzMap ℝ ℂ) (hf : tsupport f ⊆ Set.Icc (-H) H) (A : ℝ) (hA : 0 ≤ A)
    (hfA : ∀ r ≤ testOrder p, ∀ x, ‖iteratedDeriv r (f : ℝ → ℂ) x‖ ≤ A)
    (η : ℝ) (hη : 0 ≤ η) (a b : Fin N → (Fin M × ReciprocalSign) → ℝ)
    (ha : ∀ i j, |a i j| ≤ S) (hb : ∀ i j, |b i j| ≤ S)
    (hab : ∀ i j, |a i j-b i j| ≤ η)
    (T : (Fin M × ReciprocalSign) → HermiteScale (-((liftOrder p) : ℤ))) :
    ‖∑ i, ∑ j,
      (combDistributionTranslation (a i j) (hermiteScaleDistribution (liftOrder p) (T j))
        (SchwartzMap.smulLeftCLM ℂ (ζ i) f) -
      combDistributionTranslation (b i j) (hermiteScaleDistribution (liftOrder p) (T j))
        (SchwartzMap.smulLeftCLM ℂ (ζ i) f))‖ ≤
      stagePhaseErrorConstant p N (2*M) ζ H S hH hS * A * η * ∑ j, ‖T j‖ :=
  phaseErrorConstantAtOrder_prefix p (liftOrder p) N M le_rfl ζ H S hH hS
    f hf A hA hfA η hη a b ha hb hab T

end
end MeyerGeneralProblem.Adaptive
