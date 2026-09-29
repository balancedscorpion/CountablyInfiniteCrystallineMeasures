module

public import MeyerGeneralProblem.Cardinal.Adaptive.LeadingTranslationErrors
public import MeyerGeneralProblem.Cardinal.Adaptive.TorusPhaseNets

@[expose] public section

/-! # Deterministic stage parameters for both translation errors

The constants are selected from actual proved estimates, before every test,
coefficient or realized scale. A finite maximum in p and D pays both errors
without increasing the prescribed testOrder p.
-/
namespace MeyerGeneralProblem.Adaptive
noncomputable section

/-- Select the leading-error constant before specializing the Hermite order.
Keeping that order as a parameter avoids expanding the specialized estimate
inside the choice proof during independent kernel checking. -/
def leadingErrorConstantAtOrder (p q D N L : ℕ) (hq : q ≤ liftOrder p)
    (ζ : Fin N → SchwartzMap ℝ ℂ)
    (H : ℝ) (hH : 0 ≤ H) : ℝ :=
  Classical.choose (exists_partition_sum_leading_error_bound p q D N L hq ζ H hH)

/-- A source-independent constant from the proved full leading-error estimate. -/
def stageLeadingErrorConstant (p D N L : ℕ) (ζ : Fin N → SchwartzMap ℝ ℂ)
    (H : ℝ) (hH : 0 ≤ H) : ℝ :=
  leadingErrorConstantAtOrder p (liftOrder p) D N L le_rfl ζ H hH

/-- Select the phase-error constant with a general Hermite order, for the same
reason as `leadingErrorConstantAtOrder`. -/
def phaseErrorConstantAtOrder (p q N L : ℕ) (hq : q ≤ liftOrder p)
    (ζ : Fin N → SchwartzMap ℝ ℂ)
    (H S : ℝ) (hH : 0 ≤ H) (hS : 0 ≤ S) : ℝ :=
  Classical.choose (exists_partition_sum_phase_error_bound p q N L hq ζ H S hH hS)

/-- A source-independent constant from the proved full phase-error estimate. -/
def stagePhaseErrorConstant (p N L : ℕ) (ζ : Fin N → SchwartzMap ℝ ℂ)
    (H S : ℝ) (hH : 0 ≤ H) (hS : 0 ≤ S) : ℝ :=
  phaseErrorConstantAtOrder p (liftOrder p) N L le_rfl ζ H S hH hS

/-- Positivity before specializing the Hermite order. -/
theorem leadingErrorConstantAtOrder_pos (p q D N L : ℕ) (hq : q ≤ liftOrder p)
    (ζ : Fin N → SchwartzMap ℝ ℂ) (H : ℝ) (hH : 0 ≤ H) :
    0 < leadingErrorConstantAtOrder p q D N L hq ζ H hH :=
  (Classical.choose_spec (exists_partition_sum_leading_error_bound p q D N L hq ζ H hH)).1

/-- Positivity before specializing the Hermite order. -/
theorem phaseErrorConstantAtOrder_pos (p q N L : ℕ) (hq : q ≤ liftOrder p)
    (ζ : Fin N → SchwartzMap ℝ ℂ) (H S : ℝ) (hH : 0 ≤ H) (hS : 0 ≤ S) :
    0 < phaseErrorConstantAtOrder p q N L hq ζ H S hH hS :=
  (Classical.choose_spec (exists_partition_sum_phase_error_bound p q N L hq ζ H S hH hS)).1

/-- The complete estimate before specializing the Hermite order. -/
theorem leadingErrorConstantAtOrder_spec (p q D N L : ℕ) (hq : q ≤ liftOrder p) (ζ : Fin N → SchwartzMap ℝ ℂ)
    (H : ℝ) (hH : 0 ≤ H) :
    ∀ H₀ : ℝ, 1 ≤ H₀ → ∀ h : Fin N → ℝ, (∀ i, H₀ ≤ h i) →
      ∀ f : SchwartzMap ℝ ℂ, tsupport f ⊆ Set.Icc (-H) H → ∀ A : ℝ, 0 ≤ A →
      (∀ n ≤ testOrder p, ∀ x, ‖iteratedDeriv n (f : ℝ → ℂ) x‖ ≤ A) →
      ∀ P : Fin L → ℝ, (∀ j, P j ∈ Set.Icc (1/2:ℝ) 2) →
      ∀ T : Fin L → Fin (D+1) → HermiteScale (-(q : ℤ)),
      (∀ j r, combDistributionTranslation (P j) (hermiteScaleDistribution q (T j r)) =
        -hermiteScaleDistribution q (T j r)) →
      ‖∑ i, ∑ j, ∑ r : Fin (D+1),
        (((-(h i:ℂ))^D)⁻¹ * combDistributionTranslation (h i)
          (monomialDistribution r.val (hermiteScaleDistribution q (T j r))) (SchwartzMap.smulLeftCLM ℂ (ζ i) f) -
        (if r.val = D then combDistributionTranslation (h i) (hermiteScaleDistribution q (T j r))
          (SchwartzMap.smulLeftCLM ℂ (ζ i) f) else 0))‖ ≤
        leadingErrorConstantAtOrder p q D N L hq ζ H hH*A/H₀*(∑ j, ∑ r, ‖T j r‖) :=
  (Classical.choose_spec (exists_partition_sum_leading_error_bound p q D N L hq ζ H hH)).2

/-- The complete estimate before specializing the Hermite order. -/
theorem phaseErrorConstantAtOrder_spec (p q N L : ℕ) (hq : q ≤ liftOrder p) (ζ : Fin N → SchwartzMap ℝ ℂ)
    (H S : ℝ) (hH : 0 ≤ H) (hS : 0 ≤ S) :
    ∀ f : SchwartzMap ℝ ℂ, tsupport f ⊆ Set.Icc (-H) H → ∀ A : ℝ, 0 ≤ A →
      (∀ r ≤ testOrder p, ∀ x, ‖iteratedDeriv r (f : ℝ → ℂ) x‖ ≤ A) →
      ∀ η : ℝ, 0 ≤ η → ∀ a b : Fin N → Fin L → ℝ,
      (∀ i j, |a i j| ≤ S) → (∀ i j, |b i j| ≤ S) →
      (∀ i j, |a i j-b i j| ≤ η) → ∀ T : Fin L → HermiteScale (-(q : ℤ)),
      ‖∑ i, ∑ j,
        (combDistributionTranslation (a i j) (hermiteScaleDistribution q (T j))
          (SchwartzMap.smulLeftCLM ℂ (ζ i) f) -
        combDistributionTranslation (b i j) (hermiteScaleDistribution q (T j))
          (SchwartzMap.smulLeftCLM ℂ (ζ i) f))‖ ≤
        phaseErrorConstantAtOrder p q N L hq ζ H S hH hS * A * η * ∑ j, ‖T j‖ :=
  (Classical.choose_spec (exists_partition_sum_phase_error_bound p q N L hq ζ H S hH hS)).2

/-- The selected leading constant is strictly positive. -/
theorem stageLeadingErrorConstant_pos (p D N L : ℕ) (ζ : Fin N → SchwartzMap ℝ ℂ)
    (H : ℝ) (hH : 0 ≤ H) : 0 < stageLeadingErrorConstant p D N L ζ H hH :=
  leadingErrorConstantAtOrder_pos p (liftOrder p) D N L le_rfl ζ H hH

/-- The selected phase constant is strictly positive. -/
theorem stagePhaseErrorConstant_pos (p N L : ℕ) (ζ : Fin N → SchwartzMap ℝ ℂ)
    (H S : ℝ) (hH : 0 ≤ H) (hS : 0 ≤ S) : 0 < stagePhaseErrorConstant p N L ζ H S hH hS :=
  phaseErrorConstantAtOrder_pos p (liftOrder p) N L le_rfl ζ H S hH hS

/-- The selected leading constant retains the complete actual-source inequality. -/
theorem stageLeadingErrorConstant_spec (p D N L : ℕ) (ζ : Fin N → SchwartzMap ℝ ℂ)
    (H : ℝ) (hH : 0 ≤ H) :
    ∀ H₀ : ℝ, 1 ≤ H₀ → ∀ h : Fin N → ℝ, (∀ i, H₀ ≤ h i) →
      ∀ f : SchwartzMap ℝ ℂ, tsupport f ⊆ Set.Icc (-H) H → ∀ A : ℝ, 0 ≤ A →
      (∀ n ≤ testOrder p, ∀ x, ‖iteratedDeriv n (f : ℝ → ℂ) x‖ ≤ A) →
      ∀ P : Fin L → ℝ, (∀ j, P j ∈ Set.Icc (1/2:ℝ) 2) →
      ∀ T : Fin L → Fin (D+1) → HermiteScale (-((liftOrder p) : ℤ)),
      (∀ j r, combDistributionTranslation (P j) (hermiteScaleDistribution (liftOrder p) (T j r)) =
        -hermiteScaleDistribution (liftOrder p) (T j r)) →
      ‖∑ i, ∑ j, ∑ r : Fin (D+1),
        (((-(h i:ℂ))^D)⁻¹ * combDistributionTranslation (h i)
          (monomialDistribution r.val (hermiteScaleDistribution (liftOrder p) (T j r))) (SchwartzMap.smulLeftCLM ℂ (ζ i) f) -
        (if r.val = D then combDistributionTranslation (h i) (hermiteScaleDistribution (liftOrder p) (T j r))
          (SchwartzMap.smulLeftCLM ℂ (ζ i) f) else 0))‖ ≤
        stageLeadingErrorConstant p D N L ζ H hH*A/H₀*(∑ j, ∑ r, ‖T j r‖) :=
  leadingErrorConstantAtOrder_spec p (liftOrder p) D N L le_rfl ζ H hH

/-- The selected phase constant retains the complete actual-source inequality. -/
theorem stagePhaseErrorConstant_spec (p N L : ℕ) (ζ : Fin N → SchwartzMap ℝ ℂ)
    (H S : ℝ) (hH : 0 ≤ H) (hS : 0 ≤ S) :
    ∀ f : SchwartzMap ℝ ℂ, tsupport f ⊆ Set.Icc (-H) H → ∀ A : ℝ, 0 ≤ A →
      (∀ r ≤ testOrder p, ∀ x, ‖iteratedDeriv r (f : ℝ → ℂ) x‖ ≤ A) →
      ∀ η : ℝ, 0 ≤ η → ∀ a b : Fin N → Fin L → ℝ,
      (∀ i j, |a i j| ≤ S) → (∀ i j, |b i j| ≤ S) →
      (∀ i j, |a i j-b i j| ≤ η) → ∀ T : Fin L → HermiteScale (-((liftOrder p) : ℤ)),
      ‖∑ i, ∑ j,
        (combDistributionTranslation (a i j) (hermiteScaleDistribution (liftOrder p) (T j))
          (SchwartzMap.smulLeftCLM ℂ (ζ i) f) -
        combDistributionTranslation (b i j) (hermiteScaleDistribution (liftOrder p) (T j))
          (SchwartzMap.smulLeftCLM ℂ (ζ i) f))‖ ≤
        stagePhaseErrorConstant p N L ζ H S hH hS * A * η * ∑ j, ‖T j‖ :=
  phaseErrorConstantAtOrder_spec p (liftOrder p) N L le_rfl ζ H S hH hS

private theorem finite_double_sum_bound {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : ι → κ → ℝ) (hf : ∀ i j, 0 ≤ f i j) (i : ι) (j : κ) :
    f i j ≤ 1 + ∑ a, ∑ b, f a b := by
  have hrow : f i j ≤ ∑ b, f i b :=
    Finset.single_le_sum (fun b _ => hf i b) (Finset.mem_univ j)
  have hsum : (∑ b, f i b) ≤ ∑ a, ∑ b, f a b := by
    exact Finset.single_le_sum (fun a _ => Finset.sum_nonneg (fun b _ => hf a b)) (Finset.mem_univ i)
  linarith

/-- One deterministic lower translation bound and phase tolerance pay both actual
errors for every p≤M and D≤12p. No source, realized scale or future gap is an input. -/
theorem exists_joint_stage_phase_parameters (M : ℕ+) (N L : ℕ)
    (ζ : Fin N → SchwartzMap ℝ ℂ) (H S ρ ε : ℝ)
    (hH : 0 ≤ H) (hS : 0 ≤ S) (hρ : 0 < ρ) (hε : 0 < ε) :
    ∃ H₀ η : ℝ, (M : ℝ)+1 ≤ H₀ ∧ 0 < η ∧ η ≤ ρ/10 ∧ η ≤ 1/(M : ℝ) ∧
      (∀ p ≤ M.val, ∀ D ≤ 12*p, stageLeadingErrorConstant p D N L ζ H hH / H₀ ≤ ε) ∧
      (∀ p ≤ M.val, stagePhaseErrorConstant p N L ζ H S hH hS * η ≤ ε) := by
  classical
  let E (p d : ℕ) := stageLeadingErrorConstant p d N L ζ H hH
  let F (p : ℕ) := stagePhaseErrorConstant p N L ζ H S hH hS
  have hE p d : 0 < E p d := stageLeadingErrorConstant_pos p d N L ζ H hH
  have hF p : 0 < F p := stagePhaseErrorConstant_pos p N L ζ H S hH hS
  let B : ℝ := 1 + ∑ p : Fin (M.val+1), ∑ d : Fin (12*M.val+1), E p.val d.val
  let C : ℝ := 1 + ∑ p : Fin (M.val+1), F p.val
  have hB : 0 < B := by
    have hs : 0 ≤ ∑ p : Fin (M.val+1), ∑ d : Fin (12*M.val+1), E p.val d.val :=
      Finset.sum_nonneg (fun p _ => Finset.sum_nonneg (fun d _ => (hE p.val d.val).le))
    dsimp [B]
    linarith
  have hC : 0 < C := by
    have hs : 0 ≤ ∑ p : Fin (M.val+1), F p.val := Finset.sum_nonneg (fun p _ => (hF p.val).le)
    dsimp [C]
    linarith
  have hM : 0 < (M : ℝ) := by exact_mod_cast M.pos
  let H₀ : ℝ := max ((M : ℝ)+1) (B/ε)
  let η : ℝ := min (ρ/10) (min (1/(M : ℝ)) (ε/C))
  have hH₀ : (M : ℝ)+1 ≤ H₀ := le_max_left _ _
  have hH₀pos : 0 < H₀ := lt_of_lt_of_le (by positivity) hH₀
  have hη : 0 < η := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  refine ⟨H₀,η,hH₀,hη,min_le_left _ _,(min_le_right _ _).trans (min_le_left _ _),?_,?_⟩
  · intro p hp d hd
    have hp' : p < M.val+1 := by omega
    have hd' : d < 12*M.val+1 := by omega
    have heb : E p d ≤ B :=
      finite_double_sum_bound
        (fun (i : Fin (M.val+1)) (j : Fin (12*M.val+1)) => E i.val j.val)
        (fun i j => (hE i.val j.val).le) ⟨p,hp'⟩ ⟨d,hd'⟩
    have hbh : B ≤ ε*H₀ := by
      have hmax : B/ε ≤ H₀ := le_max_right _ _
      exact ((div_le_iff₀ hε).mp hmax).trans_eq (mul_comm _ _)
    exact (div_le_iff₀ hH₀pos).mpr (heb.trans hbh)
  · intro p hp
    have hp' : p < M.val+1 := by omega
    have hf : F p ≤ C := by
      have hsum := Finset.single_le_sum (fun (i : Fin (M.val+1)) _ => (hF i.val).le)
        (Finset.mem_univ (⟨p,hp'⟩ : Fin (M.val+1)))
      dsimp [C]
      linarith
    have het : η ≤ ε/C := (min_le_right _ _).trans (min_le_right _ _)
    have hbudget : C*η ≤ ε := by
      have h := (le_div_iff₀ hC).mp het
      nlinarith
    exact (mul_le_mul_of_nonneg_right hf hη.le).trans hbudget

/-- A positive bound for the number of original coefficients at every degree admitted at stage M. -/
def stageCoefficientCount (M : ℕ) : ℕ := 1 + 2*M*(12*M+1)

/-- The count bound includes both reciprocal labels and every polynomial coefficient. -/
theorem stageCoefficientCount_bound (M p D : ℕ) (hp : p ≤ M) (hD : D ≤ 12*p) :
    2*M*(D+1) ≤ stageCoefficientCount M := by
  have hd : D+1 ≤ 12*M+1 := by omega
  exact (Nat.mul_le_mul_left (2*M) hd).trans (by unfold stageCoefficientCount; omega)

/-- Deterministic finite-stage selection in the required order: both error budgets,
then a bounded actual torus net with the prescribed failure probability. -/
theorem exists_stage_phase_parameters_and_net (M : ℕ+) (N : ℕ)
    (ζ : Fin N → SchwartzMap ℝ ℂ) (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ H₀ η H₁ : ℝ, (M : ℝ)+1 ≤ H₀ ∧ 0 < η ∧ η ≤ ρ/10 ∧ η ≤ 1/(M : ℝ) ∧ H₀ ≤ H₁ ∧
      (∀ p ≤ M.val, ∀ D ≤ 12*p,
        stageLeadingErrorConstant p D N (2*M.val) ζ M (by positivity) / H₀ ≤
          (2 : ℝ)^(-(M.val : ℤ)) / stageCoefficientCount M.val) ∧
      (∀ p ≤ M.val,
        stagePhaseErrorConstant p N (2*M.val) ζ M ((M : ℝ)+4) (by positivity) (by positivity) * η ≤
          (2 : ℝ)^(-(M.val : ℤ)) / stageCoefficientCount M.val) ∧
      scaleProbability (prefixSegmentNetEvent M.val H₀ H₁ (η/4))ᶜ ≤
        ENNReal.ofReal ((2 : ℝ)^(-(M.val+4 : ℤ))) := by
  have hcount : 0 < (stageCoefficientCount M.val : ℝ) := by
    unfold stageCoefficientCount
    positivity
  have hbudget : 0 < (2 : ℝ)^(-(M.val : ℤ)) / stageCoefficientCount M.val := by positivity
  obtain ⟨H₀,η,hH₀,hη,hηρ,hηM,hlead,hphase⟩ :=
    exists_joint_stage_phase_parameters M N (2*M.val) ζ M ((M : ℝ)+4) ρ
      ((2 : ℝ)^(-(M.val : ℤ)) / stageCoefficientCount M.val)
      (by positivity) (by positivity) hρ hbudget
  obtain ⟨H₁,hH₁,hnet⟩ := exists_stage_segment_net M.val H₀ η hη
  exact ⟨H₀,η,H₁,hH₀,hη,hηρ,hηM,hH₁,hlead,hphase,hnet⟩

end
end MeyerGeneralProblem.Adaptive
