module

public import MeyerGeneralProblem.Cardinal.Adaptive.VariableCoordinateOperators

@[expose] public section

/-! Actual phase factors in every odd and even coordinate power. -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section

/-- The odd physical output of the whole coordinate map is exactly its lower block. -/
theorem variableCoordinate_odd_output (κ : ℂ) (ε : ℕ → ℝ) (ρ : ℝ) (hρ : ρ ≤ 1/2)
    (hε : ∀ i, 0 < ε i ∧ ε i ≤ ρ) :
    momentProjection (seamRowParity true) * variableCoordinateRow κ ε ρ hρ hε =
      κ⁻¹ • ((variableNewtonRowWeight ε ρ hε) * (variableCoordinateLowerCore ε ρ hρ hε)) := by
  change _ = κ⁻¹ • ((variableNewtonRowWeight ε ρ hε).comp (variableCoordinateLowerCore ε ρ hρ hε))
  rw [← variableCoordinate_lower_factor]
  ext u p
  rcases p with ⟨⟨i,e⟩,j,f⟩
  change (momentProjection (seamRowParity true)
    ((2*(Real.pi:ℂ))⁻¹ • variableSineRow κ ε ρ hρ hε (variableCoordinateFactor ε ρ hρ hε u))) ((i,e),(j,f)) = _
  cases e <;> simp [momentProjection_apply,seamRowParity,variableSineRow_apply,
    variableSineLower_apply]

/-- The complete odd-power core after removal of its actual next-level weight. -/
def variableCoordinateOddCore (ε : ℕ → ℝ) (ρ : ℝ) (hρ : ρ ≤ 1/2)
    (hε : ∀ i, 0 < ε i ∧ ε i ≤ ρ) (κ : ℂ) (m : ℕ) :
    SeamMomentArray →L[ℂ] SeamMomentArray :=
  variableCoordinateLowerCore ε ρ hρ hε * ((variableCoordinateRow κ ε ρ hρ hε)^2)^m

/-- Every odd power retains the same actual row weight, including the first power. -/
theorem variableCoordinate_odd_power_factor (κ : ℂ) (ε : ℕ → ℝ) (ρ : ℝ) (hρ : ρ ≤ 1/2)
    (hε : ∀ i, 0 < ε i ∧ ε i ≤ ρ) (m : ℕ) :
    momentProjection (seamRowParity true) * (variableCoordinateRow κ ε ρ hρ hε)^(2*m+1) =
      κ⁻¹ • ((variableNewtonRowWeight ε ρ hε) * variableCoordinateOddCore ε ρ hρ hε κ m) := by
  rw [pow_succ',← mul_assoc,variableCoordinate_odd_output,smul_mul_assoc,mul_assoc,pow_mul]
  rfl

/-- Every positive even power retains the same next-level phase weight. -/
theorem variableCoordinate_even_power_factor (κ : ℂ) (hκ : κ ≠ 0) (ε : ℕ → ℝ) (ρ : ℝ)
    (hρ : ρ ≤ 1/2) (hε : ∀ i, 0 < ε i ∧ ε i ≤ ρ) (m : ℕ) :
    (variableCoordinateRow κ ε ρ hρ hε)^(2*(m+1)) =
      (variableNewtonRowWeight ε ρ hε) * (variableCoordinateSquareCore ε ρ hρ hε *
        ((variableCoordinateRow κ ε ρ hρ hε)^2)^m) := by
  rw [pow_mul,pow_succ',variableCoordinate_square_factor κ hκ]
  rw [mul_assoc]

/-- Uniform square decay in the complete variable coordinate operator. -/
theorem variableCoordinate_square_norm_le (κ : ℂ) (hκ : κ ≠ 0) (ε : ℕ → ℝ) (ρ : ℝ)
    (hρ : ρ ≤ 1/2) (hsmall : ρ ≤ 1/32) (hε : ∀ i, 0 < ε i ∧ ε i ≤ ρ) :
    ‖(variableCoordinateRow κ ε ρ hρ hε)^2‖ ≤ ρ := by
  rw [variableCoordinate_square_factor κ hκ]
  apply (norm_mul_le _ _).trans
  exact (mul_le_mul (variableNewtonRowWeight_norm_le ε ρ hε)
    (variableCoordinateSquareCore_norm_le ε ρ hρ hsmall hε) (norm_nonneg _)
    ((hε 0).1.le.trans (hε 0).2)).trans (by simp)

/-- The complete odd-power core decays geometrically after the actual row factor. -/
theorem variableCoordinateOddCore_norm_le (κ : ℂ) (hκ : κ ≠ 0) (ε : ℕ → ℝ) (ρ : ℝ)
    (hρ : ρ ≤ 1/2) (hsmall : ρ ≤ 1/32) (hε : ∀ i, 0 < ε i ∧ ε i ≤ ρ) (m : ℕ) :
    ‖variableCoordinateOddCore ε ρ hρ hε κ m‖ ≤ ρ^m := by
  unfold variableCoordinateOddCore
  apply (norm_mul_le _ _).trans
  exact (mul_le_mul (variableCoordinateLowerCore_norm_le ε ρ hρ hsmall hε)
    ((norm_pow_le _ m).trans (pow_le_pow_left₀ (norm_nonneg _)
      (variableCoordinate_square_norm_le κ hκ ε ρ hρ hsmall hε) m)) (norm_nonneg _) zero_le_one).trans (by simp)

/-- The positive even-power core has the same geometric decay. -/
theorem variableCoordinateEvenCore_norm_le (κ : ℂ) (hκ : κ ≠ 0) (ε : ℕ → ℝ) (ρ : ℝ)
    (hρ : ρ ≤ 1/2) (hsmall : ρ ≤ 1/32) (hε : ∀ i, 0 < ε i ∧ ε i ≤ ρ) (m : ℕ) :
    ‖variableCoordinateSquareCore ε ρ hρ hε * ((variableCoordinateRow κ ε ρ hρ hε)^2)^m‖ ≤ ρ^m := by
  apply (norm_mul_le _ _).trans
  exact (mul_le_mul (variableCoordinateSquareCore_norm_le ε ρ hρ hsmall hε)
    ((norm_pow_le _ m).trans (pow_le_pow_left₀ (norm_nonneg _)
      (variableCoordinate_square_norm_le κ hκ ε ρ hρ hsmall hε) m)) (norm_nonneg _) zero_le_one).trans (by simp)

/-- Whole arcsine coordinate maps of commuting sine operators commute. This
uses the complete series in both axes, with no truncation or finite support. -/
theorem seamCoordinateOperator_commute (S T : SeamMomentArray →L[ℂ] SeamMomentArray)
    (h : Commute S T) : Commute (seamCoordinateOperator S) (seamCoordinateOperator T) := by
  have hSS : Commute (S*S) T := h.mul_left h
  have hSTT : Commute S (T*T) := h.mul_right h
  have hSSTT : Commute (S*S) (T*T) := hSS.mul_right hSS
  have hSH : Commute S (seamArcsineFactor (T*T)) := by
    exact Commute.tsum_right S (fun n => (hSTT.pow_right n).smul_right _)
  have hHT : Commute (seamArcsineFactor (S*S)) T := by
    exact Commute.tsum_left T (fun n => (hSS.pow_left n).smul_left _)
  have hHH : Commute (seamArcsineFactor (S*S)) (seamArcsineFactor (T*T)) := by
    apply Commute.tsum_left
    intro n
    apply Commute.smul_left
    apply Commute.tsum_right
    intro m
    exact ((hSSTT.pow_left n).pow_right m).smul_right _
  exact ((h.mul_right hSH).mul_left (hHT.mul_right hHH)).smul_left _ |>.smul_right _

/-- Actual variable sine multiplication commutes between physical and spectral axes. -/
theorem variableSineRowColumn_commute (κ ν : ℂ) (ε δ : ℕ → ℝ) (ρ σ : ℝ)
    (hρ : ρ ≤ 1/2) (hσ : σ ≤ 1/2)
    (hε : ∀ i, 0 < ε i ∧ ε i ≤ ρ) (hδ : ∀ i, 0 < δ i ∧ δ i ≤ σ) :
    Commute (variableSineRow κ ε ρ hρ hε) (variableSineColumn ν δ σ hσ hδ) := by
  apply Commute.symm
  change variableSineColumn ν δ σ hσ hδ * variableSineRow κ ε ρ hρ hε = _
  ext u p
  rcases p with ⟨⟨i,e⟩,j,f⟩
  change variableSineColumn ν δ σ hσ hδ (variableSineRow κ ε ρ hρ hε u) ((i,e),(j,f)) =
    variableSineRow κ ε ρ hρ hε (variableSineColumn ν δ σ hσ hδ u) ((i,e),(j,f))
  cases e <;> cases f <;> simp only [variableSineRow_apply,variableSineColumn_apply,
    Bool.false_eq_true,ite_false,ite_true] <;> ring

/-- The variable coordinate definition agrees exactly with the shared entire
arcsine coordinate construction. -/
theorem variableCoordinateRow_eq_seamCoordinate (κ : ℂ) (hκ : κ ≠ 0) (ε : ℕ → ℝ) (ρ : ℝ)
    (hρ : ρ ≤ 1/2) (hε : ∀ i, 0 < ε i ∧ ε i ≤ ρ) :
    variableCoordinateRow κ ε ρ hρ hε=seamCoordinateOperator (variableSineRow κ ε ρ hρ hε) := by
  unfold variableCoordinateRow seamCoordinateOperator
  congr 2
  unfold variableCoordinateFactor seamArcsineFactor
  congr 1
  exact (variableSineRow_square κ hκ ε ρ hρ hε).symm

end
end MeyerGeneralProblem.Adaptive
