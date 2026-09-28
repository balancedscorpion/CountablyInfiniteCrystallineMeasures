module

public import MeyerGeneralProblem.Cardinal.Adaptive.VariableGaugeRows

@[expose] public section

/-! Exact cross-axis commutation of the retained variable phase weights. -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section

/-- A complete analytic coordinate inherits every commutation of its sine map. -/
theorem seamCoordinateOperator_commute_right (S A : SeamMomentArray →L[ℂ] SeamMomentArray)
    (h : Commute S A) : Commute (seamCoordinateOperator S) A := by
  have hh : Commute (seamArcsineFactor (S*S)) A :=
    Commute.tsum_left A (fun n => ((h.mul_left h).pow_left n).smul_left _)
  exact (h.mul_left hh).smul_left _

/-- The row sine commutes exactly with every actual spectral phase diagonal. -/
theorem variableSineRow_columnWeight_commute (κ : ℂ) (ε δ : ℕ → ℝ) (ρ σ : ℝ)
    (hρ : ρ ≤ 1/2) (hε : ∀ i, 0 < ε i ∧ ε i ≤ ρ)
    (hδ : ∀ i, 0 < δ i ∧ δ i ≤ σ) :
    Commute (variableSineRow κ ε ρ hρ hε) (variableNewtonColumnWeight δ σ hδ) := by
  change variableSineRow κ ε ρ hρ hε * variableNewtonColumnWeight δ σ hδ = _
  ext u p
  rcases p with ⟨⟨i,e⟩,j,f⟩
  change variableSineRow κ ε ρ hρ hε (variableNewtonColumnWeight δ σ hδ u) ((i,e),(j,f)) =
    variableNewtonColumnWeight δ σ hδ (variableSineRow κ ε ρ hρ hε u) ((i,e),(j,f))
  cases e <;> simp only [variableSineRow_apply,variableNewtonColumnWeight_apply,
    Bool.false_eq_true,ite_false,ite_true] <;> ring

/-- The complete row coordinate preserves the exact spectral phase weight. -/
theorem variableCoordinateRow_columnWeight_commute (κ : ℂ) (hκ : κ ≠ 0)
    (ε δ : ℕ → ℝ) (ρ σ : ℝ) (hρ : ρ ≤ 1/2)
    (hε : ∀ i, 0 < ε i ∧ ε i ≤ ρ) (hδ : ∀ i, 0 < δ i ∧ δ i ≤ σ) :
    Commute (variableCoordinateRow κ ε ρ hρ hε) (variableNewtonColumnWeight δ σ hδ) := by
  rw [variableCoordinateRow_eq_seamCoordinate κ hκ]
  exact seamCoordinateOperator_commute_right _ _
    (variableSineRow_columnWeight_commute κ ε δ ρ σ hρ hε hδ)

/-- The entire row inverse-sine factor preserves the spectral phase weight. -/
theorem variableCoordinateFactor_columnWeight_commute (κ : ℂ) (hκ : κ ≠ 0)
    (ε δ : ℕ → ℝ) (ρ σ : ℝ) (hρ : ρ ≤ 1/2)
    (hε : ∀ i, 0 < ε i ∧ ε i ≤ ρ) (hδ : ∀ i, 0 < δ i ∧ δ i ≤ σ) :
    Commute (variableCoordinateFactor ε ρ hρ hε) (variableNewtonColumnWeight δ σ hδ) := by
  have h := variableSineRow_columnWeight_commute κ ε δ ρ σ hρ hε hδ
  unfold variableCoordinateFactor boundedOperatorSeries
  rw [← variableSineRow_square κ hκ]
  exact Commute.tsum_left _ (fun n => ((h.mul_left h).pow_left n).smul_left _)

/-- The full bounded Newton row core commutes with the other actual weight. -/
theorem variableNewtonRowCore_columnWeight_commute (ε δ : ℕ → ℝ) (ρ σ : ℝ) (hρ : ρ ≤ 1/2)
    (hε : ∀ i, 0 < ε i ∧ ε i ≤ ρ) (hδ : ∀ i, 0 < δ i ∧ δ i ≤ σ) :
    Commute (variableNewtonRowCore ε ρ hρ hε) (variableNewtonColumnWeight δ σ hδ) := by
  change variableNewtonRowCore ε ρ hρ hε * variableNewtonColumnWeight δ σ hδ = _
  ext u p
  rcases p with ⟨⟨i,e⟩,j,f⟩
  change variableNewtonRowCore ε ρ hρ hε (variableNewtonColumnWeight δ σ hδ u) ((i,e),(j,f)) =
    variableNewtonColumnWeight δ σ hδ (variableNewtonRowCore ε ρ hρ hε u) ((i,e),(j,f))
  simp only [variableNewtonRowCore_apply,variableNewtonColumnWeight_apply,seamRowShift_apply]
  ring

/-- The row parity input/flip map retains the independent spectral weight. -/
theorem rowFlipProjection_columnWeight_commute (e : Bool) (δ : ℕ → ℝ) (σ : ℝ)
    (hδ : ∀ i, 0 < δ i ∧ δ i ≤ σ) :
    Commute (seamRowFlip.comp (momentProjection (seamRowParity e))) (variableNewtonColumnWeight δ σ hδ) := by
  change (seamRowFlip.comp (momentProjection (seamRowParity e))) * variableNewtonColumnWeight δ σ hδ = _
  ext u p
  rcases p with ⟨⟨i,a⟩,j,f⟩
  change seamRowFlip (momentProjection (seamRowParity e) (variableNewtonColumnWeight δ σ hδ u)) ((i,a),(j,f)) =
    variableNewtonColumnWeight δ σ hδ (seamRowFlip (momentProjection (seamRowParity e) u)) ((i,a),(j,f))
  cases a <;> cases e <;> simp [seamRowFlip_apply,momentProjection_apply,seamRowParity,variableNewtonColumnWeight_apply]

/-- The constructed lower core commutes with the independent spectral weight. -/
theorem variableCoordinateLowerCore_columnWeight_commute (κ : ℂ) (hκ : κ ≠ 0)
    (ε δ : ℕ → ℝ) (ρ σ : ℝ) (hρ : ρ ≤ 1/2)
    (hε : ∀ i, 0 < ε i ∧ ε i ≤ ρ) (hδ : ∀ i, 0 < δ i ∧ δ i ≤ σ) :
    Commute (variableCoordinateLowerCore ε ρ hρ hε) (variableNewtonColumnWeight δ σ hδ) := by
  exact ((variableNewtonRowCore_columnWeight_commute ε δ ρ σ hρ hε hδ).mul_left
    ((rowFlipProjection_columnWeight_commute false δ σ hδ).mul_left
      (variableCoordinateFactor_columnWeight_commute κ hκ ε δ ρ σ hρ hε hδ))).smul_left _

/-- The complete row Newton operator preserves the actual spectral phase diagonal. -/
theorem variableNewtonRow_columnWeight_commute (ε δ : ℕ → ℝ) (ρ σ : ℝ) (hρ : ρ ≤ 1/2)
    (hε : ∀ i, 0 < ε i ∧ ε i ≤ ρ) (hδ : ∀ i, 0 < δ i ∧ δ i ≤ σ) :
    Commute (variableNewtonRow ε ρ hρ hε) (variableNewtonColumnWeight δ σ hδ) := by
  change variableNewtonRow ε ρ hρ hε * variableNewtonColumnWeight δ σ hδ = _
  ext u p
  rcases p with ⟨⟨i,e⟩,j,f⟩
  change variableNewtonRow ε ρ hρ hε (variableNewtonColumnWeight δ σ hδ u) ((i,e),(j,f)) =
    variableNewtonColumnWeight δ σ hδ (variableNewtonRow ε ρ hρ hε u) ((i,e),(j,f))
  simp only [variableNewtonRow_apply,variableNewtonColumnWeight_apply,seamRowShift_apply]
  ring

/-- The bounded square core preserves the independent column weight. -/
theorem variableCoordinateSquareCore_columnWeight_commute (κ : ℂ) (hκ : κ ≠ 0)
    (ε δ : ℕ → ℝ) (ρ σ : ℝ) (hρ : ρ ≤ 1/2)
    (hε : ∀ i, 0 < ε i ∧ ε i ≤ ρ) (hδ : ∀ i, 0 < δ i ∧ δ i ≤ σ) :
    Commute (variableCoordinateSquareCore ε ρ hρ hε) (variableNewtonColumnWeight δ σ hδ) := by
  have hJ := variableNewtonRow_columnWeight_commute ε δ ρ σ hρ hε hδ
  have hB := variableNewtonRowCore_columnWeight_commute ε δ ρ σ hρ hε hδ
  have hF := variableCoordinateFactor_columnWeight_commute κ hκ ε δ ρ σ hρ hε hδ
  exact ((hB.mul_left (((Commute.one_left _).smul_left (2:ℂ)).sub_left hJ)).mul_left
    (hF.pow_left 2)).smul_left _

/-- All odd-power cores retain cross-axis commutation. -/
theorem variableCoordinateOddCore_columnWeight_commute (κ : ℂ) (hκ : κ ≠ 0)
    (ε δ : ℕ → ℝ) (ρ σ : ℝ) (hρ : ρ ≤ 1/2)
    (hε : ∀ i, 0 < ε i ∧ ε i ≤ ρ) (hδ : ∀ i, 0 < δ i ∧ δ i ≤ σ) (m : ℕ) :
    Commute (variableCoordinateOddCore ε ρ hρ hε κ m) (variableNewtonColumnWeight δ σ hδ) :=
  (variableCoordinateLowerCore_columnWeight_commute κ hκ ε δ ρ σ hρ hε hδ).mul_left
    (((variableCoordinateRow_columnWeight_commute κ hκ ε δ ρ σ hρ hε hδ).pow_left 2).pow_left m)

/-- Actual physical parity selection commutes with any actual spectral phase diagonal. -/
theorem rowProjection_columnWeight_commute (e : Bool) (δ : ℕ → ℝ) (σ : ℝ)
    (hδ : ∀ i, 0 < δ i ∧ δ i ≤ σ) :
    Commute (momentProjection (seamRowParity e)) (variableNewtonColumnWeight δ σ hδ) := by
  change momentProjection (seamRowParity e) * variableNewtonColumnWeight δ σ hδ = _
  ext u p
  rcases p with ⟨⟨i,a⟩,j,f⟩
  change momentProjection (seamRowParity e) (variableNewtonColumnWeight δ σ hδ u) ((i,a),(j,f)) =
    variableNewtonColumnWeight δ σ hδ (momentProjection (seamRowParity e) u) ((i,a),(j,f))
  cases a <;> cases e <;> simp [momentProjection_apply,seamRowParity,variableNewtonColumnWeight_apply]

/-- The physical parity projection also commutes with its own actual phase weight. -/
theorem rowProjection_rowWeight_commute (e : Bool) (ε : ℕ → ℝ) (ρ : ℝ)
    (hε : ∀ i, 0 < ε i ∧ ε i ≤ ρ) :
    Commute (momentProjection (seamRowParity e)) (variableNewtonRowWeight ε ρ hε) := by
  change momentProjection (seamRowParity e) * variableNewtonRowWeight ε ρ hε = _
  ext u p
  rcases p with ⟨⟨i,a⟩,j,f⟩
  change momentProjection (seamRowParity e) (variableNewtonRowWeight ε ρ hε u) ((i,a),(j,f)) =
    variableNewtonRowWeight ε ρ hε (momentProjection (seamRowParity e) u) ((i,a),(j,f))
  cases a <;> cases e <;> simp [momentProjection_apply,seamRowParity,variableNewtonRowWeight_apply]

/-- Each positive coordinate power has an explicitly bounded actual phase
factor, and its bounded core still commutes with the independent phase weight. -/
theorem variableCoordinate_positive_power_factor (κ : ℂ) (hκ : κ ≠ 0) (hk : ‖κ‖ ≤ 1)
    (ε δ : ℕ → ℝ) (ρ σ : ℝ) (hρ : ρ ≤ 1/2) (hsmall : ρ ≤ 1/32)
    (hε : ∀ i, 0 < ε i ∧ ε i ≤ ρ) (hδ : ∀ i, 0 < δ i ∧ δ i ≤ σ) (n : ℕ) :
    ∃ V : SeamMomentArray →L[ℂ] SeamMomentArray,
      momentProjection (seamRowParity true) * (variableCoordinateRow κ ε ρ hρ hε)^(n+1) =
        variableNewtonRowWeight ε ρ hε * V ∧
      ‖V‖ ≤ ‖κ⁻¹‖*ρ^(n/2) ∧ Commute V (variableNewtonColumnWeight δ σ hδ) := by
  have hr : 0 ≤ ρ := (hε 0).1.le.trans (hε 0).2
  have hk1 : 1 ≤ ‖κ⁻¹‖ := by
    rw [norm_inv,inv_eq_one_div]
    exact (le_div_iff₀ (norm_pos_iff.mpr hκ)).2 (by simpa using hk)
  rcases Nat.even_or_odd n with hn | hn
  · obtain ⟨m,rfl⟩ := even_iff_exists_two_mul.mp hn
    refine ⟨κ⁻¹ • variableCoordinateOddCore ε ρ hρ hε κ m, ?_, ?_, ?_⟩
    · rw [variableCoordinate_odd_power_factor,mul_smul_comm]
    · rw [norm_smul]
      simpa using mul_le_mul_of_nonneg_left
        (variableCoordinateOddCore_norm_le κ hκ ε ρ hρ hsmall hε m) (norm_nonneg κ⁻¹)
    · exact (variableCoordinateOddCore_columnWeight_commute κ hκ ε δ ρ σ hρ hε hδ m).smul_left _
  · obtain ⟨m,rfl⟩ := hn.exists_bit1
    let V := momentProjection (seamRowParity true) *
      (variableCoordinateSquareCore ε ρ hρ hε * ((variableCoordinateRow κ ε ρ hρ hε)^2)^m)
    refine ⟨V, ?_, ?_, ?_⟩
    · have he : 2*m+1+1=2*(m+1) := by omega
      rw [he,variableCoordinate_even_power_factor κ hκ,← mul_assoc,
        (rowProjection_rowWeight_commute true ε ρ hε).eq,mul_assoc]
    · have hV : ‖V‖ ≤ ρ^m := by
        apply (norm_mul_le _ _).trans
        exact (mul_le_mul (momentProjection_norm_le_one _)
          (variableCoordinateEvenCore_norm_le κ hκ ε ρ hρ hsmall hε m) (norm_nonneg _) zero_le_one).trans (by simp)
      have hdiv : (2*m+1)/2=m := by omega
      rw [hdiv]
      exact hV.trans (le_mul_of_one_le_left (pow_nonneg hr _) hk1)
    · exact (rowProjection_columnWeight_commute true δ σ hδ).mul_left
        ((variableCoordinateSquareCore_columnWeight_commute κ hκ ε δ ρ σ hρ hε hδ).mul_left
          (((variableCoordinateRow_columnWeight_commute κ hκ ε δ ρ σ hρ hε hδ).pow_left 2).pow_left m))

end
end MeyerGeneralProblem.Adaptive
