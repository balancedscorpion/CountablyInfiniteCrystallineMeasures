module

public import MeyerGeneralProblem.Cardinal.Adaptive.VariableAxisWeights
public import MeyerGeneralProblem.Cardinal.Adaptive.SeamCoordinateIntertwining

@[expose] public section

/-! Pairing the two actual phase factors in complete coordinate powers. -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section

def axisConjugation : (SeamMomentArray →L[ℂ] SeamMomentArray) →+*
    (SeamMomentArray →L[ℂ] SeamMomentArray) where
  toFun A := seamTranspose.comp (A.comp seamTranspose)
  map_one' := by ext u p; exact congrArg (fun v : SeamMomentArray => v p) (seamTranspose_involutive u)
  map_mul' A B := by
    ext u p
    change seamTranspose (A (B (seamTranspose u))) p =
      seamTranspose (A (seamTranspose (seamTranspose (B (seamTranspose u))))) p
    rw [seamTranspose_involutive]
  map_zero' := by ext u p; simp
  map_add' A B := by ext u p; simp

private theorem axisConjugation_norm (A : SeamMomentArray →L[ℂ] SeamMomentArray) :
    ‖axisConjugation A‖ ≤ ‖A‖ := seamTranspose_conjugate_norm A

private theorem axisConjugation_projection :
    axisConjugation (momentProjection (seamRowParity true)) =
      momentProjection {p : SeamMomentIndex | p.2.2=true} := by
  ext u p
  rcases p with ⟨⟨i,e⟩,j,f⟩
  change (momentProjection (seamRowParity true) (seamTranspose u)) ((j,f),(i,e)) = _
  cases f <;> simp [momentProjection_apply,seamRowParity,seamTranspose_apply]

private theorem axisConjugation_weight (δ : ℕ → ℝ) (σ : ℝ)
    (hδ : ∀ i, 0 < δ i ∧ δ i ≤ σ) :
    axisConjugation (variableNewtonRowWeight δ σ hδ)=variableNewtonColumnWeight δ σ hδ := by
  ext u p
  rfl

/-- Every positive spectral power also retains its genuine next-level phase
factor, derived by exact axis exchange on the whole Hilbert space. -/
theorem variableCoordinateSourceColumn_positive_power_factor (Q S : ℕ) (hQ : 1 ≤ Q) (hS : 1 ≤ S)
    (n : ℕ) : ∃ V : SeamMomentArray →L[ℂ] SeamMomentArray,
      momentProjection {p : SeamMomentIndex | p.2.2=true} *
        (variableCoordinateSourceColumn Q S hQ hS)^(n+1) =
        variableNewtonColumnWeight (rapidDistance Q S) (shrinkingNewtonSourceKappa^4)
          (variableNewton_source_phase_bound Q S hQ hS) * V ∧
      ‖V‖ ≤ shrinkingNewtonSourceKappa⁻¹ * (shrinkingNewtonSourceKappa^4)^(n/2) := by
  obtain ⟨V,hV,hn,hcomm⟩ := variableCoordinate_positive_power_factor (shrinkingNewtonSourceKappa:ℂ)
    (by norm_num [shrinkingNewtonSourceKappa]) (by norm_num [shrinkingNewtonSourceKappa])
    (rapidDistance Q S) (rapidDistance Q S) (shrinkingNewtonSourceKappa^4) (shrinkingNewtonSourceKappa^4)
    (by norm_num [shrinkingNewtonSourceKappa]) (by norm_num [shrinkingNewtonSourceKappa])
    (variableNewton_source_phase_bound Q S hQ hS) (variableNewton_source_phase_bound Q S hQ hS) n
  refine ⟨axisConjugation V,?_,?_⟩
  · have he := congrArg axisConjugation hV
    rw [map_mul,map_pow,axisConjugation_projection,map_mul,axisConjugation_weight] at he
    exact he
  · exact (axisConjugation_norm V).trans (by
      simpa only [norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos shrinkingNewtonSourceKappa_pos] using hn)

/-- The actual variable spectral coordinate is the whole arcsine map of the
actual spectral sine, by norm-convergent axis intertwining. -/
theorem variableCoordinateSourceColumn_eq_seamCoordinate (Q S : ℕ) (hQ : 1 ≤ Q) (hS : 1 ≤ S) :
    variableCoordinateSourceColumn Q S hQ hS=seamCoordinateOperator (variableSineSourceColumn Q S hQ hS) := by
  have hs : ‖variableSineSourceRow Q S hQ hS * variableSineSourceRow Q S hQ hS‖ < 1 := by
    change ‖(variableSineRow _ _ _ _ _).comp (variableSineRow _ _ _ _ _)‖ < 1
    rw [variableSineRow_square _ (by norm_num [shrinkingNewtonSourceKappa])]
    apply (variableNewtonRow_kernel_norm_le (rapidDistance Q S) (shrinkingNewtonSourceKappa^4)
      (by norm_num [shrinkingNewtonSourceKappa]) (by norm_num [shrinkingNewtonSourceKappa])
      (variableNewton_source_phase_bound Q S hQ hS)).trans_lt
    norm_num [shrinkingNewtonSourceKappa]
  unfold variableCoordinateSourceColumn variableCoordinateSourceRow
  rw [variableCoordinateRow_eq_seamCoordinate _ (by norm_num [shrinkingNewtonSourceKappa])]
  exact (seamCoordinateOperator_transpose (variableSineSourceRow Q S hQ hS) hs).symm

/-- The complete actual physical and spectral variable coordinates commute. -/
theorem variableCoordinateSource_axes_commute (P R Q S : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R)
    (hQ : 1 ≤ Q) (hS : 1 ≤ S) :
    Commute (variableCoordinateSourceRow P R hP hR) (variableCoordinateSourceColumn Q S hQ hS) := by
  rw [variableCoordinateSourceColumn_eq_seamCoordinate]
  unfold variableCoordinateSourceRow
  rw [variableCoordinateRow_eq_seamCoordinate _ (by norm_num [shrinkingNewtonSourceKappa])]
  apply seamCoordinateOperator_commute
  exact variableSineRowColumn_commute _ _ _ _ _ _ _ _ _ _

private theorem rowCoordinate_columnProjection_commute (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) :
    Commute (variableCoordinateSourceRow P R hP hR)
      (momentProjection {p : SeamMomentIndex | p.2.2=true}) := by
  unfold variableCoordinateSourceRow
  rw [variableCoordinateRow_eq_seamCoordinate _ (by norm_num [shrinkingNewtonSourceKappa])]
  apply seamCoordinateOperator_commute_right
  change variableSineSourceRow P R hP hR * momentProjection {p : SeamMomentIndex | p.2.2=true} = _
  ext u p
  rcases p with ⟨⟨i,e⟩,j,f⟩
  change variableSineSourceRow P R hP hR (momentProjection {p : SeamMomentIndex | p.2.2=true} u) ((i,e),(j,f)) =
    momentProjection {p : SeamMomentIndex | p.2.2=true} (variableSineSourceRow P R hP hR u) ((i,e),(j,f))
  cases e <;> cases f <;> simp [variableSineSourceRow,variableSineRow_apply,momentProjection_apply]

/-- Every positive power of the full two-axis coordinate product retains both
actual next-level phase diagonals and a quantitatively bounded complete core. -/
theorem variableCoordinateSource_paired_power_factor (P R Q S : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R)
    (hQ : 1 ≤ Q) (hS : 1 ≤ S) (n : ℕ) :
    ∃ V : SeamMomentArray →L[ℂ] SeamMomentArray,
      (momentProjection (seamRowParity true) * momentProjection {p : SeamMomentIndex | p.2.2=true}) *
        (variableCoordinateSourceRow P R hP hR * variableCoordinateSourceColumn Q S hQ hS)^(n+1) =
      (variableNewtonRowWeight (rapidDistance P R) (shrinkingNewtonSourceKappa^4)
          (variableNewton_source_phase_bound P R hP hR) *
        variableNewtonColumnWeight (rapidDistance Q S) (shrinkingNewtonSourceKappa^4)
          (variableNewton_source_phase_bound Q S hQ hS)) * V ∧
      ‖V‖ ≤ shrinkingNewtonSourceKappa⁻¹^2 * (shrinkingNewtonSourceKappa^4)^(2*(n/2)) := by
  obtain ⟨A,hA,hnA,hAc⟩ := variableCoordinate_positive_power_factor (shrinkingNewtonSourceKappa:ℂ)
    (by norm_num [shrinkingNewtonSourceKappa]) (by norm_num [shrinkingNewtonSourceKappa])
    (rapidDistance P R) (rapidDistance Q S) (shrinkingNewtonSourceKappa^4) (shrinkingNewtonSourceKappa^4)
    (by norm_num [shrinkingNewtonSourceKappa]) (by norm_num [shrinkingNewtonSourceKappa])
    (variableNewton_source_phase_bound P R hP hR) (variableNewton_source_phase_bound Q S hQ hS) n
  change momentProjection (seamRowParity true) * (variableCoordinateSourceRow P R hP hR)^(n+1) = _ at hA
  obtain ⟨B,hB,hnB⟩ := variableCoordinateSourceColumn_positive_power_factor Q S hQ hS n
  refine ⟨A*B,?_,?_⟩
  · rw [(variableCoordinateSource_axes_commute P R Q S hP hR hQ hS).mul_pow]
    have hc := (rowCoordinate_columnProjection_commute P R hP hR).pow_left (n+1)
    calc
      _ = (momentProjection (seamRowParity true) * (variableCoordinateSourceRow P R hP hR)^(n+1)) *
          (momentProjection {p : SeamMomentIndex | p.2.2=true} * (variableCoordinateSourceColumn Q S hQ hS)^(n+1)) := by
        rw [mul_assoc,←mul_assoc (momentProjection {p : SeamMomentIndex | p.2.2=true}),←hc.eq]
        simp only [mul_assoc]
      _ = (variableNewtonRowWeight (rapidDistance P R) (shrinkingNewtonSourceKappa^4)
          (variableNewton_source_phase_bound P R hP hR) * A) *
          (variableNewtonColumnWeight (rapidDistance Q S) (shrinkingNewtonSourceKappa^4)
          (variableNewton_source_phase_bound Q S hQ hS) * B) := by rw [hA,hB]
      _ = _ := by
        rw [mul_assoc,←mul_assoc A,hAc.eq]
        simp only [mul_assoc]
  · have hna : ‖A‖ ≤ shrinkingNewtonSourceKappa⁻¹ * (shrinkingNewtonSourceKappa^4)^(n/2) := by
      simpa only [norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos shrinkingNewtonSourceKappa_pos] using hnA
    apply (norm_mul_le _ _).trans
    have hh := mul_le_mul hna hnB (norm_nonneg B) (by positivity [shrinkingNewtonSourceKappa_pos])
    convert hh using 1 <;> simp only [pow_mul,pow_two] <;> ring

end
end MeyerGeneralProblem.Adaptive
