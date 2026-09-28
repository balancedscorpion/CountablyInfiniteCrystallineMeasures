module

public import MeyerGeneralProblem.Cardinal.Adaptive.VariableGraphRemainder

@[expose] public section

/-! Triviality of the complete variable signed graph kernel. -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section

private theorem variableP_decomposition (u : SeamMomentArray) :
    seamPProjection u=seamDProjection u+seamCProjection u := by
  ext p
  rcases p with ⟨⟨i,e⟩,j,f⟩
  simp only [seamPProjection,seamDProjection,seamCProjection,momentProjection_apply,
    seamDIndices,seamCIndices,Set.mem_union,Set.mem_setOf_eq,lp.coeFn_add,Pi.add_apply]
  rcases lt_trichotomy i j with hij | rfl | hji
  · cases e <;> cases f <;> simp [hij,ne_of_lt hij]
  · cases e <;> cases f <;> simp
  · cases e <;> cases f <;> simp [not_lt_of_gt hji,ne_of_gt hji]

private theorem variableQ_P (u : SeamMomentArray) : seamQProjection (seamPProjection u)=seamCProjection u := by
  ext p
  rcases p with ⟨⟨i,e⟩,j,f⟩
  simp only [seamQProjection,seamPProjection,seamCProjection,momentProjection_apply,
    seamDIndices,seamCIndices,seamGIndices,Set.mem_union,Set.mem_setOf_eq]
  rcases lt_trichotomy i j with hij | rfl | hji
  · cases e <;> cases f <;> simp [hij,ne_of_lt hij]
  · cases e <;> cases f <;> simp
  · cases e <;> cases f <;> simp [not_lt_of_gt hji,ne_of_gt hji]

private theorem variableG_P (u : SeamMomentArray) : seamDiagonalReading true true (seamPProjection u)=0 := by
  ext n
  simp [seamDiagonalReading_apply,seamPProjection,momentProjection_apply,seamDIndices,seamCIndices]

/-- The complete actual variable graph operator has trivial kernel on its
whole domain flag. The proof uses the bounded normalized full remainder,
retains all complementary coordinates, and never inverts a phase diagonal. -/
theorem variableFullSourceOperator_kernel_zero (P R Q S : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R)
    (hQ : 1 ≤ Q) (hS : 1 ≤ S) (u : SeamMomentArray) (hu : seamPProjection u=u)
    (hF : variableFullSourceOperator P R Q S hP hR hQ hS u=0) : u=0 := by
  let F := variableFullSourceOperator P R Q S hP hR hQ hS
  let N := variableNormalizedGraphRemainder P R Q S hP hR hQ hS
  let D := variableSourceDenominatorMap P R Q S hP hR hQ hS
  have hQeq : seamQProjection u=seamCProjection u := by
    rw [←hu]
    simpa only [hu] using variableQ_P u
  have hC : ‖seamCProjection u‖ ≤ (32*shrinkingNewtonSourceKappa^2)*‖u‖ := by
    have hn := (F-seamQProjection).le_opNorm u
    change ‖F u-seamQProjection u‖ ≤ _ at hn
    rw [show F u=0 from hF,zero_sub,norm_neg,hQeq] at hn
    exact hn.trans (mul_le_mul_of_nonneg_right
      (variableFullSourceOperator_close P R Q S hP hR hQ hS) (norm_nonneg u))
  have hGu : seamDiagonalReading true true u=0 := by rw [←hu]; exact variableG_P u
  have hr := variableFullSourceOperator_diagonal_row P R Q S hP hR hQ hS u
  rw [hF,map_zero,hGu,zero_sub] at hr
  have hreal : D (N u)=variableGraphRowRemainder P R Q S hP hR hQ hS u :=
    congrArg (fun A : SeamMomentArray →L[ℂ] SeamSequence => A u)
      (variableNormalizedGraphRemainder_realizes P R Q S hP hR hQ hS)
  have he : D (N u)=D (Complex.I • seamDiagonalReading false false u) := by
    rw [map_smul,hreal]
    simpa only [neg_neg,add_zero] using eq_neg_add_iff_add_eq.mpr hr.symm
  have hN : N u=Complex.I • seamDiagonalReading false false u :=
    variableSourceDenominatorMap_injective P R Q S hP hR hQ hS he
  have hD : ‖seamDiagonalReading false false u‖ ≤ (128*shrinkingNewtonSourceKappa^2)*‖u‖ := by
    have hn := N.le_opNorm u
    rw [hN,norm_smul,Complex.norm_I,one_mul] at hn
    exact hn.trans (mul_le_mul_of_nonneg_right
      (variableNormalizedGraphRemainder_norm_le P R Q S hP hR hQ hS) (norm_nonneg u))
  have hdec : u=seamDProjection u+seamCProjection u := by rw [←hu]; simpa only [hu] using variableP_decomposition u
  have hn : ‖u‖ ≤ ‖seamDiagonalReading false false u‖+‖seamCProjection u‖ := by
    calc
      _ = ‖seamDProjection u+seamCProjection u‖ := congrArg norm hdec
      _ ≤ ‖seamDProjection u‖+‖seamCProjection u‖ := norm_add_le _ _
      _ = _ := by rw [seamDProjection_eq_diagonal,seamDiagonalEmbedding_norm]
  apply norm_eq_zero.mp
  have hnon := norm_nonneg u
  norm_num [shrinkingNewtonSourceKappa] at hC hD
  linarith

/-- The complete actual signed array equations force both full arrays to
vanish. The hypotheses are literal triangular entries, both signed diagonal
identities, and the genuine entire gauge relation. -/
theorem variableSignedArrays_zero (P R Q S : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R)
    (hQ : 1 ≤ Q) (hS : 1 ≤ S) (u v : SeamMomentArray)
    (huf : ∀ i j e f, j < i → u ((i,e),(j,f))=0)
    (hud : ∀ i, u ((i,true),(i,false))=Complex.I*(variableSourceTangent P R i:ℂ)*u ((i,false),(i,true)) ∧
      u ((i,true),(i,true))=(-Complex.I*(variableSourceTangent P R i:ℂ)/(shrinkingNewtonSourceKappa:ℂ)^2)*u ((i,false),(i,false)))
    (hvf : ∀ i j e f, i < j → v ((i,e),(j,f))=0)
    (hvd : ∀ i, v ((i,false),(i,true))=-Complex.I*(variableSourceTangent Q S i:ℂ)*v ((i,true),(i,false)) ∧
      v ((i,true),(i,true))=(Complex.I*(variableSourceTangent Q S i:ℂ)/(shrinkingNewtonSourceKappa:ℂ)^2)*v ((i,false),(i,false)))
    (hE : variableGaugeOperator P R Q S hP hR hQ hS u=v) : u=0 ∧ v=0 := by
  have hu : u=seamPProjection u+variablePhysicalSourceGraph P R hP hR (seamPProjection u) :=
    variablePhysicalGraph_reconstruct _ _ u huf hud
  have hv : seamQProjection v-variableSpectralSourceGraph Q S hQ hS v=0 :=
    variableSpectralGraph_equation _ _ v hvf hvd
  have hF : variableFullSourceOperator P R Q S hP hR hQ hS (seamPProjection u)=0 :=
    variableFullGraph_kernel _ _ _ _ _ u v hu hv hE
  have hz := variableFullSourceOperator_kernel_zero P R Q S hP hR hQ hS (seamPProjection u)
    (momentProjection_idempotent _ _) hF
  rw [hz,map_zero,add_zero] at hu
  exact ⟨hu,by rw [hu,map_zero] at hE; exact hE.symm⟩

end
end MeyerGeneralProblem.Adaptive
