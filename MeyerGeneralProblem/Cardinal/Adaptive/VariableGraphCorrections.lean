module

public import MeyerGeneralProblem.Cardinal.Adaptive.SeamGraphCorrections
public import MeyerGeneralProblem.Cardinal.Adaptive.VariableTangentWeights

@[expose] public section

/-! Literal complete graph corrections at the retained variable parity scale. -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Physical graph coefficient, supported on its two missing diagonal entries. -/
def variablePhysicalGraphCoefficient (t : ℕ → ℂ) (p : SeamMomentIndex) : ℂ :=
  if p.1.1=p.2.1 ∧ p.1.2=true then
    if p.2.2 then -Complex.I*t p.1.1/(shrinkingNewtonSourceKappa : ℂ)^2 else Complex.I*t p.1.1
  else 0

/-- Spectral graph coefficient, supported on its two missing diagonal entries. -/
def variableSpectralGraphCoefficient (t : ℕ → ℂ) (p : SeamMomentIndex) : ℂ :=
  if p.1.1=p.2.1 ∧ p.2.2=true then
    if p.1.2 then Complex.I*t p.1.1/(shrinkingNewtonSourceKappa : ℂ)^2 else -Complex.I*t p.1.1
  else 0

theorem variablePhysicalGraphCoefficient_bound (t : ℕ → ℂ)
    (ht : ∀ n, ‖t n‖ ≤ 4*shrinkingNewtonSourceKappa^4) (p : SeamMomentIndex) :
    ‖variablePhysicalGraphCoefficient t p‖ ≤ 4*shrinkingNewtonSourceKappa^2 := by
  unfold variablePhysicalGraphCoefficient
  split_ifs <;> simp only [norm_div,norm_mul,norm_neg,Complex.norm_I,one_mul,norm_zero]
  · have h := ht p.1.1
    norm_num [shrinkingNewtonSourceKappa]
    norm_num [shrinkingNewtonSourceKappa] at h ⊢
    linarith
  · exact (ht _).trans (by norm_num [shrinkingNewtonSourceKappa])
  · positivity

theorem variableSpectralGraphCoefficient_bound (t : ℕ → ℂ)
    (ht : ∀ n, ‖t n‖ ≤ 4*shrinkingNewtonSourceKappa^4) (p : SeamMomentIndex) :
    ‖variableSpectralGraphCoefficient t p‖ ≤ 4*shrinkingNewtonSourceKappa^2 := by
  unfold variableSpectralGraphCoefficient
  split_ifs <;> simp only [norm_div,norm_mul,norm_neg,Complex.norm_I,one_mul,norm_zero]
  · have h := ht p.1.1
    norm_num [shrinkingNewtonSourceKappa]
    norm_num [shrinkingNewtonSourceKappa] at h ⊢
    linarith
  · exact (ht _).trans (by norm_num [shrinkingNewtonSourceKappa])
  · positivity

/-- Actual whole physical graph correction, with no supplied operator. -/
def variablePhysicalGraph (t : ℕ → ℂ) (ht : ∀ n, ‖t n‖ ≤ 4*shrinkingNewtonSourceKappa^4) :
    SeamMomentArray →L[ℂ] SeamMomentArray :=
  (momentDiagonal (variablePhysicalGraphCoefficient t) (4*shrinkingNewtonSourceKappa^2) (by positivity)
    (variablePhysicalGraphCoefficient_bound t ht)).comp seamParityExchangeOperator

/-- Actual whole spectral graph correction, with no supplied operator. -/
def variableSpectralGraph (t : ℕ → ℂ) (ht : ∀ n, ‖t n‖ ≤ 4*shrinkingNewtonSourceKappa^4) :
    SeamMomentArray →L[ℂ] SeamMomentArray :=
  (momentDiagonal (variableSpectralGraphCoefficient t) (4*shrinkingNewtonSourceKappa^2) (by positivity)
    (variableSpectralGraphCoefficient_bound t ht)).comp seamParityExchangeOperator

@[simp] theorem variablePhysicalGraph_apply (t : ℕ → ℂ) (ht : ∀ n, ‖t n‖ ≤ 4*shrinkingNewtonSourceKappa^4)
    (u : SeamMomentArray) (p : SeamMomentIndex) :
    variablePhysicalGraph t ht u p=variablePhysicalGraphCoefficient t p*u (seamParityExchange p) := rfl

@[simp] theorem variableSpectralGraph_apply (t : ℕ → ℂ) (ht : ∀ n, ‖t n‖ ≤ 4*shrinkingNewtonSourceKappa^4)
    (u : SeamMomentArray) (p : SeamMomentIndex) :
    variableSpectralGraph t ht u p=variableSpectralGraphCoefficient t p*u (seamParityExchange p) := rfl

theorem variablePhysicalGraph_norm (t : ℕ → ℂ) (ht : ∀ n, ‖t n‖ ≤ 4*shrinkingNewtonSourceKappa^4) :
    ‖variablePhysicalGraph t ht‖ ≤ 4*shrinkingNewtonSourceKappa^2 := by
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  calc
    _ ≤ 4*shrinkingNewtonSourceKappa^2*1 := mul_le_mul
      (momentDiagonal_norm_le _ _ (by positivity) _) seamParityExchangeOperator_norm
      (norm_nonneg _) (by positivity)
    _ = _ := mul_one _

theorem variableSpectralGraph_norm (t : ℕ → ℂ) (ht : ∀ n, ‖t n‖ ≤ 4*shrinkingNewtonSourceKappa^4) :
    ‖variableSpectralGraph t ht‖ ≤ 4*shrinkingNewtonSourceKappa^2 := by
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  calc
    _ ≤ 4*shrinkingNewtonSourceKappa^2*1 := mul_le_mul
      (momentDiagonal_norm_le _ _ (by positivity) _) seamParityExchangeOperator_norm
      (norm_nonneg _) (by positivity)
    _ = _ := mul_one _

/-- Actual physical triangular and diagonal constraints give exactly the full graph. -/
theorem variablePhysicalGraph_reconstruct (t : ℕ → ℂ) (ht : ∀ n, ‖t n‖ ≤ 4*shrinkingNewtonSourceKappa^4)
    (u : SeamMomentArray) (hflag : ∀ i j e f, j < i → u ((i,e),(j,f))=0)
    (hdiag : ∀ i, u ((i,true),(i,false))=Complex.I*t i*u ((i,false),(i,true)) ∧
      u ((i,true),(i,true))=(-Complex.I*t i/(shrinkingNewtonSourceKappa : ℂ)^2)*u ((i,false),(i,false))) :
    u=seamPProjection u+variablePhysicalGraph t ht (seamPProjection u) := by
  ext p
  rcases p with ⟨⟨i,e⟩,j,f⟩
  change u ((i,e),(j,f))=seamPProjection u ((i,e),(j,f))+
    variablePhysicalGraph t ht (seamPProjection u) ((i,e),(j,f))
  simp only [variablePhysicalGraph_apply,seamPProjection,momentProjection_apply,
    variablePhysicalGraphCoefficient,seamParityExchange,seamDIndices,seamCIndices,
    Set.mem_union,Set.mem_setOf_eq]
  rcases lt_trichotomy i j with hij | rfl | hji
  · cases e <;> cases f <;> simp [hij,ne_of_lt hij]
  · cases e <;> cases f <;> simp [hdiag]
  · cases e <;> cases f <;> simp [not_lt_of_gt hji,ne_of_gt hji,hflag _ _ _ _ hji]

/-- Actual spectral triangular and diagonal constraints give the complete graph equation. -/
theorem variableSpectralGraph_equation (t : ℕ → ℂ) (ht : ∀ n, ‖t n‖ ≤ 4*shrinkingNewtonSourceKappa^4)
    (u : SeamMomentArray) (hflag : ∀ i j e f, i < j → u ((i,e),(j,f))=0)
    (hdiag : ∀ i, u ((i,false),(i,true))=-Complex.I*t i*u ((i,true),(i,false)) ∧
      u ((i,true),(i,true))=(Complex.I*t i/(shrinkingNewtonSourceKappa : ℂ)^2)*u ((i,false),(i,false))) :
    seamQProjection u-variableSpectralGraph t ht u=0 := by
  ext p
  rcases p with ⟨⟨i,e⟩,j,f⟩
  change seamQProjection u ((i,e),(j,f))-variableSpectralGraph t ht u ((i,e),(j,f))=0
  simp only [variableSpectralGraph_apply,seamQProjection,momentProjection_apply,
    variableSpectralGraphCoefficient,seamParityExchange,seamGIndices,seamCIndices,
    Set.mem_union,Set.mem_setOf_eq]
  rcases lt_trichotomy i j with hij | rfl | hji
  · cases e <;> cases f <;> simp [hij,ne_of_lt hij,hflag _ _ _ _ hij]
  · cases e <;> cases f <;> simp [hdiag]
  · cases e <;> cases f <;> simp [not_lt_of_gt hji,ne_of_gt hji]

/-- The actual complete gauge and literal source constraints yield a full graph-kernel vector. -/
theorem variableFullGraph_kernel (ta tb : ℕ → ℂ)
    (hta : ∀ n, ‖ta n‖ ≤ 4*shrinkingNewtonSourceKappa^4) (htb : ∀ n, ‖tb n‖ ≤ 4*shrinkingNewtonSourceKappa^4)
    (E : SeamMomentArray →L[ℂ] SeamMomentArray) (u v : SeamMomentArray)
    (hu : u=seamPProjection u+variablePhysicalGraph ta hta (seamPProjection u))
    (hv : seamQProjection v-variableSpectralGraph tb htb v=0) (hE : E u=v) :
    fullGraphOperator seamQProjection E (variablePhysicalGraph ta hta) (variableSpectralGraph tb htb)
      (seamPProjection u)=0 := by
  change seamQProjection (E (seamPProjection u+variablePhysicalGraph ta hta (seamPProjection u)))-
    variableSpectralGraph tb htb (E (seamPProjection u+variablePhysicalGraph ta hta (seamPProjection u)))=0
  rw [←hu,hE]
  exact hv


/-- The actual physical graph at the next-level rapid tangent sequence. -/
def variablePhysicalSourceGraph (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) :
    SeamMomentArray →L[ℂ] SeamMomentArray :=
  variablePhysicalGraph (fun i => (variableSourceTangent P R i : ℂ)) (fun i => by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (variableSourceTangent_pos P R hP hR i)]
    exact variableSourceTangent_le P R hP hR i)

/-- The actual spectral graph uses the independent next-level rapid tangent sequence. -/
def variableSpectralSourceGraph (Q S : ℕ) (hQ : 1 ≤ Q) (hS : 1 ≤ S) :
    SeamMomentArray →L[ℂ] SeamMomentArray :=
  variableSpectralGraph (fun i => (variableSourceTangent Q S i : ℂ)) (fun i => by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (variableSourceTangent_pos Q S hQ hS i)]
    exact variableSourceTangent_le Q S hQ hS i)

/-- The full actual signed graph operator retains both infinite triangular arms. -/
def variableFullSourceOperator (P R Q S : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R)
    (hQ : 1 ≤ Q) (hS : 1 ≤ S) : SeamMomentArray →L[ℂ] SeamMomentArray :=
  fullGraphOperator seamQProjection (variableGaugeOperator P R Q S hP hR hQ hS)
    (variablePhysicalSourceGraph P R hP hR) (variableSpectralSourceGraph Q S hQ hS)

/-- The entire graph-corrected variable operator obeys the source's uniform
near-projection bound, including both graph corrections and their cross term. -/
theorem variableFullSourceOperator_close (P R Q S : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R)
    (hQ : 1 ≤ Q) (hS : 1 ≤ S) :
    ‖variableFullSourceOperator P R Q S hP hR hQ hS-seamQProjection‖ ≤
      32*shrinkingNewtonSourceKappa^2 := by
  let E := variableGaugeOperator P R Q S hP hR hQ hS
  let A := variablePhysicalSourceGraph P R hP hR
  let B := variableSpectralSourceGraph Q S hQ hS
  have hA : ‖A‖ ≤ 4*shrinkingNewtonSourceKappa^2 := variablePhysicalGraph_norm _ _
  have hB : ‖B‖ ≤ 4*shrinkingNewtonSourceKappa^2 := variableSpectralGraph_norm _ _
  have hEI : ‖E-1‖ ≤ 9*shrinkingNewtonSourceKappa^2 := variableGaugeOperator_close P R Q S hP hR hQ hS
  have hE : ‖E‖ ≤ 1+9*shrinkingNewtonSourceKappa^2 := by
    have h := norm_le_norm_sub_add E 1
    rw [norm_one] at h
    linarith
  have hI : ‖1+A‖ ≤ 1+4*shrinkingNewtonSourceKappa^2 :=
    (norm_add_le _ _).trans (by rw [norm_one]; linarith)
  have hQn : ‖seamQProjection‖ ≤ 1 := momentProjection_norm_le_one _
  have he : fullGraphOperator seamQProjection E A B-seamQProjection =
      seamQProjection*E*A-B*E*(1+A)+seamQProjection*(E-1) := by
    unfold fullGraphOperator
    simp only [sub_mul, mul_sub, mul_add, add_mul, mul_one, one_mul, mul_assoc]
    abel
  change ‖fullGraphOperator seamQProjection E A B-seamQProjection‖ ≤ _
  rw [he]
  calc
    _ ≤ (‖seamQProjection‖*‖E‖)*‖A‖+(‖B‖*‖E‖)*‖1+A‖+‖seamQProjection‖*‖E-1‖ := by
      apply (norm_add_le _ _).trans
      apply add_le_add _ (norm_mul_le _ _)
      apply (norm_sub_le _ _).trans
      exact add_le_add
        ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)))
        ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)))
    _ ≤ (1*(1+9*shrinkingNewtonSourceKappa^2))*(4*shrinkingNewtonSourceKappa^2)+
        ((4*shrinkingNewtonSourceKappa^2)*(1+9*shrinkingNewtonSourceKappa^2))*(1+4*shrinkingNewtonSourceKappa^2)+
        1*(9*shrinkingNewtonSourceKappa^2) := by gcongr
    _ ≤ _ := by norm_num [shrinkingNewtonSourceKappa]

end
end MeyerGeneralProblem.Adaptive
