module

public import MeyerGeneralProblem.Cardinal.Adaptive.SeamCoordinateOperator
public import MeyerGeneralProblem.Cardinal.Adaptive.FullGraphBounds

@[expose] public section

/-! # Literal complete diagonal graph corrections -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Simultaneous exchange of both parity bits, retaining both Newton levels. -/
def seamParityExchange (p : SeamMomentIndex) : SeamMomentIndex :=
  ((p.1.1,!p.1.2),(p.2.1,!p.2.2))

theorem seamParityExchange_involutive : Function.Involutive seamParityExchange := by
  intro p
  rcases p with ⟨⟨i,e⟩,j,f⟩
  cases e <;> cases f <;> rfl

/-- Bounded complete parity exchange on the actual moment Hilbert space. -/
def seamParityExchangeOperator : SeamMomentArray →L[ℂ] SeamMomentArray :=
  momentPullback seamParityExchange seamParityExchange_involutive.injective

theorem seamParityExchangeOperator_norm : ‖seamParityExchangeOperator‖ ≤ 1 :=
  momentPullback_norm_le_one _ _

/-- Physical graph coefficient, supported on its two missing diagonal entries. -/
def seamPhysicalGraphCoefficient (t : ℕ → ℂ) (p : SeamMomentIndex) : ℂ :=
  if p.1.1=p.2.1 ∧ p.1.2=true then
    if p.2.2 then -Complex.I*t p.1.1/(1/4096 : ℂ) else Complex.I*t p.1.1
  else 0

/-- Spectral graph coefficient, supported on its two missing diagonal entries. -/
def seamSpectralGraphCoefficient (t : ℕ → ℂ) (p : SeamMomentIndex) : ℂ :=
  if p.1.1=p.2.1 ∧ p.2.2=true then
    if p.1.2 then Complex.I*t p.1.1/(1/4096 : ℂ) else -Complex.I*t p.1.1
  else 0

theorem seamPhysicalGraphCoefficient_bound (t : ℕ → ℂ)
    (ht : ∀ n, ‖t n‖ ≤ (1/4096 : ℝ)^3) (p : SeamMomentIndex) :
    ‖seamPhysicalGraphCoefficient t p‖ ≤ (1/4096 : ℝ)^2 := by
  unfold seamPhysicalGraphCoefficient
  split_ifs <;> simp only [norm_div,norm_mul,norm_neg,Complex.norm_I,one_mul,norm_zero]
  · have h := ht p.1.1
    norm_num only [norm_div,norm_one,Complex.norm_ofNat]
    norm_num at h ⊢
    linarith
  · exact (ht _).trans (by norm_num)
  · positivity

theorem seamSpectralGraphCoefficient_bound (t : ℕ → ℂ)
    (ht : ∀ n, ‖t n‖ ≤ (1/4096 : ℝ)^3) (p : SeamMomentIndex) :
    ‖seamSpectralGraphCoefficient t p‖ ≤ (1/4096 : ℝ)^2 := by
  unfold seamSpectralGraphCoefficient
  split_ifs <;> simp only [norm_div,norm_mul,norm_neg,Complex.norm_I,one_mul,norm_zero]
  · have h := ht p.1.1
    norm_num only [norm_div,norm_one,Complex.norm_ofNat]
    norm_num at h ⊢
    linarith
  · exact (ht _).trans (by norm_num)
  · positivity

/-- Actual whole physical graph correction, with no supplied operator. -/
def seamPhysicalGraph (t : ℕ → ℂ) (ht : ∀ n, ‖t n‖ ≤ (1/4096 : ℝ)^3) :
    SeamMomentArray →L[ℂ] SeamMomentArray :=
  (momentDiagonal (seamPhysicalGraphCoefficient t) ((1/4096)^2) (by positivity)
    (seamPhysicalGraphCoefficient_bound t ht)).comp seamParityExchangeOperator

/-- Actual whole spectral graph correction, with no supplied operator. -/
def seamSpectralGraph (t : ℕ → ℂ) (ht : ∀ n, ‖t n‖ ≤ (1/4096 : ℝ)^3) :
    SeamMomentArray →L[ℂ] SeamMomentArray :=
  (momentDiagonal (seamSpectralGraphCoefficient t) ((1/4096)^2) (by positivity)
    (seamSpectralGraphCoefficient_bound t ht)).comp seamParityExchangeOperator

@[simp] theorem seamPhysicalGraph_apply (t : ℕ → ℂ) (ht : ∀ n, ‖t n‖ ≤ (1/4096 : ℝ)^3)
    (u : SeamMomentArray) (p : SeamMomentIndex) :
    seamPhysicalGraph t ht u p=seamPhysicalGraphCoefficient t p*u (seamParityExchange p) := rfl

@[simp] theorem seamSpectralGraph_apply (t : ℕ → ℂ) (ht : ∀ n, ‖t n‖ ≤ (1/4096 : ℝ)^3)
    (u : SeamMomentArray) (p : SeamMomentIndex) :
    seamSpectralGraph t ht u p=seamSpectralGraphCoefficient t p*u (seamParityExchange p) := rfl

theorem seamPhysicalGraph_norm (t : ℕ → ℂ) (ht : ∀ n, ‖t n‖ ≤ (1/4096 : ℝ)^3) :
    ‖seamPhysicalGraph t ht‖ ≤ (1/4096 : ℝ)^2 := by
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  calc
    _ ≤ (1/4096 : ℝ)^2*1 := mul_le_mul
      (momentDiagonal_norm_le _ _ (by positivity) _) seamParityExchangeOperator_norm
      (norm_nonneg _) (by positivity)
    _ = _ := mul_one _

theorem seamSpectralGraph_norm (t : ℕ → ℂ) (ht : ∀ n, ‖t n‖ ≤ (1/4096 : ℝ)^3) :
    ‖seamSpectralGraph t ht‖ ≤ (1/4096 : ℝ)^2 := by
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  calc
    _ ≤ (1/4096 : ℝ)^2*1 := mul_le_mul
      (momentDiagonal_norm_le _ _ (by positivity) _) seamParityExchangeOperator_norm
      (norm_nonneg _) (by positivity)
    _ = _ := mul_one _

/-- Actual physical triangular and diagonal constraints give exactly the full graph. -/
theorem seamPhysicalGraph_reconstruct (t : ℕ → ℂ) (ht : ∀ n, ‖t n‖ ≤ (1/4096 : ℝ)^3)
    (u : SeamMomentArray) (hflag : ∀ i j e f, j < i → u ((i,e),(j,f))=0)
    (hdiag : ∀ i, u ((i,true),(i,false))=Complex.I*t i*u ((i,false),(i,true)) ∧
      u ((i,true),(i,true))=(-Complex.I*t i/(1/4096 : ℂ))*u ((i,false),(i,false))) :
    u=seamPProjection u+seamPhysicalGraph t ht (seamPProjection u) := by
  ext p
  rcases p with ⟨⟨i,e⟩,j,f⟩
  change u ((i,e),(j,f))=seamPProjection u ((i,e),(j,f))+
    seamPhysicalGraph t ht (seamPProjection u) ((i,e),(j,f))
  simp only [seamPhysicalGraph_apply,seamPProjection,momentProjection_apply,
    seamPhysicalGraphCoefficient,seamParityExchange,seamDIndices,seamCIndices,
    Set.mem_union,Set.mem_setOf_eq]
  rcases lt_trichotomy i j with hij | rfl | hji
  · cases e <;> cases f <;> simp [hij,ne_of_lt hij]
  · cases e <;> cases f <;> simp [hdiag]
  · cases e <;> cases f <;> simp [not_lt_of_gt hji,ne_of_gt hji,hflag _ _ _ _ hji]

/-- Actual spectral triangular and diagonal constraints give the complete graph equation. -/
theorem seamSpectralGraph_equation (t : ℕ → ℂ) (ht : ∀ n, ‖t n‖ ≤ (1/4096 : ℝ)^3)
    (u : SeamMomentArray) (hflag : ∀ i j e f, i < j → u ((i,e),(j,f))=0)
    (hdiag : ∀ i, u ((i,false),(i,true))=-Complex.I*t i*u ((i,true),(i,false)) ∧
      u ((i,true),(i,true))=(Complex.I*t i/(1/4096 : ℂ))*u ((i,false),(i,false))) :
    seamQProjection u-seamSpectralGraph t ht u=0 := by
  ext p
  rcases p with ⟨⟨i,e⟩,j,f⟩
  change seamQProjection u ((i,e),(j,f))-seamSpectralGraph t ht u ((i,e),(j,f))=0
  simp only [seamSpectralGraph_apply,seamQProjection,momentProjection_apply,
    seamSpectralGraphCoefficient,seamParityExchange,seamGIndices,seamCIndices,
    Set.mem_union,Set.mem_setOf_eq]
  rcases lt_trichotomy i j with hij | rfl | hji
  · cases e <;> cases f <;> simp [hij,ne_of_lt hij,hflag _ _ _ _ hij]
  · cases e <;> cases f <;> simp [hdiag]
  · cases e <;> cases f <;> simp [not_lt_of_gt hji,ne_of_gt hji]

/-- The actual complete gauge and literal source constraints yield a full graph-kernel vector. -/
theorem seamFullGraph_kernel (ta tb : ℕ → ℂ)
    (hta : ∀ n, ‖ta n‖ ≤ (1/4096 : ℝ)^3) (htb : ∀ n, ‖tb n‖ ≤ (1/4096 : ℝ)^3)
    (E : SeamMomentArray →L[ℂ] SeamMomentArray) (u v : SeamMomentArray)
    (hu : u=seamPProjection u+seamPhysicalGraph ta hta (seamPProjection u))
    (hv : seamQProjection v-seamSpectralGraph tb htb v=0) (hE : E u=v) :
    fullGraphOperator seamQProjection E (seamPhysicalGraph ta hta) (seamSpectralGraph tb htb)
      (seamPProjection u)=0 := by
  change seamQProjection (E (seamPProjection u+seamPhysicalGraph ta hta (seamPProjection u)))-
    seamSpectralGraph tb htb (E (seamPProjection u+seamPhysicalGraph ta hta (seamPProjection u)))=0
  rw [←hu,hE]
  exact hv

/-- Complete actual corrected gauge operator for the two bounded phase sequences. -/
def seamFullOperator (a b ta tb : ℕ → ℂ)
    (ha : ∀ i, ‖a i‖ ≤ (1/4096 : ℝ)^2) (hb : ∀ i, ‖b i‖ ≤ (1/4096 : ℝ)^2)
    (hta : ∀ i, ‖ta i‖ ≤ (1/4096 : ℝ)^3) (htb : ∀ i, ‖tb i‖ ≤ (1/4096 : ℝ)^3) :
    SeamMomentArray →L[ℂ] SeamMomentArray :=
  fullGraphOperator seamQProjection
    (seamGaugeOperator
      (seamSineRow (1/64) (1/4096) a ((1/4096)^2) (by positivity) ha)
      (seamSineColumn (1/64) (1/4096) b ((1/4096)^2) (by positivity) hb))
    (seamPhysicalGraph ta hta) (seamSpectralGraph tb htb)

/-- The complete actual graph-corrected operator is within 10R of the reference projection. -/
theorem seamFullOperator_close (a b ta tb : ℕ → ℂ)
    (ha : ∀ i, ‖a i‖ ≤ (1/4096 : ℝ)^2) (hb : ∀ i, ‖b i‖ ≤ (1/4096 : ℝ)^2)
    (hta : ∀ i, ‖ta i‖ ≤ (1/4096 : ℝ)^3) (htb : ∀ i, ‖tb i‖ ≤ (1/4096 : ℝ)^3) :
    ‖seamFullOperator a b ta tb ha hb hta htb-seamQProjection‖ ≤ 10*(1/4096 : ℝ) := by
  have he := seamGaugeOperator_actual_close a b ha hb
  apply fullGraphOperator_seam_close _ _ _ _ (momentProjection_norm_le_one _) _ he
    (seamPhysicalGraph_norm ta hta) (seamSpectralGraph_norm tb htb)
  have hn := norm_le_norm_sub_add
    (seamGaugeOperator
      (seamSineRow (1/64) (1/4096) a ((1/4096)^2) (by positivity) ha)
      (seamSineColumn (1/64) (1/4096) b ((1/4096)^2) (by positivity) hb)) 1
  rw [norm_one] at hn
  linarith

end
end MeyerGeneralProblem.Adaptive
