module

public import MeyerGeneralProblem.Cardinal.Adaptive.SeamNewtonOperators
public import MeyerGeneralProblem.Cardinal.Adaptive.MomentHilbertOrthogonality

@[expose] public section

/-! # Complete bounded sine multiplication on the actual seam moment array -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section

/-- Physical parity slice, with all levels and spectral parities retained. -/
def seamRowParity (e : Bool) : Set SeamMomentIndex := {p | p.1.2=e}
/-- Flip only the physical parity bit. -/
def seamRowFlipIndex (p : SeamMomentIndex) : SeamMomentIndex := ((p.1.1,!p.1.2),p.2)

theorem seamRowFlipIndex_injective : Function.Injective seamRowFlipIndex := by
  rintro ⟨⟨i,e⟩,j,f⟩ ⟨⟨k,g⟩,l,h⟩ heq
  simpa [seamRowFlipIndex] using heq

/-- Literal physical parity flip on the whole moment Hilbert space. -/
def seamRowFlip : SeamMomentArray →L[ℂ] SeamMomentArray := momentPullback seamRowFlipIndex seamRowFlipIndex_injective

@[simp] theorem seamRowFlip_apply (u : SeamMomentArray) (p : SeamMomentIndex) :
    seamRowFlip u p=u ((p.1.1,!p.1.2),p.2) := rfl

theorem seamRowFlip_norm_le_one : ‖seamRowFlip‖ ≤ 1 := momentPullback_norm_le_one _ _

/-- The complete upper parity block κ(2−J), using the genuine odd input. -/
def seamSineUpper (κ R : ℂ) (a : ℕ → ℂ) (K : ℝ) (hK : 0 ≤ K) (ha : ∀ i, ‖a i‖ ≤ K) :
    SeamMomentArray →L[ℂ] SeamMomentArray :=
  κ •(((2 : ℂ) •ContinuousLinearMap.id ℂ SeamMomentArray-seamNewtonRow R a K hK ha).comp
    (seamRowFlip.comp (momentProjection (seamRowParity true))))
/-- The complete lower parity block J/κ, using the genuine even input. -/
def seamSineLower (κ R : ℂ) (a : ℕ → ℂ) (K : ℝ) (hK : 0 ≤ K) (ha : ∀ i, ‖a i‖ ≤ K) :
    SeamMomentArray →L[ℂ] SeamMomentArray :=
  κ⁻¹ •((seamNewtonRow R a K hK ha).comp
    (seamRowFlip.comp (momentProjection (seamRowParity false))))
/-- The full physical sine operator, retaining all levels and both parity blocks. -/
def seamSineRow (κ R : ℂ) (a : ℕ → ℂ) (K : ℝ) (hK : 0 ≤ K) (ha : ∀ i, ‖a i‖ ≤ K) :
    SeamMomentArray →L[ℂ] SeamMomentArray := seamSineUpper κ R a K hK ha+seamSineLower κ R a K hK ha

@[simp] theorem seamSineUpper_apply (κ R : ℂ) (a : ℕ → ℂ) (K : ℝ) (hK : 0 ≤ K)
    (ha : ∀ i, ‖a i‖ ≤ K) (u : SeamMomentArray) (i j : ℕ) (e f : Bool) :
    seamSineUpper κ R a K hK ha u ((i,e),(j,f))=
      if e then 0 else κ*(2*u ((i,true),(j,f))-(R*u ((i+1,true),(j,f))+a i*u ((i,true),(j,f)))) := by
  change κ*(2*(seamRowFlip (momentProjection (seamRowParity true) u)) ((i,e),(j,f))-
    seamNewtonRow R a K hK ha (seamRowFlip (momentProjection (seamRowParity true) u)) ((i,e),(j,f)))=_
  cases e <;> simp [seamNewtonRow_apply,seamRowFlip_apply,momentProjection_apply,seamRowParity]

@[simp] theorem seamSineLower_apply (κ R : ℂ) (a : ℕ → ℂ) (K : ℝ) (hK : 0 ≤ K)
    (ha : ∀ i, ‖a i‖ ≤ K) (u : SeamMomentArray) (i j : ℕ) (e f : Bool) :
    seamSineLower κ R a K hK ha u ((i,e),(j,f))=
      if e then κ⁻¹*(R*u ((i+1,false),(j,f))+a i*u ((i,false),(j,f))) else 0 := by
  change κ⁻¹*seamNewtonRow R a K hK ha (seamRowFlip (momentProjection (seamRowParity false) u)) ((i,e),(j,f))=_
  cases e <;> simp [seamNewtonRow_apply,seamRowFlip_apply,momentProjection_apply,seamRowParity]

@[simp] theorem seamSineRow_apply (κ R : ℂ) (a : ℕ → ℂ) (K : ℝ) (hK : 0 ≤ K)
    (ha : ∀ i, ‖a i‖ ≤ K) (u : SeamMomentArray) (i j : ℕ) (e f : Bool) :
    seamSineRow κ R a K hK ha u ((i,e),(j,f))=
      if e then κ⁻¹*(R*u ((i+1,false),(j,f))+a i*u ((i,false),(j,f)))
      else κ*(2*u ((i,true),(j,f))-(R*u ((i+1,true),(j,f))+a i*u ((i,true),(j,f)))) := by
  change seamSineUpper κ R a K hK ha u ((i,e),(j,f))+seamSineLower κ R a K hK ha u ((i,e),(j,f))=_
  cases e <;> simp only [seamSineUpper_apply,seamSineLower_apply,Bool.false_eq_true,ite_false,ite_true,add_zero,zero_add]

private theorem seamRowFlip_norm_apply (u : SeamMomentArray) : ‖seamRowFlip u‖ ≤ ‖u‖ :=
  (seamRowFlip.le_opNorm u).trans (by nlinarith [seamRowFlip_norm_le_one,norm_nonneg u])

/-- A whole operator bound derived from the true Hilbert parity partition;
 the two disjoint blocks are not charged twice. -/
theorem seamSineRow_norm_le (κ R : ℂ) (a : ℕ → ℂ) (K : ℝ) (hK : 0 ≤ K)
    (ha : ∀ i, ‖a i‖ ≤ K) (M : ℝ) (hM : 0 ≤ M)
    (hupper : ‖κ‖*(2+‖R‖+K) ≤ M) (hlower : ‖κ⁻¹‖*(‖R‖+K) ≤ M) :
    ‖seamSineRow κ R a K hK ha‖ ≤ M := by
  have hJ := seamNewtonRow_norm_le R a K hK ha
  have hUp (u : SeamMomentArray) : ‖((2 : ℂ) •ContinuousLinearMap.id ℂ SeamMomentArray-seamNewtonRow R a K hK ha) u‖ ≤
      (2+‖R‖+K)*‖u‖ := by
    change ‖(2 : ℂ) •u-seamNewtonRow R a K hK ha u‖ ≤ _
    calc
      _ ≤ ‖(2 : ℂ) •u‖+‖seamNewtonRow R a K hK ha u‖ := norm_sub_le _ _
      _ ≤ (2+‖R‖+K)*‖u‖ := by
        rw [norm_smul]
        norm_num only [Complex.norm_ofNat]
        have hj := (seamNewtonRow R a K hK ha).le_opNorm u
        have hh := mul_le_mul_of_nonneg_right hJ (norm_nonneg u)
        nlinarith
  apply moment_partition_operator_bound (seamRowParity true) _ _ M hM
  · intro u
    change ‖κ •(((2 : ℂ) •ContinuousLinearMap.id ℂ SeamMomentArray-seamNewtonRow R a K hK ha)
      (seamRowFlip (momentProjection (seamRowParity true) u)))‖ ≤ _
    rw [norm_smul]
    calc
      _ ≤ ‖κ‖*((2+‖R‖+K)*‖seamRowFlip (momentProjection (seamRowParity true) u)‖) :=
        mul_le_mul_of_nonneg_left (hUp _) (norm_nonneg _)
      _ ≤ ‖κ‖*((2+‖R‖+K)*‖momentProjection (seamRowParity true) u‖) := by
        gcongr
        exact seamRowFlip_norm_apply _
      _ ≤ _ := by nlinarith [norm_nonneg (momentProjection (seamRowParity true) u)]
  · intro u
    have hs : (seamRowParity true)ᶜ=seamRowParity false := by
      ext p
      simp [seamRowParity]
    rw [hs]
    change ‖κ⁻¹ •(seamNewtonRow R a K hK ha (seamRowFlip (momentProjection (seamRowParity false) u)))‖ ≤ _
    rw [norm_smul]
    calc
      _ ≤ ‖κ⁻¹‖*(‖seamNewtonRow R a K hK ha‖*‖seamRowFlip (momentProjection (seamRowParity false) u)‖) :=
        mul_le_mul_of_nonneg_left ((seamNewtonRow R a K hK ha).le_opNorm _) (norm_nonneg _)
      _ ≤ ‖κ⁻¹‖*((‖R‖+K)*‖momentProjection (seamRowParity false) u‖) := by
        gcongr
        exact seamRowFlip_norm_apply _
      _ ≤ _ := by nlinarith [norm_nonneg (momentProjection (seamRowParity false) u)]
  · rintro u ⟨⟨i,e⟩,j,f⟩
    cases e <;> simp only [seamSineUpper_apply,seamSineLower_apply,Bool.false_eq_true,ite_false,ite_true,or_true,true_or]

/-- The accepted constant-R operator is bounded by 3κ in the full Hilbert norm. -/
theorem seamSineRow_constant_bound (a : ℕ → ℂ) (ha : ∀ i, ‖a i‖ ≤ (1/4096 : ℝ)^2) :
    ‖seamSineRow (1/64) (1/4096) a ((1/4096)^2) (by positivity) ha‖ ≤ 3*(1/64 : ℝ) := by
  apply seamSineRow_norm_le
  · norm_num
  · norm_num
  · norm_num

/-- The exact full sine square is J(2−J) on both parity sectors. -/
theorem seamSineRow_square (κ R : ℂ) (hκ : κ ≠ 0) (a : ℕ → ℂ)
    (K : ℝ) (hK : 0 ≤ K) (ha : ∀ i, ‖a i‖ ≤ K) :
    (seamSineRow κ R a K hK ha).comp (seamSineRow κ R a K hK ha)=
      (seamNewtonRow R a K hK ha).comp
        ((2 : ℂ) •ContinuousLinearMap.id ℂ SeamMomentArray-seamNewtonRow R a K hK ha) := by
  ext u p
  rcases p with ⟨⟨i,e⟩,j,f⟩
  change seamSineRow κ R a K hK ha (seamSineRow κ R a K hK ha u) ((i,e),(j,f))=
    R*(2*u ((i+1,e),(j,f))-(R*u ((i+2,e),(j,f))+a (i+1)*u ((i+1,e),(j,f))))+
      a i*(2*u ((i,e),(j,f))-(R*u ((i+1,e),(j,f))+a i*u ((i,e),(j,f))))
  cases e <;> simp only [seamSineRow_apply,Bool.false_eq_true,ite_false,ite_true] <;>
    field_simp [hκ] <;> ring

/-- Exchange the two complete Newton axes, including parity bits. -/
def seamTransposeIndex (p : SeamMomentIndex) : SeamMomentIndex := (p.2,p.1)

theorem seamTransposeIndex_injective : Function.Injective seamTransposeIndex := by
  rintro ⟨a,b⟩ ⟨c,d⟩ h
  simpa [seamTransposeIndex,Prod.mk.injEq,and_comm] using h

/-- The literal coordinate transposition on the full array. -/
def seamTranspose : SeamMomentArray →L[ℂ] SeamMomentArray := momentPullback seamTransposeIndex seamTransposeIndex_injective

@[simp] theorem seamTranspose_apply (u : SeamMomentArray) (p : SeamMomentIndex) :
    seamTranspose u p=u (p.2,p.1) := rfl

@[simp] theorem seamTranspose_involutive (u : SeamMomentArray) : seamTranspose (seamTranspose u)=u := by
  ext p
  rfl

theorem seamTranspose_norm_le_one : ‖seamTranspose‖ ≤ 1 := momentPullback_norm_le_one _ _

theorem seamTranspose_norm_apply (u : SeamMomentArray) : ‖seamTranspose u‖ ≤ ‖u‖ :=
  (seamTranspose.le_opNorm u).trans (by nlinarith [seamTranspose_norm_le_one,norm_nonneg u])

/-- The entire spectral sine operator obtained by exact axis exchange. -/
def seamSineColumn (κ R : ℂ) (b : ℕ → ℂ) (K : ℝ) (hK : 0 ≤ K) (hb : ∀ i, ‖b i‖ ≤ K) :
    SeamMomentArray →L[ℂ] SeamMomentArray :=
  seamTranspose.comp ((seamSineRow κ R b K hK hb).comp seamTranspose)

@[simp] theorem seamSineColumn_apply (κ R : ℂ) (b : ℕ → ℂ) (K : ℝ) (hK : 0 ≤ K)
    (hb : ∀ i, ‖b i‖ ≤ K) (u : SeamMomentArray) (i j : ℕ) (e f : Bool) :
    seamSineColumn κ R b K hK hb u ((i,e),(j,f))=
      if f then κ⁻¹*(R*u ((i,e),(j+1,false))+b j*u ((i,e),(j,false)))
      else κ*(2*u ((i,e),(j,true))-(R*u ((i,e),(j+1,true))+b j*u ((i,e),(j,true)))) := by
  change seamSineRow κ R b K hK hb (seamTranspose u) ((j,f),(i,e))=_
  rw [seamSineRow_apply]
  rfl

theorem seamSineColumn_norm_le_row (κ R : ℂ) (b : ℕ → ℂ) (K : ℝ) (hK : 0 ≤ K)
    (hb : ∀ i, ‖b i‖ ≤ K) :
    ‖seamSineColumn κ R b K hK hb‖ ≤ ‖seamSineRow κ R b K hK hb‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro u
  change ‖seamTranspose (seamSineRow κ R b K hK hb (seamTranspose u))‖ ≤ _
  calc
    _ ≤ ‖seamSineRow κ R b K hK hb (seamTranspose u)‖ := seamTranspose_norm_apply _
    _ ≤ ‖seamSineRow κ R b K hK hb‖*‖seamTranspose u‖ := (seamSineRow κ R b K hK hb).le_opNorm _
    _ ≤ _ := mul_le_mul_of_nonneg_left (seamTranspose_norm_apply _) (norm_nonneg _)

/-- The spectral sine has the same checked constant-R bound on the whole space. -/
theorem seamSineColumn_constant_bound (b : ℕ → ℂ) (hb : ∀ i, ‖b i‖ ≤ (1/4096 : ℝ)^2) :
    ‖seamSineColumn (1/64) (1/4096) b ((1/4096)^2) (by positivity) hb‖ ≤ 3*(1/64 : ℝ) :=
  (seamSineColumn_norm_le_row _ _ _ _ _ _).trans (seamSineRow_constant_bound b hb)

end
end MeyerGeneralProblem.Adaptive
