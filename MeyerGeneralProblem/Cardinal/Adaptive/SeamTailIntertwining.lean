module

public import MeyerGeneralProblem.Cardinal.Adaptive.SeamCoordinateIntertwining
public import MeyerGeneralProblem.Cardinal.Adaptive.SeamGraphCorrections

@[expose] public section

/-! # Complete shifted-quadrant covariance of the actual seam operators -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section

/-- Simultaneous shift of both Newton levels, retaining every parity. -/
def seamTailIndex (h : ℕ) (p : SeamMomentIndex) : SeamMomentIndex :=
  ((p.1.1+h,p.1.2),(p.2.1+h,p.2.2))

theorem seamTailIndex_injective (h : ℕ) : Function.Injective (seamTailIndex h) := by
  rintro ⟨⟨i,e⟩,j,f⟩ ⟨⟨i',e'⟩,j',f'⟩ hh
  simp only [seamTailIndex,Prod.mk.injEq] at hh
  obtain ⟨⟨hi,rfl⟩,hj,rfl⟩ := hh
  congr <;> omega

/-- Actual extraction of the entire shifted quadrant in its original normalization. -/
def seamTailShift (h : ℕ) : SeamMomentArray →L[ℂ] SeamMomentArray :=
  momentPullback (seamTailIndex h) (seamTailIndex_injective h)

@[simp] theorem seamTailShift_apply (h : ℕ) (u : SeamMomentArray) (p : SeamMomentIndex) :
    seamTailShift h u p=u (seamTailIndex h p) := rfl

theorem seamTailShift_norm (h : ℕ) : ‖seamTailShift h‖ ≤ 1 := momentPullback_norm_le_one _ _

theorem seamTailShift_P (h : ℕ) (u : SeamMomentArray) :
    seamTailShift h (seamPProjection u)=seamPProjection (seamTailShift h u) := by
  ext p
  simp only [seamTailShift_apply,seamPProjection,momentProjection_apply,
    seamDIndices,seamCIndices,Set.mem_union,Set.mem_setOf_eq,seamTailIndex]
  simp

theorem seamTailShift_Q (h : ℕ) : seamTailShift h*seamQProjection=seamQProjection*seamTailShift h := by
  ext u p
  change seamTailShift h (seamQProjection u) p=seamQProjection (seamTailShift h u) p
  simp only [seamTailShift_apply,seamQProjection,momentProjection_apply,
    seamGIndices,seamCIndices,Set.mem_union,Set.mem_setOf_eq,seamTailIndex]
  simp

theorem seamTailShift_sine_row (h : ℕ) (κ R : ℂ) (a : ℕ → ℂ) (K : ℝ)
    (hK : 0 ≤ K) (ha : ∀ i, ‖a i‖ ≤ K) :
    (seamTailShift h).comp (seamSineRow κ R a K hK ha)=
      (seamSineRow κ R (fun i => a (i+h)) K hK (fun i => ha (i+h))).comp (seamTailShift h) := by
  ext u p
  rcases p with ⟨⟨i,e⟩,j,f⟩
  change seamSineRow κ R a K hK ha u ((i+h,e),(j+h,f))=
    seamSineRow κ R (fun i => a (i+h)) K hK (fun i => ha (i+h)) (seamTailShift h u) ((i,e),(j,f))
  simp only [seamSineRow_apply,seamTailShift_apply,seamTailIndex]
  have hi : i+h+1=i+1+h := by omega
  simp only [hi]

theorem seamTailShift_sine_column (h : ℕ) (κ R : ℂ) (a : ℕ → ℂ) (K : ℝ)
    (hK : 0 ≤ K) (ha : ∀ i, ‖a i‖ ≤ K) :
    (seamTailShift h).comp (seamSineColumn κ R a K hK ha)=
      (seamSineColumn κ R (fun i => a (i+h)) K hK (fun i => ha (i+h))).comp (seamTailShift h) := by
  ext u p
  rcases p with ⟨⟨i,e⟩,j,f⟩
  change seamSineColumn κ R a K hK ha u ((i+h,e),(j+h,f))=
    seamSineColumn κ R (fun i => a (i+h)) K hK (fun i => ha (i+h)) (seamTailShift h u) ((i,e),(j,f))
  simp only [seamSineColumn_apply,seamTailShift_apply,seamTailIndex]
  have hj : j+h+1=j+1+h := by omega
  simp only [hj]

/-- Full coordinate covariance includes the complete arcsine power series. -/
theorem seamTailShift_coordinate_row (h : ℕ) (a : ℕ → ℂ)
    (ha : ∀ i, ‖a i‖ ≤ (1/4096 : ℝ)^2) :
    (seamTailShift h).comp (seamCoordinateOperator (seamSineRow (1/64) (1/4096) a ((1/4096)^2) (by positivity) ha))=
      (seamCoordinateOperator (seamSineRow (1/64) (1/4096) (fun i => a (i+h)) ((1/4096)^2) (by positivity)
        (fun i => ha (i+h)))).comp (seamTailShift h) :=
  seamCoordinateOperator_intertwine _ _ _
    ((seamSineRow_square_norm a ha).trans_lt (by norm_num))
    ((seamSineRow_square_norm _ _).trans_lt (by norm_num)) (seamTailShift_sine_row _ _ _ _ _ _ _)

/-- The full spectral coordinate obeys the same exact shifted-quadrant identity. -/
theorem seamTailShift_coordinate_column (h : ℕ) (a : ℕ → ℂ)
    (ha : ∀ i, ‖a i‖ ≤ (1/4096 : ℝ)^2) :
    (seamTailShift h).comp (seamCoordinateOperator (seamSineColumn (1/64) (1/4096) a ((1/4096)^2) (by positivity) ha))=
      (seamCoordinateOperator (seamSineColumn (1/64) (1/4096) (fun i => a (i+h)) ((1/4096)^2) (by positivity)
        (fun i => ha (i+h)))).comp (seamTailShift h) :=
  seamCoordinateOperator_intertwine _ _ _
    ((seamSineColumn_square_norm a ha).trans_lt (by norm_num))
    ((seamSineColumn_square_norm _ _).trans_lt (by norm_num)) (seamTailShift_sine_column _ _ _ _ _ _ _)

/-- The full quadratic generator intertwines with the actual shifted node sequences. -/
theorem seamTailShift_generator (h : ℕ) (a b : ℕ → ℂ)
    (ha : ∀ i, ‖a i‖ ≤ (1/4096 : ℝ)^2) (hb : ∀ i, ‖b i‖ ≤ (1/4096 : ℝ)^2) :
    (seamTailShift h).comp (seamGaugeGenerator
      (seamSineRow (1/64) (1/4096) a ((1/4096)^2) (by positivity) ha)
      (seamSineColumn (1/64) (1/4096) b ((1/4096)^2) (by positivity) hb))=
    (seamGaugeGenerator
      (seamSineRow (1/64) (1/4096) (fun i => a (i+h)) ((1/4096)^2) (by positivity) (fun i => ha (i+h)))
      (seamSineColumn (1/64) (1/4096) (fun i => b (i+h)) ((1/4096)^2) (by positivity) (fun i => hb (i+h)))).comp (seamTailShift h) := by
  have hx := seamTailShift_coordinate_row h a ha
  have hy := seamTailShift_coordinate_column h b hb
  change seamTailShift h*_= _*seamTailShift h
  change seamTailShift h*_= _*seamTailShift h at hx hy
  simp only [seamGaugeGenerator,mul_smul_comm,smul_mul_assoc]
  apply congrArg (fun Z : SeamMomentArray →L[ℂ] SeamMomentArray => (-2*(Real.pi : ℂ)*Complex.I) •Z)
  rw [←mul_assoc,hx,mul_assoc,hy,←mul_assoc]

/-- The complete operator exponential respects the exact shifted-quadrant covariance. -/
theorem seamTailShift_gauge (h : ℕ) (a b : ℕ → ℂ)
    (ha : ∀ i, ‖a i‖ ≤ (1/4096 : ℝ)^2) (hb : ∀ i, ‖b i‖ ≤ (1/4096 : ℝ)^2) :
    (seamTailShift h).comp (seamGaugeOperator
      (seamSineRow (1/64) (1/4096) a ((1/4096)^2) (by positivity) ha)
      (seamSineColumn (1/64) (1/4096) b ((1/4096)^2) (by positivity) hb))=
    (seamGaugeOperator
      (seamSineRow (1/64) (1/4096) (fun i => a (i+h)) ((1/4096)^2) (by positivity) (fun i => ha (i+h)))
      (seamSineColumn (1/64) (1/4096) (fun i => b (i+h)) ((1/4096)^2) (by positivity) (fun i => hb (i+h)))).comp (seamTailShift h) := by
  simp only [seamGaugeOperator,fullExponential_eq_series]
  apply boundedOperatorSeries_intertwine _ inverseFactorial_norm_le_one _ _ _ _ _ (seamTailShift_generator h a b ha hb)
  all_goals
    apply (seamGaugeGenerator_norm _ _ (seamSineRow_constant_bound _ _) (seamSineRow_square_norm _ _)
      (seamSineColumn_constant_bound _ _) (seamSineColumn_square_norm _ _)).trans_lt
    norm_num

theorem seamTailShift_physical_graph (h : ℕ) (t : ℕ → ℂ)
    (ht : ∀ i, ‖t i‖ ≤ (1/4096 : ℝ)^3) :
    seamTailShift h*seamPhysicalGraph t ht=
      seamPhysicalGraph (fun i => t (i+h)) (fun i => ht (i+h))*seamTailShift h := by
  ext u p
  change seamTailShift h (seamPhysicalGraph t ht u) p=
    seamPhysicalGraph (fun i => t (i+h)) (fun i => ht (i+h)) (seamTailShift h u) p
  simp only [seamTailShift_apply,seamPhysicalGraph_apply,seamPhysicalGraphCoefficient,
    seamParityExchange,seamTailIndex,Nat.add_right_cancel_iff]

theorem seamTailShift_spectral_graph (h : ℕ) (t : ℕ → ℂ)
    (ht : ∀ i, ‖t i‖ ≤ (1/4096 : ℝ)^3) :
    seamTailShift h*seamSpectralGraph t ht=
      seamSpectralGraph (fun i => t (i+h)) (fun i => ht (i+h))*seamTailShift h := by
  ext u p
  change seamTailShift h (seamSpectralGraph t ht u) p=
    seamSpectralGraph (fun i => t (i+h)) (fun i => ht (i+h)) (seamTailShift h u) p
  simp only [seamTailShift_apply,seamSpectralGraph_apply,seamSpectralGraphCoefficient,
    seamParityExchange,seamTailIndex,Nat.add_right_cancel_iff]

/-- The entire graph-corrected seam equation is covariant under simultaneous tail extraction. -/
theorem seamTailShift_full_operator (h : ℕ) (a b ta tb : ℕ → ℂ)
    (ha : ∀ i, ‖a i‖ ≤ (1/4096 : ℝ)^2) (hb : ∀ i, ‖b i‖ ≤ (1/4096 : ℝ)^2)
    (hta : ∀ i, ‖ta i‖ ≤ (1/4096 : ℝ)^3) (htb : ∀ i, ‖tb i‖ ≤ (1/4096 : ℝ)^3) :
    seamTailShift h*seamFullOperator a b ta tb ha hb hta htb=
      seamFullOperator (fun i => a (i+h)) (fun i => b (i+h)) (fun i => ta (i+h)) (fun i => tb (i+h))
        (fun i => ha (i+h)) (fun i => hb (i+h)) (fun i => hta (i+h)) (fun i => htb (i+h))*seamTailShift h := by
  have he := seamTailShift_gauge h a b ha hb
  change seamTailShift h*_= _*seamTailShift h at he
  exact ((SemiconjBy.sub_right
    (show SemiconjBy _ _ _ from seamTailShift_Q h)
    (show SemiconjBy _ _ _ from seamTailShift_spectral_graph h tb htb)).mul_right
      (show SemiconjBy _ _ _ from he)).mul_right
    ((SemiconjBy.one_right (seamTailShift h)).add_right
      (show SemiconjBy _ _ _ from seamTailShift_physical_graph h ta hta))

/-- Every whole flag-kernel vector yields a whole kernel vector for the shifted node sequence. -/
theorem seamTailShift_kernel (h : ℕ) (a b ta tb : ℕ → ℂ)
    (ha : ∀ i, ‖a i‖ ≤ (1/4096 : ℝ)^2) (hb : ∀ i, ‖b i‖ ≤ (1/4096 : ℝ)^2)
    (hta : ∀ i, ‖ta i‖ ≤ (1/4096 : ℝ)^3) (htb : ∀ i, ‖tb i‖ ≤ (1/4096 : ℝ)^3)
    (u : SeamMomentArray) (hu : seamFullOperator a b ta tb ha hb hta htb u=0) :
    seamFullOperator (fun i => a (i+h)) (fun i => b (i+h)) (fun i => ta (i+h)) (fun i => tb (i+h))
      (fun i => ha (i+h)) (fun i => hb (i+h)) (fun i => hta (i+h)) (fun i => htb (i+h))
      (seamTailShift h u)=0 := by
  have hh := congrArg (fun A : SeamMomentArray →L[ℂ] SeamMomentArray => A u)
    (seamTailShift_full_operator h a b ta tb ha hb hta htb)
  change seamTailShift h (seamFullOperator a b ta tb ha hb hta htb u)=_ at hh
  rw [hu,map_zero] at hh
  exact hh.symm

end
end MeyerGeneralProblem.Adaptive
