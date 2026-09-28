module

public import MeyerGeneralProblem.Cardinal.Adaptive.SeamCoordinateOperator
public import MeyerGeneralProblem.Cardinal.Adaptive.OperatorSeriesIntertwining

@[expose] public section

/-! # Exact full-series coordinate covariance under bounded intertwiners -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section

/-- Every bounded sine intertwiner acts on the complete coordinate series.
The identity includes the entire arcsine factor on both sides. -/
theorem seamCoordinateOperator_intertwine (U S T : SeamMomentArray →L[ℂ] SeamMomentArray)
    (hSS : ‖S*S‖ < 1) (hTT : ‖T*T‖ < 1) (h : U.comp S=T.comp U) :
    U.comp (seamCoordinateOperator S)=(seamCoordinateOperator T).comp U := by
  have hpow : U.comp (S*S)=(T*T).comp U := by
    simpa only [pow_two] using operator_intertwine_pow U S T h 2
  have hf : U*seamArcsineFactor (S*S)=seamArcsineFactor (T*T)*U :=
    boundedOperatorSeries_intertwine _ scalarArcsineCoefficient_cast_norm U (S*S) (T*T) hSS hTT hpow
  have hh : U*S=T*U := h
  change U*seamCoordinateOperator S=seamCoordinateOperator T*U
  simp only [seamCoordinateOperator,seamOperator_mul_smul,seamOperator_smul_mul]
  congr 1
  calc
    U*(S*seamArcsineFactor (S*S))=(U*S)*seamArcsineFactor (S*S) := (mul_assoc _ _ _).symm
    _ = (T*U)*seamArcsineFactor (S*S) := by rw [hh]
    _ = T*(U*seamArcsineFactor (S*S)) := mul_assoc _ _ _
    _ = T*(seamArcsineFactor (T*T)*U) := by rw [hf]
    _ = (T*seamArcsineFactor (T*T))*U := (mul_assoc _ _ _).symm

/-- Exact square of an actual axis-conjugated whole operator. -/
theorem seamTranspose_conjugate_square (S : SeamMomentArray →L[ℂ] SeamMomentArray) :
    (seamTranspose.comp (S.comp seamTranspose))*(seamTranspose.comp (S.comp seamTranspose))=
      seamTranspose.comp ((S*S).comp seamTranspose) := by
  ext u p
  change seamTranspose (S (seamTranspose (seamTranspose (S (seamTranspose u))))) p=
    seamTranspose (S (S (seamTranspose u))) p
  rw [seamTranspose_involutive]

/-- The full scalar-series coordinate respects actual exchange of the two axes. -/
theorem seamCoordinateOperator_transpose (S : SeamMomentArray →L[ℂ] SeamMomentArray)
    (hSS : ‖S*S‖ < 1) :
    seamCoordinateOperator (seamTranspose.comp (S.comp seamTranspose))=
      seamTranspose.comp ((seamCoordinateOperator S).comp seamTranspose) := by
  let T := seamTranspose.comp (S.comp seamTranspose)
  have hTT : ‖T*T‖ < 1 := by
    dsimp only [T]
    rw [seamTranspose_conjugate_square]
    exact (seamTranspose_conjugate_norm (S*S)).trans_lt hSS
  have h : seamTranspose.comp S=T.comp seamTranspose := by
    ext u p
    change seamTranspose (S u) p=seamTranspose (S (seamTranspose (seamTranspose u))) p
    rw [seamTranspose_involutive]
  have hx := seamCoordinateOperator_intertwine seamTranspose S T hSS hTT h
  ext u p
  have he := congrArg (fun A : SeamMomentArray →L[ℂ] SeamMomentArray => A (seamTranspose u) p) hx
  change seamTranspose (seamCoordinateOperator S (seamTranspose u)) p=
    seamCoordinateOperator T (seamTranspose (seamTranspose u)) p at he
  rw [seamTranspose_involutive] at he
  exact he.symm

/-- The actual constant-R spectral coordinate is the exact axis exchange of
its physical operator, not an independently assumed matrix. -/
theorem seamCoordinateOperator_column (b : ℕ → ℂ) (hb : ∀ i, ‖b i‖ ≤ (1/4096 : ℝ)^2) :
    seamCoordinateOperator (seamSineColumn (1/64) (1/4096) b ((1/4096)^2) (by positivity) hb)=
      seamTranspose.comp ((seamCoordinateOperator (seamSineRow (1/64) (1/4096) b ((1/4096)^2) (by positivity) hb)).comp seamTranspose) :=
  seamCoordinateOperator_transpose _ ((seamSineRow_square_norm b hb).trans_lt (by norm_num))

end
end MeyerGeneralProblem.Adaptive
