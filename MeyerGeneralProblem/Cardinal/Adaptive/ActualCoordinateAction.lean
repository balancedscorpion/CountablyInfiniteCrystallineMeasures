module

public import MeyerGeneralProblem.Cardinal.Adaptive.CompactSineSeries
public import MeyerGeneralProblem.Cardinal.Adaptive.HalfNewtonMultiplierRecurrences
public import MeyerGeneralProblem.Cardinal.Adaptive.SeamCoordinateIntertwining

@[expose] public section

/-! # Actual full operator action through continuous Schwartz slices -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section

/-- One literal sine multiplier is precisely the exact Newton test recurrence. -/
theorem compactSinePower_one_halfNewtonTest (ε : ℕ+ → ℝ) (i : ℕ) (e : Bool) :
    compactSinePower 1 (halfNewtonTest ε i e)=halfNewtonSineTest ε i e := by
  ext x
  rw [compactSinePower_apply,pow_one,halfNewtonSineTest_apply]

/-- Sine-power test multiplication composes exactly at every order. -/
theorem compactSinePower_comp (a b : ℕ) (f : SchwartzMap ℝ ℂ) :
    compactSinePower a (compactSinePower b f)=compactSinePower (a+b) f := by
  ext x
  simp only [compactSinePower_apply,pow_add]
  ring

private theorem node_slice_recurrence (ε : ℕ+ → ℝ) (U : TemperedDistribution ℝ ℂ)
    (i j : ℕ) (e f : Bool) :
    halfNewtonNormalization i e j f*U (halfNewtonNodeTest ε i e)=
      (1/4096 : ℂ)*(halfNewtonNormalization (i+1) e j f*U (halfNewtonTest ε (i+1) e))+
      criticalNewtonNode (ε ⟨i+1,by omega⟩)*(halfNewtonNormalization i e j f*U (halfNewtonTest ε i e)) := by
  simp only [halfNewtonNodeTest,map_add,map_smul,smul_eq_mul]
  rw [halfNewtonNormalization_row_succ i j e f]
  ring

/-- The full bounded sine operator acts on any actual continuous slice family
by literal sine multiplication. This finite algebra does not alter any source carrier. -/
theorem seamSineRow_slice_action (ε : ℕ+ → ℝ)
    (K : ℝ) (hK : 0 ≤ K) (ha : ∀ i, ‖criticalNewtonNode (ε ⟨i+1,by omega⟩)‖ ≤ K)
    (U : ℕ → Bool → TemperedDistribution ℝ ℂ) (u : SeamMomentArray)
    (hu : ∀ i e j f, u ((i,e),(j,f))=halfNewtonNormalization i e j f*U j f (halfNewtonTest ε i e))
    (i j : ℕ) (e f : Bool) :
    seamSineRow (1/64) (1/4096) (fun n => criticalNewtonNode (ε ⟨n+1,by omega⟩)) K hK ha u ((i,e),(j,f))=
      halfNewtonNormalization i e j f*U j f (compactSinePower 1 (halfNewtonTest ε i e)) := by
  rw [seamSineRow_apply,compactSinePower_one_halfNewtonTest]
  cases e
  · simp only [Bool.false_eq_true,ite_false,hu,halfNewtonSineTest,map_sub,map_smul,smul_eq_mul]
    rw [halfNewtonNormalization_even,halfNewtonNormalization_row_succ i j true f]
    ring
  · simp only [ite_true,hu,halfNewtonSineTest]
    have h := node_slice_recurrence ε (U j f) i j false f
    rw [←h,halfNewtonNormalization_even]
    norm_num
    ring

/-- Every power of the actual full sine operator is identified with the
corresponding complete test multiplier, without a finite-dimensional truncation. -/
theorem seamSineRow_pow_slice_action (ε : ℕ+ → ℝ)
    (K : ℝ) (hK : 0 ≤ K) (ha : ∀ i, ‖criticalNewtonNode (ε ⟨i+1,by omega⟩)‖ ≤ K)
    (U : ℕ → Bool → TemperedDistribution ℝ ℂ) (u : SeamMomentArray)
    (hu : ∀ i e j f, u ((i,e),(j,f))=halfNewtonNormalization i e j f*U j f (halfNewtonTest ε i e))
    (d i j : ℕ) (e f : Bool) :
    ((seamSineRow (1/64) (1/4096) (fun n => criticalNewtonNode (ε ⟨n+1,by omega⟩)) K hK ha)^d) u ((i,e),(j,f))=
      halfNewtonNormalization i e j f*U j f (compactSinePower d (halfNewtonTest ε i e)) := by
  induction d generalizing i j e f with
  | zero => simpa only [pow_zero,ContinuousLinearMap.one_apply,compactSinePower,
      pow_zero,SchwartzMap.smulLeftCLM_const,one_smul,ContinuousLinearMap.id_apply] using hu i e j f
  | succ d ih =>
    let V (j : ℕ) (f : Bool) : TemperedDistribution ℝ ℂ :=
      (U j f).comp (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => (Real.sin (2*Real.pi*x):ℂ)^d))
    have hv := seamSineRow_slice_action ε K hK ha V
      (((seamSineRow (1/64) (1/4096) (fun n => criticalNewtonNode (ε ⟨n+1,by omega⟩)) K hK ha)^d) u)
      (fun i e j f => ih i j e f) i j e f
    rw [pow_succ',ContinuousLinearMap.mul_apply]
    change _=halfNewtonNormalization i e j f*U j f (compactSinePower (d+1) (halfNewtonTest ε i e))
    rw [hv]
    change halfNewtonNormalization i e j f*U j f (compactSinePower d (compactSinePower 1 (halfNewtonTest ε i e)))=_
    rw [compactSinePower_comp]

/-- The actual bounded coordinate operator is the complete odd sine-power
series, converging in operator norm. -/
theorem seamCoordinateOperator_hasSum (S : SeamMomentArray →L[ℂ] SeamMomentArray)
    (hS : ‖S*S‖ < 1) :
    HasSum (fun n => ((2*Real.pi:ℂ)⁻¹*(scalarArcsineCoefficient n:ℂ)) •S^(2*n+1))
      (seamCoordinateOperator S) := by
  have h := HasSum.const_smul ((2*Real.pi:ℂ)⁻¹) ((seamArcsineFactor_hasSum (S*S) hS).mul_left S)
  have he (n : ℕ) : (2*Real.pi:ℂ)⁻¹ •(S*((scalarArcsineCoefficient n:ℂ) •(S*S)^n))=
      ((2*Real.pi:ℂ)⁻¹*(scalarArcsineCoefficient n:ℂ)) •S^(2*n+1) := by
    rw [mul_smul_comm,smul_smul,←pow_two,←pow_mul,pow_succ']
  simpa only [he,seamCoordinateOperator] using h

/-- Literal multiplication by an arbitrary compact Schwartz chart factor. -/
def schwartzChartProduct (φ f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.smulLeftCLM ℂ (φ : ℝ → ℂ) f

/-- The chart product is pointwise multiplication of the genuine tests. -/
theorem schwartzChartProduct_apply (φ f : SchwartzMap ℝ ℂ) (x : ℝ) :
    schwartzChartProduct φ f x=φ x*f x :=
  SchwartzMap.smulLeftCLM_apply_apply φ.hasTemperateGrowth f x

/-- Compact chart multiplication commutes with every complete sine power. -/
theorem schwartzChartProduct_sinePower (φ f : SchwartzMap ℝ ℂ) (d : ℕ) :
    schwartzChartProduct φ (compactSinePower d f)=compactSinePower d (schwartzChartProduct φ f) := by
  ext x
  simp only [schwartzChartProduct_apply,compactSinePower_apply]
  ring

/-- Coordinate multiplication can be moved onto the compact chart factor exactly. -/
theorem schwartzChartProduct_coordinate (φ f : SchwartzMap ℝ ℂ) :
    mixedSchwartz 1 0 (schwartzChartProduct φ f)=schwartzChartProduct (mixedSchwartz 1 0 φ) f := by
  ext x
  simp only [schwartzChartProduct_apply,mixedSchwartz_apply,iteratedDeriv_zero,pow_one]
  ring

/-- The full bounded physical coordinate operator acts on actual compact
Schwartz slices by literal coordinate multiplication. Both infinite array arms
and the entire convergent arcsine series are retained. -/
theorem seamCoordinateRow_chart_slice_action (ε : ℕ+ → ℝ)
    (K : ℝ) (hK : 0 ≤ K) (ha : ∀ i, ‖criticalNewtonNode (ε ⟨i+1,by omega⟩)‖ ≤ K)
    (φ : SchwartzMap ℝ ℂ) (b : ℝ) (hb : 0 < b) (hb' : b < 1/8)
    (hφ : ∀ x, b ≤ |x| → φ x=0)
    (V : ℕ → Bool → TemperedDistribution ℝ ℂ) (u : SeamMomentArray)
    (hu : ∀ i e j f, u ((i,e),(j,f))=
      halfNewtonNormalization i e j f*V j f (schwartzChartProduct φ (halfNewtonTest ε i e)))
    (hS : ‖(seamSineRow (1/64) (1/4096) (fun n => criticalNewtonNode (ε ⟨n+1,by omega⟩)) K hK ha)*
      (seamSineRow (1/64) (1/4096) (fun n => criticalNewtonNode (ε ⟨n+1,by omega⟩)) K hK ha)‖ < 1)
    (i j : ℕ) (e f : Bool) :
    seamCoordinateOperator (seamSineRow (1/64) (1/4096)
      (fun n => criticalNewtonNode (ε ⟨n+1,by omega⟩)) K hK ha) u ((i,e),(j,f))=
      halfNewtonNormalization i e j f*V j f
        (schwartzChartProduct (mixedSchwartz 1 0 φ) (halfNewtonTest ε i e)) := by
  let S := seamSineRow (1/64) (1/4096) (fun n => criticalNewtonNode (ε ⟨n+1,by omega⟩)) K hK ha
  let U (j : ℕ) (f : Bool) : TemperedDistribution ℝ ℂ :=
    (V j f).comp (SchwartzMap.smulLeftCLM ℂ (φ : ℝ → ℂ))
  have hup : ∀ d i e j f, ((S^d) u) ((i,e),(j,f))=
      halfNewtonNormalization i e j f*V j f (compactSinePower d (schwartzChartProduct φ (halfNewtonTest ε i e))) := by
    intro d i e j f
    have h := seamSineRow_pow_slice_action ε K hK ha U u hu d i j e f
    change _=halfNewtonNormalization i e j f*V j f (schwartzChartProduct φ (compactSinePower d (halfNewtonTest ε i e))) at h
    simpa only [schwartzChartProduct_sinePower] using h
  have hop := (lp.evalCLM ℂ (fun _ : SeamMomentIndex => ℂ) 2 ((i,e),(j,f))).hasSum
    ((ContinuousLinearMap.apply ℂ SeamMomentArray u).hasSum (seamCoordinateOperator_hasSum S hS))
  change HasSum (fun n => ((2*Real.pi:ℂ)⁻¹*(scalarArcsineCoefficient n:ℂ))*((S^(2*n+1)) u ((i,e),(j,f))))
    (seamCoordinateOperator S u ((i,e),(j,f))) at hop
  simp only [hup] at hop
  have ht := (compactArcsineTerm_distribution_hasSum (schwartzChartProduct φ (halfNewtonTest ε i e))
    b hb hb' (by intro x hx; rw [schwartzChartProduct_apply,hφ x hx,zero_mul]) (V j f)).mul_left
      (halfNewtonNormalization i e j f)
  rw [schwartzChartProduct_coordinate] at ht
  have he : (fun n => ((2*Real.pi:ℂ)⁻¹*(scalarArcsineCoefficient n:ℂ))*
        (halfNewtonNormalization i e j f*V j f (compactSinePower (2*n+1) (schwartzChartProduct φ (halfNewtonTest ε i e)))))=
      (fun n => halfNewtonNormalization i e j f*V j f
        (compactArcsineTerm n (schwartzChartProduct φ (halfNewtonTest ε i e)))) := by
    funext n
    simp only [compactArcsineTerm,map_smul,smul_eq_mul]
    ring
  rw [he] at hop
  exact hop.unique ht

/-- The complete spectral coordinate acts on genuine compact frequency slices. -/
theorem seamCoordinateColumn_chart_slice_action (δ : ℕ+ → ℝ)
    (K : ℝ) (hK : 0 ≤ K) (ha : ∀ i, ‖criticalNewtonNode (δ ⟨i+1,by omega⟩)‖ ≤ K)
    (φ : SchwartzMap ℝ ℂ) (b : ℝ) (hb : 0 < b) (hb' : b < 1/8)
    (hφ : ∀ x, b ≤ |x| → φ x=0)
    (V : ℕ → Bool → TemperedDistribution ℝ ℂ) (u : SeamMomentArray)
    (hu : ∀ i e j f, u ((i,e),(j,f))=
      halfNewtonNormalization i e j f*V i e (schwartzChartProduct φ (halfNewtonTest δ j f)))
    (hS : ‖(seamSineRow (1/64) (1/4096) (fun n => criticalNewtonNode (δ ⟨n+1,by omega⟩)) K hK ha)*
      (seamSineRow (1/64) (1/4096) (fun n => criticalNewtonNode (δ ⟨n+1,by omega⟩)) K hK ha)‖ < 1)
    (i j : ℕ) (e f : Bool) :
    seamCoordinateOperator (seamSineColumn (1/64) (1/4096)
      (fun n => criticalNewtonNode (δ ⟨n+1,by omega⟩)) K hK ha) u ((i,e),(j,f))=
      halfNewtonNormalization i e j f*V i e
        (schwartzChartProduct (mixedSchwartz 1 0 φ) (halfNewtonTest δ j f)) := by
  have ht : ∀ j f i e, seamTranspose u ((j,f),(i,e))=
      halfNewtonNormalization j f i e*V i e (schwartzChartProduct φ (halfNewtonTest δ j f)) := by
    intro j f i e
    rw [seamTranspose_apply,hu,halfNewtonNormalization_swap]
  have h := seamCoordinateRow_chart_slice_action δ K hK ha φ b hb hb' hφ V (seamTranspose u) ht hS j i f e
  rw [seamSineColumn,seamCoordinateOperator_transpose _ hS]
  change seamCoordinateOperator _ (seamTranspose u) ((j,f),(i,e))=_
  rw [h,halfNewtonNormalization_swap]

/-- A physical coordinate is literal multiplication on the first factor of
any actual characteristic-adjusted Zak family. -/
theorem seamCoordinateRow_chart_bilinear_action (ε δ : ℕ+ → ℝ)
    (K : ℝ) (hK : 0 ≤ K) (ha : ∀ i, ‖criticalNewtonNode (ε ⟨i+1,by omega⟩)‖ ≤ K)
    (T : TemperedDistribution ℝ ℂ) (φ ψ : SchwartzMap ℝ ℂ)
    (b : ℝ) (hb : 0 < b) (hb' : b < 1/8) (hφ : ∀ x, b ≤ |x| → φ x=0)
    (u : SeamMomentArray)
    (hu : ∀ i e j f, u ((i,e),(j,f))=halfNewtonNormalization i e j f*
      halfNewtonBilinear T (schwartzChartProduct φ (halfNewtonTest ε i e))
        (schwartzChartProduct ψ (halfNewtonTest δ j f)))
    (hS : ‖(seamSineRow (1/64) (1/4096) (fun n => criticalNewtonNode (ε ⟨n+1,by omega⟩)) K hK ha)*
      (seamSineRow (1/64) (1/4096) (fun n => criticalNewtonNode (ε ⟨n+1,by omega⟩)) K hK ha)‖ < 1)
    (i j : ℕ) (e f : Bool) :
    seamCoordinateOperator (seamSineRow (1/64) (1/4096)
      (fun n => criticalNewtonNode (ε ⟨n+1,by omega⟩)) K hK ha) u ((i,e),(j,f))=
      halfNewtonNormalization i e j f*halfNewtonBilinear T
        (schwartzChartProduct (mixedSchwartz 1 0 φ) (halfNewtonTest ε i e))
        (schwartzChartProduct ψ (halfNewtonTest δ j f)) := by
  let V (j : ℕ) (f : Bool) : TemperedDistribution ℝ ℂ :=
    (zakPhysicalSlice T (combSchwartzModulation (-1/2) (schwartzChartProduct ψ (halfNewtonTest δ j f)))).comp
      (combSchwartzModulation (1/2))
  exact seamCoordinateRow_chart_slice_action ε K hK ha φ b hb hb' hφ V u hu hS i j e f

/-- A spectral coordinate is literal multiplication on the second factor of
any actual characteristic-adjusted Zak family. -/
theorem seamCoordinateColumn_chart_bilinear_action (ε δ : ℕ+ → ℝ)
    (K : ℝ) (hK : 0 ≤ K) (ha : ∀ i, ‖criticalNewtonNode (δ ⟨i+1,by omega⟩)‖ ≤ K)
    (T : TemperedDistribution ℝ ℂ) (φ ψ : SchwartzMap ℝ ℂ)
    (b : ℝ) (hb : 0 < b) (hb' : b < 1/8) (hψ : ∀ x, b ≤ |x| → ψ x=0)
    (u : SeamMomentArray)
    (hu : ∀ i e j f, u ((i,e),(j,f))=halfNewtonNormalization i e j f*
      halfNewtonBilinear T (schwartzChartProduct φ (halfNewtonTest ε i e))
        (schwartzChartProduct ψ (halfNewtonTest δ j f)))
    (hS : ‖(seamSineRow (1/64) (1/4096) (fun n => criticalNewtonNode (δ ⟨n+1,by omega⟩)) K hK ha)*
      (seamSineRow (1/64) (1/4096) (fun n => criticalNewtonNode (δ ⟨n+1,by omega⟩)) K hK ha)‖ < 1)
    (i j : ℕ) (e f : Bool) :
    seamCoordinateOperator (seamSineColumn (1/64) (1/4096)
      (fun n => criticalNewtonNode (δ ⟨n+1,by omega⟩)) K hK ha) u ((i,e),(j,f))=
      halfNewtonNormalization i e j f*halfNewtonBilinear T
        (schwartzChartProduct φ (halfNewtonTest ε i e))
        (schwartzChartProduct (mixedSchwartz 1 0 ψ) (halfNewtonTest δ j f)) := by
  let V (i : ℕ) (e : Bool) : TemperedDistribution ℝ ℂ :=
    (zakTensorSlice T (combSchwartzModulation (1/2) (schwartzChartProduct φ (halfNewtonTest ε i e)))).comp
      (combSchwartzModulation (-1/2))
  have hv : ∀ i e j f, u ((i,e),(j,f))=halfNewtonNormalization i e j f*
      V i e (schwartzChartProduct ψ (halfNewtonTest δ j f)) := by
    intro i e j f
    change _=halfNewtonNormalization i e j f*zakTensorSlice T
      (combSchwartzModulation (1/2) (schwartzChartProduct φ (halfNewtonTest ε i e)))
      (combSchwartzModulation (-1/2) (schwartzChartProduct ψ (halfNewtonTest δ j f)))
    simpa only [zakTensorSlice_apply,halfNewtonBilinear] using hu i e j f
  have hh := seamCoordinateColumn_chart_slice_action δ K hK ha ψ b hb hb' hψ V u hv hS i j e f
  change _=halfNewtonNormalization i e j f*zakTensorSlice T
    (combSchwartzModulation (1/2) (schwartzChartProduct φ (halfNewtonTest ε i e)))
    (combSchwartzModulation (-1/2) (schwartzChartProduct (mixedSchwartz 1 0 ψ) (halfNewtonTest δ j f))) at hh
  simpa only [zakTensorSlice_apply,halfNewtonBilinear] using hh

/-- The analytic coordinate passage depends only on the exact finite sine
recurrence of continuous slices. The normalization may be variable. -/
theorem actualCoordinate_chart_slice_action
    (N : ℕ → Bool → ℕ → Bool → ℂ) (ε : ℕ+ → ℝ)
    (S : SeamMomentArray →L[ℂ] SeamMomentArray) (hS : ‖S*S‖ < 1)
    (hrec : ∀ (U : ℕ → Bool → TemperedDistribution ℝ ℂ) (u : SeamMomentArray),
      (∀ i e j f, u ((i,e),(j,f))=N i e j f*U j f (halfNewtonTest ε i e)) →
      ∀ i e j f, S u ((i,e),(j,f))=N i e j f*U j f (compactSinePower 1 (halfNewtonTest ε i e)))
    (φ : SchwartzMap ℝ ℂ) (b : ℝ) (hb : 0 < b) (hb' : b < 1/8)
    (hφ : ∀ x, b ≤ |x| → φ x=0)
    (V : ℕ → Bool → TemperedDistribution ℝ ℂ) (u : SeamMomentArray)
    (hu : ∀ i e j f, u ((i,e),(j,f))=N i e j f*V j f (schwartzChartProduct φ (halfNewtonTest ε i e)))
    (i j : ℕ) (e f : Bool) :
    seamCoordinateOperator S u ((i,e),(j,f))=
      N i e j f*V j f (schwartzChartProduct (mixedSchwartz 1 0 φ) (halfNewtonTest ε i e)) := by
  have hp (U : ℕ → Bool → TemperedDistribution ℝ ℂ) (v : SeamMomentArray)
      (hv : ∀ i e j f, v ((i,e),(j,f))=N i e j f*U j f (halfNewtonTest ε i e)) :
      ∀ d i e j f, ((S^d) v) ((i,e),(j,f))=N i e j f*U j f (compactSinePower d (halfNewtonTest ε i e)) := by
    intro d
    induction d with
    | zero => simpa only [pow_zero,ContinuousLinearMap.one_apply,compactSinePower,
        pow_zero,SchwartzMap.smulLeftCLM_const,one_smul,ContinuousLinearMap.id_apply] using hv
    | succ d ih =>
      let W (j : ℕ) (f : Bool) : TemperedDistribution ℝ ℂ :=
        (U j f).comp (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => (Real.sin (2*Real.pi*x):ℂ)^d))
      have hh := hrec W ((S^d) v) ih
      intro i e j f
      rw [pow_succ',ContinuousLinearMap.mul_apply,hh]
      change N i e j f*U j f (compactSinePower d (compactSinePower 1 (halfNewtonTest ε i e)))=_
      rw [compactSinePower_comp]
  let U (j : ℕ) (f : Bool) : TemperedDistribution ℝ ℂ :=
    (V j f).comp (SchwartzMap.smulLeftCLM ℂ (φ : ℝ → ℂ))
  have hup : ∀ d i e j f, ((S^d) u) ((i,e),(j,f))=
      N i e j f*V j f (compactSinePower d (schwartzChartProduct φ (halfNewtonTest ε i e))) := by
    intro d i e j f
    have h := hp U u hu d i e j f
    change _=N i e j f*V j f (schwartzChartProduct φ (compactSinePower d (halfNewtonTest ε i e))) at h
    simpa only [schwartzChartProduct_sinePower] using h
  have hop := (lp.evalCLM ℂ (fun _ : SeamMomentIndex => ℂ) 2 ((i,e),(j,f))).hasSum
    ((ContinuousLinearMap.apply ℂ SeamMomentArray u).hasSum (seamCoordinateOperator_hasSum S hS))
  change HasSum (fun n => ((2*Real.pi:ℂ)⁻¹*(scalarArcsineCoefficient n:ℂ))*((S^(2*n+1)) u ((i,e),(j,f))))
    (seamCoordinateOperator S u ((i,e),(j,f))) at hop
  simp only [hup] at hop
  have ht := (compactArcsineTerm_distribution_hasSum (schwartzChartProduct φ (halfNewtonTest ε i e))
    b hb hb' (by intro x hx; rw [schwartzChartProduct_apply,hφ x hx,zero_mul]) (V j f)).mul_left (N i e j f)
  rw [schwartzChartProduct_coordinate] at ht
  have he : (fun n => ((2*Real.pi:ℂ)⁻¹*(scalarArcsineCoefficient n:ℂ))*
        (N i e j f*V j f (compactSinePower (2*n+1) (schwartzChartProduct φ (halfNewtonTest ε i e)))))=
      (fun n => N i e j f*V j f (compactArcsineTerm n (schwartzChartProduct φ (halfNewtonTest ε i e)))) := by
    funext n
    simp only [compactArcsineTerm,map_smul,smul_eq_mul]
    ring
  rw [he] at hop
  exact hop.unique ht

end
end MeyerGeneralProblem.Adaptive
