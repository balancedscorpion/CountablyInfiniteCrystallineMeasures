module

public import MeyerGeneralProblem.Cardinal.Adaptive.HalfNewtonCoordinates
public import MeyerGeneralProblem.Cardinal.Adaptive.SeamSineOperator

@[expose] public section

/-! # Actual compact test recurrences identifying the whole Newton operators -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section

/-- The literal compact Newton test multiplied by the Newton coordinate. -/
def halfNewtonNodeTest (ε : ℕ+ → ℝ) (i : ℕ) (e : Bool) : SchwartzMap ℝ ℂ :=
  halfNewtonTest ε (i+1) e+criticalNewtonNode (ε ⟨i+1,by omega⟩) •halfNewtonTest ε i e

/-- Pointwise multiplication is identified on the complete genuine test. -/
theorem halfNewtonNodeTest_apply (ε : ℕ+ → ℝ) (i : ℕ) (e : Bool) (x : ℝ) :
    halfNewtonNodeTest ε i e x=criticalNewtonNode x*halfNewtonTest ε i e x := by
  have h := congrFun (halfNewtonFunction_mul_node ε i e) x
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul] at h
  change zakCentralCutoff x*halfNewtonFunction ε (i+1) e x+
    criticalNewtonNode (ε ⟨i+1,by omega⟩)*(zakCentralCutoff x*halfNewtonFunction ε i e x)=_
  rw [halfNewtonTest_apply]
  linear_combination -(zakCentralCutoff x)*h

/-- Literal sine multiplication of the genuine compact test, at either parity. -/
def halfNewtonSineTest (ε : ℕ+ → ℝ) (i : ℕ) (e : Bool) : SchwartzMap ℝ ℂ :=
  if e then halfNewtonNodeTest ε i false
  else (2-criticalNewtonNode (ε ⟨i+1,by omega⟩)) •halfNewtonTest ε i true-halfNewtonTest ε (i+1) true

theorem halfNewtonSineTest_apply (ε : ℕ+ → ℝ) (i : ℕ) (e : Bool) (x : ℝ) :
    halfNewtonSineTest ε i e x=(Real.sin (2*Real.pi*x) : ℂ)*halfNewtonTest ε i e x := by
  cases e
  · have h := congrFun (halfNewtonFunction_sin_even ε i) x
    simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul] at h
    change (2-criticalNewtonNode (ε ⟨i+1,by omega⟩))*(zakCentralCutoff x*halfNewtonFunction ε i true x)-
      zakCentralCutoff x*halfNewtonFunction ε (i+1) true x=_
    rw [halfNewtonTest_apply]
    linear_combination -(zakCentralCutoff x)*h
  · have h := congrFun (halfNewtonFunction_sin_odd ε i) x
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul] at h
    change zakCentralCutoff x*halfNewtonFunction ε (i+1) false x+
      criticalNewtonNode (ε ⟨i+1,by omega⟩)*(zakCentralCutoff x*halfNewtonFunction ε i false x)=_
    rw [halfNewtonTest_apply]
    linear_combination -(zakCentralCutoff x)*h

/-- The scalar normalization of every full constant-R Newton coordinate. -/
def halfNewtonNormalization (i : ℕ) (e : Bool) (j : ℕ) (f : Bool) : ℂ :=
  ((1/4096 : ℂ)^(i+j)*(1/64 : ℂ)^(e.toNat+f.toNat))⁻¹

theorem halfNewtonNormalization_row_succ (i j : ℕ) (e f : Bool) :
    halfNewtonNormalization i e j f=(1/4096 : ℂ)*halfNewtonNormalization (i+1) e j f := by
  unfold halfNewtonNormalization
  rw [show i+1+j=(i+j)+1 by omega,pow_succ,mul_inv_rev,mul_inv_rev]
  norm_num
  ring

/-- Every original whole-source bilinear pairing respects the true test addition. -/
theorem halfNewtonBilinear_add_first (T : TemperedDistribution ℝ ℂ) (u v w : SchwartzMap ℝ ℂ) :
    halfNewtonBilinear T (u+v) w=halfNewtonBilinear T u w+halfNewtonBilinear T v w := by
  simp only [halfNewtonBilinear,map_add,zakTensorAction_add_left]

theorem halfNewtonBilinear_smul_first (T : TemperedDistribution ℝ ℂ) (a : ℂ) (u v : SchwartzMap ℝ ℂ) :
    halfNewtonBilinear T (a •u) v=a*halfNewtonBilinear T u v := by
  simp only [halfNewtonBilinear,map_smul,zakTensorAction_smul_left]

theorem halfNewtonBilinear_sub_first (T : TemperedDistribution ℝ ℂ) (u v w : SchwartzMap ℝ ℂ) :
    halfNewtonBilinear T (u-v) w=halfNewtonBilinear T u w-halfNewtonBilinear T v w := by
  have hn := halfNewtonBilinear_smul_first T (-1) v w
  rw [neg_one_smul] at hn
  rw [sub_eq_add_neg,halfNewtonBilinear_add_first,hn]
  ring

/-- Actual multiplication by z yields the complete normalized row recurrence. -/
theorem halfNewtonMoment_node_row (ε δ : ℕ+ → ℝ) (T : TemperedDistribution ℝ ℂ)
    (i j : ℕ) (e f : Bool) :
    halfNewtonNormalization i e j f*halfNewtonBilinear T (halfNewtonNodeTest ε i e) (halfNewtonTest δ j f)=
      (1/4096 : ℂ)*halfNewtonMoment ε δ T (i+1) e j f+
        criticalNewtonNode (ε ⟨i+1,by omega⟩)*halfNewtonMoment ε δ T i e j f := by
  rw [halfNewtonNodeTest,halfNewtonBilinear_add_first,halfNewtonBilinear_smul_first]
  change halfNewtonNormalization i e j f*(_+_)=
    (1/4096 : ℂ)*(halfNewtonNormalization (i+1) e j f*_)+
      criticalNewtonNode (ε ⟨i+1,by omega⟩)*(halfNewtonNormalization i e j f*_)
  simp only [halfNewtonCoordinate]
  rw [mul_add]
  congr 1
  · rw [halfNewtonNormalization_row_succ i j e f]
    ring
  · ring

/-- The exact parity normalization retained by the full sine operator. -/
theorem halfNewtonNormalization_even (i j : ℕ) (f : Bool) :
    halfNewtonNormalization i false j f=(1/64 : ℂ)*halfNewtonNormalization i true j f := by
  unfold halfNewtonNormalization
  simp only [Bool.toNat_false,Bool.toNat_true,zero_add,show 1+f.toNat=f.toNat+1 by omega,pow_succ,mul_inv_rev]
  norm_num
  ring

/-- Exact original whole-source even-to-odd sine recurrence. -/
theorem halfNewtonMoment_sine_row_even (ε δ : ℕ+ → ℝ) (T : TemperedDistribution ℝ ℂ)
    (i j : ℕ) (f : Bool) :
    halfNewtonNormalization i false j f*halfNewtonBilinear T (halfNewtonSineTest ε i false) (halfNewtonTest δ j f)=
      (1/64 : ℂ)*(2*halfNewtonMoment ε δ T i true j f-
        ((1/4096 : ℂ)*halfNewtonMoment ε δ T (i+1) true j f+
          criticalNewtonNode (ε ⟨i+1,by omega⟩)*halfNewtonMoment ε δ T i true j f)) := by
  simp only [halfNewtonSineTest,Bool.false_eq_true,ite_false,halfNewtonBilinear_sub_first,halfNewtonBilinear_smul_first]
  change halfNewtonNormalization i false j f*((2-criticalNewtonNode (ε ⟨i+1,by omega⟩))*_ - _)=
    (1/64 : ℂ)*(2*(halfNewtonNormalization i true j f*_)-
      ((1/4096 : ℂ)*(halfNewtonNormalization (i+1) true j f*_)+
        criticalNewtonNode (ε ⟨i+1,by omega⟩)*(halfNewtonNormalization i true j f*_)))
  simp only [halfNewtonCoordinate]
  rw [halfNewtonNormalization_even,halfNewtonNormalization_row_succ i j true f]
  ring

/-- Exact original whole-source odd-to-even sine recurrence. -/
theorem halfNewtonMoment_sine_row_odd (ε δ : ℕ+ → ℝ) (T : TemperedDistribution ℝ ℂ)
    (i j : ℕ) (f : Bool) :
    halfNewtonNormalization i true j f*halfNewtonBilinear T (halfNewtonSineTest ε i true) (halfNewtonTest δ j f)=
      (1/64 : ℂ)⁻¹*((1/4096 : ℂ)*halfNewtonMoment ε δ T (i+1) false j f+
        criticalNewtonNode (ε ⟨i+1,by omega⟩)*halfNewtonMoment ε δ T i false j f) := by
  have h := halfNewtonMoment_node_row ε δ T i j false f
  rw [halfNewtonNormalization_even] at h
  change halfNewtonNormalization i true j f*halfNewtonBilinear T (halfNewtonNodeTest ε i false) (halfNewtonTest δ j f)=_
  rw [← h]
  ring

/-- The literal node-multiplied coordinates of any actual moment vector
are the genuine bounded whole-array Newton operator. -/
theorem halfNewtonMoment_node_operator (ε δ : ℕ+ → ℝ) (T : TemperedDistribution ℝ ℂ)
    (K : ℝ) (hK : 0 ≤ K) (ha : ∀ i, ‖criticalNewtonNode (ε ⟨i+1,by omega⟩)‖ ≤ K)
    (u : SeamMomentArray) (hu : ∀ i e j f, u ((i,e),(j,f))=halfNewtonMoment ε δ T i e j f)
    (i j : ℕ) (e f : Bool) :
    seamNewtonRow (1/4096) (fun n => criticalNewtonNode (ε ⟨n+1,by omega⟩)) K hK ha u ((i,e),(j,f))=
      halfNewtonNormalization i e j f*halfNewtonBilinear T (halfNewtonNodeTest ε i e) (halfNewtonTest δ j f) := by
  rw [seamNewtonRow_apply,hu,hu]
  exact (halfNewtonMoment_node_row ε δ T i j e f).symm

/-- The actual compact sine multiplier is represented by the proved complete
Hilbert operator on every actual square-summable source array. -/
theorem halfNewtonMoment_sine_operator (ε δ : ℕ+ → ℝ) (T : TemperedDistribution ℝ ℂ)
    (K : ℝ) (hK : 0 ≤ K) (ha : ∀ i, ‖criticalNewtonNode (ε ⟨i+1,by omega⟩)‖ ≤ K)
    (u : SeamMomentArray) (hu : ∀ i e j f, u ((i,e),(j,f))=halfNewtonMoment ε δ T i e j f)
    (i j : ℕ) (e f : Bool) :
    seamSineRow (1/64) (1/4096) (fun n => criticalNewtonNode (ε ⟨n+1,by omega⟩)) K hK ha u ((i,e),(j,f))=
      halfNewtonNormalization i e j f*halfNewtonBilinear T (halfNewtonSineTest ε i e) (halfNewtonTest δ j f) := by
  rw [seamSineRow_apply]
  cases e
  · simpa only [Bool.false_eq_true,ite_false,hu] using (halfNewtonMoment_sine_row_even ε δ T i j f).symm
  · simpa only [ite_true,hu] using (halfNewtonMoment_sine_row_odd ε δ T i j f).symm

theorem halfNewtonNormalization_swap (i j : ℕ) (e f : Bool) :
    halfNewtonNormalization i e j f=halfNewtonNormalization j f i e := by
  simp only [halfNewtonNormalization,Nat.add_comm]

theorem halfNewtonNormalization_column_succ (i j : ℕ) (e f : Bool) :
    halfNewtonNormalization i e j f=(1/4096 : ℂ)*halfNewtonNormalization i e (j+1) f := by
  rw [halfNewtonNormalization_swap i j e f,halfNewtonNormalization_swap i (j+1) e f]
  exact halfNewtonNormalization_row_succ j i f e

theorem halfNewtonNormalization_second_even (i j : ℕ) (e : Bool) :
    halfNewtonNormalization i e j false=(1/64 : ℂ)*halfNewtonNormalization i e j true := by
  rw [halfNewtonNormalization_swap i j e false,halfNewtonNormalization_swap i j e true]
  exact halfNewtonNormalization_even j i e

theorem halfNewtonBilinear_add_second (T : TemperedDistribution ℝ ℂ) (u v w : SchwartzMap ℝ ℂ) :
    halfNewtonBilinear T u (v+w)=halfNewtonBilinear T u v+halfNewtonBilinear T u w := by
  simp only [halfNewtonBilinear,map_add,zakTensorAction_add_right]

theorem halfNewtonBilinear_smul_second (T : TemperedDistribution ℝ ℂ) (a : ℂ) (u v : SchwartzMap ℝ ℂ) :
    halfNewtonBilinear T u (a •v)=a*halfNewtonBilinear T u v := by
  simp only [halfNewtonBilinear,map_smul,zakTensorAction_smul_right]

theorem halfNewtonBilinear_sub_second (T : TemperedDistribution ℝ ℂ) (u v w : SchwartzMap ℝ ℂ) :
    halfNewtonBilinear T u (v-w)=halfNewtonBilinear T u v-halfNewtonBilinear T u w := by
  have hn := halfNewtonBilinear_smul_second T (-1) u w
  rw [neg_one_smul] at hn
  rw [sub_eq_add_neg,halfNewtonBilinear_add_second,hn]
  ring

/-- The original complete node recurrence holds on the spectral axis too. -/
theorem halfNewtonMoment_node_column (ε δ : ℕ+ → ℝ) (T : TemperedDistribution ℝ ℂ)
    (i j : ℕ) (e f : Bool) :
    halfNewtonNormalization i e j f*halfNewtonBilinear T (halfNewtonTest ε i e) (halfNewtonNodeTest δ j f)=
      (1/4096 : ℂ)*halfNewtonMoment ε δ T i e (j+1) f+
        criticalNewtonNode (δ ⟨j+1,by omega⟩)*halfNewtonMoment ε δ T i e j f := by
  rw [halfNewtonNodeTest,halfNewtonBilinear_add_second,halfNewtonBilinear_smul_second]
  change halfNewtonNormalization i e j f*(_+_)=
    (1/4096 : ℂ)*(halfNewtonNormalization i e (j+1) f*_)+
      criticalNewtonNode (δ ⟨j+1,by omega⟩)*(halfNewtonNormalization i e j f*_)
  simp only [halfNewtonCoordinate]
  rw [mul_add]
  congr 1
  · rw [halfNewtonNormalization_column_succ i j e f]
    ring
  · ring

/-- Exact original-source spectral even-to-odd sine recurrence. -/
theorem halfNewtonMoment_sine_column_even (ε δ : ℕ+ → ℝ) (T : TemperedDistribution ℝ ℂ)
    (i j : ℕ) (e : Bool) :
    halfNewtonNormalization i e j false*halfNewtonBilinear T (halfNewtonTest ε i e) (halfNewtonSineTest δ j false)=
      (1/64 : ℂ)*(2*halfNewtonMoment ε δ T i e j true-
        ((1/4096 : ℂ)*halfNewtonMoment ε δ T i e (j+1) true+
          criticalNewtonNode (δ ⟨j+1,by omega⟩)*halfNewtonMoment ε δ T i e j true)) := by
  simp only [halfNewtonSineTest,Bool.false_eq_true,ite_false,halfNewtonBilinear_sub_second,halfNewtonBilinear_smul_second]
  change halfNewtonNormalization i e j false*((2-criticalNewtonNode (δ ⟨j+1,by omega⟩))*_ - _)=
    (1/64 : ℂ)*(2*(halfNewtonNormalization i e j true*_)-
      ((1/4096 : ℂ)*(halfNewtonNormalization i e (j+1) true*_)+
        criticalNewtonNode (δ ⟨j+1,by omega⟩)*(halfNewtonNormalization i e j true*_)))
  simp only [halfNewtonCoordinate]
  rw [halfNewtonNormalization_second_even,halfNewtonNormalization_column_succ i j e true]
  ring

/-- Exact original-source spectral odd-to-even sine recurrence. -/
theorem halfNewtonMoment_sine_column_odd (ε δ : ℕ+ → ℝ) (T : TemperedDistribution ℝ ℂ)
    (i j : ℕ) (e : Bool) :
    halfNewtonNormalization i e j true*halfNewtonBilinear T (halfNewtonTest ε i e) (halfNewtonSineTest δ j true)=
      (1/64 : ℂ)⁻¹*((1/4096 : ℂ)*halfNewtonMoment ε δ T i e (j+1) false+
        criticalNewtonNode (δ ⟨j+1,by omega⟩)*halfNewtonMoment ε δ T i e j false) := by
  have h := halfNewtonMoment_node_column ε δ T i j e false
  rw [halfNewtonNormalization_second_even] at h
  change halfNewtonNormalization i e j true*halfNewtonBilinear T (halfNewtonTest ε i e) (halfNewtonNodeTest δ j false)=_
  rw [← h]
  ring

/-- The actual spectral compact sine multiplier agrees with the complete
column Hilbert operator, with all parity and integer signs retained. -/
theorem halfNewtonMoment_sine_column_operator (ε δ : ℕ+ → ℝ) (T : TemperedDistribution ℝ ℂ)
    (K : ℝ) (hK : 0 ≤ K) (hb : ∀ j, ‖criticalNewtonNode (δ ⟨j+1,by omega⟩)‖ ≤ K)
    (u : SeamMomentArray) (hu : ∀ i e j f, u ((i,e),(j,f))=halfNewtonMoment ε δ T i e j f)
    (i j : ℕ) (e f : Bool) :
    seamSineColumn (1/64) (1/4096) (fun n => criticalNewtonNode (δ ⟨n+1,by omega⟩)) K hK hb u ((i,e),(j,f))=
      halfNewtonNormalization i e j f*halfNewtonBilinear T (halfNewtonTest ε i e) (halfNewtonSineTest δ j f) := by
  rw [seamSineColumn_apply]
  cases f
  · simpa only [Bool.false_eq_true,ite_false,hu] using (halfNewtonMoment_sine_column_even ε δ T i j e).symm
  · simpa only [ite_true,hu] using (halfNewtonMoment_sine_column_odd ε δ T i j e).symm

end
end MeyerGeneralProblem.Adaptive
