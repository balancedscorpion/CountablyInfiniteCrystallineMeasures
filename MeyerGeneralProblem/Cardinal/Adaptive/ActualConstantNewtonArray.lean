module

public import MeyerGeneralProblem.Cardinal.Adaptive.FixedNewtonMembership
public import MeyerGeneralProblem.Cardinal.Adaptive.HalfNewtonGaugeLocalization

@[expose] public section

/-! # Actual complete constant-normalized source arrays -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open scoped FourierTransform ENNReal

/-- Natural-index extension of the actual signed phase distances; the unused
zeroth entry does not enter any Newton product. -/
def phaseNatDistance (α : ℕ+ → ℝ) (n : ℕ) : ℝ := 1/2-α n.toPNat'

/-- Positive-index values coincide exactly with the original phase distances. -/
theorem phaseNatDistance_coe (α : ℕ+ → ℝ) (j : ℕ+) :
    phaseNatDistance α j=1/2-α j := by simp [phaseNatDistance]

/-- Whole paired-source phase localization identifies the complete fixed-chart
array with the prescribed Newton readings. -/
theorem fixedChartNewtonMoment_eq_actual (α β : ℕ+ → ℝ)
    (hia : ∀ j, 0 < α j ∧ α j < 1/2) (hib : ∀ j, 0 < β j ∧ β j < 1/2)
    (ha : ∀ j, |1/2-α j| ≤ 1/8192) (hb : ∀ j, |1/2-β j| ≤ 1/8192)
    (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier ((criticalPhaseTailCarrier α hia 0 0).translate (-1/2)) T)
    (hFT : AtomicOnCarrier ((criticalPhaseTailCarrier β hib 0 0).translate (-1/2)) (𝓕 T))
    (i j : ℕ) (e f : Bool) :
    fixedChartNewtonMoment (1/4096) (1/64) (1/8192) (1/4096) (by norm_num)
      (phaseNatDistance α) (phaseNatDistance β) T i e j f=
    halfNewtonMoment (fun l => 1/2-α l) (fun l => 1/2-β l) T i e j f := by
  unfold fixedChartNewtonMoment halfNewtonMoment halfNewtonCoordinate
  simp only [phaseNatDistance_coe,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat]
  rw [halfNewtonBilinear_shrinking_tests α β hia hib T hT hFT i j e f
    (1/8192) (1/4096) (1/8192) (1/4096) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun l => (ha l).trans (by norm_num)) (fun l => (hb l).trans (by norm_num))
    (fun l _ => ha l) (fun l _ => hb l)]

/-- Every original tempered paired source has its entire normalized moment
array in ℓ². The native order is derived from the source, without any moment premise. -/
theorem summable_sq_halfNewtonMatrix_actual (α β : ℕ+ → ℝ)
    (hia : ∀ j, 0 < α j ∧ α j < 1/2) (hib : ∀ j, 0 < β j ∧ β j < 1/2)
    (ha : ∀ j, |1/2-α j| ≤ 1/8192) (hb : ∀ j, |1/2-β j| ≤ 1/8192)
    (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier ((criticalPhaseTailCarrier α hia 0 0).translate (-1/2)) T)
    (hFT : AtomicOnCarrier ((criticalPhaseTailCarrier β hib 0 0).translate (-1/2)) (𝓕 T)) :
    Summable (fun z : (ℕ×Bool)×(ℕ×Bool) =>
      ‖halfNewtonMoment (fun l => 1/2-α l) (fun l => 1/2-β l) T
        z.1.1 z.1.2 z.2.1 z.2.2‖^2) := by
  obtain ⟨p,u,hu⟩ := exists_hermiteScale_representation T
  have h := summable_sq_fixedChartNewtonMatrix (1/4096) (1/8192) (1/4096) (1/64)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    p u (phaseNatDistance α) (phaseNatDistance β)
    (fun l => (ha (l+1).toPNat').trans (by norm_num))
    (fun l => (hb (l+1).toPNat').trans (by norm_num))
  simpa only [hu,fixedChartNewtonMoment_eq_actual α β hia hib ha hb T hT hFT] using h

/-- The actual complete source moments as one literal square-summable vector. -/
def actualConstantNewtonArray (α β : ℕ+ → ℝ)
    (hia : ∀ j, 0 < α j ∧ α j < 1/2) (hib : ∀ j, 0 < β j ∧ β j < 1/2)
    (ha : ∀ j, |1/2-α j| ≤ 1/8192) (hb : ∀ j, |1/2-β j| ≤ 1/8192)
    (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier ((criticalPhaseTailCarrier α hia 0 0).translate (-1/2)) T)
    (hFT : AtomicOnCarrier ((criticalPhaseTailCarrier β hib 0 0).translate (-1/2)) (𝓕 T)) :
    lp (fun _ : (ℕ×Bool)×(ℕ×Bool) => ℂ) 2 :=
  ⟨fun z => halfNewtonMoment (fun l => 1/2-α l) (fun l => 1/2-β l) T z.1.1 z.1.2 z.2.1 z.2.2,
    memℓp_gen (by simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
      summable_sq_halfNewtonMatrix_actual α β hia hib ha hb T hT hFT)⟩

/-- The literal array includes every actual moment, including both infinite arms. -/
theorem actualConstantNewtonArray_apply (α β : ℕ+ → ℝ)
    (hia : ∀ j, 0 < α j ∧ α j < 1/2) (hib : ∀ j, 0 < β j ∧ β j < 1/2)
    (ha : ∀ j, |1/2-α j| ≤ 1/8192) (hb : ∀ j, |1/2-β j| ≤ 1/8192)
    (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier ((criticalPhaseTailCarrier α hia 0 0).translate (-1/2)) T)
    (hFT : AtomicOnCarrier ((criticalPhaseTailCarrier β hib 0 0).translate (-1/2)) (𝓕 T))
    (z : (ℕ×Bool)×(ℕ×Bool)) :
    actualConstantNewtonArray α β hia hib ha hb T hT hFT z=
      halfNewtonMoment (fun l => 1/2-α l) (fun l => 1/2-β l) T z.1.1 z.1.2 z.2.1 z.2.2 := rfl

/-- The actual lp source vector retains the complete physical triangular flag. -/
theorem actualConstantNewtonArray_upper_flag (α β : ℕ+ → ℝ)
    (hia : ∀ j, 0 < α j ∧ α j < 1/2) (hib : ∀ j, 0 < β j ∧ β j < 1/2)
    (ha : ∀ j, |1/2-α j| ≤ 1/8192) (hb : ∀ j, |1/2-β j| ≤ 1/8192)
    (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier ((criticalPhaseTailCarrier α hia 0 0).translate (-1/2)) T)
    (hFT : AtomicOnCarrier ((criticalPhaseTailCarrier β hib 0 0).translate (-1/2)) (𝓕 T))
    (i j : ℕ) (e f : Bool) (hij : j < i) :
    actualConstantNewtonArray α β hia hib ha hb T hT hFT ((i,e),(j,f))=0 := by
  exact halfNewtonMoment_upper_flag α β hia hib
    (fun l => by have hh := (abs_le.mp (hb l)).2; linarith) T hT hFT i j e f hij

/-- The genuine complete lp vector is faithful to the whole original recentered source. -/
theorem actualConstantNewtonArray_faithful (α β : ℕ+ → ℝ)
    (hia : ∀ j, 0 < α j ∧ α j < 1/2) (hib : ∀ j, 0 < β j ∧ β j < 1/2)
    (ha : ∀ j, |1/2-α j| ≤ 1/8192) (hb : ∀ j, |1/2-β j| ≤ 1/8192)
    (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier ((criticalPhaseTailCarrier α hia 0 0).translate (-1/2)) T)
    (hFT : AtomicOnCarrier ((criticalPhaseTailCarrier β hib 0 0).translate (-1/2)) (𝓕 T))
    (hz : actualConstantNewtonArray α β hia hib ha hb T hT hFT=0) : T=0 := by
  apply halfNewtonCoordinates_faithful (fun l => 1/2-α l) (fun l => 1/2-β l) α β hia hib
    (fun l => by have hh := (abs_le.mp (ha l)).2; linarith)
    (fun l => by have hh := (abs_le.mp (hb l)).2; linarith) T hT hFT
  intro i e j f
  rw [←halfNewtonMoment_eq_zero_iff]
  exact congrArg (fun u : lp (fun _ : (ℕ×Bool)×(ℕ×Bool) => ℂ) 2 => u ((i,e),(j,f))) hz

/-- The complete original lp array has both exact physical diagonal equations. -/
theorem actualConstantNewtonArray_diagonal (α β : ℕ+ → ℝ)
    (hia : ∀ j, 0 < α j ∧ α j < 1/2) (hib : ∀ j, 0 < β j ∧ β j < 1/2)
    (ha : ∀ j, |1/2-α j| ≤ 1/8192) (hb : ∀ j, |1/2-β j| ≤ 1/8192)
    (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier ((criticalPhaseTailCarrier α hia 0 0).translate (-1/2)) T)
    (hFT : AtomicOnCarrier ((criticalPhaseTailCarrier β hib 0 0).translate (-1/2)) (𝓕 T))
    (i : ℕ) :
    let A := actualConstantNewtonArray α β hia hib ha hb T hT hFT
    A ((i,true),(i,false))=Complex.I*(Real.tan (Real.pi*(1/2-α ⟨i+1,Nat.succ_pos i⟩)):ℂ)*A ((i,false),(i,true)) ∧
    A ((i,true),(i,true))=(-Complex.I*(Real.tan (Real.pi*(1/2-α ⟨i+1,Nat.succ_pos i⟩)):ℂ)/(1/4096:ℂ))*A ((i,false),(i,false)) := by
  exact halfNewtonMoment_diagonal_relations α β hia hib
    (fun l => by have hh := (abs_le.mp (hb l)).2; linarith) T hT hFT i

/-- The full actual Fourier companion moment array is also square summable;
reflection, transposition and the exact parity sign preserve its complete norm. -/
theorem summable_sq_halfNewtonFourierMatrix_actual (α β : ℕ+ → ℝ)
    (hia : ∀ j, 0 < α j ∧ α j < 1/2) (hib : ∀ j, 0 < β j ∧ β j < 1/2)
    (ha : ∀ j, |1/2-α j| ≤ 1/8192) (hb : ∀ j, |1/2-β j| ≤ 1/8192)
    (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier (criticalPhaseTailCarrier α hia 0 0) T)
    (hFT : AtomicOnCarrier (criticalPhaseTailCarrier β hib 0 0) (𝓕 T)) :
    Summable (fun z : (ℕ×Bool)×(ℕ×Bool) =>
      ‖halfNewtonFourierMoment (fun l => 1/2-α l) (fun l => 1/2-β l) T
        z.1.1 z.1.2 z.2.1 z.2.2‖^2) := by
  obtain ⟨hp,hq⟩ := halfWeylFourierCompanion_atomic_records α β hia hib T hT hFT
  have h := summable_sq_halfNewtonMatrix_actual β α hib hia hb ha (halfWeylFourierCompanion T) hp hq
  have hs := (Equiv.prodComm (ℕ×Bool) (ℕ×Bool)).summable_iff.mpr h
  have he (z : (ℕ×Bool)×(ℕ×Bool)) :
      ‖halfNewtonFourierMoment (fun l => 1/2-α l) (fun l => 1/2-β l) T z.1.1 z.1.2 z.2.1 z.2.2‖^2=
      ‖halfNewtonMoment (fun l => 1/2-β l) (fun l => 1/2-α l) (halfWeylFourierCompanion T)
        z.2.1 z.2.2 z.1.1 z.1.2‖^2 := by
    rw [halfNewtonFourierMoment_eq_transposed,norm_mul]
    have hh : ‖halfNewtonParitySign z.1.2‖=1 := by cases z.1.2 <;> simp [halfNewtonParitySign]
    rw [hh,one_mul]
  simpa only [he,Function.comp_def,Equiv.prodComm_apply,Prod.fst_swap,Prod.snd_swap] using hs

/-- The complete actual Fourier moment vector, on the same literal lp index. -/
def actualConstantFourierArray (α β : ℕ+ → ℝ)
    (hia : ∀ j, 0 < α j ∧ α j < 1/2) (hib : ∀ j, 0 < β j ∧ β j < 1/2)
    (ha : ∀ j, |1/2-α j| ≤ 1/8192) (hb : ∀ j, |1/2-β j| ≤ 1/8192)
    (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier (criticalPhaseTailCarrier α hia 0 0) T)
    (hFT : AtomicOnCarrier (criticalPhaseTailCarrier β hib 0 0) (𝓕 T)) :
    lp (fun _ : (ℕ×Bool)×(ℕ×Bool) => ℂ) 2 :=
  ⟨fun z => halfNewtonFourierMoment (fun l => 1/2-α l) (fun l => 1/2-β l) T z.1.1 z.1.2 z.2.1 z.2.2,
    memℓp_gen (by simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
      summable_sq_halfNewtonFourierMatrix_actual α β hia hib ha hb T hT hFT)⟩

/-- Every complete Fourier-array entry is the actual whole-source reading. -/
theorem actualConstantFourierArray_apply (α β : ℕ+ → ℝ)
    (hia : ∀ j, 0 < α j ∧ α j < 1/2) (hib : ∀ j, 0 < β j ∧ β j < 1/2)
    (ha : ∀ j, |1/2-α j| ≤ 1/8192) (hb : ∀ j, |1/2-β j| ≤ 1/8192)
    (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier (criticalPhaseTailCarrier α hia 0 0) T)
    (hFT : AtomicOnCarrier (criticalPhaseTailCarrier β hib 0 0) (𝓕 T))
    (z : (ℕ×Bool)×(ℕ×Bool)) :
    actualConstantFourierArray α β hia hib ha hb T hT hFT z=
      halfNewtonFourierMoment (fun l => 1/2-α l) (fun l => 1/2-β l) T z.1.1 z.1.2 z.2.1 z.2.2 := rfl

/-- The actual complete Fourier lp array retains the opposite triangular flag. -/
theorem actualConstantFourierArray_lower_flag (α β : ℕ+ → ℝ)
    (hia : ∀ j, 0 < α j ∧ α j < 1/2) (hib : ∀ j, 0 < β j ∧ β j < 1/2)
    (ha : ∀ j, |1/2-α j| ≤ 1/8192) (hb : ∀ j, |1/2-β j| ≤ 1/8192)
    (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier (criticalPhaseTailCarrier α hia 0 0) T)
    (hFT : AtomicOnCarrier (criticalPhaseTailCarrier β hib 0 0) (𝓕 T))
    (i j : ℕ) (e f : Bool) (hij : i < j) :
    actualConstantFourierArray α β hia hib ha hb T hT hFT ((i,e),(j,f))=0 := by
  exact halfNewtonFourierMoment_lower_flag α β hia hib
    (fun l => by have hh := (abs_le.mp (ha l)).2; linarith) T hT hFT i j e f hij

/-- Both exact Fourier diagonal constraints hold on the genuine complete lp vector. -/
theorem actualConstantFourierArray_diagonal (α β : ℕ+ → ℝ)
    (hia : ∀ j, 0 < α j ∧ α j < 1/2) (hib : ∀ j, 0 < β j ∧ β j < 1/2)
    (ha : ∀ j, |1/2-α j| ≤ 1/8192) (hb : ∀ j, |1/2-β j| ≤ 1/8192)
    (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier (criticalPhaseTailCarrier α hia 0 0) T)
    (hFT : AtomicOnCarrier (criticalPhaseTailCarrier β hib 0 0) (𝓕 T))
    (i : ℕ) :
    let B := actualConstantFourierArray α β hia hib ha hb T hT hFT
    B ((i,false),(i,true))=-Complex.I*(Real.tan (Real.pi*(1/2-β ⟨i+1,Nat.succ_pos i⟩)):ℂ)*B ((i,true),(i,false)) ∧
    B ((i,true),(i,true))=(Complex.I*(Real.tan (Real.pi*(1/2-β ⟨i+1,Nat.succ_pos i⟩)):ℂ)/(1/4096:ℂ))*B ((i,false),(i,false)) := by
  exact halfNewtonFourierMoment_diagonal_relations α β hia hib
    (fun l => by have hh := (abs_le.mp (ha l)).2; linarith) T hT hFT i

/-- The complete Fourier lp vector is entrywise the full actual analytic gauge
of the original source. This is a convergent whole-source identity, not a formal polynomial. -/
theorem actualConstantFourierArray_gauge (α β : ℕ+ → ℝ)
    (hia : ∀ j, 0 < α j ∧ α j < 1/2) (hib : ∀ j, 0 < β j ∧ β j < 1/2)
    (ha : ∀ j, |1/2-α j| ≤ 1/8192) (hb : ∀ j, |1/2-β j| ≤ 1/8192)
    (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier (criticalPhaseTailCarrier α hia 0 0) T)
    (hFT : AtomicOnCarrier (criticalPhaseTailCarrier β hib 0 0) (𝓕 T))
    (i j : ℕ) (e f : Bool) :
    actualConstantFourierArray α β hia hib ha hb T hT hFT ((i,e),(j,f))=
    (((1/4096 : ℂ)^(i+j)*(1/64 : ℂ)^(e.toNat+f.toNat))⁻¹)*
      halfNewtonGaugeBilinear (halfWeylDistributionCLM T)
        (halfNewtonTest (fun l => 1/2-α l) i e) (halfNewtonTest (fun l => 1/2-β l) j f) := by
  exact (halfNewtonGaugeMoment_eq_FourierMoment α β hia hib
    (fun l => by have hh := (abs_le.mp (ha l)).2; linarith)
    (fun l => by have hh := (abs_le.mp (hb l)).2; linarith) T hT hFT i j e f).symm

end
end MeyerGeneralProblem.Adaptive
