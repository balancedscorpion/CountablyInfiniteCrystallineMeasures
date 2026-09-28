module

public import MeyerGeneralProblem.Cardinal.Adaptive.HalfNewtonDiagonal

@[expose] public section

/-! # Actual Fourier companion of the complete half-seam Newton source -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open scoped FourierTransform

/-- Reflection preserves every full critical tail with its original thresholds. -/
theorem criticalPhaseTailSet_neg_mem (α : ℕ+ → ℝ) (k d : ℕ) {x : ℝ}
    (hx : x ∈ criticalPhaseTailSet α k d) : -x ∈ criticalPhaseTailSet α k d := by
  obtain ⟨j,u,n,hn,rfl⟩ := hx
  refine ⟨j,!u,-n,by simpa only [Int.natAbs_neg] using hn,?_⟩
  cases u <;> simp only [signedPhase,Bool.not_false,Bool.not_true,ite_true,Bool.false_eq_true,ite_false,Int.cast_neg] <;> ring

/-- The true square Fourier transform retains the complete original critical
carrier through actual reflection, not a supplied second support record. -/
theorem criticalPhaseTail_atomic_fourier_sq (α : ℕ+ → ℝ)
    (hia : ∀ j, 0 < α j ∧ α j < 1/2) (k d : ℕ) (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier (criticalPhaseTailCarrier α hia k d) T) :
    AtomicOnCarrier (criticalPhaseTailCarrier α hia k d) (𝓕 (𝓕 T)) := by
  intro f hf
  rw [fourier_sq_eq_reflection,temperedReflectionCLM_apply]
  apply hT
  intro x hx
  rw [schwartzReflectionCLM_apply]
  exact hf _ (criticalPhaseTailSet_neg_mem α k d hx)

private theorem character_add_right (a x y : ℝ) :
    combModulationCharacter a (x+y)=combModulationCharacter a x*combModulationCharacter a y := by
  simp only [combModulationCharacter_eq_exp]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem half_character_quarter : combModulationCharacter (1/2) (1/2)=Complex.I := by
  rw [combModulationCharacter_eq_exp,
    show 2*(Real.pi : ℂ)*Complex.I*((1/2 : ℝ) : ℂ)*((1/2 : ℝ) : ℂ)=((Real.pi/2 : ℝ) : ℂ)*Complex.I by push_cast; ring,
    Complex.exp_mul_I]
  simp

/-- Exact Fourier half-Weyl conjugation, including the imaginary scalar forced
by the two half shifts. -/
theorem halfWeyl_fourier_conjugation (T : TemperedDistribution ℝ ℂ) :
    combDistributionModulation (-1) (𝓕 (halfWeylDistributionCLM T))=
      Complex.I •halfWeylDistributionCLM (𝓕 T) := by
  rw [fourier_halfWeylDistribution]
  ext f
  change (𝓕 T) (combSchwartzModulation (1/2)
    (combSchwartzTranslation (-1/2) (combSchwartzModulation (-1) f)))=
      Complex.I*(𝓕 T) (combSchwartzTranslation (-1/2) (combSchwartzModulation (-1/2) f))
  rw [← smul_eq_mul,← map_smul]
  congr 1
  ext x
  simp only [combSchwartzModulation_apply,combSchwartzTranslation_apply,_root_.smul_apply,smul_eq_mul]
  have he : combModulationCharacter (1/2) x=
      combModulationCharacter (1/2) (-1/2+x)*Complex.I := by
    calc
      _ = combModulationCharacter (1/2) ((-1/2+x)+1/2) := by congr 1; ring
      _ = _ := by rw [character_add_right,half_character_quarter]
  rw [he]
  have hm := combModulationCharacter_add_left (1/2) (-1) (-1/2+x)
  rw [show (1/2 : ℝ)+(-1)=(-1/2) by ring] at hm
  rw [show (combModulationCharacter (1/2) (-1/2+x)*Complex.I)*
      (combModulationCharacter (-1) (-1/2+x)*f (-1/2+x))=
      Complex.I*(combModulationCharacter (1/2) (-1/2+x)*combModulationCharacter (-1) (-1/2+x))*f (-1/2+x) by ring,
    ← hm]
  ring

/-- The actual Fourier companion used in the rotated Newton family. -/
def halfWeylFourierCompanion (T : TemperedDistribution ℝ ℂ) : TemperedDistribution ℝ ℂ :=
  combDistributionModulation (-1) (𝓕 (halfWeylDistributionCLM T))

/-- Both full companion records are derived from the original paired source,
with the phase sequences exchanged and no additional support premise. -/
theorem halfWeylFourierCompanion_atomic_records (α β : ℕ+ → ℝ)
    (hia : ∀ j, 0 < α j ∧ α j < 1/2) (hib : ∀ j, 0 < β j ∧ β j < 1/2)
    (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier (criticalPhaseTailCarrier α hia 0 0) T)
    (hFT : AtomicOnCarrier (criticalPhaseTailCarrier β hib 0 0) (𝓕 T)) :
    AtomicOnCarrier ((criticalPhaseTailCarrier β hib 0 0).translate (-1/2)) (halfWeylFourierCompanion T) ∧
    AtomicOnCarrier ((criticalPhaseTailCarrier α hia 0 0).translate (-1/2)) (𝓕 (halfWeylFourierCompanion T)) := by
  have hw := halfWeylDistribution_atomic_records β α hib hia (𝓕 T) hFT
    (criticalPhaseTail_atomic_fourier_sq α hia 0 0 T hT)
  unfold halfWeylFourierCompanion
  rw [halfWeyl_fourier_conjugation,FourierTransform.fourier_smul]
  constructor
  · intro f hf
    simp only [_root_.smul_apply,hw.1 f hf,smul_zero]
  · intro f hf
    simp only [_root_.smul_apply,hw.2 f hf,smul_zero]

/-- The exact reflection sign of the two source parities. -/
def halfNewtonParitySign (e : Bool) : ℂ := if e then -1 else 1

/-- The actual compact Newton test reflects with its prescribed parity sign. -/
theorem halfNewtonTest_reflection (ε : ℕ+ → ℝ) (i : ℕ) (e : Bool) :
    schwartzReflectionCLM (halfNewtonTest ε i e)=halfNewtonParitySign e •halfNewtonTest ε i e := by
  have hc (x : ℝ) : zakCentralCutoff (-x)=zakCentralCutoff x := by
    change (zakCentralBump (-x) : ℂ)=(zakCentralBump x : ℂ)
    rw [zakCentralBump.neg]
  have hp (x : ℝ) : halfNewtonProduct ε i (-x)=halfNewtonProduct ε i x := by
    simp only [halfNewtonProduct,criticalNewtonNode,mul_neg,Real.cos_neg]
  ext x
  simp only [schwartzReflectionCLM_apply,halfNewtonTest_apply,_root_.smul_apply,smul_eq_mul,
    halfNewtonFunction,hc,hp,mul_neg,Real.sin_neg,Real.cos_neg,Complex.ofReal_neg]
  cases e <;> simp only [halfNewtonParitySign,ite_true,Bool.false_eq_true,ite_false] <;> ring

/-- The whole rotated Fourier companion family. Its identification with the
full analytic gauge is a separate theorem, not part of this definition. -/
def halfNewtonFourierBilinear (T : TemperedDistribution ℝ ℂ) (f g : SchwartzMap ℝ ℂ) : ℂ :=
  halfNewtonBilinear (halfWeylFourierCompanion T) g (schwartzReflectionCLM f)

/-- Fixed-normalized moments of the genuine rotated Fourier companion. -/
def halfNewtonFourierMoment (ε δ : ℕ+ → ℝ) (T : TemperedDistribution ℝ ℂ)
    (i : ℕ) (e : Bool) (j : ℕ) (f : Bool) : ℂ :=
  (((1/4096 : ℂ)^(i+j)*(1/64 : ℂ)^(e.toNat+f.toNat))⁻¹)*
    halfNewtonFourierBilinear T (halfNewtonTest ε i e) (halfNewtonTest δ j f)

/-- Exact reflection and transposition of the entire actual Fourier moment
array, retaining both parity signs and the symmetric fixed normalization. -/
theorem halfNewtonFourierMoment_eq_transposed (ε δ : ℕ+ → ℝ)
    (T : TemperedDistribution ℝ ℂ) (i : ℕ) (e : Bool) (j : ℕ) (f : Bool) :
    halfNewtonFourierMoment ε δ T i e j f=
      halfNewtonParitySign e*halfNewtonMoment δ ε (halfWeylFourierCompanion T) j f i e := by
  unfold halfNewtonFourierMoment halfNewtonFourierBilinear halfNewtonMoment halfNewtonCoordinate halfNewtonBilinear
  rw [halfNewtonTest_reflection,map_smul,zakTensorAction_smul_right]
  rw [Nat.add_comm i j,Nat.add_comm e.toNat f.toNat]
  ring

/-- The actual rotated Fourier moments satisfy the opposite complete
triangular flag, derived from the original source's two atomic records. -/
theorem halfNewtonFourierMoment_lower_flag (α β : ℕ+ → ℝ)
    (hia : ∀ j, 0 < α j ∧ α j < 1/2) (hib : ∀ j, 0 < β j ∧ β j < 1/2)
    (hsmall : ∀ j, 1/4 ≤ α j) (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier (criticalPhaseTailCarrier α hia 0 0) T)
    (hFT : AtomicOnCarrier (criticalPhaseTailCarrier β hib 0 0) (𝓕 T))
    (i j : ℕ) (e f : Bool) (hij : i < j) :
    halfNewtonFourierMoment (fun l => 1/2-α l) (fun l => 1/2-β l) T i e j f=0 := by
  obtain ⟨hp,hq⟩ := halfWeylFourierCompanion_atomic_records α β hia hib T hT hFT
  rw [halfNewtonFourierMoment_eq_transposed,
    halfNewtonMoment_upper_flag β α hib hia hsmall (halfWeylFourierCompanion T) hp hq j i f e hij,mul_zero]

/-- The actual Fourier companion has exactly the reversed imaginary diagonal
signs. No equality to an analytic gauge is assumed to obtain these equations. -/
theorem halfNewtonFourierMoment_diagonal_relations (α β : ℕ+ → ℝ)
    (hia : ∀ j, 0 < α j ∧ α j < 1/2) (hib : ∀ j, 0 < β j ∧ β j < 1/2)
    (hsmall : ∀ j, 1/4 ≤ α j) (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier (criticalPhaseTailCarrier α hia 0 0) T)
    (hFT : AtomicOnCarrier (criticalPhaseTailCarrier β hib 0 0) (𝓕 T))
    (i : ℕ) :
    halfNewtonFourierMoment (fun l => 1/2-α l) (fun l => 1/2-β l) T i false i true=
      -Complex.I*(Real.tan (Real.pi*(1/2-β ⟨i+1,Nat.succ_pos i⟩)) : ℂ)*
        halfNewtonFourierMoment (fun l => 1/2-α l) (fun l => 1/2-β l) T i true i false ∧
    halfNewtonFourierMoment (fun l => 1/2-α l) (fun l => 1/2-β l) T i true i true=
      (Complex.I*(Real.tan (Real.pi*(1/2-β ⟨i+1,Nat.succ_pos i⟩)) : ℂ)/(1/4096 : ℂ))*
        halfNewtonFourierMoment (fun l => 1/2-α l) (fun l => 1/2-β l) T i false i false := by
  obtain ⟨hp,hq⟩ := halfWeylFourierCompanion_atomic_records α β hia hib T hT hFT
  obtain ⟨hc,hd⟩ := halfNewtonMoment_diagonal_relations β α hib hia hsmall
    (halfWeylFourierCompanion T) hp hq i
  simp only [halfNewtonFourierMoment_eq_transposed,halfNewtonParitySign,
    ite_true,Bool.false_eq_true,ite_false,one_mul,neg_one_mul]
  rw [hc,hd]
  constructor <;> ring

/-- Integer source modulation transfers exactly to the physical test of the
whole Zak family, with no extra coefficient or frequency shift. -/
theorem zakTensorAction_integer_source_modulation (T : TemperedDistribution ℝ ℂ)
    (f g : SchwartzMap ℝ ℂ) (m : ℤ) :
    zakTensorAction (combDistributionModulation (m : ℝ) T) f g=
      zakTensorAction T (combSchwartzModulation (m : ℝ) f) g := by
  unfold zakTensorAction
  apply tsum_congr
  intro n
  congr 1
  rw [combDistributionModulation_apply]
  congr 1
  ext x
  simp only [combSchwartzModulation_apply,combSchwartzTranslation_apply]
  have he : combModulationCharacter (m : ℝ) (-(n : ℝ)+x)=combModulationCharacter (m : ℝ) x := by
    convert combModulationCharacter_int_translate m (-n) x using 1
    congr 1
    push_cast
    ring
  rw [he]

/-- The rotated companion pairing is exactly the reflected whole Fourier Zak
action to which the literal two-variable gauge identity must be compared. -/
theorem halfNewtonFourierBilinear_eq_fourier_Zak (T : TemperedDistribution ℝ ℂ)
    (f g : SchwartzMap ℝ ℂ) :
    halfNewtonFourierBilinear T f g=
      zakTensorAction (𝓕 (halfWeylDistributionCLM T)) (combSchwartzModulation (-1/2) g)
        (combSchwartzModulation (-1/2) (schwartzReflectionCLM f)) := by
  unfold halfNewtonFourierBilinear halfNewtonBilinear halfWeylFourierCompanion
  rw [show (-1 : ℝ)=((-1 : ℤ) : ℝ) by norm_num,zakTensorAction_integer_source_modulation]
  congr 1
  ext x
  simp only [combSchwartzModulation_apply]
  rw [← mul_assoc,← combModulationCharacter_add_left]
  congr 2
  norm_num

end
end MeyerGeneralProblem.Adaptive
