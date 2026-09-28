module

public import MeyerGeneralProblem.Cardinal.Adaptive.VariableFullKernel
public import MeyerGeneralProblem.Cardinal.Adaptive.HalfNewtonMultiplierRecurrences

@[expose] public section

/-! Exact variable-weight normalization of the actual compact Newton readings. -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section

/-- Every actual positive phase sequence has strictly positive finite Newton weights. -/
theorem shrinkingNewtonWeight_strictly_pos (ε : ℕ → ℝ) (hε : ∀ i, 0 < ε i) (i : ℕ) :
    0 < shrinkingNewtonWeight ε i := Finset.prod_pos (fun j _ => hε (j+1))

/-- The original finite product adds exactly the next-level phase weight. -/
theorem shrinkingNewtonWeight_succ (ε : ℕ → ℝ) (i : ℕ) :
    shrinkingNewtonWeight ε (i+1)=shrinkingNewtonWeight ε i*ε (i+1) :=
  Finset.prod_range_succ _ _

/-- The complete variable normalization at an arbitrary nonzero parity scale. -/
def variableNewtonNormalization (κ : ℝ) (ε δ : ℕ → ℝ) (i : ℕ) (e : Bool) (j : ℕ) (f : Bool) : ℂ :=
  (((κ:ℂ)^(e.toNat+f.toNat))*((shrinkingNewtonWeight ε i*shrinkingNewtonWeight δ j:ℝ):ℂ))⁻¹

/-- The normalized whole source reading is exactly the original finite-product normalization. -/
theorem shrinkingNewtonMomentWithScale_normalization (κ : ℝ) (ε δ : ℕ → ℝ)
    (T : TemperedDistribution ℝ ℂ) (i : ℕ) (e : Bool) (j : ℕ) (f : Bool) :
    shrinkingNewtonMomentWithScale κ ε δ T i e j f=
      variableNewtonNormalization κ ε δ i e j f * halfNewtonCoordinate (fun l => ε l) (fun l => δ l) T i e j f := by
  unfold shrinkingNewtonMomentWithScale shrinkingNewtonCoordinate variableNewtonNormalization
  rw [mul_inv_rev,div_eq_mul_inv]
  ring

/-- The full analytically gauged reading uses exactly the same variable normalization. -/
theorem shrinkingNewtonGaugeMomentWithScale_normalization (κ : ℝ) (ε δ : ℕ → ℝ)
    (T : TemperedDistribution ℝ ℂ) (i : ℕ) (e : Bool) (j : ℕ) (f : Bool) :
    shrinkingNewtonGaugeMomentWithScale κ ε δ T i e j f=
      variableNewtonNormalization κ ε δ i e j f * halfNewtonGaugeBilinear T
        (halfNewtonTest (fun l => ε l) i e) (halfNewtonTest (fun l => δ l) j f) := by
  unfold shrinkingNewtonGaugeMomentWithScale shrinkingNewtonGaugeCoordinate variableNewtonNormalization
  rw [mul_inv_rev,div_eq_mul_inv]
  ring

/-- Row succession uses precisely epsilon at i+1. -/
theorem variableNewtonNormalization_row_succ (κ : ℝ) (ε δ : ℕ → ℝ)
    (hε : ∀ i, 0 < ε i) (i j : ℕ) (e f : Bool) :
    variableNewtonNormalization κ ε δ i e j f=
      (ε (i+1):ℂ)*variableNewtonNormalization κ ε δ (i+1) e j f := by
  unfold variableNewtonNormalization
  rw [shrinkingNewtonWeight_succ]
  push_cast
  have he : (ε (i+1):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (hε _))
  field_simp

/-- The physical even normalization differs from the odd one by exactly kappa. -/
theorem variableNewtonNormalization_row_even (κ : ℝ) (hκ : κ ≠ 0) (ε δ : ℕ → ℝ)
    (i j : ℕ) (f : Bool) :
    variableNewtonNormalization κ ε δ i false j f=
      (κ:ℂ)*variableNewtonNormalization κ ε δ i true j f := by
  unfold variableNewtonNormalization
  have hc : (κ:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hκ
  cases f <;> simp only [Bool.toNat_false,Bool.toNat_true,zero_add,add_zero,one_add_one_eq_two,pow_zero,pow_one,one_mul]
  all_goals field_simp

/-- Variable sine multiplication acts on arbitrary actual continuous slices
through the exact finite Newton recurrence. -/
theorem variableSineRow_slice_action (κ : ℝ) (hκ : κ ≠ 0) (ε δ : ℕ → ℝ) (ρ : ℝ)
    (hρ : ρ ≤ 1/2) (hε : ∀ i, 0 < ε i ∧ ε i ≤ ρ)
    (U : ℕ → Bool → TemperedDistribution ℝ ℂ) (u : SeamMomentArray)
    (hu : ∀ i e j f, u ((i,e),(j,f))=variableNewtonNormalization κ ε δ i e j f*
      U j f (halfNewtonTest (fun l => ε l) i e)) (i j : ℕ) (e f : Bool) :
    variableSineRow κ ε ρ hρ hε u ((i,e),(j,f))=
      variableNewtonNormalization κ ε δ i e j f * U j f (halfNewtonSineTest (fun l => ε l) i e) := by
  rw [variableSineRow_apply]
  cases e
  · simp only [Bool.false_eq_true,ite_false,hu,halfNewtonSineTest,map_sub,map_smul,smul_eq_mul]
    rw [variableNewtonNormalization_row_even κ hκ,variableNewtonNormalization_row_succ κ ε δ
      (fun n => (hε n).1) i j true f]
    simp only [PNat.mk_coe]
    ring
  · simp only [ite_true,hu,halfNewtonSineTest,halfNewtonNodeTest,map_add,map_smul,smul_eq_mul]
    rw [variableNewtonNormalization_row_even κ hκ,variableNewtonNormalization_row_even κ hκ]
    rw [variableNewtonNormalization_row_succ κ ε δ (fun n => (hε n).1) i j true f]
    have hc : (κ:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hκ
    simp only [PNat.mk_coe]
    field_simp <;> ring

/-- Exact axis exchange of the whole variable normalization. -/
theorem variableNewtonNormalization_swap (κ : ℝ) (ε δ : ℕ → ℝ) (i : ℕ) (e : Bool) (j : ℕ) (f : Bool) :
    variableNewtonNormalization κ ε δ i e j f=variableNewtonNormalization κ δ ε j f i e := by
  simp only [variableNewtonNormalization,add_comm,mul_comm]

end
end MeyerGeneralProblem.Adaptive
