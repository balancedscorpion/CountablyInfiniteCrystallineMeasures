module

public import MeyerGeneralProblem.Cardinal.Adaptive.CriticalCarrierRepair

@[expose] public section

/-! # Actual block phase order and complete native rank transport -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section

/-- Actual rapid distances strictly decrease with their natural index. -/
theorem rapidDistance_strictAnti {P R : ℕ} (hP : 1 ≤ P) (hR : 1 ≤ R) :
    StrictAnti (rapidDistance P R) := by
  intro i j hij
  unfold rapidDistance
  apply mul_lt_mul_of_pos_left _ (by norm_num)
  apply Real.exp_lt_exp.mpr
  exact mul_lt_mul_of_neg_left ((pow_right_strictMono₀ (rapidBase_one_lt hP)) hij)
    (neg_lt_zero.mpr (rapidDecay_pos hP hR))

/-- The original exponential scale places every tail phase strictly above the
largest matched head phase, uniformly in the tail index. -/
theorem rapidDistance_lt_head_spacing {P R : ℕ} (hP : 1 ≤ P) (hR : 1 ≤ R) (i : ℕ) :
    rapidDistance P R i < 1 / (4*(headLength R : ℝ)) := by
  have hk : (0 : ℝ) < headLength R := by exact_mod_cast headLength_pos hR
  have hp : (1 : ℝ) ≤ P := by exact_mod_cast hP
  have hl : 0 < Real.log (rapidScale R) := Real.log_pos (rapidScale_one_lt hR)
  have hb : 1 ≤ rapidBase P ^ i := one_le_pow₀ (rapidBase_one_lt hP).le
  have hd : Real.log (rapidScale R) ≤ rapidDecay P R * rapidBase P ^ i := by
    have hd' : Real.log (rapidScale R) ≤ rapidDecay P R := by
      unfold rapidDecay
      nlinarith
    exact hd'.trans (le_mul_of_one_le_right (rapidDecay_pos hP hR).le hb)
  have he : Real.exp (-(rapidDecay P R)*rapidBase P ^ i) ≤ (rapidScale R)⁻¹ := by
    rw [← Real.exp_log (lt_trans zero_lt_one (rapidScale_one_lt hR)), ← Real.exp_neg]
    exact Real.exp_le_exp.mpr (by linarith)
  have hu : rapidDistance P R i ≤ (1/16)*(rapidScale R)⁻¹ :=
    mul_le_mul_of_nonneg_left he (by norm_num)
  apply hu.trans_lt
  unfold rapidScale
  change (1/16 : ℝ)/(2^64*(headLength R : ℝ)) < 1/(4*(headLength R : ℝ))
  apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
  norm_num
  linarith

/-- All actual block phases are strictly increasing, across the head/tail seam
as well as within each piece of the original schedule. -/
theorem blockPhase_strictMono {P R : ℕ} (hP : 1 ≤ P) (hR : 1 ≤ R) :
    StrictMono (blockPhase P R) := by
  intro i j hij
  have hijN : (i : ℕ) < (j : ℕ) := hij
  have hijR : (i : ℝ) < (j : ℝ) := by exact_mod_cast hijN
  have hk : (0 : ℝ) < headLength R := by exact_mod_cast headLength_pos hR
  unfold blockPhase
  split_ifs with hi hj hj
  · apply (div_lt_div_iff_of_pos_right (by positivity : (0 : ℝ)<4*headLength R)).mpr
    linarith
  · have hiR : (i : ℝ) ≤ headLength R := by exact_mod_cast hi
    have hd := rapidDistance_lt_head_spacing hP hR ((j : ℕ)-headLength R)
    have hh : (2*(i : ℝ)-1)/(4*(headLength R : ℝ)) ≤
        1/2-1/(4*(headLength R : ℝ)) := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ)<4*headLength R)).mpr
      field_simp
      nlinarith
    linarith
  · omega
  · have hd := rapidDistance_strictAnti hP hR (show (i : ℕ)-headLength R < (j : ℕ)-headLength R by omega)
    linarith

/-- The exact actual head and rapid tail have no phase coincidences. -/
theorem blockPhase_injective {P R : ℕ} (hP : 1 ≤ P) (hR : 1 ≤ R) :
    Function.Injective (blockPhase P R) := (blockPhase_strictMono hP hR).injective


/-- The actual native source of the complete centrally deleted rapid block. -/
def actualBlockNativeSource (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) (p : ℕ) :
    Submodule ℂ (TemperedDistribution ℝ ℂ) :=
  pairedAtomicSource (blockCarrier P R hP hR) (blockCarrier P R hP hR) ⊓
    originalNativeDistributionSpace p

/-- The zero-shift complete critical carrier agrees with the actual critical
block, with no change to the infinite phase tail or its cell thresholds. -/
theorem criticalPhaseTailCarrier_block_zero (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) :
    criticalPhaseTailCarrier (blockPhase P R) (blockPhase_mem_Ioo hP hR) 0 0 =
      criticalBlockCarrier P R hP hR := by
  apply LocallyFiniteCarrier.ext
  exact criticalPhaseTailSet_block_zero P R

/-- Concrete finite-hole exchange transports the complete zero-shift critical
source into the actual gapped block without losing an original native order. -/
def criticalBlockNativeSourceEquiv (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R)
    (p : ℕ) (hp : 1 ≤ p) :
    criticalOriginalNativeSource (blockPhase P R) (blockPhase P R)
      (blockPhase_mem_Ioo hP hR) (blockPhase_mem_Ioo hP hR) 0 p ≃ₗ[ℂ]
        actualBlockNativeSource P R hP hR p := by
  change ↥(pairedAtomicSource _ _ ⊓ originalNativeDistributionSpace p) ≃ₗ[ℂ] _
  rw [criticalPhaseTailCarrier_block_zero]
  exact concreteBlockNativeHoleExchange P R hP hR p hp

/-- Every actual reindexed critical tail injects into the gapped rapid block,
with a loss of exactly two original orders independent of the head length. -/
theorem criticalBlockTail_rank_le_actualBlock (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R)
    (k p : ℕ) :
    Module.rank ℂ (criticalOriginalNativeSource (blockPhase P R) (blockPhase P R)
      (blockPhase_mem_Ioo hP hR) (blockPhase_mem_Ioo hP hR) k p) ≤
        Module.rank ℂ (actualBlockNativeSource P R hP hR (p+2)) := by
  have h := criticalNativeSource_rank_le_all (blockPhase P R) (blockPhase P R)
    (blockPhase_injective hP hR) (blockPhase_mem_Ioo hP hR)
    (blockPhase_injective hP hR) (blockPhase_mem_Ioo hP hR) k p
  exact h.trans_eq (criticalBlockNativeSourceEquiv P R hP hR (p+2) (by omega)).rank_eq

/-- The exact original rapid-tail schedule after the matched head. -/
def rapidTailPhase (P R : ℕ) (j : ℕ+) : ℝ := 1/2-rapidDistance P R j

/-- Reindexing past the matched head yields the literal original rapid phases. -/
theorem criticalTailPhases_block_head (P R : ℕ) :
    criticalTailPhases (blockPhase P R) (headLength R) = rapidTailPhase P R := by
  funext j
  unfold criticalTailPhases blockPhase rapidTailPhase
  rw [ite_eq_right (by change ¬ headLength R+(j : ℕ) ≤ headLength R; have := j.pos; omega)]
  congr 2
  simp

/-- The native source at the full head depth is the complete original rapid
critical tail; this interface retains every infinite tail atom. -/
theorem criticalPhaseTailCarrier_block_head (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) :
    (criticalPhaseTailCarrier (blockPhase P R) (blockPhase_mem_Ioo hP hR) (headLength R) 0).carrier =
      {x | ∃ (j : ℕ+) (u : Bool) (n : ℤ), (j : ℕ) ≤ n.natAbs ∧
        x=(n : ℝ)+signedPhase u (rapidTailPhase P R j)} := by
  change criticalPhaseTailSet (blockPhase P R) (headLength R) 0 = _
  unfold criticalPhaseTailSet
  rw [criticalTailPhases_block_head]
  simp only [add_zero]

end
end MeyerGeneralProblem.Adaptive
