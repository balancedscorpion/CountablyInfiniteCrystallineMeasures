module

public import MeyerGeneralProblem.Cardinal.Adaptive.PrefixInterfaces
public import MeyerGeneralProblem.Cardinal.Adaptive.FiniteSmoothPartition

@[expose] public section

/-! # Explicit head gaps and deterministic finite-prefix partition radii -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section

/-- Every actual positive phase stays at least one quarter head-spacing from zero. -/
theorem blockPhase_head_gap {P R : ℕ} (hP : 1 ≤ P) (hR : 1 ≤ R) (j : ℕ+) :
    1/(4*(headLength R:ℝ)) ≤ blockPhase P R j := by
  have hk : (1:ℝ) ≤ headLength R := by exact_mod_cast headLength_pos hR
  have hden : 0 < 4*(headLength R:ℝ) := by positivity
  unfold blockPhase
  split_ifs with hj
  · apply (div_le_div_iff_of_pos_right hden).mpr
    have hj' : (1:ℝ) ≤ (j:ℕ) := by exact_mod_cast j.pos
    linarith
  · have ht := (rapidDistance_bounds hP hR ((j:ℕ)-headLength R)).2
    have hquarter : 1/(4*(headLength R:ℝ)) ≤ 1/4 := by
      apply (div_le_div_iff₀ hden (by norm_num : (0:ℝ)<4)).mpr
      linarith
    linarith

/-- The entire actual periodic phase closure, including its seams, misses an
explicit interval around zero whose width depends only on the finite head. -/
theorem periodicPhaseSet_head_gap {P R : ℕ} (hP : 1 ≤ P) (hR : 1 ≤ R)
    {x : ℝ} (hx : x ∈ periodicPhaseSet P R) :
    1/(4*(headLength R:ℝ)) ≤ |x| := by
  obtain ⟨n,β,hβ,rfl⟩ := hx
  have hk : (1:ℝ) ≤ headLength R := by exact_mod_cast headLength_pos hR
  have hsmall : 1/(4*(headLength R:ℝ)) ≤ 1/2 := by
    apply (div_le_div_iff₀ (by positivity) (by norm_num : (0:ℝ)<2)).mpr
    linarith
  have hb : 1/(4*(headLength R:ℝ)) ≤ |β| ∧ |β| ≤ 1/2 := by
    rcases hβ with hβ|rfl
    · obtain ⟨j,positive,rfl⟩ := hβ
      have hj := blockPhase_head_gap hP hR j
      have hj' := blockPhase_mem_Ioo hP hR j
      cases positive <;> simp only [signedPhase, Bool.false_eq_true, ite_false,
        ite_true, abs_neg, abs_of_pos hj'.1] <;> exact ⟨hj,hj'.2.le⟩
    · simpa only [abs_of_pos (by norm_num : (0:ℝ)<1/2)] using ⟨hsmall,le_rfl⟩
  by_cases hn : n=0
  · simpa only [hn, Int.cast_zero, zero_add] using hb.1
  · have hn' : (1:ℝ) ≤ |(n:ℝ)| := by
      exact_mod_cast (show (1:ℤ) ≤ |n| by have := abs_pos.mpr hn; omega)
    have htri := abs_add_le ((n:ℝ)+β) (-β)
    have he : ((n:ℝ)+β)+(-β) = n := by ring
    rw [he, abs_neg] at htri
    linarith

/-- Physical reciprocal scaling preserves an explicit half-sized head gap. -/
theorem physicalPeriodicSet_head_gap (R : ℕ+ → ℕ) (s : ℕ+ → ℝ)
    (hR : ∀ i, 1 ≤ R i) (hs : ∀ i, s i ∈ Set.Icc 1 2) (b : Label)
    {x : ℝ} (hx : x ∈ physicalPeriodicSet R s b) :
    1/(8*(headLength (R b.1):ℝ)) ≤ |x| := by
  obtain ⟨y,hy,rfl⟩ := hx
  have hg := periodicPhaseSet_head_gap b.1.pos (hR b.1) hy
  have ht := labelScale_mem_Icc s hs b
  have hp : 0 < labelScale s b := lt_of_lt_of_le (by norm_num) ht.1
  have hi : (1/2:ℝ) ≤ (labelScale s b)⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ hp]
    linarith [ht.2]
  rw [abs_mul, abs_of_pos (inv_pos.mpr hp)]
  calc
    1/(8*(headLength (R b.1):ℝ)) = (1/2)*(1/(4*(headLength (R b.1):ℝ))) := by ring
    _ ≤ (labelScale s b)⁻¹ * |y| := mul_le_mul hi hg (by positivity) (by positivity)

/-- One fixed small piece radius, determined by the stage, previous gaps and
closure separation only; every head contributes before any scale realization. -/
def prefixPieceRadius (M : ℕ+) (gaps : GapPrefix M.val) (γ : ℝ) : ℝ :=
  min (γ/2) (min (1/(M.val:ℝ)) (1/(100*(1+∑ i, (headLength (gaps i):ℝ)))))

/-- The explicit prefix radius has all source caps and is strictly below every
head-gap threshold as well as the closure separation. -/
theorem prefixPieceRadius_spec (M : ℕ+) (gaps : GapPrefix M.val)
    (hgaps : ∀ i, 1 ≤ gaps i) (γ : ℝ) (hγ : 0 < γ) :
    0 < prefixPieceRadius M gaps γ ∧ prefixPieceRadius M gaps γ < γ ∧
      prefixPieceRadius M gaps γ ≤ 1/(M.val:ℝ) ∧
      ∀ i, prefixPieceRadius M gaps γ < 1/(100*(headLength (gaps i):ℝ)) := by
  classical
  have hs : 0 ≤ ∑ i : Fin M.val, (headLength (gaps i):ℝ) :=
    Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have hM : (0:ℝ)<M.val := by exact_mod_cast M.pos
  have hpos : 0 < prefixPieceRadius M gaps γ := by unfold prefixPieceRadius; positivity
  refine ⟨hpos,?_,?_,?_⟩
  · exact (min_le_left _ _).trans_lt (by linarith)
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · intro i
    have hi : (0:ℝ)<headLength (gaps i) := by exact_mod_cast headLength_pos (hgaps i)
    have his : (headLength (gaps i):ℝ) ≤ ∑ j : Fin M.val, (headLength (gaps j):ℝ) :=
      Finset.single_le_sum (f := fun j : Fin M.val => (headLength (gaps j):ℝ))
        (fun _ _ => Nat.cast_nonneg _) (Finset.mem_univ i)
    apply ((min_le_right _ _).trans (min_le_right _ _)).trans_lt
    apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith

end
end MeyerGeneralProblem.Adaptive
