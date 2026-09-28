module

public import MeyerGeneralProblem.Cardinal.Adaptive.ActualStageSelection

@[expose] public section

/-! # A deterministic gap sequence from the actual analytic stage choices -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section

/-- The actual next gap. The unused nonpositive-prefix branch keeps the recursion
total without supplying an analytic certificate for an invalid prefix. -/
def actualNextGap (ψ : SchwartzMap ℝ ℂ) (n : ℕ) (gaps : GapPrefix (n+1)) : ℕ :=
  if h : ∀ i, 1 ≤ gaps i then
    (actualStepSelection ψ ⟨n+1,Nat.succ_pos _⟩ gaps h).nextGapLowerBound (gaps (Fin.last n))
  else 2^(n+2)

/-- The exponential floor holds even on unused prefixes. -/
theorem actualNextGap_exponential (ψ : SchwartzMap ℝ ℂ) (n : ℕ) (gaps : GapPrefix (n+1)) :
    2^(n+2) ≤ actualNextGap ψ n gaps := by
  unfold actualNextGap
  split_ifs with h
  · exact ((actualStepSelection ψ ⟨n+1,Nat.succ_pos _⟩ gaps h).nextGapLowerBound_spec
      (gaps (Fin.last n)) _ le_rfl).1
  · exact le_rfl

/-- All stage choices are made before any scale tuple, native order or source. -/
def actualGaps (ψ : SchwartzMap ℝ ℂ) : ℕ → ℕ := recursiveGaps (actualNextGap ψ)

/-- Exact recursion through the chosen finite prefix. -/
theorem actualGaps_succ (ψ : SchwartzMap ℝ ℂ) (n : ℕ) :
    actualGaps ψ (n+1) = actualNextGap ψ n (fun i => actualGaps ψ i) :=
  recursiveGaps_succ _ _

/-- Exponential escape for every actual gap. -/
theorem actualGaps_exponential (ψ : SchwartzMap ℝ ℂ) (n : ℕ) :
    2^(n+1) ≤ actualGaps ψ n := by
  cases n with
  | zero => simp [actualGaps]
  | succ n => rw [actualGaps_succ]; exact actualNextGap_exponential _ _ _

/-- Every recursively selected gap is positive. -/
theorem actualGaps_pos (ψ : SchwartzMap ℝ ℂ) (n : ℕ) : 1 ≤ actualGaps ψ n :=
  (one_le_pow₀ (by norm_num : (1:ℕ) ≤ 2)).trans (actualGaps_exponential ψ n)

/-- The deterministic completed gap sequence on the source's positive labels. -/
def actualPositiveGaps (ψ : SchwartzMap ℝ ℂ) (i : ℕ+) : ℕ := actualGaps ψ (i.val-1)

/-- Positive-label indexing agrees exactly with the finite-prefix coordinates. -/
theorem actualPositiveGaps_prefix (ψ : SchwartzMap ℝ ℂ) {M : ℕ} (i : Fin M) :
    actualPositiveGaps ψ (prefixScaleIndex i) = actualGaps ψ i.val := by
  change actualGaps ψ (i.val+1-1) = actualGaps ψ i.val
  rw [Nat.add_sub_cancel]

/-- The completed positive sequence has the exact exponential escape demanded by G05. -/
theorem actualPositiveGaps_exponential (ψ : SchwartzMap ℝ ℂ) (i : ℕ+) :
    2^i.val ≤ actualPositiveGaps ψ i := by
  have h := actualGaps_exponential ψ (i.val-1)
  have hi : i.val-1+1=i.val := by have := i.pos; omega
  simpa only [actualPositiveGaps,hi] using h

/-- The completed positive sequence has no zero gaps. -/
theorem actualPositiveGaps_pos (ψ : SchwartzMap ℝ ℂ) (i : ℕ+) :
    1 ≤ actualPositiveGaps ψ i := actualGaps_pos ψ _

/-- The actual constants at positive stage n+1, taken from precisely its already
chosen initial segment. -/
def actualStage (ψ : SchwartzMap ℝ ℂ) (n : ℕ) :
    StepConstants ⟨n+1,Nat.succ_pos _⟩ (fun i => actualGaps ψ i.val) :=
  actualStepSelection ψ _ _ (fun i => actualGaps_pos ψ i.val)

/-- The constructed sequence inherits the actual analytic stage laws. -/
theorem actualStage_laws (ψ : SchwartzMap ℝ ℂ) (n : ℕ) :
    ActualStepLaws ψ ⟨n+1,Nat.succ_pos _⟩ (fun i => actualGaps ψ i.val)
      (fun i => actualGaps_pos ψ i.val) (actualStage ψ n) :=
  actualStepSelection_laws _ _ _ _

/-- The next integer pays all fixed geometric demands and contains the common
spatial cutoff. No later choice changes the preceding analytic estimates. -/
theorem actualGaps_step (ψ : SchwartzMap ℝ ℂ) (n : ℕ) :
    2^(n+2) ≤ actualGaps ψ (n+1) ∧ 2*actualGaps ψ n ≤ actualGaps ψ (n+1) ∧
      6*((actualStage ψ n).translationBound+(n+1:ℝ)+2) ≤ (actualGaps ψ (n+1):ℝ) ∧
      6*((actualStage ψ n).spatialCutoff+1) ≤ actualGaps ψ (n+1) := by
  have hp : ∀ i : Fin (n+1), 1 ≤ actualGaps ψ i.val := fun i => actualGaps_pos ψ i.val
  have he : actualGaps ψ (n+1) = (actualStage ψ n).nextGapLowerBound (actualGaps ψ n) := by
    rw [actualGaps_succ,actualNextGap,dite_eq_left hp]
    rfl
  rw [he]
  simpa only [PNat.mk_coe,Nat.cast_add,Nat.cast_one,Nat.add_assoc] using
    (actualStage ψ n).nextGapLowerBound_spec (actualGaps ψ n) _ le_rfl

end
end MeyerGeneralProblem.Adaptive
