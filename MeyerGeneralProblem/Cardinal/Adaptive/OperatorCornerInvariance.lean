module

public import MeyerGeneralProblem.Cardinal.Adaptive.OperatorSeriesIntertwining
public import MeyerGeneralProblem.Cardinal.Adaptive.FullExponentialBounds

@[expose] public section

/-! # Complete series preserve invariant coordinate corners -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- The projected output depends only on the projected input, including its entire complement. -/
def OperatorCornerInvariant (P A : E →L[ℂ] E) : Prop := P*A=P*A*P

namespace OperatorCornerInvariant

theorem one (P : E →L[ℂ] E) (hP : P*P=P) : OperatorCornerInvariant P 1 := by
  simp only [OperatorCornerInvariant,mul_one,hP]

theorem add {P A B : E →L[ℂ] E} (hA : OperatorCornerInvariant P A)
    (hB : OperatorCornerInvariant P B) : OperatorCornerInvariant P (A+B) := by
  unfold OperatorCornerInvariant at *
  simpa only [mul_add,add_mul] using congrArg₂ (·+·) hA hB

theorem sub {P A B : E →L[ℂ] E} (hA : OperatorCornerInvariant P A)
    (hB : OperatorCornerInvariant P B) : OperatorCornerInvariant P (A-B) := by
  unfold OperatorCornerInvariant at *
  simpa only [mul_sub,sub_mul] using congrArg₂ (·-·) hA hB

theorem smul {P A : E →L[ℂ] E} (hA : OperatorCornerInvariant P A) (z : ℂ) :
    OperatorCornerInvariant P (z •A) := by
  unfold OperatorCornerInvariant at *
  simpa only [mul_smul_comm,smul_mul_assoc] using congrArg (z •·) hA

theorem mul {P A B : E →L[ℂ] E} (hA : OperatorCornerInvariant P A)
    (hB : OperatorCornerInvariant P B) : OperatorCornerInvariant P (A*B) := by
  unfold OperatorCornerInvariant at *
  calc
    P*(A*B)=(P*A)*B := (mul_assoc _ _ _).symm
    _ = (P*A*P)*B := congrArg (·*B) hA
    _ = (P*A)*(P*B) := mul_assoc _ _ _
    _ = (P*A)*(P*B*P) := congrArg ((P*A)*·) hB
    _ = ((P*A*P)*B)*P := by simp only [mul_assoc]
    _ = ((P*A)*B)*P := by rw [←hA]
    _ = P*(A*B)*P := by rw [mul_assoc P A B]

/-- Complete operator-norm series preserve the corner, through an actual bounded compression. -/
theorem series [NontrivialTopology E] {P A : E →L[ℂ] E}
    (hA : OperatorCornerInvariant P A) (hP : P*P=P) (hPn : ‖P‖ ≤ 1)
    (c : ℕ → ℂ) (hc : ∀ n, ‖c n‖ ≤ 1) (hAn : ‖A‖ < 1) :
    OperatorCornerInvariant P (boundedOperatorSeries c A) := by
  have hn : ‖P*A*P‖ ≤ ‖A‖ := by
    calc
      _ ≤ (‖P‖*‖A‖)*‖P‖ := (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ (1*‖A‖)*1 := by gcongr
      _ = _ := by ring
  have hi : P.comp A=(P*A*P).comp P := by
    change P*A=P*A*P*P
    rw [mul_assoc (P*A) P P,hP]
    exact hA
  have hs := boundedOperatorSeries_intertwine c hc P A (P*A*P) hAn (hn.trans_lt hAn) hi
  change P*boundedOperatorSeries c A=boundedOperatorSeries c (P*A*P)*P at hs
  unfold OperatorCornerInvariant
  rw [hs,mul_assoc (boundedOperatorSeries c (P*A*P)) P P,hP]

/-- Every exponential term remains inside the same full coordinate corner. -/
theorem exp [NontrivialTopology E] {P A : E →L[ℂ] E}
    (hA : OperatorCornerInvariant P A) (hP : P*P=P) (hPn : ‖P‖ ≤ 1) (hAn : ‖A‖ < 1) :
    OperatorCornerInvariant P (NormedSpace.exp A) := by
  rw [fullExponential_eq_series]
  exact hA.series hP hPn _ inverseFactorial_norm_le_one hAn

end OperatorCornerInvariant
end
end MeyerGeneralProblem.Adaptive
