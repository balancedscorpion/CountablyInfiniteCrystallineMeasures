module

public import MeyerGeneralProblem.Cardinal.Adaptive.CriticalNativeRepair

@[expose] public section

/-! # Consecutive samples and the single endpoint phase

The endpoint is one coset, represented by `none`; it is never counted twice.
Consecutive samples are taken at their actual integer indices.
-/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open scoped FourierTransform BigOperators

theorem endpointCharacter_nat (n : ℕ) (x : ℝ) :
    criticalCharacter (n : ℤ) x = (criticalCharacter 1 x)^n := by
  unfold criticalCharacter
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem endpointCharacter_injective {a b : ℝ}
    (ha : -1/2 < a ∧ a ≤ 1/2) (hb : -1/2 < b ∧ b ≤ 1/2)
    (h : criticalCharacter 1 a = criticalCharacter 1 b) : a = b := by
  have hf (x : ℝ) : criticalCharacter 1 x = Complex.exp (((2*Real.pi*x : ℝ) : ℂ)*Complex.I) := by
    unfold criticalCharacter
    congr 1
    push_cast
    ring
  rw [hf a, hf b] at h
  have im (x : ℝ) : (((2*Real.pi*x : ℝ) : ℂ)*Complex.I).im = 2*Real.pi*x := by simp
  have hp := Real.pi_pos
  have he := Complex.exp_inj_of_neg_pi_lt_of_le_pi
    (x := (((2*Real.pi*a : ℝ) : ℂ)*Complex.I))
    (y := (((2*Real.pi*b : ℝ) : ℂ)*Complex.I))
    (by rw [im]; nlinarith [ha.1]) (by rw [im]; nlinarith [ha.2])
    (by rw [im]; nlinarith [hb.1]) (by rw [im]; nlinarith [hb.2]) h
  have hi := congrArg Complex.im he
  rw [im,im] at hi
  nlinarith

theorem finiteCharacterPower_samples_zero {ι : Type*} [Fintype ι]
    (z a : ι → ℂ) (hz : Function.Injective z)
    (h : ∀ n : Fin (Fintype.card ι), ∑ i, z i^(n : ℕ)*a i = 0) : a = 0 := by
  let e := Fintype.equivFin ι
  let M := (Matrix.vandermonde (fun i => z (e.symm i))).transpose
  have hdet : M.det ≠ 0 := by
    rw [Matrix.det_transpose]
    exact Matrix.det_vandermonde_ne_zero_iff.mpr (hz.comp e.symm.injective)
  have hunit : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).mpr (isUnit_iff_ne_zero.mpr hdet)
  have hm : M.mulVec (fun i => a (e.symm i)) = 0 := by
    funext n
    change (∑ j, z (e.symm j)^(n : ℕ)*a (e.symm j)) = 0
    rw [← Fintype.sum_equiv e (fun i => z i^(n : ℕ)*a i)
      (fun j => z (e.symm j)^(n : ℕ)*a (e.symm j)) (by intro i; simp)]
    exact h n
  have hzv : (fun i => a (e.symm i)) = 0 := by
    apply (Matrix.mulVec_injective_iff_isUnit.mpr hunit)
    simpa using hm
  funext i
  simpa using congrFun hzv (e i)


/-- The finite interior signed phases together with one endpoint coset. -/
abbrev EndpointPhaseIndex (k : ℕ) := Option (Fin k × Bool)

/-- The endpoint representative is positive one half. -/
def endpointPhase {k : ℕ} (α : Fin k → ℝ) : EndpointPhaseIndex k → ℝ
  | none => 1/2
  | some (i,u) => criticalSignedPhase u (α i)

theorem endpointPhase_range {k : ℕ} (α : Fin k → ℝ)
    (hi : ∀ i, 0 < α i ∧ α i < 1/2) (a : EndpointPhaseIndex k) :
    -1/2 < endpointPhase α a ∧ endpointPhase α a ≤ 1/2 := by
  cases a with
  | none => norm_num [endpointPhase]
  | some a =>
    rcases a with ⟨i,u⟩
    have h := hi i
    cases u <;> simp only [endpointPhase,criticalSignedPhase,Bool.false_eq_true,ite_false,ite_true] <;>
      constructor <;> linarith

theorem endpointPhase_injective {k : ℕ} (α : Fin k → ℝ) (ha : Function.Injective α)
    (hi : ∀ i, 0 < α i ∧ α i < 1/2) : Function.Injective (endpointPhase α) := by
  intro a b he
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some b =>
      rcases b with ⟨j,v⟩
      have h := hi j
      cases v <;> simp only [endpointPhase,criticalSignedPhase,Bool.false_eq_true,ite_false,ite_true] at he <;> linarith
  | some a =>
    rcases a with ⟨i,u⟩
    cases b with
    | none =>
      have h := hi i
      cases u <;> simp only [endpointPhase,criticalSignedPhase,Bool.false_eq_true,ite_false,ite_true] at he <;> linarith
    | some b =>
      rcases b with ⟨j,v⟩
      have h := hi i
      have h' := hi j
      apply congrArg some
      cases u <;> cases v <;> simp only [endpointPhase,criticalSignedPhase,Bool.false_eq_true,ite_false,ite_true] at he
      · exact Prod.ext (ha he) rfl
      · linarith
      · linarith
      · exact Prod.ext (ha (neg_inj.mp he)) rfl

/-- Distinct half-open phase representatives have distinct unit characters. -/
theorem endpointCharacters_injective {k : ℕ} (α : Fin k → ℝ) (ha : Function.Injective α)
    (hi : ∀ i, 0 < α i ∧ α i < 1/2) :
    Function.Injective (fun a => criticalCharacter 1 (endpointPhase α a)) := by
  intro a b h
  exact endpointPhase_injective α ha hi (endpointCharacter_injective
    (endpointPhase_range α hi a) (endpointPhase_range α hi b) h)

/-- A finite character sum is determined by any consecutive set of samples. -/
theorem finiteCharacter_consecutive_zero {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (a : ι → ℂ)
    (hx : Function.Injective (fun i => criticalCharacter 1 (x i))) (start : ℤ)
    (h : ∀ n : Fin (Fintype.card ι), ∑ i, criticalCharacter (start+(n : ℕ)) (x i)*a i = 0) :
    a = 0 := by
  have hz := finiteCharacterPower_samples_zero (fun i => criticalCharacter 1 (x i))
    (fun i => criticalCharacter start (x i)*a i) hx (fun n => by
      have he := h n
      have hadd (i : ι) : criticalCharacter (start+(n : ℕ)) (x i) =
          criticalCharacter start (x i)*criticalCharacter (n : ℕ) (x i) :=
        (congrFun (criticalCharacter_mul start (n : ℕ)) (x i)).symm
      simpa only [hadd,endpointCharacter_nat,mul_left_comm,mul_assoc,mul_comm] using he)
  funext i
  have hi := congrFun hz i
  exact (mul_eq_zero.mp hi).resolve_left (Complex.exp_ne_zero _)

end
end MeyerGeneralProblem.Adaptive
