module

public import MeyerGeneralProblem.Cardinal.Adaptive.EndpointCharacters

@[expose] public section

/-! # The actual finite endpoint sample kernel

The endpoint row and column carry one phase each. Killing their corner
reduces their consecutive equations to a Vandermonde system, then the interior
triangular kernel applies with its complete Fourier gauge.
-/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open scoped FourierTransform BigOperators

/-- Coefficients indexed by the physical and spectral single-endpoint phase families. -/
abbrev EndpointMatrix (k : ℕ) := EndpointPhaseIndex k → EndpointPhaseIndex k → ℂ

/-- The exact negative Fourier gauge for a translated modulated integer comb. -/
def endpointGauge (a b : ℝ) : ℂ :=
  Complex.exp (-((2*Real.pi*a*b : ℝ) : ℂ)*Complex.I)

/-- The actual physical coefficient sample at one integer cell. -/
def endpointRow {k : ℕ} (β : Fin k → ℝ) (c : EndpointMatrix k)
    (a : EndpointPhaseIndex k) (n : ℤ) : ℂ :=
  ∑ b, criticalCharacter n (endpointPhase β b)*c a b

/-- The actual spectral coefficient sample with its complete Fourier phase. -/
def endpointFourierRow {k : ℕ} (α β : Fin k → ℝ) (c : EndpointMatrix k)
    (b : EndpointPhaseIndex k) (n : ℤ) : ℂ :=
  ∑ a, criticalCharacter (-n) (endpointPhase α a)*
    (endpointGauge (endpointPhase α a) (endpointPhase β b)*c a b)

theorem endpointGauge_signed (a b : ℝ) (u v : Bool) (z : ℂ) :
    endpointGauge (criticalSignedPhase u a) (criticalSignedPhase v b)*z =
      Complex.exp (-((2*Real.pi*a*b : ℝ) : ℂ)*Complex.I*(if u=v then 1 else -1))*z := by
  congr 2
  cases u <;> cases v <;> simp [endpointGauge,criticalSignedPhase]

/-- Consecutive samples determine a whole signed interior row. -/
theorem signedCharacter_consecutive_zero {k : ℕ} (β : Fin k → ℝ)
    (hb : Function.Injective β) (hi : ∀ i, 0 < β i ∧ β i < 1/2)
    (a : Fin k → Bool → ℂ) (start : ℤ)
    (h : ∀ n : Fin (2*k), finiteSignedRow β a (criticalCharacter (start+(n : ℕ))) = 0) : a = 0 := by
  have hx : Function.Injective (fun i : Fin k × Bool => criticalCharacter 1 (criticalSignedPhase i.2 (β i.1))) := by
    intro i j he
    exact Option.some_injective _ (endpointCharacters_injective β hb hi he)
  have hz := finiteCharacter_consecutive_zero
    (fun i : Fin k × Bool => criticalSignedPhase i.2 (β i.1)) (fun i => a i.1 i.2) hx start
    (fun n => by
      have he := h ⟨n,by have hh := n.isLt; simpa [mul_comm] using hh⟩
      simpa only [finiteSignedRow,LinearMap.coe_mk,AddHom.coe_mk,Fintype.sum_prod_type] using he)
  funext i u
  exact congrFun hz (i,u)

/-- Reversed consecutive Fourier samples determine an interior row as well. -/
theorem signedCharacter_negative_consecutive_zero {k : ℕ} (α : Fin k → ℝ)
    (ha : Function.Injective α) (hi : ∀ i, 0 < α i ∧ α i < 1/2)
    (a : Fin k → Bool → ℂ) (start : ℤ)
    (h : ∀ n : Fin (2*k), finiteSignedRow α a (criticalCharacter (-(start+(n : ℕ)))) = 0) : a = 0 := by
  by_cases hk : k = 0
  · subst k; ext i; exact Fin.elim0 i
  apply signedCharacter_consecutive_zero α ha hi a (-start-(2*k-1 : ℕ))
  intro n
  have hn : (n : ℕ) < 2*k := n.isLt
  let r : Fin (2*k) := ⟨2*k-1-n,by omega⟩
  have he : -start-((2*k-1 : ℕ) : ℤ)+(n : ℕ) = -(start+(r : ℕ)) := by
    dsimp [r]
    omega
  rw [he]
  exact h r

/-- The original finite endpoint equations have trivial kernel once the
single endpoint corner is fixed to zero. All endpoint equations use exactly
`-k,...,k-1`; no extra endpoint equation is inserted. -/
theorem endpointMatrix_kernel {k : ℕ} (α β : Fin k → ℝ)
    (ha : Function.Injective α) (hb : Function.Injective β)
    (hia : ∀ i, 0 < α i ∧ α i < 1/2) (hib : ∀ i, 0 < β i ∧ β i < 1/2)
    (c : EndpointMatrix k) (hcorner : c none none = 0)
    (hendA : ∀ n : Fin (2*k), endpointRow β c none (-(k : ℤ)+(n : ℕ)) = 0)
    (hendB : ∀ n : Fin (2*k), endpointFourierRow α β c none (-(k : ℤ)+(n : ℕ)) = 0)
    (hA : ∀ (i : Fin k) (u : Bool) (n : ℤ), |n| ≤ (i : ℤ) →
      endpointRow β c (some (i,u)) n = 0)
    (hB : ∀ (j : Fin k) (v : Bool) (n : ℤ), |n| ≤ (j : ℤ) →
      endpointFourierRow α β c (some (j,v)) n = 0) : c = 0 := by
  have hrow : ∀ b, c none b = 0 := by
    have hz := signedCharacter_consecutive_zero β hb hib (fun j v => c none (some (j,v))) (-k)
      (fun n => by simpa [endpointRow,Fintype.sum_option,Fintype.sum_prod_type,hcorner,
        finiteSignedRow,endpointPhase] using hendA n)
    intro b
    cases b with
    | none => exact hcorner
    | some b => exact congrFun (congrFun hz b.1) b.2
  have hcol : ∀ a, c a none = 0 := by
    have hz := signedCharacter_negative_consecutive_zero α ha hia
      (fun i u => endpointGauge (criticalSignedPhase u (α i)) (1/2)*c (some (i,u)) none) (-k)
      (fun n => by simpa [endpointFourierRow,Fintype.sum_option,Fintype.sum_prod_type,hcorner,
        finiteSignedRow,endpointPhase] using hendB n)
    intro a
    cases a with
    | none => exact hcorner
    | some a =>
      exact (mul_eq_zero.mp (congrFun (congrFun hz a.1) a.2)).resolve_left (Complex.exp_ne_zero _)
  have hint := critical_triangular_samples_kernel α β ha hb hia hib
    (fun i j u v => c (some (i,u)) (some (j,v)))
    (fun i u n hn => by simpa [endpointRow,Fintype.sum_option,Fintype.sum_prod_type,
      hcol,finiteSignedRow,endpointPhase] using hA i u n hn)
    (fun j v n hn => by
      have he := hB j v n hn
      simpa [endpointFourierRow,Fintype.sum_option,Fintype.sum_prod_type,hrow,
        finiteSignedRow,endpointPhase,endpointGauge_signed,signedGauge] using he)
  funext a b
  cases a with
  | none => exact hrow b
  | some a =>
    cases b with
    | none => exact hcol (some a)
    | some b => exact congrFun (congrFun (congrFun (congrFun hint a.1) b.1) a.2) b.2

end
end MeyerGeneralProblem.Adaptive
