module

public import MeyerGeneralProblem.Cardinal.Adaptive.EndpointReverseZak
public import MeyerGeneralProblem.Cardinal.Adaptive.HalfWeylSource

@[expose] public section

/-! Exact half-Weyl recentering of complete finite endpoint sources. -/

noncomputable section
open scoped BigOperators

namespace MeyerGeneralProblem.Adaptive

/-- Translation followed by modulation of the whole Poisson source, retaining
the complete phase factor rather than replacing the source by sample values. -/
theorem wholePoissonSource_translate_modulate (a b s t : ℝ) :
    combDistributionModulation t (combDistributionTranslation s (wholePoissonSource a b)) =
      combModulationCharacter t (a+s) • wholePoissonSource (a+s) (b+t) := by
  ext f
  rw [combDistributionModulation_apply,combDistributionTranslation_apply,wholePoissonSource_apply]
  simp only [combSchwartzTranslation_apply,combSchwartzModulation_apply,smul_apply,smul_eq_mul,
    wholePoissonSource_apply]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  have he : criticalCharacter n b*combModulationCharacter t (s+(a+n)) =
      combModulationCharacter t (a+s)*criticalCharacter n (b+t) := by
    simp only [criticalCharacter,combModulationCharacter_eq_exp]
    rw [← Complex.exp_add,← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [← mul_assoc,he,mul_assoc,show s+(a+(n:ℝ))=a+s+n by ring]

/-- An integer shift of the spectral representative leaves the entire source unchanged. -/
theorem wholePoissonSource_frequency_int (a b : ℝ) (z : ℤ) :
    wholePoissonSource a (b+z)=wholePoissonSource a b := by
  ext f
  simp only [wholePoissonSource_apply]
  apply tsum_congr
  intro n
  have he : criticalCharacter n (b+z)=criticalCharacter n b := by
    unfold criticalCharacter
    push_cast
    rw [mul_add,Complex.exp_add]
    have hh : Complex.exp (2*(Real.pi:ℂ)*Complex.I*(n:ℂ)*(z:ℂ))=1 := by
      have he : 2*(Real.pi:ℂ)*Complex.I*(n:ℂ)*(z:ℂ) = ((n*z:ℤ):ℂ)*(2*Real.pi*Complex.I) := by
        push_cast
        ring
      rw [he,Complex.exp_int_mul_two_pi_mul_I]
    rw [hh,mul_one]
  rw [he]

/-- An integer change of the physical representative has its exact character factor. -/
theorem wholePoissonSource_physical_int (a b : ℝ) (z : ℤ) :
    wholePoissonSource (a+z) b = criticalCharacter (-z) b • wholePoissonSource a b := by
  ext f
  simp only [wholePoissonSource_apply,smul_apply,smul_eq_mul]
  rw [← tsum_mul_left]
  rw [← (Equiv.addRight z).tsum_eq (fun n : ℤ => criticalCharacter (-z) b *
    (criticalCharacter n b*f (a+n)))]
  apply tsum_congr
  intro n
  change criticalCharacter n b*f (a+z+n) =
    criticalCharacter (-z) b*(criticalCharacter (n+z) b*f (a+(n+z : ℤ)))
  have he : criticalCharacter (-z) b*criticalCharacter (n+z) b=criticalCharacter n b := by
    have hh := congrFun (criticalCharacter_mul (-z) (n+z)) b
    simpa only [Pi.mul_apply,show -z+(n+z)=n by omega] using hh
  rw [← mul_assoc,he]
  simp only [Int.cast_add,add_assoc,add_comm]

/-- Exact complete half-Weyl recentering on each Poisson summand. -/
theorem halfWeyl_wholePoissonSource (a b : ℝ) :
    halfWeylDistributionCLM (wholePoissonSource a b) =
      combModulationCharacter (-1/2) (a-1/2) • wholePoissonSource (a-1/2) (b-1/2) := by
  simpa only [halfWeylDistributionCLM,ContinuousLinearMap.comp_apply,sub_eq_add_neg,neg_div] using wholePoissonSource_translate_modulate a b (-1/2) (-1/2)

/-- The small signed phase after half-Weyl recentering; the endpoint is zero. -/
def endpointCenteredPhase {k : ℕ} (δ : Fin k → ℝ) : EndpointPhaseIndex k → ℝ
  | none => 0
  | some (i,u) => if u then δ i else -δ i

/-- The actual integer representative correction of each original endpoint phase. -/
def endpointCenterCell {k : ℕ} : EndpointPhaseIndex k → ℤ
  | none => 0
  | some (_,u) => if u then -1 else 0

/-- Exact representative conversion, including the single endpoint. -/
theorem endpointPhase_recenter {k : ℕ} (α : Fin k → ℝ) (a : EndpointPhaseIndex k) :
    endpointPhase α a-1/2 =
      endpointCenteredPhase (fun i => 1/2-α i) a+endpointCenterCell a := by
  cases a with
  | none => norm_num [endpointPhase,endpointCenteredPhase,endpointCenterCell]
  | some a =>
      obtain ⟨i,u⟩ := a
      cases u <;> simp only [endpointPhase,criticalSignedPhase,endpointCenteredPhase,
        endpointCenterCell,Bool.false_eq_true,ite_false,ite_true,Int.cast_zero,Int.cast_neg,Int.cast_one] <;> ring

/-- The exact scalar produced by half-Weyl recentering and the physical integer
representative correction. There is no correction for the spectral integer. -/
def endpointCenterFactor {k : ℕ} (α β : Fin k → ℝ) (a b : EndpointPhaseIndex k) : ℂ :=
  combModulationCharacter (-1/2) (endpointPhase α a-1/2)*
    criticalCharacter (-endpointCenterCell a) (endpointCenteredPhase (fun i => 1/2-β i) b)

/-- Every complete Poisson summand becomes a complete source on the small signed
phases, with the explicit nontrivial scalar retained. -/
theorem halfWeyl_endpoint_summand {k : ℕ} (α β : Fin k → ℝ) (a b : EndpointPhaseIndex k) :
    halfWeylDistributionCLM (wholePoissonSource (endpointPhase α a) (endpointPhase β b)) =
      endpointCenterFactor α β a b • wholePoissonSource
        (endpointCenteredPhase (fun i => 1/2-α i) a)
        (endpointCenteredPhase (fun i => 1/2-β i) b) := by
  rw [halfWeyl_wholePoissonSource]
  rw [endpointPhase_recenter β b,wholePoissonSource_frequency_int]
  rw [endpointPhase_recenter α a,wholePoissonSource_physical_int,smul_smul]
  rw [endpointCenterFactor,endpointPhase_recenter α a]

/-- The entire actual half-Weyl endpoint source, on the actual centered phases. -/
theorem halfWeyl_endpointPoissonSynthesis {k : ℕ} (α β : Fin k → ℝ) (c : EndpointMatrix k) :
    halfWeylDistributionCLM (endpointPoissonSynthesis α β c) =
      ∑ a, ∑ b, (c a b*endpointCenterFactor α β a b) • wholePoissonSource
        (endpointCenteredPhase (fun i => 1/2-α i) a)
        (endpointCenteredPhase (fun i => 1/2-β i) b) := by
  change halfWeylDistributionCLM (∑ a, ∑ b, c a b • wholePoissonSource _ _) = _
  simp only [map_sum,map_smul,halfWeyl_endpoint_summand,smul_smul]

/-- Exact actual recentered source pairing at the small signed phases. -/
theorem halfWeyl_endpointPoissonSynthesis_reverseZak {k : ℕ}
    (α β : Fin k → ℝ) (c : EndpointMatrix k) (f : SchwartzMap ℝ ℂ) :
    halfWeylDistributionCLM (endpointPoissonSynthesis α β c) f =
      ∑ a, ∑ b, (c a b*endpointCenterFactor α β a b)*reverseZakChart f
        (endpointCenteredPhase (fun i => 1/2-α i) a)
        (endpointCenteredPhase (fun i => 1/2-β i) b) := by
  rw [halfWeyl_endpointPoissonSynthesis]
  simp only [sum_apply,smul_apply,smul_eq_mul,wholePoissonSource_reverseZak]

end MeyerGeneralProblem.Adaptive
