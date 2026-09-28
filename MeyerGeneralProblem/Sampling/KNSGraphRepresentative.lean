module

public import MeyerGeneralProblem.Sampling.KNSGraphSpaceFourier
public import MeyerGeneralProblem.Sampling.SignedSquareSobolevDomain

@[expose] public section

/-!
# Actual representatives of the full KNS graph

The reflected ordinary Fourier integral of the actual frequency coordinate
recovers the physical coordinate almost everywhere. At graph order at least
two it gives an actual C1 Fourier pair with both L1 and L2 memberships and
both second square moments. Point samples are not transferred from AE
equality; identification with smooth inputs uses continuity on both sides.
-/

namespace MeyerGeneralProblem
namespace KNSGraphSpace

noncomputable section

open MeasureTheory Set
open scoped FourierTransform ContDiff

/-- The actual inverse Fourier integral of the graph frequency coordinate,
written using the negative-phase forward Fourier integral and reflection. -/
def representative (k : ℕ) (v : KNSGraphSpace k) (x : ℝ) : ℂ :=
  𝓕 (KNSGraphSpace.frequency k v : ℝ → ℂ) (-x)

/-- The chosen physical representative has the genuine inverse-integral sign. -/
theorem representative_eq_inverse (k : ℕ) (v : KNSGraphSpace k) (x : ℝ) :
    representative k v x = 𝓕⁻ (KNSGraphSpace.frequency k v : ℝ → ℂ) x :=
  (Real.fourierInv_eq_fourier_neg _ _).symm

private theorem frequency_power_memLp {k : ℕ} (v : KNSGraphSpace k) :
    MemLp (fun x : ℝ => (x : ℂ)^k * KNSGraphSpace.frequency k v x) 2 :=
  (memLp_congr_ae (KNSGraphSpace.frequencyWeight_ae v)).mpr (Lp.memLp _)

/-- At positive graph order the actual inverse integral recovers the physical
L2 coordinate almost everywhere, without assuming continuity of that coordinate. -/
theorem representative_ae {k : ℕ} (hk : 1 ≤ k) (v : KNSGraphSpace k) :
    representative k v =ᵐ[volume] (KNSGraphSpace.physical k v : ℝ → ℂ) := by
  have hreg := fourier_regular_of_physical_power k hk
    (Lp.memLp (KNSGraphSpace.frequency k v)) (frequency_power_memLp v)
  have hFq : (𝓕 (KNSGraphSpace.frequency k v : ℝ → ℂ) : ℝ → ℂ) =ᵐ[volume]
      (𝓕 (KNSGraphSpace.frequency k v) : KNSL2) := by
    simpa only [Lp.toLp_coeFn] using hreg.2.2.1
  have hreflect : (𝓕 (KNSGraphSpace.frequency k v) : KNSL2) =
      knsL2Reflection (KNSGraphSpace.physical k v) := by
    rw [KNSGraphSpace.frequency_eq_fourier, knsL2_fourier_fourier]
  rw [hreflect] at hFq
  have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae_eq_comp
    (hFq.trans (knsL2Reflection_ae (KNSGraphSpace.physical k v)))
  filter_upwards [h] with x hx
  simpa only [Function.comp_apply, neg_neg, representative] using hx

/-- Fourier transformation of the chosen representative agrees pointwise
with the integral of the original physical coordinate. -/
theorem fourier_representative_eq {k : ℕ} (hk : 1 ≤ k) (v : KNSGraphSpace k) :
    (𝓕 (representative k v) : ℝ → ℂ) =
      𝓕 (KNSGraphSpace.physical k v : ℝ → ℂ) := by
  funext x
  exact Real.fourier_congr_ae (representative_ae hk v) x

/-- The actual Fourier integral of the chosen representative recovers the
frequency coordinate almost everywhere. -/
theorem fourier_representative_ae {k : ℕ} (hk : 1 ≤ k) (v : KNSGraphSpace k) :
    (𝓕 (representative k v) : ℝ → ℂ) =ᵐ[volume]
      (KNSGraphSpace.frequency k v : ℝ → ℂ) := by
  rw [fourier_representative_eq hk v, KNSGraphSpace.frequency_eq_fourier]
  simpa only [Lp.toLp_coeFn] using
    (fourier_regular_of_physical_power k hk (Lp.memLp (KNSGraphSpace.physical k v))
      (KNSGraphSpace.memLp_physicalWeight v)).2.2.1

/-- Both actual members of the Fourier pair are continuously differentiable
at graph order at least two. -/
theorem representative_contDiff_pair {k : ℕ} (hk : 2 ≤ k) (v : KNSGraphSpace k) :
    ContDiff ℝ 1 (representative k v) ∧
      ContDiff ℝ 1 (𝓕 (representative k v) : ℝ → ℂ) := by
  have hk1 : 1 ≤ k := by omega
  have hp := (fourier_regular_of_physical_power k hk1
    (Lp.memLp (KNSGraphSpace.physical k v)) (KNSGraphSpace.memLp_physicalWeight v)).2.1
  have hq := (fourier_regular_of_physical_power k hk1
    (Lp.memLp (KNSGraphSpace.frequency k v)) (frequency_power_memLp v)).2.1
  have horder : (1 : WithTop ℕ∞) ≤ (k : WithTop ℕ∞) - 1 := by
    change ((1 : ℕ∞) : WithTop ℕ∞) ≤
      ((k : ℕ∞) : WithTop ℕ∞) - ((1 : ℕ∞) : WithTop ℕ∞)
    rw [← WithTop.coe_sub, WithTop.coe_le_coe]
    exact ENat.le_sub_of_add_le_right (by simp) (by exact_mod_cast hk)
  have hp1 : ContDiff ℝ 1 (𝓕 (KNSGraphSpace.physical k v : ℝ → ℂ)) :=
    hp.of_le horder
  have hq1 : ContDiff ℝ 1 (𝓕 (KNSGraphSpace.frequency k v : ℝ → ℂ)) :=
    hq.of_le horder
  constructor
  · exact hq1.comp (by fun_prop : ContDiff ℝ 1 (fun x : ℝ => -x))
  · rw [fourier_representative_eq hk1 v]
    exact hp1

private theorem secondMoment_of_power {g : ℝ → ℂ} {k : ℕ} (hk : 1 ≤ k)
    (hg : MemLp g 2) (hw : MemLp (fun x : ℝ => (x : ℂ)^k * g x) 2) :
    Integrable (fun x : ℝ => x^2 * ‖g x‖^2) := by
  have hm := memLp_fourierDerivativeData_of_le hg
    (memLp_fourierDerivativeData_of_physical_power k hw) hk
  have hi := (integrable_norm_sq_of_memLp_complex hm).const_mul ((2*Real.pi)^2)⁻¹
  convert hi using 1
  funext x
  rw [norm_fourierDerivativeData]
  simp only [pow_one, mul_pow, sq_abs]
  field_simp

/-- Every full graph element of order at least two has an actual C1 Fourier
pair with both L1 and L2 memberships and both second square moments.
All representative and integrability conclusions are derived from graph membership. -/
theorem representative_properties {k : ℕ} (hk : 2 ≤ k) (v : KNSGraphSpace k) :
    representative k v =ᵐ[volume] (KNSGraphSpace.physical k v : ℝ → ℂ) ∧
    (𝓕 (representative k v) : ℝ → ℂ) =ᵐ[volume]
      (KNSGraphSpace.frequency k v : ℝ → ℂ) ∧
    ContDiff ℝ 1 (representative k v) ∧
    ContDiff ℝ 1 (𝓕 (representative k v) : ℝ → ℂ) ∧
    Integrable (representative k v) ∧
    Integrable (𝓕 (representative k v) : ℝ → ℂ) ∧
    MemLp (representative k v) 2 ∧
    MemLp (𝓕 (representative k v) : ℝ → ℂ) 2 ∧
    Integrable (fun x : ℝ => x^2 * ‖representative k v x‖^2) ∧
    Integrable (fun x : ℝ => x^2 * ‖𝓕 (representative k v) x‖^2) := by
  have hk1 : 1 ≤ k := by omega
  have hp := fourier_regular_of_physical_power k hk1
    (Lp.memLp (KNSGraphSpace.physical k v)) (KNSGraphSpace.memLp_physicalWeight v)
  have hq := fourier_regular_of_physical_power k hk1
    (Lp.memLp (KNSGraphSpace.frequency k v)) (frequency_power_memLp v)
  have hf := representative_ae hk1 v
  have hF := fourier_representative_ae hk1 v
  have hC := representative_contDiff_pair hk v
  refine ⟨hf, hF, hC.1, hC.2, hp.1.congr hf.symm, hq.1.congr hF.symm,
    (memLp_congr_ae hf).mpr (Lp.memLp _),
    (memLp_congr_ae hF).mpr (Lp.memLp _), ?_, ?_⟩
  · apply (secondMoment_of_power hk1 (Lp.memLp (KNSGraphSpace.physical k v))
      (KNSGraphSpace.memLp_physicalWeight v)).congr
    filter_upwards [hf] with x hx
    rw [hx]
  · apply (secondMoment_of_power hk1 (Lp.memLp (KNSGraphSpace.frequency k v))
      (frequency_power_memLp v)).congr
    filter_upwards [hF] with x hx
    rw [hx]

/-- The construction sends the actual zero graph element to the zero function. -/
theorem representative_zero (k : ℕ) : representative k (0 : KNSGraphSpace k) = 0 := by
  funext x
  simp [representative, Real.fourier_eq]

/-- On an actual embedded Schwartz function the chosen representative is the
original function pointwise; no evenness or graph-density assertion is used. -/
theorem representative_schwartzEmbedding {k : ℕ} (hk : 2 ≤ k) (φ : SchwartzMap ℝ ℂ) :
    representative k (KNSGraphSpace.schwartzEmbedding k φ) = (φ : ℝ → ℂ) := by
  have hae := representative_ae (by omega : 1 ≤ k) (KNSGraphSpace.schwartzEmbedding k φ)
  rw [KNSGraphSpace.physical_schwartzEmbedding] at hae
  exact ((representative_contDiff_pair hk _).1.continuous.ae_eq_iff_eq volume
    φ.continuous).mp (hae.trans (φ.coeFn_toLp 2 volume))

end
end KNSGraphSpace
end MeyerGeneralProblem
