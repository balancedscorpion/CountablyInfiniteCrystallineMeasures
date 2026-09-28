module

public import MeyerGeneralProblem.Sampling.ClassicalFourierSobolev
public import Mathlib.Analysis.InnerProductSpace.PiL2
import all Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.Algebra.Module.ClosedSubmodule
import all Mathlib.Topology.Algebra.Module.ClosedSubmodule

@[expose] public section

/-!
# The actual complete KNS graph space

The graph records the four genuine L2 coordinates `f`, its Fourier
transform, its physical power weight and its Fourier power weight.
Distributional equalizers prove closedness; local distributional uniqueness
then recovers the actual almost-everywhere multiplication identities.
No smooth representative or completeness hypothesis is built into the input.
-/

namespace MeyerGeneralProblem

noncomputable section

open MeasureTheory Set
open scoped FourierTransform ComplexInnerProductSpace

/-- The actual complex L2 space on the real line. -/
abbrev KNSL2 := Lp ℂ 2 (volume : Measure ℝ)

/-- Four actual L2 coordinates, with the Hilbert sum norm rather than
the supremum norm on an ordinary product. -/
abbrev KNSGraphAmbient := PiLp 2 (fun _ : Fin 4 => KNSL2)

abbrev knsDistributionEmbedding : KNSL2 →L[ℂ] TemperedDistribution ℝ ℂ :=
  Lp.toTemperedDistributionCLM ℂ volume 2

abbrev knsPowerDistribution (k : ℕ) :
    TemperedDistribution ℝ ℂ →L[ℂ] TemperedDistribution ℝ ℂ :=
  TemperedDistribution.smulLeftCLM ℂ (fun x : ℝ => (x : ℂ) ^ k)

abbrev knsAmbientProjection (i : Fin 4) : KNSGraphAmbient →L[ℂ] KNSL2 :=
  PiLp.proj 2 (fun _ : Fin 4 => KNSL2) i

/-- The closed actual weighted Fourier graph. Its second coordinate is
the L2 Fourier transform of its first; the last two are genuine polynomial
weights, initially expressed as distributional equalizers. -/
def knsGraphSubmodule (k : ℕ) : ClosedSubmodule ℂ KNSGraphAmbient where
  carrier := {v | v 1 = 𝓕 (v 0) ∧
    knsDistributionEmbedding (v 2) = knsPowerDistribution k (knsDistributionEmbedding (v 0)) ∧
    knsDistributionEmbedding (v 3) = knsPowerDistribution k (knsDistributionEmbedding (v 1))}
  zero_mem' := by
    change (0 : KNSL2) = 𝓕 (0 : KNSL2) ∧
      knsDistributionEmbedding 0 = knsPowerDistribution k (knsDistributionEmbedding 0) ∧
      knsDistributionEmbedding 0 = knsPowerDistribution k (knsDistributionEmbedding 0)
    simp only [map_zero, FourierTransform.fourier_zero, and_self]
  add_mem' := by
    intro v w hv hw
    simp only [mem_ofPred_eq, PiLp.add_apply, map_add, FourierTransform.fourier_add,
      hv.1, hw.1, hv.2.1, hw.2.1, hv.2.2, hw.2.2, and_self]
  smul_mem' := by
    intro a v hv
    simp only [mem_ofPred_eq, PiLp.smul_apply, map_smul, FourierTransform.fourier_smul,
      hv.1, hv.2.1, hv.2.2, and_self]
  isClosed' := by
    apply IsClosed.inter
    · exact isClosed_eq (knsAmbientProjection 1).continuous
        ((FourierTransform.fourierCLM ℂ KNSL2).comp (knsAmbientProjection 0)).continuous
    · apply IsClosed.inter
      · exact isClosed_eq (knsDistributionEmbedding.comp (knsAmbientProjection 2)).continuous
          ((knsPowerDistribution k).comp
            (knsDistributionEmbedding.comp (knsAmbientProjection 0))).continuous
      · exact isClosed_eq (knsDistributionEmbedding.comp (knsAmbientProjection 3)).continuous
          ((knsPowerDistribution k).comp
            (knsDistributionEmbedding.comp (knsAmbientProjection 1))).continuous

/-- The complete KNS graph Hilbert space. Its norm squared is exactly
`2 * ‖f‖² + ‖x^k f‖² + ‖ξ^k Fourier(f)‖²`. -/
abbrev KNSGraphSpace (k : ℕ) := (knsGraphSubmodule k).toSubmodule

namespace KNSGraphSpace

/-- Every order of the actual graph domain is complete, by closedness
inside a finite Hilbert sum of genuine L2 spaces. -/
theorem complete (k : ℕ) : CompleteSpace (KNSGraphSpace k) :=
  (knsGraphSubmodule k).isClosed.isComplete.completeSpace_coe

/-- Completeness of the actual graph, available to Hilbert-space APIs. -/
instance (k : ℕ) : CompleteSpace (KNSGraphSpace k) := complete k

/-- Bounded coordinate projections of the actual graph. -/
def coordinate (k : ℕ) (i : Fin 4) : KNSGraphSpace k →L[ℂ] KNSL2 :=
  (knsAmbientProjection i).comp (knsGraphSubmodule k).toSubmodule.subtypeL

/-- The physical L2 function underlying a graph element. -/
abbrev physical (k : ℕ) : KNSGraphSpace k →L[ℂ] KNSL2 := coordinate k 0

/-- The actual Fourier L2 function underlying a graph element. -/
abbrev frequency (k : ℕ) : KNSGraphSpace k →L[ℂ] KNSL2 := coordinate k 1

/-- The physical power-weighted L2 coordinate. -/
abbrev physicalWeight (k : ℕ) : KNSGraphSpace k →L[ℂ] KNSL2 := coordinate k 2

/-- The frequency power-weighted L2 coordinate. -/
abbrev frequencyWeight (k : ℕ) : KNSGraphSpace k →L[ℂ] KNSL2 := coordinate k 3

/-- The second coordinate is the actual Fourier transform, not an
independent input with merely a matching norm. -/
theorem frequency_eq_fourier {k : ℕ} (v : KNSGraphSpace k) :
    frequency k v = 𝓕 (physical k v) := v.property.1

/-- The physical weighted coordinate has the actual multiplication
representative almost everywhere. -/
theorem physicalWeight_ae {k : ℕ} (v : KNSGraphSpace k) :
    (fun x : ℝ => (x : ℂ) ^ k * physical k v x) =ᵐ[volume] physicalWeight k v :=
  ae_mul_eq_of_L2_distribution_eq _ _ _ (by fun_prop) v.property.2.1

/-- The frequency weighted coordinate has the actual multiplication
representative almost everywhere. -/
theorem frequencyWeight_ae {k : ℕ} (v : KNSGraphSpace k) :
    (fun x : ℝ => (x : ℂ) ^ k * frequency k v x) =ᵐ[volume] frequencyWeight k v :=
  ae_mul_eq_of_L2_distribution_eq _ _ _ (by fun_prop) v.property.2.2

/-- Actual physical power-weight membership follows from graph membership. -/
theorem memLp_physicalWeight {k : ℕ} (v : KNSGraphSpace k) :
    MemLp (fun x : ℝ => (x : ℂ) ^ k * physical k v x) 2 :=
  (memLp_congr_ae (physicalWeight_ae v)).mpr (Lp.memLp _)

/-- Actual Fourier power-weight membership follows from graph membership. -/
theorem memLp_frequencyWeight {k : ℕ} (v : KNSGraphSpace k) :
    MemLp (fun x : ℝ => (x : ℂ) ^ k * (𝓕 (physical k v) : KNSL2) x) 2 := by
  rw [← frequency_eq_fourier v]
  exact (memLp_congr_ae (frequencyWeight_ae v)).mpr (Lp.memLp _)

/-- Each genuine L2 coordinate is bounded by the graph norm. -/
theorem norm_coordinate_le {k : ℕ} (v : KNSGraphSpace k) (i : Fin 4) :
    ‖coordinate k i v‖ ≤ ‖v‖ := PiLp.norm_apply_le v.val i

/-- The exact retained KNS norm, including both copies of unweighted mass. -/
theorem norm_sq {k : ℕ} (v : KNSGraphSpace k) :
    ‖v‖ ^ 2 = 2 * ‖physical k v‖ ^ 2 + ‖physicalWeight k v‖ ^ 2 +
      ‖frequencyWeight k v‖ ^ 2 := by
  change ‖v.val‖ ^ 2 = _
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ‖physical k v‖ ^ 2 + (‖frequency k v‖ ^ 2 +
    (‖physicalWeight k v‖ ^ 2 + ‖frequencyWeight k v‖ ^ 2)) = _
  rw [frequency_eq_fourier, Lp.norm_fourier_eq]
  ring

private theorem distributionEmbedding_injective : Function.Injective knsDistributionEmbedding :=
  LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot (F := ℂ) (μ := volume))

/-- A graph element is determined by its actual physical L2 function. -/
theorem physical_injective (k : ℕ) : Function.Injective (physical k) := by
  intro v w h
  apply Subtype.ext
  apply PiLp.ext
  intro i
  fin_cases i
  · exact h
  · exact v.property.1.trans ((congrArg (fun f : KNSL2 => 𝓕 f) h).trans w.property.1.symm)
  · apply distributionEmbedding_injective
    exact v.property.2.1.trans ((congrArg (fun f : KNSL2 =>
      knsPowerDistribution k (knsDistributionEmbedding f)) h).trans w.property.2.1.symm)
  · apply distributionEmbedding_injective
    change knsDistributionEmbedding (v.val 3) = knsDistributionEmbedding (w.val 3)
    rw [v.property.2.2, w.property.2.2, v.property.1, w.property.1]
    exact congrArg (fun f : KNSL2 => knsPowerDistribution k (knsDistributionEmbedding (𝓕 f))) h

theorem power_toLp_distribution (k : ℕ) (f : KNSL2)
    (hw : MemLp (fun x : ℝ => (x : ℂ) ^ k * f x) 2) :
    knsDistributionEmbedding hw.toLp = knsPowerDistribution k (knsDistributionEmbedding f) := by
  ext φ
  simp only [Lp.toTemperedDistributionCLM_apply, Lp.toTemperedDistribution_apply,
    TemperedDistribution.smulLeftCLM_apply_apply]
  apply integral_congr_ae
  filter_upwards [hw.coeFn_toLp] with x hx
  rw [SchwartzMap.smulLeftCLM_apply (by fun_prop :
    (fun x : ℝ => (x : ℂ) ^ k).HasTemperateGrowth)]
  simp only [hx, smul_eq_mul]
  ring

/-- Construct a graph element from an actual L2 function with both
actual power weights in L2. No classical differentiability is required. -/
def ofLp (k : ℕ) (f : KNSL2)
    (hphysical : MemLp (fun x : ℝ => (x : ℂ) ^ k * f x) 2)
    (hfrequency : MemLp (fun x : ℝ => (x : ℂ) ^ k * (𝓕 f : KNSL2) x) 2) :
    KNSGraphSpace k :=
  ⟨WithLp.toLp 2 ![f, 𝓕 f, hphysical.toLp, hfrequency.toLp],
    rfl, power_toLp_distribution k f hphysical,
    power_toLp_distribution k (𝓕 f) hfrequency⟩

/-- The graph constructor preserves the original L2 element exactly. -/
theorem physical_ofLp (k : ℕ) (f : KNSL2)
    (hphysical : MemLp (fun x : ℝ => (x : ℂ) ^ k * f x) 2)
    (hfrequency : MemLp (fun x : ℝ => (x : ℂ) ^ k * (𝓕 f : KNSL2) x) 2) :
    physical k (ofLp k f hphysical hfrequency) = f := rfl

/-- Exact range characterization of the physical projection: the graph
is the full actual mixed weighted domain, not a smaller abstract completion. -/
theorem exists_physical_eq_iff (k : ℕ) (f : KNSL2) :
    (∃ v : KNSGraphSpace k, physical k v = f) ↔
      MemLp (fun x : ℝ => (x : ℂ) ^ k * f x) 2 ∧
      MemLp (fun x : ℝ => (x : ℂ) ^ k * (𝓕 f : KNSL2) x) 2 := by
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨memLp_physicalWeight v, memLp_frequencyWeight v⟩
  · rintro ⟨hw, hF⟩
    exact ⟨ofLp k f hw hF, rfl⟩

private theorem weighted_integral_of_ae (k : ℕ) (f g : KNSL2)
    (h : (fun x : ℝ => (x : ℂ) ^ k * f x) =ᵐ[volume] g) :
    (∫ x : ℝ, |x| ^ (2 * k) * ‖f x‖ ^ 2) = ‖g‖ ^ 2 := by
  have he : (fun x : ℝ => |x| ^ (2 * k) * ‖f x‖ ^ 2) =ᵐ[volume]
      fun x : ℝ => ‖g x‖ ^ 2 := by
    filter_upwards [h] with x hx
    rw [← hx, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, mul_pow,
      ← pow_mul, Nat.mul_comm k 2]
  rw [integral_congr_ae he, integral_norm_sq_eq_toLp_norm_sq_complex (Lp.memLp g),
    Lp.toLp_coeFn]

/-- The graph norm is the actual physical/Fourier mixed weighted energy,
with all integrals tied to genuine L2 representatives. -/
theorem norm_sq_integral {k : ℕ} (v : KNSGraphSpace k) :
    ‖v‖ ^ 2 = 2 * ‖physical k v‖ ^ 2 +
      (∫ x : ℝ, |x| ^ (2 * k) * ‖physical k v x‖ ^ 2) +
      (∫ ξ : ℝ, |ξ| ^ (2 * k) * ‖(𝓕 (physical k v) : KNSL2) ξ‖ ^ 2) := by
  rw [← frequency_eq_fourier v, weighted_integral_of_ae k _ _ (physicalWeight_ae v),
    weighted_integral_of_ae k _ _ (frequencyWeight_ae v), norm_sq]

abbrev knsSchwartzPower (k : ℕ) : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
  SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => (x : ℂ) ^ k)

private theorem knsSchwartzPower_distribution (k : ℕ) (φ : SchwartzMap ℝ ℂ) :
    knsDistributionEmbedding ((knsSchwartzPower k φ).toLp 2) =
      knsPowerDistribution k (knsDistributionEmbedding (φ.toLp 2)) := by
  ext ψ
  simp only [Lp.toTemperedDistributionCLM_apply, Lp.toTemperedDistribution_apply,
    TemperedDistribution.smulLeftCLM_apply_apply]
  apply integral_congr_ae
  filter_upwards [(knsSchwartzPower k φ).coeFn_toLp 2 volume,
    φ.coeFn_toLp 2 volume] with x hx hφ
  simp only [hx, hφ, knsSchwartzPower, SchwartzMap.smulLeftCLM_apply
    (by fun_prop : (fun x : ℝ => (x : ℂ) ^ k).HasTemperateGrowth), smul_eq_mul]
  ring

def knsSchwartzAmbient (k : ℕ) : SchwartzMap ℝ ℂ →L[ℂ] KNSGraphAmbient :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 4 => KNSL2)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi ![SchwartzMap.toLpCLM ℂ ℂ 2 volume,
      (SchwartzMap.toLpCLM ℂ ℂ 2 volume).comp (FourierTransform.fourierCLM ℂ (SchwartzMap ℝ ℂ)),
      (SchwartzMap.toLpCLM ℂ ℂ 2 volume).comp (knsSchwartzPower k),
      ((SchwartzMap.toLpCLM ℂ ℂ 2 volume).comp (knsSchwartzPower k)).comp
        (FourierTransform.fourierCLM ℂ (SchwartzMap ℝ ℂ))])

/-- Actual Schwartz functions embed continuously and complex-linearly
in every graph order. This does not assert graph-density of the embedding. -/
def schwartzEmbedding (k : ℕ) : SchwartzMap ℝ ℂ →L[ℂ] KNSGraphSpace k :=
  (knsSchwartzAmbient k).codRestrict (knsGraphSubmodule k).toSubmodule (by
    intro φ
    exact ⟨(SchwartzMap.toLp_fourier_eq φ).symm,
      knsSchwartzPower_distribution k φ, knsSchwartzPower_distribution k (𝓕 φ)⟩)

/-- The Schwartz embedding has exactly the original L2 representative. -/
theorem physical_schwartzEmbedding (k : ℕ) (φ : SchwartzMap ℝ ℂ) :
    physical k (schwartzEmbedding k φ) = φ.toLp 2 := rfl

/-- The actual Schwartz embedding loses no functions at any graph order. -/
theorem schwartzEmbedding_injective (k : ℕ) : Function.Injective (schwartzEmbedding k) := by
  intro φ ψ h
  apply SchwartzMap.injective_toLp 2 volume
  exact congrArg (physical k) h

/-- A regression at order zero: the actual graph contains every L2
function, without requiring even continuity of its representative. -/
theorem exists_physical_order_zero (f : KNSL2) :
    ∃ v : KNSGraphSpace 0, physical 0 v = f := by
  apply (exists_physical_eq_iff 0 f).mpr
  simpa only [pow_zero, one_mul] using And.intro (Lp.memLp f) (Lp.memLp (𝓕 f : KNSL2))

end KNSGraphSpace

end

end MeyerGeneralProblem
