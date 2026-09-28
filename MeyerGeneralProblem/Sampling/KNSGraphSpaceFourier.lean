module

public import MeyerGeneralProblem.Sampling.KNSGraphSpace

@[expose] public section

/-!
# Actual Fourier symmetry of the complete KNS graph

Double Fourier transformation is actual real reflection on L2, proved by
density from Schwartz inversion. Reflection of the physical power weight
then constructs Fourier transformation on the full weighted graph with
its exact norm. No symmetry of a sampling carrier is required or asserted.
-/

namespace MeyerGeneralProblem

noncomputable section

open MeasureTheory Set
open scoped FourierTransform

/-- Actual reflection of L2 functions on the real line as a complex
linear isometry, defined by measure-preserving composition. -/
def knsL2Reflection : KNSL2 →ₗᵢ[ℂ] KNSL2 :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun x : ℝ => -x) (Measure.measurePreserving_neg volume)

/-- The L2 reflection has the genuine reflected representative almost everywhere. -/
theorem knsL2Reflection_ae (f : KNSL2) :
    (knsL2Reflection f : ℝ → ℂ) =ᵐ[volume] fun x : ℝ => f (-x) :=
  Lp.coeFn_compMeasurePreserving f (Measure.measurePreserving_neg volume)

/-- Actual real reflection is an involution on L2. -/
theorem knsL2Reflection_involutive : Function.Involutive knsL2Reflection := by
  intro f
  apply Lp.ext
  have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae_eq_comp
    (knsL2Reflection_ae f)
  filter_upwards [knsL2Reflection_ae (knsL2Reflection f), h] with x hx hy
  simpa only [Function.comp_apply, neg_neg] using hx.trans hy

/-- Double Fourier transformation on actual L2 is real reflection.
The identity is extended from genuine Schwartz inversion by L2 density. -/
theorem knsL2_fourier_fourier (f : KNSL2) :
    𝓕 (𝓕 f : KNSL2) = knsL2Reflection f := by
  apply DenseRange.induction_on (p := fun f : KNSL2 => 𝓕 (𝓕 f : KNSL2) = knsL2Reflection f)
    (SchwartzMap.denseRange_toLpCLM (p := 2) ENNReal.ofNat_ne_top) f
  · exact isClosed_eq
      ((FourierTransform.fourierCLM ℂ KNSL2).comp
        (FourierTransform.fourierCLM ℂ KNSL2)).continuous knsL2Reflection.continuous
  intro φ
  change 𝓕 (𝓕 (φ.toLp 2) : KNSL2) = knsL2Reflection (φ.toLp 2)
  rw [SchwartzMap.toLp_fourier_eq, SchwartzMap.toLp_fourier_eq]
  apply Lp.ext
  have hφ := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae_eq_comp
    (φ.coeFn_toLp 2 volume)
  filter_upwards [(𝓕 (𝓕 φ)).coeFn_toLp 2 volume,
    knsL2Reflection_ae (φ.toLp 2), hφ] with x hx hy hz
  simp only [Function.comp_apply] at hz
  rw [hx, hy, hz]
  have h := congrArg (fun ψ : SchwartzMap ℝ ℂ => ψ (-x))
    (show 𝓕⁻ (𝓕 φ : SchwartzMap ℝ ℂ) = φ from FourierTransform.fourierInv_fourier_eq φ)
  change (𝓕 (𝓕 φ) : SchwartzMap ℝ ℂ) (-(-x)) = φ (-x) at h
  simpa only [neg_neg] using h

/-- Four successive genuine L2 Fourier transforms are the identity. -/
theorem knsL2_fourier_four (f : KNSL2) :
    𝓕 (𝓕 (𝓕 (𝓕 f : KNSL2) : KNSL2) : KNSL2) = f := by
  rw [knsL2_fourier_fourier, knsL2_fourier_fourier, knsL2Reflection_involutive]

private theorem power_reflection_ae (k : ℕ) (f g : KNSL2)
    (hw : (fun x : ℝ => (x : ℂ) ^ k * f x) =ᵐ[volume] g) :
    (fun x : ℝ => (x : ℂ) ^ k * knsL2Reflection f x) =ᵐ[volume]
      ((-1 : ℂ) ^ k • knsL2Reflection g : KNSL2) := by
  have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae_eq_comp hw
  filter_upwards [knsL2Reflection_ae f, knsL2Reflection_ae g, h,
    Lp.coeFn_smul ((-1 : ℂ) ^ k) (knsL2Reflection g)] with x hf hg hw hs
  simp only [Function.comp_apply] at hw
  rw [hf, hs]
  simp only [Pi.smul_apply, smul_eq_mul, hg, ← hw, Complex.ofReal_neg]
  have hp : (-1 : ℂ) ^ k * (-(x : ℂ)) ^ k = (x : ℂ) ^ k := by
    rw [← mul_pow]
    congr 1
    ring
  rw [← mul_assoc, hp]

namespace KNSGraphSpace

theorem memLp_fourier_twice_weight {k : ℕ} (v : KNSGraphSpace k) :
    MemLp (fun x : ℝ => (x : ℂ) ^ k * (𝓕 (𝓕 (physical k v) : KNSL2) : KNSL2) x) 2 := by
  rw [knsL2_fourier_fourier]
  exact (memLp_congr_ae (power_reflection_ae k _ _ (physicalWeight_ae v))).mpr (Lp.memLp _)

/-- Fourier transformation on the actual complete graph, constructed
from the actual transformed L2 function and proved weighted membership. -/
def fourier (k : ℕ) (v : KNSGraphSpace k) : KNSGraphSpace k :=
  ofLp k (𝓕 (physical k v)) (memLp_frequencyWeight v) (memLp_fourier_twice_weight v)

/-- Graph Fourier transformation acts by the actual L2 Fourier transform. -/
theorem physical_fourier {k : ℕ} (v : KNSGraphSpace k) :
    physical k (fourier k v) = 𝓕 (physical k v) := rfl

/-- The transformed physical weight is exactly the original frequency weight. -/
theorem physicalWeight_fourier {k : ℕ} (v : KNSGraphSpace k) :
    physicalWeight k (fourier k v) = frequencyWeight k v := by
  apply Lp.ext
  exact (physicalWeight_ae (fourier k v)).symm.trans (by
    simpa only [physical_fourier, ← frequency_eq_fourier v] using frequencyWeight_ae v)

/-- The transformed frequency weight is the actual reflected physical
weight with the necessary parity factor. -/
theorem frequencyWeight_fourier {k : ℕ} (v : KNSGraphSpace k) :
    frequencyWeight k (fourier k v) = (-1 : ℂ) ^ k • knsL2Reflection (physicalWeight k v) := by
  apply Lp.ext
  apply (frequencyWeight_ae (fourier k v)).symm.trans
  rw [frequency_eq_fourier, physical_fourier, knsL2_fourier_fourier]
  exact power_reflection_ae k _ _ (physicalWeight_ae v)

/-- Actual Fourier transformation preserves the exact KNS graph norm. -/
theorem norm_fourier {k : ℕ} (v : KNSGraphSpace k) : ‖fourier k v‖ = ‖v‖ := by
  have hsq : ‖fourier k v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [norm_sq, norm_sq, physical_fourier, physicalWeight_fourier,
      frequencyWeight_fourier, Lp.norm_fourier_eq, norm_smul, norm_pow,
      norm_neg, norm_one, one_pow, one_mul, knsL2Reflection.norm_map]
    ring
  nlinarith [norm_nonneg (fourier k v), norm_nonneg v]

/-- Actual Fourier transformation on the graph is a complex linear isometry. -/
def fourierLinearIsometry (k : ℕ) : KNSGraphSpace k →ₗᵢ[ℂ] KNSGraphSpace k where
  toFun := fourier k
  map_add' v w := by
    apply physical_injective k
    simp only [physical_fourier, map_add, FourierTransform.fourier_add]
  map_smul' a v := by
    apply physical_injective k
    simp only [physical_fourier, map_smul, FourierTransform.fourier_smul, RingHom.id_apply]
  norm_map' := norm_fourier

/-- Four graph Fourier transforms give back the original actual element. -/
theorem fourier_four {k : ℕ} (v : KNSGraphSpace k) :
    fourier k (fourier k (fourier k (fourier k v))) = v := by
  apply physical_injective k
  simp only [physical_fourier, knsL2_fourier_four]

/-- The actual graph Fourier operator is onto: three further transforms
give an inverse. No closed-range or index assertion is used. -/
theorem fourier_surjective (k : ℕ) : Function.Surjective (fourier k) := by
  intro v
  exact ⟨fourier k (fourier k (fourier k v)), fourier_four v⟩

/-- Genuine Fourier symmetry of the full complete mixed-weight domain,
as a complex linear isometric equivalence. -/
def fourierEquiv (k : ℕ) : KNSGraphSpace k ≃ₗᵢ[ℂ] KNSGraphSpace k :=
  LinearIsometryEquiv.ofSurjective (fourierLinearIsometry k) (fourier_surjective k)

end KNSGraphSpace

end

end MeyerGeneralProblem
