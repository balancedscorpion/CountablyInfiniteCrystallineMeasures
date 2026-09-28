module

public import MeyerGeneralProblem.Sampling.KNSGraphRepresentative
public import MeyerGeneralProblem.Sampling.KNSGraphSchwartzComparison

@[expose] public section

/-!
# First derivatives and the mixed Schwartz bound at graph order two

The actual reflected Fourier representative has its first classical derivative
in L2 at exactly graph order two. Its pure second physical weight is also in L2.
On the existing Schwartz embedding, the actual mixed function agrees pointwise
with the Schwartz multiplier-derivative, and the retained mixed-energy estimate
bounds its L2 norm by the actual graph norm. No graph-density premise is used.
The arbitrary-graph mixed estimate is proved in KNSGraphMixedCompletion.
-/

namespace MeyerGeneralProblem.KNSGraphDerivative

noncomputable section

open MeasureTheory MeyerGeneralProblem
open scoped FourierTransform

/-- The actual order-two representative has its first classical derivative
in L2, using one spare Fourier moment and the genuine reflection sign. -/
theorem representative_deriv_memLp (v : KNSGraphSpace 2) :
    MemLp (deriv (KNSGraphSpace.representative 2 v)) 2 := by
  let q : ℝ → ℂ := KNSGraphSpace.frequency 2 v
  have hq : MemLp q 2 := Lp.memLp _
  have hq2 : MemLp (fun x : ℝ => (x : ℂ)^2 * q x) 2 :=
    (memLp_congr_ae (KNSGraphSpace.frequencyWeight_ae v)).mpr (Lp.memLp _)
  have hK := memLp_fourierDerivativeData_of_physical_power 2 hq2
  have hm : ∀ j : ℕ, j ≤ 1 → Integrable (fun x : ℝ => x^j • q x) := by
    intro j hj
    exact integrable_real_moment_of_fourierSobolev hq hK (by omega)
  have hM := memLp_fourierDerivativeData_of_le hq hK (show 1 ≤ 2 by omega)
  obtain ⟨hD, _⟩ := memLp_iteratedDeriv_fourier_of_integrable_moments_le
    hm (show 1 ≤ 1 by omega) hM
  have hneg := (hD.comp_measurePreserving
    (Measure.measurePreserving_neg (volume : Measure ℝ))).neg
  convert hneg using 1
  funext x
  change deriv (fun y : ℝ => (𝓕 q : ℝ → ℂ) (-y)) x = _
  have he := iteratedDeriv_comp_neg 1 (𝓕 q : ℝ → ℂ) x
  simpa only [iteratedDeriv_one, pow_one, neg_one_smul, Function.comp_apply,
    Pi.neg_apply, KNSGraphSpace.representative, q] using he

/-- The pure second physical weight of the actual representative is L2,
by its already-proved AE relation to the physical graph coordinate. -/
theorem representative_second_weight_memLp (v : KNSGraphSpace 2) :
    MemLp (fun x : ℝ => (x : ℂ)^2 * KNSGraphSpace.representative 2 v x) 2 := by
  apply (memLp_congr_ae ?_).mpr (KNSGraphSpace.memLp_physicalWeight v)
  filter_upwards [KNSGraphSpace.representative_ae (by omega : 1 ≤ 2) v] with x hx
  rw [hx]

/-- The actual mixed function on an embedded Schwartz element is the
Schwartz multiplier-derivative itself, pointwise rather than just AE. -/
theorem embedded_mixed_eq (f : SchwartzMap ℝ ℂ) :
    (fun x : ℝ => (x : ℂ) *
      deriv (KNSGraphSpace.representative 2 (KNSGraphSpace.schwartzEmbedding 2 f)) x) =
    (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => x)
      (SchwartzMap.derivCLM ℂ ℂ f) : ℝ → ℂ) := by
  rw [KNSGraphSpace.representative_schwartzEmbedding (by omega : 2 ≤ 2)]
  funext x
  rw [SchwartzMap.smulLeftCLM_apply_apply (by fun_prop),
    SchwartzMap.derivCLM_apply]
  exact Complex.real_smul.symm

/-- Embedded Schwartz elements genuinely have the mixed function in L2. -/
theorem embedded_mixed_memLp (f : SchwartzMap ℝ ℂ) :
    MemLp (fun x : ℝ => (x : ℂ) *
      deriv (KNSGraphSpace.representative 2 (KNSGraphSpace.schwartzEmbedding 2 f)) x) 2 := by
  rw [embedded_mixed_eq]
  exact (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => x)
    (SchwartzMap.derivCLM ℂ ℂ f)).memLp 2

/-- A safe positive constant fixed before the embedded Schwartz input. -/
theorem mixed_graph_constant_pos : 0 < 1 + (2 * Real.pi)^4 := by positivity

/-- The retained mixed Schwartz inequality bounds the actual embedded
representative by its actual order-two graph norm, with no density premise. -/
theorem embedded_mixed_graph_bound (f : SchwartzMap ℝ ℂ) :
    ‖(embedded_mixed_memLp f).toLp‖^2 ≤
      (1 + (2 * Real.pi)^4) * ‖KNSGraphSpace.schwartzEmbedding 2 f‖^2 := by
  let W := SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => x^2) f
  let D := SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ f)
  let M := SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => x) (SchwartzMap.derivCLM ℂ ℂ f)
  have heLp : (embedded_mixed_memLp f).toLp = M.toLp 2 volume := by
    apply Lp.ext
    filter_upwards [(embedded_mixed_memLp f).coeFn_toLp,
      M.coeFn_toLp 2 volume] with x hx hy
    rw [hx, hy]
    exact congrFun (embedded_mixed_eq f) x
  have hW : W = coordinateMultiplicationCLM (coordinateMultiplicationCLM f) := by
    ext x
    dsimp only [W]
    rw [SchwartzMap.smulLeftCLM_apply_apply (g := fun x : ℝ => x^2) (by fun_prop)]
    simp only [coordinateMultiplicationCLM_apply, Complex.real_smul]
    push_cast
    ring
  have heN := KNSGraphSchwartzComparison.norm_schwartzEmbedding_two_sq f
  rw [← hW] at heN
  have hm := KNSMixedWeightedSchwartz.mixed_lp_norm_sq_le f
  change ‖M.toLp 2 volume‖^2 ≤ ‖f.toLp 2 volume‖^2 +
    (‖W.toLp 2 volume‖^2 + ‖D.toLp 2 volume‖^2)/2 at hm
  rw [heLp]
  let P : ℝ := (2 * Real.pi)^4
  let N : ℝ := ‖KNSGraphSpace.schwartzEmbedding 2 f‖^2
  have hp : 0 < P := by dsimp [P]; positivity
  have hp1 : 1 ≤ P := by
    dsimp [P]
    have hbase : 1 ≤ 2 * Real.pi := by linarith [Real.two_le_pi]
    exact one_le_pow₀ hbase
  have hn : 0 ≤ N := sq_nonneg _
  have hN : N = 2 * ‖f.toLp 2 volume‖^2 + ‖W.toLp 2 volume‖^2 +
      P⁻¹ * ‖D.toLp 2 volume‖^2 := heN
  have ha : ‖f.toLp 2 volume‖^2 ≤ N := by
    rw [hN]
    have hi : 0 ≤ P⁻¹ * ‖D.toLp 2 volume‖^2 := by positivity
    nlinarith [sq_nonneg ‖W.toLp 2 volume‖, sq_nonneg ‖f.toLp 2 volume‖]
  have hb : ‖W.toLp 2 volume‖^2 ≤ N := by
    rw [hN]
    have hi : 0 ≤ P⁻¹ * ‖D.toLp 2 volume‖^2 := by positivity
    nlinarith [sq_nonneg ‖f.toLp 2 volume‖]
  have hc0 : P⁻¹ * ‖D.toLp 2 volume‖^2 ≤ N := by
    rw [hN]
    nlinarith [sq_nonneg ‖W.toLp 2 volume‖, sq_nonneg ‖f.toLp 2 volume‖]
  have hc : ‖D.toLp 2 volume‖^2 ≤ P * N := by
    have hh := mul_le_mul_of_nonneg_left hc0 hp.le
    simpa only [← mul_assoc, mul_inv_cancel₀ hp.ne', one_mul] using hh
  have hPN : N ≤ P * N := by nlinarith
  change ‖M.toLp 2 volume‖^2 ≤ (1 + P) * N
  nlinarith

/-- The embedded estimate has a single positive constant before all inputs. -/
theorem exists_embedded_mixed_graph_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ f : SchwartzMap ℝ ℂ,
      ‖(embedded_mixed_memLp f).toLp‖^2 ≤
        C * ‖KNSGraphSpace.schwartzEmbedding 2 f‖^2 :=
  ⟨1 + (2 * Real.pi)^4, mixed_graph_constant_pos, embedded_mixed_graph_bound⟩

/-- The genuine zero graph vector has a zero mixed function. -/
theorem zero_graph_mixed :
    (fun x : ℝ => (x : ℂ) * deriv
      (KNSGraphSpace.representative 2 (0 : KNSGraphSpace 2)) x) = 0 := by
  rw [KNSGraphSpace.representative_zero]
  ext x
  simp

end
end MeyerGeneralProblem.KNSGraphDerivative
