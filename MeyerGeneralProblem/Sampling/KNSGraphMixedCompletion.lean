module

public import MeyerGeneralProblem.Sampling.KNSGraphDerivative
public import MeyerGeneralProblem.Sampling.KNSGraphOscillator

@[expose] public section

/-!
# Mixed weighted derivatives on the actual order-two KNS graph

The genuine Schwartz multiplier-derivative extends boundedly from the
unrestricted positive Hermite scale. The proved graph reconstruction and
continuous distributional identities identify that extension with x times the
classical derivative of the actual graph representative almost everywhere,
without assuming mixed L2 membership. A single positive constant is chosen
before every graph vector. Unrestricted Schwartz density is derived at graph
order two, and the full estimate reduces to the original Schwartz theorem.
Zero and nonzero Hermite inputs are included. No carrier-zero-preserving core,
arbitrary-order mixed jets, sampler transfer, or whole supercritical claim follows
from this module alone.
-/

namespace MeyerGeneralProblem.KNSGraphMixedCompletion

noncomputable section

set_option maxHeartbeats 4000000

open MeasureTheory MeyerGeneralProblem LineDeriv
open MeyerGeneralProblem.KNSGraphDerivative MeyerGeneralProblem.KNSGraphOscillator
open scoped FourierTransform

/-- The actual Schwartz multiplier and derivative followed by the genuine
L2 map, before any extension is made. -/
def mixedSchwartz : SchwartzMap ℝ ℂ →L[ℂ] KNSL2 :=
  (SchwartzMap.toLpCLM ℂ ℂ 2 volume).comp
    (coordinateMultiplicationCLM.comp (SchwartzMap.derivCLM ℂ ℂ))

/-- The complex-linear mixed map equals the real multiplier used by the
retained endpoint theorem, as actual L2 vectors. -/
theorem mixedSchwartz_eq_real_toLp (φ : SchwartzMap ℝ ℂ) :
    mixedSchwartz φ = (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => x)
      (SchwartzMap.derivCLM ℂ ℂ φ)).toLp 2 volume := by
  change (coordinateMultiplicationCLM (SchwartzMap.derivCLM ℂ ℂ φ)).toLp 2 volume = _
  congr 1
  ext x
  rw [coordinateMultiplicationCLM_apply,
    SchwartzMap.smulLeftCLM_apply_apply (g := fun x : ℝ => x) (by fun_prop)]
  exact Complex.real_smul.symm

/-- The existing mixed endpoint theorem controls this genuine Schwartz
map by the unrestricted order-one Hermite norm. -/
theorem mixedSchwartz_norm_le (φ : SchwartzMap ℝ ℂ) :
    ‖mixedSchwartz φ‖ ≤ (3 * (1 + (2 * Real.pi)^4)) * ‖schwartzToHermiteScale 1 φ‖ := by
  have he : mixedSchwartz φ = (embedded_mixed_memLp φ).toLp := by
    rw [mixedSchwartz_eq_real_toLp]
    apply Lp.ext
    filter_upwards [(embedded_mixed_memLp φ).coeFn_toLp,
      (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => x)
        (SchwartzMap.derivCLM ℂ ℂ φ)).coeFn_toLp 2 volume] with x hx hy
    rw [hy, hx]
    exact (congrFun (embedded_mixed_eq φ) x).symm
  have hs := embedded_mixed_graph_bound φ
  rw [← he] at hs
  let C : ℝ := 1 + (2 * Real.pi)^4
  have hC : 1 ≤ C := by dsimp [C]; linarith [pow_nonneg Real.pi_pos.le 4]
  have hC0 : 0 ≤ C := by linarith
  have hN : 0 ≤ ‖KNSGraphSpace.schwartzEmbedding 2 φ‖ := norm_nonneg _
  have hnorm : ‖mixedSchwartz φ‖ ≤ C * ‖KNSGraphSpace.schwartzEmbedding 2 φ‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC0 hN)).mp
    have hprod : 0 ≤ (C-1) * C * ‖KNSGraphSpace.schwartzEmbedding 2 φ‖^2 := by positivity
    change ‖mixedSchwartz φ‖^2 ≤ (C * ‖KNSGraphSpace.schwartzEmbedding 2 φ‖)^2
    change ‖mixedSchwartz φ‖^2 ≤ C * ‖KNSGraphSpace.schwartzEmbedding 2 φ‖^2 at hs
    nlinarith
  calc
    _ ≤ C * ‖KNSGraphSpace.schwartzEmbedding 2 φ‖ := hnorm
    _ ≤ C * (3 * ‖schwartzToHermiteScale 1 φ‖) :=
      mul_le_mul_of_nonneg_left
        (KNSGraphSchwartzComparison.norm_schwartzEmbedding_two_le φ) hC0
    _ = _ := by dsimp [C]; ring

/-- The mixed operator extended through the existing unrestricted
positive Hermite scale; no graph-core assumption enters this definition. -/
def mixedExtension : HermiteScale 1 →L[ℂ] KNSL2 :=
  mixedSchwartz.toLinearMap.extendOfNorm (schwartzToHermiteScale 1).toLinearMap

/-- The extension agrees with the actual Schwartz mixed operator. -/
theorem mixedExtension_schwartz (φ : SchwartzMap ℝ ℂ) :
    mixedExtension (schwartzToHermiteScale 1 φ) = mixedSchwartz φ := by
  exact LinearMap.extendOfNorm_eq (schwartzToHermiteScale_denseRange 1)
    ⟨3 * (1 + (2 * Real.pi)^4), mixedSchwartz_norm_le⟩ φ

/-- The extension norm has a fixed bound before all positive-scale inputs. -/
theorem mixedExtension_norm_le (u : HermiteScale 1) :
    ‖mixedExtension u‖ ≤ (3 * (1 + (2 * Real.pi)^4)) * ‖u‖ :=
  LinearMap.norm_extendOfNorm_apply_le (schwartzToHermiteScale_denseRange 1)
    (3 * (1 + (2 * Real.pi)^4)) mixedSchwartz_norm_le u

/-- The Schwartz mixed map is exactly multiplication of its distributional
derivative, fixing its sign and the order of the two operations. -/
theorem mixedSchwartz_distribution (φ : SchwartzMap ℝ ℂ) :
    (mixedSchwartz φ : TemperedDistribution ℝ ℂ) =
      TemperedDistribution.smulLeftCLM ℂ (fun x : ℝ => (x : ℂ))
        (TemperedDistribution.derivCLM ℂ (φ.toLp 2 volume : TemperedDistribution ℝ ℂ)) := by
  have hd : TemperedDistribution.derivCLM ℂ
      (φ.toLp 2 volume : TemperedDistribution ℝ ℂ) =
      ((SchwartzMap.derivCLM ℂ ℂ φ).toLp 2 volume : TemperedDistribution ℝ ℂ) := by
    simp only [Lp.toTemperedDistribution_toLp_eq,
      TemperedDistribution.derivCLM_toTemperedDistributionCLM_eq ℂ]
  rw [hd, mixedSchwartz_eq_real_toLp]
  ext ψ
  simp only [Lp.toTemperedDistribution_apply, TemperedDistribution.smulLeftCLM_apply_apply]
  apply integral_congr_ae
  filter_upwards [(SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => x)
    (SchwartzMap.derivCLM ℂ ℂ φ)).coeFn_toLp 2 volume,
    (SchwartzMap.derivCLM ℂ ℂ φ).coeFn_toLp 2 volume] with x hx hy
  rw [hx, hy,
    SchwartzMap.smulLeftCLM_apply_apply (g := fun x : ℝ => x) (by fun_prop),
    SchwartzMap.smulLeftCLM_apply_apply (g := fun x : ℝ => (x : ℂ)) (by fun_prop)]
  simp only [smul_eq_mul, Complex.real_smul]
  ring

/-- Continuous equality on the unrestricted Schwartz range identifies
the completed mixed operator distributionally on every Hermite-scale input. -/
theorem mixedExtension_distribution (u : HermiteScale 1) :
    (mixedExtension u : TemperedDistribution ℝ ℂ) =
      TemperedDistribution.smulLeftCLM ℂ (fun x : ℝ => (x : ℂ))
        (TemperedDistribution.derivCLM ℂ
          (KNSGraphSpace.physical 2 (graphExtension u) : TemperedDistribution ℝ ℂ)) := by
  let P : HermiteScale 1 → Prop := fun w =>
    (mixedExtension w : TemperedDistribution ℝ ℂ) =
      TemperedDistribution.smulLeftCLM ℂ (fun x : ℝ => (x : ℂ))
        (TemperedDistribution.derivCLM ℂ
          (KNSGraphSpace.physical 2 (graphExtension w) : TemperedDistribution ℝ ℂ))
  change P u
  apply DenseRange.induction_on (p := P) (schwartzToHermiteScale_denseRange 1) u
  · exact isClosed_eq
      ((Lp.toTemperedDistributionCLM ℂ volume 2).continuous.comp mixedExtension.continuous)
      ((TemperedDistribution.smulLeftCLM ℂ (fun x : ℝ => (x : ℂ))).continuous.comp
        ((TemperedDistribution.derivCLM ℂ).continuous.comp
          ((Lp.toTemperedDistributionCLM ℂ volume 2).continuous.comp
            ((KNSGraphSpace.physical 2).continuous.comp graphExtension.continuous))))
  intro φ
  change (mixedExtension (schwartzToHermiteScale 1 φ) : TemperedDistribution ℝ ℂ) = _
  rw [mixedExtension_schwartz, graphExtension_schwartz,
    KNSGraphSpace.physical_schwartzEmbedding, mixedSchwartz_distribution]

/-- The one-dimensional distribution derivative and the unit directional
derivative are the same operator, with the existing sign convention. -/
theorem derivCLM_eq_lineDeriv (T : TemperedDistribution ℝ ℂ) :
    TemperedDistribution.derivCLM ℂ T = lineDerivOp (1 : ℝ) T := by
  ext φ
  simp only [TemperedDistribution.derivCLM_apply_apply,
    TemperedDistribution.lineDerivOp_apply_apply, MeyerGeneralProblem.KNSGraphOscillator.lineDeriv_one]

/-- The actual C1 representative's classical derivative agrees with the
distributional derivative of the actual physical L2 coordinate. -/
theorem representative_deriv_distribution (v : KNSGraphSpace 2) :
    TemperedDistribution.derivCLM ℂ
      (KNSGraphSpace.physical 2 v : TemperedDistribution ℝ ℂ) =
      ((representative_deriv_memLp v).toLp : TemperedDistribution ℝ ℂ) := by
  have hF : MemLp (KNSGraphSpace.representative 2 v) 2 :=
    (memLp_congr_ae (KNSGraphSpace.representative_ae (by omega : 1 ≤ 2) v)).mpr (Lp.memLp _)
  have he : hF.toLp = KNSGraphSpace.physical 2 v := by
    apply Lp.ext
    exact hF.coeFn_toLp.trans (KNSGraphSpace.representative_ae (by omega : 1 ≤ 2) v)
  rw [derivCLM_eq_lineDeriv, ← he]
  exact lineDeriv_L2_of_classical_deriv
    ((KNSGraphSpace.representative_contDiff_pair (by omega : 2 ≤ 2) v).1.differentiable
      (by norm_num)) hF (representative_deriv_memLp v)

/-- The completed mixed vector is the actual x times classical derivative
of the new representative almost everywhere. L2 membership is not assumed. -/
theorem mixed_representative_ae (v : KNSGraphSpace 2) :
    (fun x : ℝ => (x : ℂ) * deriv (KNSGraphSpace.representative 2 v) x) =ᵐ[volume]
      (mixedExtension ((TauCeti.twoPiHermiteHilbertBasis ℂ).repr (oscillator v)) : ℝ → ℂ) := by
  have hdist := mixedExtension_distribution
    ((TauCeti.twoPiHermiteHilbertBasis ℂ).repr (oscillator v))
  rw [graphExtension_oscillator, representative_deriv_distribution] at hdist
  have hae := ae_mul_eq_of_L2_distribution_eq _ _ (fun x : ℝ => (x : ℂ)) (by fun_prop) hdist
  filter_upwards [hae, (representative_deriv_memLp v).coeFn_toLp] with x hx hy
  rwa [hy] at hx

/-- The cheapest requested arbitrary-graph discriminator: at exactly
order two the actual representative's mixed derivative belongs to L2. -/
theorem representative_mixed_memLp (v : KNSGraphSpace 2) :
    MemLp (fun x : ℝ => (x : ℂ) * deriv (KNSGraphSpace.representative 2 v) x) 2 :=
  (memLp_congr_ae (mixed_representative_ae v)).mpr (Lp.memLp _)

/-- Its L2 vector is exactly the extended operator, not an unrelated
chosen L2 witness. -/
theorem representative_mixed_toLp (v : KNSGraphSpace 2) :
    (representative_mixed_memLp v).toLp =
      mixedExtension ((TauCeti.twoPiHermiteHilbertBasis ℂ).repr (oscillator v)) := by
  apply Lp.ext
  exact (representative_mixed_memLp v).coeFn_toLp.trans (mixed_representative_ae v)

/-- A single explicit positive constant bounds the squared L2 mixed norm
for every actual graph vector at order two, without any extra premise. -/
theorem exists_uniform_mixed_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ v : KNSGraphSpace 2,
      ‖(representative_mixed_memLp v).toLp‖^2 ≤ C * ‖v‖^2 := by
  let C : ℝ := 3 * (1 + (2 * Real.pi)^4) * (2 * Real.pi + 1/2)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C^2, sq_pos_of_pos hC, fun v => ?_⟩
  have hn : ‖(representative_mixed_memLp v).toLp‖ ≤ C * ‖v‖ := by
    rw [representative_mixed_toLp]
    calc
      _ ≤ (3 * (1 + (2 * Real.pi)^4)) *
          ‖(TauCeti.twoPiHermiteHilbertBasis ℂ).repr (oscillator v)‖ :=
        mixedExtension_norm_le _
      _ = (3 * (1 + (2 * Real.pi)^4)) * ‖oscillator v‖ := by
        rw [(TauCeti.twoPiHermiteHilbertBasis ℂ).repr.norm_map]
      _ ≤ (3 * (1 + (2 * Real.pi)^4)) * ((2 * Real.pi + 1/2) * ‖v‖) :=
        mul_le_mul_of_nonneg_left (oscillator_norm_le v) (by positivity)
      _ = C * ‖v‖ := by dsimp [C]; ring
  have hs := sq_le_sq₀ (norm_nonneg ((representative_mixed_memLp v).toLp))
    (mul_nonneg hC.le (norm_nonneg v)) |>.mpr hn
  simpa only [mul_pow] using hs

/-- The actual unrestricted Schwartz embedding is dense in graph order
two. This is derived from the positive-scale dense range and the proved
oscillator reconstruction, not assumed and not carrier-zero-constrained. -/
theorem schwartzEmbedding_two_denseRange :
    DenseRange (KNSGraphSpace.schwartzEmbedding 2) := by
  intro v
  rw [← graphExtension_oscillator v]
  let P : HermiteScale 1 → Prop := fun u =>
    graphExtension u ∈ closure (Set.range (KNSGraphSpace.schwartzEmbedding 2))
  apply DenseRange.induction_on (p := P) (schwartzToHermiteScale_denseRange 1)
    ((TauCeti.twoPiHermiteHilbertBasis ℂ).repr (oscillator v))
  · exact isClosed_closure.preimage graphExtension.continuous
  intro φ
  change graphExtension (schwartzToHermiteScale 1 φ) ∈ _
  rw [graphExtension_schwartz]
  exact subset_closure (Set.mem_range_self φ)

/-- The full arbitrary-graph mixed vector genuinely reduces to the old
Schwartz mixed vector on the existing embedding. -/
theorem embedded_full_mixed_agrees (φ : SchwartzMap ℝ ℂ) :
    (representative_mixed_memLp (KNSGraphSpace.schwartzEmbedding 2 φ)).toLp =
      mixedSchwartz φ := by
  rw [mixedSchwartz_eq_real_toLp]
  apply Lp.ext
  filter_upwards [(representative_mixed_memLp
    (KNSGraphSpace.schwartzEmbedding 2 φ)).coeFn_toLp,
    (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => x)
      (SchwartzMap.derivCLM ℂ ℂ φ)).coeFn_toLp 2 volume] with x hx hy
  rw [hx, hy]
  exact congrFun (embedded_mixed_eq φ) x

/-- The original precise Schwartz energy bound applies to the full
graph theorem's actual L2 mixed vector, not merely a parallel local copy. -/
theorem embedded_full_original_estimate (φ : SchwartzMap ℝ ℂ) :
    ‖(representative_mixed_memLp (KNSGraphSpace.schwartzEmbedding 2 φ)).toLp‖^2 ≤
      ‖φ.toLp 2 volume‖^2 +
        (‖(SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => x^2) φ).toLp 2 volume‖^2 +
          ‖(SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ φ)).toLp 2 volume‖^2)/2 := by
  rw [embedded_full_mixed_agrees, mixedSchwartz_eq_real_toLp]
  exact KNSMixedWeightedSchwartz.mixed_lp_norm_sq_le φ

/-- The full theorem handles the genuine zero graph input with zero L2
mixed vector, rather than excluding the zero branch. -/
theorem full_zero_mixed : (representative_mixed_memLp (0 : KNSGraphSpace 2)).toLp = 0 := by
  apply Lp.ext
  filter_upwards [(representative_mixed_memLp (0 : KNSGraphSpace 2)).coeFn_toLp,
    Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with x hx hz
  rw [hx, hz]
  exact congrFun zero_graph_mixed x

/-- The actual embedded Hermite controls are nonzero graph vectors. -/
theorem normalized_graph_nonzero (n : ℕ) :
    KNSGraphSpace.schwartzEmbedding 2 (normalizedHermiteSchwartz n) ≠ 0 := by
  intro hz
  have hp := congrArg (KNSGraphSpace.physical 2) hz
  rw [KNSGraphSpace.physical_schwartzEmbedding, map_zero] at hp
  have hn : ‖(normalizedHermiteSchwartz n).toLp 2 volume‖ = 1 := by
    rw [normalizedHermiteSchwartz_eq_twoPi, TauCeti.toLp_twoPiHermiteSchwartzMap]
    exact (TauCeti.orthonormal_twoPiHermiteFunctionLp ℂ).norm_eq_one n
  rw [hp, norm_zero] at hn
  norm_num at hn

/-- A genuine nonzero first-excited Hermite graph input exercises the
arbitrary-graph membership and its exact Schwartz reduction. -/
theorem nonzero_control :
    ∃ v : KNSGraphSpace 2, v ≠ 0 ∧
      MemLp (fun x : ℝ => (x : ℂ) * deriv (KNSGraphSpace.representative 2 v) x) 2 ∧
      (representative_mixed_memLp v).toLp = mixedSchwartz (normalizedHermiteSchwartz 1) :=
  ⟨KNSGraphSpace.schwartzEmbedding 2 (normalizedHermiteSchwartz 1),
    normalized_graph_nonzero 1, representative_mixed_memLp _,
    embedded_full_mixed_agrees _⟩

/-- Packaged exact discriminator: a single positive C is chosen before
every graph vector; actual mixed membership and its squared L2 bound
are both conclusions at exactly graph order two. -/
theorem exists_uniform_mixed_membership_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ v : KNSGraphSpace 2,
      ∃ hM : MemLp (fun x : ℝ => (x : ℂ) *
        deriv (KNSGraphSpace.representative 2 v) x) 2,
        ‖hM.toLp‖^2 ≤ C * ‖v‖^2 := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_mixed_bound
  exact ⟨C, hC, fun v => ⟨representative_mixed_memLp v, hbound v⟩⟩

end
end MeyerGeneralProblem.KNSGraphMixedCompletion
