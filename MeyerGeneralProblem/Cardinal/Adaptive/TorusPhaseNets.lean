module

public import MeyerGeneralProblem.Cardinal.Adaptive.ReciprocalLaurentPolynomial
public import MeyerGeneralProblem.Cardinal.Adaptive.CatalogueNonresonance
public import Mathlib.Analysis.Fourier.AddCircleMulti
import all Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.RingTheory.Localization.Module
import all Mathlib.RingTheory.Localization.Module
public import MeyerGeneralProblem.Cardinal.Adaptive.TorusFlowDensity

@[expose] public section

/-!
# Actual reciprocal frequencies and finite torus phases

The frequencies are the literal half-scaled forward and reciprocal coordinates.
Integer relations are excluded using the established quantitative Laurent law.
-/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal

/-- Every nonzero reciprocal coefficient table has a null zero event under the genuine law. -/
theorem reciprocalLaurent_coordinate_zero_null {q : ℕ} (hq : 0 < q)
    (f : Fin q → ℕ+) (hf : Function.Injective f) (a b : Fin q → ℝ)
    (d : ℝ) (hd : 0 < d) (hc : (∃ i, d ≤ |a i|) ∨ ∃ i, d ≤ |b i|) :
    scaleProbability {s | reciprocalLaurentValue a b (fun i => s (f i)) = 0} = 0 := by
  have he : 0 < (1 : ℝ)/(2*(q : ℝ)) := by positivity
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal
      (16*(q : ℝ)*((2^q*(1/(n+1 : ℝ)))/d)^((1 : ℝ)/(2*(q : ℝ))))) atTop (𝓝 0) := by
    have hu : Tendsto (fun n : ℕ => 1/(n+1 : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have ht := (Real.continuous_rpow_const he.le).continuousAt.tendsto.comp
      ((hu.const_mul (2^q : ℝ)).div_const d)
    have ht' := ENNReal.continuous_ofReal.continuousAt.tendsto.comp (ht.const_mul (16*(q : ℝ)))
    simpa only [Function.comp_def, mul_zero, zero_div, Real.zero_rpow he.ne', ENNReal.ofReal_zero] using ht'
  apply le_antisymm ?_ bot_le
  apply ge_of_tendsto hlim
  apply Eventually.of_forall
  intro n
  have hsub : {s : ℕ+ → ℝ | reciprocalLaurentValue a b (fun i => s (f i)) = 0} ⊆
      {s | |reciprocalLaurentValue a b (fun i => s (f i))| < 1/(n+1 : ℝ)} := by
    intro s hs
    change reciprocalLaurentValue a b (fun i => s (f i)) = 0 at hs
    change |reciprocalLaurentValue a b (fun i => s (f i))| < 1/(n+1 : ℝ)
    rw [hs, abs_zero]
    positivity
  exact (measure_mono hsub).trans ((reciprocalLaurent_coordinate_sublevel_le hq f hf a b d
    (1/(n+1 : ℝ)) hd (by positivity) hc).trans (min_le_right _ _))

/-- The frequencies of the actual physical anti-periods, in normalized torus coordinates. -/
def prefixTorusFrequency {M : ℕ} (s : ℕ+ → ℝ) (b : Fin M × ReciprocalSign) : ℝ :=
  labelScale s (prefixScaleIndex b.1,b.2)/2

/-- A literal integer frequency relation. -/
def prefixFrequencyRelation {M : ℕ} (k : Fin M × ReciprocalSign → ℤ) (s : ℕ+ → ℝ) : ℝ :=
  ∑ b, (k b : ℝ)*prefixTorusFrequency s b

/-- Integer frequency relations are exactly the original reciprocal Laurent sums, divided by two. -/
theorem prefixFrequencyRelation_eq_laurent {M : ℕ} (k : Fin M × ReciprocalSign → ℤ)
    (s : ℕ+ → ℝ) :
    prefixFrequencyRelation k s = reciprocalLaurentValue
      (fun i => (k (i,.forward) : ℝ)) (fun i => (k (i,.reciprocal) : ℝ))
      (fun i => s (prefixScaleIndex i))/2 := by
  have hsign : (Finset.univ : Finset ReciprocalSign) = {.forward,.reciprocal} := by decide
  simp only [prefixFrequencyRelation, Fintype.sum_prod_type,
    reciprocalLaurentValue, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  simp [hsign, prefixTorusFrequency, labelScale]
  ring

/-- No nontrivial integer relation survives almost surely, including the dependent reciprocal pair. -/
theorem ae_prefix_frequency_no_integer_relations (M : ℕ) :
    ∀ᵐ s ∂scaleProbability, ∀ k : Fin M × ReciprocalSign → ℤ,
      prefixFrequencyRelation k s = 0 → k = 0 := by
  apply ae_all_iff.mpr
  intro k
  by_cases hk : k = 0
  · exact Eventually.of_forall (fun _ _ => hk)
  have hnonzero : ∃ b, k b ≠ 0 := by
    by_contra! h
    exact hk (funext h)
  obtain ⟨⟨i,σ⟩,hi⟩ := hnonzero
  have hM : 0 < M := Nat.zero_lt_of_lt i.isLt
  have hc : (∃ i, (1 : ℝ) ≤ |(k (i,.forward) : ℝ)|) ∨
      ∃ i, (1 : ℝ) ≤ |(k (i,.reciprocal) : ℝ)| := by
    cases σ with
    | forward => exact Or.inl ⟨i,one_le_abs_int_cast hi⟩
    | reciprocal => exact Or.inr ⟨i,one_le_abs_int_cast hi⟩
  have hf : Function.Injective (@prefixScaleIndex M) := by
    intro i j hij
    apply Fin.ext
    have h := congrArg Subtype.val hij
    change i.val+1 = j.val+1 at h
    omega
  have hnull := reciprocalLaurent_coordinate_zero_null hM prefixScaleIndex hf
    (fun i => (k (i,.forward) : ℝ)) (fun i => (k (i,.reciprocal) : ℝ)) 1 (by norm_num) hc
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with s hs
  intro hzero
  apply False.elim
  apply hs
  rw [prefixFrequencyRelation_eq_laurent, div_eq_zero_iff] at hzero
  simpa using hzero

/-- The actual finite reciprocal frequency family is rationally linearly independent a.e. -/
theorem ae_prefixTorusFrequency_rationally_independent (M : ℕ) :
    ∀ᵐ s ∂scaleProbability, LinearIndependent ℚ (@prefixTorusFrequency M s) := by
  filter_upwards [ae_prefix_frequency_no_integer_relations M] with s hs
  apply (LinearIndependent.iff_fractionRing ℤ ℚ).mp
  apply Fintype.linearIndependent_iff.mpr
  intro k hk i
  have hz : prefixFrequencyRelation k s = 0 := by
    simpa only [prefixFrequencyRelation, zsmul_eq_mul] using hk
  exact congrFun (hs k hz) i

/-- All finite prefixes obey the same rational independence event. -/
theorem ae_all_prefix_frequencies_rationally_independent :
    ∀ᵐ s ∂scaleProbability, ∀ M : ℕ, LinearIndependent ℚ (@prefixTorusFrequency M s) :=
  ae_all_iff.mpr ae_prefixTorusFrequency_rationally_independent

/-- The full frequency tuple is measurable under the actual product scale law. -/
theorem measurable_prefixTorusFrequency (M : ℕ) :
    Measurable (fun s : ℕ+ → ℝ => @prefixTorusFrequency M s) := by
  apply measurable_pi_lambda
  intro b
  simp only [prefixTorusFrequency, labelScale_eq_scaleFactor]
  exact ((measurable_scaleFactor b.2).comp (measurable_pi_apply (prefixScaleIndex b.1))).div_const 2

/-- The genuine bounded-time strict-net event for the first M reciprocal frequencies. -/
def prefixSegmentNetEvent (M : ℕ) (H₀ H η : ℝ) : Set (ℕ+ → ℝ) :=
  (fun s => @prefixTorusFrequency M s) ⁻¹' torusSegmentNet H₀ H η

/-- Compactness-based openness gives actual measurability, without an uncountable-intersection assumption. -/
theorem prefixSegmentNetEvent_measurable (M : ℕ) (H₀ H η : ℝ) :
    MeasurableSet (prefixSegmentNetEvent M H₀ H η) :=
  (torusSegmentNet_isOpen H₀ H η).measurableSet.preimage (measurable_prefixTorusFrequency M)

/-- The original real flow and every forward tail are dense almost surely. -/
theorem ae_prefix_flow_forward_dense (M : ℕ) (H₀ : ℝ) :
    ∀ᵐ s ∂scaleProbability,
      Dense (torusLinearFlow (@prefixTorusFrequency M s) '' Ici H₀) := by
  filter_upwards [ae_prefix_frequency_no_integer_relations M] with s hs
  exact dense_forward_real_flow _ (torusLinearFlow_denseRange _ hs) H₀

/-- For almost every actual scale tuple, some finite segment after H0 is a strict eta-net. -/
theorem ae_exists_prefix_segment_net (M : ℕ) (H₀ η : ℝ) (hη : 0 < η) :
    ∀ᵐ s ∂scaleProbability, ∃ H : ℝ, H₀ ≤ H ∧ s ∈ prefixSegmentNetEvent M H₀ H η := by
  filter_upwards [ae_prefix_frequency_no_integer_relations M] with s hs
  exact exists_forward_flow_segment_net _ (torusLinearFlow_denseRange _ hs) H₀ η hη

/-- Increasing the endpoint only improves the actual net event. -/
theorem prefixSegmentNetEvent_mono (M : ℕ) (H₀ η : ℝ) :
    Monotone (fun H => prefixSegmentNetEvent M H₀ H η) :=
  fun _ _ h => preimage_mono (torusSegmentNet_mono H₀ η h)

/-- A deterministic upper translation bound pays any prescribed positive probability budget. -/
theorem exists_prefix_segment_net_failure_bound (M : ℕ) (H₀ η ε : ℝ)
    (hη : 0 < η) (hε : 0 < ε) :
    ∃ H : ℝ, H₀ ≤ H ∧ scaleProbability (prefixSegmentNetEvent M H₀ H η)ᶜ ≤ ENNReal.ofReal ε := by
  let B : ℕ → Set (ℕ+ → ℝ) := fun n => (prefixSegmentNetEvent M H₀ (H₀+n) η)ᶜ
  have hnull : scaleProbability (⋂ n, B n) = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [ae_exists_prefix_segment_net M H₀ η hη] with s hs
    obtain ⟨H,hH,hnet⟩ := hs
    obtain ⟨n,hn⟩ := exists_nat_ge (H-H₀)
    have hn' : H ≤ H₀+(n : ℝ) := by linarith
    intro hmem
    exact mem_iInter.mp hmem n ((prefixSegmentNetEvent_mono M H₀ η hn') hnet)
  have hmono : Antitone B := by
    intro n m hnm
    apply compl_subset_compl.mpr
    apply prefixSegmentNetEvent_mono
    have hnm' : (n : ℝ) ≤ m := by exact_mod_cast hnm
    linarith
  have hlim := tendsto_measure_iInter_atTop (μ := scaleProbability)
    (fun n : ℕ => (prefixSegmentNetEvent_measurable M H₀ (H₀+n) η).compl.nullMeasurableSet)
    hmono ⟨0,measure_ne_top _ _⟩
  rw [hnull] at hlim
  obtain ⟨n,hn⟩ := (hlim.eventually (Iio_mem_nhds (ENNReal.ofReal_pos.mpr hε))).exists
  exact ⟨H₀+n,le_add_of_nonneg_right (Nat.cast_nonneg n),hn.le⟩

/-- Accepted stage net tolerance and geometric failure budget, chosen without future gaps. -/
theorem exists_stage_segment_net (M : ℕ) (H₀ η : ℝ) (hη : 0 < η) :
    ∃ H : ℝ, H₀ ≤ H ∧
      scaleProbability (prefixSegmentNetEvent M H₀ H (η/4))ᶜ ≤
        ENNReal.ofReal ((2 : ℝ)^(-(M+4 : ℤ))) :=
  exists_prefix_segment_net_failure_bound M H₀ (η/4) _ (by positivity) (by positivity)

/-- A normalized circle error becomes a physical phase error when the frequency is at least one quarter. -/
theorem physical_phase_error_of_circle_dist (ν h a η : ℝ) (hν : 1/4 ≤ ν) (hη : 0 < η)
    (hd : dist ((ν*h : ℝ) : UnitAddCircle) ((ν*a : ℝ) : UnitAddCircle) < η/4) :
    ∃ n : ℤ, |h-a-(n : ℝ)/ν| < η := by
  have hνpos : 0 < ν := by linarith
  rw [dist_eq_norm, ← QuotientAddGroup.mk_sub, UnitAddCircle.norm_eq] at hd
  let n : ℤ := round (ν*h-ν*a)
  refine ⟨n, ?_⟩
  have heq : h-a-(n : ℝ)/ν = (ν*h-ν*a-(n : ℝ))/ν := by field_simp
  rw [heq, abs_div, abs_of_pos hνpos]
  apply (div_lt_iff₀ hνpos).mpr
  have hmul := mul_le_mul_of_nonneg_left hν hη.le
  have hd' : |ν*h-ν*a-(n : ℝ)| < η/4 := hd
  nlinarith

/-- The actual strict torus net supplies all prescribed physical phases simultaneously,
with the accepted factor four and genuine anti-periods two over the label scale. -/
theorem prefix_net_supplies_physical_phases (M : ℕ) (s : ℕ+ → ℝ)
    (hs : ∀ i, s i ∈ Icc (1 : ℝ) 2) (H₀ H η : ℝ) (hη : 0 < η)
    (hnet : s ∈ prefixSegmentNetEvent M H₀ H (η/4))
    (a : Fin M × ReciprocalSign → ℝ) :
    ∃ h : ℝ, H₀ ≤ h ∧ h ≤ H ∧ ∀ b : Fin M × ReciprocalSign, ∃ n : ℤ,
      |h-a b-(n : ℝ)*(2/labelScale s (prefixScaleIndex b.1,b.2))| < η := by
  let z : UnitAddTorus (Fin M × ReciprocalSign) := fun b =>
    ((prefixTorusFrequency s b*a b : ℝ) : UnitAddCircle)
  obtain ⟨h,hh0,hhH,hh⟩ := hnet z
  refine ⟨h,hh0,hhH,?_⟩
  intro b
  have hscale := labelScale_mem_Icc s hs (prefixScaleIndex b.1,b.2)
  have hν : 1/4 ≤ prefixTorusFrequency s b := by unfold prefixTorusFrequency; linarith [hscale.1]
  have hdist : dist ((prefixTorusFrequency s b*h : ℝ) : UnitAddCircle)
      ((prefixTorusFrequency s b*a b : ℝ) : UnitAddCircle) < η/4 := by
    simpa only [torusLinearFlow, AddMonoidHom.coe_mk, ZeroHom.coe_mk, z, mul_comm] using
      (dist_le_pi_dist (torusLinearFlow (prefixTorusFrequency s) h) z b).trans_lt hh
  obtain ⟨n,hn⟩ := physical_phase_error_of_circle_dist _ h (a b) η hν hη hdist
  refine ⟨n, ?_⟩
  have heq : (n : ℝ)/prefixTorusFrequency s b = (n : ℝ)*(2/labelScale s (prefixScaleIndex b.1,b.2)) := by
    unfold prefixTorusFrequency
    rw [div_div_eq_mul_div]
    ring
  rwa [heq] at hn

end
end MeyerGeneralProblem.Adaptive
