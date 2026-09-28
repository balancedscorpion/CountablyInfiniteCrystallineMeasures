module

public import MeyerGeneralProblem.Cardinal.Adaptive.HeadNativeBounds
public import Mathlib.Analysis.Normed.Module.WeakDual
import all Mathlib.Analysis.Normed.Module.WeakDual

@[expose] public section

/-! # Sequential weak compactness in the original Hermite scale -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open Set Filter TopologicalSpace
open scoped Topology FourierTransform

/-- The original Hermite scale is separable through its actual countable dense
Hermite basis, independent of the integer order used for decoding. -/
theorem nativeScale_separable (p : ℤ) : SeparableSpace (HermiteScale p) := by
  have h := ((countable_range (coefficientAtom : ℕ → CoefficientSpace ℕ)).isSeparable.span (R := ℂ)).closure
  change IsSeparable (↑(Submodule.span ℂ (range (coefficientAtom : ℕ → CoefficientSpace ℕ))).topologicalClosure : Set (CoefficientSpace ℕ)) at h
  rw [coefficientAtom_dense_span] at h
  exact isSeparable_univ_iff.mp h

/-- The bilinear native functional represented by an actual negative-order vector. -/
def nativeWeakFunctional (p : ℕ) (T : HermiteScale (-(p:ℤ))) :
    StrongDual ℂ (HermiteScale (p:ℤ)) :=
  InnerProductSpace.toDual ℂ (HermiteScale (p:ℤ)) (star T)

/-- The functional keeps exactly the original negative-scale norm. -/
theorem nativeWeakFunctional_norm (p : ℕ) (T : HermiteScale (-(p:ℤ))) :
    ‖nativeWeakFunctional p T‖ = ‖T‖ := by simp only [nativeWeakFunctional,LinearIsometryEquiv.norm_map,norm_star]

/-- This is the original bilinear Hermite pairing, not the sesquilinear pairing. -/
theorem nativeWeakFunctional_apply (p : ℕ) (T : HermiteScale (-(p:ℤ)))
    (u : HermiteScale (p:ℤ)) : nativeWeakFunctional p T u = hermiteScalePairing (p:ℤ) T u := by
  rw [nativeWeakFunctional,InnerProductSpace.toDual_apply_apply,hermiteScalePairing,lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  simp [RCLike.inner_apply,mul_comm]

/-- Sequential Banach-Alaoglu and the actual Riesz isometry produce a bounded
original native vector and weak convergence against every positive native vector.
No coefficientwise limit or source-realization hypothesis is supplied. -/
theorem exists_native_weak_subsequence (p : ℕ) (T : ℕ → HermiteScale (-(p:ℤ)))
    (B : ℝ) (hB : ∀ n, ‖T n‖ ≤ B) :
    ∃ U : HermiteScale (-(p:ℤ)), ‖U‖ ≤ B ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ u : HermiteScale (p:ℤ), Tendsto (fun n => hermiteScalePairing (p:ℤ) (T (φ n)) u)
        atTop (𝓝 (hermiteScalePairing (p:ℤ) U u)) := by
  let := nativeScale_separable (p:ℤ)
  let V (n : ℕ) : WeakDual ℂ (HermiteScale (p:ℤ)) :=
    WeakDual.toStrongDual.symm (nativeWeakFunctional p (T n))
  have hmem (n : ℕ) : V n ∈ WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 B := by
    simpa only [V,mem_preimage,LinearEquiv.apply_symm_apply,Metric.mem_closedBall,dist_zero_right,
      nativeWeakFunctional_norm] using hB n
  obtain ⟨v,hv,φ,hφ,hlim⟩ := (WeakDual.isSeqCompact_closedBall ℂ (HermiteScale (p:ℤ)) 0 B) hmem
  let U : HermiteScale (-(p:ℤ)) := star ((InnerProductSpace.toDual ℂ (HermiteScale (p:ℤ))).symm
    (WeakDual.toStrongDual v))
  have he : nativeWeakFunctional p U = WeakDual.toStrongDual v := by
    simp only [nativeWeakFunctional,U,star_star,LinearIsometryEquiv.apply_symm_apply]
  refine ⟨U,?_,φ,hφ,fun u => ?_⟩
  · rw [← nativeWeakFunctional_norm p U,he]
    simpa only [mem_preimage,Metric.mem_closedBall,dist_zero_right] using hv
  · have hh := ((WeakDual.eval_continuous u).tendsto v).comp hlim
    change Tendsto (fun n => nativeWeakFunctional p (T (φ n)) u)
      atTop (𝓝 ((WeakDual.toStrongDual v) u)) at hh
    simpa only [← he,nativeWeakFunctional_apply] using hh

/-- The native weak subsequence converges on every complete Schwartz test. -/
theorem exists_native_distribution_subsequence (p : ℕ) (T : ℕ → HermiteScale (-(p:ℤ)))
    (B : ℝ) (hB : ∀ n, ‖T n‖ ≤ B) :
    ∃ U : HermiteScale (-(p:ℤ)), ‖U‖ ≤ B ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ f : SchwartzMap ℝ ℂ, Tendsto (fun n => hermiteScaleDistribution p (T (φ n)) f)
        atTop (𝓝 (hermiteScaleDistribution p U f)) := by
  obtain ⟨U,hU,φ,hφ,hlim⟩ := exists_native_weak_subsequence p T B hB
  exact ⟨U,hU,φ,hφ,fun f => by simpa only [hermiteScaleDistribution_apply] using hlim (schwartzToHermiteScale p f)⟩

/-- Exact eventual equality of the carrier in every compact window, as needed
for the finite endpoint approximants. It refers to whole sets, not coefficient arrays. -/
def EventuallyLocallyEqualCarriers (S : ℕ → LocallyFiniteCarrier) (L : LocallyFiniteCarrier) : Prop :=
  ∀ K : Set ℝ, IsCompact K → ∀ᶠ n : ℕ in atTop, (S n).carrier ∩ K = L.carrier ∩ K

/-- Local carrier equality survives subsequence extraction without changing its limit. -/
theorem EventuallyLocallyEqualCarriers.subseq {S : ℕ → LocallyFiniteCarrier} {L : LocallyFiniteCarrier}
    (h : EventuallyLocallyEqualCarriers S L) (φ : ℕ → ℕ) (hφ : StrictMono φ) :
    EventuallyLocallyEqualCarriers (S ∘ φ) L := by
  intro K hK
  exact hφ.tendsto_atTop.eventually (h K hK)

/-- Actual atomic records pass to a whole Schwartz weak limit when the actual
carriers agree eventually in every compact window. This excludes new derivatives. -/
theorem atomicOnCarrier_of_weak_limit (S : ℕ → LocallyFiniteCarrier) (L : LocallyFiniteCarrier)
    (T : ℕ → TemperedDistribution ℝ ℂ) (U : TemperedDistribution ℝ ℂ)
    (hcarrier : EventuallyLocallyEqualCarriers S L) (hT : ∀ n, AtomicOnCarrier (S n) (T n))
    (hlim : ∀ f : SchwartzMap ℝ ℂ, Tendsto (fun n => T n f) atTop (𝓝 (U f))) :
    AtomicOnCarrier L U := by
  have hcompact (f : SchwartzMap ℝ ℂ) (hf : HasCompactSupport f)
      (hzero : SchwartzVanishesOn L f) : U f=0 := by
    have hevent : ∀ᶠ n : ℕ in atTop, T n f=0 := by
      filter_upwards [hcarrier (tsupport f) hf] with n hn
      apply hT n f
      intro x hx
      by_cases hxs : x ∈ tsupport f
      · have hxL : x ∈ L.carrier ∩ tsupport f := by rw [← hn]; exact ⟨hx,hxs⟩
        exact hzero x hxL.1
      · by_contra he
        exact hxs (subset_tsupport f he)
    have hz : Tendsto (fun n => T n f) atTop (𝓝 0) :=
      tendsto_const_nhds.congr' (hevent.mono fun n hn => hn.symm)
    exact tendsto_nhds_unique (hlim f) hz
  intro f hf
  have hz : Tendsto (fun N : ℕ => U (compactSchwartzApproximation N f)) atTop (𝓝 0) := by
    have he (N : ℕ) := hcompact _ (compactSchwartzApproximation_hasCompactSupport N f)
      (compactSchwartzApproximation_preserves_vanishing L N f hf)
    simpa only [he] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℂ)) atTop (𝓝 0))
  exact tendsto_nhds_unique ((U.continuous.tendsto f).comp (compactSchwartzApproximation_tendsto f)) hz

/-- A genuine original-norm bound on actual finite sources, exact eventual
carrier identities, and a fixed nonzero Schwartz observation produce a nonzero
whole native source with both atomic records. The Fourier eigenvalue is retained. -/
theorem exists_native_atomic_limit (p : ℕ) (T : ℕ → HermiteScale (-(p:ℤ)))
    (B : ℝ) (hB : ∀ n, ‖T n‖ ≤ B)
    (S A : ℕ → LocallyFiniteCarrier) (L K : LocallyFiniteCarrier)
    (hS : EventuallyLocallyEqualCarriers S L) (hA : EventuallyLocallyEqualCarriers A K)
    (hphys : ∀ n, AtomicOnCarrier (S n) (hermiteScaleDistribution p (T n)))
    (hspec : ∀ n, AtomicOnCarrier (A n) (𝓕 (hermiteScaleDistribution p (T n))))
    (f₀ : SchwartzMap ℝ ℂ) (c : ℂ) (hc : c ≠ 0)
    (hobs : ∀ n, hermiteScaleDistribution p (T n) f₀ = c)
    (eigenvalue : ℂ) (heigen : ∀ n, 𝓕 (hermiteScaleDistribution p (T n)) = eigenvalue • hermiteScaleDistribution p (T n)) :
    ∃ U : HermiteScale (-(p:ℤ)), ‖U‖ ≤ B ∧ U ≠ 0 ∧
      AtomicOnCarrier L (hermiteScaleDistribution p U) ∧
      AtomicOnCarrier K (𝓕 (hermiteScaleDistribution p U)) ∧
      hermiteScaleDistribution p U f₀ = c ∧
      𝓕 (hermiteScaleDistribution p U) = eigenvalue • hermiteScaleDistribution p U := by
  obtain ⟨U,hU,φ,hφ,hlim⟩ := exists_native_distribution_subsequence p T B hB
  have hFlim (f : SchwartzMap ℝ ℂ) :
      Tendsto (fun n => 𝓕 (hermiteScaleDistribution p (T (φ n))) f) atTop
        (𝓝 (𝓕 (hermiteScaleDistribution p U) f)) := by
    simpa only [TemperedDistribution.fourier_apply] using hlim (𝓕 f)
  have hobsU : hermiteScaleDistribution p U f₀=c := by
    have hconst : Tendsto (fun n => hermiteScaleDistribution p (T (φ n)) f₀) atTop (𝓝 c) := by
      simpa only [hobs] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => c) atTop (𝓝 c))
    exact tendsto_nhds_unique (hlim f₀) hconst
  refine ⟨U,hU,?_,?_,?_,hobsU,?_⟩
  · intro hu
    apply hc
    rw [hu] at hobsU
    have hz : hermiteScaleDistribution p 0=0 := map_zero (hermiteScaleDistributionCLM p)
    simpa only [hz,zero_apply] using hobsU.symm
  · exact atomicOnCarrier_of_weak_limit (S ∘ φ) L _ _ (hS.subseq φ hφ) (fun n => hphys (φ n)) hlim
  · exact atomicOnCarrier_of_weak_limit (A ∘ φ) K _ _ (hA.subseq φ hφ) (fun n => hspec (φ n)) hFlim
  · ext f
    have heigenvalue := (hlim f).const_mul eigenvalue
    have he (n : ℕ) : 𝓕 (hermiteScaleDistribution p (T (φ n))) f =
        eigenvalue * hermiteScaleDistribution p (T (φ n)) f := by rw [heigen]; rfl
    have hsame := hFlim f
    simp only [he] at hsame
    exact tendsto_nhds_unique hsame heigenvalue

end
end MeyerGeneralProblem.Adaptive
