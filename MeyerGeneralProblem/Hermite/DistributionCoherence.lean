module

public import MeyerGeneralProblem.Endpoint.IntrinsicFixedOrder
public import MeyerGeneralProblem.Endpoint.LayerMonotonicity
public import MeyerGeneralProblem.Distribution.MeyerSpace
public import MeyerGeneralProblem.Hermite.ScaleEmbedding
public import MeyerGeneralProblem.Hermite.Exhaustion

@[expose] public section

/-!
# Intrinsic fixed-order Meyer layers in the distributional Meyer space

The intrinsic physical support annihilates the full positive-scale vanishing
subspace, hence in particular every carrier-vanishing Schwartz test.  Fourier
coherence then realizes the intrinsic fixed-order Meyer layer as an injective
continuous-linear subspace of the distributional Meyer space.

Conversely, compact physical cutoffs of a locally atomic distribution are
finite carrier Dirac sums.  Their Hermite coefficient errors have a uniform
polynomial envelope.  Placing that envelope in a sufficiently negative scale
proves strong convergence there and hence intrinsic physical support.  A
common-order argument for the distribution and its Fourier transform proves
that the positive intrinsic layers cover the entire distributional Meyer
space.  No same-order reverse-support identification is asserted.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter
open scoped Topology

/-- Intrinsic fixed-order physical support gives the distributional
vanishing-ideal condition. -/
theorem atomicOnCarrier_hermiteScaleDistribution_of_mem_fixedOrderPhysicalSupport
    (S : LocallyFiniteCarrier) (m : ℕ) (hm : 1 ≤ m)
    (T : HermiteScale (-(m : ℤ)))
    (hT : T ∈ fixedOrderPhysicalSupport S m hm) :
    AtomicOnCarrier S (hermiteScaleDistribution m T) := by
  intro f hf
  exact locallyFiniteSupportedHermiteMeasureSubspace_annihilates_vanishingSchwartz
    m hm S T hT f hf

/-- The fixed-order Meyer layer realizes inside the genuine distributional
Meyer space with no total-variation growth assumption. -/
theorem hermiteScaleDistribution_mem_distributionalMeyerSpace
    (S : LocallyFiniteCarrier) (m : ℕ) (hm : 1 ≤ m)
    (T : HermiteScale (-(m : ℤ)))
    (hT : T ∈ FixedOrderMeyerLayer S m hm) :
    hermiteScaleDistribution m T ∈ DistributionalMeyerSpace S := by
  obtain ⟨hphysical, hfourier⟩ :=
    (mem_fixedOrderMeyerLayer_iff S m hm T).mp hT
  rw [mem_distributionalMeyerSpace_iff]
  constructor
  · exact atomicOnCarrier_hasLocallyAtomicAction S _
      (atomicOnCarrier_hermiteScaleDistribution_of_mem_fixedOrderPhysicalSupport
        S m hm T hphysical)
  · rw [← hermiteFourier_represents_distributionalFourier]
    exact atomicOnCarrier_hasLocallyAtomicAction S _
      (atomicOnCarrier_hermiteScaleDistribution_of_mem_fixedOrderPhysicalSupport
        S m hm (hermiteFourier (-(m : ℤ)) T) hfourier)

/-- Continuous-linear realization of the intrinsic fixed-order Meyer layer
inside the distributional Meyer space. -/
def fixedOrderMeyerLayerToDistributionalMeyerSpace
    (S : LocallyFiniteCarrier) (m : ℕ) (hm : 1 ≤ m) :
    FixedOrderMeyerLayer S m hm →L[ℂ] DistributionalMeyerSpace S :=
  ((hermiteScaleDistributionCLM m).comp
    (FixedOrderMeyerLayer S m hm).subtypeL).codRestrict
    (DistributionalMeyerSpace S) fun T =>
      hermiteScaleDistribution_mem_distributionalMeyerSpace
        S m hm T T.property

@[simp]
theorem fixedOrderMeyerLayerToDistributionalMeyerSpace_apply
    (S : LocallyFiniteCarrier) (m : ℕ) (hm : 1 ≤ m)
    (T : FixedOrderMeyerLayer S m hm) :
    (fixedOrderMeyerLayerToDistributionalMeyerSpace S m hm T :
        TemperedDistribution ℝ ℂ) =
      hermiteScaleDistribution m (T : HermiteScale (-(m : ℤ))) :=
  rfl

/-- The fixed-order realization loses no Hermite-scale vector. -/
theorem fixedOrderMeyerLayerToDistributionalMeyerSpace_injective
    (S : LocallyFiniteCarrier) (m : ℕ) (hm : 1 ≤ m) :
    Function.Injective (fixedOrderMeyerLayerToDistributionalMeyerSpace S m hm) := by
  intro T U hTU
  apply Subtype.ext
  apply hermiteScaleDistribution_injective m
  exact congrArg (fun V : DistributionalMeyerSpace S =>
    (V : TemperedDistribution ℝ ℂ)) hTU

/-- The Schwartz-to-positive-scale map retains every Schwartz function. -/
theorem schwartzToHermiteScale_injective (m : ℕ) :
    Function.Injective (schwartzToHermiteScale m) := by
  intro f g hfg
  apply SchwartzMap.ext
  intro x
  rw [← hermite_reconstruction f x, ← hermite_reconstruction g x]
  apply tsum_congr
  intro n
  have hc := congrArg
    (fun u : HermiteScale (m : ℤ) => rawHermiteCoefficients (m : ℤ) u n) hfg
  simp only [schwartzToHermiteScale_raw] at hc
  rw [hc]

private theorem schwartzHermiteCoefficients_normalizedHermiteSchwartz_unit
    (i j : ℕ) :
    schwartzHermiteCoefficients (normalizedHermiteSchwartz i) j =
      if j = i then 1 else 0 := by
  rw [schwartzHermiteCoefficients_apply_repr,
    normalizedHermiteSchwartz_eq_twoPi,
    TauCeti.toLp_twoPiHermiteSchwartzMap]
  have hb : TauCeti.twoPiHermiteFunctionLp ℂ i =
      (TauCeti.twoPiHermiteHilbertBasis ℂ) i := by
    exact (congrFun (TauCeti.coe_twoPiHermiteHilbertBasis (𝕜 := ℂ)) i).symm
  rw [hb, HilbertBasis.repr_self]
  simp [lp.single_apply, Pi.single_apply]

private theorem coefficientAtom_apply_unit (i j : ℕ) :
    coefficientAtom i j = if j = i then 1 else 0 := by
  have h := congrArg (fun u : CoefficientSpace ℕ => u j)
    ((coefficientHilbertBasis ℕ).repr_self i)
  change coefficientAtom i j =
    (lp.single (E := fun _ : ℕ => ℂ) 2 i (1 : ℂ)) j at h
  simpa [lp.single_apply, Pi.single_apply] using h

private theorem schwartzToHermiteScale_inverseWeightHermite
    (m i : ℕ) :
    schwartzToHermiteScale m
        ((hermiteScaleWeight (m : ℤ) i : ℂ)⁻¹ • normalizedHermiteSchwartz i) =
      coefficientAtom i := by
  apply Subtype.ext
  funext j
  rw [map_smul]
  change (hermiteScaleWeight (m : ℤ) i : ℂ)⁻¹ *
      schwartzToHermiteScale m (normalizedHermiteSchwartz i) j =
    coefficientAtom i j
  rw [schwartzToHermiteScale_apply, normalizeHermiteCoefficients,
    schwartzHermiteCoefficients_normalizedHermiteSchwartz_unit,
    coefficientAtom_apply_unit]
  by_cases hji : j = i
  · subst j
    simp only [ite_true, mul_one]
    apply inv_mul_cancel₀
    exact_mod_cast hermiteScaleWeight_ne_zero (m : ℤ) i
  · simp [hji]

/-- Schwartz functions are dense in the unrestricted positive Hermite
scale.  This does not assert density after imposing all carrier zeros. -/
theorem schwartzToHermiteScale_denseRange (m : ℕ) :
    DenseRange (schwartzToHermiteScale m) := by
  have hrange :
      Submodule.span ℂ (Set.range (coefficientAtom : ℕ → HermiteScale (m : ℤ))) ≤
        (schwartzToHermiteScale m).range := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨(hermiteScaleWeight (m : ℤ) i : ℂ)⁻¹ •
      normalizedHermiteSchwartz i,
      schwartzToHermiteScale_inverseWeightHermite m i⟩
  change Dense ((schwartzToHermiteScale m).range : Set (HermiteScale (m : ℤ)))
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  apply top_unique
  rw [← coefficientAtom_dense_span]
  exact Submodule.topologicalClosure_mono hrange

/-- The carrier-constrained positive-scale realization.  Its range lies in
the entire positive-scale vanishing subspace, but density of this range is
a separate approximation obligation. -/
def schwartzVanishingToHermiteVanishing
    (S : LocallyFiniteCarrier) (m : ℕ) (hm : 1 ≤ m) :
    schwartzVanishingSubmodule S →L[ℂ]
      (locallyFiniteCarrierHermiteVanishingSubspace m hm S).toSubmodule :=
  ((schwartzToHermiteScale m).comp
    (schwartzVanishingSubmodule S).subtypeL).codRestrict
    (locallyFiniteCarrierHermiteVanishingSubspace m hm S).toSubmodule fun f =>
      schwartzToHermiteScale_mem_locallyFiniteCarrierHermiteVanishingSubspace
        m hm S f f.property

@[simp]
theorem schwartzVanishingToHermiteVanishing_apply
    (S : LocallyFiniteCarrier) (m : ℕ) (hm : 1 ≤ m)
    (f : schwartzVanishingSubmodule S) :
    (schwartzVanishingToHermiteVanishing S m hm f : HermiteScale (m : ℤ)) =
      schwartzToHermiteScale m f :=
  rfl

theorem schwartzVanishingToHermiteVanishing_injective
    (S : LocallyFiniteCarrier) (m : ℕ) (hm : 1 ≤ m) :
    Function.Injective (schwartzVanishingToHermiteVanishing S m hm) := by
  intro f g hfg
  apply Subtype.ext
  apply schwartzToHermiteScale_injective m
  exact congrArg (fun u :
    (locallyFiniteCarrierHermiteVanishingSubspace m hm S).toSubmodule =>
      (u : HermiteScale (m : ℤ))) hfg

/-- The closure of the realized Schwartz vanishing ideal is contained in
the full positive-scale vanishing subspace.  Equality is the additional
same-order support-density obligation. -/
theorem schwartzVanishingHermiteClosure_le_vanishingSubspace
    (S : LocallyFiniteCarrier) (m : ℕ) (hm : 1 ≤ m) :
    ((schwartzVanishingSubmodule S).map
      (schwartzToHermiteScale m).toLinearMap).topologicalClosure ≤
        (locallyFiniteCarrierHermiteVanishingSubspace m hm S).toSubmodule := by
  refine Submodule.topologicalClosure_minimal _ ?_
    (locallyFiniteCarrierHermiteVanishingSubspace m hm S).isClosed'
  intro u hu
  obtain ⟨f, hf, rfl⟩ := hu
  exact schwartzToHermiteScale_mem_locallyFiniteCarrierHermiteVanishingSubspace
    m hm S f hf

/-- Distributional atomicity of a represented vector annihilates the
closure of the realized Schwartz vanishing ideal.  This conclusion does not
replace that closure by the entire positive-scale vanishing subspace. -/
theorem atomicOnCarrier_hermiteScaleDistribution_annihilates_schwartzVanishingClosure
    (S : LocallyFiniteCarrier) (m : ℕ)
    (T : HermiteScale (-(m : ℤ)))
    (hT : AtomicOnCarrier S (hermiteScaleDistribution m T)) :
    ((schwartzVanishingSubmodule S).map
      (schwartzToHermiteScale m).toLinearMap).topologicalClosure ≤
        (hermiteScalePairingLeftCLM m T).ker := by
  refine Submodule.topologicalClosure_minimal _ ?_
    (hermiteScalePairingLeftCLM m T).isClosed_ker
  intro u hu
  obtain ⟨f, hf, rfl⟩ := hu
  change hermiteScalePairingLeftCLM m T (schwartzToHermiteScale m f) = 0
  rw [hermiteScalePairingLeftCLM_apply, ← hermiteScaleDistribution_apply]
  exact hT f hf

private theorem natPolynomiallyBounded_finset_sum
    {ι : Type*} (s : Finset ι) (a : ι → ℕ → ℝ)
    (ha : ∀ i ∈ s, NatPolynomiallyBounded (a i)) :
    NatPolynomiallyBounded (fun n => ∑ i ∈ s, a i n) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨0, le_rfl, 0, fun n => by simp⟩
  | @insert i s hi ih =>
      simpa only [Finset.sum_insert hi] using
        (ha i (Finset.mem_insert_self i s)).add
          (ih (fun j hj => ha j (Finset.mem_insert_of_mem hj)))

private theorem compactSchwartzApproximationBound_hermite_polynomiallyBounded
    (k l : ℕ) :
    NatPolynomiallyBounded (fun n =>
      compactSchwartzApproximationBound k l (normalizedHermiteSchwartz n)) := by
  unfold compactSchwartzApproximationBound
  apply natPolynomiallyBounded_finset_sum
  intro i hi
  apply NatPolynomiallyBounded.const_mul (l.choose i : ℝ) (Nat.cast_nonneg _)
  by_cases hi0 : i = 0
  · simp only [hi0, ite_true]
    exact NatPolynomiallyBounded.const_mul 2 (by norm_num)
      (normalizedHermiteSchwartzSeminorm_polynomiallyBounded (k + 1) l)
  · simp only [hi0, ite_false]
    exact NatPolynomiallyBounded.const_mul
      (SchwartzMap.seminorm ℂ 0 i compactSchwartzCutoff)
      (apply_nonneg _ _)
      (normalizedHermiteSchwartzSeminorm_polynomiallyBounded k (l - i))

/-- Cutoff errors of a fixed tempered distribution, tested on the Hermite
basis, have a uniform polynomial envelope multiplied by `(N+1)⁻¹`. -/
theorem exists_cutoffHermiteError_polynomialBound
    (T : TemperedDistribution ℝ ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ d : ℕ, ∀ N n : ℕ,
      ‖T (compactSchwartzApproximation N (normalizedHermiteSchwartz n) -
          normalizedHermiteSchwartz n)‖ ≤
        compactSchwartzCutoffScale N * (C * ((n : ℝ) + 1) ^ d) := by
  obtain ⟨s, B, hB, hT⟩ :=
    temperedDistribution_norm_le_finsetSchwartzSeminorm T
  have hpoly : NatPolynomiallyBounded (fun n => (B : ℝ) *
      ∑ p ∈ s, compactSchwartzApproximationBound p.1 p.2
        (normalizedHermiteSchwartz n)) :=
    NatPolynomiallyBounded.const_mul (B : ℝ) B.coe_nonneg
      (natPolynomiallyBounded_finset_sum s _ fun p hp =>
        compactSchwartzApproximationBound_hermite_polynomiallyBounded p.1 p.2)
  obtain ⟨C, hC, d, hd⟩ := hpoly
  refine ⟨C, hC, d, fun N n => ?_⟩
  let f := normalizedHermiteSchwartz n
  have hsup : s.sup (schwartzSeminormFamily ℂ ℝ ℂ)
      (compactSchwartzApproximation N f - f) ≤
        compactSchwartzCutoffScale N *
          ∑ p ∈ s, compactSchwartzApproximationBound p.1 p.2 f := by
    apply Seminorm.finset_sup_apply_le
      (mul_nonneg (compactSchwartzCutoffScale_pos N).le
        (Finset.sum_nonneg fun p hp =>
          compactSchwartzApproximationBound_nonneg p.1 p.2 f))
    intro p hp
    exact (compactSchwartzApproximation_seminorm_le N p.1 p.2 f).trans
      (mul_le_mul_of_nonneg_left
        (Finset.single_le_sum
          (fun q hq => compactSchwartzApproximationBound_nonneg q.1 q.2 f) hp)
        (compactSchwartzCutoffScale_pos N).le)
  calc
    ‖T (compactSchwartzApproximation N f - f)‖ ≤
        B * s.sup (schwartzSeminormFamily ℂ ℝ ℂ)
          (compactSchwartzApproximation N f - f) := hT _
    _ ≤ B * (compactSchwartzCutoffScale N *
        ∑ p ∈ s, compactSchwartzApproximationBound p.1 p.2 f) :=
      mul_le_mul_of_nonneg_left hsup B.coe_nonneg
    _ = compactSchwartzCutoffScale N *
        (B * ∑ p ∈ s, compactSchwartzApproximationBound p.1 p.2 f) := by ring
    _ ≤ compactSchwartzCutoffScale N * (C * ((n : ℝ) + 1) ^ d) :=
      mul_le_mul_of_nonneg_left (hd n) (compactSchwartzCutoffScale_pos N).le

private theorem locallyAtomicFormula_eq_sum_of_cover
    (S : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ)
    (a : S.subtype → ℂ) (ha : IsLocallyAtomicCoefficientFamily S T a)
    (f : SchwartzMap ℝ ℂ) (hfc : HasCompactSupport f)
    (E : Finset S.subtype) (hE : ∀ x, x ∉ E → f x = 0) :
    T f = ∑ x ∈ E, a x * f x := by
  classical
  obtain ⟨F, hF, hsum⟩ := ha f hfc
  rw [hsum]
  calc
    (∑ x ∈ F, a x * f x) = ∑ x ∈ F ∪ E, a x * f x := by
      apply Finset.sum_subset Finset.subset_union_left
      intro x hx hxF
      rw [hF x hxF, mul_zero]
    _ = ∑ x ∈ E, a x * f x := by
      symm
      apply Finset.sum_subset Finset.subset_union_right
      intro x hx hxE
      rw [hE x hxE, mul_zero]

/-- Every genuine Dirac vector at a carrier point lies in intrinsic
physical support. -/
theorem hermitePointMass_mem_fixedOrderPhysicalSupport
    (S : LocallyFiniteCarrier) (m : ℕ) (hm : 1 ≤ m) (x : S.subtype) :
    hermitePointMass m hm (x : ℝ) ∈ fixedOrderPhysicalSupport S m hm := by
  change hermitePointMass m hm (x : ℝ) ∈
    (locallyFiniteSupportedHermiteMeasureSubspace m hm S).toSubmodule
  rw [← locallyFiniteAtomicSupportSubspace_eq_supportedHermiteMeasureSubspace]
  have hatom := atom_mem_atomicSupportSubspace
    (locallyFiniteCarrierHermitePointMass m hm S) x
  have hscaled := (atomicSupportSubspace
    (locallyFiniteCarrierHermitePointMass m hm S)).smul_mem
      ((‖hermitePointMass m hm (x : ℝ)‖ : ℝ) : ℂ) hatom
  have hnorm : ‖hermitePointMass m hm (x : ℝ)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (hermitePointMass_ne_zero m hm (x : ℝ))
  simpa [locallyFiniteCarrierHermitePointMass, normalizedHermitePointMass,
    smul_smul, hnorm] using hscaled

/-- Cutting a locally atomic distribution off in physical space is a
finite sum of carrier Dirac vectors in every positive negative-scale order. -/
theorem exists_cutoffHermiteVector
    (S : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ)
    (hT : HasLocallyAtomicAction S T)
    (m : ℕ) (hm : 1 ≤ m) (N : ℕ) :
    ∃ v : HermiteScale (-(m : ℤ)),
      v ∈ fixedOrderPhysicalSupport S m hm ∧
        ∀ f : SchwartzMap ℝ ℂ,
          hermiteScaleDistribution m v f =
            T (compactSchwartzApproximation N f) := by
  classical
  obtain ⟨E, hE⟩ :=
    S.exists_finite_nonzero_values_of_hasCompactSupport
      (scaledCompactSchwartzCutoff N)
      (scaledCompactSchwartzCutoff_hasCompactSupport N)
  let a : S.subtype → ℂ := fun x => T (S.isolationSchwartz x)
  have ha : IsLocallyAtomicCoefficientFamily S T a :=
    atomicOnCarrier_isLocallyAtomicCoefficientFamily S T
      (hasLocallyAtomicAction_atomicOnCarrier S T hT)
  let v : HermiteScale (-(m : ℤ)) :=
    ∑ x ∈ E, (a x * scaledCompactSchwartzCutoff N x) •
      hermitePointMass m hm (x : ℝ)
  refine ⟨v, ?_, fun f => ?_⟩
  · apply Submodule.sum_mem
    intro x hx
    exact Submodule.smul_mem _ _
      (hermitePointMass_mem_fixedOrderPhysicalSupport S m hm x)
  · have hformula := locallyAtomicFormula_eq_sum_of_cover S T a ha
      (compactSchwartzApproximation N f)
      (compactSchwartzApproximation_hasCompactSupport N f) E
      (fun x hx => by
        rw [compactSchwartzApproximation_apply, hE x hx, zero_mul])
    rw [hformula]
    change (hermiteScaleDistributionCLM m v) f = _
    dsimp only [v]
    rw [map_sum]
    simp only [_root_.sum_apply, map_smul, smul_apply, smul_eq_mul,
      hermiteScaleDistributionCLM_apply, hermitePointMass_represents_delta,
      pointMass_apply, compactSchwartzApproximation_apply]
    apply Finset.sum_congr rfl
    intro x hx
    ring

/-- Realization tested against one Hermite function recovers the raw
coefficient of a negative-scale vector. -/
theorem hermiteScaleDistribution_apply_normalizedHermiteSchwartz
    (m : ℕ) (u : HermiteScale (-(m : ℤ))) (n : ℕ) :
    hermiteScaleDistribution m u (normalizedHermiteSchwartz n) =
      rawHermiteCoefficients (-(m : ℤ)) u n := by
  rw [hermiteScaleDistribution_apply_raw]
  simp_rw [schwartzHermiteCoefficients_normalizedHermiteSchwartz_unit]
  simp only [mul_ite, mul_one, mul_zero, tsum_ite_eq]

/-- A realized vector can be moved to any larger negative-scale order
without changing its distribution. -/
theorem exists_hermiteScale_larger_representation
    {m r : ℕ} (hmr : m ≤ r) (u : HermiteScale (-(m : ℤ))) :
    ∃ v : HermiteScale (-(r : ℤ)),
      hermiteScaleDistribution r v = hermiteScaleDistribution m u := by
  induction r, hmr using Nat.le_induction with
  | base => exact ⟨u, rfl⟩
  | succ r hmr ih =>
      obtain ⟨v, hv⟩ := ih
      exact ⟨hermiteScaleInclusion r v,
        (hermiteScaleDistribution_inclusion r v).trans hv⟩

/-- Intrinsic physical support also survives passage to any larger
negative-scale order. -/
theorem exists_fixedOrderPhysicalSupport_larger_representation
    (S : LocallyFiniteCarrier) {m r : ℕ} (hm : 1 ≤ m) (hmr : m ≤ r)
    (u : HermiteScale (-(m : ℤ)))
    (hu : u ∈ fixedOrderPhysicalSupport S m hm) :
    ∃ v : HermiteScale (-(r : ℤ)),
      v ∈ fixedOrderPhysicalSupport S r (hm.trans hmr) ∧
        hermiteScaleDistribution r v = hermiteScaleDistribution m u := by
  induction r, hmr using Nat.le_induction with
  | base => exact ⟨u, hu, rfl⟩
  | succ r hmr ih =>
      obtain ⟨v, hvs, hv⟩ := ih
      exact ⟨hermiteScaleInclusion r v,
        hermiteScaleInclusion_mem_fixedOrderPhysicalSupport
          S r (hm.trans hmr) v hvs,
        (hermiteScaleDistribution_inclusion r v).trans hv⟩

private theorem hermiteScale_norm_le_of_raw_bound
    (m : ℕ) (u w : HermiteScale (-(m : ℤ))) (a : ℝ) (ha : 0 ≤ a)
    (h : ∀ n, ‖rawHermiteCoefficients (-(m : ℤ)) u n‖ ≤
      a * ‖rawHermiteCoefficients (-(m : ℤ)) w n‖) :
    ‖u‖ ≤ a * ‖w‖ := by
  have hu : ‖u‖ ≤ ‖(a : ℂ) • w‖ := by
    apply lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0)
    intro n
    have hun := congrFun (normalize_rawHermiteCoefficients (-(m : ℤ)) u) n
    have hwn := congrFun (normalize_rawHermiteCoefficients (-(m : ℤ)) w) n
    change (hermiteScaleWeight (-(m : ℤ)) n : ℂ) *
      rawHermiteCoefficients (-(m : ℤ)) u n = u n at hun
    change (hermiteScaleWeight (-(m : ℤ)) n : ℂ) *
      rawHermiteCoefficients (-(m : ℤ)) w n = w n at hwn
    change ‖u n‖ ≤ ‖(a : ℂ) * w n‖
    rw [← hun, ← hwn]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha]
    calc
      |hermiteScaleWeight (-(m : ℤ)) n| *
          ‖rawHermiteCoefficients (-(m : ℤ)) u n‖ ≤
          |hermiteScaleWeight (-(m : ℤ)) n| *
            (a * ‖rawHermiteCoefficients (-(m : ℤ)) w n‖) :=
        mul_le_mul_of_nonneg_left (h n) (abs_nonneg _)
      _ = a * (|hermiteScaleWeight (-(m : ℤ)) n| *
          ‖rawHermiteCoefficients (-(m : ℤ)) w n‖) := by ring
  simpa only [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ha] using hu

/-- Every locally atomic tempered distribution belongs to intrinsic
physical support at some positive negative-scale order.  The order is
allowed to increase to absorb the uniform polynomial cutoff-error envelope. -/
theorem exists_fixedOrderPhysicalSupport_representation
    (S : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ)
    (hT : HasLocallyAtomicAction S T) :
    ∃ m : ℕ, ∃ hm : 1 ≤ m, ∃ u : HermiteScale (-(m : ℤ)),
      u ∈ fixedOrderPhysicalSupport S m hm ∧ hermiteScaleDistribution m u = T := by
  classical
  obtain ⟨C, hC, d, herror⟩ := exists_cutoffHermiteError_polynomialBound T
  let envelope : ℕ → ℂ := fun n => (C * ((n : ℝ) + 1) ^ d : ℝ)
  have henvelope : NatPolynomiallyBounded (fun n => ‖envelope n‖) := by
    refine ⟨C, hC, d, fun n => ?_⟩
    simp only [envelope, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hC (by positivity : 0 ≤ ((n : ℝ) + 1) ^ d))]
    exact le_rfl
  obtain ⟨m₀, u₀, hu₀⟩ := exists_hermiteScale_representation T
  obtain ⟨m₁, w₁, hw₁⟩ :=
    exists_negativeHermiteScale_of_polynomiallyBounded envelope henvelope
  let m := m₀ + m₁ + 1
  have hm : 1 ≤ m := by dsimp only [m]; omega
  obtain ⟨u, hu⟩ := exists_hermiteScale_larger_representation
    (show m₀ ≤ m by dsimp only [m]; omega) u₀
  obtain ⟨w, hw⟩ := exists_hermiteScale_larger_representation
    (show m₁ ≤ m by dsimp only [m]; omega) w₁
  have huT : hermiteScaleDistribution m u = T := hu.trans hu₀
  have hwraw : ∀ n, rawHermiteCoefficients (-(m : ℤ)) w n = envelope n := by
    intro n
    rw [← hermiteScaleDistribution_apply_normalizedHermiteSchwartz, hw,
      hermiteScaleDistribution_apply_normalizedHermiteSchwartz, hw₁]
  choose v hvs hv using fun N => exists_cutoffHermiteVector S T hT m hm N
  have hnorm : ∀ N : ℕ, ‖v N - u‖ ≤ compactSchwartzCutoffScale N * ‖w‖ := by
    intro N
    apply hermiteScale_norm_le_of_raw_bound m (v N - u) w
      (compactSchwartzCutoffScale N) (compactSchwartzCutoffScale_pos N).le
    intro n
    have hraw : rawHermiteCoefficients (-(m : ℤ)) (v N - u) n =
        T (compactSchwartzApproximation N (normalizedHermiteSchwartz n) -
          normalizedHermiteSchwartz n) := by
      rw [← hermiteScaleDistribution_apply_normalizedHermiteSchwartz]
      change (hermiteScaleDistributionCLM m (v N - u)) _ = _
      rw [map_sub]
      change hermiteScaleDistribution m (v N) _ -
        hermiteScaleDistribution m u _ = _
      rw [hv N, huT, map_sub]
    rw [hraw, hwraw]
    simpa only [envelope, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hC (by positivity : 0 ≤ ((n : ℝ) + 1) ^ d))]
      using herror N n
  have hvlim : Tendsto v atTop (nhds u) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun N => norm_nonneg _) hnorm
    simpa only [zero_mul] using compactSchwartzCutoffScale_tendsto.mul_const ‖w‖
  refine ⟨m, hm, u, ?_, huT⟩
  exact (fixedOrderPhysicalSupport S m hm).isClosed'.mem_of_tendsto
    hvlim (Filter.Eventually.of_forall hvs)

/-- Every genuine distributional Meyer vector is represented in some
positive intrinsic fixed-order Meyer layer.  Physical and Fourier support
are first obtained at possibly different orders and then moved to a common
order; injectivity of realization identifies the Fourier vectors there. -/
theorem exists_fixedOrderMeyerLayer_representation
    (S : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ DistributionalMeyerSpace S) :
    ∃ m : ℕ, ∃ hm : 1 ≤ m, ∃ u : HermiteScale (-(m : ℤ)),
      u ∈ FixedOrderMeyerLayer S m hm ∧ hermiteScaleDistribution m u = T := by
  obtain ⟨hphysical, hfourier⟩ := (mem_distributionalMeyerSpace_iff S T).mp hT
  obtain ⟨m₀, hm₀, u₀, hu₀s, hu₀⟩ :=
    exists_fixedOrderPhysicalSupport_representation S T hphysical
  obtain ⟨m₁, hm₁, v₁, hv₁s, hv₁⟩ :=
    exists_fixedOrderPhysicalSupport_representation S
      (FourierTransform.fourier T) hfourier
  let m := m₀ + m₁
  have hm : 1 ≤ m := by dsimp only [m]; omega
  obtain ⟨u, hus, hu⟩ := exists_fixedOrderPhysicalSupport_larger_representation
    S hm₀ (show m₀ ≤ m by dsimp only [m]; omega) u₀ hu₀s
  obtain ⟨v, hvs, hv⟩ := exists_fixedOrderPhysicalSupport_larger_representation
    S hm₁ (show m₁ ≤ m by dsimp only [m]; omega) v₁ hv₁s
  have huT : hermiteScaleDistribution m u = T := hu.trans hu₀
  have hFourier : hermiteFourier (-(m : ℤ)) u = v := by
    apply hermiteScaleDistribution_injective m
    rw [hermiteFourier_represents_distributionalFourier, huT, hv, hv₁]
  refine ⟨m, hm, u, ?_, huT⟩
  rw [mem_fixedOrderMeyerLayer_iff]
  exact ⟨hus, hFourier ▸ hvs⟩

/-- The injective realizations of positive intrinsic fixed-order layers
cover the distributional Meyer space.  Successor indexing makes this a
countable family without a dependent positivity predicate. -/
theorem fixedOrderMeyerLayerToDistributionalMeyerSpace_cover
    (S : LocallyFiniteCarrier) (T : DistributionalMeyerSpace S) :
    ∃ m : ℕ, ∃ u : FixedOrderMeyerLayer S (m + 1) (by omega),
      fixedOrderMeyerLayerToDistributionalMeyerSpace S (m + 1) (by omega) u = T := by
  obtain ⟨m, hm, u, hus, hu⟩ :=
    exists_fixedOrderMeyerLayer_representation S T T.property
  refine ⟨m, ⟨hermiteScaleInclusion m u,
    hermiteScaleInclusion_mem_fixedOrderMeyerLayer S m hm u hus⟩, ?_⟩
  apply Subtype.ext
  change hermiteScaleDistribution (m + 1) (hermiteScaleInclusion m u) = T
  exact (hermiteScaleDistribution_inclusion m u).trans hu

end

end MeyerGeneralProblem
