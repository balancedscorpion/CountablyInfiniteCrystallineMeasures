module

public import Mathlib.Analysis.Fourier.AddCircleMulti
import all Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.MeasureTheory.Measure.Haar.Basic
import all Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Group.Integral
import all Mathlib.MeasureTheory.Group.Integral
public import Mathlib.Topology.UrysohnsLemma
import all Mathlib.Topology.UrysohnsLemma
public import Mathlib.Topology.Algebra.Group.SubmonoidClosure
import all Mathlib.Topology.Algebra.Group.SubmonoidClosure
public import Mathlib.Topology.Maps.Proper.Basic
import all Mathlib.Topology.Maps.Proper.Basic

@[expose] public section

/-!
# Character separation for real flows on a finite torus

Fourier density and Haar averaging on a closed subgroup supply the finite-torus
character criterion used by the actual reciprocal frequency flow.
-/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open MeasureTheory Set Filter TopologicalSpace
open scoped Topology ENNReal

/-- The normalized Haar measure on the unit circle for the finite torus argument. -/
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- Integration of continuous complex functions on a compact space as a continuous linear map. -/
def compactIntegralCLM {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ] : C(X,ℂ) →L[ℂ] ℂ :=
  (L1.integralCLM' ℂ).comp (ContinuousMap.toLp 1 μ ℂ)

/-- The compact integral map evaluates to the original Bochner integral. -/
theorem compactIntegralCLM_apply {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ] (f : C(X,ℂ)) :
    compactIntegralCLM μ f = ∫ x, f x ∂μ := by
  change L1.integralCLM' ℂ (ContinuousMap.toLp 1 μ ℂ f) = _
  rw [← L1.integral_eq', L1.integral_eq_integral]
  exact integral_congr_ae (ContinuousMap.coeFn_toLp (p := 1) (𝕜 := ℂ) μ f)

/-- Fourier characters multiply under addition of torus points. -/
theorem mFourier_point_add {ι : Type*} [Fintype ι] (k : ι → ℤ) (x y : UnitAddTorus ι) :
    UnitAddTorus.mFourier k (x+y) = UnitAddTorus.mFourier k x * UnitAddTorus.mFourier k y := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Pi.add_apply,
    fourier_apply, smul_add, AddCircle.toCircle_add, Circle.coe_mul, Finset.prod_mul_distrib]

/-- Every nontrivial character integrates to zero over the torus. -/
theorem integral_mFourier_eq_zero {ι : Type*} [Fintype ι] (k : ι → ℤ) (hk : k ≠ 0) :
    ∫ x : UnitAddTorus ι, UnitAddTorus.mFourier k x = 0 := by
  classical
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk]
  rw [integral_fintype_prod_volume_eq_prod]
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hk
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  have hi0 : k i ≠ 0 := hi
  have haux := (orthonormal_iff_ite.mp (orthonormal_fourier (T := 1))) 0 (k i)
  simp only [ContinuousMap.inner_toLp, ← fourier_neg, ← fourier_add, neg_zero, add_zero,
    ite_eq_right (Ne.symm hi0)] at haux
  convert! haux using 1

/-- A character nontrivial on a subgroup has zero Haar integral on that subgroup. -/
theorem integral_subgroup_character_zero {ι : Type*} [Fintype ι]
    (H : AddSubgroup (UnitAddTorus ι)) (μ : Measure H) [μ.IsAddLeftInvariant]
    (k : ι → ℤ) (z : H) (hz : UnitAddTorus.mFourier k z.val ≠ 1) :
    ∫ x : H, UnitAddTorus.mFourier k x.val ∂μ = 0 := by
  have hshift := integral_add_left_eq_self (μ := μ)
    (fun x : H => UnitAddTorus.mFourier k x.val) z
  have heq : (fun x : H => UnitAddTorus.mFourier k (z+x).val) =
      (fun x : H => UnitAddTorus.mFourier k z.val * UnitAddTorus.mFourier k x.val) := by
    funext x
    exact mFourier_point_add k z.val x.val
  rw [heq, integral_const_mul] at hshift
  exact eq_zero_of_mul_eq_self_left hz hshift

/-- A closed torus subgroup detected by no nonzero integer character is the whole torus. -/
theorem closed_torus_subgroup_eq_top {ι : Type*} [Fintype ι]
    (H : AddSubgroup (UnitAddTorus ι)) (hH : IsClosed (H : Set (UnitAddTorus ι)))
    (hchars : ∀ k : ι → ℤ, k ≠ 0 → ∃ z : H, UnitAddTorus.mFourier k z.val ≠ 1) :
    H = ⊤ := by
  classical
  let : CompactSpace H := isCompact_iff_compactSpace.mp hH.isCompact
  let μ : Measure H := Measure.addHaarMeasure ⊤
  let : IsProbabilityMeasure μ := ⟨by
    change Measure.addHaarMeasure (⊤ : PositiveCompacts H) univ = 1
    simpa only [PositiveCompacts.coe_top] using (Measure.addHaarMeasure_self (K₀ := (⊤ : PositiveCompacts H)))⟩
  let incl : C(H, UnitAddTorus ι) := ⟨Subtype.val, continuous_subtype_val⟩
  let A : C(UnitAddTorus ι,ℂ) →L[ℂ] ℂ :=
    (compactIntegralCLM μ).comp (ContinuousMap.compCLM ℂ ℂ incl)
  let B : C(UnitAddTorus ι,ℂ) →L[ℂ] ℂ := compactIntegralCLM volume
  have hAB : A = B := by
    apply ContinuousLinearMap.ext_on (s := range (@UnitAddTorus.mFourier ι _))
    · rw [dense_iff_closure_eq, ← Submodule.topologicalClosure_coe,
        UnitAddTorus.span_mFourier_closure_eq_top]
      rfl
    · rintro f ⟨k,rfl⟩
      change compactIntegralCLM μ ((UnitAddTorus.mFourier k).comp incl) =
        compactIntegralCLM volume (UnitAddTorus.mFourier k)
      simp only [compactIntegralCLM_apply, ContinuousMap.comp_apply, incl, ContinuousMap.coe_mk]
      by_cases hk : k = 0
      · subst k
        simp only [UnitAddTorus.mFourier_zero, ContinuousMap.one_apply, integral_const, probReal_univ, one_smul]
      · obtain ⟨z,hz⟩ := hchars k hk
        rw [integral_subgroup_character_zero H μ k z hz, integral_mFourier_eq_zero k hk]
  apply top_unique
  intro x _
  by_contra hx
  obtain ⟨f,hfH,hfx,hf01⟩ := exists_continuous_zero_one_of_isClosed hH
    (isClosed_singleton (x := x)) (disjoint_singleton_right.mpr hx)
  let g : C(UnitAddTorus ι,ℂ) := ⟨fun y => (f y : ℂ), Complex.continuous_ofReal.comp f.continuous⟩
  have hgA : A g = 0 := by
    change compactIntegralCLM μ (g.comp incl) = 0
    rw [compactIntegralCLM_apply]
    have heq : (fun y : H => (g.comp incl) y) = 0 := by
      funext y
      change (f y.val : ℂ) = 0
      rw [hfH y.property]
      rfl
    rw [heq]
    exact integral_zero _ _
  have hgB : B g = (∫ y, f y : ℝ) := by
    change compactIntegralCLM volume g = _
    rw [compactIntegralCLM_apply]
    exact integral_ofReal
  have hxone : f x = 1 := hfx (mem_singleton x)
  have hpos : 0 < ∫ y, f y := f.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (x := x) (HasCompactSupport.of_compactSpace f) (fun y => (hf01 y).1) (by rw [hxone]; exact one_ne_zero)
  rw [hAB,hgB] at hgA
  exact (ne_of_gt hpos) (Complex.ofReal_eq_zero.mp hgA)

/-- The genuine real translation flow in normalized finite-torus coordinates. -/
def torusLinearFlow {ι : Type*} (v : ι → ℝ) : ℝ →+ UnitAddTorus ι where
  toFun t i := (t*v i : ℝ)
  map_zero' := by ext i; simp
  map_add' t u := by ext i; simp [add_mul]

/-- The linear torus flow is continuous. -/
theorem torusLinearFlow_continuous {ι : Type*} (v : ι → ℝ) : Continuous (torusLinearFlow v) := by
  apply continuous_pi
  intro i
  exact (AddCircle.continuous_mk' (1 : ℝ)).comp (continuous_id.mul_const (v i))

/-- Every torus character on the real flow has the exact scalar frequency given by its integer relation. -/
theorem mFourier_torusLinearFlow {ι : Type*} [Fintype ι] (v : ι → ℝ) (k : ι → ℤ) (t : ℝ) :
    UnitAddTorus.mFourier k (torusLinearFlow v t) =
      fourier 1 ((t*∑ i, (k i : ℝ)*v i : ℝ) : UnitAddCircle) := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, torusLinearFlow, AddMonoidHom.coe_mk,
    ZeroHom.coe_mk, fourier_coe_apply]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  simp only [mul_one, div_one, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Nonzero integer frequency relations supply an explicit point detected by the character. -/
theorem exists_torusFlow_character_ne_one {ι : Type*} [Fintype ι] (v : ι → ℝ) (k : ι → ℤ)
    (hk : (∑ i, (k i : ℝ)*v i) ≠ 0) :
    ∃ t : ℝ, UnitAddTorus.mFourier k (torusLinearFlow v t) ≠ 1 := by
  let a : ℝ := ∑ i, (k i : ℝ)*v i
  have ha : a ≠ 0 := hk
  refine ⟨1/(2*a), ?_⟩
  rw [mFourier_torusLinearFlow]
  have ht : 1/(2*a)*a = (1/2 : ℝ) := by field_simp
  change fourier 1 ((1/(2*a)*a : ℝ) : UnitAddCircle) ≠ 1
  rw [ht]
  have he : fourier 1 ((1/2 : ℝ) : UnitAddCircle) = -1 := by
    rw [fourier_coe_apply]
    convert Complex.exp_pi_mul_I using 1; congr 1; push_cast; ring
  rw [he]
  norm_num

/-- Rationally independent frequencies give a dense real flow on the full finite torus. -/
theorem torusLinearFlow_denseRange {ι : Type*} [Fintype ι] (v : ι → ℝ)
    (hv : ∀ k : ι → ℤ, (∑ i, (k i : ℝ)*v i) = 0 → k = 0) :
    DenseRange (torusLinearFlow v) := by
  let H := (torusLinearFlow v).range.topologicalClosure
  have htop : H = ⊤ := by
    apply closed_torus_subgroup_eq_top H (AddSubgroup.isClosed_topologicalClosure _)
    intro k hk
    have hsum : (∑ i, (k i : ℝ)*v i) ≠ 0 := fun h => hk (hv k h)
    obtain ⟨t,ht⟩ := exists_torusFlow_character_ne_one v k hsum
    exact ⟨⟨torusLinearFlow v t, AddSubgroup.le_topologicalClosure _ ⟨t,rfl⟩⟩,ht⟩
  rw [DenseRange, dense_iff_closure_eq]
  have hcoe := congrArg (fun K : AddSubgroup (UnitAddTorus ι) => (K : Set (UnitAddTorus ι))) htop
  simpa only [H, AddSubgroup.topologicalClosure_coe, AddMonoidHom.coe_range,
    AddSubgroup.coe_top] using hcoe

/-- Compact-group recurrence turns a dense real flow into a dense nonnegative half-flow. -/
theorem dense_nonnegative_real_flow {G : Type*} [AddCommGroup G] [TopologicalSpace G]
    [CompactSpace G] [IsTopologicalAddGroup G] (f : ℝ →+ G) (hf : DenseRange f) :
    Dense (f '' Ici (0 : ℝ)) := by
  have hsub : range f ⊆ closure (f '' Ici (0 : ℝ)) := by
    rintro _ ⟨t,rfl⟩
    by_cases ht : 0 ≤ t
    · exact subset_closure ⟨t,ht,rfl⟩
    · have hcl : f t ∈ closure (range (fun n : ℕ => n • f (-t))) := by
        rw [← closure_range_zsmul_eq_nsmul]
        apply subset_closure
        refine ⟨-1, ?_⟩
        simp
      apply closure_mono ?_ hcl
      rintro _ ⟨n,rfl⟩
      refine ⟨(n : ℝ)*(-t), mul_nonneg (Nat.cast_nonneg _) (neg_nonneg.mpr (le_of_lt (lt_of_not_ge ht))), ?_⟩
      simpa only [nsmul_eq_mul] using f.map_nsmul n (-t)
  intro x
  exact closure_minimal hsub isClosed_closure (hf x)

/-- Every prescribed forward tail of a dense real flow is dense. -/
theorem dense_forward_real_flow {G : Type*} [AddCommGroup G] [TopologicalSpace G]
    [CompactSpace G] [IsTopologicalAddGroup G] (f : ℝ →+ G) (hf : DenseRange f) (H₀ : ℝ) :
    Dense (f '' Ici H₀) := by
  have hpos := dense_nonnegative_real_flow f hf
  have htrans := (Homeomorph.addLeft (f H₀)).isDenseEmbedding.dense_image.mpr hpos
  apply htrans.mono
  rintro _ ⟨z,⟨t,ht,rfl⟩,rfl⟩
  exact ⟨H₀+t,show H₀ ≤ H₀+t from le_add_of_nonneg_right ht, f.map_add H₀ t⟩

/-- Compactness converts forward-tail density into a finite deterministic segment net. -/
theorem exists_forward_flow_segment_net {G : Type*} [AddCommGroup G] [MetricSpace G]
    [CompactSpace G] [IsTopologicalAddGroup G] (f : ℝ →+ G) (hf : DenseRange f)
    (H₀ η : ℝ) (hη : 0 < η) :
    ∃ H : ℝ, H₀ ≤ H ∧ ∀ z : G, ∃ t : ℝ, H₀ ≤ t ∧ t ≤ H ∧ dist (f t) z < η := by
  classical
  let U : Ici H₀ → Set G := fun t => Metric.ball (f t.val) η
  have hcover : (univ : Set G) ⊆ ⋃ t : Ici H₀, U t := by
    intro z _
    obtain ⟨x,⟨t,ht,rfl⟩,hx⟩ := (dense_forward_real_flow f hf H₀).exists_dist_lt z hη
    exact mem_iUnion.mpr ⟨⟨t,ht⟩,by simpa only [U, Metric.mem_ball, dist_comm] using hx⟩
  obtain ⟨F,hF⟩ := isCompact_univ.elim_finite_subcover U (fun _ => Metric.isOpen_ball) hcover
  let H : ℝ := max H₀ (∑ t ∈ F, |t.val|)
  refine ⟨H,le_max_left _ _,?_⟩
  intro z
  have hz := hF (mem_univ z)
  simp only [mem_iUnion] at hz
  obtain ⟨t,htF,hz⟩ := hz
  refine ⟨t.val,t.property,?_,?_⟩
  · exact (le_abs_self t.val).trans ((Finset.single_le_sum (fun t _ => abs_nonneg t.val) htF).trans
      (le_max_right _ _))
  · simpa only [U, Metric.mem_ball, dist_comm] using hz

/-- A finite real segment of the actual linear flow is a strict metric net. -/
def torusSegmentNet {ι : Type*} [Fintype ι] (H₀ H η : ℝ) : Set (ι → ℝ) :=
  {v | ∀ z : UnitAddTorus ι, ∃ t : ℝ, H₀ ≤ t ∧ t ≤ H ∧ dist (torusLinearFlow v t) z < η}

/-- The bounded-segment net condition is open in the entire frequency vector. -/
theorem torusSegmentNet_isOpen {ι : Type*} [Fintype ι] (H₀ H η : ℝ) :
    IsOpen (@torusSegmentNet ι _ H₀ H η) := by
  let U : Set ((ι → ℝ) × UnitAddTorus ι) := ⋃ t ∈ Icc H₀ H,
    {p | dist (torusLinearFlow p.1 t) p.2 < η}
  have hU : IsOpen U := by
    apply isOpen_iUnion
    intro t
    apply isOpen_iUnion
    intro _
    apply isOpen_lt ?_ continuous_const
    apply Continuous.dist ?_ continuous_snd
    apply continuous_pi
    intro i
    exact (AddCircle.continuous_mk' (1 : ℝ)).comp
      (continuous_const.mul ((continuous_apply i).comp continuous_fst))
  have hclosed := isClosedMap_fst_of_compactSpace (X := ι → ℝ) (Y := UnitAddTorus ι) _ hU.isClosed_compl
  have heq : torusSegmentNet H₀ H η = (Prod.fst '' Uᶜ)ᶜ := by
    ext v
    simp only [torusSegmentNet, mem_ofPred_eq, mem_compl_iff, mem_image, U, mem_iUnion,
      Prod.exists, exists_and_right, exists_eq_right, mem_Icc]
    aesop
  rw [heq]
  exact hclosed.isOpen_compl

/-- Enlarging the upper time endpoint preserves every strict net. -/
theorem torusSegmentNet_mono {ι : Type*} [Fintype ι] (H₀ η : ℝ) :
    Monotone (@torusSegmentNet ι _ H₀ · η) := by
  intro H H' h v hv z
  obtain ⟨t,ht0,ht,hz⟩ := hv z
  exact ⟨t,ht0,ht.trans h,hz⟩

end
end MeyerGeneralProblem.Adaptive
