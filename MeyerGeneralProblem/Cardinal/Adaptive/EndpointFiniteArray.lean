module

public import MeyerGeneralProblem.Cardinal.Adaptive.EndpointLocalizedMoments

@[expose] public section

/-! Complete zero-padded Newton arrays of actual finite endpoint sources. -/
noncomputable section
open scoped BigOperators
namespace MeyerGeneralProblem.Adaptive

/-- Actual finite rapid phases, padded by the single seam distance zero after the cap. -/
def endpointPaddedDistance (P R k : ℕ) (r : ℕ+) : ℝ :=
  if r.val ≤ k then rapidDistance P R r.val else 0

/-- Above the cap, the full Newton product vanishes at every actual finite
representative because it includes every phase and the seam factor. -/
theorem halfNewtonProduct_endpointPadded_zero {P R : ℕ} (k i : ℕ) (hi : k < i)
    (u : EndpointPhaseIndex k) :
    halfNewtonProduct (endpointPaddedDistance P R k) i
      (endpointCenteredPhase (fun j => 1/2-rapidEndpointPhaseData P R k j) u)=0 := by
  cases u with
  | none =>
      unfold halfNewtonProduct
      apply Finset.prod_eq_zero (Finset.mem_range.mpr hi)
      simp [endpointCenteredPhase,endpointPaddedDistance]
  | some u =>
      obtain ⟨j,e⟩ := u
      have hj : j.val < i := by omega
      have he : 1/2-rapidEndpointPhaseData P R k j=rapidDistance P R (j.val+1) := by
        unfold rapidEndpointPhaseData
        ring
      unfold halfNewtonProduct
      apply Finset.prod_eq_zero (Finset.mem_range.mpr hj)
      have hp : endpointPaddedDistance P R k ⟨j.val+1,by omega⟩=rapidDistance P R (j.val+1) := by
        apply ite_eq_left
        exact Nat.succ_le_of_lt j.isLt
      cases e <;> simp only [endpointCenteredPhase,he,hp,Bool.false_eq_true,ite_false,ite_true,
        criticalNewtonNode,mul_neg,Real.cos_neg,sub_self]

/-- The genuine finite whole-source coordinate vanishes outside the complete
finite index square. Both parity bits and the endpoint remain present. -/
theorem halfNewtonCoordinate_endpointPadded_zero {P R : ℕ} (hP : 1 ≤ P) (hR : 1 ≤ R)
    (k : ℕ) (c : EndpointMatrix k) (i j : ℕ) (e d : Bool) (hij : k < i ∨ k < j) :
    halfNewtonCoordinate (endpointPaddedDistance P R k) (endpointPaddedDistance P R k)
      (halfWeylDistributionCLM (endpointPoissonSynthesis
        (rapidEndpointPhaseData P R k) (rapidEndpointPhaseData P R k) c)) i e j d=0 := by
  unfold halfNewtonCoordinate
  rw [halfNewtonBilinear_recentered_endpoint _ _ c
    (fun u => lt_of_le_of_lt (endpointCenteredPhase_rapid_small hP hR k u) (by norm_num))
    (fun u => lt_of_le_of_lt (endpointCenteredPhase_rapid_small hP hR k u) (by norm_num))
    _ _ (halfNewtonTest_central_zero _ i e) (halfNewtonTest_central_zero _ j d)]
  apply Finset.sum_eq_zero
  intro u _
  apply Finset.sum_eq_zero
  intro v _
  rcases hij with hi|hj
  · rw [halfNewtonTest_apply,halfNewtonFunction,halfNewtonProduct_endpointPadded_zero k i hi u]
    simp only [mul_zero,zero_mul]
  · rw [halfNewtonTest_apply,halfNewtonTest_apply,halfNewtonFunction,halfNewtonFunction,
      halfNewtonProduct_endpointPadded_zero k j hj v]
    simp only [mul_zero]

/-- The prescribed constant normalization preserves the exact finite square support. -/
theorem halfNewtonMoment_endpointPadded_zero {P R : ℕ} (hP : 1 ≤ P) (hR : 1 ≤ R)
    (k : ℕ) (c : EndpointMatrix k) (i j : ℕ) (e d : Bool) (hij : k < i ∨ k < j) :
    halfNewtonMoment (endpointPaddedDistance P R k) (endpointPaddedDistance P R k)
      (halfWeylDistributionCLM (endpointPoissonSynthesis
        (rapidEndpointPhaseData P R k) (rapidEndpointPhaseData P R k) c)) i e j d=0 := by
  rw [halfNewtonMoment_eq_zero_iff]
  exact halfNewtonCoordinate_endpointPadded_zero hP hR k c i j e d hij

/-- The complete four-parity normalized finite-source array is genuinely square
summable. Its finite support follows from actual node evaluations, including zero. -/
theorem summable_sq_endpointPaddedMoment {P R : ℕ} (hP : 1 ≤ P) (hR : 1 ≤ R)
    (k : ℕ) (c : EndpointMatrix k) :
    Summable (fun z : (ℕ×Bool)×(ℕ×Bool) =>
      ‖halfNewtonMoment (endpointPaddedDistance P R k) (endpointPaddedDistance P R k)
        (halfWeylDistributionCLM (endpointPoissonSynthesis
          (rapidEndpointPhaseData P R k) (rapidEndpointPhaseData P R k) c))
        z.1.1 z.1.2 z.2.1 z.2.2‖^2) := by
  apply summable_of_hasFiniteSupport
  apply Set.Finite.subset ((Set.finite_Iic k).prod (Set.toFinite (Set.univ : Set Bool)) |>.prod
    ((Set.finite_Iic k).prod (Set.toFinite (Set.univ : Set Bool))))
  intro z hz
  have h : ¬(k < z.1.1 ∨ k < z.2.1) := by
    intro hh
    exact hz (by
      dsimp only
      rw [halfNewtonMoment_endpointPadded_zero hP hR k c z.1.1 z.2.1 z.1.2 z.2.2 hh,norm_zero]
      norm_num)
  exact ⟨⟨by simpa using (not_lt.mp (fun hh => h (Or.inl hh))),Set.mem_univ _⟩,
    ⟨by simpa using (not_lt.mp (fun hh => h (Or.inr hh))),Set.mem_univ _⟩⟩

/-- Retained levels use exactly the original rapid prefix, so zero padding does
not alter any finite-grid Newton function. -/
theorem halfNewtonFunction_endpointPadded_prefix (P R k i : ℕ) (hi : i ≤ k)
    (e : Bool) (x : ℝ) :
    halfNewtonFunction (endpointPaddedDistance P R k) i e x =
      halfNewtonFunction (fun r => rapidDistance P R r.val) i e x := by
  unfold halfNewtonFunction halfNewtonProduct
  congr 1
  apply Finset.prod_congr rfl
  intro r hr
  have hk : r+1 ≤ k := by have := Finset.mem_range.mp hr; omega
  change criticalNewtonNode x-criticalNewtonNode (if r+1 ≤ k then rapidDistance P R (r+1) else 0) =
    criticalNewtonNode x-criticalNewtonNode (rapidDistance P R (r+1))
  rw [ite_eq_left hk]

/-- Every retained actual normalized coordinate agrees with the original rapid
coordinate used by the exact admission theorem. -/
theorem halfNewtonMoment_endpointPadded_prefix (P R k i j : ℕ) (hi : i ≤ k) (hj : j ≤ k)
    (e d : Bool) (T : TemperedDistribution ℝ ℂ) :
    halfNewtonMoment (endpointPaddedDistance P R k) (endpointPaddedDistance P R k) T i e j d =
      halfNewtonMoment (fun r => rapidDistance P R r.val) (fun r => rapidDistance P R r.val) T i e j d := by
  have ht (n : ℕ) (hn : n ≤ k) (a : Bool) :
      halfNewtonTest (endpointPaddedDistance P R k) n a=halfNewtonTest (fun r => rapidDistance P R r.val) n a := by
    ext x
    simp only [halfNewtonTest_apply,halfNewtonFunction_endpointPadded_prefix P R k n hn]
  simp only [halfNewtonMoment,halfNewtonCoordinate,ht i hi e,ht j hj d]

end MeyerGeneralProblem.Adaptive
