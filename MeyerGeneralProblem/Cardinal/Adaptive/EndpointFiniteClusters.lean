module

public import MeyerGeneralProblem.Cardinal.Adaptive.EndpointFiniteArray
public import MeyerGeneralProblem.Cardinal.Adaptive.EndpointCarrierLimit
public import MeyerGeneralProblem.Cardinal.Adaptive.HalfNewtonFourier

@[expose] public section

/-! Exact finite endpoint clusters and their asymmetric surviving cells. -/
noncomputable section
open scoped FourierTransform BigOperators
namespace MeyerGeneralProblem.Adaptive

/-- The actual translated deleted finite carrier has two interior arms and the
single seam arm with exactly its prescribed escaping cells. -/
theorem endpointDeletedCarrier_recentered_mem {k : ℕ} (α : Fin k → ℝ)
    (ha : Function.Injective α) (hi : ∀ j, 0 < α j ∧ α j < 1/2) (x : ℝ) :
    x ∈ ((endpointDeletedCarrier α).translate (-1/2)).carrier ↔
      (∃ (j : Fin k) (n : ℤ), j.val < n.natAbs ∧ x=(n:ℝ)-(1/2-α j)) ∨
      (∃ (j : Fin k) (n : ℤ), j.val < (n+1).natAbs ∧ x=(n:ℝ)+(1/2-α j)) ∨
      (∃ n : ℤ, (n < -(k:ℤ) ∨ (k:ℤ) ≤ n) ∧ x=(n:ℝ)) := by
  constructor
  · rintro ⟨y,hy,rfl⟩
    rw [endpointDeletedCarrier_mem_iff α ha hi] at hy
    rcases hy with ⟨j,u,n,hn,rfl⟩|⟨n,hn,rfl⟩
    · cases u
      · exact Or.inl ⟨j,n,hn,by simp only [criticalSignedPhase,Bool.false_eq_true,ite_false]; ring⟩
      · exact Or.inr (Or.inl ⟨j,n-1,by simpa using hn,by simp only [criticalSignedPhase,ite_true,Int.cast_sub,Int.cast_one]; ring⟩)
    · exact Or.inr (Or.inr ⟨n,hn,by ring⟩)
  · rintro (⟨j,n,hn,rfl⟩|⟨j,n,hn,rfl⟩|⟨n,hn,rfl⟩)
    · refine ⟨α j+n,?_,by ring⟩
      rw [endpointDeletedCarrier_mem_iff α ha hi]
      exact Or.inl ⟨j,false,n,hn,rfl⟩
    · refine ⟨-(α j)+(n+1:ℤ),?_,by push_cast; ring⟩
      rw [endpointDeletedCarrier_mem_iff α ha hi]
      exact Or.inl ⟨j,true,n+1,hn,rfl⟩
    · refine ⟨1/2+n,?_,by ring⟩
      rw [endpointDeletedCarrier_mem_iff α ha hi]
      exact Or.inr ⟨n,hn,rfl⟩

private theorem finite_central_other_cell (f : SchwartzMap ℝ ℂ)
    (hf : ∀ x, 1/2 ≤ |x| → f x=0) (a : ℝ) (ha : |a| < 1/2)
    (n m : ℤ) (hn : n ≠ m) : f (-(m:ℝ)+((n:ℝ)+a))=0 := by
  apply hf
  have hh : (1:ℝ) ≤ |((n-m:ℤ):ℝ)| := by exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hn)
  have hb := abs_add_le (-(m:ℝ)+((n:ℝ)+a)) (-a)
  rw [show -(m:ℝ)+((n:ℝ)+a)+(-a)=((n-m:ℤ):ℝ) by push_cast; ring,abs_neg] at hb
  linarith

/-- A finite translated cluster is annihilated by its actual interior nodes and
its possible seam value, with no strict-interior infinite extension assumed. -/
theorem endpointSource_cluster_zero {k : ℕ} (α : Fin k → ℝ)
    (ha : Function.Injective α) (hi : ∀ j, 0 < α j ∧ α j < 1/2)
    (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier ((endpointDeletedCarrier α).translate (-1/2)) T)
    (f : SchwartzMap ℝ ℂ) (hf : ∀ x, 1/2 ≤ |x| → f x=0) (m : ℤ)
    (hminus : ∀ j : Fin k, j.val < m.natAbs → f (-(1/2-α j))=0)
    (hplus : ∀ j : Fin k, j.val < (m+1).natAbs → f (1/2-α j)=0)
    (hseam : (m < -(k:ℤ) ∨ (k:ℤ) ≤ m) → f 0=0) :
    T (combSchwartzTranslation (-(m:ℝ)) f)=0 := by
  apply hT
  intro x hx
  rw [endpointDeletedCarrier_recentered_mem α ha hi] at hx
  rcases hx with ⟨j,n,hn,rfl⟩|⟨j,n,hn,rfl⟩|⟨n,hn,rfl⟩
  · rw [combSchwartzTranslation_apply]
    by_cases he : n=m
    · subst n
      rw [show -(m:ℝ)+((m:ℝ)-(1/2-α j))=-(1/2-α j) by ring]
      exact hminus j hn
    · have hs : |-(1/2-α j)| < 1/2 := by rw [abs_neg,abs_of_pos (by linarith [(hi j).2])]; linarith [(hi j).1]
      simpa only [sub_eq_add_neg] using finite_central_other_cell f hf _ hs n m he
  · rw [combSchwartzTranslation_apply]
    by_cases he : n=m
    · subst n
      rw [show -(m:ℝ)+((m:ℝ)+(1/2-α j))=1/2-α j by ring]
      exact hplus j hn
    · have hs : |1/2-α j| < 1/2 := by rw [abs_of_pos (by linarith [(hi j).2])]; linarith [(hi j).1]
      exact finite_central_other_cell f hf _ hs n m he
  · rw [combSchwartzTranslation_apply]
    by_cases he : n=m
    · subst n
      rw [neg_add_cancel]
      exact hseam hn
    · simpa only [add_zero] using finite_central_other_cell f hf 0 (by norm_num) n m he

/-- The actual translated finite carrier lies in the same quarter-cell chart,
including the single zero seam. -/
theorem endpointDeletedCarrier_recentered_quarter {k : ℕ} (α : Fin k → ℝ)
    (ha : Function.Injective α) (hi : ∀ j, 0 < α j ∧ α j < 1/2)
    (hs : ∀ j, 1/4 ≤ α j) :
    ∀ x ∈ ((endpointDeletedCarrier α).translate (-1/2)).carrier,
      ∃ (a : ℝ) (n : ℤ), |a| ≤ 1/4 ∧ x=a+n := by
  intro x hx
  rw [endpointDeletedCarrier_recentered_mem α ha hi] at hx
  rcases hx with ⟨j,n,_hn,rfl⟩|⟨j,n,_hn,rfl⟩|⟨n,_hn,rfl⟩
  · refine ⟨-(1/2-α j),n,?_,by ring⟩
    rw [abs_neg,abs_of_pos (by linarith [(hi j).2])]
    linarith [hs j]
  · refine ⟨1/2-α j,n,?_,by ring⟩
    rw [abs_of_pos (by linarith [(hi j).2])]
    linarith [hs j]
  · exact ⟨0,n,by norm_num,by ring⟩

/-- The compact Fourier probe extracts the complete physical cluster also for
finite endpoint spectra; this includes its surviving endpoint cells. -/
theorem zakTensorAction_endpoint_chartProbe {k : ℕ} (β : Fin k → ℝ)
    (hb : Function.Injective β) (hi : ∀ j, 0 < β j ∧ β j < 1/2)
    (hs : ∀ j, 1/4 ≤ β j) (T : TemperedDistribution ℝ ℂ)
    (hFT : AtomicOnCarrier ((endpointDeletedCarrier β).translate (-1/2)) (𝓕 T))
    (f : SchwartzMap ℝ ℂ) (m : ℤ) :
    zakTensorAction T f (zakChartFourierProbe m)=T (combSchwartzTranslation (-(m:ℝ)) f) := by
  have hh := congrArg (fun U : TemperedDistribution ℝ ℂ => U f)
    (zakPhysicalSlice_chartFourierProbe _ T hFT (endpointDeletedCarrier_recentered_quarter β hb hi hs) m)
  simpa only [zakPhysicalSlice_apply,combDistributionTranslation_apply] using hh

/-- A retained physical phase is killed by every preceding complete Newton prefix. -/
theorem halfNewtonProduct_endpointPadded_phase_zero (P R k i : ℕ) (j : Fin k)
    (hj : j.val < i) (x : ℝ)
    (hx : x=rapidDistance P R (j.val+1) ∨ x= -rapidDistance P R (j.val+1)) :
    halfNewtonProduct (endpointPaddedDistance P R k) i x=0 := by
  have he : endpointPaddedDistance P R k ⟨j.val+1,by omega⟩=rapidDistance P R (j.val+1) :=
    ite_eq_left (Nat.succ_le_of_lt j.isLt)
  apply halfNewtonProduct_zero_at_head _ i ⟨j.val+1,by omega⟩ (by simpa using hj) x
  rwa [he]

/-- The actual zero-padded Newton row annihilates every interior physical
cluster. The finite seam is excluded by its exact holes or the zero Newton factor. -/
theorem endpointNewtonRow_cluster_zero {P R : ℕ} (hP : 1 ≤ P) (hR : 1 ≤ R)
    (k : ℕ) (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier ((endpointDeletedCarrier (rapidEndpointPhaseData P R k)).translate (-1/2)) T)
    (i : ℕ) (e : Bool) (m : ℤ) (hm : m.natAbs ≤ i) (hm' : (m+1).natAbs ≤ i) :
    T (combSchwartzTranslation (-(m:ℝ))
      (combSchwartzModulation (1/2) (halfNewtonTest (endpointPaddedDistance P R k) i e)))=0 := by
  apply endpointSource_cluster_zero _ (rapidEndpointPhaseData_injective hP hR k)
    (rapidEndpointPhaseData_interior hP hR k) T hT
  · intro x hx
    simp only [combSchwartzModulation_apply,halfNewtonTest_apply,zakCentralCutoff_zero x hx,zero_mul,mul_zero]
  · intro j hj
    have he : 1/2-rapidEndpointPhaseData P R k j=rapidDistance P R (j.val+1) := by
      unfold rapidEndpointPhaseData
      ring
    simp only [combSchwartzModulation_apply,halfNewtonTest_apply,halfNewtonFunction,he,
      halfNewtonProduct_endpointPadded_phase_zero P R k i j (hj.trans_le hm) _ (Or.inr rfl),mul_zero]
  · intro j hj
    have he : 1/2-rapidEndpointPhaseData P R k j=rapidDistance P R (j.val+1) := by
      unfold rapidEndpointPhaseData
      ring
    simp only [combSchwartzModulation_apply,halfNewtonTest_apply,halfNewtonFunction,he,
      halfNewtonProduct_endpointPadded_phase_zero P R k i j (hj.trans_le hm') _ (Or.inl rfl),mul_zero]
  · intro hs
    have hi : k < i := by omega
    have hh := halfNewtonProduct_endpointPadded_zero (P := P) (R := R) k i hi none
    simp only [endpointCenteredPhase] at hh
    simp only [combSchwartzModulation_apply,halfNewtonTest_apply,halfNewtonFunction,hh,mul_zero]

/-- Actual Fourier probe readings of the finite Newton row vanish on its full
interior band, from the complete two deleted carrier records. -/
theorem endpointNewtonRow_chartProbe_zero {P R : ℕ} (hP : 1 ≤ P) (hR : 1 ≤ R)
    (k : ℕ) (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier ((endpointDeletedCarrier (rapidEndpointPhaseData P R k)).translate (-1/2)) T)
    (hFT : AtomicOnCarrier ((endpointDeletedCarrier (rapidEndpointPhaseData P R k)).translate (-1/2)) (𝓕 T))
    (i : ℕ) (e : Bool) (m : ℤ) (hm : m.natAbs ≤ i) (hm' : (m+1).natAbs ≤ i) :
    zakTensorAction T (combSchwartzModulation (1/2) (halfNewtonTest (endpointPaddedDistance P R k) i e))
      (zakChartFourierProbe m)=0 := by
  rw [zakTensorAction_endpoint_chartProbe _ (rapidEndpointPhaseData_injective hP hR k)
    (rapidEndpointPhaseData_interior hP hR k) (fun j => by
      unfold rapidEndpointPhaseData
      linarith [(rapidDistance_bounds hP hR (j.val+1)).2]) T hFT]
  exact endpointNewtonRow_cluster_zero hP hR k T hT i e m hm hm'

end MeyerGeneralProblem.Adaptive
