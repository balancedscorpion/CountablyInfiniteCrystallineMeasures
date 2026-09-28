module

public import MeyerGeneralProblem.Cardinal.Adaptive.CriticalGreenFourier
public import MeyerGeneralProblem.Distribution.CompactSmoothDivision
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import all Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

@[expose] public section

/-! # Recover complete value-only sources from actual simple head multipliers -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open Filter
open scoped Topology ContDiff

/-- Compact removable division recovers the entire Schwartz vanishing ideal.
The multiplier action is an actual Schwartz CLM, and its zero set and the
incoming atomic carrier are retained explicitly. -/
theorem atomicOnCarrier_of_simple_multiplier (S R : LocallyFiniteCarrier)
    (q : ℝ → ℂ) (hq : ContDiff ℝ ∞ q)
    (hsimple : ∀ x, q x = 0 → deriv q x ≠ 0)
    (U : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ)
    (hU : ∀ f x, U f x = q x*f x)
    (hzeros : ∀ x, q x = 0 → x ∈ R.carrier)
    (hSR : S.carrier ⊆ R.carrier) (hS : ∀ x ∈ S.carrier, q x ≠ 0)
    (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier S (PointwiseConvergenceCLM.precomp ℂ U T)) :
    AtomicOnCarrier R T := by
  intro f hf
  have hc (g : SchwartzMap ℝ ℂ) (hg : HasCompactSupport g)
      (hgv : SchwartzVanishesOn R g) : T g = 0 := by
    have hz : ∀ x, q x = 0 → g x = 0 := fun x hx => hgv x (hzeros x hx)
    let ψ := compactSchwartzDivision g hg q hq hsimple hz
    have he : U ψ = g := by
      ext x
      rw [hU]
      exact mul_removableQuotient hz x
    rw [← he]
    apply hT ψ
    intro x hx
    change removableQuotient g q x = 0
    rw [removableQuotient,ite_eq_right (hS x hx),hgv x (hSR hx),zero_div]
  have hz (N : ℕ) : T (compactSchwartzApproximation N f) = 0 :=
    hc _ (compactSchwartzApproximation_hasCompactSupport N f)
      (compactSchwartzApproximation_preserves_vanishing R N f hf)
  have hl : Tendsto (fun N => T (compactSchwartzApproximation N f)) atTop (𝓝 (T f)) :=
    (T.continuous.tendsto f).comp (compactSchwartzApproximation_tendsto f)
  have h0 : Tendsto (fun N => T (compactSchwartzApproximation N f)) atTop (𝓝 0) := by
    simpa only [hz] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))
  exact tendsto_nhds_unique hl h0

/-- Smoothness of the original real Newton coordinate. -/
theorem criticalNewtonNode_contDiff : ContDiff ℝ ∞ criticalNewtonNode :=
  Complex.ofRealCLM.contDiff.comp (contDiff_const.sub ((contDiff_const.mul contDiff_id).cos))

/-- Smoothness of the accepted finite cosine product on the whole real line. -/
theorem criticalHeadTrigProduct_contDiff {k : ℕ} (α : Fin k → ℝ) :
    ContDiff ℝ ∞ (criticalHeadTrigProduct α) := by
  unfold criticalHeadTrigProduct
  have hc := criticalNewtonNode_contDiff
  fun_prop

/-- Exact derivative of the original Newton coordinate. -/
theorem criticalNewtonNode_hasDerivAt (x : ℝ) :
    HasDerivAt criticalNewtonNode ((2*Real.pi*Real.sin (2*Real.pi*x) : ℝ) : ℂ) x := by
  have h : HasDerivAt (fun y : ℝ => 1-Real.cos (2*Real.pi*y))
      (2*Real.pi*Real.sin (2*Real.pi*x)) x := by
    have hh := (hasDerivAt_const x (1 : ℝ)).sub
      (((hasDerivAt_id x).const_mul (2*Real.pi)).cos)
    simp only [id_eq,mul_one] at hh
    convert hh using 1 <;> first | rfl | ring
  exact h.ofReal_comp

/-- Every zero of the accepted head multiplier is simple, from distinct
strictly interior phases and the actual trigonometric derivative. -/
theorem criticalHeadTrigProduct_simple_zeros {k : ℕ} (α : Fin k → ℝ)
    (ha : Function.Injective α) (hi : ∀ i, 0 < α i ∧ α i < 1/2) :
    ∀ x, criticalHeadTrigProduct α x = 0 → deriv (criticalHeadTrigProduct α) x ≠ 0 := by
  intro x hx
  obtain ⟨i,_,hi0⟩ := Finset.prod_eq_zero_iff.mp hx
  have hnode : criticalNewtonNode x = criticalNewtonNode (α i) := sub_eq_zero.mp hi0
  have hcos : Real.cos (2*Real.pi*x) = Real.cos (2*Real.pi*(α i)) := by
    have h := Complex.ofReal_injective hnode
    linarith
  have hsinpos : 0 < Real.sin (2*Real.pi*(α i)) :=
    Real.sin_pos_of_pos_of_lt_pi (by nlinarith [Real.pi_pos,(hi i).1])
      (by nlinarith [Real.pi_pos,(hi i).2])
  have hsin : Real.sin (2*Real.pi*x) ≠ 0 := by
    intro hz
    have h1 := Real.sin_sq_add_cos_sq (2*Real.pi*x)
    have h2 := Real.sin_sq_add_cos_sq (2*Real.pi*(α i))
    rw [hz,hcos] at h1
    nlinarith
  let g : ℝ → ℂ := fun y => ∏ j ∈ Finset.univ.erase i,
    (criticalNewtonNode y-criticalNewtonNode (α j))
  have hg : ContDiff ℝ ∞ g := by
    dsimp [g]
    have hc := criticalNewtonNode_contDiff
    fun_prop
  have hg0 : g x ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj hz
    have he : criticalNewtonNode (α i)=criticalNewtonNode (α j) :=
      hnode.symm.trans (sub_eq_zero.mp hz)
    have hij := ha (criticalNewtonNode_injective_on_interior (hi i) (hi j) he)
    exact (Finset.mem_erase.mp hj).1 hij.symm
  have he : criticalHeadTrigProduct α = fun y =>
      (criticalNewtonNode y-criticalNewtonNode (α i))*g y := by
    funext y
    exact (Finset.mul_prod_erase Finset.univ
      (fun j => criticalNewtonNode y-criticalNewtonNode (α j)) (Finset.mem_univ i)).symm
  have hd := ((criticalNewtonNode_hasDerivAt x).sub_const (criticalNewtonNode (α i))).mul
    (hg.differentiable (by simp) x).hasDerivAt
  change HasDerivAt (fun y => (criticalNewtonNode y-criticalNewtonNode (α i))*g y) _ x at hd
  rw [← he] at hd
  rw [hd.deriv,hi0,zero_mul,add_zero]
  exact mul_ne_zero (by exact_mod_cast mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hsin) hg0

/-- Every unrestricted integer translate of every signed head phase. -/
def criticalHeadCosetSet {k : ℕ} (α : Fin k → ℝ) : Set ℝ :=
  {x | ∃ (i : Fin k) (u : Bool) (n : ℤ), x = (n : ℝ)+signedPhase u (α i)}

/-- The accepted head multiplier has exactly its complete signed head cosets as zeros. -/
theorem criticalHeadTrigProduct_zero_iff {k : ℕ} (α : Fin k → ℝ) (x : ℝ) :
    criticalHeadTrigProduct α x = 0 ↔ x ∈ criticalHeadCosetSet α := by
  constructor
  · intro hx
    obtain ⟨i,_,hi0⟩ := Finset.prod_eq_zero_iff.mp hx
    have hnode := sub_eq_zero.mp hi0
    have hcos : Real.cos (2*Real.pi*(α i))=Real.cos (2*Real.pi*x) := by
      have h := Complex.ofReal_injective hnode
      linarith
    obtain ⟨n,hn|hn⟩ := Real.cos_eq_cos_iff.mp hcos
    · refine ⟨i,true,n,?_⟩
      simp only [signedPhase,ite_true]
      apply mul_left_cancel₀ (show (2*Real.pi : ℝ) ≠ 0 by positivity)
      nlinarith
    · refine ⟨i,false,n,?_⟩
      simp only [signedPhase,Bool.false_eq_true,ite_false]
      apply mul_left_cancel₀ (show (2*Real.pi : ℝ) ≠ 0 by positivity)
      nlinarith
  · rintro ⟨i,u,n,rfl⟩
    apply Finset.prod_eq_zero_iff.mpr
    refine ⟨i,Finset.mem_univ _,?_⟩
    have hc (y : ℝ) : Real.cos (2*Real.pi*((n : ℝ)+y))=Real.cos (2*Real.pi*y) := by
      rw [show 2*Real.pi*((n : ℝ)+y)=2*Real.pi*y+(n : ℝ)*(2*Real.pi) by ring]
      exact Real.cos_add_int_mul_two_pi _ _
    simp only [criticalNewtonNode,hc]
    cases u <;> simp [signedPhase,mul_neg,Real.cos_neg]

/-- The unrestricted finite family of head cosets is locally finite. -/
def criticalHeadCosetCarrier {k : ℕ} (α : Fin k → ℝ) : LocallyFiniteCarrier where
  carrier := criticalHeadCosetSet α
  finite_inter_Icc a b := by
    have hf : (⋃ q : Fin k × Bool,
        (shiftedIntegerCombCarrier (signedPhase q.2 (α q.1))).carrier ∩ Set.Icc a b).Finite :=
      Set.finite_iUnion (fun q => (shiftedIntegerCombCarrier (signedPhase q.2 (α q.1))).finite_inter_Icc a b)
    apply hf.subset
    rintro x ⟨⟨i,u,n,hx⟩,hxI⟩
    apply Set.mem_iUnion.mpr
    refine ⟨(i,u),⟨?_,hxI⟩⟩
    refine ⟨n,?_⟩
    rw [hx]
    exact add_comm _ _

/-- Add unrestricted head cosets to an actual locally finite tail carrier. -/
def criticalHeadExtensionCarrier {k : ℕ} (β : Fin k → ℝ) (S : LocallyFiniteCarrier) :
    LocallyFiniteCarrier where
  carrier := criticalHeadCosetSet β ∪ S.carrier
  finite_inter_Icc a b := by
    simpa only [Set.union_inter_distrib_right,criticalHeadCosetCarrier] using
      ((criticalHeadCosetCarrier β).finite_inter_Icc a b).union (S.finite_inter_Icc a b)

/-- The actual simple cosine multiplier recovers a whole value-only source
on head cosets plus tail, without any assumed atomicity of that source. -/
theorem criticalHeadMultiplier_recovers_atomic {k : ℕ} (β : Fin k → ℝ)
    (hb : Function.Injective β) (hi : ∀ i, 0 < β i ∧ β i < 1/2)
    (S : LocallyFiniteCarrier) (hS : ∀ x ∈ S.carrier, criticalHeadTrigProduct β x ≠ 0)
    (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier S (criticalHeadMultiplierDistributionCLM β T)) :
    AtomicOnCarrier (criticalHeadExtensionCarrier β S) T := by
  exact atomicOnCarrier_of_simple_multiplier S (criticalHeadExtensionCarrier β S) (criticalHeadTrigProduct β) (criticalHeadTrigProduct_contDiff β)
    (criticalHeadTrigProduct_simple_zeros β hb hi) (criticalHeadMultiplierTestCLM β)
    (criticalHeadMultiplierTestCLM_apply β)
    (fun x hx => Or.inl ((criticalHeadTrigProduct_zero_iff β x).mp hx))
    (fun x hx => Or.inr hx) hS T hT

/-- First k phases of the original infinite sequence, with their original indices. -/
def criticalPrefixPhases (α : ℕ+ → ℝ) (k : ℕ) (i : Fin k) : ℝ :=
  α ⟨i.val+1,by omega⟩

/-- Distinct original phases give a distinct finite prefix. -/
theorem criticalPrefixPhases_injective (α : ℕ+ → ℝ) (ha : Function.Injective α) (k : ℕ) :
    Function.Injective (criticalPrefixPhases α k) := by
  intro i j he
  have h := congrArg (fun n : ℕ+ => (n : ℕ)) (ha he)
  apply Fin.ext
  change i.val+1=j.val+1 at h
  omega

/-- Every actual prefix retains the original strictly interior phase condition. -/
theorem criticalPrefixPhases_inside (α : ℕ+ → ℝ)
    (hi : ∀ j, 0 < α j ∧ α j < 1/2) (k : ℕ) :
    ∀ i, 0 < criticalPrefixPhases α k i ∧ criticalPrefixPhases α k i < 1/2 :=
  fun i => hi ⟨i.val+1,by omega⟩

/-- No tail point is a zero of its own actual prefix multiplier. Distinctness
is used on the original infinite sequence, not on a surrogate finite cap. -/
theorem criticalPrefix_nonzero_on_tail (α : ℕ+ → ℝ) (ha : Function.Injective α)
    (hi : ∀ j, 0 < α j ∧ α j < 1/2) (k : ℕ) :
    ∀ x ∈ criticalPhaseTailSet α k k, criticalHeadTrigProduct (criticalPrefixPhases α k) x ≠ 0 := by
  rintro x ⟨j,u,n,hn,hx⟩ hz
  obtain ⟨i,v,m,hy⟩ := (criticalHeadTrigProduct_zero_iff (criticalPrefixPhases α k) x).mp hz
  have hb : |signedPhase v (criticalPrefixPhases α k i)| < 1/2 := by
    have h := criticalPrefixPhases_inside α hi k i
    cases v <;> simpa [signedPhase,abs_of_pos h.1] using h.2
  have he := (integer_cell_unique (criticalTailPhase_abs_lt_half α hi k j u) hb (hx.symm.trans hy)).2
  have haeq : criticalTailPhases α k j = criticalPrefixPhases α k i := by
    have he' := congrArg abs he
    have hj := hi ⟨k+(j : ℕ),by have := j.pos; omega⟩
    have hi' := hi ⟨i.val+1,by omega⟩
    cases u <;> cases v <;>
      simpa [signedPhase,criticalTailPhases,criticalPrefixPhases,abs_of_pos hj.1,abs_of_pos hi'.1] using he'
  have hn := congrArg (fun z : ℕ+ => (z : ℕ)) (ha haeq)
  change k+(j : ℕ)=i.val+1 at hn
  have := j.pos
  have := i.isLt
  omega

/-- Actual restored physical carrier for the original complete sequence. -/
def criticalRestoredPhaseCarrier (α : ℕ+ → ℝ)
    (hi : ∀ j, 0 < α j ∧ α j < 1/2) (k : ℕ) : LocallyFiniteCarrier :=
  criticalHeadExtensionCarrier (criticalPrefixPhases α k) (criticalPhaseTailCarrier α hi k k)

/-- The actual whole preliminary inverse for two original infinite phase records. -/
def criticalFullPreinverseCLM (α β : ℕ+ → ℝ)
    (ha : Function.Injective α) (hia : ∀ j, 0 < α j ∧ α j < 1/2)
    (hb : Function.Injective β) (hib : ∀ j, 0 < β j ∧ β j < 1/2) (k : ℕ) :
    TemperedDistribution ℝ ℂ →L[ℂ] TemperedDistribution ℝ ℂ :=
  criticalWholePreinverseCLM (criticalPrefixPhases α k) (criticalPrefixPhases β k)
    (criticalPrefixPhases_injective α ha k) (criticalPrefixPhases_inside α hia k)
    (criticalPrefixPhases_injective β hb k) (criticalPrefixPhases_inside β hib k)

/-- Complete physical AND Fourier value-only records of the actual source
preinverse. No finite-cap or phasewise source representation is assumed. -/
theorem criticalFullPreinverse_atomic_records (α β : ℕ+ → ℝ)
    (ha : Function.Injective α) (hia : ∀ j, 0 < α j ∧ α j < 1/2)
    (hb : Function.Injective β) (hib : ∀ j, 0 < β j ∧ β j < 1/2) (k : ℕ) (hk : 1 ≤ k)
    (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier (criticalPhaseTailCarrier α hia k 0) T)
    (hFT : AtomicOnCarrier (criticalPhaseTailCarrier β hib k 0) (FourierTransform.fourier T)) :
    AtomicOnCarrier (criticalRestoredPhaseCarrier α hia k) (criticalFullPreinverseCLM α β ha hia hb hib k T) ∧
    AtomicOnCarrier (criticalRestoredPhaseCarrier β hib k)
      (FourierTransform.fourier (criticalFullPreinverseCLM α β ha hia hb hib k T)) := by
  constructor
  · apply criticalHeadMultiplier_recovers_atomic (criticalPrefixPhases α k)
      (criticalPrefixPhases_injective α ha k) (criticalPrefixPhases_inside α hia k)
      (criticalPhaseTailCarrier α hia k k) (criticalPrefix_nonzero_on_tail α ha hia k)
    exact criticalWholePreinverse_multiplier_tail hk _ _ _ _ _ _ α hia T hT
  · apply criticalHeadMultiplier_recovers_atomic (criticalPrefixPhases β k)
      (criticalPrefixPhases_injective β hb k) (criticalPrefixPhases_inside β hib k)
      (criticalPhaseTailCarrier β hib k k) (criticalPrefix_nonzero_on_tail β hb hib k)
    rw [← fourier_criticalHeadDifferenceDistribution]
    exact criticalWholePreinverse_fourier_difference_tail hk _ _ _ _ _ _ β hib T hFT

/-- The restored-source preinverse satisfies the exact original head equation. -/
theorem criticalFullPreinverse_rightInverse (α β : ℕ+ → ℝ)
    (ha : Function.Injective α) (hia : ∀ j, 0 < α j ∧ α j < 1/2)
    (hb : Function.Injective β) (hib : ∀ j, 0 < β j ∧ β j < 1/2) (k : ℕ) (hk : 1 ≤ k)
    (T : TemperedDistribution ℝ ℂ) :
    criticalHeadMultiplierDistributionCLM (criticalPrefixPhases α k)
      (criticalHeadDifferenceDistributionCLM (criticalPrefixPhases β k)
        (criticalFullPreinverseCLM α β ha hia hb hib k T)) = T :=
  criticalWholePreinverse_rightInverse hk _ _ _ _ _ _ T

/-- Every original native input has a two-order native representative of the
actual whole restored preinverse, with a head-only constant fixed before T. -/
theorem criticalFullPreinverse_native_bound (α β : ℕ+ → ℝ)
    (ha : Function.Injective α) (hia : ∀ j, 0 < α j ∧ α j < 1/2)
    (hb : Function.Injective β) (hib : ∀ j, 0 < β j ∧ β j < 1/2) (k p : ℕ) :
    ∃ C > 0, ∀ T : HermiteScale (-(p : ℤ)),
      ∃ U : HermiteScale (-((p+2 : ℕ) : ℤ)), ‖U‖ ≤ C*‖T‖ ∧
        hermiteScaleDistribution (p+2) U =
          criticalFullPreinverseCLM α β ha hia hb hib k (hermiteScaleDistribution p T) := by
  obtain ⟨C,hC,hbnd⟩ := criticalWholePreinverseNativeCLM_bound
    (criticalPrefixPhases α k) (criticalPrefixPhases β k)
    (criticalPrefixPhases_injective α ha k) (criticalPrefixPhases_inside α hia k)
    (criticalPrefixPhases_injective β hb k) (criticalPrefixPhases_inside β hib k) p
  refine ⟨C,hC,fun T => ⟨_,hbnd T,?_⟩⟩
  exact criticalWholePreinverseNativeCLM_realizes _ _ _ _ _ _ p T

/-- The head cosets of the concrete rapid block are the complete original half grid. -/
theorem criticalPrefix_block_cosets (P R : ℕ) (hR : 1 ≤ R) :
    criticalHeadCosetSet (criticalPrefixPhases (blockPhase P R) (headLength R)) =
      Set.range (halfShiftedGridPoint (headLength R)) := by
  ext x
  rw [mem_headGrid_iff P R hR x]
  constructor
  · rintro ⟨i,u,n,hx⟩
    exact ⟨⟨i.val+1,by omega⟩,u,n,i.isLt,hx⟩
  · rintro ⟨j,u,n,hj,hx⟩
    let i : Fin (headLength R) := ⟨(j : ℕ)-1,by have := j.pos; omega⟩
    have he : (⟨i.val+1,by omega⟩ : ℕ+) = j := by
      apply Subtype.ext
      change (j : ℕ)-1+1=(j : ℕ)
      have := j.pos
      omega
    refine ⟨i,u,n,?_⟩
    simpa only [criticalPrefixPhases,he] using hx

/-- The recovered complete source uses exactly the existing concrete restored
carrier, including every unchanged rapid-tail atom. -/
theorem criticalRestoredPhaseCarrier_block_eq (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) :
    (criticalRestoredPhaseCarrier (blockPhase P R) (blockPhase_mem_Ioo hP hR)
      (headLength R)).carrier = restoredHeadSet P R := by
  change criticalHeadCosetSet (criticalPrefixPhases (blockPhase P R) (headLength R)) ∪
    criticalPhaseTailSet (blockPhase P R) (headLength R) (headLength R) = _
  rw [criticalPrefix_block_cosets P R hR,criticalPhaseTailSet_block_restored]
  rfl

end
end MeyerGeneralProblem.Adaptive
