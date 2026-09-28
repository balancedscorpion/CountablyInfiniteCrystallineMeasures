module

public import MeyerGeneralProblem.Cardinal.Adaptive.EndpointHalfNewtonCoordinates
public import MeyerGeneralProblem.Cardinal.Adaptive.HalfCoordinateReverseZak

@[expose] public section

/-! Actual finite endpoint pairing in the literal HalfNewton coordinate convention. -/
noncomputable section
open scoped BigOperators
namespace MeyerGeneralProblem.Adaptive
/-- The exact finite functional of the actual recentered endpoint source,
including the fixed gauge correction of its literal coefficients. -/
def endpointHalfCoordinateAction {k : ℕ} (α β : Fin k → ℝ) (c : EndpointMatrix k) :
    (ℝ → ℝ → ℂ) →ₗ[ℂ] ℂ where
  toFun F := ∑ a, ∑ b, (c a b*endpointCenterFactor α β a b /
    halfCoordinateGauge (endpointCenteredPhase (fun i => 1/2-α i) a)
      (endpointCenteredPhase (fun i => 1/2-β i) b))*
    F (endpointCenteredPhase (fun i => 1/2-α i) a)
      (endpointCenteredPhase (fun i => 1/2-β i) b)
  map_add' F G := by simp [Pi.add_apply,mul_add,Finset.sum_add_distrib]
  map_smul' z F := by simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply,Finset.mul_sum,mul_left_comm]

/-- The finite functional agrees with the actual complete half-Weyl source
on the literal gauged reverse test. -/
theorem endpointHalfCoordinateAction_halfCoordinateReverseZak {k : ℕ} (α β : Fin k → ℝ)
    (c : EndpointMatrix k) (f : SchwartzMap ℝ ℂ) :
    endpointHalfCoordinateAction α β c (halfCoordinateReverseZakChart f) =
      halfWeylDistributionCLM (endpointPoissonSynthesis α β c) f := by
  rw [halfWeyl_endpointPoissonSynthesis_reverseZak]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  have hn : halfCoordinateGauge (endpointCenteredPhase (fun i => 1/2-α i) a)
      (endpointCenteredPhase (fun i => 1/2-β i) b) ≠ 0 := by
    exact mul_ne_zero (Complex.exp_ne_zero _) (Complex.exp_ne_zero _)
  rw [halfCoordinateReverseZakChart,← mul_assoc,div_mul_cancel₀ _ hn]

/-- Equality only at the actual finite phase pairs suffices for the actual
finite source functional. It is not an assumed carrier or norm certificate. -/
theorem endpointHalfCoordinateAction_congr {k : ℕ} (α β : Fin k → ℝ) (c : EndpointMatrix k)
    (F G : ℝ → ℝ → ℂ)
    (h : ∀ a b, F (endpointCenteredPhase (fun i => 1/2-α i) a)
      (endpointCenteredPhase (fun i => 1/2-β i) b) =
      G (endpointCenteredPhase (fun i => 1/2-α i) a)
      (endpointCenteredPhase (fun i => 1/2-β i) b)) :
    endpointHalfCoordinateAction α β c F = endpointHalfCoordinateAction α β c G := by
  unfold endpointHalfCoordinateAction
  simp only [LinearMap.coe_mk,AddHom.coe_mk]
  simp_rw [h]

/-- Literal finite Newton moments of the actual recentered finite endpoint source.
This is a definition by its constructed coefficients, without an existence premise. -/
def rapidEndpointHalfCoordinate (P R k : ℕ) (c : EndpointMatrix k) (e d : Bool)
    (i j : Fin (k+1)) : ℂ :=
  endpointHalfCoordinateAction (rapidEndpointPhaseData P R k) (rapidEndpointPhaseData P R k) c
    (fun x y => characteristicNewtonBasis e (rapidInterpolationPhase P R k) i x *
      characteristicNewtonBasis d (rapidInterpolationPhase P R k) j y)

/-- Full exact four-parity Newton pairing for the actual half-Weyl endpoint
source. Both the infinite source and finite moments are concrete definitions. -/
theorem halfWeyl_rapidEndpointSource_halfCoordinate_pairing {P R : ℕ} (hP : 1 ≤ P) (hR : 1 ≤ R)
    (k : ℕ) (c : EndpointMatrix k) (f : SchwartzMap ℝ ℂ) :
    halfWeylDistributionCLM (endpointPoissonSynthesis
      (rapidEndpointPhaseData P R k) (rapidEndpointPhaseData P R k) c) f =
      ∑ e : Bool, ∑ d : Bool, ∑ i, ∑ j,
        rapidGridCoefficient P R hP hR k e d (halfCoordinateReverseZakChart f) i j *
          rapidEndpointHalfCoordinate P R k c e d i j := by
  let α := rapidEndpointPhaseData P R k
  let F : ℝ → ℝ → ℂ := ∑ e : Bool, ∑ d : Bool, ∑ i, ∑ j,
    rapidGridCoefficient P R hP hR k e d (halfCoordinateReverseZakChart f) i j •
      (fun x y => characteristicNewtonBasis e (rapidInterpolationPhase P R k) i x *
        characteristicNewtonBasis d (rapidInterpolationPhase P R k) j y)
  rw [← endpointHalfCoordinateAction_halfCoordinateReverseZak]
  have he : endpointHalfCoordinateAction α α c (halfCoordinateReverseZakChart f) = endpointHalfCoordinateAction α α c F := by
    apply endpointHalfCoordinateAction_congr
    intro a b
    have hh := rapidGrid_reconstruct P R hP hR k (halfCoordinateReverseZakChart f)
      (endpointPositiveGridIndex a) (endpointPositiveGridIndex b)
      (endpointCenteredPhase (fun i => 1/2-α i) a) (endpointCenteredPhase (fun i => 1/2-α i) b)
      (endpointCenteredPhase_rapid_mem P R k a) (endpointCenteredPhase_rapid_mem P R k b)
    simpa only [F,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,mul_assoc] using hh.symm
  rw [he]
  simp only [F,map_sum,map_smul,smul_eq_mul,rapidEndpointHalfCoordinate,α]

/-- The inverse linear gauge is exactly the two actual half-coordinate characters. -/
theorem halfCoordinateGauge_inv (x y : ℝ) :
    (halfCoordinateGauge x y)⁻¹ =
      combModulationCharacter (1/2) x*combModulationCharacter (-1/2) y := by
  simp only [halfCoordinateGauge,mul_inv,← Complex.exp_neg,combModulationCharacter_eq_exp]
  congr 1 <;> congr 1 <;> push_cast <;> ring

/-- The finite rapid interpolation basis is the literal infinite-prefix HalfNewton function. -/
theorem characteristicNewtonBasis_eq_halfNewtonFunction (P R k : ℕ) (i : Fin (k+1))
    (e : Bool) (x : ℝ) :
    characteristicNewtonBasis e (rapidInterpolationPhase P R k) i x =
      halfNewtonFunction (fun r => rapidDistance P R r.val) i.val e x := by
  unfold characteristicNewtonBasis halfNewtonFunction parityTrigFactor halfNewtonProduct
  rw [eval_newtonBasisPolynomial]
  congr 1
  apply Finset.prod_bij (fun a _ => a.val)
  · intro a ha
    have hh : a < i := Finset.mem_Iio.mp ha
    exact Finset.mem_range.mpr hh
  · intro a ha b hb hab
    exact Fin.ext hab
  · intro a ha
    exact ⟨⟨a,by have := Finset.mem_range.mp ha; omega⟩,Finset.mem_Iio.mpr
      (Finset.mem_range.mp ha),rfl⟩
  · intro a ha
    have hak : a.val < k := by have := Finset.mem_Iio.mp ha; omega
    simp only [rapidInterpolationPhase,rapidFiniteDistance,ite_eq_left hak,
      criticalNewtonNode,parityNewtonCoordinate]
    rfl

/-- Every actual recentered rapid endpoint representative lies in the flat central cutoff. -/
theorem endpointCenteredPhase_rapid_small {P R : ℕ} (hP : 1 ≤ P) (hR : 1 ≤ R)
    (k : ℕ) (a : EndpointPhaseIndex k) :
    |endpointCenteredPhase (fun i => 1/2-rapidEndpointPhaseData P R k i) a| ≤ 1/4 := by
  cases a with
  | none => simp [endpointCenteredPhase]
  | some a =>
      obtain ⟨i,e⟩ := a
      have hh := rapidDistance_bounds hP hR (i.val+1)
      have he : 1/2-rapidEndpointPhaseData P R k i=rapidDistance P R (i.val+1) := by
        unfold rapidEndpointPhaseData
        ring
      cases e <;> simp only [endpointCenteredPhase,he,Bool.false_eq_true,ite_false,
        ite_true,abs_neg,abs_of_pos hh.1] <;> linarith [hh.2]

/-- Actual HalfNewton coordinates are linear in the whole tempered source. -/
def halfNewtonCoordinateSourceLM (ε δ : ℕ+ → ℝ) (i j : ℕ) (e d : Bool) :
    TemperedDistribution ℝ ℂ →ₗ[ℂ] ℂ where
  toFun T := T (zakSchwartzTranspose (combSchwartzModulation (-1/2) (halfNewtonTest δ j d))
    (combSchwartzModulation (1/2) (halfNewtonTest ε i e)))
  map_add' T U := by simp
  map_smul' z T := by simp

/-- The source evaluation map realizes exactly the existing HalfNewton definition. -/
theorem halfNewtonCoordinateSourceLM_apply (ε δ : ℕ+ → ℝ) (i j : ℕ) (e d : Bool)
    (T : TemperedDistribution ℝ ℂ) :
    halfNewtonCoordinateSourceLM ε δ i j e d T=halfNewtonCoordinate ε δ T i e j d := by
  exact zakSchwartzTranspose_realizes T _ _

/-- Literal finite Newton coordinates coincide with the actual whole-source HalfNewton
coordinates, with all signed cells and the single endpoint retained. -/
theorem rapidEndpointHalfCoordinate_eq_actual {P R : ℕ} (hP : 1 ≤ P) (hR : 1 ≤ R)
    (k : ℕ) (c : EndpointMatrix k) (e d : Bool) (i j : Fin (k+1)) :
    rapidEndpointHalfCoordinate P R k c e d i j =
      halfNewtonCoordinate (fun r => rapidDistance P R r.val) (fun r => rapidDistance P R r.val)
        (halfWeylDistributionCLM (endpointPoissonSynthesis
          (rapidEndpointPhaseData P R k) (rapidEndpointPhaseData P R k) c)) i.val e j.val d := by
  rw [← halfNewtonCoordinateSourceLM_apply,halfWeyl_endpointPoissonSynthesis]
  simp only [map_sum,map_smul,smul_eq_mul,halfNewtonCoordinateSourceLM_apply]
  unfold rapidEndpointHalfCoordinate endpointHalfCoordinateAction
  simp only [LinearMap.coe_mk,AddHom.coe_mk]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [halfNewtonCoordinate_wholePoisson_central _ _ _ _
    (endpointCenteredPhase_rapid_small hP hR k a) (endpointCenteredPhase_rapid_small hP hR k b)]
  rw [div_eq_mul_inv,halfCoordinateGauge_inv,
    characteristicNewtonBasis_eq_halfNewtonFunction,characteristicNewtonBasis_eq_halfNewtonFunction]
  ring
/-- Actual whole finite endpoint sources satisfy the uniform original-native
bound once their concrete moments satisfy the full-maximum estimate. The only
remaining analytic premise is stated on those actual moments, not a source certificate. -/
theorem exists_rapidEndpointSource_literal_pairing_bound {P R : ℕ}
    (hP : 1 ≤ P) (hR : 1 ≤ R) (L : ℕ) (hL : 4 < rapidBase P^L)
    (K : ℝ) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, ∀ c : EndpointMatrix k, ∀ A : ℝ, 0 ≤ A →
      (∀ e d i j, ‖rapidEndpointHalfCoordinate P R k c e d i j‖ ≤
        A*K^(max i.val j.val)*shrinkingNewtonWeight (rapidDistance P R) (max i.val j.val)) →
      ∀ f : SchwartzMap ℝ ℂ,
      ‖endpointPoissonSynthesis (rapidEndpointPhaseData P R k) (rapidEndpointPhaseData P R k) c f‖ ≤
        C*A*‖schwartzToHermiteScale (2*L+2) f‖ := by
  have hX (e d : Bool) := exists_halfCoordinateReverseZak_rapidGridCoefficient_bound e d L
  have hh := exists_chart_four_parity_moment_bound hP hR L hL K hK halfCoordinateReverseZakChart
    (fun e d => by
      obtain ⟨C,hC,hc⟩ := hX e d
      exact ⟨C,hC,hc P R hP hR⟩)
  obtain ⟨B,hB,hb⟩ := hh
  obtain ⟨D,hD,hd⟩ := exists_halfWeylInverseTest_native_bound (2*L+2)
  refine ⟨B*D,mul_pos hB hD,?_⟩
  intro k c A hA hM f
  rw [halfWeylInverseTest_realizes,halfWeyl_rapidEndpointSource_halfCoordinate_pairing hP hR]
  exact ((hb k (halfWeylInverseTest f) A hA (rapidEndpointHalfCoordinate P R k c) hM).trans
    (mul_le_mul_of_nonneg_left (hd f) (by positivity))).trans_eq (by ring)

/-- The prescribed normalization can only increase the norm of a raw HalfNewton coordinate. -/
theorem halfNewtonCoordinate_norm_le_moment (ε δ : ℕ+ → ℝ)
    (T : TemperedDistribution ℝ ℂ) (i j : ℕ) (e d : Bool) :
    ‖halfNewtonCoordinate ε δ T i e j d‖ ≤ ‖halfNewtonMoment ε δ T i e j d‖ := by
  let z : ℂ := (1/4096 : ℂ)^(i+j)*(1/64 : ℂ)^(e.toNat+d.toNat)
  have hz : z ≠ 0 := by
    dsimp [z]
    apply mul_ne_zero <;> apply pow_ne_zero <;> norm_num
  have he : halfNewtonCoordinate ε δ T i e j d = z*halfNewtonMoment ε δ T i e j d := by
    rw [halfNewtonMoment,← mul_assoc,mul_inv_cancel₀ hz,one_mul]
  have hn : ‖z‖ ≤ 1 := by
    dsimp [z]
    rw [norm_mul,norm_pow,norm_pow]
    have h1 : ‖(1/4096 : ℂ)‖ ≤ 1 := by norm_num
    have h2 : ‖(1/64 : ℂ)‖ ≤ 1 := by norm_num
    exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) h1) (by positivity)
      (pow_le_one₀ (norm_nonneg _) h2)
  calc
    _ = ‖z*halfNewtonMoment ε δ T i e j d‖ := congrArg norm he
    _ ≤ 1*‖halfNewtonMoment ε δ T i e j d‖ := by rw [norm_mul]; gcongr
    _ = _ := one_mul _

/-- Actual original-native admission transfer from the existing normalized HalfNewton
moment array of the complete recentered finite source. The B07 decay premise is explicit. -/
theorem exists_rapidEndpointSource_actualMoment_pairing_bound {P R : ℕ}
    (hP : 1 ≤ P) (hR : 1 ≤ R) (L : ℕ) (hL : 4 < rapidBase P^L)
    (K : ℝ) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, ∀ c : EndpointMatrix k, ∀ A : ℝ, 0 ≤ A →
      (∀ (e d : Bool) (i j : Fin (k+1)),
        ‖halfNewtonMoment (fun r => rapidDistance P R r.val) (fun r => rapidDistance P R r.val)
          (halfWeylDistributionCLM (endpointPoissonSynthesis
            (rapidEndpointPhaseData P R k) (rapidEndpointPhaseData P R k) c)) i.val e j.val d‖ ≤
        A*K^(max i.val j.val)*shrinkingNewtonWeight (rapidDistance P R) (max i.val j.val)) →
      ∀ f : SchwartzMap ℝ ℂ,
      ‖endpointPoissonSynthesis (rapidEndpointPhaseData P R k) (rapidEndpointPhaseData P R k) c f‖ ≤
        C*A*‖schwartzToHermiteScale (2*L+2) f‖ := by
  obtain ⟨C,hC,hc⟩ := exists_rapidEndpointSource_literal_pairing_bound hP hR L hL K hK
  refine ⟨C,hC,?_⟩
  intro k c A hA hM
  apply hc k c A hA
  intro e d i j
  rw [rapidEndpointHalfCoordinate_eq_actual hP hR]
  exact (halfNewtonCoordinate_norm_le_moment _ _ _ _ _ _ _).trans (hM e d i j)

/-- A single original Schwartz observation for the zeroth even HalfNewton coordinate.
It is independent of every rapid phase, finite cap and source. -/
def endpointZerothObservation : SchwartzMap ℝ ℂ :=
  combSchwartzTranslation (-1/2) (combSchwartzModulation (-1/2)
    (zakSchwartzTranspose (combSchwartzModulation (-1/2) (halfNewtonTest (fun _ => 0) 0 false))
      (combSchwartzModulation (1/2) (halfNewtonTest (fun _ => 0) 0 false))))

/-- Literal zeroth coordinate normalization is an actual fixed Schwartz observation,
with no finite matrix corner or source-dependent probe substituted for it. -/
theorem endpointZerothObservation_realizes (ε δ : ℕ+ → ℝ) (T : TemperedDistribution ℝ ℂ) :
    T endpointZerothObservation = halfNewtonMoment ε δ (halfWeylDistributionCLM T) 0 false 0 false := by
  have he (ε : ℕ+ → ℝ) : halfNewtonTest ε 0 false=halfNewtonTest (fun _ => 0) 0 false := by
    ext x
    simp only [halfNewtonTest_apply,halfNewtonFunction,halfNewtonProduct,
      Finset.range_zero,Finset.prod_empty]
  simp only [halfNewtonMoment,Nat.zero_add,Bool.toNat_false,pow_zero,mul_one,inv_one,one_mul]
  rw [← halfNewtonCoordinateSourceLM_apply]
  unfold halfNewtonCoordinateSourceLM
  simp only [LinearMap.coe_mk,AddHom.coe_mk,he]
  rfl

end MeyerGeneralProblem.Adaptive
