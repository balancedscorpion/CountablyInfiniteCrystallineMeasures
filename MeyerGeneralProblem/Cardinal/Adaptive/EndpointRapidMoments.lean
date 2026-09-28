module

public import MeyerGeneralProblem.Cardinal.Adaptive.EndpointRecenteredPairing
public import MeyerGeneralProblem.Cardinal.Adaptive.RapidMomentAdmission

@[expose] public section

/-! Concrete actual finite endpoint Newton moments and exact reconstruction. -/

noncomputable section
open scoped BigOperators

namespace MeyerGeneralProblem.Adaptive

/-- The exact finite functional of the actual recentered endpoint source,
including the fixed gauge correction of its literal coefficients. -/
def endpointCenteredAction {k : ℕ} (α β : Fin k → ℝ) (c : EndpointMatrix k) :
    (ℝ → ℝ → ℂ) →ₗ[ℂ] ℂ where
  toFun F := ∑ a, ∑ b, (c a b*endpointCenterFactor α β a b /
    fixedZakGauge (endpointCenteredPhase (fun i => 1/2-α i) a)
      (endpointCenteredPhase (fun i => 1/2-β i) b))*
    F (endpointCenteredPhase (fun i => 1/2-α i) a)
      (endpointCenteredPhase (fun i => 1/2-β i) b)
  map_add' F G := by simp [Pi.add_apply,mul_add,Finset.sum_add_distrib]
  map_smul' z F := by simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply,Finset.mul_sum,mul_left_comm]

/-- The finite functional agrees with the actual complete half-Weyl source
on the literal gauged reverse test. -/
theorem endpointCenteredAction_gaugedReverseZak {k : ℕ} (α β : Fin k → ℝ)
    (c : EndpointMatrix k) (f : SchwartzMap ℝ ℂ) :
    endpointCenteredAction α β c (gaugedReverseZakChart f) =
      halfWeylDistributionCLM (endpointPoissonSynthesis α β c) f := by
  rw [halfWeyl_endpointPoissonSynthesis_reverseZak]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  have hn : fixedZakGauge (endpointCenteredPhase (fun i => 1/2-α i) a)
      (endpointCenteredPhase (fun i => 1/2-β i) b) ≠ 0 := by
    exact Complex.exp_ne_zero _
  rw [gaugedReverseZakChart,← mul_assoc,div_mul_cancel₀ _ hn]

/-- Equality only at the actual finite phase pairs suffices for the actual
finite source functional. It is not an assumed carrier or norm certificate. -/
theorem endpointCenteredAction_congr {k : ℕ} (α β : Fin k → ℝ) (c : EndpointMatrix k)
    (F G : ℝ → ℝ → ℂ)
    (h : ∀ a b, F (endpointCenteredPhase (fun i => 1/2-α i) a)
      (endpointCenteredPhase (fun i => 1/2-β i) b) =
      G (endpointCenteredPhase (fun i => 1/2-α i) a)
      (endpointCenteredPhase (fun i => 1/2-β i) b)) :
    endpointCenteredAction α β c F = endpointCenteredAction α β c G := by
  unfold endpointCenteredAction
  simp only [LinearMap.coe_mk,AddHom.coe_mk]
  simp_rw [h]

/-- The actual interior phases for a finite rapid endpoint source. -/
def rapidEndpointPhaseData (P R k : ℕ) : Fin k → ℝ :=
  fun i => 1/2-rapidDistance P R (i.val+1)

/-- The positive-grid index underlying an actual signed endpoint phase. -/
def endpointPositiveGridIndex {k : ℕ} : EndpointPhaseIndex k → Fin (k+1)
  | none => Fin.last k
  | some (i,_) => i.castSucc

/-- Every recentered actual phase is one of the exact signed rapid nodes,
with the endpoint mapped to the single zero node. -/
theorem endpointCenteredPhase_rapid_mem (P R k : ℕ) (a : EndpointPhaseIndex k) :
    endpointCenteredPhase (fun i => 1/2-rapidEndpointPhaseData P R k i) a =
      rapidInterpolationPhase P R k (endpointPositiveGridIndex a) ∨
    endpointCenteredPhase (fun i => 1/2-rapidEndpointPhaseData P R k i) a =
      -rapidInterpolationPhase P R k (endpointPositiveGridIndex a) := by
  cases a with
  | none => left; simp [endpointCenteredPhase,endpointPositiveGridIndex,
      rapidInterpolationPhase,rapidFiniteDistance]
  | some a =>
      obtain ⟨i,u⟩ := a
      cases u
      · right
        change -(1/2-(1/2-rapidDistance P R (i.val+1))) =
          -(if i.val < k then rapidDistance P R (i.val+1) else 0)
        rw [ite_eq_left i.isLt]
        ring
      · left
        change 1/2-(1/2-rapidDistance P R (i.val+1)) =
          (if i.val < k then rapidDistance P R (i.val+1) else 0)
        rw [ite_eq_left i.isLt]
        ring

/-- Literal finite Newton moments of the actual recentered finite endpoint source.
This is a definition by its constructed coefficients, without an existence premise. -/
def rapidEndpointMoment (P R k : ℕ) (c : EndpointMatrix k) (e d : Bool)
    (i j : Fin (k+1)) : ℂ :=
  endpointCenteredAction (rapidEndpointPhaseData P R k) (rapidEndpointPhaseData P R k) c
    (fun x y => characteristicNewtonBasis e (rapidInterpolationPhase P R k) i x *
      characteristicNewtonBasis d (rapidInterpolationPhase P R k) j y)

/-- Full exact four-parity Newton pairing for the actual half-Weyl endpoint
source. Both the infinite source and finite moments are concrete definitions. -/
theorem halfWeyl_rapidEndpointSource_moment_pairing {P R : ℕ} (hP : 1 ≤ P) (hR : 1 ≤ R)
    (k : ℕ) (c : EndpointMatrix k) (f : SchwartzMap ℝ ℂ) :
    halfWeylDistributionCLM (endpointPoissonSynthesis
      (rapidEndpointPhaseData P R k) (rapidEndpointPhaseData P R k) c) f =
      ∑ e : Bool, ∑ d : Bool, ∑ i, ∑ j,
        rapidGridCoefficient P R hP hR k e d (gaugedReverseZakChart f) i j *
          rapidEndpointMoment P R k c e d i j := by
  let α := rapidEndpointPhaseData P R k
  let F : ℝ → ℝ → ℂ := ∑ e : Bool, ∑ d : Bool, ∑ i, ∑ j,
    rapidGridCoefficient P R hP hR k e d (gaugedReverseZakChart f) i j •
      (fun x y => characteristicNewtonBasis e (rapidInterpolationPhase P R k) i x *
        characteristicNewtonBasis d (rapidInterpolationPhase P R k) j y)
  rw [← endpointCenteredAction_gaugedReverseZak]
  have he : endpointCenteredAction α α c (gaugedReverseZakChart f) = endpointCenteredAction α α c F := by
    apply endpointCenteredAction_congr
    intro a b
    have hh := rapidGrid_reconstruct P R hP hR k (gaugedReverseZakChart f)
      (endpointPositiveGridIndex a) (endpointPositiveGridIndex b)
      (endpointCenteredPhase (fun i => 1/2-α i) a) (endpointCenteredPhase (fun i => 1/2-α i) b)
      (endpointCenteredPhase_rapid_mem P R k a) (endpointCenteredPhase_rapid_mem P R k b)
    simpa only [F,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,mul_assoc] using hh.symm
  rw [he]
  simp only [F,map_sum,map_smul,smul_eq_mul,rapidEndpointMoment,α]

/-- Actual rapid endpoint phase data satisfy the strict interior condition. -/
theorem rapidEndpointPhaseData_interior {P R : ℕ} (hP : 1 ≤ P) (hR : 1 ≤ R)
    (k : ℕ) (i : Fin k) : 0 < rapidEndpointPhaseData P R k i ∧ rapidEndpointPhaseData P R k i < 1/2 := by
  have hh := rapidDistance_bounds hP hR (i.val+1)
  unfold rapidEndpointPhaseData
  constructor <;> linarith [hh.1,hh.2]

/-- The actual finite rapid interior phases are distinct. -/
theorem rapidEndpointPhaseData_injective {P R : ℕ} (hP : 1 ≤ P) (hR : 1 ≤ R)
    (k : ℕ) : Function.Injective (rapidEndpointPhaseData P R k) := by
  intro i j hij
  have he : rapidDistance P R (i.val+1)=rapidDistance P R (j.val+1) := by
    unfold rapidEndpointPhaseData at hij
    linarith
  have hh := (rapidDistance_strictAnti hP hR).injective he
  exact Fin.ext (by omega)

/-- Exact actual normalized endpoint source moment pairing, using its constructed
matrix and the proved interior/injectivity data of the literal rapid phases. -/
theorem normalizedRapidEndpointSource_moment_pairing {P R : ℕ} (hP : 1 ≤ P) (hR : 1 ≤ R)
    (k : ℕ) (f : SchwartzMap ℝ ℂ) :
    halfWeylDistributionCLM (normalizedEndpointSource
      (rapidEndpointPhaseData P R k) (rapidEndpointPhaseData P R k)
      (rapidEndpointPhaseData_injective hP hR k) (rapidEndpointPhaseData_injective hP hR k)
      (rapidEndpointPhaseData_interior hP hR k) (rapidEndpointPhaseData_interior hP hR k)) f =
      ∑ e : Bool, ∑ d : Bool, ∑ i, ∑ j,
        rapidGridCoefficient P R hP hR k e d (gaugedReverseZakChart f) i j *
          rapidEndpointMoment P R k (normalizedEndpointMatrix
            (rapidEndpointPhaseData P R k) (rapidEndpointPhaseData P R k)
            (rapidEndpointPhaseData_injective hP hR k) (rapidEndpointPhaseData_injective hP hR k)
            (rapidEndpointPhaseData_interior hP hR k) (rapidEndpointPhaseData_interior hP hR k)) e d i j :=
  halfWeyl_rapidEndpointSource_moment_pairing hP hR k _ f

/-- The actual Schwartz test transpose of the inverse half-Weyl map. -/
def halfWeylInverseTest (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  combSchwartzModulation (1/2) (combSchwartzTranslation (1/2) f)

/-- Whole-source inversion is exact on every Schwartz test. -/
theorem halfWeylInverseTest_realizes (T : TemperedDistribution ℝ ℂ) (f : SchwartzMap ℝ ℂ) :
    T f=halfWeylDistributionCLM T (halfWeylInverseTest f) := by
  have hh := congrArg (fun S : TemperedDistribution ℝ ℂ => S f) (halfWeylInverse_left T)
  exact hh.symm

/-- The actual inverse half-Weyl test costs no additional original native order. -/
theorem exists_halfWeylInverseTest_native_bound (p : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : SchwartzMap ℝ ℂ,
      ‖schwartzToHermiteScale p (halfWeylInverseTest f)‖ ≤ C*‖schwartzToHermiteScale p f‖ := by
  obtain ⟨A,hA,ha⟩ := exists_hermite_translation_bound p
  obtain ⟨B,hB,hb⟩ := exists_hermite_modulation_bound p
  let D : ℝ := (1+|(1/2:ℝ)|)^(2*p)
  refine ⟨(B*D)*(A*D),by dsimp [D]; positivity,?_⟩
  intro f
  exact ((hb (1/2) (combSchwartzTranslation (1/2) f)).trans
    (mul_le_mul_of_nonneg_left (ha (1/2) f) (by positivity))).trans_eq (by ring)

/-- Actual whole finite endpoint sources satisfy the uniform original-native
bound once their concrete moments satisfy the full-maximum estimate. The only
remaining analytic premise is stated on those actual moments, not a source certificate. -/
theorem exists_rapidEndpointSource_pairing_bound {P R : ℕ}
    (hP : 1 ≤ P) (hR : 1 ≤ R) (L : ℕ) (hL : 4 < rapidBase P^L)
    (K : ℝ) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, ∀ c : EndpointMatrix k, ∀ A : ℝ, 0 ≤ A →
      (∀ e d i j, ‖rapidEndpointMoment P R k c e d i j‖ ≤
        A*K^(max i.val j.val)*shrinkingNewtonWeight (rapidDistance P R) (max i.val j.val)) →
      ∀ f : SchwartzMap ℝ ℂ,
      ‖endpointPoissonSynthesis (rapidEndpointPhaseData P R k) (rapidEndpointPhaseData P R k) c f‖ ≤
        C*A*‖schwartzToHermiteScale (2*L+2) f‖ := by
  obtain ⟨B,hB,hb⟩ := exists_gaugedReverseZak_four_parity_moment_bound hP hR L hL K hK
  obtain ⟨D,hD,hd⟩ := exists_halfWeylInverseTest_native_bound (2*L+2)
  refine ⟨B*D,mul_pos hB hD,?_⟩
  intro k c A hA hM f
  rw [halfWeylInverseTest_realizes,halfWeyl_rapidEndpointSource_moment_pairing hP hR]
  exact ((hb k (halfWeylInverseTest f) A hA (rapidEndpointMoment P R k c) hM).trans
    (mul_le_mul_of_nonneg_left (hd f) (by positivity))).trans_eq (by ring)

end MeyerGeneralProblem.Adaptive
