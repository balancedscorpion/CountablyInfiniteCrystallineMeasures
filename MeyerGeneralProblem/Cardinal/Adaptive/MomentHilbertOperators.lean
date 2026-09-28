module

public import MeyerGeneralProblem.Cardinal.Adaptive.SeamShiftOperators
public import MeyerGeneralProblem.Cardinal.Adaptive.ProjectedComplementBounds

@[expose] public section

/-! # Actual coordinate operators on square-summable moment arrays -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open scoped ENNReal
attribute [local instance] Classical.propDecidable

/-- Square-summable complex coordinates on the actual countable index set. -/
abbrev MomentHilbert (ι : Type*) := lp (fun _ : ι => ℂ) 2

/-- A literal bounded diagonal multiplication on square-summable coordinates. -/
def momentDiagonalVector {ι : Type*} (a : ι → ℂ) (K : ℝ)
    (ha : ∀ i, ‖a i‖ ≤ K) (u : MomentHilbert ι) : MomentHilbert ι :=
  ⟨fun i => a i*u i,((lp.memℓp u).norm.const_mul K).mono (fun i => by
    rw [norm_mul]; exact mul_le_mul_of_nonneg_right (ha i) (norm_nonneg _))⟩

theorem momentDiagonalVector_norm_le {ι : Type*} (a : ι → ℂ) (K : ℝ)
    (hK : 0 ≤ K) (ha : ∀ i, ‖a i‖ ≤ K) (u : MomentHilbert ι) :
    ‖momentDiagonalVector a K ha u‖ ≤ K*‖u‖ := by
  have h := lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (x := momentDiagonalVector a K ha u) (y := (K : ℂ) •u) (fun i => by
      change ‖a i*u i‖ ≤ ‖(K : ℂ)*u i‖
      rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hK]
      exact mul_le_mul_of_nonneg_right (ha i) (norm_nonneg _))
  simpa only [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hK] using h

/-- The actual bounded diagonal operator, with an explicit original norm bound. -/
def momentDiagonal {ι : Type*} (a : ι → ℂ) (K : ℝ)
    (hK : 0 ≤ K) (ha : ∀ i, ‖a i‖ ≤ K) : MomentHilbert ι →L[ℂ] MomentHilbert ι :=
  LinearMap.mkContinuous
    { toFun := momentDiagonalVector a K ha
      map_add' u v := by ext i; change a i*(u i+v i)=a i*u i+a i*v i; ring
      map_smul' z u := by ext i; change a i*(z*u i)=z*(a i*u i); ring }
    K (momentDiagonalVector_norm_le a K hK ha)

@[simp] theorem momentDiagonal_apply {ι : Type*} (a : ι → ℂ) (K : ℝ)
    (hK : 0 ≤ K) (ha : ∀ i, ‖a i‖ ≤ K) (u : MomentHilbert ι) (i : ι) :
    momentDiagonal a K hK ha u i=a i*u i := rfl

theorem momentDiagonal_norm_le {ι : Type*} (a : ι → ℂ) (K : ℝ)
    (hK : 0 ≤ K) (ha : ∀ i, ‖a i‖ ≤ K) : ‖momentDiagonal a K hK ha‖ ≤ K :=
  ContinuousLinearMap.opNorm_le_bound _ hK (momentDiagonalVector_norm_le a K hK ha)

/-- The genuine coordinate projection onto any subset of indices. -/
def momentProjection {ι : Type*} (s : Set ι) : MomentHilbert ι →L[ℂ] MomentHilbert ι :=
  momentDiagonal (fun i => if i ∈ s then 1 else 0) 1 zero_le_one
    (fun i => by split_ifs <;> norm_num)

@[simp] theorem momentProjection_apply {ι : Type*} (s : Set ι) (u : MomentHilbert ι) (i : ι) :
    momentProjection s u i=if i ∈ s then u i else 0 := by
  classical
  simp only [momentProjection,momentDiagonal_apply]
  split_ifs <;> simp

theorem momentProjection_norm_le_one {ι : Type*} (s : Set ι) : ‖momentProjection s‖ ≤ 1 :=
  momentDiagonal_norm_le _ _ _ _

@[simp] theorem momentProjection_idempotent {ι : Type*} (s : Set ι) (u : MomentHilbert ι) :
    momentProjection s (momentProjection s u)=momentProjection s u := by
  ext i
  simp only [momentProjection_apply]
  split_ifs <;> rfl

theorem momentProjection_inter {ι : Type*} (s t : Set ι) (u : MomentHilbert ι) :
    momentProjection s (momentProjection t u)=momentProjection (s ∩ t) u := by
  ext i
  classical
  simp only [momentProjection_apply,Set.mem_inter_iff]
  split_ifs <;> simp_all

/-- Coordinate pullback along an actual injection. -/
def momentPullbackVector {ι κ : Type*} (f : ι → κ) (hf : Function.Injective f)
    (u : MomentHilbert κ) : MomentHilbert ι :=
  ⟨fun i => u (f i),memℓp_gen (((lp.memℓp u).summable (by norm_num)).comp_injective hf)⟩

theorem momentPullbackVector_norm_le {ι κ : Type*} (f : ι → κ) (hf : Function.Injective f)
    (u : MomentHilbert κ) : ‖momentPullbackVector f hf u‖ ≤ ‖u‖ := by
  apply lp.norm_le_of_tsum_le (by norm_num) (norm_nonneg _)
  rw [lp.norm_rpow_eq_tsum (by norm_num)]
  exact tsum_comp_le_tsum_of_inj ((lp.memℓp u).summable (by norm_num))
    (fun i => by positivity) hf

/-- Pullback is a contraction on the complete square-summable space. -/
def momentPullback {ι κ : Type*} (f : ι → κ) (hf : Function.Injective f) :
    MomentHilbert κ →L[ℂ] MomentHilbert ι :=
  LinearMap.mkContinuous
    { toFun := momentPullbackVector f hf
      map_add' u v := by ext i; rfl
      map_smul' z u := by ext i; rfl } 1
    (fun u => by simpa using momentPullbackVector_norm_le f hf u)

@[simp] theorem momentPullback_apply {ι κ : Type*} (f : ι → κ) (hf : Function.Injective f)
    (u : MomentHilbert κ) (i : ι) : momentPullback f hf u i=u (f i) := rfl

theorem momentPullback_norm_le_one {ι κ : Type*} (f : ι → κ) (hf : Function.Injective f) :
    ‖momentPullback f hf‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  change ‖momentPullbackVector f hf u‖ ≤ 1*‖u‖
  simpa using momentPullbackVector_norm_le f hf u

end
end MeyerGeneralProblem.Adaptive
