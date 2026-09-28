module

public import MeyerGeneralProblem.Cardinal.Adaptive.MomentHilbertOperators

@[expose] public section

/-! # Genuine isometric coordinate insertion in the complete moment space -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
attribute [local instance] Classical.propDecidable

private theorem momentExtend_at {ι κ : Type*} (f : ι → κ) (hf : Function.Injective f)
    (u : ι → ℂ) (i : ι) : Function.extend f u 0 (f i)=u i :=
  congrFun (Function.extend_comp hf u 0) i

private theorem momentExtend_off {ι κ : Type*} (f : ι → κ) (u : ι → ℂ)
    (k : κ) (hk : k ∉ Set.range f) : Function.extend f u 0 k=0 :=
  Function.extend_apply' u (0 : κ → ℂ) k hk

/-- Insert an actual square-summable family along an injection, with zero
on every complementary coordinate. -/
def momentEmbeddingVector {ι κ : Type*} (f : ι → κ) (hf : Function.Injective f)
    (u : MomentHilbert ι) : MomentHilbert κ :=
  ⟨Function.extend f u 0,memℓp_gen (by
    apply (hf.summable_iff (fun k hk => ?_)).mp
    · simpa only [Function.comp_def,momentExtend_at f hf] using (lp.memℓp u).summable (by norm_num)
    · rw [momentExtend_off f u k hk,norm_zero]
      simp)⟩

@[simp] theorem momentEmbeddingVector_at {ι κ : Type*} (f : ι → κ) (hf : Function.Injective f)
    (u : MomentHilbert ι) (i : ι) : momentEmbeddingVector f hf u (f i)=u i :=
  momentExtend_at f hf u i

@[simp] theorem momentEmbeddingVector_off {ι κ : Type*} (f : ι → κ) (hf : Function.Injective f)
    (u : MomentHilbert ι) (k : κ) (hk : k ∉ Set.range f) : momentEmbeddingVector f hf u k=0 :=
  momentExtend_off f u k hk

theorem momentEmbeddingVector_norm {ι κ : Type*} (f : ι → κ) (hf : Function.Injective f)
    (u : MomentHilbert ι) : ‖momentEmbeddingVector f hf u‖=‖u‖ := by
  rw [lp.norm_eq_tsum_rpow (by norm_num),lp.norm_eq_tsum_rpow (by norm_num)]
  congr 1
  have hsupport : Function.support (fun k => ‖momentEmbeddingVector f hf u k‖^(2 : ℝ)) ⊆ Set.range f := by
    intro k hk
    by_contra h
    have hz := momentEmbeddingVector_off f hf u k h
    simp only [Function.mem_support,norm_zero,ne_eq] at hk
    rw [hz,norm_zero,Real.zero_rpow (by norm_num : (2 : ℝ) ≠ 0)] at hk
    exact hk rfl
  simpa only [momentEmbeddingVector_at,ENNReal.toReal_ofNat] using (hf.tsum_eq hsupport).symm

/-- Actual insertion is a bounded linear isometry on the whole Hilbert space. -/
def momentEmbedding {ι κ : Type*} (f : ι → κ) (hf : Function.Injective f) :
    MomentHilbert ι →L[ℂ] MomentHilbert κ :=
  LinearMap.mkContinuous
    { toFun := momentEmbeddingVector f hf
      map_add' u v := by
        ext k
        by_cases hk : k ∈ Set.range f
        · obtain ⟨i,rfl⟩ := hk
          change momentEmbeddingVector f hf (u+v) (f i)=momentEmbeddingVector f hf u (f i)+momentEmbeddingVector f hf v (f i)
          simp only [momentEmbeddingVector_at]
          rfl
        · change momentEmbeddingVector f hf (u+v) k=momentEmbeddingVector f hf u k+momentEmbeddingVector f hf v k
          simp only [momentEmbeddingVector_off f hf _ k hk,add_zero]
      map_smul' z u := by
        ext k
        by_cases hk : k ∈ Set.range f
        · obtain ⟨i,rfl⟩ := hk
          change momentEmbeddingVector f hf (z •u) (f i)=z*momentEmbeddingVector f hf u (f i)
          simp only [momentEmbeddingVector_at]
          rfl
        · change momentEmbeddingVector f hf (z •u) k=z*momentEmbeddingVector f hf u k
          simp only [momentEmbeddingVector_off f hf _ k hk,mul_zero] } 1
    (fun u => by
      change ‖momentEmbeddingVector f hf u‖ ≤ 1*‖u‖
      rw [momentEmbeddingVector_norm,one_mul])

@[simp] theorem momentEmbedding_at {ι κ : Type*} (f : ι → κ) (hf : Function.Injective f)
    (u : MomentHilbert ι) (i : ι) : momentEmbedding f hf u (f i)=u i :=
  momentEmbeddingVector_at f hf u i

@[simp] theorem momentEmbedding_off {ι κ : Type*} (f : ι → κ) (hf : Function.Injective f)
    (u : MomentHilbert ι) (k : κ) (hk : k ∉ Set.range f) : momentEmbedding f hf u k=0 :=
  momentEmbeddingVector_off f hf u k hk

theorem momentEmbedding_norm {ι κ : Type*} (f : ι → κ) (hf : Function.Injective f)
    (u : MomentHilbert ι) : ‖momentEmbedding f hf u‖=‖u‖ := momentEmbeddingVector_norm f hf u

theorem momentEmbedding_norm_le_one {ι κ : Type*} (f : ι → κ) (hf : Function.Injective f) :
    ‖momentEmbedding f hf‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  rw [momentEmbedding_norm,one_mul]

@[simp] theorem momentPullback_embedding {ι κ : Type*} (f : ι → κ) (hf : Function.Injective f)
    (u : MomentHilbert ι) : momentPullback f hf (momentEmbedding f hf u)=u := by
  ext i
  exact momentEmbedding_at f hf u i

theorem momentEmbedding_pullback {ι κ : Type*} (f : ι → κ) (hf : Function.Injective f)
    (u : MomentHilbert κ) : momentEmbedding f hf (momentPullback f hf u)=momentProjection (Set.range f) u := by
  ext k
  by_cases hk : k ∈ Set.range f
  · obtain ⟨i,rfl⟩ := hk
    simp
  · simp [momentEmbedding_off f hf _ k hk,hk]

end
end MeyerGeneralProblem.Adaptive
