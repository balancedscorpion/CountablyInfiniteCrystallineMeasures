module

public import MeyerGeneralProblem.Cardinal.Adaptive.NativeDualOperators
public import MeyerGeneralProblem.Cardinal.Adaptive.OriginalMixedNorms

@[expose] public section

/-! # Original Hermite transposes of actual Schwartz operators -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section

def testPositiveExtension (p q : ℕ)
    (A : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ) :
    HermiteScale (q:ℤ) →L[ℂ] HermiteScale (p:ℤ) :=
  ((schwartzToHermiteScale p).comp A).toLinearMap.extendOfNorm
    (schwartzToHermiteScale q).toLinearMap

def testTransposeLinear (p q : ℕ)
    (A : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ) :
    HermiteScale (-(p:ℤ)) →ₗ[ℂ] HermiteScale (-(q:ℤ)) where
  toFun T := star ((testPositiveExtension p q A).adjoint (star T))
  map_add' T S := by simp
  map_smul' c T := by simp

/-- The bilinear native transpose of the actual Schwartz operator, obtained
by dense extension. Its distributional meaning follows from the bound below. -/
def nativeTestTranspose (p q : ℕ)
    (A : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ) :
    HermiteScale (-(p:ℤ)) →L[ℂ] HermiteScale (-(q:ℤ)) :=
  (testTransposeLinear p q A).mkContinuous ‖testPositiveExtension p q A‖ fun T => by
    change ‖star ((testPositiveExtension p q A).adjoint (star T))‖ ≤ _
    simpa only [norm_star, LinearIsometryEquiv.norm_map] using
      (testPositiveExtension p q A).adjoint.le_opNorm (star T)

/-- A proved bound on the actual Schwartz test operator identifies the whole
native transpose, on every Schwartz test. -/
theorem nativeTestTranspose_apply (p q : ℕ)
    (A : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ)
    (hb : ∃ B : ℝ, ∀ f : SchwartzMap ℝ ℂ,
      ‖schwartzToHermiteScale p (A f)‖ ≤ B*‖schwartzToHermiteScale q f‖)
    (T : HermiteScale (-(p:ℤ))) (f : SchwartzMap ℝ ℂ) :
    hermiteScaleDistribution q (nativeTestTranspose p q A T) f =
      hermiteScaleDistribution p T (A f) := by
  have hp (r : ℕ) (U : HermiteScale (-(r:ℤ))) (u : HermiteScale (r:ℤ)) :
      hermiteScalePairing (r:ℤ) U u = inner ℂ (star U) u := by
    rw [hermiteScalePairing, lp.inner_eq_tsum]
    apply tsum_congr
    intro n
    simp [RCLike.inner_apply, mul_comm]
  have hl : testPositiveExtension p q A (schwartzToHermiteScale q f) =
      schwartzToHermiteScale p (A f) :=
    LinearMap.extendOfNorm_eq (schwartzToHermiteScale_denseRange q) hb f
  rw [hermiteScaleDistribution_apply, hermiteScaleDistribution_apply, hp, hp]
  change inner ℂ (star (star ((testPositiveExtension p q A).adjoint (star T))))
    (schwartzToHermiteScale q f) = _
  rw [star_star, ContinuousLinearMap.adjoint_inner_left, hl]

/-- The same original norm bound controls the constructed bilinear transpose. -/
theorem nativeTestTranspose_norm_le (p q : ℕ)
    (A : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ f : SchwartzMap ℝ ℂ,
      ‖schwartzToHermiteScale p (A f)‖ ≤ B*‖schwartzToHermiteScale q f‖) :
    ‖nativeTestTranspose p q A‖ ≤ B := by
  have hl : ‖testPositiveExtension p q A‖ ≤ B :=
    LinearMap.opNorm_extendOfNorm_le (schwartzToHermiteScale_denseRange q) hB hb
  apply ContinuousLinearMap.opNorm_le_bound _ hB
  intro T
  change ‖star ((testPositiveExtension p q A).adjoint (star T))‖ ≤ _
  have h := (testPositiveExtension p q A).adjoint.le_opNorm (star T)
  simp only [norm_star, LinearIsometryEquiv.norm_map] at h ⊢
  exact h.trans (mul_le_mul_of_nonneg_right hl (norm_nonneg _))

/-- Actual multiplication of a Schwartz test by a coordinate monomial. -/
def monomialTestCLM (d : ℕ) : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
  coordinateMultiplicationCLM ^ d

/-- Pointwise interpretation of the actual monomial test operator. -/
theorem monomialTestCLM_apply (d : ℕ) (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    monomialTestCLM d f x = (x:ℂ)^d * f x := by
  induction d with
  | zero => simp [monomialTestCLM]
  | succ d ih =>
      rw [monomialTestCLM, pow_succ', mul_apply_eq_comp,
        coordinateMultiplicationCLM_apply]
      change (x:ℂ) * monomialTestCLM d f x = _
      rw [ih, pow_succ]
      ring

/-- Monomial multiplication consumes at most d original positive orders. -/
theorem exists_monomialTest_norm_bound (p d : ℕ) :
    ∃ B > 0, ∀ f : SchwartzMap ℝ ℂ,
      ‖schwartzToHermiteScale p (monomialTestCLM d f)‖ ≤
        B*‖schwartzToHermiteScale (p+d) f‖ := by
  obtain ⟨B,hB,hb⟩ := exists_mixedSchwartz_norm_bound d p d 0 (by omega)
  refine ⟨B,hB,fun f => ?_⟩
  have he : monomialTestCLM d f = mixedSchwartz d 0 f := by
    ext x
    simp [monomialTestCLM_apply, mixedSchwartz_apply]
  rw [he]
  exact hb f

/-- Monomial multiplication on the whole distribution, with the original
negative-order bound obtained from its actual test transpose. -/
def nativeMonomial (p d : ℕ) :
    HermiteScale (-(p:ℤ)) →L[ℂ] HermiteScale (-((p+d:ℕ):ℤ)) :=
  nativeTestTranspose p (p+d) (monomialTestCLM d)

/-- The native monomial has the genuine distributional action on every test. -/
theorem nativeMonomial_apply (p d : ℕ) (T : HermiteScale (-(p:ℤ)))
    (f : SchwartzMap ℝ ℂ) :
    hermiteScaleDistribution (p+d) (nativeMonomial p d T) f =
      hermiteScaleDistribution p T (monomialTestCLM d f) := by
  obtain ⟨B,_,hb⟩ := exists_monomialTest_norm_bound p d
  exact nativeTestTranspose_apply p (p+d) (monomialTestCLM d) ⟨B,hb⟩ T f

/-- A monomial's original native norm is controlled independently of its source. -/
theorem exists_nativeMonomial_norm_bound (p d : ℕ) :
    ∃ B > 0, ‖nativeMonomial p d‖ ≤ B := by
  obtain ⟨B,hB,hb⟩ := exists_monomialTest_norm_bound p d
  exact ⟨B,hB,nativeTestTranspose_norm_le p (p+d) (monomialTestCLM d) B hB.le hb⟩

/-- The canonical dense transpose of the identity between original orders. -/
def nativeOrderInclusion (p q : ℕ) :
    HermiteScale (-(p:ℤ)) →L[ℂ] HermiteScale (-(q:ℤ)) :=
  nativeTestTranspose p q (ContinuousLinearMap.id ℂ _)

/-- Increasing the negative order retains the entire original distribution. -/
theorem nativeOrderInclusion_realizes (p q : ℕ) (hpq : p ≤ q)
    (T : HermiteScale (-(p:ℤ))) :
    hermiteScaleDistribution q (nativeOrderInclusion p q T) = hermiteScaleDistribution p T := by
  have hb (f : SchwartzMap ℝ ℂ) : ‖schwartzToHermiteScale p f‖ ≤
      (1:ℝ)*‖schwartzToHermiteScale q f‖ := by
    rw [one_mul]
    have h := schwartzToHermiteScale_norm_mono_add p (q-p) f
    have he : p+(q-p)=q := by omega
    rw [he] at h
    exact h
  ext f
  exact nativeTestTranspose_apply p q (ContinuousLinearMap.id ℂ _) ⟨1,hb⟩ T f

/-- The genuine inclusion into a larger original negative order is contractive. -/
theorem nativeOrderInclusion_norm_le (p q : ℕ) (hpq : p ≤ q) :
    ‖nativeOrderInclusion p q‖ ≤ 1 := by
  apply nativeTestTranspose_norm_le p q _ 1 (by norm_num)
  intro f
  simp only [ContinuousLinearMap.id_apply, one_mul]
  have h := schwartzToHermiteScale_norm_mono_add p (q-p) f
  have he : p+(q-p)=q := by omega
  rw [he] at h
  exact h

end
end MeyerGeneralProblem.Adaptive
