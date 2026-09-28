module

public import MeyerGeneralProblem.Cardinal.Adaptive.CriticalGreenInverse
public import MeyerGeneralProblem.Cardinal.Adaptive.NativeMultipliers
public import MeyerGeneralProblem.Cardinal.Adaptive.NativeTranslations
public import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import all Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum

@[expose] public section

/-! # Original norm estimates for the actual whole Green inverse -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff FourierTransform

/-- Spatial decay comparison before integration, retaining the translated function. -/
theorem criticalGreen_weighted_shift_pointwise (r m n : ℕ) (f : SchwartzMap ℝ ℂ)
    (x : ℝ) (hx : -1/4 ≤ x) :
    |x|^r * ‖iteratedDeriv m f (x+((n : ℝ)+1))‖ ≤
      (2 : ℝ)^(r+2) * (|x+((n : ℝ)+1)|^(r+2) *
        ‖iteratedDeriv m f (x+((n : ℝ)+1))‖) / ((n : ℝ)+1)^2 := by
  let t : ℝ := (n : ℝ)+1
  let y : ℝ := x+t
  have ht : 1 ≤ t := by dsimp [t]; linarith [Nat.cast_nonneg (α := ℝ) n]
  have hy : 0 < y := by dsimp [y]; linarith
  have hx' : |x| ≤ 2*y := by
    apply abs_le.mpr
    dsimp [y]
    constructor <;> linarith
  have ht' : t ≤ 2*y := by dsimp [y]; linarith
  have hpow : |x|^r * t^2 ≤ (2 : ℝ)^(r+2)*y^(r+2) := by
    calc
      _ ≤ (2*y)^r*(2*y)^2 :=
        mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hx' r)
          (pow_le_pow_left₀ (by linarith) ht' 2) (by positivity) (by positivity)
      _ = _ := by rw [← pow_add,mul_pow]
  apply (le_div_iff₀ (by positivity : 0 < t^2)).mpr
  change (|x|^r*‖iteratedDeriv m f y‖)*t^2 ≤ _
  rw [abs_of_pos hy]
  calc
    _ = (|x|^r*t^2)*‖iteratedDeriv m f y‖ := by ring
    _ ≤ ((2 : ℝ)^(r+2)*y^(r+2))*‖iteratedDeriv m f y‖ :=
      mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
    _ = _ := by ring

/-- Each individual term of the actual Green sum is itself a Schwartz function. -/
def criticalPositiveTermSchwartz (n : ℕ) (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ where
  toFun := criticalPositiveTerm n f
  smooth' := criticalPositiveTerm_contDiff n f
  decay' r m := ⟨criticalPositiveTermBound r m f / ((n : ℝ)+1)^2,fun x => by
    simpa only [Real.norm_eq_abs,norm_iteratedFDeriv_eq_norm_iteratedDeriv] using
      criticalPositiveTerm_weighted_bound r m n f x⟩

/-- Coercion of an actual single cutoff term. -/
theorem criticalPositiveTermSchwartz_apply (n : ℕ) (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    criticalPositiveTermSchwartz n f x = criticalPositiveTerm n f x := rfl

/-- Translation preserves the actual L2 norm. -/
theorem green_translation_toLp_norm (a : ℝ) (f : SchwartzMap ℝ ℂ) :
    ‖(combSchwartzTranslation a f).toLp 2 volume‖ = ‖f.toLp 2 volume‖ := by
  simpa only [norm_schwartzToHermiteScale_zero] using
    schwartzToHermiteScale_zero_translation_norm a f

/-- The true cutoff derivative is dominated by translated mixed derivatives
of total order two higher, with a summable translation factor. -/
theorem criticalPositiveTerm_mixed_pointwise (r m n : ℕ) (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    ‖mixedSchwartz r m (criticalPositiveTermSchwartz n f) x‖ ≤
      ∑ i ∈ Finset.range (m+1),
        ((2 : ℝ)^(r+2)*(m.choose i : ℝ)*criticalCutoffDerivativeBound i / ((n : ℝ)+1)^2) *
          ‖combSchwartzTranslation ((n : ℝ)+1) (mixedSchwartz (r+2) (m-i) f) x‖ := by
  rw [mixedSchwartz_apply]
  change ‖(x : ℂ)^r * iteratedDeriv m (criticalPositiveTerm n f) x‖ ≤ _
  simp only [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs]
  rw [iteratedDeriv_criticalPositiveTerm]
  calc
    _ ≤ |x|^r*∑ i ∈ Finset.range (m+1),
        ‖(m.choose i : ℂ)*iteratedDeriv i criticalPositiveCutoff x*
          iteratedDeriv (m-i) f (x+((n : ℝ)+1))‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ = ∑ i ∈ Finset.range (m+1), |x|^r*
        ‖(m.choose i : ℂ)*iteratedDeriv i criticalPositiveCutoff x*
          iteratedDeriv (m-i) f (x+((n : ℝ)+1))‖ := Finset.mul_sum _ _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      rw [combSchwartzTranslation_apply]
      rw [add_comm ((n : ℝ)+1) x,mixedSchwartz_apply]
      conv_rhs => simp only [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs]
      by_cases hx : x < -1/4
      · rw [iteratedDeriv_criticalPositiveCutoff_left i hx,mul_zero,zero_mul,norm_zero,mul_zero]
        exact mul_nonneg (div_nonneg (mul_nonneg
          (mul_nonneg (by positivity) (Nat.cast_nonneg _))
          (criticalCutoffDerivativeBound_nonneg i)) (by positivity)) (by positivity)
      · have hc := norm_iteratedDeriv_criticalPositiveCutoff_le i x
        have hf := criticalGreen_weighted_shift_pointwise r (m-i) n f x (by linarith)
        calc
          _ = ((m.choose i : ℝ)*‖iteratedDeriv i criticalPositiveCutoff x‖)*
              (|x|^r*‖iteratedDeriv (m-i) f (x+((n : ℝ)+1))‖) := by
                rw [norm_mul,norm_mul,RCLike.norm_natCast]; ring
          _ ≤ ((m.choose i : ℝ)*criticalCutoffDerivativeBound i)*
              ((2 : ℝ)^(r+2)*(|x+((n : ℝ)+1)|^(r+2)*
                ‖iteratedDeriv (m-i) f (x+((n : ℝ)+1))‖) / ((n : ℝ)+1)^2) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg _)) hf
              (by positivity) (mul_nonneg (Nat.cast_nonneg _) (criticalCutoffDerivativeBound_nonneg i))
          _ = _ := by ring

/-- Integrated single-term estimate in the original mixed L2 quantities. -/
theorem criticalPositiveTerm_mixed_toLp_bound (r m n : ℕ) (f : SchwartzMap ℝ ℂ) :
    ‖(mixedSchwartz r m (criticalPositiveTermSchwartz n f)).toLp 2 volume‖ ≤
      ∑ i ∈ Finset.range (m+1),
        ((2 : ℝ)^(r+2)*(m.choose i : ℝ)*criticalCutoffDerivativeBound i / ((n : ℝ)+1)^2) *
          ‖(mixedSchwartz (r+2) (m-i) f).toLp 2 volume‖ := by
  have h := schwartz_norm_toLp_le_weighted_sum (Finset.range (m+1))
    (fun i => (2 : ℝ)^(r+2)*(m.choose i : ℝ)*criticalCutoffDerivativeBound i / ((n : ℝ)+1)^2)
    (fun i _ => div_nonneg (mul_nonneg (mul_nonneg (by positivity) (Nat.cast_nonneg _))
      (criticalCutoffDerivativeBound_nonneg i)) (by positivity))
    (mixedSchwartz r m (criticalPositiveTermSchwartz n f))
    (fun i => combSchwartzTranslation ((n : ℝ)+1) (mixedSchwartz (r+2) (m-i) f))
    (criticalPositiveTerm_mixed_pointwise r m n f)
  simpa only [green_translation_toLp_norm] using h

/-- Every derivative of the actual whole positive inverse equals its convergent
termwise derivative series. -/
theorem iteratedDeriv_positiveGreenTestCLM (w : ℕ → ℂ) {B : ℝ} (hB : 0 ≤ B)
    (hw : ∀ n, ‖w n‖ ≤ B) (f : SchwartzMap ℝ ℂ) (m : ℕ) (x : ℝ) :
    iteratedDeriv m (positiveGreenTestCLM w hB hw f : ℝ → ℂ) x =
      ∑' n, w n*iteratedDeriv m (criticalPositiveTerm n f) x := by
  have hd := iteratedFDeriv_tsum_apply
    (𝕜 := ℝ) (N := (⊤ : ℕ∞))
    (fun n => contDiff_const.mul (criticalPositiveTerm_contDiff n f))
    (v := fun m n => (B*criticalPositiveTermBound 0 m f)*criticalGreenDecay n)
    (fun m _ => summable_criticalGreenDecay.mul_left _)
    (fun m n x _ => by
      simpa only [pow_zero,one_mul] using weighted_positiveGreenTerm_bound w hB hw 0 m n f x)
    (k := m) (by simp) x
  change iteratedDeriv m (fun y => ∑' n, w n*criticalPositiveTerm n f y) x = _
  rw [iteratedDeriv_eq_equiv_comp,Function.comp_apply,hd]
  change (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin m) ℂ).symm.toContinuousLinearEquiv
    (∑' n, iteratedFDeriv ℝ m (fun y => w n*criticalPositiveTerm n f y) x) = _
  rw [(ContinuousMultilinearMap.piFieldEquiv ℝ (Fin m) ℂ).symm.toContinuousLinearEquiv.map_tsum]
  apply tsum_congr
  intro n
  change iteratedDeriv m (fun y => w n*criticalPositiveTerm n f y) x = _
  exact iteratedDeriv_const_mul_field _ _

/-- Original mixed L2 degree controls each of its individual mixed derivatives. -/
theorem green_mixed_norm_le_sum (n j k : ℕ) (h : j+k ≤ n) (f : SchwartzMap ℝ ℂ) :
    ‖(mixedSchwartz j k f).toLp 2 volume‖ ≤ mixedL2Sum n f := by
  unfold mixedL2Sum
  apply Finset.single_le_sum (a := (j,k))
    (f := fun z : ℕ × ℕ => ‖(mixedSchwartz z.1 z.2 f).toLp 2 volume‖)
  · intro z hz; exact norm_nonneg _
  · exact (mem_mixedIndices n j k).mpr h

/-- Summable term decay costs exactly two in mixed degree, hence one original
Hermite order. -/
theorem criticalPositiveTerm_mixed_decay (r m n : ℕ) (f : SchwartzMap ℝ ℂ) :
    ‖(mixedSchwartz r m (criticalPositiveTermSchwartz n f)).toLp 2 volume‖ ≤
      (criticalPositiveTermConstant r m*mixedL2Sum (r+m+2) f)*criticalGreenDecay n := by
  apply (criticalPositiveTerm_mixed_toLp_bound r m n f).trans
  calc
    _ ≤ ∑ i ∈ Finset.range (m+1),
        ((2 : ℝ)^(r+2)*(m.choose i : ℝ)*criticalCutoffDerivativeBound i / ((n : ℝ)+1)^2) *
          mixedL2Sum (r+m+2) f := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (green_mixed_norm_le_sum _ _ _ (by omega) f)
        (div_nonneg (mul_nonneg (mul_nonneg (by positivity) (Nat.cast_nonneg _))
          (criticalCutoffDerivativeBound_nonneg i)) (by positivity))
    _ = _ := by
      simp only [criticalPositiveTermConstant,criticalGreenDecay,div_eq_mul_inv,inv_pow,
        Finset.mul_sum,mul_assoc,mul_comm,mul_left_comm]

/-- Absolute convergence in actual L2 of every mixed derivative series. -/
theorem summable_norm_positiveGreen_mixed (w : ℕ → ℂ) {B : ℝ} (hB : 0 ≤ B)
    (hw : ∀ n, ‖w n‖ ≤ B) (r m : ℕ) (f : SchwartzMap ℝ ℂ) :
    Summable (fun n => ‖w n • (mixedSchwartz r m (criticalPositiveTermSchwartz n f)).toLp 2 volume‖) := by
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _)
    (fun n => ?_) (summable_criticalGreenDecay.mul_left
      (B*(criticalPositiveTermConstant r m*mixedL2Sum (r+m+2) f)))
  rw [norm_smul]
  exact (mul_le_mul (hw n) (criticalPositiveTerm_mixed_decay r m n f) (norm_nonneg _) hB).trans_eq (by ring)

/-- Identification of the genuine mixed derivative in L2 with its convergent
whole translation series; this is not an abstractly chosen L2 representative. -/
theorem positiveGreen_mixed_toLp_eq_tsum (w : ℕ → ℂ) {B : ℝ} (hB : 0 ≤ B)
    (hw : ∀ n, ‖w n‖ ≤ B) (r m : ℕ) (f : SchwartzMap ℝ ℂ) :
    (mixedSchwartz r m (positiveGreenTestCLM w hB hw f)).toLp 2 volume =
      ∑' n, w n • (mixedSchwartz r m (criticalPositiveTermSchwartz n f)).toLp 2 volume := by
  have ht := Lp.coeFn_tsum (tsum_enorm_ne_top_iff_summable_norm.mpr
    (summable_norm_positiveGreen_mixed w hB hw r m f))
  have ha : ∀ᵐ x ∂(volume : Measure ℝ), ∀ n : ℕ,
      (w n • (mixedSchwartz r m (criticalPositiveTermSchwartz n f)).toLp 2 volume) x =
        w n * mixedSchwartz r m (criticalPositiveTermSchwartz n f) x := by
    rw [ae_all_iff]
    intro n
    filter_upwards [Lp.coeFn_smul (w n) ((mixedSchwartz r m (criticalPositiveTermSchwartz n f)).toLp 2 volume),
      (mixedSchwartz r m (criticalPositiveTermSchwartz n f)).coeFn_toLp 2 volume] with x hs hx
    simp only [hs,hx,Pi.smul_apply,smul_eq_mul]
  apply Lp.ext
  filter_upwards [(mixedSchwartz r m (positiveGreenTestCLM w hB hw f)).coeFn_toLp 2 volume,ht,ha] with x hx htx hax
  rw [hx,htx]
  simp only [hax,mixedSchwartz_apply]
  rw [iteratedDeriv_positiveGreenTestCLM,← tsum_mul_left]
  apply tsum_congr
  intro n
  change (x : ℂ)^r*(w n*iteratedDeriv m (criticalPositiveTerm n f) x) =
    w n*((x : ℂ)^r*iteratedDeriv m (criticalPositiveTerm n f) x)
  ring

/-- The L2 norm of the genuine whole mixed derivative is controlled by the
summed single-term bound. -/
theorem positiveGreen_mixed_toLp_bound (w : ℕ → ℂ) {B : ℝ} (hB : 0 ≤ B)
    (hw : ∀ n, ‖w n‖ ≤ B) (r m : ℕ) (f : SchwartzMap ℝ ℂ) :
    ‖(mixedSchwartz r m (positiveGreenTestCLM w hB hw f)).toLp 2 volume‖ ≤
      (B*criticalPositiveTermConstant r m*(∑' n, criticalGreenDecay n))*mixedL2Sum (r+m+2) f := by
  rw [positiveGreen_mixed_toLp_eq_tsum]
  apply (norm_tsum_le_tsum_norm (summable_norm_positiveGreen_mixed w hB hw r m f)).trans
  calc
    _ ≤ ∑' n, B*(criticalPositiveTermConstant r m*mixedL2Sum (r+m+2) f)*criticalGreenDecay n := by
      apply Summable.tsum_le_tsum _ (summable_norm_positiveGreen_mixed w hB hw r m f)
        (summable_criticalGreenDecay.mul_left _)
      intro n
      rw [norm_smul]
      exact (mul_le_mul (hw n) (criticalPositiveTerm_mixed_decay r m n f) (norm_nonneg _) hB).trans_eq (by ring)
    _ = _ := by rw [tsum_mul_left]; ring

/-- Increasing the finite mixed degree preserves the original mixed L2 sum. -/
theorem green_mixedL2Sum_mono {a b : ℕ} (h : a ≤ b) (f : SchwartzMap ℝ ℂ) :
    mixedL2Sum a f ≤ mixedL2Sum b f := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro z hz
    exact (mem_mixedIndices b z.1 z.2).mpr (((mem_mixedIndices a z.1 z.2).mp hz).trans h)
  · intro z _ _; exact norm_nonneg _

/-- Complete positive Green sum has exactly one order of loss in the ORIGINAL
Hermite graph norms. Its coefficient sequence needs only a uniform bound. -/
theorem positiveGreen_original_norm_bound (w : ℕ → ℂ) {B : ℝ} (hB : 0 ≤ B)
    (hw : ∀ n, ‖w n‖ ≤ B) (p : ℕ) :
    ∃ C > 0, ∀ f : SchwartzMap ℝ ℂ,
      ‖schwartzToHermiteScale p (positiveGreenTestCLM w hB hw f)‖ ≤
        C*‖schwartzToHermiteScale (p+1) f‖ := by
  obtain ⟨A,hA,hAn⟩ := exists_hermite_norm_le_mixedL2Sum p
  obtain ⟨D,hD,hDn⟩ := exists_mixedL2Sum_le_hermite_norm (p+1)
  let K : ℝ := ∑ z ∈ mixedIndices (2*p),
    B*criticalPositiveTermConstant z.1 z.2*(∑' n, criticalGreenDecay n)
  have hK : 0 ≤ K := by
    apply Finset.sum_nonneg
    intro z _
    exact mul_nonneg (mul_nonneg hB (criticalPositiveTermConstant_nonneg _ _))
      (tsum_nonneg (fun n => sq_nonneg _))
  refine ⟨A*K*D+1,by positivity,fun f => ?_⟩
  have hm : mixedL2Sum (2*p) (positiveGreenTestCLM w hB hw f) ≤
      K*mixedL2Sum (2*(p+1)) f := by
    unfold mixedL2Sum
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro z hz
    have hz' := (mem_mixedIndices (2*p) z.1 z.2).mp hz
    exact (positiveGreen_mixed_toLp_bound w hB hw z.1 z.2 f).trans
      (mul_le_mul_of_nonneg_left (green_mixedL2Sum_mono (by omega) f)
        (mul_nonneg (mul_nonneg hB (criticalPositiveTermConstant_nonneg _ _))
          (tsum_nonneg (fun n => sq_nonneg _))))
  calc
    _ ≤ A*(K*mixedL2Sum (2*(p+1)) f) := (hAn _).trans (mul_le_mul_of_nonneg_left hm hA.le)
    _ ≤ A*(K*(D*‖schwartzToHermiteScale (p+1) f‖)) := by
      gcongr
      exact hDn f
    _ ≤ _ := by nlinarith [norm_nonneg (schwartzToHermiteScale (p+1) f)]

/-- Reflection is exactly isometric in every original Hermite order. -/
theorem green_reflection_original_norm (p : ℕ) (f : SchwartzMap ℝ ℂ) :
    ‖schwartzToHermiteScale p (combSchwartzDilation (-1) (by norm_num) f)‖ =
      ‖schwartzToHermiteScale p f‖ := by
  have he : combSchwartzDilation (-1) (by norm_num) f = 𝓕⁻ (𝓕⁻ f) := by
    rw [SchwartzMap.fourierInv_apply_eq (𝓕⁻ f),FourierTransform.fourier_fourierInv_eq]
    ext x
    simp only [combSchwartzDilation_apply,neg_one_mul]
    rfl
  rw [he,schwartzToHermiteScale_fourierInv_norm,schwartzToHermiteScale_fourierInv_norm]

/-- The reflected negative Green half has the same exact original order loss. -/
theorem negativeGreen_original_norm_bound (w : ℕ → ℂ) {B : ℝ} (hB : 0 ≤ B)
    (hw : ∀ n, ‖w n‖ ≤ B) (p : ℕ) :
    ∃ C > 0, ∀ f : SchwartzMap ℝ ℂ,
      ‖schwartzToHermiteScale p (negativeGreenTestCLM w hB hw f)‖ ≤
        C*‖schwartzToHermiteScale (p+1) f‖ := by
  obtain ⟨C,hC,h⟩ := positiveGreen_original_norm_bound w hB hw p
  refine ⟨C,hC,fun f => ?_⟩
  simpa only [negativeGreenTestCLM,ContinuousLinearMap.comp_apply,green_reflection_original_norm] using
    h (combSchwartzDilation (-1) (by norm_num) f)

/-- The actual normalized WHOLE Green inverse loses only one original Hermite
order, with a proved constant depending on its fixed finite head. -/
theorem criticalGreen_original_norm_bound {k : ℕ} (α : Fin k → ℝ)
    (hα : Function.Injective α) (hi : ∀ i, 0 < α i ∧ α i < 1/2) (p : ℕ) :
    ∃ C > 0, ∀ f : SchwartzMap ℝ ℂ,
      ‖schwartzToHermiteScale p (criticalGreenTestCLM α hα hi f)‖ ≤
        C*‖schwartzToHermiteScale (p+1) f‖ := by
  obtain ⟨A,hA,ha⟩ := positiveGreen_original_norm_bound
    (fun n => criticalHeadGreen true α ((n : ℤ)+1))
    (actualGreenBound_nonneg true α hα hi) (fun n => norm_criticalHeadGreen_le true α hα hi _) p
  obtain ⟨D,hD,hd⟩ := negativeGreen_original_norm_bound
    (fun n => criticalHeadGreen false α (-((n : ℤ)+1)))
    (actualGreenBound_nonneg false α hα hi) (fun n => norm_criticalHeadGreen_le false α hα hi _) p
  refine ⟨A+D,by positivity,fun f => ?_⟩
  simp only [criticalGreenTestCLM,_root_.add_apply,map_add]
  exact (norm_add_le _ _).trans ((add_le_add (ha f) (hd f)).trans_eq (by ring))

def criticalGreenPositiveLift {k : ℕ} (α : Fin k → ℝ)
    (hα : Function.Injective α) (hi : ∀ i, 0 < α i ∧ α i < 1/2) (p : ℕ) :
    HermiteScale ((p+1 : ℕ) : ℤ) →L[ℂ] HermiteScale (p : ℤ) :=
  ((schwartzToHermiteScale p).comp (criticalGreenTestCLM α hα hi)).toLinearMap.extendOfNorm
    (schwartzToHermiteScale (p+1)).toLinearMap

def criticalGreenTransposeLM {k : ℕ} (α : Fin k → ℝ)
    (hα : Function.Injective α) (hi : ∀ i, 0 < α i ∧ α i < 1/2) (p : ℕ) :
    HermiteScale (-(p : ℤ)) →ₗ[ℂ] HermiteScale (-((p+1 : ℕ) : ℤ)) where
  toFun T := star ((criticalGreenPositiveLift α hα hi p).adjoint (star T))
  map_add' T S := by simp
  map_smul' c T := by simp

/-- Constructed native Green inverse from original H_-p to H_-(p+1), obtained
by dense extension of the ACTUAL test operator and its bilinear transpose. -/
def criticalGreenNativeCLM {k : ℕ} (α : Fin k → ℝ)
    (hα : Function.Injective α) (hi : ∀ i, 0 < α i ∧ α i < 1/2) (p : ℕ) :
    HermiteScale (-(p : ℤ)) →L[ℂ] HermiteScale (-((p+1 : ℕ) : ℤ)) :=
  (criticalGreenTransposeLM α hα hi p).mkContinuous ‖criticalGreenPositiveLift α hα hi p‖ fun T => by
    change ‖star ((criticalGreenPositiveLift α hα hi p).adjoint (star T))‖ ≤ _
    simpa only [norm_star,LinearIsometryEquiv.norm_map] using
      (criticalGreenPositiveLift α hα hi p).adjoint.le_opNorm (star T)

/-- The native inverse realizes the same whole tempered distribution on every
Schwartz test. The required original bound is a proved theorem, not an input. -/
theorem criticalGreenNativeCLM_realizes {k : ℕ} (α : Fin k → ℝ)
    (hα : Function.Injective α) (hi : ∀ i, 0 < α i ∧ α i < 1/2) (p : ℕ)
    (T : HermiteScale (-(p : ℤ))) :
    hermiteScaleDistribution (p+1) (criticalGreenNativeCLM α hα hi p T) =
      criticalGreenDistributionCLM α hα hi (hermiteScaleDistribution p T) := by
  obtain ⟨C,hC,hbound⟩ := criticalGreen_original_norm_bound α hα hi p
  have hp (r : ℕ) (U : HermiteScale (-(r : ℤ))) (u : HermiteScale (r : ℤ)) :
      hermiteScalePairing (r : ℤ) U u = inner ℂ (star U) u := by
    rw [hermiteScalePairing,lp.inner_eq_tsum]
    apply tsum_congr
    intro n
    simp [RCLike.inner_apply,mul_comm]
  have hl (f : SchwartzMap ℝ ℂ) :
      criticalGreenPositiveLift α hα hi p (schwartzToHermiteScale (p+1) f) =
        schwartzToHermiteScale p (criticalGreenTestCLM α hα hi f) :=
    LinearMap.extendOfNorm_eq (schwartzToHermiteScale_denseRange (p+1)) ⟨C,hbound⟩ f
  ext f
  rw [criticalGreenDistributionCLM_apply,hermiteScaleDistribution_apply,
    hermiteScaleDistribution_apply,hp,hp]
  change inner ℂ (star (star ((criticalGreenPositiveLift α hα hi p).adjoint (star T))))
    (schwartzToHermiteScale (p+1) f) = _
  rw [star_star,ContinuousLinearMap.adjoint_inner_left,hl]

/-- Actual native right inversion preserves the input whole distribution and
costs exactly one original order. -/
theorem criticalGreenNativeCLM_rightInverse {k : ℕ} (hk : 1 ≤ k) (α : Fin k → ℝ)
    (hα : Function.Injective α) (hi : ∀ i, 0 < α i ∧ α i < 1/2) (p : ℕ)
    (T : HermiteScale (-(p : ℤ))) :
    criticalHeadDifferenceDistributionCLM α
      (hermiteScaleDistribution (p+1) (criticalGreenNativeCLM α hα hi p T)) =
        hermiteScaleDistribution p T := by
  rw [criticalGreenNativeCLM_realizes,criticalGreenDistribution_rightInverse hk]

/-- A finite original operator norm controls the constructed native inverse. -/
theorem criticalGreenNativeCLM_norm_bound {k : ℕ} (α : Fin k → ℝ)
    (hα : Function.Injective α) (hi : ∀ i, 0 < α i ∧ α i < 1/2) (p : ℕ) :
    ∃ C > 0, ‖criticalGreenNativeCLM α hα hi p‖ ≤ C := by
  obtain ⟨C,hC,hbound⟩ := criticalGreen_original_norm_bound α hα hi p
  refine ⟨C,hC,?_⟩
  have hl : ‖criticalGreenPositiveLift α hα hi p‖ ≤ C :=
    LinearMap.opNorm_extendOfNorm_le (schwartzToHermiteScale_denseRange (p+1)) hC.le hbound
  apply ContinuousLinearMap.opNorm_le_bound _ hC.le
  intro T
  change ‖star ((criticalGreenPositiveLift α hα hi p).adjoint (star T))‖ ≤ _
  have h := (criticalGreenPositiveLift α hα hi p).adjoint.le_opNorm (star T)
  simp only [norm_star,LinearIsometryEquiv.norm_map] at h ⊢
  exact h.trans (mul_le_mul_of_nonneg_right hl (norm_nonneg _))

end
end MeyerGeneralProblem.Adaptive
