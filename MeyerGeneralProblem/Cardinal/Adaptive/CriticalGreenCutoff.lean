module

public import MeyerGeneralProblem.Cardinal.Adaptive.CriticalGreenNormalization
public import MeyerGeneralProblem.Cardinal.Adaptive.OriginalMixedNorms
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import all Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Calculus.SmoothSeries
import all Mathlib.Analysis.Calculus.SmoothSeries

@[expose] public section

/-! # Fixed smooth half-line cutoffs for the whole critical Green inverse -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open Filter
open scoped Topology ContDiff

/-- A fixed smooth positive-half cutoff, with transition entirely in the
source's empty central interval. -/
def criticalPositiveCutoff (x : ℝ) : ℂ := Real.smoothTransition (2*x+1/2)

/-- The fixed complementary negative-half cutoff. -/
def criticalNegativeCutoff (x : ℝ) : ℂ := 1-criticalPositiveCutoff x

/-- The split is a partition of unity on every real point. -/
theorem criticalCutoff_partition (x : ℝ) :
    criticalPositiveCutoff x+criticalNegativeCutoff x=1 := by
  simp [criticalNegativeCutoff]

/-- Smoothness of the actual positive cutoff. -/
theorem criticalPositiveCutoff_contDiff : ContDiff ℝ ∞ criticalPositiveCutoff := by
  exact Complex.ofRealCLM.contDiff.comp (Real.smoothTransition.contDiff.comp
    ((contDiff_const.mul contDiff_id).add contDiff_const))

/-- Smoothness of its complementary cutoff. -/
theorem criticalNegativeCutoff_contDiff : ContDiff ℝ ∞ criticalNegativeCutoff :=
  contDiff_const.sub criticalPositiveCutoff_contDiff

/-- The positive cutoff vanishes on the full forbidden left half-line. -/
theorem criticalPositiveCutoff_eq_zero {x : ℝ} (hx : x ≤ -1/4) :
    criticalPositiveCutoff x=0 := by
  unfold criticalPositiveCutoff
  rw [Real.smoothTransition.zero_of_nonpos (by linarith)]
  norm_num

/-- The positive cutoff is one on the full right half-line. -/
theorem criticalPositiveCutoff_eq_one {x : ℝ} (hx : 1/4 ≤ x) :
    criticalPositiveCutoff x=1 := by
  unfold criticalPositiveCutoff
  rw [Real.smoothTransition.one_of_one_le (by linarith)]
  norm_num

/-- Every derivative of the positive cutoff vanishes strictly left of its
transition interval. This includes derivative order zero. -/
theorem iteratedDeriv_criticalPositiveCutoff_left (n : ℕ) {x : ℝ} (hx : x < -1/4) :
    iteratedDeriv n criticalPositiveCutoff x=0 := by
  have he : criticalPositiveCutoff =ᶠ[𝓝 x] (fun _ : ℝ => (0 : ℂ)) := by
    filter_upwards [eventually_lt_nhds hx] with y hy
    exact criticalPositiveCutoff_eq_zero hy.le
  rw [he.iteratedDeriv_eq n,iteratedDeriv_fun_const_zero]

/-- Positive-order derivatives vanish strictly right of the transition. -/
theorem iteratedDeriv_criticalPositiveCutoff_right (n : ℕ) (hn : n ≠ 0)
    {x : ℝ} (hx : 1/4 < x) : iteratedDeriv n criticalPositiveCutoff x=0 := by
  have he : criticalPositiveCutoff =ᶠ[𝓝 x] (fun _ : ℝ => (1 : ℂ)) := by
    filter_upwards [eventually_gt_nhds hx] with y hy
    exact criticalPositiveCutoff_eq_one hy.le
  rw [he.iteratedDeriv_eq n,iteratedDeriv_const]
  simp [hn]

/-- Every derivative of the fixed cutoff has a finite global bound; no
boundedness certificate is imposed on the Green operator. -/
theorem criticalPositiveCutoff_derivative_bounded (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, ‖iteratedDeriv n criticalPositiveCutoff x‖ ≤ C := by
  by_cases hn : n=0
  · subst n
    refine ⟨1,by norm_num,fun x => ?_⟩
    simpa [criticalPositiveCutoff,Real.norm_eq_abs,abs_of_nonneg (Real.smoothTransition.nonneg _)]
      using Real.smoothTransition.le_one (2*x+1/2)
  · have hc : Continuous (iteratedDeriv n criticalPositiveCutoff) :=
      ContDiff.continuous_iteratedDeriv n criticalPositiveCutoff_contDiff (by simp)
    obtain ⟨C,hC⟩ := (isCompact_Icc (a := (-1/4 : ℝ)) (b := (1/4 : ℝ))).exists_bound_of_continuousOn hc.continuousOn
    refine ⟨max C 0,le_max_right _ _,fun x => ?_⟩
    by_cases hl : x < -1/4
    · rw [iteratedDeriv_criticalPositiveCutoff_left n hl,norm_zero]
      exact le_max_right _ _
    by_cases hr : 1/4 < x
    · rw [iteratedDeriv_criticalPositiveCutoff_right n hn hr,norm_zero]
      exact le_max_right _ _
    exact (hC x ⟨by linarith,by linarith⟩).trans (le_max_left _ _)


/-- Chosen finite derivative bounds for the one fixed cutoff. -/
def criticalCutoffDerivativeBound (n : ℕ) : ℝ :=
  (criticalPositiveCutoff_derivative_bounded n).choose

/-- Nonnegativity of the constructed cutoff derivative bound. -/
theorem criticalCutoffDerivativeBound_nonneg (n : ℕ) :
    0 ≤ criticalCutoffDerivativeBound n :=
  (criticalPositiveCutoff_derivative_bounded n).choose_spec.1

/-- Uniform bound on each actual cutoff derivative. -/
theorem norm_iteratedDeriv_criticalPositiveCutoff_le (n : ℕ) (x : ℝ) :
    ‖iteratedDeriv n criticalPositiveCutoff x‖ ≤ criticalCutoffDerivativeBound n :=
  (criticalPositiveCutoff_derivative_bounded n).choose_spec.2 x

/-- The elementary half-line geometry gains two powers of the translation
index from two extra powers of spatial decay. -/
theorem criticalGreen_weighted_shift_bound (r m n : ℕ) (f : SchwartzMap ℝ ℂ)
    (x : ℝ) (hx : -1/4 ≤ x) :
    |x|^r * ‖iteratedDeriv m f (x+((n : ℝ)+1))‖ ≤
      (2 : ℝ)^(r+2) * SchwartzMap.seminorm ℂ (r+2) m f / ((n : ℝ)+1)^2 := by
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
  have hs : y^(r+2)*‖iteratedDeriv m f y‖ ≤ SchwartzMap.seminorm ℂ (r+2) m f := by
    simpa only [abs_of_pos hy] using SchwartzMap.le_seminorm' ℂ (r+2) m f y
  apply (le_div_iff₀ (by positivity : 0 < t^2)).mpr
  change (|x|^r*‖iteratedDeriv m f y‖)*t^2 ≤ _
  calc
    _ = (|x|^r*t^2)*‖iteratedDeriv m f y‖ := by ring
    _ ≤ ((2 : ℝ)^(r+2)*y^(r+2))*‖iteratedDeriv m f y‖ :=
      mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
    _ = (2 : ℝ)^(r+2)*(y^(r+2)*‖iteratedDeriv m f y‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hs (by positivity)

/-- One actual translated cutoff term, before summing the bounded Green weights. -/
def criticalPositiveTerm (n : ℕ) (f : SchwartzMap ℝ ℂ) (x : ℝ) : ℂ :=
  criticalPositiveCutoff x * f (x+((n : ℝ)+1))

/-- Each translated cutoff term is smooth on the entire line. -/
theorem criticalPositiveTerm_contDiff (n : ℕ) (f : SchwartzMap ℝ ℂ) :
    ContDiff ℝ ∞ (criticalPositiveTerm n f) :=
  criticalPositiveCutoff_contDiff.mul ((f.smooth ⊤).comp (contDiff_id.add contDiff_const))

/-- Exact Leibniz expansion for the actual cutoff terms. -/
theorem iteratedDeriv_criticalPositiveTerm (r n : ℕ) (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    iteratedDeriv r (criticalPositiveTerm n f) x =
      ∑ i ∈ Finset.range (r+1), (r.choose i : ℂ) *
        iteratedDeriv i criticalPositiveCutoff x *
        iteratedDeriv (r-i) f (x+((n : ℝ)+1)) := by
  change iteratedDeriv r (criticalPositiveCutoff * (fun y => f (y+((n : ℝ)+1)))) x = _
  rw [iteratedDeriv_mul]
  · simp only [iteratedDeriv_comp_add_const]
  · exact criticalPositiveCutoff_contDiff.contDiffAt.of_le (by simp)
  · exact ((f.smooth ⊤).comp (contDiff_id.add contDiff_const)).contDiffAt.of_le (by simp)


/-- Finite continuous seminorm controlling every translated cutoff term. -/
def criticalPositiveTermBound (r m : ℕ) (f : SchwartzMap ℝ ℂ) : ℝ :=
  (2 : ℝ)^(r+2)*∑ i ∈ Finset.range (m+1),
    (m.choose i : ℝ)*criticalCutoffDerivativeBound i*SchwartzMap.seminorm ℂ (r+2) (m-i) f

/-- The finite seminorm bound is nonnegative. -/
theorem criticalPositiveTermBound_nonneg (r m : ℕ) (f : SchwartzMap ℝ ℂ) :
    0 ≤ criticalPositiveTermBound r m f := by
  unfold criticalPositiveTermBound
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (criticalCutoffDerivativeBound_nonneg i))
    (apply_nonneg _ _)

/-- Summable decay in the translation index for EVERY weighted derivative of
the actual cutoff term. This supplies the analytic series convergence mechanism. -/
theorem criticalPositiveTerm_weighted_bound (r m n : ℕ) (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    |x|^r*‖iteratedDeriv m (criticalPositiveTerm n f) x‖ ≤
      criticalPositiveTermBound r m f / ((n : ℝ)+1)^2 := by
  rw [iteratedDeriv_criticalPositiveTerm]
  calc
    _ ≤ |x|^r*∑ i ∈ Finset.range (m+1),
        ‖(m.choose i : ℂ)*iteratedDeriv i criticalPositiveCutoff x*
          iteratedDeriv (m-i) f (x+((n : ℝ)+1))‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ = ∑ i ∈ Finset.range (m+1), |x|^r*
        ‖(m.choose i : ℂ)*iteratedDeriv i criticalPositiveCutoff x*
          iteratedDeriv (m-i) f (x+((n : ℝ)+1))‖ := Finset.mul_sum _ _ _
    _ ≤ ∑ i ∈ Finset.range (m+1),
        ((2 : ℝ)^(r+2)*((m.choose i : ℝ)*criticalCutoffDerivativeBound i*
          SchwartzMap.seminorm ℂ (r+2) (m-i) f)) / ((n : ℝ)+1)^2 := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hx : x < -1/4
      · rw [iteratedDeriv_criticalPositiveCutoff_left i hx,mul_zero,zero_mul,norm_zero,mul_zero]
        exact div_nonneg
          (mul_nonneg (by positivity) (mul_nonneg
            (mul_nonneg (Nat.cast_nonneg _) (criticalCutoffDerivativeBound_nonneg i))
            (apply_nonneg _ _))) (by positivity)
      · have hc := norm_iteratedDeriv_criticalPositiveCutoff_le i x
        have hf := criticalGreen_weighted_shift_bound r (m-i) n f x (by linarith)
        calc
          _ = ((m.choose i : ℝ)*‖iteratedDeriv i criticalPositiveCutoff x‖)*
              (|x|^r*‖iteratedDeriv (m-i) f (x+((n : ℝ)+1))‖) := by
                rw [norm_mul,norm_mul,RCLike.norm_natCast]; ring
          _ ≤ ((m.choose i : ℝ)*criticalCutoffDerivativeBound i)*
              ((2 : ℝ)^(r+2)*SchwartzMap.seminorm ℂ (r+2) (m-i) f / ((n : ℝ)+1)^2) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg _)) hf
              (by positivity) (mul_nonneg (Nat.cast_nonneg _) (criticalCutoffDerivativeBound_nonneg i))
          _ = _ := by ring
    _ = _ := by rw [← Finset.sum_div,← Finset.mul_sum]; rfl


/-- The fixed summable translation majorant. -/
def criticalGreenDecay (n : ℕ) : ℝ := ((n : ℝ)+1)⁻¹^2

/-- Summability of the actual majorant used for all weighted derivatives. -/
theorem summable_criticalGreenDecay : Summable criticalGreenDecay := by
  change Summable (fun n : ℕ => ((n : ℝ)+1)⁻¹^2)
  simpa only [criticalGreenDecay,Nat.cast_add,Nat.cast_one,one_div,inv_pow] using
    (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1<2))

/-- The whole positive cutoff series for a bounded coefficient sequence. -/
def positiveGreenTestFunction (w : ℕ → ℂ) (f : SchwartzMap ℝ ℂ) (x : ℝ) : ℂ :=
  ∑' n, w n * criticalPositiveTerm n f x

/-- Weighted derivative bound for an individual coefficient-weighted term. -/
theorem weighted_positiveGreenTerm_bound (w : ℕ → ℂ) {B : ℝ} (hB : 0 ≤ B)
    (hw : ∀ n, ‖w n‖ ≤ B) (r m n : ℕ) (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    |x|^r*‖iteratedFDeriv ℝ m (fun y => w n*criticalPositiveTerm n f y) x‖ ≤
      (B*criticalPositiveTermBound r m f)*criticalGreenDecay n := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,iteratedDeriv_const_mul_field,norm_mul]
  calc
    _ = ‖w n‖*(|x|^r*‖iteratedDeriv m (criticalPositiveTerm n f) x‖) := by ring
    _ ≤ B*(criticalPositiveTermBound r m f / ((n : ℝ)+1)^2) :=
      mul_le_mul (hw n) (criticalPositiveTerm_weighted_bound r m n f x) (by positivity) hB
    _ = _ := by simp only [criticalGreenDecay,div_eq_mul_inv,inv_pow]; ring

/-- The actual scalar cutoff series converges absolutely at every point. -/
theorem summable_positiveGreenTestFunction (w : ℕ → ℂ) {B : ℝ} (hB : 0 ≤ B)
    (hw : ∀ n, ‖w n‖ ≤ B) (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    Summable (fun n => w n*criticalPositiveTerm n f x) := by
  apply Summable.of_norm_bounded (summable_criticalGreenDecay.mul_left (B*criticalPositiveTermBound 0 0 f))
  intro n
  simpa only [pow_zero,one_mul,norm_iteratedFDeriv_zero] using
    weighted_positiveGreenTerm_bound w hB hw 0 0 n f x

/-- All derivative series converge uniformly, so the actual whole series is
smooth. The bound is proved from the cutoff geometry, not supplied as an input. -/
theorem positiveGreenTestFunction_contDiff (w : ℕ → ℂ) {B : ℝ} (hB : 0 ≤ B)
    (hw : ∀ n, ‖w n‖ ≤ B) (f : SchwartzMap ℝ ℂ) :
    ContDiff ℝ ∞ (positiveGreenTestFunction w f) := by
  apply contDiff_tsum
    (fun n => contDiff_const.mul (criticalPositiveTerm_contDiff n f))
    (v := fun m n => (B*criticalPositiveTermBound 0 m f)*criticalGreenDecay n)
  · intro m _
    exact summable_criticalGreenDecay.mul_left _
  · intro m n x _
    simpa only [pow_zero,one_mul] using weighted_positiveGreenTerm_bound w hB hw 0 m n f x

/-- The whole series inherits every weighted Schwartz derivative bound. -/
theorem positiveGreenTestFunction_weighted_bound (w : ℕ → ℂ) {B : ℝ} (hB : 0 ≤ B)
    (hw : ∀ n, ‖w n‖ ≤ B) (r m : ℕ) (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    |x|^r*‖iteratedFDeriv ℝ m (positiveGreenTestFunction w f) x‖ ≤
      (B*criticalPositiveTermBound r m f)*(∑' n, criticalGreenDecay n) := by
  have hd := iteratedFDeriv_tsum_apply
    (𝕜 := ℝ) (N := (⊤ : ℕ∞))
    (fun n => contDiff_const.mul (criticalPositiveTerm_contDiff n f))
    (v := fun m n => (B*criticalPositiveTermBound 0 m f)*criticalGreenDecay n)
    (fun m _ => summable_criticalGreenDecay.mul_left _)
    (fun m n x _ => by
      simpa only [pow_zero,one_mul] using weighted_positiveGreenTerm_bound w hB hw 0 m n f x)
    (k := m) (by simp) x
  change |x|^r*‖iteratedFDeriv ℝ m (fun y => ∑' n, w n*criticalPositiveTerm n f y) x‖ ≤ _
  rw [hd]
  have hn : Summable (fun n => ‖iteratedFDeriv ℝ m (fun y => w n*criticalPositiveTerm n f y) x‖) := by
    apply Summable.of_nonneg_of_le (fun n => norm_nonneg _)
      (fun n => ?_) (summable_criticalGreenDecay.mul_left (B*criticalPositiveTermBound 0 m f))
    simpa only [pow_zero,one_mul] using weighted_positiveGreenTerm_bound w hB hw 0 m n f x
  calc
    _ ≤ |x|^r*(∑' n, ‖iteratedFDeriv ℝ m (fun y => w n*criticalPositiveTerm n f y) x‖) :=
      mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hn) (by positivity)
    _ = ∑' n, |x|^r*‖iteratedFDeriv ℝ m (fun y => w n*criticalPositiveTerm n f y) x‖ :=
      tsum_mul_left.symm
    _ ≤ ∑' n, (B*criticalPositiveTermBound r m f)*criticalGreenDecay n :=
      (hn.mul_left _).tsum_le_tsum
        (fun n => weighted_positiveGreenTerm_bound w hB hw r m n f x)
        (summable_criticalGreenDecay.mul_left _)
    _ = _ := tsum_mul_left


/-- Fixed finite Leibniz constant for a target Schwartz seminorm. -/
def criticalPositiveTermConstant (r m : ℕ) : ℝ :=
  (2 : ℝ)^(r+2)*∑ i ∈ Finset.range (m+1), (m.choose i : ℝ)*criticalCutoffDerivativeBound i

/-- Nonnegativity of the fixed Leibniz constant. -/
theorem criticalPositiveTermConstant_nonneg (r m : ℕ) : 0 ≤ criticalPositiveTermConstant r m := by
  apply mul_nonneg (by positivity)
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (Nat.cast_nonneg _) (criticalCutoffDerivativeBound_nonneg i))

/-- The complete term bound uses one fixed finite family of input seminorms. -/
theorem criticalPositiveTermBound_le_sup (r m : ℕ) (f : SchwartzMap ℝ ℂ) :
    criticalPositiveTermBound r m f ≤ criticalPositiveTermConstant r m *
      (Finset.Iic (r+2,m)).sup (schwartzSeminormFamily ℂ ℝ ℂ) f := by
  unfold criticalPositiveTermBound criticalPositiveTermConstant
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  apply mul_le_mul_of_nonneg_left _
    (mul_nonneg (Nat.cast_nonneg _) (criticalCutoffDerivativeBound_nonneg i))
  have hs : SchwartzMap.seminorm ℂ (r+2) (m-i) ≤
      (Finset.Iic (r+2,m)).sup (schwartzSeminormFamily ℂ ℝ ℂ) :=
    Finset.le_sup (b := (r+2,m-i)) (f := schwartzSeminormFamily ℂ ℝ ℂ)
      (Finset.mem_Iic.mpr ⟨le_rfl,Nat.sub_le _ _⟩)
  exact hs f

/-- The positive whole Green transpose as an actual continuous linear map on
Schwartz space, built from the proved uniform series bounds. -/
def positiveGreenTestCLM (w : ℕ → ℂ) {B : ℝ} (hB : 0 ≤ B) (hw : ∀ n, ‖w n‖ ≤ B) :
    SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
  SchwartzMap.mkCLM (positiveGreenTestFunction w)
    (fun f g x => by
      have he (n : ℕ) : w n*criticalPositiveTerm n (f+g) x =
          w n*criticalPositiveTerm n f x+w n*criticalPositiveTerm n g x := by
        simp [criticalPositiveTerm,mul_add]
      simp only [positiveGreenTestFunction,he]
      exact (summable_positiveGreenTestFunction w hB hw f x).tsum_add
        (summable_positiveGreenTestFunction w hB hw g x))
    (fun a f x => by
      have he (n : ℕ) : w n*criticalPositiveTerm n (a • f) x = a*(w n*criticalPositiveTerm n f x) := by
        simp only [criticalPositiveTerm,smul_apply,smul_eq_mul]; ring
      simp only [positiveGreenTestFunction,he,smul_eq_mul,RingHom.id_apply]
      exact tsum_mul_left)
    (positiveGreenTestFunction_contDiff w hB hw)
    (by
      rintro ⟨r,m⟩
      refine ⟨Finset.Iic (r+2,m), B*criticalPositiveTermConstant r m*(∑' n, criticalGreenDecay n),
        mul_nonneg (mul_nonneg hB (criticalPositiveTermConstant_nonneg r m)) (tsum_nonneg (by intro n; exact sq_nonneg _)),?_⟩
      intro f x
      have h := positiveGreenTestFunction_weighted_bound w hB hw r m f x
      apply (show _ ≤ _ from h).trans
      have hh := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (criticalPositiveTermBound_le_sup r m f) hB)
        (show 0 ≤ ∑' n, criticalGreenDecay n from tsum_nonneg (by intro n; exact sq_nonneg _))
      simpa only [Real.norm_eq_abs,mul_assoc,mul_left_comm,mul_comm] using hh)

/-- Pointwise action of the actual positive Schwartz operator. -/
theorem positiveGreenTestCLM_apply (w : ℕ → ℂ) {B : ℝ} (hB : 0 ≤ B)
    (hw : ∀ n, ‖w n‖ ≤ B) (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    positiveGreenTestCLM w hB hw f x = ∑' n, w n*criticalPositiveTerm n f x := rfl


/-- Reflection exchanges the two fixed cutoffs exactly. -/
theorem criticalCutoff_reflection (x : ℝ) :
    criticalPositiveCutoff (-x)=criticalNegativeCutoff x := by
  have hr (u : ℝ) : Real.smoothTransition (1-u)=1-Real.smoothTransition u := by
    have hp := (Real.smoothTransition.pos_denom u).ne'
    simp only [Real.smoothTransition,sub_sub_cancel]
    rw [add_comm (expNegInvGlue (1-u))]
    field_simp
    ring
  have he : 2*(-x)+1/2=1-(2*x+1/2) := by ring
  simp only [criticalPositiveCutoff,criticalNegativeCutoff,he,hr,Complex.ofReal_sub,Complex.ofReal_one]

/-- A reflected actual positive operator gives the complete negative cutoff
series, with continuity inherited from Schwartz reflection. -/
def negativeGreenTestCLM (w : ℕ → ℂ) {B : ℝ} (hB : 0 ≤ B) (hw : ∀ n, ‖w n‖ ≤ B) :
    SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
  (combSchwartzDilation (-1) (by norm_num)).comp
    ((positiveGreenTestCLM w hB hw).comp (combSchwartzDilation (-1) (by norm_num)))

/-- Exact action of the entire negative cutoff series. -/
theorem negativeGreenTestCLM_apply (w : ℕ → ℂ) {B : ℝ} (hB : 0 ≤ B)
    (hw : ∀ n, ‖w n‖ ≤ B) (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    negativeGreenTestCLM w hB hw f x =
      ∑' n, w n*(criticalNegativeCutoff x*f (x-((n : ℝ)+1))) := by
  simp only [negativeGreenTestCLM,ContinuousLinearMap.comp_apply,combSchwartzDilation_apply,
    neg_one_mul,positiveGreenTestCLM_apply,criticalPositiveTerm,criticalCutoff_reflection]
  congr 1
  funext n
  congr 2
  congr 1
  ring

/-- The finite bound used for the actual source coefficients is derived from
the simple-root proof, rather than supplied as a certificate. -/
def actualGreenBound {k : ℕ} (positive : Bool) (α : Fin k → ℝ)
    (hα : Function.Injective α) (hi : ∀ i, 0 < α i ∧ α i < 1/2) : ℝ :=
  (criticalHeadGreen_bounded positive α hα hi).choose

/-- Derived nonnegative coefficient bound for the actual head. -/
theorem actualGreenBound_nonneg {k : ℕ} (positive : Bool) (α : Fin k → ℝ)
    (hα : Function.Injective α) (hi : ∀ i, 0 < α i ∧ α i < 1/2) :
    0 ≤ actualGreenBound positive α hα hi :=
  (criticalHeadGreen_bounded positive α hα hi).choose_spec.1

/-- Every actual Green coefficient satisfies its proved head-dependent bound. -/
theorem norm_criticalHeadGreen_le {k : ℕ} (positive : Bool) (α : Fin k → ℝ)
    (hα : Function.Injective α) (hi : ∀ i, 0 < α i ∧ α i < 1/2) (t : ℤ) :
    ‖criticalHeadGreen positive α t‖ ≤ actualGreenBound positive α hα hi :=
  (criticalHeadGreen_bounded positive α hα hi).choose_spec.2 t

/-- The actual whole Schwartz transpose for the critical finite difference
inverse, with both complete one-sided sums and the fixed smooth partition. -/
def criticalGreenTestCLM {k : ℕ} (α : Fin k → ℝ)
    (hα : Function.Injective α) (hi : ∀ i, 0 < α i ∧ α i < 1/2) :
    SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
  positiveGreenTestCLM (fun n => criticalHeadGreen true α ((n : ℤ)+1))
    (actualGreenBound_nonneg true α hα hi) (fun n => norm_criticalHeadGreen_le true α hα hi ((n : ℤ)+1)) +
  negativeGreenTestCLM (fun n => criticalHeadGreen false α (-((n : ℤ)+1)))
    (actualGreenBound_nonneg false α hα hi) (fun n => norm_criticalHeadGreen_le false α hα hi (-((n : ℤ)+1)))

/-- The exact whole-source transpose formula, before any atomic source
restriction or phasewise decomposition is considered. -/
theorem criticalGreenTestCLM_apply {k : ℕ} (α : Fin k → ℝ)
    (hα : Function.Injective α) (hi : ∀ i, 0 < α i ∧ α i < 1/2)
    (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    criticalGreenTestCLM α hα hi f x =
      (∑' n : ℕ, criticalHeadGreen true α ((n : ℤ)+1)*
        (criticalPositiveCutoff x*f (x+((n : ℝ)+1)))) +
      (∑' n : ℕ, criticalHeadGreen false α (-((n : ℤ)+1))*
        (criticalNegativeCutoff x*f (x-((n : ℝ)+1)))) := by
  simp only [criticalGreenTestCLM,_root_.add_apply,
    positiveGreenTestCLM_apply,negativeGreenTestCLM_apply,criticalPositiveTerm]

/-- The actual Green operator on all original tempered distributions, by
precomposition with the constructed continuous Schwartz transpose. -/
def criticalGreenDistributionCLM {k : ℕ} (α : Fin k → ℝ)
    (hα : Function.Injective α) (hi : ∀ i, 0 < α i ∧ α i < 1/2) :
    TemperedDistribution ℝ ℂ →L[ℂ] TemperedDistribution ℝ ℂ :=
  PointwiseConvergenceCLM.precomp ℂ (criticalGreenTestCLM α hα hi)

/-- Distributional action on every Schwartz test, with no source restriction. -/
theorem criticalGreenDistributionCLM_apply {k : ℕ} (α : Fin k → ℝ)
    (hα : Function.Injective α) (hi : ∀ i, 0 < α i ∧ α i < 1/2)
    (T : TemperedDistribution ℝ ℂ) (f : SchwartzMap ℝ ℂ) :
    criticalGreenDistributionCLM α hα hi T f = T (criticalGreenTestCLM α hα hi f) := rfl

end
end MeyerGeneralProblem.Adaptive
