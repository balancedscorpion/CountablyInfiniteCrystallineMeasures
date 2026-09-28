module

public import MeyerGeneralProblem.Cardinal.Adaptive.ZakPeriodization
public import Mathlib.Analysis.Fourier.AddCircle
import all Mathlib.Analysis.Fourier.AddCircle

@[expose] public section

/-! Sharp separated compact-chart Zak estimates in the original Hermite norms. -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open Filter Set MeasureTheory
open scoped Topology FourierTransform

/-- On each open unit cell, the actual whole Schwartz Zak transpose has
exactly one nonzero compact packet. This is an identity of the full series. -/
theorem zakSchwartzTranspose_on_cell (f g : SchwartzMap ℝ ℂ)
    (hf : ∀ y : ℝ, 1/2 ≤ |y| → f y=0) (n : ℤ) (x : ℝ)
    (hx : |x-(n:ℝ)| < 1/2) :
    zakSchwartzTranspose g f x=(𝓕 g) (n:ℝ)*f (x-(n:ℝ)) := by
  rw [zakSchwartzTranspose_apply]
  apply tsum_eq_single n
  intro m hmn
  have hnm : (n-m:ℤ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hmn)
  have hnat : 1 ≤ (n-m).natAbs := Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hnm)
  have hnorm : (1:ℝ) ≤ |(n:ℝ)-(m:ℝ)| := by
    have hi : (1:ℤ) ≤ ((n-m).natAbs:ℤ) := Int.ofNat_le.mpr hnat
    rw [Int.natCast_natAbs] at hi
    exact_mod_cast hi
  have htri := abs_sub_le (n:ℝ) x (m:ℝ)
  rw [abs_sub_comm (n:ℝ) x] at htri
  rw [hf _ (by linarith)]
  exact mul_zero _

/-- All derivatives of the actual Schwartz transpose agree locally with
that unique packet, without a formal Schwartz-series differentiation assumption. -/
theorem zakSchwartzTranspose_derivative_on_cell (f g : SchwartzMap ℝ ℂ)
    (hf : ∀ y : ℝ, 1/2 ≤ |y| → f y=0) (n : ℤ) (x : ℝ)
    (hx : |x-(n:ℝ)| < 1/2) (r : ℕ) :
    iteratedDeriv r (zakSchwartzTranspose g f : ℝ → ℂ) x =
      (𝓕 g) (n:ℝ)*iteratedDeriv r (f : ℝ → ℂ) (x-(n:ℝ)) := by
  have hc : Continuous (fun y : ℝ => |y-(n:ℝ)|) := by fun_prop
  have he : (zakSchwartzTranspose g f : ℝ → ℂ) =ᶠ[𝓝 x]
      (fun y => (𝓕 g) (n:ℝ)*f (y-(n:ℝ))) := by
    filter_upwards [(hc.tendsto x).eventually (eventually_lt_nhds hx)] with y hy
    exact zakSchwartzTranspose_on_cell f g hf n y hy
  rw [he.iteratedDeriv_eq r,iteratedDeriv_const_mul_field]
  congr 1
  exact congrFun (iteratedDeriv_comp_sub_const r (f : ℝ → ℂ) (n:ℝ)) x

/-- For a compact central-chart test, its literal integer Fourier samples
are exactly the unit-interval Fourier coefficients, with the original sign. -/
theorem compact_fourier_sample_eq_coefficient (g : SchwartzMap ℝ ℂ)
    (hg : ∀ y : ℝ, 1/2 ≤ |y| → g y=0) (n : ℤ) :
    (𝓕 g) (n:ℝ) = fourierCoeffOn (a := (-1:ℝ)/2) (b := (1:ℝ)/2)
      (by norm_num) (g : ℝ → ℂ) n := by
  rw [fourierCoeffOn_eq_integral]
  norm_num only [show (1:ℝ)/2-(-1:ℝ)/2=1 by norm_num,div_one,one_smul]
  simp only [SchwartzMap.fourier_coe,Real.fourier_real_eq_integral_exp_smul]
  rw [intervalIntegral.integral_of_le (by norm_num)]
  trans ∫ y in Ioc (-(1/2:ℝ)) (1/2:ℝ), Complex.exp ((-2*Real.pi*y*(n:ℝ):ℝ)*Complex.I) • g y
  · apply (setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_).symm
    have hy' : y ≤ -(1/2) ∨ 1/2 < y := by simpa only [mem_Ioc,not_and_or,not_lt,not_le] using hy
    have habs : 1/2 ≤ |y| := by rcases hy' with h | h; exact (neg_le_abs y).trans' (by linarith); exact h.le.trans (le_abs_self y)
    rw [hg y habs,smul_zero]
  · apply setIntegral_congr_fun measurableSet_Ioc
    intro x hx
    dsimp only
    simp only [fourier_coe_apply]
    norm_num only [show (1:ℝ)/2-(-(1:ℝ)/2)=1 by norm_num]
    congr 2
    push_cast
    ring

/-- Parseval for the actual whole integer Fourier samples of a compact chart
Schwartz test. There is no loss of derivative order in this sampling identity. -/
theorem compact_fourier_samples_parseval (g : SchwartzMap ℝ ℂ)
    (hg : ∀ y : ℝ, 1/2 ≤ |y| → g y=0) :
    HasSum (fun n : ℤ => ‖(𝓕 g) (n:ℝ)‖^2) (‖g.toLp 2 volume‖^2) := by
  have h := hasSum_sq_fourierCoeffOn (a := (-1:ℝ)/2) (b := (1:ℝ)/2)
    (f := (g : ℝ → ℂ)) (by norm_num) ((g.memLp 2).restrict _)
  have he : (∫ x in (-1:ℝ)/2..(1:ℝ)/2, ‖g x‖^2) = ‖g.toLp 2 volume‖^2 := by
    have hi : (∫ x : ℝ, ‖g x‖^2) = ‖g.toLp 2 volume‖^2 :=
      integral_norm_sq_eq_toLp_norm_sq_complex (g.memLp 2)
    rw [intervalIntegral.integral_of_le (by norm_num),← hi]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    have hy' : y ≤ -1/2 ∨ 1/2 < y := by simpa only [mem_Ioc,not_and_or,not_lt,not_le] using hy
    have habs : 1/2 ≤ |y| := by rcases hy' with h | h; exact (neg_le_abs y).trans' (by linarith); exact h.le.trans (le_abs_self y)
    rw [hg y habs,norm_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0)]
  simp only [show (1:ℝ)/2-(-1:ℝ)/2=1 by norm_num,inv_one,one_smul,he] at h
  simpa only [compact_fourier_sample_eq_coefficient g hg] using h

/-- A compact chart margin is retained by all actual Schwartz derivatives. -/
theorem compactChart_mixedDerivative_zero (g : SchwartzMap ℝ ℂ) (r : ℝ)
    (hr : r < 1/2) (hg : ∀ y : ℝ, r ≤ |y| → g y=0) (k : ℕ) (x : ℝ)
    (hx : 1/2 ≤ |x|) : mixedSchwartz 0 k g x=0 := by
  have he : (g : ℝ → ℂ) =ᶠ[𝓝 x] (fun _ => 0) := by
    filter_upwards [(continuous_abs.tendsto x).eventually (eventually_gt_nhds (hr.trans_le hx))] with y hy
    exact hg y hy.le
  rw [mixedSchwartz_apply,pow_zero,one_mul,he.iteratedDeriv_eq k]
  simp only [iteratedDeriv_const,ite_self]

/-- The Fourier transform of each actual iterated Schwartz derivative has
its exact original 2π normalization and integer moment multiplier. -/
theorem fourier_mixedDerivative (g : SchwartzMap ℝ ℂ) (k : ℕ) (x : ℝ) :
    (𝓕 (mixedSchwartz 0 k g)) x =
      (2*(Real.pi:ℂ)*Complex.I*(x:ℂ))^k*(𝓕 g) x := by
  induction k with
  | zero => simp [mixedSchwartz]
  | succ k ih =>
    have he : mixedSchwartz 0 (k+1) g = SchwartzMap.derivCLM ℂ ℂ (mixedSchwartz 0 k g) := by
      simp only [mixedSchwartz,Function.iterate_zero_apply,Function.iterate_succ_apply']
    rw [he,fourier_derivCLM]
    simp only [_root_.smul_apply,smul_eq_mul,coordinateMultiplicationCLM_apply,ih,pow_succ]
    ring

/-- Parseval applied to actual derivatives pays weighted integer samples
at exactly their derivative order, including the zero frequency. -/
theorem compact_fourier_weighted_samples_parseval (g : SchwartzMap ℝ ℂ) (r : ℝ)
    (hr : r < 1/2) (hg : ∀ y : ℝ, r ≤ |y| → g y=0) (k : ℕ) :
    HasSum (fun n : ℤ => (2*Real.pi)^(2*k)*|(n:ℝ)|^(2*k)*‖(𝓕 g) (n:ℝ)‖^2)
      (‖(mixedSchwartz 0 k g).toLp 2 volume‖^2) := by
  have h := compact_fourier_samples_parseval (mixedSchwartz 0 k g)
    (compactChart_mixedDerivative_zero g r hr hg k)
  convert h using 1
  ext n
  rw [fourier_mixedDerivative]
  simp only [norm_mul,norm_pow,Complex.norm_I,Complex.norm_real,Real.norm_eq_abs,
    Complex.norm_ofNat,abs_of_pos Real.pi_pos,mul_pow,← pow_mul]
  ring

private theorem compactChart_integral_norm_sq (f : SchwartzMap ℝ ℂ)
    (hf : ∀ y : ℝ, 1/2 ≤ |y| → f y=0) :
    (∫ x in (-1:ℝ)/2..(1:ℝ)/2, ‖f x‖^2) = ‖f.toLp 2 volume‖^2 := by
  have hi : (∫ x : ℝ, ‖f x‖^2) = ‖f.toLp 2 volume‖^2 :=
    integral_norm_sq_eq_toLp_norm_sq_complex (f.memLp 2)
  rw [intervalIntegral.integral_of_le (by norm_num),← hi]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro y hy
  have hy' : y ≤ -1/2 ∨ 1/2 < y := by simpa only [mem_Ioc,not_and_or,not_lt,not_le] using hy
  have habs : 1/2 ≤ |y| := by rcases hy' with h | h; exact (neg_le_abs y).trans' (by linarith); exact h.le.trans (le_abs_self y)
  rw [hf y habs,norm_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0)]

/-- The exact L2 mass on one physical cell of the actual Zak transpose. -/
theorem zakSchwartzTranspose_cell_mass (f g : SchwartzMap ℝ ℂ)
    (hf : ∀ y : ℝ, 1/2 ≤ |y| → f y=0) (n : ℤ) :
    (∫ x in (-1:ℝ)/2+(n:ℝ)..(-1:ℝ)/2+(n:ℝ)+1, ‖zakSchwartzTranspose g f x‖^2) =
      ‖(𝓕 g) (n:ℝ)‖^2*‖f.toLp 2 volume‖^2 := by
  have he : (∫ x in (-1:ℝ)/2+(n:ℝ)..(-1:ℝ)/2+(n:ℝ)+1, ‖zakSchwartzTranspose g f x‖^2) =
      ∫ x in (-1:ℝ)/2+(n:ℝ)..(-1:ℝ)/2+(n:ℝ)+1, ‖(𝓕 g) (n:ℝ)‖^2*‖f (x-(n:ℝ))‖^2 := by
    apply intervalIntegral.integral_congr_Ioo_of_le (by linarith)
    intro x hx
    dsimp only
    rw [zakSchwartzTranspose_on_cell f g hf n x (by rw [abs_lt]; constructor <;> linarith [hx.1,hx.2]),
      norm_mul,mul_pow]
  rw [he,intervalIntegral.integral_const_mul,intervalIntegral.integral_comp_sub_right (fun y : ℝ => ‖f y‖^2) (n:ℝ)]
  have h1 : (-1:ℝ)/2+(n:ℝ)-(n:ℝ)=(-1:ℝ)/2 := by ring
  have h2 : (-1:ℝ)/2+(n:ℝ)+1-(n:ℝ)=(1:ℝ)/2 := by ring
  rw [h1,h2,compactChart_integral_norm_sq f hf]

/-- The compact separated Zak transpose preserves the product L2 norm.
Both complete cell and Fourier sums are evaluated by genuine Parseval. -/
theorem zakSchwartzTranspose_L2_norm (f g : SchwartzMap ℝ ℂ)
    (hf : ∀ y : ℝ, 1/2 ≤ |y| → f y=0)
    (hg : ∀ y : ℝ, 1/2 ≤ |y| → g y=0) :
    ‖(zakSchwartzTranspose g f).toLp 2 volume‖ = ‖f.toLp 2 volume‖*‖g.toLp 2 volume‖ := by
  have hint : Integrable (fun x : ℝ => ‖zakSchwartzTranspose g f x‖^2) :=
    ((zakSchwartzTranspose g f).memLp 2).integrable_norm_pow (by norm_num)
  have h1 := hint.hasSum_intervalIntegral ((-1:ℝ)/2)
  have hnorm : (∫ x : ℝ, ‖zakSchwartzTranspose g f x‖^2) =
      ‖(zakSchwartzTranspose g f).toLp 2 volume‖^2 :=
    integral_norm_sq_eq_toLp_norm_sq_complex ((zakSchwartzTranspose g f).memLp 2)
  simp only [zakSchwartzTranspose_cell_mass f g hf,hnorm] at h1
  have h2 := (compact_fourier_samples_parseval g hg).mul_right (‖f.toLp 2 volume‖^2)
  have he := h1.unique h2
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow,he,mul_comm]

/-- Differentiation commutes with the actual Zak transpose in its physical
test variable. This is an identity of genuine Schwartz functions. -/
theorem zakSchwartzTranspose_derivative (f g : SchwartzMap ℝ ℂ) :
    SchwartzMap.derivCLM ℂ ℂ (zakSchwartzTranspose g f) =
      zakSchwartzTranspose g (SchwartzMap.derivCLM ℂ ℂ f) := by
  suffices he : 𝓕 (SchwartzMap.derivCLM ℂ ℂ (zakSchwartzTranspose g f)) =
      𝓕 (zakSchwartzTranspose g (SchwartzMap.derivCLM ℂ ℂ f)) by
    have hh := congrArg (fun u : SchwartzMap ℝ ℂ => 𝓕⁻ u) he
    simpa only [FourierTransform.fourierInv_fourier_eq] using hh
  rw [fourier_derivCLM]
  simp only [zakSchwartzTranspose,ContinuousLinearMap.comp_apply,
    FourierTransform.fourierCLM_apply,FourierTransform.fourierInvCLM_apply,
    FourierTransform.fourier_fourierInv_eq,fourier_derivCLM]
  ext x
  simp only [_root_.smul_apply,smul_eq_mul,coordinateMultiplicationCLM_apply,
    SchwartzMap.smulLeftCLM_apply_apply (zakReflectedPeriodization_temperate g)]
  ring

private theorem summable_zak_packets (f g : SchwartzMap ℝ ℂ) (x : ℝ) :
    Summable (fun n : ℤ => (𝓕 g) (n:ℝ)*f (x-(n:ℝ))) := by
  simpa only [pointMass_apply,combSchwartzTranslation_apply,sub_eq_add_neg,add_comm] using
    summable_zakTensorAction (pointMass x) f g

/-- Position multiplication of the actual Zak test is the exact sum of
physical position and frequency differentiation, with the original constant. -/
theorem zakSchwartzTranspose_position (f g : SchwartzMap ℝ ℂ) :
    coordinateMultiplicationCLM (zakSchwartzTranspose g f) =
      zakSchwartzTranspose g (coordinateMultiplicationCLM f) +
        (2*(Real.pi:ℂ)*Complex.I)⁻¹ • zakSchwartzTranspose (SchwartzMap.derivCLM ℂ ℂ g) f := by
  ext x
  simp only [coordinateMultiplicationCLM_apply,_root_.add_apply,_root_.smul_apply,smul_eq_mul,
    zakSchwartzTranspose_apply]
  have hs := summable_zak_packets (coordinateMultiplicationCLM f) g x
  simp only [coordinateMultiplicationCLM_apply] at hs
  rw [← tsum_mul_left,← tsum_mul_left,
    ← hs.tsum_add
      ((summable_zak_packets f (SchwartzMap.derivCLM ℂ ℂ g) x).mul_left ((2*(Real.pi:ℂ)*Complex.I)⁻¹))]
  apply tsum_congr
  intro n
  rw [fourier_derivCLM]
  simp only [_root_.smul_apply,smul_eq_mul,coordinateMultiplicationCLM_apply]
  push_cast
  have hp : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  ring

/-- The finite unweighted derivative L2 sum on an actual Schwartz chart test. -/
def compactDerivativeL2Sum (m : ℕ) (f : SchwartzMap ℝ ℂ) : ℝ :=
  ∑ r ∈ Finset.range (m+1), ‖(mixedSchwartz 0 r f).toLp 2 volume‖

private theorem compactDerivativeL2Sum_nonneg (m : ℕ) (f : SchwartzMap ℝ ℂ) :
    0 ≤ compactDerivativeL2Sum m f := Finset.sum_nonneg (fun _ _ => norm_nonneg _)

private theorem mixedDerivative_deriv (k : ℕ) (f : SchwartzMap ℝ ℂ) :
    mixedSchwartz 0 k (SchwartzMap.derivCLM ℂ ℂ f)=mixedSchwartz 0 (k+1) f := by
  simp only [mixedSchwartz,Function.iterate_zero_apply,Function.iterate_succ_apply]

private theorem compactDerivativeL2Sum_mono (a b : ℕ) (hab : a ≤ b) (f : SchwartzMap ℝ ℂ) :
    compactDerivativeL2Sum a f ≤ compactDerivativeL2Sum b f :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) (fun _ _ _ => norm_nonneg _)

private theorem compactDerivativeL2Sum_deriv_le (a : ℕ) (f : SchwartzMap ℝ ℂ) :
    compactDerivativeL2Sum a (SchwartzMap.derivCLM ℂ ℂ f) ≤ compactDerivativeL2Sum (a+1) f := by
  unfold compactDerivativeL2Sum
  simp_rw [mixedDerivative_deriv]
  conv_rhs => rw [Finset.sum_range_succ']
  exact le_add_of_nonneg_right (norm_nonneg _)

private theorem compact_position_L2_le (f : SchwartzMap ℝ ℂ)
    (hf : ∀ y : ℝ, 1/2 ≤ |y| → f y=0) :
    ‖(coordinateMultiplicationCLM f).toLp 2 volume‖ ≤ ‖f.toLp 2 volume‖ := by
  have h := schwartz_norm_toLp_le_weighted_sum (Finset.univ : Finset Unit)
    (fun _ => (1:ℝ)) (by simp) (coordinateMultiplicationCLM f) (fun _ => f) (by
      intro x
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_unit,nsmul_eq_mul,Nat.cast_one,one_mul,
        coordinateMultiplicationCLM_apply,norm_mul,Complex.norm_real,Real.norm_eq_abs]
      by_cases hx : 1/2 ≤ |x|
      · rw [hf x hx,norm_zero,mul_zero]
      · have hh : |x| ≤ 1 := by linarith
        exact (mul_le_mul_of_nonneg_right hh (norm_nonneg _)).trans_eq (one_mul _))
  simpa using h

private theorem zak_position_mixed_step (a : ℕ) (f g : SchwartzMap ℝ ℂ) :
    ‖(mixedSchwartz (a+1) 0 (zakSchwartzTranspose g f)).toLp 2 volume‖ ≤
      ‖(mixedSchwartz a 0 (zakSchwartzTranspose g (coordinateMultiplicationCLM f))).toLp 2 volume‖ +
      ‖(2*(Real.pi:ℂ)*Complex.I)⁻¹‖*
        ‖(mixedSchwartz a 0 (zakSchwartzTranspose (SchwartzMap.derivCLM ℂ ℂ g) f)).toLp 2 volume‖ := by
  let α : ℂ := (2*(Real.pi:ℂ)*Complex.I)⁻¹
  let u := mixedSchwartz a 0 (zakSchwartzTranspose g (coordinateMultiplicationCLM f))
  let v := mixedSchwartz a 0 (zakSchwartzTranspose (SchwartzMap.derivCLM ℂ ℂ g) f)
  have he (x : ℝ) : mixedSchwartz (a+1) 0 (zakSchwartzTranspose g f) x = u x+α*v x := by
    have hh := congrArg (fun h : SchwartzMap ℝ ℂ => h x) (zakSchwartzTranspose_position f g)
    simp only [coordinateMultiplicationCLM_apply,_root_.add_apply,_root_.smul_apply,smul_eq_mul] at hh
    dsimp [u,v,α]
    simp only [mixedSchwartz_apply,iteratedDeriv_zero,pow_succ]
    rw [mul_assoc,hh]
    ring
  have h := schwartz_norm_toLp_le_weighted_sum (Finset.univ : Finset (Fin 2))
    ![1,‖α‖] (by intro j hj; fin_cases j <;> simp) (mixedSchwartz (a+1) 0 (zakSchwartzTranspose g f))
    ![u,v] (by
      intro x
      simp only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,one_mul,he]
      simpa only [norm_mul] using norm_add_le (u x) (α*v x))
  simpa only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,one_mul] using h

/-- Every position moment of a compact separated Zak test is bounded by
exactly that many derivatives of the frequency chart test. -/
theorem zakSchwartzTranspose_position_L2_bound (a : ℕ) (f g : SchwartzMap ℝ ℂ)
    (hf : ∀ y : ℝ, 1/2 ≤ |y| → f y=0)
    (hg : ∀ k : ℕ, ∀ y : ℝ, 1/2 ≤ |y| → mixedSchwartz 0 k g y=0) :
    ‖(mixedSchwartz a 0 (zakSchwartzTranspose g f)).toLp 2 volume‖ ≤
      (1+‖(2*(Real.pi:ℂ)*Complex.I)⁻¹‖)^a * ‖f.toLp 2 volume‖*compactDerivativeL2Sum a g := by
  induction a generalizing f g with
  | zero =>
    have hg0 : ∀ y : ℝ, 1/2 ≤ |y| → g y=0 := by simpa [mixedSchwartz] using hg 0
    simp only [mixedSchwartz,Function.iterate_zero_apply,pow_zero,one_mul]
    rw [zakSchwartzTranspose_L2_norm f g hf hg0]
    simp [compactDerivativeL2Sum,mixedSchwartz]
  | succ a ih =>
    have hxf : ∀ y : ℝ, 1/2 ≤ |y| → coordinateMultiplicationCLM f y=0 := by
      intro y hy; rw [coordinateMultiplicationCLM_apply,hf y hy,mul_zero]
    have hdg : ∀ k : ℕ, ∀ y : ℝ, 1/2 ≤ |y| → mixedSchwartz 0 k (SchwartzMap.derivCLM ℂ ℂ g) y=0 := by
      intro k y hy; rw [mixedDerivative_deriv]; exact hg (k+1) y hy
    have h1 := ih (coordinateMultiplicationCLM f) g hxf hg
    have h2 := ih f (SchwartzMap.derivCLM ℂ ℂ g) hf hdg
    have h1' := h1.trans (mul_le_mul
      (mul_le_mul_of_nonneg_left (compact_position_L2_le f hf) (by positivity))
      (compactDerivativeL2Sum_mono a (a+1) (by omega) g)
      (compactDerivativeL2Sum_nonneg _ _) (by positivity))
    have h2' := h2.trans (mul_le_mul_of_nonneg_left (compactDerivativeL2Sum_deriv_le a g) (by positivity))
    apply (zak_position_mixed_step a f g).trans
    apply (add_le_add h1' (mul_le_mul_of_nonneg_left h2' (norm_nonneg _))).trans_eq
    rw [pow_succ]
    ring

/-- The iterated derivative identity for the genuine Schwartz transpose. -/
theorem zakSchwartzTranspose_mixedDerivative (k : ℕ) (f g : SchwartzMap ℝ ℂ) :
    mixedSchwartz 0 k (zakSchwartzTranspose g f)=zakSchwartzTranspose g (mixedSchwartz 0 k f) := by
  induction k with
  | zero => simp [mixedSchwartz]
  | succ k ih =>
    have hd (u : SchwartzMap ℝ ℂ) : mixedSchwartz 0 (k+1) u =
        SchwartzMap.derivCLM ℂ ℂ (mixedSchwartz 0 k u) := by
      simp only [mixedSchwartz,Function.iterate_zero_apply,Function.iterate_succ_apply']
    rw [hd,ih,zakSchwartzTranspose_derivative,hd]

/-- A compact separated chart test maps into the original positive Hermite
order p using at most 2p derivatives in each variable. No extra two derivatives
are paid by an absolute sum over physical cells. -/
theorem exists_zakSchwartzTranspose_native_bound (p : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f g : SchwartzMap ℝ ℂ) (r : ℝ), r < 1/2 →
      (∀ y : ℝ, r ≤ |y| → f y=0) → (∀ y : ℝ, r ≤ |y| → g y=0) →
      ‖schwartzToHermiteScale p (zakSchwartzTranspose g f)‖ ≤
        C*compactDerivativeL2Sum (2*p) f*compactDerivativeL2Sum (2*p) g := by
  obtain ⟨D,hD,hreverse⟩ := exists_hermite_norm_le_mixedL2Sum p
  let θ : ℝ := 1+‖(2*(Real.pi:ℂ)*Complex.I)⁻¹‖
  have hθ : 1 ≤ θ := le_add_of_nonneg_right (norm_nonneg _)
  let K : ℝ := (mixedIndices (2*p)).card*θ^(2*p)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨D*K+1,by positivity,fun f g r hr hf hg => ?_⟩
  have hsingle (a b : ℕ) (hab : a+b ≤ 2*p) :
      ‖(mixedSchwartz a b (zakSchwartzTranspose g f)).toLp 2 volume‖ ≤
        θ^(2*p)*compactDerivativeL2Sum (2*p) f*compactDerivativeL2Sum (2*p) g := by
    have he : mixedSchwartz a b (zakSchwartzTranspose g f) =
        mixedSchwartz a 0 (zakSchwartzTranspose g (mixedSchwartz 0 b f)) := by
      rw [← zakSchwartzTranspose_mixedDerivative]
      simp only [mixedSchwartz,Function.iterate_zero_apply]
    rw [he]
    have h := zakSchwartzTranspose_position_L2_bound a (mixedSchwartz 0 b f) g
      (compactChart_mixedDerivative_zero f r hr hf b)
      (compactChart_mixedDerivative_zero g r hr hg)
    have hfbound : ‖(mixedSchwartz 0 b f).toLp 2 volume‖ ≤ compactDerivativeL2Sum (2*p) f :=
      Finset.single_le_sum (s := Finset.range (2*p+1)) (a := b)
        (f := fun k => ‖(mixedSchwartz 0 k f).toLp 2 volume‖) (fun _ _ => norm_nonneg _)
        (Finset.mem_range.mpr (by omega))
    exact h.trans (mul_le_mul
      (mul_le_mul (pow_le_pow_right₀ hθ (by omega : a ≤ 2*p)) hfbound (norm_nonneg _)
        (by positivity))
      (compactDerivativeL2Sum_mono a (2*p) (by omega) g)
      (compactDerivativeL2Sum_nonneg _ _)
      (mul_nonneg (pow_nonneg (zero_le_one.trans hθ) _) (compactDerivativeL2Sum_nonneg _ _)))
  have hsum : mixedL2Sum (2*p) (zakSchwartzTranspose g f) ≤
      K*compactDerivativeL2Sum (2*p) f*compactDerivativeL2Sum (2*p) g := by
    unfold mixedL2Sum
    calc
      _ ≤ ∑ z ∈ mixedIndices (2*p),
          θ^(2*p)*compactDerivativeL2Sum (2*p) f*compactDerivativeL2Sum (2*p) g := by
        apply Finset.sum_le_sum
        intro z hz
        exact hsingle z.1 z.2 ((mem_mixedIndices _ _ _).mp hz)
      _ = _ := by rw [Finset.sum_const,nsmul_eq_mul]; dsimp [K]; ring
  apply (hreverse _).trans
  apply (mul_le_mul_of_nonneg_left hsum hD.le).trans
  have hf0 := compactDerivativeL2Sum_nonneg (2*p) f
  have hg0 := compactDerivativeL2Sum_nonneg (2*p) g
  nlinarith [mul_nonneg hf0 hg0]

/-- The actual original native source acts on compact separated Zak tests
with the sharp 2p derivative count needed by shrinking Newton membership. -/
theorem exists_zakTensorAction_sharp_native_bound (p : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : HermiteScale (-(p:ℤ))) (f g : SchwartzMap ℝ ℂ) (r : ℝ),
      r < 1/2 → (∀ y : ℝ, r ≤ |y| → f y=0) → (∀ y : ℝ, r ≤ |y| → g y=0) →
      ‖zakTensorAction (hermiteScaleDistribution p T) f g‖ ≤
        C*‖T‖*compactDerivativeL2Sum (2*p) f*compactDerivativeL2Sum (2*p) g := by
  obtain ⟨C,hC,hbound⟩ := exists_zakSchwartzTranspose_native_bound p
  refine ⟨C,hC,fun T f g r hr hf hg => ?_⟩
  rw [← zakSchwartzTranspose_realizes,hermiteScaleDistribution_apply]
  have h := (norm_hermiteScalePairing_le (p:ℤ) T (schwartzToHermiteScale p (zakSchwartzTranspose g f))).trans
    (mul_le_mul_of_nonneg_left (hbound f g r hr hf hg) (norm_nonneg T))
  simpa only [mul_assoc,mul_left_comm,mul_comm] using h

end
end MeyerGeneralProblem.Adaptive
