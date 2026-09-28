module

public import MeyerGeneralProblem.Cardinal.Adaptive.ReverseZakSampling
public import Mathlib.Analysis.Calculus.SmoothSeries
import all Mathlib.Analysis.Calculus.SmoothSeries

@[expose] public section

/-! The actual reverse Zak series and its mixed derivatives. -/

noncomputable section
open scoped BigOperators ContDiff

namespace MeyerGeneralProblem.Adaptive

/-- The frequency in the literal inverse Zak Fourier series. -/
def reverseZakFrequency (n : ℤ) : ℂ := (2*Real.pi:ℝ)*Complex.I*(n:ℂ)

/-- The complete mixed-derivative series, before any chart cutoff. -/
def reverseZakJet (f : SchwartzMap ℝ ℂ) (a b : ℕ) (x y : ℝ) : ℂ :=
  ∑' n : ℤ, reverseZakFrequency n ^ b * iteratedDeriv a (f : ℝ → ℂ) (x+n) *
    Complex.exp (reverseZakFrequency n * y)

/-- The actual reverse Zak chart is the zeroth mixed-derivative series. -/
def reverseZakChart (f : SchwartzMap ℝ ℂ) (x y : ℝ) : ℂ := reverseZakJet f 0 0 x y

/-- Unit modulus of each actual Fourier character. -/
theorem reverseZak_character_norm (n : ℤ) (y : ℝ) :
    ‖Complex.exp (reverseZakFrequency n*y)‖ = 1 := by
  rw [Complex.norm_exp]
  simp [reverseZakFrequency,Complex.mul_re,Complex.mul_im]

/-- The frequency magnitude uses the literal integer index. -/
theorem reverseZakFrequency_norm (n : ℤ) :
    ‖reverseZakFrequency n‖ = (2*Real.pi)*|(n:ℝ)| := by
  simp only [reverseZakFrequency,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    Complex.norm_I,mul_one,Complex.norm_intCast]
  rw [abs_of_pos (by norm_num : 0 < (2:ℝ)),abs_of_pos Real.pi_pos]

/-- A local summable majorant, obtained at an auxiliary order solely for
termwise differentiation. The sharp final native bound uses a separate order. -/
theorem exists_reverseZak_local_majorant (f : SchwartzMap ℝ ℂ) (a b : ℕ) (c : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, |x-c| ≤ 1 → ∀ n : ℤ,
      (1+|(n:ℝ)|)^b * ‖iteratedDeriv a (f : ℝ → ℂ) (x+n)‖ ≤ C*integerCombDecay n := by
  obtain ⟨C,hC,hb⟩ := exists_reverseZak_lattice_native_bound (a+b+2) a (b+2) (by omega)
  let g := combSchwartzTranslation c f
  refine ⟨C*‖schwartzToHermiteScale (a+b+2) g‖, by positivity, ?_⟩
  intro x hx n
  obtain ⟨hs,ht⟩ := hb g (x-c) hx
  have hval : iteratedDeriv a (g : ℝ → ℂ) (x-c+n) =
      iteratedDeriv a (f : ℝ → ℂ) (x+n) := by
    change iteratedDeriv a (fun z => f (c+z)) (x-c+n) = _
    simp only [iteratedDeriv_comp_const_add,show c+(x-c+(n:ℝ))=x+n by ring]
  have hn := (Summable.le_tsum hs n (fun n _ => by positivity)).trans ht
  rw [hval] at hn
  rw [integerCombDecay,inv_pow,← div_eq_mul_inv,le_div_iff₀ (by positivity)]
  simpa only [pow_add,mul_assoc,mul_left_comm,mul_comm] using hn

/-- Absolute convergence of every actual mixed-derivative series everywhere. -/
theorem summable_reverseZakJet (f : SchwartzMap ℝ ℂ) (a b : ℕ) (x y : ℝ) :
    Summable (fun n : ℤ => reverseZakFrequency n ^ b *
      iteratedDeriv a (f : ℝ → ℂ) (x+n) * Complex.exp (reverseZakFrequency n*y)) := by
  obtain ⟨C,hC,hb⟩ := exists_reverseZak_local_majorant f a b x
  apply Summable.of_norm_bounded (summable_integerCombDecay.mul_left ((2*Real.pi)^b*C))
  intro n
  rw [norm_mul,norm_mul,norm_pow,reverseZak_character_norm,mul_one,reverseZakFrequency_norm,mul_pow]
  have hh := hb x (by simp) n
  have hw : |(n:ℝ)|^b ≤ (1+|(n:ℝ)|)^b := by gcongr; linarith
  calc
    (2*Real.pi)^b*|(n:ℝ)|^b*‖iteratedDeriv a (f : ℝ → ℂ) (x+n)‖
      ≤ (2*Real.pi)^b*((1+|(n:ℝ)|)^b*‖iteratedDeriv a (f : ℝ → ℂ) (x+n)‖) := by rw [mul_assoc]; gcongr
    _ ≤ (2*Real.pi)^b*(C*integerCombDecay n) := by gcongr
    _ = ((2*Real.pi)^b*C)*integerCombDecay n := by ring

/-- Sharp original-native bound for the literal mixed-derivative series. -/
theorem exists_reverseZakJet_native_bound (p a b : ℕ) (hdeg : a+b+2 ≤ 2*p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : SchwartzMap ℝ ℂ) (x y : ℝ), |x| ≤ 1 →
      ‖reverseZakJet f a b x y‖ ≤ C*‖schwartzToHermiteScale p f‖ := by
  obtain ⟨C,hC,hb⟩ := exists_reverseZak_lattice_native_bound p a b hdeg
  refine ⟨(2*Real.pi)^b*C, by positivity, ?_⟩
  intro f x y hx
  obtain ⟨hs,ht⟩ := hb f x hx
  apply (norm_tsum_le_tsum_norm (summable_reverseZakJet f a b x y).norm).trans
  have hpoint (n : ℤ) : ‖reverseZakFrequency n^b*iteratedDeriv a (f : ℝ → ℂ) (x+n)*
      Complex.exp (reverseZakFrequency n*y)‖ ≤
      (2*Real.pi)^b*((1+|(n:ℝ)|)^b*‖iteratedDeriv a (f : ℝ → ℂ) (x+n)‖) := by
    rw [norm_mul,norm_mul,norm_pow,reverseZak_character_norm,mul_one,reverseZakFrequency_norm,mul_pow]
    rw [mul_assoc]
    gcongr
    linarith
  apply ((summable_reverseZakJet f a b x y).norm.tsum_le_tsum hpoint
    (hs.mul_left ((2*Real.pi)^b))).trans
  rw [tsum_mul_left]
  exact (mul_le_mul_of_nonneg_left ht (by positivity)).trans_eq (by ring)

private theorem reverseZak_term_norm_le (f : SchwartzMap ℝ ℂ) (a b : ℕ) (n : ℤ) (x y : ℝ) :
    ‖reverseZakFrequency n^b * iteratedDeriv a (f : ℝ → ℂ) (x+n) *
      Complex.exp (reverseZakFrequency n*y)‖ ≤
      (2*Real.pi)^b*((1+|(n:ℝ)|)^b*‖iteratedDeriv a (f : ℝ → ℂ) (x+n)‖) := by
  rw [norm_mul,norm_mul,norm_pow,reverseZak_character_norm,mul_one,reverseZakFrequency_norm,
    mul_pow,mul_assoc]
  gcongr
  linarith

private theorem reverseZak_term_hasDerivAt_x (f : SchwartzMap ℝ ℂ) (a b : ℕ)
    (n : ℤ) (x y : ℝ) :
    HasDerivAt (fun z : ℝ => reverseZakFrequency n^b * iteratedDeriv a (f : ℝ → ℂ) (z+n) *
      Complex.exp (reverseZakFrequency n*y))
      (reverseZakFrequency n^b * iteratedDeriv (a+1) (f : ℝ → ℂ) (x+n) *
        Complex.exp (reverseZakFrequency n*y)) x := by
  have hd : HasDerivAt (iteratedDeriv a (f : ℝ → ℂ))
      (iteratedDeriv (a+1) (f : ℝ → ℂ) (x+n)) (x+n) := by
    rw [iteratedDeriv_succ]
    exact ((f.smooth (a+1)).differentiable_iteratedDeriv' a).differentiableAt.hasDerivAt
  simpa only [Function.comp_def,id_eq,mul_one,one_smul] using
    ((hd.scomp x ((hasDerivAt_id x).add_const (n:ℝ))).const_mul
      (reverseZakFrequency n^b)).mul_const (Complex.exp (reverseZakFrequency n*y))

private theorem reverseZak_term_hasDerivAt_y (f : SchwartzMap ℝ ℂ) (a b : ℕ)
    (n : ℤ) (x y : ℝ) :
    HasDerivAt (fun z : ℝ => reverseZakFrequency n^b * iteratedDeriv a (f : ℝ → ℂ) (x+n) *
      Complex.exp (reverseZakFrequency n*z))
      (reverseZakFrequency n^(b+1) * iteratedDeriv a (f : ℝ → ℂ) (x+n) *
        Complex.exp (reverseZakFrequency n*y)) y := by
  have hh := (((hasDerivAt_id y).ofReal_comp.const_mul (reverseZakFrequency n)).cexp).const_mul
    (reverseZakFrequency n^b * iteratedDeriv a (f : ℝ → ℂ) (x+n))
  simpa only [id_eq,Complex.ofReal_one,mul_one,one_mul,pow_succ,mul_assoc,mul_left_comm,mul_comm] using hh

/-- Differentiation in the spatial coordinate of the full reverse Zak series. -/
theorem reverseZakJet_hasDerivAt_x (f : SchwartzMap ℝ ℂ) (a b : ℕ) (x y : ℝ) :
    HasDerivAt (fun z => reverseZakJet f a b z y) (reverseZakJet f (a+1) b x y) x := by
  obtain ⟨C,hC,hb⟩ := exists_reverseZak_local_majorant f (a+1) b x
  unfold reverseZakJet
  apply hasDerivAt_tsum_of_isPreconnected
    (g := fun n (z : ℝ) => reverseZakFrequency n^b * iteratedDeriv a (f : ℝ → ℂ) (z+n) *
      Complex.exp (reverseZakFrequency n*y))
    (g' := fun n (z : ℝ) => reverseZakFrequency n^b * iteratedDeriv (a+1) (f : ℝ → ℂ) (z+n) *
      Complex.exp (reverseZakFrequency n*y))
    (u := fun n => ((2*Real.pi)^b*C)*integerCombDecay n)
    (t := Set.Ioo (x-1) (x+1)) (y₀ := x)
    (summable_integerCombDecay.mul_left _) isOpen_Ioo (convex_Ioo _ _).isPreconnected
  · intro n z hz
    exact reverseZak_term_hasDerivAt_x f a b n z y
  · intro n z hz
    have hh := hb z (abs_le.mpr ⟨by linarith [hz.1],by linarith [hz.2]⟩) n
    exact (reverseZak_term_norm_le f (a+1) b n z y).trans
      ((mul_le_mul_of_nonneg_left hh (by positivity)).trans_eq (by ring))
  · constructor <;> linarith
  · exact summable_reverseZakJet f a b x y
  · constructor <;> linarith

/-- Differentiation in the Fourier coordinate of the full reverse Zak series. -/
theorem reverseZakJet_hasDerivAt_y (f : SchwartzMap ℝ ℂ) (a b : ℕ) (x y : ℝ) :
    HasDerivAt (fun z => reverseZakJet f a b x z) (reverseZakJet f a (b+1) x y) y := by
  obtain ⟨C,hC,hb⟩ := exists_reverseZak_local_majorant f a (b+1) x
  unfold reverseZakJet
  apply hasDerivAt_tsum
    (g := fun n (z : ℝ) => reverseZakFrequency n^b * iteratedDeriv a (f : ℝ → ℂ) (x+n) *
      Complex.exp (reverseZakFrequency n*z))
    (g' := fun n (z : ℝ) => reverseZakFrequency n^(b+1) * iteratedDeriv a (f : ℝ → ℂ) (x+n) *
      Complex.exp (reverseZakFrequency n*z))
    (u := fun n => ((2*Real.pi)^(b+1)*C)*integerCombDecay n) (y₀ := y)
    (summable_integerCombDecay.mul_left _)
  · intro n z
    exact reverseZak_term_hasDerivAt_y f a b n x z
  · intro n z
    have hh := hb x (by simp) n
    exact (reverseZak_term_norm_le f a (b+1) n x z).trans
      ((mul_le_mul_of_nonneg_left hh (by positivity)).trans_eq (by ring))
  · exact summable_reverseZakJet f a b x y

/-- Every iterated spatial derivative is the literal differentiated series. -/
theorem iteratedDeriv_reverseZakJet_x (f : SchwartzMap ℝ ℂ) (a b k : ℕ) (y : ℝ) :
    iteratedDeriv k (fun x => reverseZakJet f a b x y) =
      fun x => reverseZakJet f (a+k) b x y := by
  induction k with
  | zero => simp only [iteratedDeriv_zero,add_zero]
  | succ k ih =>
      rw [iteratedDeriv_succ,ih]
      funext x
      simpa only [Nat.add_assoc] using (reverseZakJet_hasDerivAt_x f (a+k) b x y).deriv

/-- Every iterated Fourier-coordinate derivative is the literal differentiated series. -/
theorem iteratedDeriv_reverseZakJet_y (f : SchwartzMap ℝ ℂ) (a b k : ℕ) (x : ℝ) :
    iteratedDeriv k (fun y => reverseZakJet f a b x y) =
      fun y => reverseZakJet f a (b+k) x y := by
  induction k with
  | zero => simp only [iteratedDeriv_zero,add_zero]
  | succ k ih =>
      rw [iteratedDeriv_succ,ih]
      funext y
      simpa only [Nat.add_assoc] using (reverseZakJet_hasDerivAt_y f a (b+k) x y).deriv

/-- Smoothness in the spatial variable at every Fourier coordinate. -/
theorem reverseZakJet_contDiff_x (f : SchwartzMap ℝ ℂ) (a b : ℕ) (y : ℝ) :
    ContDiff ℝ ∞ (fun x => reverseZakJet f a b x y) := by
  apply contDiff_of_differentiable_iteratedDeriv
  intro k hk
  rw [iteratedDeriv_reverseZakJet_x]
  exact fun x => (reverseZakJet_hasDerivAt_x f (a+k) b x y).differentiableAt

/-- Smoothness in the Fourier variable of every actual spatial derivative. -/
theorem reverseZakJet_contDiff_y (f : SchwartzMap ℝ ℂ) (a b : ℕ) (x : ℝ) :
    ContDiff ℝ ∞ (fun y => reverseZakJet f a b x y) := by
  apply contDiff_of_differentiable_iteratedDeriv
  intro k hk
  rw [iteratedDeriv_reverseZakJet_y]
  exact fun y => (reverseZakJet_hasDerivAt_y f a (b+k) x y).differentiableAt

/-- Exact mixed derivatives of the actual reverse chart, in the same order
used by finite-smoothness tensor interpolation. -/
theorem reverseZakChart_mixed_derivative (f : SchwartzMap ℝ ℂ) (a b : ℕ) (x y : ℝ) :
    iteratedDeriv b (fun v => iteratedDeriv a (fun u => reverseZakChart f u v) x) y =
      reverseZakJet f a b x y := by
  simp only [reverseZakChart,iteratedDeriv_reverseZakJet_x,zero_add,
    iteratedDeriv_reverseZakJet_y]

/-- Native control of the actual mixed derivatives, with no additional test
regularity assumption and no replacement by formal coefficient arrays. -/
theorem exists_reverseZakChart_derivative_bound (p a b : ℕ) (hdeg : a+b+2 ≤ 2*p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : SchwartzMap ℝ ℂ) (x y : ℝ), |x| ≤ 1 →
      ‖iteratedDeriv b (fun v => iteratedDeriv a (fun u => reverseZakChart f u v) x) y‖ ≤
        C*‖schwartzToHermiteScale p f‖ := by
  simpa only [reverseZakChart_mixed_derivative] using exists_reverseZakJet_native_bound p a b hdeg

/-- One constant controls every mixed derivative in the square of orders at
most `r`, at exactly the original order `r+1`. -/
theorem exists_reverseZakChart_mixed_bound (r : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : SchwartzMap ℝ ℂ) (a b : ℕ), a ≤ r → b ≤ r →
      ∀ x y : ℝ, |x| ≤ 1 →
      ‖iteratedDeriv b (fun v => iteratedDeriv a (fun u => reverseZakChart f u v) x) y‖ ≤
        C*‖schwartzToHermiteScale (r+1) f‖ := by
  classical
  have hh (i : Fin (r+1) × Fin (r+1)) :=
    exists_reverseZakChart_derivative_bound (r+1) i.1.val i.2.val (by omega)
  choose C hC hb using hh
  let D : ℝ := ∑ i, C i
  have hCD (i : Fin (r+1) × Fin (r+1)) : C i ≤ D :=
    Finset.single_le_sum (fun j _ => (hC j).le) (Finset.mem_univ i)
  have hD : 0 < D := (hC (0,0)).trans_le (hCD (0,0))
  refine ⟨D,hD,?_⟩
  intro f a b ha hb' x y hx
  let i : Fin (r+1) × Fin (r+1) := (⟨a,by omega⟩,⟨b,by omega⟩)
  exact (hb i f x y hx).trans (mul_le_mul_of_nonneg_right (hCD i) (norm_nonneg _))

end MeyerGeneralProblem.Adaptive
