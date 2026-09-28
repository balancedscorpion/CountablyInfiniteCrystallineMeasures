module

public import MeyerGeneralProblem.Cardinal.Adaptive.HeadNativeBounds
public import MeyerGeneralProblem.Cardinal.Adaptive.NativeTranslations

@[expose] public section

/-! Sharp lattice sampling for the reverse Zak chart in the original native norm. -/

noncomputable section

open scoped BigOperators

namespace MeyerGeneralProblem.Adaptive

/-- Uniform absolute sampling of a polynomial derivative on every translate of
an integer lattice in the unit chart. The two degrees paid here are exactly the
one original Hermite order in the absolute lattice estimate. -/
theorem exists_mixed_lattice_native_bound (p j a : ℕ) (hdeg : j+a+2 ≤ 2*p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : SchwartzMap ℝ ℂ) (x : ℝ), |x| ≤ 1 →
      Summable (fun n : ℤ => |x+n|^j * ‖iteratedDeriv a (f : ℝ → ℂ) (x+n)‖) ∧
      (∑' n : ℤ, |x+n|^j * ‖iteratedDeriv a (f : ℝ → ℂ) (x+n)‖) ≤
        C * ‖schwartzToHermiteScale p f‖ := by
  obtain ⟨A,hA,ha⟩ := exists_lattice_absolute_hermite_one_bound 1 0 (by norm_num)
  obtain ⟨B,hB,hb⟩ := exists_hermite_translation_bound 1
  obtain ⟨D,hD,hd⟩ := exists_mixedSchwartz_norm_bound (p-1) 1 j a (by omega)
  refine ⟨A*(B*4)*D, by positivity, ?_⟩
  intro f x hx
  have hs := ha (combSchwartzTranslation x (mixedSchwartz j a f))
  simp only [zero_add,one_mul,combSchwartzTranslation_apply,mixedSchwartz_apply,
    norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs] at hs
  refine ⟨hs.1, hs.2.trans ?_⟩
  have ht := hb x (mixedSchwartz j a f)
  have hp : 1+(p-1)=p := by omega
  have hm := hd f
  rw [hp] at hm
  have hx2 : (1+|x|)^(2*1) ≤ (4:ℝ) := by
    calc
      (1+|x|)^(2*1) ≤ (2:ℝ)^(2*1) := by gcongr; linarith
      _ = 4 := by norm_num
  calc
    A * ‖schwartzToHermiteScale 1 (combSchwartzTranslation x (mixedSchwartz j a f))‖
      ≤ A * (B*4*‖schwartzToHermiteScale 1 (mixedSchwartz j a f)‖) :=
        mul_le_mul_of_nonneg_left (ht.trans (by gcongr)) hA.le
    _ ≤ A * (B*4*(D*‖schwartzToHermiteScale p f‖)) := by gcongr
    _ = (A*(B*4)*D)*‖schwartzToHermiteScale p f‖ := by ring

/-- The integer weight of a reverse Zak derivative is controlled by the zeroth
and highest spatial weights uniformly on the unit chart. -/
theorem reverseZak_weight_bound (b : ℕ) (n : ℤ) (x : ℝ) (hx : |x| ≤ 1) :
    (1+|(n:ℝ)|)^b ≤ 2^(b-1)*(2^b+|x+n|^b) := by
  have ht : |(n:ℝ)| ≤ |x+n|+1 := by
    have hh := abs_sub (x+n) x
    rw [show x+(n:ℝ)-x=n by ring] at hh
    linarith
  exact (pow_le_pow_left₀ (by positivity) (by linarith : 1+|(n:ℝ)| ≤ 2+|x+n|) b).trans
    (add_pow_le (by norm_num) (abs_nonneg _) b)

/-- Weighted absolute sampling with the exact total-degree cost needed by a
reverse Zak chart. In particular all mixed orders at most `r` in each coordinate
are controlled by the original `H_(r+1)` norm. -/
theorem exists_reverseZak_lattice_native_bound (p a b : ℕ) (hdeg : a+b+2 ≤ 2*p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : SchwartzMap ℝ ℂ) (x : ℝ), |x| ≤ 1 →
      Summable (fun n : ℤ => (1+|(n:ℝ)|)^b * ‖iteratedDeriv a (f : ℝ → ℂ) (x+n)‖) ∧
      (∑' n : ℤ, (1+|(n:ℝ)|)^b * ‖iteratedDeriv a (f : ℝ → ℂ) (x+n)‖) ≤
        C * ‖schwartzToHermiteScale p f‖ := by
  obtain ⟨A,hA,ha⟩ := exists_mixed_lattice_native_bound p 0 a (by omega)
  obtain ⟨B,hB,hb⟩ := exists_mixed_lattice_native_bound p b a (by omega)
  refine ⟨2^(b-1)*(2^b*A+B), by positivity, ?_⟩
  intro f x hx
  obtain ⟨hsa,hta⟩ := ha f x hx
  simp only [pow_zero,one_mul] at hsa hta
  obtain ⟨hsb,htb⟩ := hb f x hx
  have hs := ((hsa.mul_left ((2:ℝ)^b)).add hsb).mul_left ((2:ℝ)^(b-1))
  have hpoint (n : ℤ) :
      (1+|(n:ℝ)|)^b * ‖iteratedDeriv a (f : ℝ → ℂ) (x+n)‖ ≤
      2^(b-1)*(2^b*‖iteratedDeriv a (f : ℝ → ℂ) (x+n)‖+
        |x+n|^b*‖iteratedDeriv a (f : ℝ → ℂ) (x+n)‖) := by
    nlinarith [mul_le_mul_of_nonneg_right (reverseZak_weight_bound b n x hx)
      (norm_nonneg (iteratedDeriv a (f : ℝ → ℂ) (x+n)))]
  have hs' := Summable.of_nonneg_of_le (fun n => by positivity) hpoint hs
  refine ⟨hs', (hs'.tsum_le_tsum hpoint hs).trans ?_⟩
  rw [tsum_mul_left, Summable.tsum_add (hsa.mul_left _) hsb, tsum_mul_left]
  calc
    2^(b-1)*(2^b*(∑' n : ℤ, ‖iteratedDeriv a (f : ℝ → ℂ) (x+n)‖)+
      ∑' n : ℤ, |x+n|^b*‖iteratedDeriv a (f : ℝ → ℂ) (x+n)‖)
      ≤ 2^(b-1)*(2^b*(A*‖schwartzToHermiteScale p f‖)+
        B*‖schwartzToHermiteScale p f‖) := by gcongr
    _ = (2^(b-1)*(2^b*A+B))*‖schwartzToHermiteScale p f‖ := by ring

end MeyerGeneralProblem.Adaptive
