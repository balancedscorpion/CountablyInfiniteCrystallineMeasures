module

public import MeyerGeneralProblem.Interpolation.BlockOverlap
public import Mathlib.Data.Nat.Choose.Sum
import all Mathlib.Data.Nat.Choose.Sum

@[expose] public section

/-!
# Actual derivatives through the quadratic block chart

A finite recursive Leibniz expansion controls derivatives of `h(x²)` by
the actual derivatives of `h`. Its constants precede the local function
and the position; no bound on a derivative is inferred from a value bound.
-/

namespace MeyerGeneralProblem

open scoped ContDiff BigOperators

noncomputable section

/-- The monomial-weighted derivative used in the quadratic chain recursion. -/
def quadraticChainMonomial (a b : ℕ) (h : ℝ → ℂ) (x : ℝ) : ℂ :=
  x ^ a • iteratedDeriv b h (x ^ 2)

/-- Finite recursion giving the actual differentiated quadratic monomial. -/
def quadraticChainExpansion : ℕ → ℕ → ℕ → (ℝ → ℂ) → ℝ → ℂ
  | 0, a, b, h, x => quadraticChainMonomial a b h x
  | n+1, a, b, h, x => (a : ℝ) • quadraticChainExpansion n (a-1) b h x +
      (2 : ℝ) • quadraticChainExpansion n (a+1) (b+1) h x

/-- Explicit constants for the quadratic chain recursion. -/
def quadraticChainConstant : ℕ → ℕ → ℝ
  | 0, _ => 1
  | n+1, a => (a : ℝ) * quadraticChainConstant n (a-1) +
      2 * quadraticChainConstant n (a+1)

private theorem contDiff_iteratedDeriv_infty {h : ℝ → ℂ}
    (hh : ContDiff ℝ ∞ h) (b : ℕ) : ContDiff ℝ ∞ (iteratedDeriv b h) := by
  induction b with
  | zero => simpa using hh
  | succ b ih =>
    rw [iteratedDeriv_succ]
    exact (show ContDiff ℝ (∞ + 1) (iteratedDeriv b h) by simpa using ih).deriv'

/-- Every monomial in the expansion is genuinely smooth. -/
theorem contDiff_quadraticChainMonomial (a b : ℕ) {h : ℝ → ℂ}
    (hh : ContDiff ℝ ∞ h) : ContDiff ℝ ∞ (quadraticChainMonomial a b h) := by
  exact (by fun_prop : ContDiff ℝ ∞ (fun x : ℝ => x ^ a)).smul
    ((contDiff_iteratedDeriv_infty hh b).comp (by fun_prop))

/-- Exact first-derivative chain rule with the zero-power term handled
by its literal zero coefficient. -/
theorem deriv_quadraticChainMonomial (a b : ℕ) {h : ℝ → ℂ}
    (hh : ContDiff ℝ ∞ h) :
    deriv (quadraticChainMonomial a b h) = fun x =>
      (a : ℝ) • quadraticChainMonomial (a-1) b h x +
        (2 : ℝ) • quadraticChainMonomial (a+1) (b+1) h x := by
  funext x
  have hd : HasDerivAt (iteratedDeriv b h)
      (iteratedDeriv (b+1) h (x ^ 2)) (x ^ 2) := by
    rw [iteratedDeriv_succ]
    exact ((contDiff_iteratedDeriv_infty hh b).differentiable (by simp) _).hasDerivAt
  have hcomp := hd.scomp (h := fun y : ℝ => y ^ 2) x (hasDerivAt_pow 2 x)
  have hprod := (hasDerivAt_pow a x).fun_smul hcomp
  change deriv (fun y : ℝ => y ^ a • iteratedDeriv b h (y ^ 2)) x = _
  have hderiv : deriv (fun y : ℝ => y ^ a • iteratedDeriv b h (y ^ 2)) x =
      x ^ a • ((2 : ℝ) * x) • iteratedDeriv (b+1) h (x ^ 2) +
        ((a : ℝ) * x ^ (a-1)) • iteratedDeriv b h (x ^ 2) := by
    simpa only [Pi.smul_apply, Function.comp_apply, Nat.cast_ofNat,
      show 2-1=1 by rfl, pow_one] using hprod.deriv
  rw [hderiv]
  simp only [quadraticChainMonomial, smul_smul, pow_succ]
  module

/-- The finite recursion equals the genuine iterated derivative. -/
theorem iteratedDeriv_quadraticChainMonomial (n a b : ℕ) {h : ℝ → ℂ}
    (hh : ContDiff ℝ ∞ h) :
    iteratedDeriv n (quadraticChainMonomial a b h) =
      quadraticChainExpansion n a b h := by
  induction n generalizing a b with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ', deriv_quadraticChainMonomial a b hh]
    funext x
    rw [iteratedDeriv_fun_add
      (((contDiff_quadraticChainMonomial (a-1) b hh).of_le (by simp)).const_smul (a : ℝ)).contDiffAt
      (((contDiff_quadraticChainMonomial (a+1) (b+1) hh).of_le (by simp)).const_smul (2 : ℝ)).contDiffAt]
    simp only [iteratedDeriv_fun_const_smul_field, ih, quadraticChainExpansion]

/-- All explicit quadratic-chain constants are nonnegative. -/
theorem quadraticChainConstant_nonneg (n a : ℕ) : 0 ≤ quadraticChainConstant n a := by
  induction n generalizing a with
  | zero => norm_num [quadraticChainConstant]
  | succ n ih =>
    simp only [quadraticChainConstant]
    exact add_nonneg (mul_nonneg (Nat.cast_nonneg a) (ih (a-1)))
      (mul_nonneg (by norm_num) (ih (a+1)))

/-- An actual finite derivative tower bounds the recursive expansion on
the exterior physical ray. The constant is independent of the local data. -/
theorem norm_quadraticChainExpansion_le (n a b : ℕ) (h : ℝ → ℂ)
    {x M : ℝ} (hx : 1 ≤ |x|) (hM : 0 ≤ M)
    (hbound : ∀ i, b ≤ i → i ≤ b+n → ‖iteratedDeriv i h (x ^ 2)‖ ≤ M) :
    ‖quadraticChainExpansion n a b h x‖ ≤
      quadraticChainConstant n a * |x| ^ (a+n) * M := by
  induction n generalizing a b with
  | zero =>
    simpa [quadraticChainExpansion, quadraticChainMonomial, quadraticChainConstant,
      norm_smul, Real.norm_eq_abs, abs_pow] using
      mul_le_mul_of_nonneg_left (hbound b le_rfl (by omega)) (pow_nonneg (abs_nonneg x) a)
  | succ n ih =>
    have h₁ := ih (a-1) b (fun i hi hi' => hbound i hi (by omega))
    have h₂ := ih (a+1) (b+1) (fun i hi hi' => hbound i (by omega) (by omega))
    have hpow : |x| ^ (a-1+n) ≤ |x| ^ (a+(n+1)) :=
      pow_le_pow_right₀ hx (by omega)
    have hC₁ := quadraticChainConstant_nonneg n (a-1)
    have hC₂ := quadraticChainConstant_nonneg n (a+1)
    calc
      _ ≤ ‖(a : ℝ) • quadraticChainExpansion n (a-1) b h x‖ +
          ‖(2 : ℝ) • quadraticChainExpansion n (a+1) (b+1) h x‖ := norm_add_le _ _
      _ = (a : ℝ) * ‖quadraticChainExpansion n (a-1) b h x‖ +
          2 * ‖quadraticChainExpansion n (a+1) (b+1) h x‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg (Nat.cast_nonneg a), Real.norm_of_nonneg (by norm_num)]
      _ ≤ (a : ℝ) * (quadraticChainConstant n (a-1) * |x| ^ (a-1+n) * M) +
          2 * (quadraticChainConstant n (a+1) * |x| ^ (a+1+n) * M) := by gcongr
      _ ≤ (a : ℝ) * (quadraticChainConstant n (a-1) * |x| ^ (a+(n+1)) * M) +
          2 * (quadraticChainConstant n (a+1) * |x| ^ (a+(n+1)) * M) := by
        rw [show a+1+n=a+(n+1) by omega]
        gcongr
      _ = _ := by simp only [quadraticChainConstant]; ring

/-- Actual derivatives through the quadratic chart have the exact
polynomial physical growth needed for weighted block interpolation. -/
theorem norm_iteratedDeriv_comp_sq_le (n : ℕ) {h : ℝ → ℂ}
    (hh : ContDiff ℝ ∞ h) {x M : ℝ} (hx : 1 ≤ |x|) (hM : 0 ≤ M)
    (hbound : ∀ i ≤ n, ‖iteratedDeriv i h (x ^ 2)‖ ≤ M) :
    ‖iteratedDeriv n (fun y : ℝ => h (y ^ 2)) x‖ ≤
      quadraticChainConstant n 0 * |x| ^ n * M := by
  have heq : (fun y : ℝ => h (y ^ 2)) = quadraticChainMonomial 0 0 h := by
    funext y
    simp [quadraticChainMonomial]
  rw [heq, iteratedDeriv_quadraticChainMonomial n 0 0 hh]
  simpa only [zero_add] using norm_quadraticChainExpansion_le n 0 0 h hx hM
    (fun i _ hi => hbound i (by simpa using hi))

/-- Genuine Leibniz formula for a real scalar cutoff and a complex local
function, retaining every binomial factor. -/
theorem iteratedDeriv_fun_real_smul {f : ℝ → ℝ} {g : ℝ → ℂ}
    {n : ℕ} {x : ℝ} (hf : ContDiffAt ℝ n f x) (hg : ContDiffAt ℝ n g x) :
    iteratedDeriv n (fun y => f y • g y) x =
      ∑ i ∈ Finset.range (n+1),
        n.choose i • iteratedDeriv i f x • iteratedDeriv (n-i) g x := by
  simpa only [iteratedDerivWithin_univ, Pi.smul_def'] using
    iteratedDerivWithin_smul (Set.mem_univ x) uniqueDiffOn_univ hf.contDiffWithinAt hg.contDiffWithinAt

/-- One positive constant controls the actual first k cutoff derivatives,
uniformly in every block width at least one and every block index. -/
theorem exists_uniform_blockCutoff_derivatives_le (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℝ), 1 ≤ B → ∀ (b : ℕ) (s : ℝ) (j : ℕ), j ≤ k →
      ‖iteratedDeriv j (blockCutoff B b) s‖ ≤ C := by
  choose c hcpos hc using exists_uniform_blockCutoff_derivative_bound
  let C : ℝ := ∑ j ∈ Finset.range (k+1), c j
  have hle (j : ℕ) (hj : j ≤ k) : c j ≤ C :=
    Finset.single_le_sum (fun i _ => (hcpos i).le) (Finset.mem_range.mpr (by omega))
  refine ⟨C, (hcpos 0).trans_le (hle 0 (Nat.zero_le k)), ?_⟩
  intro B hB b s j hj
  have hBpos : 0 < B := by linarith
  have hinv : B⁻¹ ≤ 1 := (inv_le_one₀ hBpos).mpr hB
  have hpow : B⁻¹ ^ j ≤ 1 := pow_le_one₀ (inv_nonneg.mpr hBpos.le) hinv
  exact (hc j B hBpos b s).trans
    ((mul_le_mul_of_nonneg_left hpow (hcpos j).le).trans_eq (mul_one _)) |>.trans (hle j hj)

/-- The actual cutoff product has the finite-order bound used before
quadratic substitution. The input is only the local function's actual
derivative values, never a gap-dependent inverse Vandermonde bound. -/
theorem exists_uniform_cutoffProduct_derivative_bound (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℝ), 1 ≤ B → ∀ (b : ℕ) (h : ℝ → ℂ),
      ContDiff ℝ ∞ h → ∀ (s M : ℝ), 0 ≤ M →
      (∀ i ≤ k, ‖iteratedDeriv i h s‖ ≤ M) →
      ∀ j ≤ k, ‖iteratedDeriv j (fun t => blockCutoff B b t • h t) s‖ ≤ C*M := by
  obtain ⟨K, hK, hcut⟩ := exists_uniform_blockCutoff_derivatives_le k
  refine ⟨(2:ℝ)^k*K, by positivity, ?_⟩
  intro B hB b h hh s M hM hbound j hj
  rw [iteratedDeriv_fun_real_smul
    (contDiff_blockCutoff B b).contDiffAt ((hh.of_le (by simp)).contDiffAt)]
  calc
    _ ≤ ∑ i ∈ Finset.range (j+1),
        ‖j.choose i • iteratedDeriv i (blockCutoff B b) s • iteratedDeriv (j-i) h s‖ :=
      norm_sum_le _ _
    _ = ∑ i ∈ Finset.range (j+1),
        (j.choose i:ℝ) * ‖iteratedDeriv i (blockCutoff B b) s‖ * ‖iteratedDeriv (j-i) h s‖ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← Nat.cast_smul_eq_nsmul ℝ, norm_smul, norm_smul,
        Real.norm_of_nonneg (Nat.cast_nonneg _), mul_assoc]
    _ ≤ ∑ i ∈ Finset.range (j+1), (j.choose i:ℝ)*K*M := by
      apply Finset.sum_le_sum
      intro i hi
      have hik : i ≤ k := by have := Finset.mem_range.mp hi; omega
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hcut B hB b s i hik) (Nat.cast_nonneg _))
        (hbound (j-i) (by omega)) (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) hK.le)
    _ = (2:ℝ)^j*K*M := by
      rw [← Finset.sum_mul, ← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow, Nat.cast_ofNat]
    _ ≤ _ := by gcongr; norm_num

/-- Uniform derivative growth for the actual cutoff local piece in the
physical coordinate. The coefficient is chosen before every block and
local function, and the power of x is the requested derivative order. -/
theorem exists_uniform_quadraticCutoff_derivative_bound (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : ℝ), 1 ≤ B → ∀ (b : ℕ) (h : ℝ → ℂ),
      ContDiff ℝ ∞ h → ∀ (x M : ℝ), 1 ≤ |x| → 0 ≤ M →
      (∀ i ≤ k, ‖iteratedDeriv i h (x^2)‖ ≤ M) →
      ‖iteratedDeriv k (fun y => blockCutoff B b (y^2) • h (y^2)) x‖ ≤ C*|x|^k*M := by
  obtain ⟨C, hC, hprod⟩ := exists_uniform_cutoffProduct_derivative_bound k
  refine ⟨quadraticChainConstant k 0*C,
    mul_nonneg (quadraticChainConstant_nonneg _ _) hC.le, ?_⟩
  intro B hB b h hh x M hx hM hbound
  have h := norm_iteratedDeriv_comp_sq_le k ((contDiff_blockCutoff B b).smul hh)
    hx (mul_nonneg hC.le hM) (hprod B hB b h hh (x^2) M hM hbound)
  simp only [Pi.smul_apply'] at h
  convert h using 1; ring

end

end MeyerGeneralProblem
