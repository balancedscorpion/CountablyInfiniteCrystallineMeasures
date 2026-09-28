module

public import MeyerGeneralProblem.Cardinal.Adaptive.SeamFullLeadingBounds
public import MeyerGeneralProblem.Cardinal.Adaptive.SeamMomentDecay

@[expose] public section

/-! # Complete actual seam kernel and both-arm product bounds -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section

section Kernel
variable (a b ta tb : ℕ → ℂ)
variable (ha : ∀ i, ‖a i‖ ≤ (1/4096 : ℝ)^2) (hb : ∀ i, ‖b i‖ ≤ (1/4096 : ℝ)^2)
variable (hta : ∀ i, ‖ta i‖ ≤ (1/4096 : ℝ)^3) (htb : ∀ i, ‖tb i‖ ≤ (1/4096 : ℝ)^3)
variable (u : SeamMomentArray) (hu : seamPProjection u=u)
variable (hFu : seamFullOperator a b ta tb ha hb hta htb u=0)
include a b ta tb ha hb hta htb u hu hFu

/-- A complete actual flag-kernel vector is zero when its zeroth diagonal reading vanishes.
All operator norms, complementary inverses and leading compression bounds are constructed. -/
theorem seamFull_flag_zero (hz : u ((0,false),(0,false))=0) : u=0 :=
  seamSchur_flag_zero _ (seamFullOperator_close a b ta tb ha hb hta htb)
    (seamFullOperator_leading_bound a b ta tb ha hb hta htb) u hu hFu hz

/-- The actual full flag kernel has a uniform norm controlled by its genuine zeroth reading. -/
theorem seamFull_flag_norm : ‖u‖ ≤ 4*‖u ((0,false),(0,false))‖ :=
  seamSchur_flag_norm _ (seamFullOperator_close a b ta tb ha hb hta htb)
    (seamFullOperator_leading_bound a b ta tb ha hb hta htb) u hu hFu

/-- The complete actual physical array has maximum-index product decay on both infinite arms. -/
theorem seamFull_array_product (i j : ℕ) (e f : Bool) :
    ‖(u+seamPhysicalGraph ta hta u) ((i,e),(j,f))‖ ≤
      5*(∏ n ∈ Finset.range (max i j), (8589934592*(‖ta n‖+‖tb n‖+‖b n‖)))*‖u ((0,false),(0,false))‖ :=
  seamFull_moment_product a b ta tb ha hb hta htb
    (fun h => seamFullOperator_leading_bound _ _ _ _ _ _ _ _) u hu hFu i j e f

/-- Explicit phase-product form of the entire two-arm bound; zero-padded phases are allowed. -/
theorem seamFull_array_phase_product (ε : ℕ → ℝ)
    (hε : ∀ n, ‖ta n‖+‖tb n‖+‖b n‖ ≤ 128*ε n)
    (i j : ℕ) (e f : Bool) :
    ‖(u+seamPhysicalGraph ta hta u) ((i,e),(j,f))‖ ≤
      5*(1099511627776 : ℝ)^(max i j)*(∏ n ∈ Finset.range (max i j), ε n)*‖u ((0,false),(0,false))‖ := by
  have he (n : ℕ) : 8589934592*(‖ta n‖+‖tb n‖+‖b n‖) ≤ (1099511627776 : ℝ)*ε n := by
    nlinarith [hε n]
  have hp : (∏ n ∈ Finset.range (max i j), (8589934592*(‖ta n‖+‖tb n‖+‖b n‖))) ≤
      (1099511627776 : ℝ)^(max i j)*(∏ n ∈ Finset.range (max i j), ε n) := by
    calc
      _ ≤ ∏ n ∈ Finset.range (max i j), ((1099511627776 : ℝ)*ε n) :=
        Finset.prod_le_prod₀ (fun n _ => by positivity) (fun n _ => he n)
      _ = _ := by rw [Finset.prod_mul_distrib]; simp
  apply (seamFull_array_product a b ta tb ha hb hta htb u hu hFu i j e f).trans
  calc
    _ ≤ (5*((1099511627776 : ℝ)^(max i j)*(∏ n ∈ Finset.range (max i j), ε n)))*‖u ((0,false),(0,false))‖ := by
      gcongr
    _ = _ := by ring

end Kernel
end
end MeyerGeneralProblem.Adaptive
