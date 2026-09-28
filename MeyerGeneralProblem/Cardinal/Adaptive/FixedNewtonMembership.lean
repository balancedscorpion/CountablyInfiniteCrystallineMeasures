module

public import MeyerGeneralProblem.Cardinal.Adaptive.FixedNewtonBounds

@[expose] public section

/-! # Complete constant-normalized actual Newton array membership -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open scoped FourierTransform

/-- Actual whole-source Newton readings with a fixed inner chart and the literal
constant normalization. All level pairs and both parity bits are retained. -/
def fixedChartNewtonMoment (R : ℝ) (κ : ℂ) (a b : ℝ) (hab : a < b)
    (ε δ : ℕ → ℝ) (T : TemperedDistribution ℝ ℂ) (i : ℕ) (e : Bool) (j : ℕ) (f : Bool) : ℂ :=
  (((R:ℂ)^(i+j)*κ^(e.toNat+f.toNat))⁻¹)*halfNewtonBilinear T
    (shrinkingNewtonTest (fun l => ε l) i e a b hab)
    (shrinkingNewtonTest (fun l => δ l) j f a b hab)

private theorem summable_shifted_polynomial_geometric (q : ℝ) (hq : 0 < q) (hq1 : q < 1) (m : ℕ) :
    Summable (fun n : ℕ => q^n*((n:ℝ)+1)^m) := by
  have h := (summable_nat_add_iff 1).mpr
    (summable_pow_mul_geometric_of_norm_lt_one m (r := q) (by simpa only [Real.norm_eq_abs,abs_of_pos hq] using hq1))
  have hh := h.mul_right q⁻¹
  have he : (fun n : ℕ => ((n+1:ℕ):ℝ)^m*q^(n+1)*q⁻¹)=(fun n : ℕ => q^n*((n:ℝ)+1)^m) := by
    funext n
    push_cast
    rw [pow_succ]
    field_simp
  rwa [he] at hh

/-- The entire constant-normalized array has a genuine geometric majorant
against the original native source norm, uniform over arbitrary small phase arrays. -/
theorem fixedChartNewtonMoment_bound (R a b : ℝ) (κ : ℂ) (hab : a < b)
    (hb : 0 < b) (hb' : b ≤ 1/8) (hR : 0 < R) (p : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : HermiteScale (-(p:ℤ))) (ε δ : ℕ → ℝ)
      (i j : ℕ) (e f : Bool), (∀ l < i, |ε (l+1)| ≤ b) → (∀ l < j, |δ (l+1)| ≤ b) →
      ‖fixedChartNewtonMoment R κ a b hab ε δ (hermiteScaleDistribution p T) i e j f‖ ≤
        (‖κ^(e.toNat+f.toNat)‖⁻¹*C*‖T‖)*
        ((64*b^2/R)^i*((i:ℝ)+1)^(2*p))*((64*b^2/R)^j*((j:ℝ)+1)^(2*p)) := by
  obtain ⟨C,hC,hbound⟩ := fixedNewtonBilinear_native_bound a b hab hb hb' p
  refine ⟨C,hC,fun T ε δ i j e f hε hδ => ?_⟩
  have h := hbound T ε δ i j e f hε hδ
  unfold fixedChartNewtonMoment
  rw [norm_mul,norm_inv,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hR,mul_inv_rev]
  calc
    _ ≤ (‖κ^(e.toNat+f.toNat)‖⁻¹*(R^(i+j))⁻¹)*
        (C*‖T‖*((64*b^2)^i*((i:ℝ)+1)^(2*p))*((64*b^2)^j*((j:ℝ)+1)^(2*p))) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by rw [pow_add,div_pow,div_pow]; field_simp; ring

/-- Both complete infinite arms of every parity pair are square summable
when the fixed-chart factor is smaller than the constant normalization. -/
theorem summable_sq_fixedChartNewtonMoment (R a b : ℝ) (κ : ℂ) (hab : a < b)
    (hb : 0 < b) (hb' : b ≤ 1/8) (hR : 0 < R) (hsmall : 64*b^2 < R)
    (p : ℕ) (T : HermiteScale (-(p:ℤ))) (ε δ : ℕ → ℝ)
    (hε : ∀ l, |ε (l+1)| ≤ b) (hδ : ∀ l, |δ (l+1)| ≤ b) (e f : Bool) :
    Summable (fun ij : ℕ×ℕ =>
      ‖fixedChartNewtonMoment R κ a b hab ε δ (hermiteScaleDistribution p T) ij.1 e ij.2 f‖^2) := by
  let q : ℝ := 64*b^2/R
  have hq : 0 < q := by dsimp [q]; positivity
  have hq1 : q < 1 := (div_lt_one hR).mpr hsmall
  have hq2 : q^2 < 1 := by nlinarith
  have hs : Summable (fun n : ℕ => (q^n*((n:ℝ)+1)^(2*p))^2) := by
    have hh := summable_shifted_polynomial_geometric (q^2) (by positivity) hq2 (4*p)
    have he : (fun n : ℕ => (q^n*((n:ℝ)+1)^(2*p))^2) =
        (fun n : ℕ => (q^2)^n*((n:ℝ)+1)^(4*p)) := by
      funext n
      simp only [mul_pow,←pow_mul]
      congr 2 <;> omega
    rwa [he]
  obtain ⟨C,hC,hbound⟩ := fixedChartNewtonMoment_bound R a b κ hab hb hb' hR p
  have hsprod : Summable (fun ij : ℕ×ℕ =>
      (q^ij.1*((ij.1:ℝ)+1)^(2*p))^2*(q^ij.2*((ij.2:ℝ)+1)^(2*p))^2) := by
    apply (summable_prod_of_nonneg (fun ij => mul_nonneg (sq_nonneg _) (sq_nonneg _))).mpr
    refine ⟨fun i => hs.mul_left ((q^i*((i:ℝ)+1)^(2*p))^2), ?_⟩
    simpa only [tsum_mul_left] using hs.mul_right (∑' n : ℕ, (q^n*((n:ℝ)+1)^(2*p))^2)
  have hh := hsprod.mul_left ((‖κ^(e.toNat+f.toNat)‖⁻¹*C*‖T‖)^2)
  apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) _ hh
  intro ij
  have he := pow_le_pow_left₀ (norm_nonneg _)
    (hbound T ε δ ij.1 ij.2 e f (fun l _ => hε l) (fun l _ => hδ l)) 2
  simpa only [q,mul_pow,mul_assoc] using he

/-- The literal four-parity full array is square summable with no quadrant truncation. -/
theorem summable_sq_fixedChartNewtonMatrix (R a b : ℝ) (κ : ℂ) (hab : a < b)
    (hb : 0 < b) (hb' : b ≤ 1/8) (hR : 0 < R) (hsmall : 64*b^2 < R)
    (p : ℕ) (T : HermiteScale (-(p:ℤ))) (ε δ : ℕ → ℝ)
    (hε : ∀ l, |ε (l+1)| ≤ b) (hδ : ∀ l, |δ (l+1)| ≤ b) :
    Summable (fun z : (ℕ×Bool)×(ℕ×Bool) =>
      ‖fixedChartNewtonMoment R κ a b hab ε δ (hermiteScaleDistribution p T)
        z.1.1 z.1.2 z.2.1 z.2.2‖^2) := by
  let E : (ℕ×Bool)×(ℕ×Bool) ≃ (Bool×Bool)×(ℕ×ℕ) :=
    { toFun := fun z => ((z.1.2,z.2.2),(z.1.1,z.2.1))
      invFun := fun z => ((z.2.1,z.1.1),(z.2.2,z.1.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h : Summable (fun z : (Bool×Bool)×(ℕ×ℕ) =>
      ‖fixedChartNewtonMoment R κ a b hab ε δ (hermiteScaleDistribution p T)
        z.2.1 z.1.1 z.2.2 z.1.2‖^2) := by
    apply (summable_prod_of_nonneg (fun _ => sq_nonneg _)).mpr
    exact ⟨fun ef => summable_sq_fixedChartNewtonMoment R a b κ hab hb hb' hR hsmall p T ε δ hε hδ ef.1 ef.2,
      summable_of_hasFiniteSupport (Set.toFinite _)⟩
  exact E.summable_iff.mpr h

end
end MeyerGeneralProblem.Adaptive
