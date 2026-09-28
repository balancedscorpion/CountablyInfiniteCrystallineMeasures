module

public import MeyerGeneralProblem.Cardinal.Adaptive.NativeTranslations

@[expose] public section

/-! Original Hermite bounds for arbitrary small physical bumps. -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section

private theorem large_dilation_coefficients (a : ℝ) (ha : 1 ≤ a) :
    ‖(a : ℂ)⁻¹^2‖ ≤ a^2 ∧
    ‖(4 * (Real.pi : ℂ))⁻¹ * ((a : ℂ)⁻¹^2 - (a : ℂ)^2)‖ ≤
      2 * a^2 * ‖(4 * (Real.pi : ℂ))⁻¹‖ ∧
    ‖(1 - (a : ℂ)⁻¹^2)/2‖ ≤ a^2 := by
  have hap : 0 < a := by linarith
  have hi : a⁻¹ ≤ 1 := by
    rw [inv_eq_one_div]
    exact (div_le_iff₀ hap).mpr (by linarith)
  have hi0 : 0 ≤ a⁻¹ := le_of_lt (inv_pos.mpr hap)
  have hisq : ‖(a : ℂ)⁻¹^2‖ ≤ 1 := by
    simp only [norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hap]
    nlinarith
  have hasq : 1 ≤ a^2 := by nlinarith
  have hsq : ‖(a : ℂ)^2‖ = a^2 := by
    simp only [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hap]
  refine ⟨hisq.trans hasq, ?_, ?_⟩
  · rw [norm_mul]
    have hs := norm_sub_le ((a : ℂ)⁻¹^2) ((a : ℂ)^2)
    rw [hsq] at hs
    have hle : ‖(a : ℂ)⁻¹^2 - (a : ℂ)^2‖ ≤ 2*a^2 := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hle (norm_nonneg ((4*(Real.pi:ℂ))⁻¹))]
  · rw [norm_div]
    norm_num only [Complex.norm_ofNat]
    have hh := norm_sub_le (1:ℂ) ((a:ℂ)⁻¹^2)
    rw [norm_one] at hh
    linarith

/-- Large actual dilations have degree twice the original Hermite order. -/
theorem exists_large_hermite_dilation_bound (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℝ) (ha : a ≠ 0), 1 ≤ a →
      ∀ f : SchwartzMap ℝ ℂ,
        ‖schwartzToHermiteScale m (combSchwartzDilation a ha f)‖ ≤
          C * a^(2*m) * ‖schwartzToHermiteScale m f‖ := by
  induction m with
  | zero =>
      refine ⟨1, by norm_num, ?_⟩
      intro a ha hab f
      have hap : 0 < a := by linarith
      have hi : |a⁻¹| ≤ 1 := by
        rw [abs_of_pos (inv_pos.mpr hap)]
        rw [inv_eq_one_div]
        apply (div_le_iff₀ hap).mpr
        linarith
      have he := schwartzToHermiteScale_zero_dilation_norm_sq a ha f
      have hh := mul_le_mul_of_nonneg_right hi (sq_nonneg ‖schwartzToHermiteScale 0 f‖)
      simp only [mul_zero, pow_zero, one_mul]
      nlinarith [norm_nonneg (schwartzToHermiteScale 0 (combSchwartzDilation a ha f)),
        norm_nonneg (schwartzToHermiteScale 0 f)]
  | succ m ih =>
      obtain ⟨C, hC, hbound⟩ := ih
      let B : ℝ := 1 + 2 * ‖(4 * (Real.pi : ℂ))⁻¹‖ * (36 * Real.pi * 3^m) + 1
      have hB : 0 < B := by dsimp [B]; positivity
      refine ⟨C * B, mul_pos hC hB, ?_⟩
      intro a ha hab f
      obtain ⟨hα, hβ, hγ⟩ := large_dilation_coefficients a hab
      let α : ℂ := (a:ℂ)⁻¹^2
      let β : ℂ := (4 * (Real.pi:ℂ))⁻¹ * ((a:ℂ)⁻¹^2 - (a:ℂ)^2)
      let γ : ℂ := (1 - (a:ℂ)⁻¹^2)/2
      let g := α • hermiteGraphOperator f +
        β • SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ f) + γ • f
      have hg : ‖schwartzToHermiteScale m g‖ ≤ B * a^2 * ‖schwartzToHermiteScale (m+1) f‖ := by
        have hD := schwartzToHermiteScale_secondDerivative_norm_bound m f
        have hmono := schwartzToHermiteScale_norm_mono m f
        have hA := mul_le_mul_of_nonneg_right hα (norm_nonneg (schwartzToHermiteScale (m+1) f))
        have hB' := mul_le_mul hβ hD (norm_nonneg _) (by positivity)
        have hG := mul_le_mul hγ hmono (norm_nonneg _) (by positivity)
        dsimp only [g]
        rw [map_add, map_add, map_smul, map_smul, map_smul, schwartzToHermiteScale_graph]
        have htri := (norm_add_le
          (α • schwartzToHermiteScale (m+1) f + β • schwartzToHermiteScale m
            (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ f)))
          (γ • schwartzToHermiteScale m f)).trans
          (add_le_add (norm_add_le _ _) le_rfl)
        simp only [norm_smul] at htri
        dsimp only [α, β, γ, B] at htri ⊢
        nlinarith
      calc
        ‖schwartzToHermiteScale (m+1) (combSchwartzDilation a ha f)‖ =
            ‖schwartzToHermiteScale m (hermiteGraphOperator (combSchwartzDilation a ha f))‖ := by
          rw [schwartzToHermiteScale_graph]
        _ = ‖schwartzToHermiteScale m (combSchwartzDilation a ha g)‖ := by
          rw [graph_combSchwartzDilation]
        _ ≤ C * a^(2*m) * ‖schwartzToHermiteScale m g‖ := hbound a ha hab g
        _ ≤ C * a^(2*m) * (B * a^2 * ‖schwartzToHermiteScale (m+1) f‖) :=
          mul_le_mul_of_nonneg_left hg (by positivity)
        _ = (C * B) * a^(2*(m+1)) * ‖schwartzToHermiteScale (m+1) f‖ := by
          rw [show 2*(m+1) = 2*m+2 by omega, pow_add]
          ring


/-- The actual physical bump, with width δ and center y. -/
def shrinkingBump (ψ : SchwartzMap ℝ ℂ) (y δ : ℝ) (hδ : 0 < δ) : SchwartzMap ℝ ℂ :=
  combSchwartzTranslation (-y) (combSchwartzDilation δ⁻¹ (inv_ne_zero hδ.ne') ψ)

theorem shrinkingBump_apply (ψ : SchwartzMap ℝ ℂ) (y δ : ℝ) (hδ : 0 < δ) (x : ℝ) :
    shrinkingBump ψ y δ hδ x = ψ ((x-y)/δ) := by
  simp only [shrinkingBump, combSchwartzTranslation_apply, combSchwartzDilation_apply]
  congr 1
  ring

/-- A bound uniform in the physical center, width, and Schwartz profile. -/
theorem exists_shrinkingBump_norm_bound (p : ℕ) (H : ℝ) (hH : 0 ≤ H) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ψ : SchwartzMap ℝ ℂ) (y δ : ℝ) (hδ : 0 < δ),
      |y| ≤ H → δ ≤ 1 →
      ‖schwartzToHermiteScale p (shrinkingBump ψ y δ hδ)‖ ≤
        C * (δ⁻¹)^(2*p) * ‖schwartzToHermiteScale p ψ‖ := by
  obtain ⟨D, hD, hd⟩ := exists_large_hermite_dilation_bound p
  obtain ⟨T, hT, ht⟩ := exists_hermite_translation_bound p
  refine ⟨T * (1+H)^(2*p) * D, by positivity, ?_⟩
  intro ψ y δ hδ hy hδ1
  have hi : 1 ≤ δ⁻¹ := by
    rw [inv_eq_one_div]
    exact (le_div_iff₀ hδ).mpr (by simpa using hδ1)
  have hh := ht (-y) (combSchwartzDilation δ⁻¹ (inv_ne_zero hδ.ne') ψ)
  rw [abs_neg] at hh
  have hpow : (1+|y|)^(2*p) ≤ (1+H)^(2*p) := by gcongr
  have ht' : T*(1+|y|)^(2*p) ≤ T*(1+H)^(2*p) :=
    mul_le_mul_of_nonneg_left hpow hT.le
  have hf := hd δ⁻¹ (inv_ne_zero hδ.ne') hi ψ
  calc
    ‖schwartzToHermiteScale p (shrinkingBump ψ y δ hδ)‖ ≤
      T*(1+|y|)^(2*p)*‖schwartzToHermiteScale p (combSchwartzDilation δ⁻¹ (inv_ne_zero hδ.ne') ψ)‖ := hh
    _ ≤ T*(1+H)^(2*p)*(D*(δ⁻¹)^(2*p)*‖schwartzToHermiteScale p ψ‖) :=
      mul_le_mul ht' hf (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- The source-budget exponent 2p+1, for each fixed physical profile. -/
theorem exists_fixed_shrinkingBump_norm_bound (p : ℕ) (ψ : SchwartzMap ℝ ℂ)
    (H : ℝ) (hH : 0 ≤ H) :
    ∃ C : ℝ, 0 < C ∧ ∀ (y δ : ℝ) (hδ : 0 < δ), |y| ≤ H → δ ≤ 1 →
      ‖schwartzToHermiteScale p (shrinkingBump ψ y δ hδ)‖ ≤
        C / δ^(2*p+1) := by
  obtain ⟨C, hC, hc⟩ := exists_shrinkingBump_norm_bound p H hH
  refine ⟨C*‖schwartzToHermiteScale p ψ‖+1, by positivity, ?_⟩
  intro y δ hδ hy hδ1
  have hi : 1 ≤ δ⁻¹ := by
    rw [inv_eq_one_div]
    exact (le_div_iff₀ hδ).mpr (by simpa using hδ1)
  have hp : (δ⁻¹)^(2*p) ≤ (δ⁻¹)^(2*p+1) := pow_le_pow_right₀ hi (by omega)
  have hh := hc ψ y δ hδ hy hδ1
  calc
    ‖schwartzToHermiteScale p (shrinkingBump ψ y δ hδ)‖ ≤
      C*(δ⁻¹)^(2*p)*‖schwartzToHermiteScale p ψ‖ := hh
    _ ≤ C*(δ⁻¹)^(2*p+1)*‖schwartzToHermiteScale p ψ‖ := by gcongr
    _ ≤ (C*‖schwartzToHermiteScale p ψ‖+1)*(δ⁻¹)^(2*p+1) := by
      nlinarith [pow_nonneg (inv_nonneg.mpr hδ.le) (2*p+1)]
    _ = _ := by rw [inv_pow, div_eq_mul_inv]

end
end MeyerGeneralProblem.Adaptive
