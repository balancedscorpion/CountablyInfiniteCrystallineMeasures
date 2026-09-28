module

public import MeyerGeneralProblem.Cardinal.Adaptive.StageMultiplierBounds
public import MeyerGeneralProblem.Cardinal.Adaptive.ShrinkingBumpBounds

@[expose] public section

/-! # Uniform spatial cutoff bounds for actual Schwartz families -/

namespace MeyerGeneralProblem.Adaptive
noncomputable section
open Filter
open scoped BigOperators Topology ContDiff

/-- A family bounded in each of the actual Schwartz seminorms. -/
def SchwartzFamilyBounded {ι : Type*} (f : ι → SchwartzMap ℝ ℂ) : Prop :=
  ∀ k n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ i, SchwartzMap.seminorm ℂ k n (f i) ≤ C

/-- Every continuous seminorm is uniformly bounded on a Schwartz-bounded family. -/
theorem SchwartzFamilyBounded.continuous_seminorm {ι : Type*} {f : ι → SchwartzMap ℝ ℂ}
    (hf : SchwartzFamilyBounded f) (q : Seminorm ℂ (SchwartzMap ℝ ℂ)) (hq : Continuous q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i, q (f i) ≤ C := by
  classical
  choose B hB hb using hf
  obtain ⟨s,C,hC,hbound⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ ℝ ℂ) q hq
  let D : ℝ := ∑ a ∈ s, B a.1 a.2
  have hD : 0 ≤ D := Finset.sum_nonneg (fun a _ => hB a.1 a.2)
  refine ⟨C*D,by positivity,fun i => (hbound (f i)).trans ?_⟩
  change (C:ℝ)*s.sup (schwartzSeminormFamily ℂ ℝ ℂ) (f i) ≤ _
  apply mul_le_mul_of_nonneg_left _ C.coe_nonneg
  apply Seminorm.finset_sup_apply_le hD
  intro a ha
  exact (hb a.1 a.2 i).trans (Finset.single_le_sum (fun a _ => hB a.1 a.2) ha)

/-- Continuous linear Schwartz operators preserve the actual bounded-family property. -/
theorem SchwartzFamilyBounded.map {ι : Type*} {f : ι → SchwartzMap ℝ ℂ}
    (hf : SchwartzFamilyBounded f) (A : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ) :
    SchwartzFamilyBounded (fun i => A (f i)) := by
  intro k n
  apply hf.continuous_seminorm ((SchwartzMap.seminorm ℂ k n).comp A.toLinearMap)
  change Continuous (fun u : SchwartzMap ℝ ℂ => SchwartzMap.seminorm ℂ k n (A u))
  exact ((schwartz_withSeminorms ℂ ℝ ℂ).continuous_seminorm (k,n)).comp A.continuous

/-- Compact center ranges give a bounded family of all translates of a fixed test. -/
theorem schwartzFamilyBounded_translations (f : SchwartzMap ℝ ℂ) (H : ℝ) (hH : 0 ≤ H) :
    SchwartzFamilyBounded (fun a : {a : ℝ // |a| ≤ H} => combSchwartzTranslation a.val f) := by
  intro k n
  let C : ℝ := ∑ l ∈ Finset.range (k+1),
    (k.choose l:ℝ)*H^(k-l)*SchwartzMap.seminorm ℂ l n f
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C,hC,fun a => SchwartzMap.seminorm_le_bound' ℂ k n _ hC ?_⟩
  intro x
  have he : (combSchwartzTranslation a.val f : ℝ → ℂ) = fun y => f (y+a.val) := by
    ext y; simp only [combSchwartzTranslation_apply]; congr 1; ring
  rw [he, iteratedDeriv_comp_add_const]
  have hx : |x| ≤ |x+a.val|+H := by
    have h := abs_add_le (x+a.val) (-a.val)
    rw [add_neg_cancel_right, abs_neg] at h
    linarith [a.property]
  calc
    _ ≤ (|x+a.val|+H)^k * ‖iteratedDeriv n (f : ℝ → ℂ) (x+a.val)‖ := by gcongr
    _ = ∑ l ∈ Finset.range (k+1), (k.choose l:ℝ)*H^(k-l)*
        (|x+a.val|^l * ‖iteratedDeriv n (f : ℝ → ℂ) (x+a.val)‖) := by
      rw [add_pow, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro l hl
      ring
    _ ≤ C := by
      apply Finset.sum_le_sum
      intro l hl
      exact mul_le_mul_of_nonneg_left (SchwartzMap.le_seminorm' ℂ l n f (x+a.val)) (by positivity)

private theorem family_cutoff_seminorm_bound {ι : Type*} {f : ι → SchwartzMap ℝ ℂ}
    (hf : SchwartzFamilyBounded f) (k n : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ N i,
      SchwartzMap.seminorm ℂ k n (compactSchwartzApproximation N (f i)-f i) ≤
        compactSchwartzCutoffScale N * B := by
  choose C hC hb using hf
  let B := ∑ r ∈ Finset.range (n+1), (n.choose r:ℝ)*
    if r=0 then 2*C (k+1) n else SchwartzMap.seminorm ℂ 0 r compactSchwartzCutoff*C k (n-r)
  have hB : 0 ≤ B := by
    apply Finset.sum_nonneg
    intro r hr
    apply mul_nonneg (by positivity)
    split_ifs
    · exact mul_nonneg (by norm_num) (hC (k+1) n)
    · exact mul_nonneg (apply_nonneg _ _) (hC k (n-r))
  refine ⟨B,hB,fun N i => (compactSchwartzApproximation_seminorm_le N k n (f i)).trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ (compactSchwartzCutoffScale_pos N).le
  unfold compactSchwartzApproximationBound
  apply Finset.sum_le_sum
  intro r hr
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  split_ifs <;> gcongr
  · exact hb (k+1) n i
  · exact hb k (n-r) i

/-- One constant bounds the original native cutoff error for a whole bounded
Schwartz family. No member-dependent truncation or regularity is used. -/
theorem SchwartzFamilyBounded.native_cutoff_bound {ι : Type*} {f : ι → SchwartzMap ℝ ℂ}
    (hf : SchwartzFamilyBounded f) (p : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ N i,
      ‖schwartzToHermiteScale p (f i-compactSchwartzApproximation N (f i))‖ ≤
        compactSchwartzCutoffScale N * B := by
  classical
  let q : Seminorm ℂ (SchwartzMap ℝ ℂ) :=
    (normSeminorm ℂ (HermiteScale (p:ℤ))).comp (schwartzToHermiteScale p).toLinearMap
  have hq : Continuous q := continuous_norm.comp (schwartzToHermiteScale p).continuous
  obtain ⟨s,C,hC,hbound⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ ℝ ℂ) q hq
  choose D hD hd using family_cutoff_seminorm_bound hf
  let E : ℝ := ∑ a ∈ s, D a.1 a.2
  have hE : 0 ≤ E := Finset.sum_nonneg (fun a _ => hD a.1 a.2)
  refine ⟨C*E,by positivity,fun N i => ?_⟩
  have he := hbound (compactSchwartzApproximation N (f i)-f i)
  change ‖schwartzToHermiteScale p (compactSchwartzApproximation N (f i)-f i)‖ ≤
    (C:ℝ)*s.sup (schwartzSeminormFamily ℂ ℝ ℂ) (compactSchwartzApproximation N (f i)-f i) at he
  rw [map_sub, norm_sub_rev, ← map_sub] at he
  apply he.trans
  have hs : s.sup (schwartzSeminormFamily ℂ ℝ ℂ) (compactSchwartzApproximation N (f i)-f i) ≤
      compactSchwartzCutoffScale N * E := by
    apply Seminorm.finset_sup_apply_le (mul_nonneg (compactSchwartzCutoffScale_pos N).le hE)
    intro a ha
    exact (hd a.1 a.2 N i).trans (mul_le_mul_of_nonneg_left
      (Finset.single_le_sum (fun a _ => hD a.1 a.2) ha) (compactSchwartzCutoffScale_pos N).le)
  exact (mul_le_mul_of_nonneg_left hs C.coe_nonneg).trans_eq (by ring)

/-- Fixed positive width and bounded centers give an actual bounded bump family. -/
theorem schwartzFamilyBounded_shrinkingBumps (ψ : SchwartzMap ℝ ℂ) (H δ : ℝ)
    (hH : 0 ≤ H) (hδ : 0 < δ) :
    SchwartzFamilyBounded (fun y : {y : ℝ // |y| ≤ H} => shrinkingBump ψ y.val δ hδ) := by
  intro k n
  obtain ⟨C,hC,hb⟩ := schwartzFamilyBounded_translations
    (combSchwartzDilation δ⁻¹ (inv_ne_zero hδ.ne') ψ) H hH k n
  exact ⟨C,hC,fun y => hb ⟨-y.val,by simpa only [abs_neg] using y.property⟩⟩

/-- Both actual Fourier signs preserve boundedness of the complete bump family. -/
theorem schwartzFamilyBounded_fourier_bumps (ψ : SchwartzMap ℝ ℂ) (H δ : ℝ)
    (hH : 0 ≤ H) (hδ : 0 < δ) :
    SchwartzFamilyBounded (fun b : Bool × {y : ℝ // |y| ≤ H} =>
      if b.1 then (FourierTransform.fourierInvCLM ℂ (SchwartzMap ℝ ℂ))
        (shrinkingBump ψ b.2.val δ hδ)
      else (FourierTransform.fourierCLM ℂ (SchwartzMap ℝ ℂ))
        (shrinkingBump ψ b.2.val δ hδ)) := by
  have hf := schwartzFamilyBounded_shrinkingBumps ψ H δ hH hδ
  have hp := hf.map (FourierTransform.fourierCLM ℂ (SchwartzMap ℝ ℂ))
  have hn := hf.map (FourierTransform.fourierInvCLM ℂ (SchwartzMap ℝ ℂ))
  intro k n
  obtain ⟨A,hA,hAb⟩ := hp k n
  obtain ⟨B,hB,hBb⟩ := hn k n
  refine ⟨A+B,add_nonneg hA hB,?_⟩
  rintro ⟨b,y⟩
  cases b
  · simpa only [Bool.false_eq_true,ite_false] using (hAb y).trans (by linarith : A ≤ A+B)
  · simpa only [ite_true] using (hBb y).trans (by linarith : B ≤ A+B)

/-- Uniform spatial cutoff budget for a bounded Schwartz family and every
compact scale tuple of a fixed finite periodic product. -/
theorem SchwartzFamilyBounded.periodic_product_spatial_tail {ι : Type*}
    {f : ι → SchwartzMap ℝ ℂ} (hf : SchwartzFamilyBounded f) (q p : ℕ)
    (g : Fin q → ℝ → ℂ) (hg : ∀ j, ContDiff ℝ ∞ (g j))
    (hp : ∀ j, Function.Periodic (g j) 1) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ i, ∀ (s : Fin q → ℝ), (∀ j, |s j| ≤ 2) →
      ‖schwartzToHermiteScale p (SchwartzMap.smulLeftCLM ℂ (fun x => ∏ j, g j (s j*x))
        (f i-compactSchwartzApproximation N (f i)))‖ < ε := by
  obtain ⟨B,hB,hbound⟩ := exists_finite_periodic_product_multiplier_bound q p g hg hp
  obtain ⟨C,hC,hcut⟩ := hf.native_cutoff_bound p
  have ht : Tendsto (fun N => compactSchwartzCutoffScale N*(B*C)) atTop (nhds 0) := by
    simpa only [zero_mul] using compactSchwartzCutoffScale_tendsto.mul_const (B*C)
  filter_upwards [ht.eventually (eventually_lt_nhds hε)] with N hN
  intro i s hs
  apply (hbound s hs _).trans_lt
  calc
    _ ≤ B*(compactSchwartzCutoffScale N*C) := mul_le_mul_of_nonneg_left (hcut N i) hB.le
    _ = compactSchwartzCutoffScale N*(B*C) := by ring
    _ < ε := hN

/-- Budget A for every original order up to M and both Fourier signs, with
one cutoff selected before all catalogue centers and all compact scale tuples. -/
theorem exists_catalogue_spatial_budget (M q : ℕ) (g : Fin q → ℝ → ℂ)
    (hg : ∀ j, ContDiff ℝ ∞ (g j)) (hp : ∀ j, Function.Periodic (g j) 1)
    (ψ : SchwartzMap ℝ ℂ) (H δ ε : ℝ) (hH : 0 ≤ H) (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p ≤ M, ∀ inverse : Bool,
      ∀ (y : ℝ), |y| ≤ H → ∀ (s : Fin q → ℝ), (∀ j, |s j| ≤ 2) →
      let f := if inverse then (FourierTransform.fourierInvCLM ℂ (SchwartzMap ℝ ℂ))
          (shrinkingBump ψ y δ hδ)
        else (FourierTransform.fourierCLM ℂ (SchwartzMap ℝ ℂ)) (shrinkingBump ψ y δ hδ)
      ‖schwartzToHermiteScale p (SchwartzMap.smulLeftCLM ℂ (fun x => ∏ j, g j (s j*x))
        (f-compactSchwartzApproximation N f))‖ < ε := by
  have hf := schwartzFamilyBounded_fourier_bumps ψ H δ hH hδ
  have h := eventually_all.mpr (fun p : Fin (M+1) =>
    hf.periodic_product_spatial_tail q p g hg hp ε hε)
  obtain ⟨N₀,hN⟩ := eventually_atTop.mp h
  refine ⟨N₀,fun N hNN p hp inverse y hy s hs => ?_⟩
  exact hN N hNN ⟨p,by omega⟩ (inverse,⟨y,hy⟩) s hs

/-- The cutoff error vanishes on the whole interior interval. -/
theorem schwartzCutoffError_eq_zero (N : ℕ) (f : SchwartzMap ℝ ℂ) (x : ℝ)
    (hx : |x| ≤ (N:ℝ)+1) : (f-compactSchwartzApproximation N f) x = 0 := by
  simp only [sub_apply, compactSchwartzApproximation_apply,
    scaledCompactSchwartzCutoff_eq_one N hx, one_mul, sub_self]

/-- Outside twice the cutoff radius, the error is the original test exactly.
Thus a future carrier outside a chosen gap sees this same test. -/
theorem schwartzCutoffError_eq_self (N : ℕ) (f : SchwartzMap ℝ ℂ) (x : ℝ)
    (hx : 2*((N:ℝ)+1) ≤ |x|) : (f-compactSchwartzApproximation N f) x = f x := by
  have hz : scaledCompactSchwartzCutoff N x = 0 := by
    rw [scaledCompactSchwartzCutoff_apply, compactSchwartzCutoff_apply]
    have h := compactSchwartzCutoffBump.zero_of_le_dist (x := compactSchwartzCutoffScale N*x)
    have hd : compactSchwartzCutoffBump.rOut ≤ dist (compactSchwartzCutoffScale N*x) 0 := by
      simp only [compactSchwartzCutoffBump, Real.dist_eq, sub_zero, abs_mul,
        abs_of_pos (compactSchwartzCutoffScale_pos N)]
      change 2 ≤ ((N:ℝ)+1)⁻¹*|x|
      rw [← div_eq_inv_mul]
      exact (le_div_iff₀ (by positivity : (0:ℝ) < (N:ℝ)+1)).mpr hx
    simp only [h hd, Complex.ofReal_zero]
  simp only [sub_apply, compactSchwartzApproximation_apply, hz, zero_mul, sub_zero]

end
end MeyerGeneralProblem.Adaptive
