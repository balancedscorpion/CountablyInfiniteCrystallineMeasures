module

public import MeyerGeneralProblem.Cardinal.Adaptive.PhaseTranslationErrors
public import MeyerGeneralProblem.Cardinal.Adaptive.DistributionDifferences
public import Mathlib.Algebra.Order.ToIntervalMod
import all Mathlib.Algebra.Order.ToIntervalMod

@[expose] public section

/-! # Fixed-order leading-degree translation errors

The project's translation sends a test to f(h+x). Thus a translated monomial
uses (x-h)^r, and its leading normalization is (-h)^(-D). All constants below
are chosen before the test or source, with only finitely many fixed-order
test derivatives.
-/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open Set

/-- A compact multiplier has a native test bound with exactly 2q input derivatives. -/
theorem exists_piece_compact_native_bound (q : ℕ) (ζ : SchwartzMap ℝ ℂ)
    (H : ℝ) (hH : 0 ≤ H) :
    ∃ B : ℝ, 0 < B ∧ ∀ f : SchwartzMap ℝ ℂ,
      tsupport f ⊆ Icc (-H) H → ∀ A : ℝ, 0 ≤ A →
      (∀ r ≤ 2*q, ∀ x, ‖iteratedDeriv r (f : ℝ → ℂ) x‖ ≤ A) →
      ‖schwartzToHermiteScale q (SchwartzMap.smulLeftCLM ℂ ζ f)‖ ≤ B*A := by
  obtain ⟨B,hB,hbound⟩ := exists_compact_finite_regularity_native_bound_mul q H hH
  obtain ⟨C,hC,hpiece⟩ := exists_piece_finite_derivative_bound ζ (2*q)
  refine ⟨B*C,mul_pos hB hC,fun f hs A hA hf => ?_⟩
  have he : (SchwartzMap.smulLeftCLM ℂ ζ f : ℝ → ℂ) = (ζ : ℝ → ℂ) • (f : ℝ → ℂ) := by
    ext x
    exact SchwartzMap.smulLeftCLM_apply_apply ζ.hasTemperateGrowth f x
  have hvs : tsupport (SchwartzMap.smulLeftCLM ℂ ζ f) ⊆ Icc (-H) H := by
    rw [he]
    exact (tsupport_smul_subset_right (ζ : ℝ → ℂ) (f : ℝ → ℂ)).trans hs
  simpa only [mul_assoc] using hbound _ hvs (C*A) (mul_nonneg hC.le hA) (hpiece f A hA hf)

/-- On a fixed compact interval, coordinate multiplication costs no test derivatives. -/
theorem exists_compact_monomial_native_bound (q d : ℕ) (H : ℝ) (hH : 0 ≤ H) :
    ∃ B : ℝ, 0 < B ∧ ∀ f : SchwartzMap ℝ ℂ,
      tsupport f ⊆ Icc (-H) H → ∀ A : ℝ, 0 ≤ A →
      (∀ r ≤ 2*q, ∀ x, ‖iteratedDeriv r (f : ℝ → ℂ) x‖ ≤ A) →
      ‖schwartzToHermiteScale q (monomialTestCLM d f)‖ ≤ B*A := by
  let ζ := monomialTestCLM d (scaledCompactSchwartzCutoff ⌈H⌉₊)
  obtain ⟨B,hB,hbound⟩ := exists_piece_compact_native_bound q ζ H hH
  refine ⟨B,hB,fun f hs A hA hf => ?_⟩
  have he : SchwartzMap.smulLeftCLM ℂ ζ f = monomialTestCLM d f := by
    ext x
    rw [SchwartzMap.smulLeftCLM_apply_apply ζ.hasTemperateGrowth,smul_eq_mul]
    simp only [ζ,monomialTestCLM_apply]
    by_cases hx : x ∈ tsupport f
    · rw [scaledCompactSchwartzCutoff_eq_one _ ((abs_le.mpr (hs hx)).trans
        ((Nat.le_ceil H).trans (by linarith)))]
      ring
    · rw [image_eq_zero_of_notMem_tsupport hx,mul_zero,mul_zero]
  rw [← he]
  exact hbound f hs A hA hf

/-- Every nonleading normalized binomial coefficient decays at least as 1/h. -/
theorem normalized_binomial_coefficient_bound (D r j : ℕ) (hr : r ≤ D) (hj : j ≤ r)
    (hsmall : r < D ∨ 0 < j) (h : ℝ) (hh : 1 ≤ h) :
    ‖((-(h:ℂ))^D)⁻¹ * (r.choose j : ℂ) * (-(h:ℂ))^(r-j)‖ ≤ (r.choose j : ℝ)/h := by
  have hpos : 0 < h := lt_of_lt_of_le zero_lt_one hh
  have hexp : r-j+1 ≤ D := by omega
  have hp : h^(r-j)*h ≤ h^D := by
    rw [← pow_succ]
    exact pow_le_pow_right₀ hh hexp
  have hratio : h^(r-j)/h^D ≤ 1/h := by
    apply (div_le_div_iff₀ (pow_pos hpos D) hpos).mpr
    simpa only [one_mul] using hp
  simp only [norm_mul,norm_inv,norm_pow,norm_neg,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos hpos,Complex.norm_natCast]
  calc
    _ = (r.choose j : ℝ) * (h^(r-j)/h^D) := by ring
    _ ≤ (r.choose j : ℝ) * (1/h) := mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = _ := by ring

/-- The actual binomial expansion of the shifted monomial test. -/
theorem shiftedMonomialTest_eq_sum (r : ℕ) (h : ℝ) (f : SchwartzMap ℝ ℂ) :
    shiftedMonomialTest r h f = ∑ j ∈ Finset.range (r+1),
      ((r.choose j : ℂ)*(-(h:ℂ))^(r-j)) • monomialTestCLM j f := by
  ext x
  simp only [shiftedMonomialTest_apply,sum_apply,smul_apply,smul_eq_mul,monomialTestCLM_apply]
  rw [sub_eq_add_neg,add_pow,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The normalized coefficient after subtracting the unique leading constant term. -/
def leadingErrorCoefficient (D r : ℕ) (h : ℝ) (j : ℕ) : ℂ :=
  ((-(h:ℂ))^D)⁻¹ * (r.choose j : ℂ) * (-(h:ℂ))^(r-j) -
    if r = D ∧ j = 0 then 1 else 0

/-- Every coefficient in the genuine leading-error polynomial is O(1/h). -/
theorem leadingErrorCoefficient_norm_le (D r j : ℕ) (hr : r ≤ D) (hj : j ≤ r)
    (h : ℝ) (hh : 1 ≤ h) :
    ‖leadingErrorCoefficient D r h j‖ ≤ (r.choose j : ℝ)/h := by
  have hpos : 0 < h := lt_of_lt_of_le zero_lt_one hh
  have hne : (-(h:ℂ))^D ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr hpos.ne'))
  by_cases he : r = D ∧ j = 0
  · obtain ⟨rfl,rfl⟩ := he
    simp [leadingErrorCoefficient,hne,le_of_lt hpos]
  · simpa only [leadingErrorCoefficient,he,ite_false,sub_zero] using
      normalized_binomial_coefficient_bound D r j hr hj (by omega) h hh

/-- Exact signed normalization, including the degree-zero case and leading subtraction. -/
theorem normalized_shiftedMonomialTest_error_eq_sum (D r : ℕ) (h : ℝ)
    (f : SchwartzMap ℝ ℂ) :
    ((-(h:ℂ))^D)⁻¹ • shiftedMonomialTest r h f - (if r = D then f else 0) =
      ∑ j ∈ Finset.range (r+1), leadingErrorCoefficient D r h j • monomialTestCLM j f := by
  have hzero : monomialTestCLM 0 f = f := by ext x; simp [monomialTestCLM_apply]
  rw [shiftedMonomialTest_eq_sum,Finset.smul_sum]
  simp only [leadingErrorCoefficient,sub_smul,Finset.sum_sub_distrib,mul_smul]
  congr 1
  by_cases hr : r = D
  · simp [hr,hzero]
  · simp [hr]

/-- The exact normalized leading-degree error is O(1/h) in the original H_q norm,
uniform over every lower degree and all compact tests with 2q bounded derivatives. -/
theorem exists_normalized_leading_test_error_bound (q D : ℕ) (H : ℝ) (hH : 0 ≤ H) :
    ∃ B : ℝ, 0 < B ∧ ∀ r ≤ D, ∀ h : ℝ, 1 ≤ h → ∀ f : SchwartzMap ℝ ℂ,
      tsupport f ⊆ Icc (-H) H → ∀ A : ℝ, 0 ≤ A →
      (∀ n ≤ 2*q, ∀ x, ‖iteratedDeriv n (f : ℝ → ℂ) x‖ ≤ A) →
      ‖schwartzToHermiteScale q
        (((-(h:ℂ))^D)⁻¹ • shiftedMonomialTest r h f - (if r = D then f else 0))‖ ≤ B*A/h := by
  classical
  choose C hC hbound using fun j : Fin (D+1) => exists_compact_monomial_native_bound q j.val H hH
  let K : ℝ := 1 + ∑ j, C j
  have hK : 0 < K := by
    have hs : 0 ≤ ∑ j, C j := Finset.sum_nonneg (fun j _ => (hC j).le)
    dsimp [K]
    linarith
  let W (r : ℕ) : ℝ := ∑ j ∈ Finset.range (r+1), (r.choose j : ℝ)
  have hW r : 0 ≤ W r := by dsimp [W]; positivity
  let V : ℝ := 1 + ∑ r ∈ Finset.range (D+1), W r
  have hV : 0 < V := by dsimp [V]; positivity
  refine ⟨V*K,mul_pos hV hK,fun r hr h hh f hs A hA hf => ?_⟩
  have hpos : 0 < h := lt_of_lt_of_le zero_lt_one hh
  have hmono j (hj : j ≤ D) : ‖schwartzToHermiteScale q (monomialTestCLM j f)‖ ≤ K*A := by
    apply (hbound ⟨j,by omega⟩ f hs A hA hf).trans
    apply mul_le_mul_of_nonneg_right _ hA
    have hc := Finset.single_le_sum (fun z _ => (hC z).le) (Finset.mem_univ (⟨j,by omega⟩ : Fin (D+1)))
    dsimp [K]
    linarith
  rw [normalized_shiftedMonomialTest_error_eq_sum,map_sum]
  have hn := norm_sum_le (Finset.range (r+1)) (fun j =>
    schwartzToHermiteScale q (leadingErrorCoefficient D r h j • monomialTestCLM j f))
  apply hn.trans
  simp only [map_smul,norm_smul]
  calc
    _ ≤ ∑ j ∈ Finset.range (r+1), ((r.choose j : ℝ)/h)*(K*A) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjr : j ≤ r := by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hj
      exact mul_le_mul (leadingErrorCoefficient_norm_le D r j hr hjr h hh)
        (hmono j (hjr.trans hr)) (norm_nonneg _) (by positivity)
    _ = W r*(K*A)/h := by
      simp only [W,div_eq_mul_inv,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ (V*K)*A/h := by
      have hw : W r ≤ V := by
        have hw := Finset.single_le_sum (fun j _ => hW j) (Finset.mem_range.mpr (by omega : r < D+1))
        dsimp [V]
        linarith
      exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hw (mul_nonneg hK.le hA)) hpos.le).trans_eq (by ring)

/-- Antiperiodicity of a whole distribution gives antiperiodicity of its full real orbit. -/
theorem distribution_translation_orbit_antiperiodic (P : ℝ) (T : TemperedDistribution ℝ ℂ)
    (hT : combDistributionTranslation P T = -T) :
    Function.Antiperiodic (fun a : ℝ => combDistributionTranslation a T) P := by
  intro a
  ext f
  have h := congrArg (fun U : TemperedDistribution ℝ ℂ => U (combSchwartzTranslation a f)) hT
  simpa only [combDistributionTranslation_apply,neg_apply,difference_translation_add,add_comm P a] using h

/-- All translates of an actual antiperiodic coefficient have a representative in [0,4]. -/
theorem exists_bounded_antiperiodic_translate (P : ℝ) (hP : P ∈ Icc (1/2:ℝ) 2)
    (T : TemperedDistribution ℝ ℂ) (hT : combDistributionTranslation P T = -T) (h : ℝ) :
    ∃ a : ℝ, |a| ≤ 4 ∧ combDistributionTranslation h T = combDistributionTranslation a T := by
  have hpos : 0 < 2*P := by linarith [hP.1]
  let a := toIcoMod hpos 0 h
  have ha := toIcoMod_mem_Ico hpos 0 h
  have hper := (distribution_translation_orbit_antiperiodic P T hT).periodic_two_mul
  refine ⟨a,?_,?_⟩
  · change |toIcoMod hpos 0 h| ≤ 4
    rw [abs_of_nonneg ha.1]
    linarith [ha.2,hP.2]
  · change _ = (fun a => combDistributionTranslation a T) (h-toIcoDiv hpos 0 h • (2*P))
    simpa only [zsmul_eq_mul] using (hper.sub_int_mul_eq (toIcoDiv hpos 0 h)).symm

/-- Translation moves the polynomial onto its true shifted test with no sign convention hidden. -/
theorem translated_monomial_pairing (r : ℕ) (h : ℝ) (T : TemperedDistribution ℝ ℂ)
    (f : SchwartzMap ℝ ℂ) :
    combDistributionTranslation h (monomialDistribution r T) f =
      combDistributionTranslation h T (shiftedMonomialTest r h f) := by
  simp only [combDistributionTranslation_apply,monomialDistribution_apply]
  congr 1
  ext x
  simp only [combSchwartzTranslation_apply,monomialTestCLM_apply,shiftedMonomialTest_apply,
    Complex.ofReal_add,add_sub_cancel_left]

/-- Actual original-scale antiperiodic coefficients obey the uniform leading-degree
translation estimate, with no norm loss and only 2q test derivatives. -/
theorem exists_antiperiodic_leading_pairing_error_bound (q D : ℕ) (H : ℝ) (hH : 0 ≤ H) :
    ∃ B : ℝ, 0 < B ∧ ∀ r ≤ D, ∀ h : ℝ, 1 ≤ h → ∀ f : SchwartzMap ℝ ℂ,
      tsupport f ⊆ Icc (-H) H → ∀ A : ℝ, 0 ≤ A →
      (∀ n ≤ 2*q, ∀ x, ‖iteratedDeriv n (f : ℝ → ℂ) x‖ ≤ A) →
      ∀ P : ℝ, P ∈ Icc (1/2:ℝ) 2 → ∀ T : HermiteScale (-(q : ℤ)),
      combDistributionTranslation P (hermiteScaleDistribution q T) = -hermiteScaleDistribution q T →
      ‖((-(h:ℂ))^D)⁻¹ * combDistributionTranslation h (monomialDistribution r (hermiteScaleDistribution q T)) f -
        (if r = D then combDistributionTranslation h (hermiteScaleDistribution q T) f else 0)‖ ≤ B*A/h*‖T‖ := by
  obtain ⟨B,hB,hbound⟩ := exists_normalized_leading_test_error_bound q D H hH
  obtain ⟨C,hC,htranslate⟩ := exists_nativeTranslation_norm_bound q
  refine ⟨C*5^(2*q)*B,by positivity,fun r hr h hh f hs A hA hf P hP T hT => ?_⟩
  obtain ⟨a,ha,heq⟩ := exists_bounded_antiperiodic_translate P hP _ hT h
  let g := ((-(h:ℂ))^D)⁻¹ • shiftedMonomialTest r h f - (if r = D then f else 0)
  have hid : ((-(h:ℂ))^D)⁻¹ * combDistributionTranslation h (monomialDistribution r (hermiteScaleDistribution q T)) f -
      (if r = D then combDistributionTranslation h (hermiteScaleDistribution q T) f else 0) =
      combDistributionTranslation h (hermiteScaleDistribution q T) g := by
    simp only [g,map_sub,map_smul,smul_eq_mul,translated_monomial_pairing]
    split_ifs <;> simp only [map_zero]
  rw [hid,heq,← nativeTranslation_realizes,hermiteScaleDistribution_apply]
  have hn : ‖nativeTranslation q a T‖ ≤ C*5^(2*q)*‖T‖ := by
    apply ((nativeTranslation q a).le_opNorm T).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg T)
    apply (htranslate a).trans
    gcongr
    linarith
  have hg := hbound r hr h hh f hs A hA hf
  have hpos : 0 < h := lt_of_lt_of_le zero_lt_one hh
  exact (norm_hermiteScalePairing_le (q : ℤ) _ _).trans
    ((mul_le_mul hn hg (norm_nonneg _) (by positivity)).trans_eq (by ring))

/-- Actual partition pieces preserve the leading-degree estimate at the fixed input
regularity Kp, for every original output order q≤Qp. -/
theorem exists_partition_leading_pairing_error_bound (p q D N : ℕ) (hq : q ≤ liftOrder p)
    (ζ : Fin N → SchwartzMap ℝ ℂ) (H : ℝ) (hH : 0 ≤ H) :
    ∃ B : ℝ, 0 < B ∧ ∀ i r, r ≤ D → ∀ h : ℝ, 1 ≤ h → ∀ f : SchwartzMap ℝ ℂ,
      tsupport f ⊆ Icc (-H) H → ∀ A : ℝ, 0 ≤ A →
      (∀ n ≤ testOrder p, ∀ x, ‖iteratedDeriv n (f : ℝ → ℂ) x‖ ≤ A) →
      ∀ P : ℝ, P ∈ Icc (1/2:ℝ) 2 → ∀ T : HermiteScale (-(q : ℤ)),
      combDistributionTranslation P (hermiteScaleDistribution q T) = -hermiteScaleDistribution q T →
      let v := SchwartzMap.smulLeftCLM ℂ (ζ i) f
      ‖((-(h:ℂ))^D)⁻¹ * combDistributionTranslation h (monomialDistribution r (hermiteScaleDistribution q T)) v -
        (if r = D then combDistributionTranslation h (hermiteScaleDistribution q T) v else 0)‖ ≤ B*A/h*‖T‖ := by
  classical
  obtain ⟨B,hB,hbound⟩ := exists_antiperiodic_leading_pairing_error_bound q D H hH
  choose C hC hpiece using fun i => exists_piece_finite_derivative_bound (ζ i) (2*q)
  let K : ℝ := 1+∑ i, C i
  have hK : 0 < K := by
    have hn := Finset.sum_nonneg (fun i (_ : i ∈ (Finset.univ : Finset (Fin N))) => (hC i).le)
    dsimp [K]
    linarith
  refine ⟨B*K,mul_pos hB hK,fun i r hr h hh f hs A hA hf P hP T hT => ?_⟩
  have hvs : tsupport (SchwartzMap.smulLeftCLM ℂ (ζ i) f) ⊆ Icc (-H) H := by
    have he : (SchwartzMap.smulLeftCLM ℂ (ζ i) f : ℝ → ℂ) = (ζ i : ℝ → ℂ) • (f : ℝ → ℂ) := by
      ext x
      exact SchwartzMap.smulLeftCLM_apply_apply (ζ i).hasTemperateGrowth f x
    rw [he]
    exact (tsupport_smul_subset_right (ζ i : ℝ → ℂ) (f : ℝ → ℂ)).trans hs
  have horder : 2*q ≤ testOrder p := by unfold testOrder; omega
  have hderiv : ∀ n ≤ 2*q, ∀ x,
      ‖iteratedDeriv n (SchwartzMap.smulLeftCLM ℂ (ζ i) f : ℝ → ℂ) x‖ ≤ K*A := by
    intro n hn x
    apply (hpiece i f A hA (fun j hj => hf j (hj.trans horder)) n hn x).trans
    apply mul_le_mul_of_nonneg_right _ hA
    have hi := Finset.single_le_sum (fun j _ => (hC j).le) (Finset.mem_univ i)
    dsimp [K]
    linarith
  have he := hbound r hr h hh _ hvs (K*A) (mul_nonneg hK.le hA) hderiv P hP T hT
  simpa only [mul_assoc] using he

/-- The leading error summed over the actual finite partition, labels and polynomial
degrees is bounded uniformly for every later translation h_i≥H0. -/
theorem exists_partition_sum_leading_error_bound (p q D N L : ℕ) (hq : q ≤ liftOrder p)
    (ζ : Fin N → SchwartzMap ℝ ℂ) (H : ℝ) (hH : 0 ≤ H) :
    ∃ B : ℝ, 0 < B ∧ ∀ H₀ : ℝ, 1 ≤ H₀ → ∀ h : Fin N → ℝ, (∀ i, H₀ ≤ h i) →
      ∀ f : SchwartzMap ℝ ℂ, tsupport f ⊆ Icc (-H) H → ∀ A : ℝ, 0 ≤ A →
      (∀ n ≤ testOrder p, ∀ x, ‖iteratedDeriv n (f : ℝ → ℂ) x‖ ≤ A) →
      ∀ P : Fin L → ℝ, (∀ j, P j ∈ Icc (1/2:ℝ) 2) →
      ∀ T : Fin L → Fin (D+1) → HermiteScale (-(q : ℤ)),
      (∀ j r, combDistributionTranslation (P j) (hermiteScaleDistribution q (T j r)) =
        -hermiteScaleDistribution q (T j r)) →
      ‖∑ i, ∑ j, ∑ r : Fin (D+1),
        (((-(h i:ℂ))^D)⁻¹ * combDistributionTranslation (h i)
          (monomialDistribution r.val (hermiteScaleDistribution q (T j r))) (SchwartzMap.smulLeftCLM ℂ (ζ i) f) -
        (if r.val = D then combDistributionTranslation (h i) (hermiteScaleDistribution q (T j r))
          (SchwartzMap.smulLeftCLM ℂ (ζ i) f) else 0))‖ ≤ B*A/H₀*(∑ j, ∑ r, ‖T j r‖) := by
  obtain ⟨C,hC,hbound⟩ := exists_partition_leading_pairing_error_bound p q D N hq ζ H hH
  refine ⟨((N:ℝ)+1)*C,by positivity,fun H₀ hH₀ h hh f hs A hA hf P hP T hT => ?_⟩
  have hpos : 0 < H₀ := lt_of_lt_of_le zero_lt_one hH₀
  have hpoint i j (r : Fin (D+1)) :
      ‖((-(h i:ℂ))^D)⁻¹ * combDistributionTranslation (h i)
          (monomialDistribution r.val (hermiteScaleDistribution q (T j r))) (SchwartzMap.smulLeftCLM ℂ (ζ i) f) -
        (if r.val = D then combDistributionTranslation (h i) (hermiteScaleDistribution q (T j r))
          (SchwartzMap.smulLeftCLM ℂ (ζ i) f) else 0)‖ ≤ C*A/H₀*‖T j r‖ := by
    apply (hbound i r.val (by omega) (h i) (hH₀.trans (hh i)) f hs A hA hf (P j) (hP j) (T j r) (hT j r)).trans
    exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left (mul_nonneg hC.le hA) hpos (hh i)) (norm_nonneg _)
  calc
    _ ≤ ∑ i, ∑ j, ∑ r, C*A/H₀*‖T j r‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro i _
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro j _
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun r _ => hpoint i j r))
    _ = (N:ℝ)*(C*A/H₀)*(∑ j, ∑ r, ‖T j r‖) := by
      simp only [← Finset.mul_sum,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      ring
    _ ≤ (((N:ℝ)+1)*C)*A/H₀*(∑ j, ∑ r, ‖T j r‖) := by
      have hn : 0 ≤ ∑ j, ∑ r, ‖T j r‖ := Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _))
      have hp : 0 ≤ C*A/H₀*(∑ j, ∑ r, ‖T j r‖) := by positivity
      calc
        _ = (N:ℝ)*(C*A/H₀*(∑ j, ∑ r, ‖T j r‖)) := by ring
        _ ≤ ((N:ℝ)+1)*(C*A/H₀*(∑ j, ∑ r, ‖T j r‖)) := mul_le_mul_of_nonneg_right (by linarith) hp
        _ = _ := by ring

/-- The integer period in a physical torus approximation cancels on the whole
antiperiodic source, including negative integers. -/
theorem antiperiodic_translation_sub_integer_period (P : ℝ) (T : TemperedDistribution ℝ ℂ)
    (hT : combDistributionTranslation P T = -T) (h : ℝ) (n : ℤ) :
    combDistributionTranslation (h-(n:ℝ)*(2*P)) T = combDistributionTranslation h T :=
  (distribution_translation_orbit_antiperiodic P T hT).periodic_two_mul.sub_int_mul_eq n

/-- The actual normalized finite polynomial pairing is exactly the sum of the
checked coefficient errors, with its unique top coefficient retained. -/
theorem normalized_polynomial_pairing_error_eq_sum (D : ℕ) (h : ℝ)
    (T : Fin (D+1) → TemperedDistribution ℝ ℂ) (f : SchwartzMap ℝ ℂ) :
    ((-(h:ℂ))^D)⁻¹ * combDistributionTranslation h (∑ r, monomialDistribution r.val (T r)) f -
      combDistributionTranslation h (T ⟨D,Nat.lt_succ_self D⟩) f =
      ∑ r, (((-(h:ℂ))^D)⁻¹ * combDistributionTranslation h (monomialDistribution r.val (T r)) f -
        (if r.val = D then combDistributionTranslation h (T r) f else 0)) := by
  simp only [map_sum,sum_apply,Finset.mul_sum,Finset.sum_sub_distrib]
  congr 1
  symm
  rw [Finset.sum_eq_single (⟨D,Nat.lt_succ_self D⟩ : Fin (D+1))]
  · simp only [ite_true]
  · intro r _ hr
    have hval : r.val ≠ D := fun he => hr (Fin.ext he)
    simp only [hval,ite_false]
  · intro hn
    exact (hn (Finset.mem_univ _)).elim

end
end MeyerGeneralProblem.Adaptive
