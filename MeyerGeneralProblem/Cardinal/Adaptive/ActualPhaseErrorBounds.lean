module

public import MeyerGeneralProblem.Cardinal.Adaptive.ActualPhaseWitnesses

@[expose] public section

/-! # The already paid stage budgets on actual coefficient families -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open Set
open scoped FourierTransform

/-- A uniform original coefficient norm pays the exact finite prefix count. -/
theorem prefix_coefficient_norm_sum_bound (M p D : ℕ) (hp : p ≤ M) (hD : D ≤ 12*p)
    (T : (Fin M × ReciprocalSign) → Fin (D+1) → HermiteScale (-((liftOrder p):ℤ)))
    (B : ℝ) (hB : 0 ≤ B) (hT : ∀ b r, ‖T b r‖ ≤ B) :
    (∑ b, ∑ r, ‖T b r‖) ≤ (stageCoefficientCount M:ℝ)*B := by
  have hc : Fintype.card (Fin M × ReciprocalSign) = 2*M := by
    rw [Fintype.card_prod,Fintype.card_fin]
    have h : Fintype.card ReciprocalSign = 2 := rfl
    rw [h,Nat.mul_comm]
  calc
    _ ≤ ∑ _b : Fin M × ReciprocalSign, ∑ _r : Fin (D+1), B :=
      Finset.sum_le_sum (fun b _ => Finset.sum_le_sum (fun r _ => hT b r))
    _ = ((2*M*(D+1):ℕ):ℝ)*B := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,hc,nsmul_eq_mul,Nat.cast_mul,Nat.cast_add,Nat.cast_one]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast stageCoefficientCount_bound M p D hp hD) hB

/-- The top coefficient alone obeys the same positive count budget. -/
theorem prefix_single_norm_sum_bound (M p : ℕ) (hp : p ≤ M)
    (T : (Fin M × ReciprocalSign) → HermiteScale (-((liftOrder p):ℤ)))
    (B : ℝ) (hB : 0 ≤ B) (hT : ∀ b, ‖T b‖ ≤ B) :
    (∑ b, ‖T b‖) ≤ (stageCoefficientCount M:ℝ)*B := by
  have h := prefix_coefficient_norm_sum_bound M p 0 hp (by omega) (fun b _ => T b) B hB (fun b _ => hT b)
  simpa using h

/-- The actual H0 choice pays the full leading-error sum uniformly over every
source family of the prescribed fixed native order. -/
theorem actualStage_leading_error_bound (ψ : SchwartzMap ℝ ℂ) (n p D : ℕ)
    (hp : p ≤ n+1) (hD : D ≤ 12*p) (h : Fin (actualStage ψ n).partitionSize → ℝ)
    (hh : ∀ i, (actualStage ψ n).translationStart ≤ h i)
    (f : SchwartzMap ℝ ℂ) (hf : tsupport f ⊆ Icc (-(n+1:ℝ)) (n+1:ℝ))
    (hfA : ∀ r ≤ testOrder p, ∀ x, ‖iteratedDeriv r (f : ℝ → ℂ) x‖ ≤ 1)
    (P : (Fin (n+1) × ReciprocalSign) → ℝ) (hP : ∀ b, P b ∈ Icc (1/2:ℝ) 2)
    (T : (Fin (n+1) × ReciprocalSign) → Fin (D+1) → HermiteScale (-((liftOrder p):ℤ)))
    (hT : ∀ b r, combDistributionTranslation (P b) (hermiteScaleDistribution (liftOrder p) (T b r)) =
      -hermiteScaleDistribution (liftOrder p) (T b r))
    (B : ℝ) (hB : 0 ≤ B) (hnorm : ∀ b r, ‖T b r‖ ≤ B) :
    ‖∑ i, ∑ b, ∑ r : Fin (D+1),
      (((-(h i:ℂ))^D)⁻¹ * combDistributionTranslation (h i)
        (monomialDistribution r.val (hermiteScaleDistribution (liftOrder p) (T b r)))
          (SchwartzMap.smulLeftCLM ℂ ((actualStage ψ n).partition i) f) -
      (if r.val = D then combDistributionTranslation (h i) (hermiteScaleDistribution (liftOrder p) (T b r))
        (SchwartzMap.smulLeftCLM ℂ ((actualStage ψ n).partition i) f) else 0))‖ ≤
      (2:ℝ)^(-((n+1:ℕ):ℤ))*B := by
  let C := actualStage ψ n
  have hstart : 1 ≤ C.translationStart := by
    have h := (actualStage_laws ψ n).start
    dsimp [C] at *
    simp only [Nat.cast_add,Nat.cast_one] at h
    linarith [Nat.cast_nonneg (α:=ℝ) n]
  have hbound := stageLeadingErrorConstant_prefix p D C.partitionSize (n+1) C.partition
    (n+1) (by positivity) C.translationStart hstart h hh f hf 1 (by norm_num) hfA P hP T hT
  simp only [mul_one] at hbound
  have hpaid := (actualStage_laws ψ n).leading p hp D hD
  simp only [PNat.mk_coe,Nat.cast_add,Nat.cast_one] at hpaid
  have hcount : (0:ℝ) < stageCoefficientCount (n+1) := by unfold stageCoefficientCount; positivity
  have hsum := prefix_coefficient_norm_sum_bound (n+1) p D hp hD T B hB hnorm
  apply hbound.trans
  calc
    _ ≤ ((2:ℝ)^(-((n+1:ℕ):ℤ))/(stageCoefficientCount (n+1):ℝ))*
        ((stageCoefficientCount (n+1):ℝ)*B) :=
      mul_le_mul hpaid hsum (Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _)))
        (by positivity)
    _ = (2:ℝ)^(-((n+1:ℕ):ℤ))*B := by rw [← mul_assoc,div_mul_cancel₀ _ hcount.ne']

/-- The actual eta choice pays the phase error for arbitrary bounded desired and
realized representatives, with no dependence of the selected constant on sources. -/
theorem actualStage_phase_error_bound (ψ : SchwartzMap ℝ ℂ) (n p : ℕ) (hp : p ≤ n+1)
    (f : SchwartzMap ℝ ℂ) (hf : tsupport f ⊆ Icc (-(n+1:ℝ)) (n+1:ℝ))
    (hfA : ∀ r ≤ testOrder p, ∀ x, ‖iteratedDeriv r (f : ℝ → ℂ) x‖ ≤ 1)
    (a b : Fin (actualStage ψ n).partitionSize → (Fin (n+1) × ReciprocalSign) → ℝ)
    (ha : ∀ i j, |a i j| ≤ (n+1:ℝ)+4) (hb : ∀ i j, |b i j| ≤ (n+1:ℝ)+4)
    (hab : ∀ i j, |a i j-b i j| ≤ (actualStage ψ n).phaseTolerance)
    (T : (Fin (n+1) × ReciprocalSign) → HermiteScale (-((liftOrder p):ℤ)))
    (B : ℝ) (hB : 0 ≤ B) (hnorm : ∀ j, ‖T j‖ ≤ B) :
    ‖∑ i, ∑ j,
      (combDistributionTranslation (a i j) (hermiteScaleDistribution (liftOrder p) (T j))
        (SchwartzMap.smulLeftCLM ℂ ((actualStage ψ n).partition i) f) -
      combDistributionTranslation (b i j) (hermiteScaleDistribution (liftOrder p) (T j))
        (SchwartzMap.smulLeftCLM ℂ ((actualStage ψ n).partition i) f))‖ ≤
      (2:ℝ)^(-((n+1:ℕ):ℤ))*B := by
  let C := actualStage ψ n
  have hbound := stagePhaseErrorConstant_prefix p C.partitionSize (n+1) C.partition
    (n+1) ((n+1:ℝ)+4) (by positivity) (by positivity) f hf 1 (by norm_num) hfA
    C.phaseTolerance C.phaseTolerance_pos.le a b ha hb hab T
  simp only [mul_one] at hbound
  have hpaid := (actualStage_laws ψ n).phase p hp
  simp only [PNat.mk_coe,Nat.cast_add,Nat.cast_one] at hpaid
  have hcount : (0:ℝ) < stageCoefficientCount (n+1) := by unfold stageCoefficientCount; positivity
  have hsum := prefix_single_norm_sum_bound (n+1) p hp T B hB hnorm
  apply hbound.trans
  calc
    _ ≤ ((2:ℝ)^(-((n+1:ℕ):ℤ))/(stageCoefficientCount (n+1):ℝ))*
        ((stageCoefficientCount (n+1):ℝ)*B) :=
      mul_le_mul hpaid hsum (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (by positivity)
    _ = (2:ℝ)^(-((n+1:ℕ):ℤ))*B := by rw [← mul_assoc,div_mul_cancel₀ _ hcount.ne']

/-- Literal long net translations obey the paid phase budget after their exact
integer-period reduction; compact phase representatives have size at most M+3. -/
theorem actualStage_net_phase_error_bound (ψ : SchwartzMap ℝ ℂ) (s : ℕ+ → ℝ)
    (hs : ActualGoodScale ψ s) (n p : ℕ) (hp : p ≤ n+1)
    (target : Fin (n+1) × ReciprocalSign) (flip : Bool)
    (f : SchwartzMap ℝ ℂ) (hf : tsupport f ⊆ Icc (-(n+1:ℝ)) (n+1:ℝ))
    (hfA : ∀ r ≤ testOrder p, ∀ x, ‖iteratedDeriv r (f : ℝ → ℂ) x‖ ≤ 1)
    (c h : Fin (actualStage ψ n).partitionSize → ℝ)
    (hc : ∀ i, |c i| ≤ (n+1:ℝ))
    (z : Fin (actualStage ψ n).partitionSize → (Fin (n+1) × ReciprocalSign) → ℤ)
    (happrox : ∀ i b, |h i-pieceTargetPhase s target (c i) flip b-
      (z i b:ℝ)*(2/labelScale s (prefixScaleIndex b.1,b.2))| < (actualStage ψ n).phaseTolerance)
    (T : (Fin (n+1) × ReciprocalSign) → HermiteScale (-((liftOrder p):ℤ)))
    (hT : ∀ b, combDistributionTranslation (labelScale s (prefixScaleIndex b.1,b.2))⁻¹
      (hermiteScaleDistribution (liftOrder p) (T b)) = -hermiteScaleDistribution (liftOrder p) (T b))
    (B : ℝ) (hB : 0 ≤ B) (hnorm : ∀ b, ‖T b‖ ≤ B) :
    ‖∑ i, ∑ b,
      (combDistributionTranslation (h i) (hermiteScaleDistribution (liftOrder p) (T b))
        (SchwartzMap.smulLeftCLM ℂ ((actualStage ψ n).partition i) f) -
      combDistributionTranslation (pieceTargetPhase s target (c i) flip b)
        (hermiteScaleDistribution (liftOrder p) (T b))
        (SchwartzMap.smulLeftCLM ℂ ((actualStage ψ n).partition i) f))‖ ≤
      (2:ℝ)^(-((n+1:ℕ):ℤ))*B := by
  let a (i : Fin (actualStage ψ n).partitionSize) (b : Fin (n+1) × ReciprocalSign) :=
    h i-(z i b:ℝ)*(2/labelScale s (prefixScaleIndex b.1,b.2))
  have hdesired i b := pieceTargetPhase_abs_le s hs.1.1 target (c i) (n+1) (by positivity) (hc i) flip b
  have hrep (i : Fin (actualStage ψ n).partitionSize) (b : Fin (n+1) × ReciprocalSign) := physical_phase_representative s (prefixScaleIndex b.1,b.2)
    (hermiteScaleDistribution (liftOrder p) (T b)) (hT b) (h i)
    (pieceTargetPhase s target (c i) flip b) (actualStage ψ n).phaseTolerance ((n+1:ℝ)+2)
    (z i b) (hdesired i b) (happrox i b)
  have heta : (actualStage ψ n).phaseTolerance ≤ 1 := by
    have he := (actualStage_laws ψ n).phase_stage
    have hM : (1:ℝ) ≤ n+1 := by linarith [Nat.cast_nonneg (α:=ℝ) n]
    have hd : 1/(n+1:ℝ) ≤ 1 := by apply (div_le_one (by positivity)).mpr; exact hM
    simpa only [PNat.mk_coe,Nat.cast_add,Nat.cast_one] using he.trans (by
      simpa only [PNat.mk_coe,Nat.cast_add,Nat.cast_one] using hd)
  have hbound := actualStage_phase_error_bound ψ n p hp f hf hfA a
    (fun i b => pieceTargetPhase s target (c i) flip b)
    (fun i b => (hrep i b).2.1.trans (by linarith))
    (fun i b => (hdesired i b).trans (by linarith))
    (fun i b => (hrep i b).1.le) T B hB hnorm
  have heq : ∀ i b, combDistributionTranslation (a i b) (hermiteScaleDistribution (liftOrder p) (T b)) =
      combDistributionTranslation (h i) (hermiteScaleDistribution (liftOrder p) (T b)) := fun i b => (hrep i b).2.2
  simpa only [heq] using hbound

/-- Normalizing any nonnegative degree at a stage translation cannot increase a pairing. -/
theorem norm_leading_normalization_le_one (D : ℕ) (h : ℝ) (hh : 1 ≤ h) :
    ‖((-(h:ℂ))^D)⁻¹‖ ≤ 1 := by
  rw [norm_inv,norm_pow,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by linarith)]
  exact inv_le_one_of_one_le₀ (one_le_pow₀ hh)

/-- The paid B budget survives summation over the actual finite partition and
signed leading-degree normalization, with no growing test seminorm. -/
theorem actualStage_normalized_future_sum_bound (ψ : SchwartzMap ℝ ℂ) (n p D : ℕ)
    (hp : p ≤ n+1) (U : HermiteScale (-((6*p:ℕ):ℤ)))
    (hU : DistributionSupportedOn {x : ℝ | (actualGaps ψ (n+1):ℝ)/3 < |x|}
      (𝓕 (hermiteScaleDistribution (6*p) U)))
    (f : SchwartzMap ℝ ℂ) (hf : tsupport f ⊆ Icc (-(n+1:ℝ)) (n+1:ℝ))
    (hfA : ∀ r ≤ testOrder p, ∀ x, ‖iteratedDeriv r (f : ℝ → ℂ) x‖ ≤ 1)
    (h : Fin (actualStage ψ n).partitionSize → ℝ)
    (hh₀ : ∀ i, (actualStage ψ n).translationStart ≤ h i)
    (hh₁ : ∀ i, h i ≤ (actualStage ψ n).translationBound) :
    ‖∑ i, ((-(h i:ℂ))^D)⁻¹ * combDistributionTranslation (h i)
      (hermiteScaleDistribution (6*p) U) (SchwartzMap.smulLeftCLM ℂ ((actualStage ψ n).partition i) f)‖ ≤
      (2:ℝ)^(-((n+1:ℕ):ℤ))*‖U‖ := by
  have hstart : 1 ≤ (actualStage ψ n).translationStart := by
    have h := (actualStage_laws ψ n).start
    simp only [PNat.mk_coe,Nat.cast_add,Nat.cast_one] at h
    linarith [Nat.cast_nonneg (α:=ℝ) n]
  have hnorm (i : Fin (actualStage ψ n).partitionSize) := norm_leading_normalization_le_one D (h i) (hstart.trans (hh₀ i))
  have hpair (i : Fin (actualStage ψ n).partitionSize) :=
    actualStage_translated_future_pairing_bound ψ n p hp U hU i f
      (fun x hx => by have hx' := hf hx; constructor <;> linarith [hx'.1,hx'.2,Nat.cast_nonneg (α:=ℝ) n])
      hfA (h i) (by rw [abs_of_nonneg (by linarith [hh₀ i])]; exact hh₁ i)
  calc
    _ ≤ ∑ i, ‖((-(h i:ℂ))^D)⁻¹ * combDistributionTranslation (h i)
      (hermiteScaleDistribution (6*p) U) (SchwartzMap.smulLeftCLM ℂ ((actualStage ψ n).partition i) f)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin (actualStage ψ n).partitionSize,
        ((2:ℝ)^(-((n+1:ℕ):ℤ))/(1+((actualStage ψ n).partitionSize:ℝ)))*‖U‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right (hnorm i) (norm_nonneg _)).trans (by simpa only [one_mul,combDistributionTranslation_apply] using hpair i)
    _ ≤ (2:ℝ)^(-((n+1:ℕ):ℤ))*‖U‖ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      have hJ : (0:ℝ) ≤ (actualStage ψ n).partitionSize := Nat.cast_nonneg _
      have hden : (0:ℝ) < 1+(actualStage ψ n).partitionSize := by positivity
      have hfrac : ((actualStage ψ n).partitionSize:ℝ)/(1+(actualStage ψ n).partitionSize) ≤ 1 :=
        (div_le_one hden).mpr (by linarith)
      calc
        _ = (((actualStage ψ n).partitionSize:ℝ)/(1+(actualStage ψ n).partitionSize))*
            ((2:ℝ)^(-((n+1:ℕ):ℤ))*‖U‖) := by ring
        _ ≤ 1*((2:ℝ)^(-((n+1:ℕ):ℤ))*‖U‖) := mul_le_mul_of_nonneg_right hfrac (by positivity)
        _ = _ := one_mul _

end
end MeyerGeneralProblem.Adaptive
