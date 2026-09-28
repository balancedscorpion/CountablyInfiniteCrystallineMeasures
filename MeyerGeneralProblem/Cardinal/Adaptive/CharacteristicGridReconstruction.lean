module

public import MeyerGeneralProblem.Cardinal.Adaptive.CharacteristicTensorNewton

@[expose] public section

/-! # Exact four-parity Newton reconstruction on the full signed finite grid -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open Set Polynomial

/-- Literal cosine/sine Newton basis on the characteristic nodes. -/
def characteristicNewtonBasis {k : ℕ} (odd : Bool) (phase : Fin (k+1) → ℝ)
    (i : Fin (k+1)) (t : ℝ) : ℂ :=
  parityTrigFactor odd t *
    (newtonBasisPolynomial (fun a => (parityNewtonCoordinate (phase a):ℂ)) i).eval (parityNewtonCoordinate t:ℂ)

/-- Both quotient coordinates are even under independent sign reversals. -/
theorem tensorParityGridQuotient_signed (e d : Bool) (f : ℝ → ℝ → ℂ)
    (t u x y : ℝ) (ht : t=x ∨ t= -x) (hu : u=y ∨ u= -y) :
    tensorParityGridQuotient e d f t u=tensorParityGridQuotient e d f x y := by
  rcases ht with rfl|rfl <;> rcases hu with rfl|rfl <;>
    simp only [tensorParityGridQuotient,parityGridQuotient_neg]

/-- The terminal odd basis vanishes at every signed grid point, including zero. -/
theorem characteristicNewtonBasis_terminal_odd {k : ℕ} (phase : Fin (k+1) → ℝ)
    (hzero : phase (Fin.last k)=0) (a : Fin (k+1)) (t : ℝ) (ht : t=phase a ∨ t= -phase a) :
    characteristicNewtonBasis true phase (Fin.last k) t=0 := by
  by_cases ha : a=Fin.last k
  · subst a
    rcases ht with rfl|rfl <;> simp [characteristicNewtonBasis,parityTrigFactor,hzero]
  · have hz : parityNewtonCoordinate t=parityNewtonCoordinate (phase a) := by
      rcases ht with rfl|rfl <;> simp
    rw [characteristicNewtonBasis,hz,eval_newtonBasisPolynomial]
    have hp : (∏ j ∈ Finset.Iio (Fin.last k),
        ((parityNewtonCoordinate (phase a):ℂ)-(parityNewtonCoordinate (phase j):ℂ)))=0 := by
      apply Finset.prod_eq_zero (show a ∈ Finset.Iio (Fin.last k) from
        Finset.mem_Iio.mpr (Fin.lt_last_iff_ne_last.mpr ha))
      simp
    rw [hp,mul_zero]

/-- Raw finite tensor coefficients for the literal parity quotient values. -/
def characteristicGridCoefficients {k l : ℕ} (e d : Bool)
    (x : Fin (k+1) → ℝ) (y : Fin (l+1) → ℝ)
    (hx : Function.Injective (fun a => parityNewtonCoordinate (x a)))
    (hy : Function.Injective (fun b => parityNewtonCoordinate (y b)))
    (f : ℝ → ℝ → ℂ) (i : Fin (k+1)) (j : Fin (l+1)) : ℂ :=
  tensorNewtonCoefficients (fun a => (parityNewtonCoordinate (x a):ℂ))
    (fun b => (parityNewtonCoordinate (y b):ℂ))
    (Complex.ofReal_injective.comp hx) (Complex.ofReal_injective.comp hy)
    (fun a b => tensorParityGridQuotient e d f (x a) (y b)) i j

/-- The unused terminal odd row or column is set to zero. -/
def trimmedCharacteristicGridCoefficients {k l : ℕ} (e d : Bool)
    (x : Fin (k+1) → ℝ) (y : Fin (l+1) → ℝ)
    (hx : Function.Injective (fun a => parityNewtonCoordinate (x a)))
    (hy : Function.Injective (fun b => parityNewtonCoordinate (y b)))
    (f : ℝ → ℝ → ℂ) (i : Fin (k+1)) (j : Fin (l+1)) : ℂ :=
  if (e ∧ i=Fin.last k) ∨ (d ∧ j=Fin.last l) then 0 else characteristicGridCoefficients e d x y hx hy f i j

/-- Zeroing either unused terminal odd coefficient leaves every grid summand unchanged. -/
theorem trimmedCharacteristicGrid_term {k l : ℕ} (e d : Bool)
    (x : Fin (k+1) → ℝ) (y : Fin (l+1) → ℝ)
    (hx : Function.Injective (fun a => parityNewtonCoordinate (x a)))
    (hy : Function.Injective (fun b => parityNewtonCoordinate (y b)))
    (hx0 : x (Fin.last k)=0) (hy0 : y (Fin.last l)=0)
    (f : ℝ → ℝ → ℂ) (i : Fin (k+1)) (j : Fin (l+1))
    (a : Fin (k+1)) (b : Fin (l+1)) (t u : ℝ)
    (ht : t=x a ∨ t= -x a) (hu : u=y b ∨ u= -y b) :
    trimmedCharacteristicGridCoefficients e d x y hx hy f i j *
      characteristicNewtonBasis e x i t * characteristicNewtonBasis d y j u =
    characteristicGridCoefficients e d x y hx hy f i j *
      characteristicNewtonBasis e x i t * characteristicNewtonBasis d y j u := by
  unfold trimmedCharacteristicGridCoefficients
  split_ifs with h
  · rcases h with ⟨he,rfl⟩|⟨hd,rfl⟩
    · simp only [he,characteristicNewtonBasis_terminal_odd x hx0 a t ht,mul_zero,zero_mul]
    · simp only [hd,characteristicNewtonBasis_terminal_odd y hy0 b u hu,mul_zero,zero_mul]
  · rfl

/-- Each raw parity tensor interpolates at both signs of every supplied node. -/
theorem characteristicGrid_parity_interpolates {k l : ℕ} (e d : Bool)
    (x : Fin (k+1) → ℝ) (y : Fin (l+1) → ℝ)
    (hx : Function.Injective (fun a => parityNewtonCoordinate (x a)))
    (hy : Function.Injective (fun b => parityNewtonCoordinate (y b)))
    (f : ℝ → ℝ → ℂ) (a : Fin (k+1)) (b : Fin (l+1)) (t u : ℝ)
    (ht : t=x a ∨ t= -x a) (hu : u=y b ∨ u= -y b) :
    (∑ i, ∑ j, characteristicGridCoefficients e d x y hx hy f i j *
      characteristicNewtonBasis e x i t * characteristicNewtonBasis d y j u) =
      parityTrigFactor e t * parityTrigFactor d u * tensorParityGridQuotient e d f t u := by
  have htx : parityNewtonCoordinate t=parityNewtonCoordinate (x a) := by
    rcases ht with rfl|rfl <;> simp
  have huy : parityNewtonCoordinate u=parityNewtonCoordinate (y b) := by
    rcases hu with rfl|rfl <;> simp
  have he := tensorNewton_interpolates (fun a => (parityNewtonCoordinate (x a):ℂ))
    (fun b => (parityNewtonCoordinate (y b):ℂ))
    (Complex.ofReal_injective.comp hx) (Complex.ofReal_injective.comp hy)
    (fun a b => tensorParityGridQuotient e d f (x a) (y b)) a b
  rw [tensorParityGridQuotient_signed e d f t u (x a) (y b) ht hu]
  rw [← he]
  simp only [characteristicGridCoefficients,characteristicNewtonBasis,htx,huy,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The actual four-parity Newton sum, with terminal odd rows and columns zero,
reconstructs every signed finite-grid value and every seam value exactly. -/
theorem trimmedCharacteristicGrid_reconstruct {k l : ℕ}
    (x : Fin (k+1) → ℝ) (y : Fin (l+1) → ℝ)
    (hx : Function.Injective (fun a => parityNewtonCoordinate (x a)))
    (hy : Function.Injective (fun b => parityNewtonCoordinate (y b)))
    (hx0 : x (Fin.last k)=0) (hy0 : y (Fin.last l)=0)
    (f : ℝ → ℝ → ℂ) (a : Fin (k+1)) (b : Fin (l+1)) (t u : ℝ)
    (ht : t=x a ∨ t= -x a) (hu : u=y b ∨ u= -y b)
    (hnzt : ∀ e : Bool, ¬(e ∧ t=0) → parityTrigFactor e t ≠ 0)
    (hnzu : ∀ d : Bool, ¬(d ∧ u=0) → parityTrigFactor d u ≠ 0) :
    (∑ e : Bool, ∑ d : Bool, ∑ i, ∑ j,
      trimmedCharacteristicGridCoefficients e d x y hx hy f i j *
      characteristicNewtonBasis e x i t * characteristicNewtonBasis d y j u)=f t u := by
  simp_rw [trimmedCharacteristicGrid_term _ _ x y hx hy hx0 hy0 f _ _ a b t u ht hu,
    characteristicGrid_parity_interpolates _ _ x y hx hy f a b t u ht hu]
  exact tensorParityGridQuotient_reconstruct f t u hnzt hnzu

/-- Raw grid coefficients agree with the analytic characteristic coefficients
whose mixed finite-order bound was proved independently. -/
theorem characteristicGridCoefficients_eq_analytic {k l : ℕ} (e d : Bool)
    (x : Fin (k+1) → ℝ) (y : Fin (l+1) → ℝ)
    (hx : Function.Injective (fun a => parityNewtonCoordinate (x a)))
    (hy : Function.Injective (fun b => parityNewtonCoordinate (y b)))
    (hxt : ∀ a, |x a| ≤ 1/2) (hxs : ∀ a, |Real.sin (Real.pi*x a)| ≤ 1/2)
    (hyt : ∀ b, |y b| ≤ 1/2) (hys : ∀ b, |Real.sin (Real.pi*y b)| ≤ 1/2)
    (f : ℝ → ℝ → ℂ) (i : Fin (k+1)) (j : Fin (l+1)) :
    characteristicGridCoefficients e d x y hx hy f i j =
      characteristicTensorDividedDifference e d
        (finiteNodeSequence (fun a => parityNewtonCoordinate (x a))) i
        (finiteNodeSequence (fun b => parityNewtonCoordinate (y b))) j f := by
  rw [characteristicTensorDividedDifference_eq_coefficients e d _ _ hx hy f i j]
  unfold characteristicGridCoefficients
  congr 1
  funext a b
  rw [characteristicParityGridQuotient_at_phase e _ (x a) (hxt a) (hxs a)]
  simp_rw [characteristicParityGridQuotient_at_phase d _ (y b) (hyt b) (hys b)]
  rfl

/-- Finite characteristic nodes and sine radii have the exact same zero padding. -/
theorem finite_characteristic_nodes_eq {m : ℕ} (x : Fin m → ℝ) :
    finiteNodeSequence (fun a => parityNewtonCoordinate (x a)) =
      fun j => 2*(finiteNodeSequence (fun a => Real.sin (Real.pi*x a)) j)^2 := by
  funext j
  unfold finiteNodeSequence
  split_ifs <;> simp only [parityNewtonCoordinate_eq,pow_two,mul_zero]

/-- Every characteristic-coordinate denominator product is nonnegative. -/
theorem characteristic_prefix_product_nonneg {m : ℕ} (x : Fin m → ℝ) (n : ℕ) :
    0 ≤ ∏ j ∈ Finset.range n, finiteNodeSequence (fun a => parityNewtonCoordinate (x a)) j := by
  rw [finite_characteristic_nodes_eq]
  exact Finset.prod_nonneg (fun j _ => mul_nonneg (by norm_num) (sq_nonneg _))

/-- The actual trimmed grid coefficients inherit the mixed source estimate;
terminal odd coefficients are zero rather than assigned a false derivative bound. -/
theorem exists_trimmed_characteristic_grid_bound (e d : Bool) (L : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ k l : ℕ,
      ∀ x : Fin (k+1) → ℝ, ∀ y : Fin (l+1) → ℝ,
      ∀ hx : Function.Injective (fun a => parityNewtonCoordinate (x a)),
      ∀ hy : Function.Injective (fun b => parityNewtonCoordinate (y b)),
      (∀ a, |x a| ≤ 1/2) → (∀ a, |Real.sin (Real.pi*x a)| ≤ 1/2) →
      (∀ b, |y b| ≤ 1/2) → (∀ b, |Real.sin (Real.pi*y b)| ≤ 1/2) →
      ∀ f : ℝ → ℝ → ℂ,
      (∀ b, ContDiff ℝ (2*L+1) (fun a => f a b)) →
      (∀ r ≤ 2*L+1, ∀ a, ContDiff ℝ (2*L+1)
        (fun b => iteratedDeriv r (fun a => f a b) a)) →
      ∀ A : ℝ, 0 ≤ A →
      (∀ r ≤ 2*L+1, ∀ q ≤ 2*L+1, ∀ a ∈ Icc (-1/2:ℝ) (1/2),
        ∀ b ∈ Icc (-1/2:ℝ) (1/2),
        ‖iteratedDeriv q (fun b => iteratedDeriv r (fun a => f a b) a) b‖ ≤ A) →
      ∀ i : Fin (k+1), ∀ j : Fin (l+1),
      (¬((e ∧ i=Fin.last k) ∨ (d ∧ j=Fin.last l)) →
        CharacteristicRadiusPrefix e i (finiteNodeSequence (fun a => Real.sin (Real.pi*x a))) ∧
        CharacteristicRadiusPrefix d j (finiteNodeSequence (fun b => Real.sin (Real.pi*y b)))) →
      ‖trimmedCharacteristicGridCoefficients e d x y hx hy f i j‖ ≤
        4^(i.val+j.val)*(C*A)/
          ((∏ a ∈ Finset.range (i.val-L), finiteNodeSequence (fun a => parityNewtonCoordinate (x a)) a)*
           (∏ b ∈ Finset.range (j.val-L), finiteNodeSequence (fun b => parityNewtonCoordinate (y b)) b)) := by
  obtain ⟨C,hC,hbound⟩ := exists_characteristic_tensor_Newton_bound e d L
  refine ⟨C,hC,?_⟩
  intro k l x y hx hy hxt hxs hyt hys f hfx hfxy A hA hder i j hgeometry
  unfold trimmedCharacteristicGridCoefficients
  split_ifs with hterminal
  · rw [norm_zero]
    exact div_nonneg (by positivity) (mul_nonneg (characteristic_prefix_product_nonneg x _) (characteristic_prefix_product_nonneg y _))
  · rw [characteristicGridCoefficients_eq_analytic e d x y hx hy hxt hxs hyt hys f i j,
      finite_characteristic_nodes_eq,finite_characteristic_nodes_eq]
    exact hbound i j _ _ (hgeometry hterminal).1 (hgeometry hterminal).2 f hfx hfxy A hA hder


/-- On the fixed tested phase chart the cosine factor is nonzero, and the sine
factor vanishes only at the single seam. -/
theorem parityTrigFactor_ne_zero_on_chart (odd : Bool) (t : ℝ)
    (ht : |t| ≤ 1/2) (hs : |Real.sin (Real.pi*t)| ≤ 1/2)
    (h : ¬(odd ∧ t=0)) : parityTrigFactor odd t ≠ 0 := by
  have he := signedNewtonChart_sin t ht hs
  cases odd
  · change (Real.cos (Real.pi*t):ℂ) ≠ 0
    rw [← he]
    exact_mod_cast (signedNewtonChart_cos_pos (Real.sin (Real.pi*t))).ne'
  · change (Real.sin (Real.pi*t):ℂ) ≠ 0
    intro hz
    have hz' : Real.sin (Real.pi*t)=0 := by exact_mod_cast hz
    have hzero : signedNewtonChart 0=0 := by simp [signedNewtonChart,signedChartCoordinate]
    rw [hz',hzero] at he
    exact h ⟨rfl,he.symm⟩

/-- Exact reconstruction on the full signed grid follows from the literal small
phase bounds, with no separate nonvanishing certificate. -/
theorem trimmedCharacteristicGrid_reconstruct_on_chart {k l : ℕ}
    (x : Fin (k+1) → ℝ) (y : Fin (l+1) → ℝ)
    (hx : Function.Injective (fun a => parityNewtonCoordinate (x a)))
    (hy : Function.Injective (fun b => parityNewtonCoordinate (y b)))
    (hx0 : x (Fin.last k)=0) (hy0 : y (Fin.last l)=0)
    (hxt : ∀ a, |x a| ≤ 1/2) (hxs : ∀ a, |Real.sin (Real.pi*x a)| ≤ 1/2)
    (hyt : ∀ b, |y b| ≤ 1/2) (hys : ∀ b, |Real.sin (Real.pi*y b)| ≤ 1/2)
    (f : ℝ → ℝ → ℂ) (a : Fin (k+1)) (b : Fin (l+1)) (t u : ℝ)
    (ht : t=x a ∨ t= -x a) (hu : u=y b ∨ u= -y b) :
    (∑ e : Bool, ∑ d : Bool, ∑ i, ∑ j,
      trimmedCharacteristicGridCoefficients e d x y hx hy f i j *
      characteristicNewtonBasis e x i t * characteristicNewtonBasis d y j u)=f t u := by
  apply trimmedCharacteristicGrid_reconstruct x y hx hy hx0 hy0 f a b t u ht hu
  · intro e he
    apply parityTrigFactor_ne_zero_on_chart e t _ _ he
    · rcases ht with rfl|rfl <;> simpa only [abs_neg] using hxt a
    · rcases ht with rfl|rfl <;> simpa only [mul_neg,Real.sin_neg,abs_neg] using hxs a
  · intro d hd
    apply parityTrigFactor_ne_zero_on_chart d u _ _ hd
    · rcases hu with rfl|rfl <;> simpa only [abs_neg] using hyt b
    · rcases hu with rfl|rfl <;> simpa only [mul_neg,Real.sin_neg,abs_neg] using hys b


end
end MeyerGeneralProblem.Adaptive
