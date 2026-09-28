module

public import MeyerGeneralProblem.Distribution.FiniteCombConvolution

@[expose] public section

/-!
# Actual four-atom Fourier motifs

Each factor is the signed rectangle δ₀+δₐ+δᵦ−δₐ₊ᵦ. Its two independent
unit phases give the genuine Fourier bound 2√2<3. Finite binary words
define the original motif shifts and signs; finite distributivity proves
that their actual Fourier symbol is the product of the rectangle symbols.
No coefficient-cardinality bound is substituted for Fourier cancellation.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set SchwartzMap
open scoped SchwartzMap FourierTransform

/-- The parallelogram estimate for two independent unit Fourier phases. -/
theorem norm_fourier_rectangle_le_two_sqrt_two {z w : ℂ}
    (hz : ‖z‖=1) (hw : ‖w‖=1) :
    ‖1+z+w-z*w‖≤2*Real.sqrt 2 := by
  have hp : ‖(1:ℂ)+z‖^2+‖(1:ℂ)-z‖^2=4 := by
    have h := parallelogram_law_with_norm ℂ (1:ℂ) z
    norm_num only [norm_one,hz,one_pow] at h
    exact h
  have hs : ‖(1:ℂ)+z‖+‖(1:ℂ)-z‖≤2*Real.sqrt 2 := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    nlinarith [sq_nonneg (‖(1:ℂ)+z‖-‖(1:ℂ)-z‖),Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
  rw [show 1+z+w-z*w=(1+z)+w*(1-z) by ring]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul,hw,one_mul]
  exact hs

/-- The uniform four-atom Fourier constant is strictly smaller than three. -/
theorem two_sqrt_two_lt_three : 2*Real.sqrt 2<3 := by
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2),Real.sqrt_nonneg (2:ℝ)]

/-- Physical characters multiply under addition of actual shifts. -/
theorem combModulationCharacter_add_left (a b x : ℝ) :
    combModulationCharacter (a+b) x=
      combModulationCharacter a x*combModulationCharacter b x := by
  simp only [combModulationCharacter_eq_exp]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The zero physical shift has exactly unit character. -/
theorem combModulationCharacter_zero_left (x : ℝ) : combModulationCharacter 0 x=1 := by
  simp only [combModulationCharacter_eq_exp,Complex.ofReal_zero,mul_zero,zero_mul,Complex.exp_zero]

/-- Every physical shift has unit character at zero Fourier frequency. -/
theorem combModulationCharacter_zero_right (a : ℝ) : combModulationCharacter a 0=1 := by
  simp only [combModulationCharacter_eq_exp,Complex.ofReal_zero,mul_zero,Complex.exp_zero]

/-- Character factorization for a genuine finite sum of physical shifts. -/
theorem combModulationCharacter_finset_sum {ι : Type*} (s : Finset ι) (a : ι → ℝ) (x : ℝ) :
    combModulationCharacter (∑ i ∈ s, a i) x=∏ i ∈ s, combModulationCharacter (a i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty,Finset.prod_empty,combModulationCharacter_zero_left]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi,Finset.prod_insert hi,combModulationCharacter_add_left,ih]

/-- The two binary digits recording one signed-rectangle atom. -/
abbrev FourierMotifDigit := Fin 2 × Fin 2

/-- The actual physical shift of a rectangle digit. -/
def fourierMotifDigitShift (a b : ℝ) (d : FourierMotifDigit) : ℝ :=
  (d.1:ℝ)*a+(d.2:ℝ)*b

/-- The rectangle sign is negative exactly at its opposite corner. -/
def fourierMotifDigitSign (d : FourierMotifDigit) : ℂ :=
  if d.1=1 ∧ d.2=1 then -1 else 1

/-- Each original rectangle coefficient has modulus one. -/
theorem norm_fourierMotifDigitSign (d : FourierMotifDigit) : ‖fourierMotifDigitSign d‖=1 := by
  unfold fourierMotifDigitSign
  split <;> norm_num

/-- The actual four-atom Fourier symbol equals the independent-phase rectangle. -/
theorem fourierMotif_rectangle_symbol (a b x : ℝ) :
    finiteCombFourierSymbol (fourierMotifDigitShift a b) fourierMotifDigitSign x=
      1+combModulationCharacter (-a) x+combModulationCharacter (-b) x-
        combModulationCharacter (-a) x*combModulationCharacter (-b) x := by
  simp only [finiteCombFourierSymbol,Fintype.sum_prod_type,Fin.sum_univ_two,
    fourierMotifDigitShift,fourierMotifDigitSign]
  norm_num only [Fin.val_zero,Fin.val_one,Nat.cast_zero,Nat.cast_one,zero_mul,one_mul,
    zero_add,add_zero,neg_zero,combModulationCharacter_zero_left]
  simp only [show (0:Fin 2)≠1 by decide,false_and,and_false,ite_false,true_and,ite_true,
    one_mul,neg_one_mul]
  rw [neg_add,combModulationCharacter_add_left]
  ring

/-- The actual four-atom motif enjoys cancellation uniformly in both shifts
and the physical frequency, without any separation assumption. -/
theorem norm_fourierMotif_rectangle_symbol_le (a b x : ℝ) :
    ‖finiteCombFourierSymbol (fourierMotifDigitShift a b) fourierMotifDigitSign x‖≤
      2*Real.sqrt 2 := by
  rw [fourierMotif_rectangle_symbol]
  exact norm_fourier_rectangle_le_two_sqrt_two
    (norm_combModulationCharacter _ _) (norm_combModulationCharacter _ _)

/-- The genuine rectangle Fourier symbol is uniformly strictly below three. -/
theorem norm_fourierMotif_rectangle_symbol_lt_three (a b x : ℝ) :
    ‖finiteCombFourierSymbol (fourierMotifDigitShift a b) fourierMotifDigitSign x‖<3 :=
  (norm_fourierMotif_rectangle_symbol_le a b x).trans_lt two_sqrt_two_lt_three

/-- A finite motif word records independently both binary choices at every factor. -/
abbrev FourierMotifWord (n : ℕ) := Fin n → FourierMotifDigit

/-- The genuine physical shift associated with one finite motif word. -/
def fourierMotifShift {n : ℕ} (a b : Fin n → ℝ) (d : FourierMotifWord n) : ℝ :=
  ∑ i, fourierMotifDigitShift (a i) (b i) (d i)

/-- The original signed coefficient of a motif word, before merging coincidences. -/
def fourierMotifSign {n : ℕ} (d : FourierMotifWord n) : ℂ :=
  ∏ i, fourierMotifDigitSign (d i)

/-- Every original word coefficient has modulus one, before any coincident
physical atoms are merged; this is not a total-variation assertion. -/
theorem norm_fourierMotifSign {n : ℕ} (d : FourierMotifWord n) : ‖fourierMotifSign d‖=1 := by
  simp only [fourierMotifSign,norm_prod,norm_fourierMotifDigitSign,Finset.prod_const_one]

/-- There are 4^n combinatorial words; no physical injectivity is asserted here. -/
theorem card_fourierMotifWord (n : ℕ) : Fintype.card (FourierMotifWord n)=4^n := by
  simp only [FourierMotifWord,FourierMotifDigit,Fintype.card_fun,Fintype.card_prod,Fintype.card_fin]

/-- The actual finite-word Fourier sum factors as the product of the actual
four-atom symbols, by finite distributivity and the genuine character law. -/
theorem finiteFourierMotif_symbol_eq_prod {n : ℕ} (a b : Fin n → ℝ) (x : ℝ) :
    finiteCombFourierSymbol (fourierMotifShift a b) fourierMotifSign x=
      ∏ i, finiteCombFourierSymbol (fourierMotifDigitShift (a i) (b i)) fourierMotifDigitSign x := by
  classical
  simp only [finiteCombFourierSymbol,fourierMotifShift,fourierMotifSign,
    ← Finset.sum_neg_distrib,combModulationCharacter_finset_sum,← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (ι := Fin n) (κ := fun _ => FourierMotifDigit)
    (fun i d => fourierMotifDigitSign d*
      combModulationCharacter (-fourierMotifDigitShift (a i) (b i) d) x)).symm

/-- Genuine cancellation gives the stronger finite-product bound (2√2)^n. -/
theorem norm_finiteFourierMotif_symbol_le {n : ℕ} (a b : Fin n → ℝ) (x : ℝ) :
    ‖finiteCombFourierSymbol (fourierMotifShift a b) fourierMotifSign x‖≤
      (2*Real.sqrt 2)^n := by
  rw [finiteFourierMotif_symbol_eq_prod,norm_prod]
  calc
    _ ≤ ∏ _i : Fin n, (2*Real.sqrt 2) :=
      Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => norm_fourierMotif_rectangle_symbol_le _ _ _)
    _ = _ := by simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]

/-- The actual finite motif Fourier norm is bounded by 3^n, not by the
4^n coefficient count, uniformly even when physical shifts coincide. -/
theorem norm_finiteFourierMotif_symbol_le_three_pow {n : ℕ} (a b : Fin n → ℝ) (x : ℝ) :
    ‖finiteCombFourierSymbol (fourierMotifShift a b) fourierMotifSign x‖≤(3:ℝ)^n :=
  (norm_finiteFourierMotif_symbol_le a b x).trans
    (pow_le_pow_left₀ (by positivity) two_sqrt_two_lt_three.le _)

/-- At zero Fourier frequency the actual signed motif sum is exactly 2^n,
distinct from its 4^n count of original words. -/
theorem finiteFourierMotif_symbol_zero {n : ℕ} (a b : Fin n → ℝ) :
    finiteCombFourierSymbol (fourierMotifShift a b) fourierMotifSign 0=(2:ℂ)^n := by
  rw [finiteFourierMotif_symbol_eq_prod]
  simp only [fourierMotif_rectangle_symbol,combModulationCharacter_zero_right]
  norm_num

end

end MeyerGeneralProblem
