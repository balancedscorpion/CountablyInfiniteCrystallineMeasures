module

public import MeyerGeneralProblem.Distribution.FiniteFourierMotif
public import Mathlib.Algebra.BigOperators.Fin
import all Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic
import all Mathlib.Tactic

@[expose] public section

/-!
# Exact finite base-five motif geometry

Pairs of binary digits are encoded as base-25 digits `5*a+b`.
Normalizing the resulting integer by `m*25^n` is the base-five motif
with its finite factors in reverse order. This preserves the actual
rectangle factors and proves distinctness without irrational selection.
-/

namespace MeyerGeneralProblem

noncomputable section

/-- Two genuine binary digits form one rectangle choice. -/
abbrev BaseFiveMotifDigit := Fin 2 × Fin 2

/-- The exact base-25 encoding of one rectangle digit. -/
def baseFiveMotifDigitValue (d : BaseFiveMotifDigit) : ℕ := 5*d.1.val+d.2.val

/-- Every encoded digit is at most six. -/
theorem baseFiveMotifDigitValue_le (d : BaseFiveMotifDigit) :
    baseFiveMotifDigitValue d ≤ 6 := by
  unfold baseFiveMotifDigitValue
  have := d.1.isLt
  have := d.2.isLt
  omega

/-- Distinct binary rectangle choices have distinct encoded digits. -/
theorem baseFiveMotifDigitValue_injective : Function.Injective baseFiveMotifDigitValue := by
  intro d e h
  have hd1 := d.1.isLt
  have hd2 := d.2.isLt
  have he1 := e.1.isLt
  have he2 := e.2.isLt
  unfold baseFiveMotifDigitValue at h
  apply Prod.ext <;> apply Fin.ext <;> omega

/-- The actual nonnegative integer encoded by a finite motif word. -/
def baseFiveMotifValue (n : ℕ) (d : Fin n → BaseFiveMotifDigit) : ℕ :=
  ∑ i, baseFiveMotifDigitValue (d i)*25^i.val

/-- Separating the first digit gives the exact base-25 recurrence. -/
theorem baseFiveMotifValue_succ (n : ℕ) (d : Fin (n+1) → BaseFiveMotifDigit) :
    baseFiveMotifValue (n+1) d = baseFiveMotifDigitValue (d 0) +
      25*baseFiveMotifValue n (fun i => d i.succ) := by
  unfold baseFiveMotifValue
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ]
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The full finite word is recovered uniquely from its integer value. -/
theorem baseFiveMotifValue_injective (n : ℕ) : Function.Injective (baseFiveMotifValue n) := by
  induction n with
  | zero => intro d e _; funext i; exact Fin.elim0 i
  | succ n ih =>
    intro d e h
    rw [baseFiveMotifValue_succ,baseFiveMotifValue_succ] at h
    have hd := baseFiveMotifDigitValue_le (d 0)
    have he := baseFiveMotifDigitValue_le (e 0)
    have hz : baseFiveMotifDigitValue (d 0)=baseFiveMotifDigitValue (e 0) := by omega
    have ht : baseFiveMotifValue n (fun i => d i.succ)=
        baseFiveMotifValue n (fun i => e i.succ) := by omega
    have heq := ih ht
    funext i
    refine Fin.cases ?_ (fun j => congrFun heq j) i
    exact baseFiveMotifDigitValue_injective hz

/-- The complete integer motif lies strictly below one quarter of the
normalizing power, including the empty word. -/
theorem four_mul_baseFiveMotifValue_lt (n : ℕ) (d : Fin n → BaseFiveMotifDigit) :
    4*baseFiveMotifValue n d < 25^n := by
  induction n with
  | zero => simp [baseFiveMotifValue]
  | succ n ih =>
    rw [baseFiveMotifValue_succ,pow_succ]
    have hd := baseFiveMotifDigitValue_le (d 0)
    have ht := ih (fun i => d i.succ)
    omega

/-- The actual real motif position, before the block's irrational translation. -/
def baseFiveMotifPosition (m n : ℕ) (d : Fin n → BaseFiveMotifDigit) : ℝ :=
  (baseFiveMotifValue n d : ℝ)/((m:ℝ)*25^n)

/-- Every position is genuinely rational. -/
theorem baseFiveMotifPosition_rational (m n : ℕ) (d : Fin n → BaseFiveMotifDigit) :
    ∃ q : ℚ, (q:ℝ)=baseFiveMotifPosition m n d := by
  refine ⟨(baseFiveMotifValue n d : ℚ)/((m:ℚ)*25^n),?_⟩
  simp [baseFiveMotifPosition]

/-- Distinct motif words give distinct actual physical positions at positive size. -/
theorem baseFiveMotifPosition_injective (m n : ℕ) (hm : 0<m) :
    Function.Injective (baseFiveMotifPosition m n) := by
  intro d e h
  have hden : (m:ℝ)*25^n ≠ 0 := by positivity
  have hv : (baseFiveMotifValue n d : ℝ)=(baseFiveMotifValue n e : ℝ) :=
    (div_left_inj' hden).mp h
  exact baseFiveMotifValue_injective n (by exact_mod_cast hv)

/-- Every actual motif point lies in the short half-open interval
`[0,1/(4*m))`, uniformly in the number of factors. -/
theorem baseFiveMotifPosition_mem (m n : ℕ) (hm : 0<m)
    (d : Fin n → BaseFiveMotifDigit) :
    baseFiveMotifPosition m n d ∈ Set.Ico 0 (1/(4*(m:ℝ))) := by
  have hm' : 0<(m:ℝ) := by exact_mod_cast hm
  have hp : (0:ℝ)<25^n := by positivity
  have hv : 4*(baseFiveMotifValue n d : ℝ)<25^n := by
    exact_mod_cast four_mul_baseFiveMotifValue_lt n d
  constructor
  · unfold baseFiveMotifPosition
    positivity
  · unfold baseFiveMotifPosition
    apply (div_lt_iff₀ (mul_pos hm' hp)).mpr
    field_simp
    nlinarith

/-- The first base-five displacement in each reversed-order rectangle. -/
def baseFiveMotifA (m n : ℕ) (i : Fin n) : ℝ :=
  5*25^i.val/((m:ℝ)*25^n)

/-- The second base-five displacement in each reversed-order rectangle. -/
def baseFiveMotifB (m n : ℕ) (i : Fin n) : ℝ :=
  25^i.val/((m:ℝ)*25^n)

/-- The integer encoding is exactly the sum of the actual rectangle
displacements, not merely an equinumerous replacement support. -/
theorem baseFiveMotifPosition_eq_sum (m n : ℕ) (d : Fin n → BaseFiveMotifDigit) :
    baseFiveMotifPosition m n d = ∑ i : Fin n,
      (((d i).1:ℝ)*baseFiveMotifA m n i+((d i).2:ℝ)*baseFiveMotifB m n i) := by
  unfold baseFiveMotifPosition baseFiveMotifValue
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  unfold baseFiveMotifDigitValue baseFiveMotifA baseFiveMotifB
  push_cast
  ring

/-- The genuine finite Fourier motif uses exactly the encoded physical
positions when instantiated at the reversed base-five rectangle factors. -/
theorem fourierMotifShift_baseFive_eq (m n : ℕ) (d : FourierMotifWord n) :
    fourierMotifShift (baseFiveMotifA m n) (baseFiveMotifB m n) d =
      baseFiveMotifPosition m n d := by
  exact (baseFiveMotifPosition_eq_sum m n d).symm

/-- The actual injective base-five motif has the proved cancellation
bound uniformly on the complete Fourier line. -/
theorem norm_baseFiveMotif_fourierSymbol_le (m n : ℕ) (x : ℝ) :
    ‖finiteCombFourierSymbol (baseFiveMotifPosition m n) fourierMotifSign x‖ ≤ (3:ℝ)^n := by
  have he : fourierMotifShift (baseFiveMotifA m n) (baseFiveMotifB m n) =
      baseFiveMotifPosition m n := funext (fourierMotifShift_baseFive_eq m n)
  rw [← he]
  exact norm_finiteFourierMotif_symbol_le_three_pow _ _ x

/-- Any two actual motif positions differ by less than one fine-lattice
spacing, independently of the number of factors. -/
theorem abs_sub_baseFiveMotifPosition_lt (m n : ℕ) (hm : 0<m)
    (d e : Fin n → BaseFiveMotifDigit) :
    |baseFiveMotifPosition m n d-baseFiveMotifPosition m n e| < (m:ℝ)⁻¹ := by
  obtain ⟨hd0,hd⟩ := baseFiveMotifPosition_mem m n hm d
  obtain ⟨he0,he⟩ := baseFiveMotifPosition_mem m n hm e
  have hm' : (0:ℝ)<m := by exact_mod_cast hm
  have hi : (0:ℝ)<(m:ℝ)⁻¹ := inv_pos.mpr hm'
  have hquarter : 1/(4*(m:ℝ))=(m:ℝ)⁻¹/4 := by field_simp
  rw [hquarter] at hd he
  exact abs_lt.mpr ⟨by linarith,by linarith⟩

/-- Convolution with the fine lattice has unique actual decomposition:
neither a second motif point nor another lattice atom can collide. -/
theorem baseFiveMotifPosition_lattice_injective (m n : ℕ) (hm : 0<m) (γ : ℝ) :
    Function.Injective (fun p : (Fin n → BaseFiveMotifDigit) × ℤ =>
      γ+baseFiveMotifPosition m n p.1+(p.2:ℝ)/(m:ℝ)) := by
  rintro ⟨d,j⟩ ⟨e,l⟩ h
  have hm' : (0:ℝ)<m := by exact_mod_cast hm
  have habs := abs_sub_baseFiveMotifPosition_lt m n hm d e
  have heq : ((j-l:ℤ):ℝ)=(m:ℝ)*(baseFiveMotifPosition m n e-baseFiveMotifPosition m n d) := by
    have hj : ((j:ℝ)/(m:ℝ))*(m:ℝ)=(j:ℝ) := div_mul_cancel₀ _ hm'.ne'
    have hl : ((l:ℝ)/(m:ℝ))*(m:ℝ)=(l:ℝ) := div_mul_cancel₀ _ hm'.ne'
    push_cast
    nlinarith
  have hsmall : |((j-l:ℤ):ℝ)|<1 := by
    rw [heq,abs_mul,abs_of_pos hm',abs_sub_comm]
    have hh := mul_lt_mul_of_pos_left habs hm'
    simpa only [mul_inv_cancel₀ hm'.ne'] using hh
  have hjl : j=l := by
    have hh : |j-l|<(1:ℤ) := by exact_mod_cast hsmall
    have hlow := neg_abs_le (j-l)
    have hhigh := le_abs_self (j-l)
    omega
  have hde : baseFiveMotifPosition m n d=baseFiveMotifPosition m n e := by
    simp only [hjl] at h
    linarith
  exact Prod.ext (baseFiveMotifPosition_injective m n hm hde) hjl

end

end MeyerGeneralProblem
