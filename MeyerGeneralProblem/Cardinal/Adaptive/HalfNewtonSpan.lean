module

public import MeyerGeneralProblem.Cardinal.Adaptive.ZakFourierCoordinates

@[expose] public section

/-! # Exact half-integer Newton functions and their full trigonometric span -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open scoped BigOperators

/-- The actual ordered Newton product of the half-endpoint source, retaining
all levels including the empty zeroth product. -/
def halfNewtonProduct (ε : ℕ+ → ℝ) (i : ℕ) (x : ℝ) : ℂ :=
  ∏ r ∈ Finset.range i, (criticalNewtonNode x-criticalNewtonNode (ε ⟨r+1,by omega⟩))

/-- The two original half-integer parity functions: false is cosine, true sine. -/
def halfNewtonFunction (ε : ℕ+ → ℝ) (i : ℕ) (e : Bool) (x : ℝ) : ℂ :=
  (if e then (Real.sin (Real.pi*x) : ℂ) else (Real.cos (Real.pi*x) : ℂ))*halfNewtonProduct ε i x

/-- Exact next-factor recurrence of the original Newton product. -/
theorem halfNewtonProduct_succ (ε : ℕ+ → ℝ) (i : ℕ) (x : ℝ) :
    halfNewtonProduct ε (i+1) x=halfNewtonProduct ε i x*
      (criticalNewtonNode x-criticalNewtonNode (ε ⟨i+1,by omega⟩)) := by
  exact Finset.prod_range_succ _ _

/-- Multiplication by the exact Newton coordinate has the full one-step
recurrence; no finite compression is substituted. -/
theorem halfNewtonFunction_mul_node (ε : ℕ+ → ℝ) (i : ℕ) (e : Bool) :
    (fun x => criticalNewtonNode x*halfNewtonFunction ε i e x)=
      halfNewtonFunction ε (i+1) e+
        criticalNewtonNode (ε ⟨i+1,by omega⟩) • halfNewtonFunction ε i e := by
  funext x
  simp only [halfNewtonFunction,halfNewtonProduct_succ,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  ring

private theorem sine_parity_even (x : ℝ) :
    (Real.sin (2*Real.pi*x) : ℂ)*(Real.cos (Real.pi*x) : ℂ)=
      (2-criticalNewtonNode x)*(Real.sin (Real.pi*x) : ℂ) := by
  have h : Real.sin (2*Real.pi*x)*Real.cos (Real.pi*x)=
      (1+Real.cos (2*Real.pi*x))*Real.sin (Real.pi*x) := by
    rw [show 2*Real.pi*x=2*(Real.pi*x) by ring,Real.sin_two_mul,Real.cos_two_mul]
    ring
  have hc := congrArg Complex.ofReal h
  simp only [Complex.ofReal_mul,Complex.ofReal_add,Complex.ofReal_one] at hc
  rw [hc]
  unfold criticalNewtonNode
  rw [Complex.ofReal_sub,Complex.ofReal_one]
  ring

private theorem sine_parity_odd (x : ℝ) :
    (Real.sin (2*Real.pi*x) : ℂ)*(Real.sin (Real.pi*x) : ℂ)=
      criticalNewtonNode x*(Real.cos (Real.pi*x) : ℂ) := by
  have h : Real.sin (2*Real.pi*x)*Real.sin (Real.pi*x)=
      (1-Real.cos (2*Real.pi*x))*Real.cos (Real.pi*x) := by
    rw [show 2*Real.pi*x=2*(Real.pi*x) by ring,Real.sin_two_mul,Real.cos_two_mul]
    linear_combination (2*Real.cos (Real.pi*x))*(Real.sin_sq_add_cos_sq (Real.pi*x))
  simpa only [criticalNewtonNode,Complex.ofReal_mul] using congrArg Complex.ofReal h

/-- The original sine multiplier sends the even parity to the exact odd
combination prescribed by the source's full two-parity operator. -/
theorem halfNewtonFunction_sin_even (ε : ℕ+ → ℝ) (i : ℕ) :
    (fun x => (Real.sin (2*Real.pi*x) : ℂ)*halfNewtonFunction ε i false x)=
      (2-criticalNewtonNode (ε ⟨i+1,by omega⟩)) • halfNewtonFunction ε i true-
        halfNewtonFunction ε (i+1) true := by
  funext x
  simp only [halfNewtonFunction,Bool.false_eq_true,ite_false,ite_true,
    halfNewtonProduct_succ,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
  rw [← mul_assoc,sine_parity_even]
  ring

/-- The original sine multiplier sends the odd parity to the exact even
next-level combination. -/
theorem halfNewtonFunction_sin_odd (ε : ℕ+ → ℝ) (i : ℕ) :
    (fun x => (Real.sin (2*Real.pi*x) : ℂ)*halfNewtonFunction ε i true x)=
      halfNewtonFunction ε (i+1) false+
        criticalNewtonNode (ε ⟨i+1,by omega⟩) • halfNewtonFunction ε i false := by
  funext x
  simp only [halfNewtonFunction,Bool.false_eq_true,ite_false,ite_true,
    halfNewtonProduct_succ,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  rw [← mul_assoc,sine_parity_odd]
  ring

/-- Finite algebraic span of every level and both original Newton parities. -/
def halfNewtonSpan (ε : ℕ+ → ℝ) : Submodule ℂ (ℝ → ℂ) :=
  Submodule.span ℂ (Set.range (fun p : ℕ × Bool => halfNewtonFunction ε p.1 p.2))

/-- Every actual Newton function is in the span by construction. -/
theorem halfNewtonFunction_mem_span (ε : ℕ+ → ℝ) (i : ℕ) (e : Bool) :
    halfNewtonFunction ε i e ∈ halfNewtonSpan ε := Submodule.subset_span ⟨(i,e),rfl⟩

/-- The exact Newton coordinate preserves the full finite algebraic span. -/
theorem halfNewtonSpan_mul_node (ε : ℕ+ → ℝ) {f : ℝ → ℂ} (hf : f ∈ halfNewtonSpan ε) :
    (fun x => criticalNewtonNode x*f x) ∈ halfNewtonSpan ε := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨⟨i,e⟩,rfl⟩ := hf
      rw [halfNewtonFunction_mul_node]
      exact (halfNewtonSpan ε).add_mem (halfNewtonFunction_mem_span ε (i+1) e)
        ((halfNewtonSpan ε).smul_mem _ (halfNewtonFunction_mem_span ε i e))
  | zero =>
      simp only [Pi.zero_apply,mul_zero]
      exact (halfNewtonSpan ε).zero_mem
  | add f g _ _ hf hg =>
      convert! (halfNewtonSpan ε).add_mem hf hg using 1
      funext x
      simp only [Pi.add_apply,mul_add]
  | smul a f _ hf =>
      convert! (halfNewtonSpan ε).smul_mem a hf using 1
      funext x
      simp only [Pi.smul_apply,smul_eq_mul]
      ring

/-- The original sine multiplier preserves the whole Newton span, including
both parity branches at every level. -/
theorem halfNewtonSpan_mul_sin (ε : ℕ+ → ℝ) {f : ℝ → ℂ} (hf : f ∈ halfNewtonSpan ε) :
    (fun x => (Real.sin (2*Real.pi*x) : ℂ)*f x) ∈ halfNewtonSpan ε := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨⟨i,e⟩,rfl⟩ := hf
      cases e
      · rw [halfNewtonFunction_sin_even]
        exact (halfNewtonSpan ε).sub_mem
          ((halfNewtonSpan ε).smul_mem _ (halfNewtonFunction_mem_span ε i true))
          (halfNewtonFunction_mem_span ε (i+1) true)
      · rw [halfNewtonFunction_sin_odd]
        exact (halfNewtonSpan ε).add_mem (halfNewtonFunction_mem_span ε (i+1) false)
          ((halfNewtonSpan ε).smul_mem _ (halfNewtonFunction_mem_span ε i false))
  | zero =>
      simp only [Pi.zero_apply,mul_zero]
      exact (halfNewtonSpan ε).zero_mem
  | add f g _ _ hf hg =>
      convert! (halfNewtonSpan ε).add_mem hf hg using 1
      funext x
      simp only [Pi.add_apply,mul_add]
  | smul a f _ hf =>
      convert! (halfNewtonSpan ε).smul_mem a hf using 1
      funext x
      simp only [Pi.smul_apply,smul_eq_mul]
      ring


private theorem character_one_formula (x : ℝ) :
    combModulationCharacter 1 x=1-criticalNewtonNode x+Complex.I*(Real.sin (2*Real.pi*x) : ℂ) := by
  have h : Complex.exp (((2*Real.pi*x : ℝ) : ℂ)*Complex.I)=
      (Real.cos (2*Real.pi*x) : ℂ)+(Real.sin (2*Real.pi*x) : ℂ)*Complex.I := by
    rw [Complex.exp_mul_I]
    simp
  rw [combModulationCharacter,Real.fourierChar_apply,one_mul,h]
  unfold criticalNewtonNode
  rw [Complex.ofReal_sub,Complex.ofReal_one]
  ring

private theorem character_neg_one_formula (x : ℝ) :
    combModulationCharacter (-1) x=1-criticalNewtonNode x-Complex.I*(Real.sin (2*Real.pi*x) : ℂ) := by
  have h : Complex.exp (((-(2*Real.pi*x) : ℝ) : ℂ)*Complex.I)=
      (Real.cos (2*Real.pi*x) : ℂ)-(Real.sin (2*Real.pi*x) : ℂ)*Complex.I := by
    rw [Complex.exp_mul_I]
    simp [sub_eq_add_neg]
  rw [combModulationCharacter,Real.fourierChar_apply,neg_one_mul]
  rw [show 2*Real.pi*(-x)=-(2*Real.pi*x) by ring,h]
  unfold criticalNewtonNode
  rw [Complex.ofReal_sub,Complex.ofReal_one]
  ring

/-- The full Newton span is invariant under one positive integer character. -/
theorem halfNewtonSpan_mul_character_one (ε : ℕ+ → ℝ) {f : ℝ → ℂ} (hf : f ∈ halfNewtonSpan ε) :
    (fun x => combModulationCharacter 1 x*f x) ∈ halfNewtonSpan ε := by
  have he : (fun x => combModulationCharacter 1 x*f x)=
      (f-(fun x => criticalNewtonNode x*f x))+
        Complex.I • (fun x => (Real.sin (2*Real.pi*x) : ℂ)*f x) := by
    funext x
    rw [character_one_formula]
    simp only [Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
    ring
  rw [he]
  exact (halfNewtonSpan ε).add_mem ((halfNewtonSpan ε).sub_mem hf (halfNewtonSpan_mul_node ε hf))
    ((halfNewtonSpan ε).smul_mem _ (halfNewtonSpan_mul_sin ε hf))

/-- The negative character also preserves the full span, so no frequency arm
is lost by a one-sided induction. -/
theorem halfNewtonSpan_mul_character_neg_one (ε : ℕ+ → ℝ) {f : ℝ → ℂ} (hf : f ∈ halfNewtonSpan ε) :
    (fun x => combModulationCharacter (-1) x*f x) ∈ halfNewtonSpan ε := by
  have he : (fun x => combModulationCharacter (-1) x*f x)=
      (f-(fun x => criticalNewtonNode x*f x))-
        Complex.I • (fun x => (Real.sin (2*Real.pi*x) : ℂ)*f x) := by
    funext x
    rw [character_neg_one_formula]
    simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
    ring
  rw [he]
  exact (halfNewtonSpan ε).sub_mem ((halfNewtonSpan ε).sub_mem hf (halfNewtonSpan_mul_node ε hf))
    ((halfNewtonSpan ε).smul_mem _ (halfNewtonSpan_mul_sin ε hf))

private theorem character_add (a b x : ℝ) :
    combModulationCharacter (a+b) x=combModulationCharacter a x*combModulationCharacter b x := by
  unfold combModulationCharacter
  rw [add_mul,AddChar.map_add_eq_mul,Circle.coe_mul]

/-- The initial positive half-character is exactly the two zeroth parities. -/
theorem halfNewtonSpan_half_character (ε : ℕ+ → ℝ) :
    (fun x => combModulationCharacter (1/2) x) ∈ halfNewtonSpan ε := by
  have he : (fun x => combModulationCharacter (1/2) x)=
      halfNewtonFunction ε 0 false+Complex.I • halfNewtonFunction ε 0 true := by
    funext x
    have h : Complex.exp (((Real.pi*x : ℝ) : ℂ)*Complex.I)=
        (Real.cos (Real.pi*x) : ℂ)+(Real.sin (Real.pi*x) : ℂ)*Complex.I := by
      rw [Complex.exp_mul_I]
      simp
    rw [combModulationCharacter,Real.fourierChar_apply]
    rw [show 2*Real.pi*(1/2*x)=Real.pi*x by ring,h]
    simp only [halfNewtonFunction,halfNewtonProduct,Finset.range_zero,Finset.prod_empty,
      Bool.false_eq_true,ite_false,ite_true,mul_one,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    ring
  rw [he]
  exact (halfNewtonSpan ε).add_mem (halfNewtonFunction_mem_span ε 0 false)
    ((halfNewtonSpan ε).smul_mem _ (halfNewtonFunction_mem_span ε 0 true))

/-- Every positive and negative half-integer Fourier character belongs to the
finite algebraic span of the exact source Newton functions, without any node
separation or inverse interpolation premise. -/
theorem halfNewtonSpan_all_half_characters (ε : ℕ+ → ℝ) (n : ℤ) :
    (fun x => combModulationCharacter ((n : ℝ)+1/2) x) ∈ halfNewtonSpan ε := by
  induction n using Int.induction_on with
  | zero => simpa only [Int.cast_zero,zero_add] using halfNewtonSpan_half_character ε
  | succ n ih =>
      have h := halfNewtonSpan_mul_character_one ε ih
      convert! h using 1
      funext x
      rw [← character_add]
      congr 1
      push_cast
      ring
  | pred n ih =>
      have h := halfNewtonSpan_mul_character_neg_one ε ih
      convert! h using 1
      funext x
      rw [← character_add]
      congr 1
      push_cast
      ring

end
end MeyerGeneralProblem.Adaptive
