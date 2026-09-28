module

public import MeyerGeneralProblem.Cardinal.Adaptive.TensorNewtonInterpolation
public import Mathlib.Algebra.Polynomial.Expand
import all Mathlib.Algebra.Polynomial.Expand

@[expose] public section

/-! # Signed parity identities for the finite Newton chart

The signed-grid route retains exact endpoint reconstruction and avoids assigning
an odd quotient at zero where its multiplying basis already vanishes.
-/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open Polynomial Set

/-- The highest coefficient of a Newton sum is its final Newton coordinate. -/
theorem coeff_last_newtonInterpolant (n : ℕ) (nodes : Fin (n+1) → ℂ) (v : Fin (n+1) → ℂ) :
    (newtonInterpolant nodes v).coeff n = v (Fin.last n) := by
  rw [newtonInterpolant_eq_sum,finsetSum_coeff]
  simp only [coeff_C_mul]
  rw [Finset.sum_eq_single (Fin.last n)]
  · have hc := (monic_newtonBasisPolynomial nodes (Fin.last n)).leadingCoeff
    change (newtonBasisPolynomial nodes (Fin.last n)).coeff
      (newtonBasisPolynomial nodes (Fin.last n)).natDegree = 1 at hc
    rw [natDegree_newtonBasisPolynomial,Fin.val_last] at hc
    rw [hc,mul_one]
  · intro i _ hi
    have hin : i.val < n := by have := i.isLt; have hne : i.val ≠ n := fun he => hi (Fin.ext he); omega
    rw [coeff_eq_zero_of_natDegree_lt (by rw [natDegree_newtonBasisPolynomial]; exact hin),mul_zero]
  · intro hn
    exact (hn (Finset.mem_univ _)).elim

/-- A degree-bounded polynomial has its highest divided difference equal to its
ordinary highest coefficient, for arbitrary nodes including repeated ones. -/
theorem polynomialDividedDifference_eq_coeff (nodes : ℕ → ℂ) (n : ℕ) (P : ℂ[X])
    (hP : P ∈ Polynomial.degreeLT ℂ (n+1)) : polynomialDividedDifference nodes n P = P.coeff n := by
  have he := confluentNewtonInterpolant_own_data nodes (⟨P,hP⟩ : Polynomial.degreeLT ℂ (n+1))
  rw [confluentNewtonInterpolant_eq_newtonInterpolant] at he
  have hc := congrArg (fun Q : ℂ[X] => Q.coeff n) he
  rw [coeff_last_newtonInterpolant] at hc
  exact hc

/-- A coordinate square doubles the degree while preserving the corresponding
leading divided difference coefficient. -/
theorem polynomialDividedDifference_square (nodes : ℕ → ℂ) (n : ℕ) (P : ℂ[X])
    (hP : P.natDegree ≤ n) :
    polynomialDividedDifference nodes (2*n) (Polynomial.expand ℂ 2 P) = P.coeff n := by
  rw [polynomialDividedDifference_eq_coeff]
  · exact coeff_expand_mul' (by norm_num : 0 < 2) P n
  · apply Polynomial.mem_degreeLT.mpr
    apply lt_of_le_of_lt Polynomial.degree_le_natDegree
    exact_mod_cast (show (Polynomial.expand ℂ 2 P).natDegree < 2*n+1 by
      rw [natDegree_expand]
      omega)

/-- The odd square lift retains the same top coefficient at order `2n+1`. -/
theorem polynomialDividedDifference_odd_square (nodes : ℕ → ℂ) (n : ℕ) (P : ℂ[X])
    (hP : P.natDegree ≤ n) :
    polynomialDividedDifference nodes (2*n+1) (Polynomial.expand ℂ 2 P * X) = P.coeff n := by
  rw [polynomialDividedDifference_eq_coeff]
  · rw [coeff_mul_X]
    exact coeff_expand_mul' (by norm_num : 0 < 2) P n
  · apply Polynomial.mem_degreeLT.mpr
    apply lt_of_le_of_lt Polynomial.degree_le_natDegree
    have hd := Polynomial.natDegree_mul_le (p := Polynomial.expand ℂ 2 P) (q := (X : ℂ[X]))
    rw [natDegree_expand,natDegree_X] at hd
    exact_mod_cast (show (Polynomial.expand ℂ 2 P * X).natDegree < 2*n+1+1 by omega)

/-- The signed enumeration has one positive then one negative copy of each radius. -/
def signedNewtonNode (r : ℕ → ℝ) (j : ℕ) : ℝ :=
  if j%2=0 then r (j/2) else -r (j/2)

/-- Even positions carry the original radius. -/
@[simp] theorem signedNewtonNode_even (r : ℕ → ℝ) (j : ℕ) :
    signedNewtonNode r (2*j) = r j := by simp [signedNewtonNode]

/-- Odd positions carry its negative. -/
@[simp] theorem signedNewtonNode_odd (r : ℕ → ℝ) (j : ℕ) :
    signedNewtonNode r (2*j+1) = -r j := by
  simp [signedNewtonNode,Nat.add_div]

/-- Squaring the signed enumeration forgets only its sign. -/
theorem signedNewtonNode_sq (r : ℕ → ℝ) (j : ℕ) :
    signedNewtonNode r j ^ 2 = r (j/2)^2 := by
  unfold signedNewtonNode
  split_ifs <;> ring

/-- A decreasing nonnegative radius prefix gives distinct even signed nodes,
including a possible single terminal zero. -/
theorem signedNewtonNode_distinct_even (r : ℕ → ℝ) (n : ℕ)
    (hnonneg : ∀ j ≤ n, 0 ≤ r j)
    (hanti : ∀ i j, i < j → j ≤ n → r j < r i) :
    ∀ i ≤ 2*n, ∀ j ≤ 2*n, i ≠ j → signedNewtonNode r i ≠ signedNewtonNode r j := by
  intro i hi j hj hij he
  have hsq := congrArg (fun x : ℝ => x^2) he
  simp only [signedNewtonNode_sq] at hsq
  have hri := hnonneg (i/2) (by omega)
  have hrj := hnonneg (j/2) (by omega)
  have hr : r (i/2) = r (j/2) := by nlinarith
  have hind : i/2 = j/2 := by
    rcases lt_trichotomy (i/2) (j/2) with hh|hh|hh
    · exact ((hanti _ _ hh (by omega)).ne hr.symm).elim
    · exact hh
    · exact ((hanti _ _ hh (by omega)).ne hr).elim
  have hmod : i%2 ≠ j%2 := by omega
  have hrpos : 0 < r (i/2) := by
    have hn : i/2 < n := by omega
    exact (hnonneg n le_rfl).trans_lt (hanti _ _ hn le_rfl)
  unfold signedNewtonNode at he
  split_ifs at he <;> simp only [hind] at he <;> first | omega | nlinarith

/-- With a strictly positive last radius, the final negative node is distinct too. -/
theorem signedNewtonNode_distinct_odd (r : ℕ → ℝ) (n : ℕ)
    (hpos : ∀ j ≤ n, 0 < r j)
    (hanti : ∀ i j, i < j → j ≤ n → r j < r i) :
    ∀ i ≤ 2*n+1, ∀ j ≤ 2*n+1, i ≠ j → signedNewtonNode r i ≠ signedNewtonNode r j := by
  intro i hi j hj hij he
  have hsq := congrArg (fun x : ℝ => x^2) he
  simp only [signedNewtonNode_sq] at hsq
  have hri := hpos (i/2) (by omega)
  have hrj := hpos (j/2) (by omega)
  have hr : r (i/2) = r (j/2) := by nlinarith
  have hind : i/2 = j/2 := by
    rcases lt_trichotomy (i/2) (j/2) with hh|hh|hh
    · exact ((hanti _ _ hh (by omega)).ne hr.symm).elim
    · exact hh
    · exact ((hanti _ _ hh (by omega)).ne hr).elim
  have hmod : i%2 ≠ j%2 := by omega
  unfold signedNewtonNode at he
  split_ifs at he <;> simp only [hind] at he <;> first | omega | nlinarith

/-- Distinct finite interpolation turns an analytic divided difference into the
highest coefficient of any agreeing polynomial of the stated degree. -/
theorem analyticDividedDifference_eq_coeff_of_interpolation (nodes : ℕ → ℝ) (n : ℕ)
    (f : ℝ → ℂ) (P : ℂ[X]) (hP : P ∈ Polynomial.degreeLT ℂ (n+1))
    (hd : ∀ i ≤ n, ∀ j ≤ n, i ≠ j → nodes i ≠ nodes j)
    (hv : ∀ j ≤ n, f (nodes j) = P.eval (nodes j:ℂ)) :
    analyticDividedDifference nodes n f = P.coeff n := by
  rw [analyticDividedDifference_congr_values_of_distinct nodes n f (fun x => P.eval (x:ℂ)) hd hv,
    analyticDividedDifference_polynomial_eval,polynomialDividedDifference_eq_coeff _ _ _ hP]

/-- A degree below `n+1` also bounds the natural degree by `n`, including zero. -/
theorem natDegree_le_of_mem_degreeLT_succ {n : ℕ} {P : ℂ[X]}
    (hP : P ∈ Polynomial.degreeLT ℂ (n+1)) : P.natDegree ≤ n := by
  by_cases hz : P=0
  · simp [hz]
  · have := (Polynomial.natDegree_lt_iff_degree_lt hz).mpr (Polynomial.mem_degreeLT.mp hP)
    omega

/-- The square-node divided difference is exactly the even signed-node divided
difference; the last radius may equal zero. -/
theorem analyticDividedDifference_square_signed_even (r : ℕ → ℝ) (n : ℕ)
    (hnonneg : ∀ j ≤ n, 0 ≤ r j)
    (hanti : ∀ i j, i < j → j ≤ n → r j < r i)
    (G h : ℝ → ℂ)
    (hv : ∀ j ≤ 2*n, h (signedNewtonNode r j) = G (r (j/2)^2)) :
    analyticDividedDifference (fun j => r j^2) n G =
      analyticDividedDifference (signedNewtonNode r) (2*n) h := by
  have hd : ∀ i ≤ n, ∀ j ≤ n, i ≠ j → r i^2 ≠ r j^2 := by
    intro i hi j hj hij he
    have hri := hnonneg i hi
    have hrj := hnonneg j hj
    have he' : r i=r j := by nlinarith
    rcases lt_or_gt_of_ne hij with hij|hji
    · exact (hanti i j hij hj).ne he'.symm
    · exact (hanti j i hji hi).ne he'
  let xs : Fin (n+1) → ℝ := fun i => r i^2
  have hx : Function.Injective xs := by
    intro i j he
    apply Fin.ext
    by_contra hh
    exact hd i (by omega) j (by omega) hh he
  let z : Fin (n+1) → ℂ := fun i => (xs i:ℂ)
  let hz : Function.Injective z := Complex.ofReal_injective.comp hx
  let P := newtonInterpolantFromValues z hz (fun i => G (xs i))
  have hP : P ∈ Polynomial.degreeLT ℂ (n+1) :=
    newtonInterpolant_mem_degreeLT z _
  have hpv (j : ℕ) (hj : j ≤ n) : G (r j^2)=P.eval ((r j^2:ℝ):ℂ) :=
    (eval_newtonInterpolantFromValues_at_node z hz (fun i => G (xs i)) ⟨j,by omega⟩).symm
  rw [analyticDividedDifference_eq_coeff_of_interpolation _ n G P hP hd hpv]
  have hsp : ∀ j ≤ 2*n, h (signedNewtonNode r j)=
      (Polynomial.expand ℂ 2 P).eval (signedNewtonNode r j:ℂ) := by
    intro j hj
    rw [hv j hj,hpv (j/2) (by omega),Polynomial.expand_eval]
    congr 1
    norm_cast
    exact (signedNewtonNode_sq r j).symm
  rw [analyticDividedDifference_congr_values_of_distinct _ _ h (fun x => (Polynomial.expand ℂ 2 P).eval (x:ℂ))
    (signedNewtonNode_distinct_even r n hnonneg hanti) hsp,
    analyticDividedDifference_polynomial_eval,
    polynomialDividedDifference_square _ n P (natDegree_le_of_mem_degreeLT_succ hP)]

/-- The square-node divided difference is exactly the odd signed-node divided
difference after multiplication by the signed coordinate. -/
theorem analyticDividedDifference_square_signed_odd (r : ℕ → ℝ) (n : ℕ)
    (hpos : ∀ j ≤ n, 0 < r j)
    (hanti : ∀ i j, i < j → j ≤ n → r j < r i)
    (G h : ℝ → ℂ)
    (hv : ∀ j ≤ 2*n+1, h (signedNewtonNode r j) =
      G (r (j/2)^2)*(signedNewtonNode r j:ℂ)) :
    analyticDividedDifference (fun j => r j^2) n G =
      analyticDividedDifference (signedNewtonNode r) (2*n+1) h := by
  have hd : ∀ i ≤ n, ∀ j ≤ n, i ≠ j → r i^2 ≠ r j^2 := by
    intro i hi j hj hij he
    have hri := hpos i hi
    have hrj := hpos j hj
    have he' : r i=r j := by nlinarith
    rcases lt_or_gt_of_ne hij with hij|hji
    · exact (hanti i j hij hj).ne he'.symm
    · exact (hanti j i hji hi).ne he'
  let xs : Fin (n+1) → ℝ := fun i => r i^2
  have hx : Function.Injective xs := by
    intro i j he
    apply Fin.ext
    by_contra hh
    exact hd i (by omega) j (by omega) hh he
  let z : Fin (n+1) → ℂ := fun i => (xs i:ℂ)
  let hz : Function.Injective z := Complex.ofReal_injective.comp hx
  let P := newtonInterpolantFromValues z hz (fun i => G (xs i))
  have hP : P ∈ Polynomial.degreeLT ℂ (n+1) :=
    newtonInterpolant_mem_degreeLT z _
  have hpv (j : ℕ) (hj : j ≤ n) : G (r j^2)=P.eval ((r j^2:ℝ):ℂ) :=
    (eval_newtonInterpolantFromValues_at_node z hz (fun i => G (xs i)) ⟨j,by omega⟩).symm
  rw [analyticDividedDifference_eq_coeff_of_interpolation _ n G P hP hd hpv]
  have hsp : ∀ j ≤ 2*n+1, h (signedNewtonNode r j)=
      (Polynomial.expand ℂ 2 P * X).eval (signedNewtonNode r j:ℂ) := by
    intro j hj
    rw [hv j hj,hpv (j/2) (by omega),Polynomial.eval_mul,Polynomial.eval_X,Polynomial.expand_eval]
    congr 2
    norm_cast
    exact (signedNewtonNode_sq r j).symm
  rw [analyticDividedDifference_congr_values_of_distinct _ _ h (fun x => (Polynomial.expand ℂ 2 P * X).eval (x:ℂ))
    (signedNewtonNode_distinct_odd r n hpos hanti) hsp,
    analyticDividedDifference_polynomial_eval,
    polynomialDividedDifference_odd_square _ n P (natDegree_le_of_mem_degreeLT_succ hP)]

/-- Every signed radius lies in the symmetric interval determined by the first. -/
theorem signedNewtonNode_mem_Icc (r : ℕ → ℝ) (n j : ℕ)
    (hnonneg : ∀ k ≤ n, 0 ≤ r k)
    (hanti : ∀ i k, i < k → k ≤ n → r k < r i) (hj : j/2 ≤ n) :
    signedNewtonNode r j ∈ Icc (-(r 0)) (r 0) := by
  have hk := hnonneg (j/2) hj
  have hupper : r (j/2) ≤ r 0 := by
    by_cases hh : j/2=0
    · simp [hh]
    · exact (hanti 0 (j/2) (by omega) hj).le
  unfold signedNewtonNode
  split_ifs <;> constructor <;> linarith

/-- The even square coefficient costs exactly `2n` derivatives of the signed
chart, with no derivative assumed for its quotient as a function of the square. -/
theorem norm_square_dividedDifference_even (r : ℕ → ℝ) (n : ℕ)
    (hnonneg : ∀ j ≤ n, 0 ≤ r j)
    (hanti : ∀ i j, i < j → j ≤ n → r j < r i)
    (G h : ℝ → ℂ) (hv : ∀ j ≤ 2*n, h (signedNewtonNode r j) = G (r (j/2)^2))
    (hh : ContDiff ℝ (2*n) h) (A : ℝ)
    (hbound : ∀ x ∈ Icc (-(r 0)) (r 0), ‖iteratedDeriv (2*n) h x‖ ≤ A) :
    ‖analyticDividedDifference (fun j => r j^2) n G‖ ≤ A / ((2*n).factorial:ℝ) := by
  rw [analyticDividedDifference_square_signed_even r n hnonneg hanti G h hv]
  exact norm_analyticDividedDifference_le_of_contDiff _ _ hh
    (fun j hj => signedNewtonNode_mem_Icc r n j hnonneg hanti (by change j ≤ 2*n at hj; omega)) hbound

/-- The odd square coefficient costs exactly `2n+1` derivatives of its signed
chart. It requires only the positive nodes where the quotient is tested. -/
theorem norm_square_dividedDifference_odd (r : ℕ → ℝ) (n : ℕ)
    (hpos : ∀ j ≤ n, 0 < r j)
    (hanti : ∀ i j, i < j → j ≤ n → r j < r i)
    (G h : ℝ → ℂ)
    (hv : ∀ j ≤ 2*n+1, h (signedNewtonNode r j) = G (r (j/2)^2)*(signedNewtonNode r j:ℂ))
    (hh : ContDiff ℝ (2*n+1) h) (A : ℝ)
    (hbound : ∀ x ∈ Icc (-(r 0)) (r 0), ‖iteratedDeriv (2*n+1) h x‖ ≤ A) :
    ‖analyticDividedDifference (fun j => r j^2) n G‖ ≤ A / ((2*n+1).factorial:ℝ) := by
  rw [analyticDividedDifference_square_signed_odd r n hpos hanti G h hv]
  exact norm_analyticDividedDifference_le_of_contDiff _ _ hh
    (fun j hj => signedNewtonNode_mem_Icc r n j (fun k hk => (hpos k hk).le) hanti (by change j ≤ 2*n+1 at hj; omega)) hbound

/-- Even and odd projections use only the two actual signed values. -/
def signParityPiece (odd : Bool) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  (f x + (if odd then (-1:ℂ) else 1)*f (-x))/2

/-- The two signed parity pieces reconstruct the function exactly. -/
theorem signParityPiece_sum (f : ℝ → ℂ) (x : ℝ) :
    signParityPiece false f x + signParityPiece true f x = f x := by
  simp only [signParityPiece,Bool.false_eq_true,ite_false,ite_true]
  ring

/-- The odd piece is exactly zero at the single endpoint. -/
theorem signParityPiece_odd_zero (f : ℝ → ℂ) : signParityPiece true f 0 = 0 := by
  simp only [signParityPiece,ite_true,neg_zero]
  ring

/-- Reversing the coordinate acts by the exact parity sign. -/
theorem signParityPiece_neg (odd : Bool) (f : ℝ → ℂ) (x : ℝ) :
    signParityPiece odd f (-x) = (if odd then (-1:ℂ) else 1)*signParityPiece odd f x := by
  cases odd <;> simp only [signParityPiece,Bool.false_eq_true,ite_false,ite_true,neg_neg] <;> ring

/-- The literal cosine/sine basis in the accepted characteristic chart. -/
def parityTrigFactor (odd : Bool) (x : ℝ) : ℂ :=
  if odd then (Real.sin (Real.pi*x):ℂ) else (Real.cos (Real.pi*x):ℂ)

/-- Finite-grid quotient values. The terminal odd value is zero because its basis
vanishes there; it is never used to define an analytic extension. -/
def parityGridQuotient (odd : Bool) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  if odd ∧ x=0 then 0 else signParityPiece odd f x / parityTrigFactor odd x

/-- Reconstruction is exact at every admissible signed point and at the endpoint. -/
theorem parityGridQuotient_reconstruct (odd : Bool) (f : ℝ → ℂ) (x : ℝ)
    (hnz : ¬(odd ∧ x=0) → parityTrigFactor odd x ≠ 0) :
    parityTrigFactor odd x * parityGridQuotient odd f x = signParityPiece odd f x := by
  by_cases hz : odd ∧ x=0
  · rcases hz with ⟨ho,rfl⟩
    simp only [ho,parityGridQuotient,ite_true,and_self,mul_zero,signParityPiece_odd_zero]
  · rw [parityGridQuotient,ite_eq_right hz,mul_div_cancel₀ _ (hnz hz)]

/-- The literal trigonometric factors have the requested parity. -/
theorem parityTrigFactor_neg (odd : Bool) (x : ℝ) :
    parityTrigFactor odd (-x)=(if odd then (-1:ℂ) else 1)*parityTrigFactor odd x := by
  cases odd <;> simp [parityTrigFactor,Real.sin_neg,Real.cos_neg]

/-- Each finite quotient is even, including its explicitly assigned odd endpoint. -/
theorem parityGridQuotient_neg (odd : Bool) (f : ℝ → ℂ) (x : ℝ) :
    parityGridQuotient odd f (-x)=parityGridQuotient odd f x := by
  by_cases hx : x=0
  · simp [hx]
  · have hnx : -x ≠ 0 := neg_ne_zero.mpr hx
    simp only [parityGridQuotient,hx,hnx,and_false,ite_false,
      signParityPiece_neg,parityTrigFactor_neg]
    cases odd <;> simp

/-- Finite quotient data in the two characteristic coordinates. -/
def tensorParityGridQuotient (e d : Bool) (f : ℝ → ℝ → ℂ) (x y : ℝ) : ℂ :=
  parityGridQuotient e (fun u => parityGridQuotient d (f u) y) x

/-- The four parity terms reconstruct every admissible point, including either
zero coordinate. This identity is independent of any smooth extension. -/
theorem tensorParityGridQuotient_reconstruct (f : ℝ → ℝ → ℂ) (x y : ℝ)
    (hx : ∀ e : Bool, ¬(e ∧ x=0) → parityTrigFactor e x ≠ 0)
    (hy : ∀ d : Bool, ¬(d ∧ y=0) → parityTrigFactor d y ≠ 0) :
    (∑ e : Bool, ∑ d : Bool,
      parityTrigFactor e x * parityTrigFactor d y * tensorParityGridQuotient e d f x y)=f x y := by
  rw [Finset.sum_comm]
  have hrow (d : Bool) : (∑ e : Bool, parityTrigFactor e x * parityTrigFactor d y *
      tensorParityGridQuotient e d f x y) = parityTrigFactor d y * parityGridQuotient d (f x) y := by
    simp_rw [show ∀ e, parityTrigFactor e x * parityTrigFactor d y * tensorParityGridQuotient e d f x y =
      parityTrigFactor d y * (parityTrigFactor e x * parityGridQuotient e
        (fun u => parityGridQuotient d (f u) y) x) by intro e; unfold tensorParityGridQuotient; ring]
    simp_rw [parityGridQuotient_reconstruct _ _ _ (hx _)]
    rw [← Finset.mul_sum,Fintype.sum_bool,add_comm,signParityPiece_sum]
  simp_rw [hrow,parityGridQuotient_reconstruct _ _ _ (hy _)]
  rw [Fintype.sum_bool,add_comm,signParityPiece_sum]

/-- The accepted characteristic coordinate is exactly twice the squared sine. -/
def parityNewtonCoordinate (x : ℝ) : ℝ := 1-Real.cos (2*Real.pi*x)

/-- The sine-square chart keeps the literal source coordinate. -/
theorem parityNewtonCoordinate_eq (x : ℝ) :
    parityNewtonCoordinate x = 2*Real.sin (Real.pi*x)^2 := by
  unfold parityNewtonCoordinate
  rw [show 2*Real.pi*x=2*(Real.pi*x) by ring,Real.cos_two_mul]
  nlinarith [Real.sin_sq_add_cos_sq (Real.pi*x)]

/-- The Newton coordinate identifies the two signed points exactly. -/
@[simp] theorem parityNewtonCoordinate_neg (x : ℝ) :
    parityNewtonCoordinate (-x)=parityNewtonCoordinate x := by
  simp only [parityNewtonCoordinate_eq,mul_neg,Real.sin_neg,neg_sq]

/-- The terminal odd Newton factor vanishes at every signed radius and at zero. -/
theorem terminal_odd_newton_factor_zero (k : ℕ) (r : Fin k → ℝ) (x : ℝ)
    (hx : x=0 ∨ ∃ j, x=r j ∨ x= -r j) :
    (x:ℂ)*(∏ j : Fin k, ((x:ℂ)^2-(r j:ℂ)^2))=0 := by
  rcases hx with rfl|⟨j,hj⟩
  · simp
  · have hz : (∏ a : Fin k, ((x:ℂ)^2-(r a:ℂ)^2))=0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      rcases hj with rfl|rfl <;> simp
    rw [hz,mul_zero]


end
end MeyerGeneralProblem.Adaptive
