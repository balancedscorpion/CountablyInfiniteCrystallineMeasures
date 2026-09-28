module

public import MeyerGeneralProblem.Cardinal.Adaptive.ActualHoleExchange
public import Mathlib.Algebra.LinearRecurrence
import all Mathlib.Algebra.LinearRecurrence
public import Mathlib.LinearAlgebra.Lagrange
import all Mathlib.LinearAlgebra.Lagrange

@[expose] public section

/-! # Simple unit-root recurrence bound for critical head inversion

This module supplies the scalar boundedness step of the complete critical-head
inverse. It does not yet construct the cutoff Green operator on Schwartz space.
-/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open scoped BigOperators

/-- Every solution of a recurrence with a complete distinct unit-root spectrum
is a finite character sum, hence bounded uniformly in the time index. -/
theorem recurrence_unit_roots_bounded (E : LinearRecurrence ℂ)
    (z : Fin E.order → ℂ) (hz : Function.Injective z)
    (hroot : ∀ i, E.charPoly.IsRoot (z i)) (hunit : ∀ i, ‖z i‖ = 1)
    (u : ℕ → ℂ) (hu : E.IsSolution u) :
    ∃ a : Fin E.order → ℂ, (∀ n, u n = ∑ i, a i * z i ^ n) ∧
      ∀ n, ‖u n‖ ≤ ∑ i, ‖a i‖ := by
  let M := (Matrix.vandermonde z).transpose
  have hM : IsUnit M := by
    apply (Matrix.isUnit_iff_isUnit_det M).mpr
    apply isUnit_iff_ne_zero.mpr
    rw [Matrix.det_transpose]
    exact Matrix.det_vandermonde_ne_zero_iff.mpr hz
  obtain ⟨a,ha⟩ := (Matrix.mulVec_surjective_iff_isUnit.mpr hM) (fun i => u i)
  have hsol : E.IsSolution (fun n => ∑ i, a i * z i ^ n) := by
    have hh : (∑ i, a i • (fun n : ℕ => z i ^ n)) ∈ E.solSpace := by
      apply Submodule.sum_mem
      intro i _
      exact E.solSpace.smul_mem (a i) ((E.geom_sol_iff_root_charPoly (z i)).mpr (hroot i))
    change E.IsSolution _ at hh
    convert hh using 1
    ext n
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have heq : u = (fun n => ∑ i, a i * z i ^ n) := by
    apply (E.eq_iff_eqOn_range_order u _ hu hsol).mpr
    intro n hn
    have hn' : n < E.order := Finset.mem_range.mp hn
    have hh := congrFun ha ⟨n,hn'⟩
    change (∑ i, z i ^ n * a i) = u n at hh
    simpa only [mul_comm] using hh.symm
  refine ⟨a,fun n => congrFun heq n,?_⟩
  intro n
  rw [heq]
  exact (norm_sum_le _ _).trans_eq (by simp only [norm_mul,norm_pow,hunit,one_pow,mul_one])

/-- The monic recurrence whose characteristic polynomial is the actual product
of the supplied linear root factors. -/
def rootProductRecurrence {d : ℕ} (z : Fin d → ℂ) : LinearRecurrence ℂ where
  order := d
  coeffs i := -(Lagrange.nodal Finset.univ z).coeff i

/-- Exact identification of the recurrence symbol, with no root certificate. -/
theorem rootProductRecurrence_charPoly {d : ℕ} (z : Fin d → ℂ) :
    (rootProductRecurrence z).charPoly = Lagrange.nodal Finset.univ z := by
  let Q := Lagrange.nodal Finset.univ z
  have hd : Q.natDegree = d := by simp [Q,Lagrange.natDegree_nodal]
  have hm : Q.Monic := Lagrange.nodal_monic
  have hh := Q.as_sum_range
  rw [hd,Finset.sum_range_succ,← Fin.sum_univ_eq_sum_range] at hh
  rw [show Q.coeff d = 1 from hd ▸ hm.coeff_natDegree] at hh
  change Polynomial.monomial d 1 - ∑ i : Fin d, Polynomial.monomial i (-Q.coeff i) = Q
  conv_rhs => rw [hh]
  simp only [Polynomial.monomial_neg,Finset.sum_neg_distrib,sub_neg_eq_add]
  exact add_comm _ _

/-- All initial data have bounded solutions for a product of distinct unit
roots, with a finite constant depending on the roots and initial data. -/
theorem rootProductRecurrence_bounded {d : ℕ} (z : Fin d → ℂ)
    (hz : Function.Injective z) (hunit : ∀ i, ‖z i‖ = 1)
    (init : Fin d → ℂ) :
    ∃ C : ℝ, ∀ n, ‖(rootProductRecurrence z).mkSol init n‖ ≤ C := by
  obtain ⟨a,_,ha⟩ := recurrence_unit_roots_bounded (rootProductRecurrence z) z hz
    (fun i => by
      rw [rootProductRecurrence_charPoly]
      exact Lagrange.eval_nodal_at_node (Finset.mem_univ i)) hunit _
    ((rootProductRecurrence z).is_sol_mkSol init)
  exact ⟨∑ i, ‖a i‖,ha⟩


/-- Fundamental solution of the product recurrence: zero before the origin,
with the initial impulse in the last of its d initial slots. -/
def rootForwardGreen {d : ℕ} (z : Fin d → ℂ) (n : ℤ) : ℂ :=
  if 0 ≤ n then
    (rootProductRecurrence z).mkSol (fun i => if i.val+1 = d then 1 else 0) n.toNat
  else 0

/-- All earlier cells vanish, including the entire negative half-line. -/
theorem rootForwardGreen_eq_zero {d : ℕ} (z : Fin d → ℂ) (n : ℤ)
    (hn : n < (d : ℤ)-1) : rootForwardGreen z n = 0 := by
  unfold rootForwardGreen
  split_ifs with h
  · have hn' : n.toNat < d := by omega
    have he := (rootProductRecurrence z).mkSol_eq_init
      (fun i => if i.val+1=d then 1 else 0) ⟨n.toNat,hn'⟩
    simpa [show ¬ n.toNat+1=d by omega] using he
  · rfl

/-- The first nonzero coefficient has exactly unit amplitude. -/
theorem rootForwardGreen_first {d : ℕ} (hd : 1 ≤ d) (z : Fin d → ℂ) :
    rootForwardGreen z ((d : ℤ)-1) = 1 := by
  unfold rootForwardGreen
  rw [ite_eq_left (by omega)]
  have hn : ((d : ℤ)-1).toNat = d-1 := by omega
  rw [hn]
  have he := (rootProductRecurrence z).mkSol_eq_init
    (fun i => if i.val+1=d then 1 else 0) ⟨d-1,show d-1 < d by omega⟩
  simpa [show d-1+1=d by omega] using he

/-- The full characteristic equation holds for every nonnegative cell. -/
theorem rootForwardGreen_recurrence {d : ℕ} (z : Fin d → ℂ) (n : ℕ) :
    ∑ i : Fin (d+1), (Lagrange.nodal Finset.univ z).coeff i *
      rootForwardGreen z ((n : ℤ)+(i : ℤ)) = 0 := by
  have htop : (Lagrange.nodal Finset.univ z).coeff d = 1 := by
    simpa using (Lagrange.nodal_monic (s := Finset.univ) (v := z)).coeff_natDegree
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc,Fin.val_last,htop,one_mul]
  have hs := (rootProductRecurrence z).is_sol_mkSol
    (fun i => if i.val+1=d then 1 else 0) n
  change _ = ∑ i : Fin d, -(Lagrange.nodal Finset.univ z).coeff i * _ at hs
  simp only [neg_mul,Finset.sum_neg_distrib] at hs
  simp only [rootForwardGreen, ← Int.natCast_add,Int.natCast_nonneg,ite_true,Int.toNat_natCast]
  have hs' : (rootProductRecurrence z).mkSol
      (fun i => if i.val+1=d then 1 else 0) (n+d) =
      -∑ i : Fin d, (Lagrange.nodal Finset.univ z).coeff i *
        (rootProductRecurrence z).mkSol (fun i => if i.val+1=d then 1 else 0) (n+i) := hs
  rw [hs']
  exact add_neg_cancel _

/-- The characteristic convolution gives one exact impulse, with no boundary
condition at infinity and no summability assertion for the Green sequence. -/
theorem rootForwardGreen_impulse {d : ℕ} (hd : 1 ≤ d) (z : Fin d → ℂ) (n : ℤ) :
    ∑ i : Fin (d+1), (Lagrange.nodal Finset.univ z).coeff i *
      rootForwardGreen z (n+(i : ℤ)) = if n = -1 then 1 else 0 := by
  by_cases hn : 0 ≤ n
  · have he := rootForwardGreen_recurrence z n.toNat
    rw [Int.toNat_of_nonneg hn] at he
    simpa [show n ≠ -1 by omega] using he
  · by_cases he : n = -1
    · subst n
      rw [ite_eq_left rfl,Fin.sum_univ_castSucc]
      have hs : (∑ i : Fin d, (Lagrange.nodal Finset.univ z).coeff i *
          rootForwardGreen z (-1+(i : ℤ))) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        rw [rootForwardGreen_eq_zero z _ (by have := i.isLt; omega),mul_zero]
      simp only [Fin.val_castSucc,Fin.val_last] at *
      rw [hs,zero_add,show (-1 : ℤ)+d=d-1 by omega,rootForwardGreen_first hd]
      simpa using (Lagrange.nodal_monic (s := Finset.univ) (v := z)).coeff_natDegree
    · rw [ite_eq_right he]
      apply Finset.sum_eq_zero
      intro i _
      rw [rootForwardGreen_eq_zero z _ (by have := i.isLt; omega),mul_zero]

/-- Explicit descending Green coefficients for the polynomial in the integer
translation variable. They vanish unless the translation is at most -d. -/
def rootNegativeGreen {d : ℕ} (z : Fin d → ℂ) (t : ℤ) : ℂ := rootForwardGreen z (-t-1)

/-- Exact finite convolution inverse for the entire one-sided Green sequence. -/
theorem rootNegativeGreen_impulse {d : ℕ} (hd : 1 ≤ d) (z : Fin d → ℂ) (t : ℤ) :
    ∑ i : Fin (d+1), (Lagrange.nodal Finset.univ z).coeff i *
      rootNegativeGreen z (t-(i : ℤ)) = if t = 0 then 1 else 0 := by
  simpa only [rootNegativeGreen,show ∀ i : ℤ, -(t-i)-1 = (-t-1)+i by intro; ring,
    show -t-1 = -1 ↔ t=0 by omega] using rootForwardGreen_impulse hd z (-t-1)

/-- Exact support half-line for the descending Green coefficients. -/
theorem rootNegativeGreen_eq_zero {d : ℕ} (z : Fin d → ℂ) (t : ℤ)
    (ht : -(d : ℤ) < t) : rootNegativeGreen z t = 0 :=
  rootForwardGreen_eq_zero z _ (by omega)

/-- Simple unit roots give a uniform bound on ALL Green coefficients, not a
summability claim. The constant may depend on the root separation. -/
theorem rootNegativeGreen_bounded {d : ℕ} (z : Fin d → ℂ)
    (hz : Function.Injective z) (hunit : ∀ i, ‖z i‖ = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℤ, ‖rootNegativeGreen z t‖ ≤ C := by
  obtain ⟨C,hC⟩ := rootProductRecurrence_bounded z hz hunit
    (fun i => if i.val+1=d then 1 else 0)
  refine ⟨max C 0,le_max_right _ _,fun t => ?_⟩
  unfold rootNegativeGreen rootForwardGreen
  split_ifs
  · exact (hC _).trans (le_max_left _ _)
  · simp


/-- The actual signed unit-circle roots attached to an arbitrary finite head. -/
def criticalHeadRoots {k : ℕ} (α : Fin k → ℝ) : Fin (Fintype.card (Fin k × Bool)) → ℂ :=
  fun i => let a := (Fintype.equivFin (Fin k × Bool)).symm i
    criticalCharacter 1 (criticalSignedPhase a.2 (α a.1))

private theorem criticalCharacter_one_injective {a b : ℝ}
    (ha : -1/2 < a ∧ a < 1/2) (hb : -1/2 < b ∧ b < 1/2)
    (h : criticalCharacter 1 a = criticalCharacter 1 b) : a = b := by
  have hf (x : ℝ) : criticalCharacter 1 x = Complex.exp (((2*Real.pi*x : ℝ) : ℂ)*Complex.I) := by
    unfold criticalCharacter
    congr 1
    push_cast
    ring
  rw [hf a, hf b] at h
  have im (x : ℝ) : (((2*Real.pi*x : ℝ) : ℂ)*Complex.I).im = 2*Real.pi*x := by simp
  have hp := Real.pi_pos
  have he := Complex.exp_inj_of_neg_pi_lt_of_le_pi
    (x := (((2*Real.pi*a : ℝ) : ℂ)*Complex.I))
    (y := (((2*Real.pi*b : ℝ) : ℂ)*Complex.I))
    (by rw [im]; nlinarith [ha.1]) (by rw [im]; nlinarith [ha.2])
    (by rw [im]; nlinarith [hb.1]) (by rw [im]; nlinarith [hb.2]) h
  have hi := congrArg Complex.im he
  rw [im,im] at hi
  nlinarith

/-- Distinct strictly interior phases give distinct signed roots; endpoints and
phase collisions are excluded explicitly. -/
theorem criticalHeadRoots_injective {k : ℕ} (α : Fin k → ℝ)
    (hα : Function.Injective α) (hinside : ∀ i, 0 < α i ∧ α i < 1/2) :
    Function.Injective (criticalHeadRoots α) := by
  have hs : Function.Injective (fun a : Fin k × Bool =>
      criticalCharacter 1 (criticalSignedPhase a.2 (α a.1))) := by
    have hb (a : Fin k × Bool) :
        -1/2 < criticalSignedPhase a.2 (α a.1) ∧ criticalSignedPhase a.2 (α a.1) < 1/2 := by
      have h := hinside a.1
      rcases a with ⟨i,u⟩
      cases u <;> simp only [criticalSignedPhase,Bool.false_eq_true,ite_false,ite_true] <;>
        constructor <;> linarith
    intro a b he
    have heq := criticalCharacter_one_injective (hb a) (hb b) he
    rcases a with ⟨i,u⟩
    rcases b with ⟨j,v⟩
    have hi := hinside i
    have hj := hinside j
    cases u <;> cases v <;>
      simp only [criticalSignedPhase,Bool.false_eq_true,ite_false,ite_true] at heq
    · exact Prod.ext (hα heq) rfl
    · linarith
    · linarith
    · exact Prod.ext (hα (neg_inj.mp heq)) rfl
  exact hs.comp (Fintype.equivFin (Fin k × Bool)).symm.injective

/-- The signed critical roots have exactly unit complex norm. -/
theorem criticalHeadRoots_norm {k : ℕ} (α : Fin k → ℝ)
    (i : Fin (Fintype.card (Fin k × Bool))) : ‖criticalHeadRoots α i‖ = 1 := by
  simp [criticalHeadRoots,criticalCharacter,Complex.norm_exp,Complex.mul_re,Complex.mul_im]

/-- Actual arbitrary interior phase heads have bounded descending Green
coefficients. The causal support and impulse are supplied by the preceding
unconditional recurrence identities. No Green-sequence certificate is assumed. -/
theorem criticalHeadNegativeGreen_bounded {k : ℕ} (α : Fin k → ℝ)
    (hα : Function.Injective α) (hinside : ∀ i, 0 < α i ∧ α i < 1/2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℤ, ‖rootNegativeGreen (criticalHeadRoots α) t‖ ≤ C :=
  rootNegativeGreen_bounded _ (criticalHeadRoots_injective α hα hinside) (criticalHeadRoots_norm α)


/-- Descending Green coefficients for the centered Laurent symbol with roots
exp(±2πiα_j). The shift restores the source convention t ≤ -k. -/
def criticalHeadNegativeGreen {k : ℕ} (α : Fin k → ℝ) (t : ℤ) : ℂ :=
  rootNegativeGreen (criticalHeadRoots α) (t-(k : ℤ))

/-- The original centered descending support threshold is exact. -/
theorem criticalHeadNegativeGreen_eq_zero {k : ℕ} (α : Fin k → ℝ) (t : ℤ)
    (ht : -(k : ℤ) < t) : criticalHeadNegativeGreen α t = 0 := by
  apply rootNegativeGreen_eq_zero
  simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,Nat.cast_mul,Nat.cast_ofNat]
  omega

/-- Exact centered Laurent convolution impulse, with both k shifts retained. -/
theorem criticalHeadNegativeGreen_impulse {k : ℕ} (hk : 1 ≤ k) (α : Fin k → ℝ) (t : ℤ) :
    ∑ i : Fin (Fintype.card (Fin k × Bool)+1),
      (Lagrange.nodal Finset.univ (criticalHeadRoots α)).coeff i *
        criticalHeadNegativeGreen α (t-((i : ℤ)-(k : ℤ))) = if t=0 then 1 else 0 := by
  have hd : 1 ≤ Fintype.card (Fin k × Bool) := by simp; omega
  simpa only [criticalHeadNegativeGreen,
    show ∀ i : ℤ, t-(i-(k : ℤ))-(k : ℤ)=t-i by intro; ring] using
      rootNegativeGreen_impulse hd (criticalHeadRoots α) t

/-- The complete centered descending sequence is bounded for every distinct
strictly interior head. No constant uniform in head length or separation is claimed. -/
theorem criticalHeadNegativeGreen_uniform_bound {k : ℕ} (α : Fin k → ℝ)
    (hα : Function.Injective α) (hinside : ∀ i, 0 < α i ∧ α i < 1/2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℤ, ‖criticalHeadNegativeGreen α t‖ ≤ C := by
  obtain ⟨C,hC,hbound⟩ := criticalHeadNegativeGreen_bounded α hα hinside
  exact ⟨C,hC,fun t => hbound (t-(k : ℤ))⟩

end
end MeyerGeneralProblem.Adaptive
