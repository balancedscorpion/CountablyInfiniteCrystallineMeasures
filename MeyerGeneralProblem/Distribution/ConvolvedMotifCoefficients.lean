module

public import MeyerGeneralProblem.Distribution.BaseFiveMotifGeometry
public import MeyerGeneralProblem.Distribution.FiniteCombConvolutionSupport

@[expose] public section

/-!
# Actual local coefficients of convolved base-five motifs

Finite convolution is evaluated against genuine Schwartz isolation tests.
The proved motif–lattice injectivity rules out collisions; zero original
coefficients are handled separately. A first-period unit coefficient then
produces an actual finite set of distinct atoms with coefficient-norm mass
‖z‖4^n. No variation identity is inferred from combinatorial cardinality.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set SchwartzMap
open scoped SchwartzMap FourierTransform

variable (m n : ℕ) [NeZero m]

/-- The actual finite-convolution support container at arbitrary physical translation. -/
def convolvedMotifCarrier (c : ZMod (m*m) → ℂ) (γ : ℝ) : LocallyFiniteCarrier :=
  finiteCombConvolutionCarrier (squarePeriodicCombSupport m c)
    (fun d : FourierMotifWord n => γ+baseFiveMotifPosition m n d)

/-- The genuine finite convolution with arbitrary complex amplitude and translation. -/
def convolvedMotifDistribution (c : ZMod (m*m) → ℂ) (γ : ℝ) (z : ℂ) :
    TemperedDistribution ℝ ℂ :=
  finiteCombConvolution (fun d : FourierMotifWord n => γ+baseFiveMotifPosition m n d)
    (fun d => z*fourierMotifSign d) (squarePeriodicComb m c)

/-- Exact action at the original shifted motif–lattice points. -/
theorem convolvedMotifDistribution_apply (c : ZMod (m*m) → ℂ) (γ : ℝ) (z : ℂ)
    (f : SchwartzMap ℝ ℂ) :
    convolvedMotifDistribution m n c γ z f=
      ∑ d : FourierMotifWord n, (z*fourierMotifSign d)*
        ∑' j : ℤ, c (j : ZMod (m*m))*f (γ+baseFiveMotifPosition m n d+(j:ℝ)/(m:ℝ)) := by
  exact finiteCombConvolution_squarePeriodicComb_apply _ _ _ _ _

/-- The convolution has independently defined local atomic action on its carrier. -/
theorem convolvedMotifDistribution_hasLocallyAtomicAction
    (c : ZMod (m*m) → ℂ) (γ : ℝ) (z : ℂ) :
    HasLocallyAtomicAction (convolvedMotifCarrier m n c γ) (convolvedMotifDistribution m n c γ z) :=
  hasLocallyAtomicAction_finiteCombConvolution _ _ (squarePeriodicComb_hasLocallyAtomicAction m c) _ _

/-- The actual point arising from a nonzero source coefficient is in the carrier. -/
def convolvedMotifPoint (c : ZMod (m*m) → ℂ) (γ : ℝ)
    (d : FourierMotifWord n) (j : ℤ) (hj : c (j : ZMod (m*m))≠0) :
    (convolvedMotifCarrier m n c γ).subtype :=
  ⟨γ+baseFiveMotifPosition m n d+(j:ℝ)/(m:ℝ),
    mem_finiteCombConvolutionCarrier _ _ d ⟨j,rfl,hj⟩⟩

/-- The carrier subtype retains the exact original physical coordinate. -/
theorem convolvedMotifPoint_val (c : ZMod (m*m) → ℂ) (γ : ℝ)
    (d : FourierMotifWord n) (j : ℤ) (hj : c (j : ZMod (m*m))≠0) :
    (convolvedMotifPoint m n c γ d j hj : ℝ)=γ+baseFiveMotifPosition m n d+(j:ℝ)/(m:ℝ) := rfl

/-- Every other original sample contributes zero to the actual isolation action;
zero coefficients need no carrier-membership assertion. -/
theorem convolvedMotif_isolation_sample_eq_zero (c : ZMod (m*m) → ℂ) (γ : ℝ)
    (d : FourierMotifWord n) (j : ℤ) (hj : c (j : ZMod (m*m))≠0)
    (e : FourierMotifWord n) (k : ℤ) (hek : (e,k)≠(d,j)) :
    c (k : ZMod (m*m))*(convolvedMotifCarrier m n c γ).isolationSchwartz
      (convolvedMotifPoint m n c γ d j hj)
      (γ+baseFiveMotifPosition m n e+(k:ℝ)/(m:ℝ))=0 := by
  by_cases hk : c (k : ZMod (m*m))=0
  · rw [hk,zero_mul]
  · have hmem : γ+baseFiveMotifPosition m n e+(k:ℝ)/(m:ℝ) ∈
        (convolvedMotifCarrier m n c γ).carrier := (convolvedMotifPoint m n c γ e k hk).property
    have hne : γ+baseFiveMotifPosition m n e+(k:ℝ)/(m:ℝ)≠
        (convolvedMotifPoint m n c γ d j hj : ℝ) := by
      rw [convolvedMotifPoint_val]
      intro heq
      exact hek (baseFiveMotifPosition_lattice_injective m n
        (Nat.pos_of_ne_zero (NeZero.ne m)) γ heq)
    rw [(convolvedMotifCarrier m n c γ).isolationSchwartz_of_mem_of_ne _ hmem hne,mul_zero]

/-- Exact local coefficient of the genuine convolved distribution, proved
by collapsing both actual sample sums against a Schwartz isolation test. -/
theorem convolvedMotifDistribution_isolation_apply (c : ZMod (m*m) → ℂ) (γ : ℝ) (z : ℂ)
    (d : FourierMotifWord n) (j : ℤ) (hj : c (j : ZMod (m*m))≠0) :
    convolvedMotifDistribution m n c γ z
      ((convolvedMotifCarrier m n c γ).isolationSchwartz (convolvedMotifPoint m n c γ d j hj))=
        z*fourierMotifSign d*c (j : ZMod (m*m)) := by
  classical
  rw [convolvedMotifDistribution_apply,Finset.sum_eq_single d]
  · rw [tsum_eq_single j]
    · have hself := (convolvedMotifCarrier m n c γ).isolationSchwartz_self
        (convolvedMotifPoint m n c γ d j hj)
      rw [convolvedMotifPoint_val] at hself
      rw [hself,mul_one]
    · intro k hkj
      exact convolvedMotif_isolation_sample_eq_zero m n c γ d j hj d k
        (fun h => hkj (congrArg Prod.snd h))
  · intro e _ hed
    have hz : ∀ k : ℤ, c (k : ZMod (m*m))*(convolvedMotifCarrier m n c γ).isolationSchwartz
        (convolvedMotifPoint m n c γ d j hj)
        (γ+baseFiveMotifPosition m n e+(k:ℝ)/(m:ℝ))=0 := fun k =>
      convolvedMotif_isolation_sample_eq_zero m n c γ d j hj e k
        (fun h => hed (congrArg Prod.fst h))
    simp only [hz,tsum_zero,mul_zero]
  · intro hd
    exact (hd (Finset.mem_univ d)).elim

/-- A fixed nonzero source atom produces distinct actual motif points. -/
theorem convolvedMotifPoint_injective (c : ZMod (m*m) → ℂ) (γ : ℝ)
    (j : ℤ) (hj : c (j : ZMod (m*m))≠0) :
    Function.Injective (fun d : FourierMotifWord n => convolvedMotifPoint m n c γ d j hj) := by
  intro d e h
  have hval := congrArg (fun x : (convolvedMotifCarrier m n c γ).subtype => (x:ℝ)) h
  simp only [convolvedMotifPoint_val] at hval
  have heq : (d,j)=(e,j) := baseFiveMotifPosition_lattice_injective m n
    (Nat.pos_of_ne_zero (NeZero.ne m)) γ hval
  exact congrArg Prod.fst heq

/-- The first-period integer representative of a genuine unit source coefficient. -/
def convolvedMotifUnitPoint (c : ZMod (m*m) → ℂ) (γ : ℝ)
    (r : ZMod (m*m)) (hr : c r=1) (d : FourierMotifWord n) :
    (convolvedMotifCarrier m n c γ).subtype :=
  convolvedMotifPoint m n c γ d (r.val:ℤ)
    (by simpa only [Int.cast_natCast,ZMod.natCast_zmod_val,hr] using (one_ne_zero : (1:ℂ)≠0))

/-- The distinguished point uses the actual first-period representative r.val/m. -/
theorem convolvedMotifUnitPoint_val (c : ZMod (m*m) → ℂ) (γ : ℝ)
    (r : ZMod (m*m)) (hr : c r=1) (d : FourierMotifWord n) :
    (convolvedMotifUnitPoint m n c γ r hr d : ℝ)=
      γ+baseFiveMotifPosition m n d+(r.val:ℝ)/(m:ℝ) := by
  simp only [convolvedMotifUnitPoint,convolvedMotifPoint_val,Int.cast_natCast]

/-- Distinguished first-period motif points are genuinely distinct. -/
theorem convolvedMotifUnitPoint_injective (c : ZMod (m*m) → ℂ) (γ : ℝ)
    (r : ZMod (m*m)) (hr : c r=1) :
    Function.Injective (convolvedMotifUnitPoint m n c γ r hr) :=
  convolvedMotifPoint_injective m n c γ _ _

/-- Every actual distinguished coefficient is the amplitude times the original sign. -/
theorem convolvedMotifDistribution_unit_isolation_apply
    (c : ZMod (m*m) → ℂ) (γ : ℝ) (z : ℂ) (r : ZMod (m*m)) (hr : c r=1)
    (d : FourierMotifWord n) :
    convolvedMotifDistribution m n c γ z
      ((convolvedMotifCarrier m n c γ).isolationSchwartz (convolvedMotifUnitPoint m n c γ r hr d))=
        z*fourierMotifSign d := by
  rw [convolvedMotifUnitPoint,convolvedMotifDistribution_isolation_apply]
  simp only [Int.cast_natCast,ZMod.natCast_zmod_val,hr,mul_one]

/-- The norm of each distinguished local coefficient is the actual amplitude norm. -/
theorem norm_convolvedMotifDistribution_unit_isolation_apply
    (c : ZMod (m*m) → ℂ) (γ : ℝ) (z : ℂ) (r : ZMod (m*m)) (hr : c r=1)
    (d : FourierMotifWord n) :
    ‖convolvedMotifDistribution m n c γ z
      ((convolvedMotifCarrier m n c γ).isolationSchwartz (convolvedMotifUnitPoint m n c γ r hr d))‖=
        ‖z‖ := by
  rw [convolvedMotifDistribution_unit_isolation_apply,norm_mul,norm_fourierMotifSign,mul_one]

/-- The actual finite set of distinguished first-period carrier points. -/
def convolvedMotifUnitAtoms (c : ZMod (m*m) → ℂ) (γ : ℝ)
    (r : ZMod (m*m)) (hr : c r=1) : Finset (convolvedMotifCarrier m n c γ).subtype :=
  Finset.univ.image (convolvedMotifUnitPoint m n c γ r hr)

/-- This physical finite set has 4^n distinct points by the proved injection. -/
theorem card_convolvedMotifUnitAtoms (c : ZMod (m*m) → ℂ) (γ : ℝ)
    (r : ZMod (m*m)) (hr : c r=1) :
    (convolvedMotifUnitAtoms m n c γ r hr).card=4^n := by
  classical
  rw [convolvedMotifUnitAtoms,Finset.card_image_of_injective _
    (convolvedMotifUnitPoint_injective m n c γ r hr),Finset.card_univ,card_fourierMotifWord]

/-- Exact coefficient-norm mass on the actual finite set, obtained from
the isolation coefficient formula and physical injectivity, not cardinality alone. -/
theorem convolvedMotifUnitAtoms_coefficient_mass
    (c : ZMod (m*m) → ℂ) (γ : ℝ) (z : ℂ) (r : ZMod (m*m)) (hr : c r=1) :
    (∑ x ∈ convolvedMotifUnitAtoms m n c γ r hr,
      ‖convolvedMotifDistribution m n c γ z ((convolvedMotifCarrier m n c γ).isolationSchwartz x)‖)=
        ‖z‖*(4:ℝ)^n := by
  classical
  rw [convolvedMotifUnitAtoms,Finset.sum_image]
  · simp only [norm_convolvedMotifDistribution_unit_isolation_apply,Finset.sum_const,
      Finset.card_univ,card_fourierMotifWord,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
    ring
  · intro d _ e _ h
    exact convolvedMotifUnitPoint_injective m n c γ r hr h

/-- At nonzero amplitude, every distinguished point has an actually nonzero
isolated coefficient, including arbitrary complex amplitude phases. -/
theorem convolvedMotifUnitAtoms_coefficient_ne_zero
    (c : ZMod (m*m) → ℂ) (γ : ℝ) (z : ℂ) (hz : z≠0)
    (r : ZMod (m*m)) (hr : c r=1)
    (x : (convolvedMotifCarrier m n c γ).subtype)
    (hx : x ∈ convolvedMotifUnitAtoms m n c γ r hr) :
    convolvedMotifDistribution m n c γ z ((convolvedMotifCarrier m n c γ).isolationSchwartz x)≠0 := by
  classical
  obtain ⟨d,_,rfl⟩ := Finset.mem_image.mp hx
  apply norm_ne_zero_iff.mp
  rw [norm_convolvedMotifDistribution_unit_isolation_apply]
  exact norm_ne_zero_iff.mpr hz

/-- Small nonnegative block translations keep every actual distinguished
first-period atom in [0,m+1], independently of the number of motif factors. -/
theorem convolvedMotifUnitPoint_mem_Icc (c : ZMod (m*m) → ℂ) (γ : ℝ)
    (hγ0 : 0≤γ) (hγ : γ≤1/4) (r : ZMod (m*m)) (hr : c r=1)
    (d : FourierMotifWord n) :
    (convolvedMotifUnitPoint m n c γ r hr d : ℝ) ∈ Set.Icc 0 ((m:ℝ)+1) := by
  have hm : (0:ℝ)<m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  have hm1 : (1:ℝ)≤m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  have hp := baseFiveMotifPosition_mem m n (Nat.pos_of_ne_zero (NeZero.ne m)) d
  have hsmall : 1/(4*(m:ℝ))≤1/4 := by
    apply (div_le_div_iff₀ (by positivity : (0:ℝ)<4*m) (by norm_num : (0:ℝ)<4)).mpr
    nlinarith
  have hr0 : (0:ℝ)≤(r.val:ℝ)/(m:ℝ) := by positivity
  have hrm : (r.val:ℝ)/(m:ℝ)<m := by
    apply (div_lt_iff₀ hm).mpr
    exact_mod_cast ZMod.val_lt r
  rw [convolvedMotifUnitPoint_val]
  exact ⟨by linarith [hp.1],by linarith [hp.2.le.trans hsmall]⟩

end

end MeyerGeneralProblem
