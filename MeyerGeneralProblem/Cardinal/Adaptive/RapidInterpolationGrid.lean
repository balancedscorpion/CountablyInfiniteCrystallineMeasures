module

public import MeyerGeneralProblem.Cardinal.Adaptive.CharacteristicGridReconstruction
public import MeyerGeneralProblem.Cardinal.Adaptive.PhaseGeometry
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import all Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

@[expose] public section

/-! # Concrete rapid-distance grids for finite characteristic interpolation -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open Set

/-- The actual rapid parameters have the exact cancellation used in adjacent decay. -/
theorem rapidDecay_mul_base_sub_one {P R : ℕ} (hP : 1 ≤ P) :
    rapidDecay P R*(rapidBase P-1)=Real.log (rapidScale R) := by
  have hp : (P:ℝ) ≠ 0 := by exact_mod_cast (show P ≠ 0 by omega)
  unfold rapidDecay rapidBase
  field_simp
  ring

/-- Each actual rapid distance contracts by at least a factor four. -/
theorem rapidDistance_succ_le_quarter {P R : ℕ} (hP : 1 ≤ P) (hR : 1 ≤ R) (i : ℕ) :
    rapidDistance P R (i+1) ≤ rapidDistance P R i/4 := by
  have hQ : (4:ℝ) ≤ rapidScale R := by
    have hh : (1:ℝ) ≤ headLength R := by exact_mod_cast headLength_pos hR
    unfold rapidScale
    nlinarith
  have hlog : Real.log 4 ≤ Real.log (rapidScale R) := Real.log_le_log (by norm_num) hQ
  have hb : 1 ≤ rapidBase P^i := one_le_pow₀ (rapidBase_one_lt hP).le
  have hd : 0 < rapidDecay P R := rapidDecay_pos hP hR
  have hcancel := rapidDecay_mul_base_sub_one (R := R) hP
  have hlogpos : 0 ≤ Real.log (rapidScale R) := (Real.log_pos (rapidScale_one_lt hR)).le
  have hexp : -(rapidDecay P R)*rapidBase P^(i+1) ≤
      -(rapidDecay P R)*rapidBase P^i-Real.log 4 := by
    rw [pow_succ]
    have hg : Real.log (rapidScale R) ≤ rapidBase P^i*Real.log (rapidScale R) := by nlinarith
    have he : rapidDecay P R*rapidBase P^i*(rapidBase P-1)=rapidBase P^i*Real.log (rapidScale R) := by rw [← hcancel]; ring
    nlinarith
  unfold rapidDistance
  calc
    _ ≤ (1/16)*Real.exp (-(rapidDecay P R)*rapidBase P^i-Real.log 4) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by norm_num)
    _ = _ := by rw [Real.exp_sub,Real.exp_log (by norm_num : (0:ℝ) < 4)]; ring

/-- The actual rapid sequence is strictly decreasing before any zero padding. -/
theorem rapidDistance_strictAnti {P R : ℕ} (hP : 1 ≤ P) (hR : 1 ≤ R) :
    StrictAnti (rapidDistance P R) := by
  apply strictAnti_nat_of_succ_lt
  intro i
  have h := rapidDistance_succ_le_quarter hP hR i
  have hp := (rapidDistance_bounds hP hR i).1
  linarith

/-- The lower sine chord and upper tangent retain uniform quantitative phase control. -/
theorem sine_phase_bounds (t : ℝ) (ht : 0 ≤ t) (hu : t ≤ 1/16) :
    2*t ≤ Real.sin (Real.pi*t) ∧ Real.sin (Real.pi*t) ≤ 4*t := by
  constructor
  · have h := Real.mul_le_sin (x := Real.pi*t) (by positivity) (by nlinarith [Real.pi_pos])
    convert h using 1
    field_simp
  · have h := Real.sin_le (show 0 ≤ Real.pi*t by positivity)
    have hp := Real.pi_le_four
    nlinarith

/-- Fourfold phase contraction implies the required one-half contraction of
literal characteristic nodes, with spare room in the inequality. -/
theorem sine_square_ratio (t u : ℝ) (ht : 0 ≤ t) (htu : t ≤ 1/16)
    (hu : 0 ≤ u) (hquarter : u ≤ t/4) :
    Real.sin (Real.pi*u)^2 ≤ Real.sin (Real.pi*t)^2/2 := by
  have htu' : u ≤ 1/16 := by linarith
  have h1 := sine_phase_bounds t ht htu
  have h2 := sine_phase_bounds u hu htu'
  have hn1 : 0 ≤ Real.sin (Real.pi*t) := by linarith [h1.1]
  have hn2 : 0 ≤ Real.sin (Real.pi*u) := by linarith [h2.1]
  nlinarith [sq_nonneg (Real.sin (Real.pi*t)-2*Real.sin (Real.pi*u))]

/-- The first k actual positive rapid distances, followed by zero padding.
Finite interpolation uses only indices zero through k, hence exactly one endpoint. -/
def rapidFiniteDistance (P R k j : ℕ) : ℝ :=
  if j<k then rapidDistance P R (j+1) else 0

/-- Every padded finite distance remains in the literal small phase chart. -/
theorem rapidFiniteDistance_bounds {P R : ℕ} (hP : 1 ≤ P) (hR : 1 ≤ R) (k j : ℕ) :
    0 ≤ rapidFiniteDistance P R k j ∧ rapidFiniteDistance P R k j ≤ 1/16 := by
  unfold rapidFiniteDistance
  split_ifs
  · exact ⟨(rapidDistance_bounds hP hR (j+1)).1.le,(rapidDistance_bounds hP hR (j+1)).2⟩
  · norm_num

/-- Positive finite entries are exactly the retained pre-endpoint distances. -/
theorem rapidFiniteDistance_pos {P R : ℕ} (hP : 1 ≤ P) (hR : 1 ≤ R)
    (k j : ℕ) (hj : j<k) : 0 < rapidFiniteDistance P R k j := by
  rw [rapidFiniteDistance,ite_eq_left hj]
  exact (rapidDistance_bounds hP hR (j+1)).1

/-- The single final finite-grid entry is exactly zero. -/
@[simp] theorem rapidFiniteDistance_at_cap (P R k : ℕ) : rapidFiniteDistance P R k k=0 := by
  simp [rapidFiniteDistance]

/-- Finite zero padding preserves strict decrease through the first endpoint. -/
theorem rapidFiniteDistance_decreasing {P R : ℕ} (hP : 1 ≤ P) (hR : 1 ≤ R)
    (k : ℕ) {i j : ℕ} (hij : i<j) (hj : j ≤ k) :
    rapidFiniteDistance P R k j < rapidFiniteDistance P R k i := by
  have hi : i<k := by omega
  by_cases hjk : j<k
  · simp only [rapidFiniteDistance,hi,hjk,ite_true]
    exact rapidDistance_strictAnti hP hR (by omega)
  · have hjk' : j=k := by omega
    rw [hjk',rapidFiniteDistance_at_cap]
    exact rapidFiniteDistance_pos hP hR k i hi

/-- Every finite successor retains the strong contraction, even at the endpoint. -/
theorem rapidFiniteDistance_succ_le_quarter {P R : ℕ} (hP : 1 ≤ P) (hR : 1 ≤ R)
    (k j : ℕ) : rapidFiniteDistance P R k (j+1) ≤ rapidFiniteDistance P R k j/4 := by
  by_cases hj : j+1<k
  · have hj' : j<k := by omega
    simp only [rapidFiniteDistance,hj,hj',ite_true]
    exact rapidDistance_succ_le_quarter hP hR (j+1)
  · rw [rapidFiniteDistance,ite_eq_right hj]
    exact div_nonneg (rapidFiniteDistance_bounds hP hR k j).1 (by norm_num)

/-- The concrete finite interpolation phases, with one zero endpoint. -/
def rapidInterpolationPhase (P R k : ℕ) (j : Fin (k+1)) : ℝ := rapidFiniteDistance P R k j

/-- The actual sine radii, retaining exactly the same finite zero padding. -/
def rapidInterpolationRadius (P R k j : ℕ) : ℝ := Real.sin (Real.pi*rapidFiniteDistance P R k j)

/-- The finite phase chart satisfies both hypotheses of exact signed reconstruction. -/
theorem rapidInterpolationPhase_chart {P R : ℕ} (hP : 1 ≤ P) (hR : 1 ≤ R)
    (k : ℕ) (j : Fin (k+1)) :
    |rapidInterpolationPhase P R k j| ≤ 1/2 ∧
      |Real.sin (Real.pi*rapidInterpolationPhase P R k j)| ≤ 1/2 := by
  have hd := rapidFiniteDistance_bounds hP hR k j
  have hs := sine_phase_bounds _ hd.1 hd.2
  change |rapidFiniteDistance P R k j| ≤ 1/2 ∧ |Real.sin (Real.pi*rapidFiniteDistance P R k j)| ≤ 1/2
  rw [abs_of_nonneg hd.1,abs_of_nonneg (by linarith [hs.1] : 0 ≤ Real.sin (Real.pi*rapidFiniteDistance P R k j))]
  constructor <;> linarith [hs.2]

/-- Every retained parity prefix has the exact concrete geometry required by the
mixed coefficient estimate; only the unused odd terminal prefix is omitted. -/
theorem rapidInterpolationRadius_prefix {P R : ℕ} (hP : 1 ≤ P) (hR : 1 ≤ R)
    (odd : Bool) (k n : ℕ) (hn : n ≤ k) (hodd : odd=true → n<k) :
    CharacteristicRadiusPrefix odd n (rapidInterpolationRadius P R k) := by
  constructor
  · intro j _
    have hd := rapidFiniteDistance_bounds hP hR k j
    have hs := sine_phase_bounds _ hd.1 hd.2
    exact le_trans (by linarith [hd.1]) hs.1
  · intro i j hij hj
    have hdi := rapidFiniteDistance_bounds hP hR k i
    have hdj := rapidFiniteDistance_bounds hP hR k j
    apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
    · nlinarith [Real.pi_pos]
    · nlinarith [Real.pi_pos]
    · exact mul_lt_mul_of_pos_left (rapidFiniteDistance_decreasing hP hR k hij (hj.trans hn)) Real.pi_pos
  · intro j _
    have hd := rapidFiniteDistance_bounds hP hR k j
    exact sine_square_ratio _ _ hd.1 hd.2 (rapidFiniteDistance_bounds hP hR k (j+1)).1
      (rapidFiniteDistance_succ_le_quarter hP hR k j)
  · have hd := rapidFiniteDistance_bounds hP hR k 0
    have hs := sine_phase_bounds _ hd.1 hd.2
    change Real.sin (Real.pi*rapidFiniteDistance P R k 0) ≤ 1/2
    linarith [hs.2]
  · intro ho j hj
    have hp := rapidFiniteDistance_pos hP hR k j (lt_of_le_of_lt hj (hodd ho))
    have hd := rapidFiniteDistance_bounds hP hR k j
    have hs := sine_phase_bounds _ hd.1 hd.2
    change 0 < Real.sin (Real.pi*rapidFiniteDistance P R k j)
    linarith [hs.1]

/-- The natural sine sequence agrees exactly with finite-node zero padding. -/
theorem finite_rapidInterpolationRadius (P R k : ℕ) :
    finiteNodeSequence (fun a : Fin (k+1) => Real.sin (Real.pi*rapidInterpolationPhase P R k a)) =
      rapidInterpolationRadius P R k := by
  funext j
  unfold finiteNodeSequence
  split_ifs with hj
  · rfl
  · simp [rapidInterpolationRadius,rapidFiniteDistance,show ¬j<k by omega]

/-- Characteristic nodes of the actual finite rapid grid are distinct. -/
theorem rapidInterpolationPhase_characteristic_injective {P R : ℕ} (hP : 1 ≤ P) (hR : 1 ≤ R)
    (k : ℕ) : Function.Injective (fun a : Fin (k+1) => parityNewtonCoordinate (rapidInterpolationPhase P R k a)) := by
  intro a b hab
  have hp := rapidInterpolationRadius_prefix hP hR false k k le_rfl (by simp)
  apply Fin.ext
  by_contra hne
  have hd := squared_nodes_distinct (rapidInterpolationRadius P R k) k hp.nonneg hp.decreasing
    a (by omega) b (by omega) hne
  apply hd
  simp only [parityNewtonCoordinate_eq] at hab
  exact mul_left_cancel₀ (by norm_num : (2:ℝ) ≠ 0) hab


/-- The actual adaptive rapid sequence is uniformly much smaller than its coarse
one-sixteenth bound; this bound includes the zeroth entry. -/
theorem rapidDistance_le_small_constant {P R : ℕ} (hP : 1 ≤ P) (hR : 1 ≤ R) (i : ℕ) :
    rapidDistance P R i ≤ 1/(2:ℝ)^68 := by
  have hQ : (2:ℝ)^64 ≤ rapidScale R := by
    have hh : (1:ℝ) ≤ headLength R := by exact_mod_cast headLength_pos hR
    unfold rapidScale
    nlinarith
  have hQpos : 0 < rapidScale R := lt_trans zero_lt_one (rapidScale_one_lt hR)
  have hlogpos := Real.log_pos (rapidScale_one_lt hR)
  have hp : (1:ℝ) ≤ P := by exact_mod_cast hP
  have hb : 1 ≤ rapidBase P^i := one_le_pow₀ (rapidBase_one_lt hP).le
  have he : -(rapidDecay P R)*rapidBase P^i ≤ -Real.log (rapidScale R) := by
    unfold rapidDecay
    have hmul : 1 ≤ 6*(P:ℝ)*rapidBase P^i := by nlinarith
    nlinarith
  have hex := Real.exp_le_exp.mpr he
  rw [Real.exp_neg,Real.exp_log hQpos] at hex
  have hinv : (rapidScale R)⁻¹ ≤ ((2:ℝ)^64)⁻¹ := inv_anti₀ (by positivity) hQ
  unfold rapidDistance
  calc
    _ ≤ (1/16)*((2:ℝ)^64)⁻¹ := mul_le_mul_of_nonneg_left (hex.trans hinv) (by norm_num)
    _ = _ := by norm_num

/-- Small nonnegative phases have a quantitatively controlled tangent. -/
theorem tan_phase_le_eight_mul (t : ℝ) (ht : 0 ≤ t) (hu : t ≤ 1/16) :
    Real.tan (Real.pi*t) ≤ 8*t := by
  have hs := sine_phase_bounds t ht hu
  have hsn : 0 ≤ Real.sin (Real.pi*t) := by linarith [hs.1]
  have hc : 0 ≤ Real.cos (Real.pi*t) := Real.cos_nonneg_of_mem_Icc ⟨by nlinarith [Real.pi_pos],by nlinarith [Real.pi_pos]⟩
  have hchalf : 1/2 ≤ Real.cos (Real.pi*t) := by
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi*t)]
  rw [Real.tan_eq_sin_div_cos]
  apply (div_le_iff₀ (by linarith : 0 < Real.cos (Real.pi*t))).mpr
  nlinarith

/-- The actual rapid distances already satisfy the fixed constant-R moment
smallness condition, without deleting additional phases. -/
theorem rapidDistance_tan_small {P R : ℕ} (hP : 1 ≤ P) (hR : 1 ≤ R) (i : ℕ) :
    Real.tan (Real.pi*rapidDistance P R i) ≤ (1/(4096:ℝ))^3 := by
  have hd := rapidDistance_bounds hP hR i
  have hs := rapidDistance_le_small_constant hP hR i
  have ht := tan_phase_le_eight_mul _ hd.1.le hd.2
  norm_num at hs ⊢
  linarith


/-- Actual finite rapid-grid coefficients, including exactly one endpoint and
zero terminal odd rows or columns. -/
def rapidGridCoefficient (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) (k : ℕ)
    (e d : Bool) (f : ℝ → ℝ → ℂ) (i j : Fin (k+1)) : ℂ :=
  trimmedCharacteristicGridCoefficients e d (rapidInterpolationPhase P R k) (rapidInterpolationPhase P R k)
    (rapidInterpolationPhase_characteristic_injective hP hR k)
    (rapidInterpolationPhase_characteristic_injective hP hR k) f i j

/-- Exact original test reconstruction on every signed actual rapid grid point,
including its single endpoint, with the same coefficients used in the bound. -/
theorem rapidGrid_reconstruct (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) (k : ℕ)
    (f : ℝ → ℝ → ℂ) (a b : Fin (k+1)) (t u : ℝ)
    (ht : t=rapidInterpolationPhase P R k a ∨ t= -rapidInterpolationPhase P R k a)
    (hu : u=rapidInterpolationPhase P R k b ∨ u= -rapidInterpolationPhase P R k b) :
    (∑ e : Bool, ∑ d : Bool, ∑ i, ∑ j, rapidGridCoefficient P R hP hR k e d f i j *
      characteristicNewtonBasis e (rapidInterpolationPhase P R k) i t *
      characteristicNewtonBasis d (rapidInterpolationPhase P R k) j u)=f t u := by
  exact trimmedCharacteristicGrid_reconstruct_on_chart _ _
    (rapidInterpolationPhase_characteristic_injective hP hR k)
    (rapidInterpolationPhase_characteristic_injective hP hR k)
    (rapidFiniteDistance_at_cap P R k) (rapidFiniteDistance_at_cap P R k)
    (fun a => (rapidInterpolationPhase_chart hP hR k a).1)
    (fun a => (rapidInterpolationPhase_chart hP hR k a).2)
    (fun b => (rapidInterpolationPhase_chart hP hR k b).1)
    (fun b => (rapidInterpolationPhase_chart hP hR k b).2) f a b t u ht hu

/-- Actual rapid-grid coefficients satisfy the uniform fixed-order estimate at
every cap; all geometric hypotheses are discharged from the concrete formula. -/
theorem exists_rapidGridCoefficient_bound (e d : Bool) (L : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ P R : ℕ, ∀ hP : 1 ≤ P, ∀ hR : 1 ≤ R, ∀ k : ℕ,
      ∀ f : ℝ → ℝ → ℂ,
      (∀ b, ContDiff ℝ (2*L+1) (fun a => f a b)) →
      (∀ r ≤ 2*L+1, ∀ a, ContDiff ℝ (2*L+1)
        (fun b => iteratedDeriv r (fun a => f a b) a)) →
      ∀ A : ℝ, 0 ≤ A →
      (∀ r ≤ 2*L+1, ∀ q ≤ 2*L+1, ∀ a ∈ Icc (-1/2:ℝ) (1/2),
        ∀ b ∈ Icc (-1/2:ℝ) (1/2),
        ‖iteratedDeriv q (fun b => iteratedDeriv r (fun a => f a b) a) b‖ ≤ A) →
      ∀ i j : Fin (k+1), ‖rapidGridCoefficient P R hP hR k e d f i j‖ ≤
        4^(i.val+j.val)*(C*A)/
          ((∏ a ∈ Finset.range (i.val-L), finiteNodeSequence (fun a => parityNewtonCoordinate (rapidInterpolationPhase P R k a)) a)*
           (∏ b ∈ Finset.range (j.val-L), finiteNodeSequence (fun b => parityNewtonCoordinate (rapidInterpolationPhase P R k b)) b)) := by
  obtain ⟨C,hC,hbound⟩ := exists_trimmed_characteristic_grid_bound e d L
  refine ⟨C,hC,?_⟩
  intro P R hP hR k f hfx hfxy A hA hder i j
  apply hbound k k (rapidInterpolationPhase P R k) (rapidInterpolationPhase P R k)
    (rapidInterpolationPhase_characteristic_injective hP hR k)
    (rapidInterpolationPhase_characteristic_injective hP hR k)
    (fun a => (rapidInterpolationPhase_chart hP hR k a).1)
    (fun a => (rapidInterpolationPhase_chart hP hR k a).2)
    (fun b => (rapidInterpolationPhase_chart hP hR k b).1)
    (fun b => (rapidInterpolationPhase_chart hP hR k b).2) f hfx hfxy A hA hder i j
  intro hnonterminal
  rw [finite_rapidInterpolationRadius]
  constructor
  · apply rapidInterpolationRadius_prefix hP hR e k i (by omega)
    intro he
    have hne : i ≠ Fin.last k := fun hi => hnonterminal (Or.inl ⟨he,hi⟩)
    exact Fin.lt_last_iff_ne_last.mpr hne
  · apply rapidInterpolationRadius_prefix hP hR d k j (by omega)
    intro hd
    have hne : j ≠ Fin.last k := fun hj => hnonterminal (Or.inr ⟨hd,hj⟩)
    exact Fin.lt_last_iff_ne_last.mpr hne


end
end MeyerGeneralProblem.Adaptive
