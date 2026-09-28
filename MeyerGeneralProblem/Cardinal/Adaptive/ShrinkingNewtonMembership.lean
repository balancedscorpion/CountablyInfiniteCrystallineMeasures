module

public import MeyerGeneralProblem.Cardinal.Adaptive.ShrinkingNewtonNorms
public import MeyerGeneralProblem.Cardinal.Adaptive.RapidInterpolationGrid

@[expose] public section

/-! Actual variable-weight Newton coordinates and their native membership estimates. -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open Set MeasureTheory
open scoped FourierTransform

private theorem derivativeL2Sum_native_bound (p : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : SchwartzMap ℝ ℂ,
      compactDerivativeL2Sum (2*p) f ≤ C*‖schwartzToHermiteScale p f‖ := by
  obtain ⟨C,hC,hb⟩ := exists_mixedL2Sum_le_hermite_norm p
  refine ⟨(2*p+1:ℕ)*C,by positivity,fun f => ?_⟩
  have h (r : ℕ) (hr : r ∈ Finset.range (2*p+1)) :
      ‖(mixedSchwartz 0 r f).toLp 2 volume‖ ≤ mixedL2Sum (2*p) f := by
    exact Finset.single_le_sum (s := mixedIndices (2*p)) (a := (0,r))
      (f := fun z => ‖(mixedSchwartz z.1 z.2 f).toLp 2 volume‖) (fun z _ => norm_nonneg _) (by
      simp only [mem_mixedIndices,zero_add]; have := Finset.mem_range.mp hr; omega)
  calc
    _ ≤ ∑ r ∈ Finset.range (2*p+1), mixedL2Sum (2*p) f := Finset.sum_le_sum h
    _ = (2*p+1:ℕ)*mixedL2Sum (2*p) f := by simp
    _ ≤ (2*p+1:ℕ)*(C*‖schwartzToHermiteScale p f‖) := by gcongr; exact hb f
    _ = _ := by ring

/-- Characteristic adjustment preserves the sharp original native order in
both compact Zak test variables. -/
theorem exists_halfNewtonBilinear_native_bound (p : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : HermiteScale (-(p:ℤ))) (f g : SchwartzMap ℝ ℂ) (r : ℝ),
      r < 1/2 → (∀ y, r ≤ |y| → f y=0) → (∀ y, r ≤ |y| → g y=0) →
      ‖halfNewtonBilinear (hermiteScaleDistribution p T) f g‖ ≤
        C*‖T‖*‖schwartzToHermiteScale p f‖*‖schwartzToHermiteScale p g‖ := by
  obtain ⟨C,hC,hb⟩ := exists_zakTensorAction_sharp_native_bound p
  obtain ⟨D,hD,hd⟩ := derivativeL2Sum_native_bound p
  obtain ⟨E,hE,he⟩ := exists_hermite_modulation_bound p
  let K : ℝ := D*E*(1+|(1/2:ℝ)|)^(2*p)
  have hK : 0 < K := by dsimp [K]; positivity
  have hm (a : ℝ) (ha : |a|=|(1/2:ℝ)|) (f : SchwartzMap ℝ ℂ) :
      compactDerivativeL2Sum (2*p) (combSchwartzModulation a f) ≤
        K*‖schwartzToHermiteScale p f‖ := by
    have h := (hd (combSchwartzModulation a f)).trans (mul_le_mul_of_nonneg_left (he a f) hD.le)
    rw [ha] at h
    simpa only [K,mul_assoc] using h
  refine ⟨C*K*K,by positivity,fun T f g r hr hf hg => ?_⟩
  have hs (a : ℝ) (f : SchwartzMap ℝ ℂ) (hh : ∀ y, r ≤ |y| → f y=0) :
      ∀ y, r ≤ |y| → combSchwartzModulation a f y=0 := by
    intro y hy; rw [combSchwartzModulation_apply,hh y hy,mul_zero]
  have h := hb T (combSchwartzModulation (1/2) f) (combSchwartzModulation (-1/2) g)
    r hr (hs _ _ hf) (hs _ _ hg)
  apply h.trans
  have hf' := hm (1/2) rfl f
  have hg' := hm (-1/2) (by norm_num) g
  have hf0 : 0 ≤ compactDerivativeL2Sum (2*p) (combSchwartzModulation (1/2) f) :=
    Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hg0 : 0 ≤ compactDerivativeL2Sum (2*p) (combSchwartzModulation (-1/2) g) :=
    Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  calc
    _ ≤ C*‖T‖*(K*‖schwartzToHermiteScale p f‖)*(K*‖schwartzToHermiteScale p g‖) := by
      gcongr
    _ = _ := by ring

/-- Inner radius retaining every level after i with a positive open margin. -/
def shrinkingNewtonInnerRadius (ε : ℕ → ℝ) (i : ℕ) : ℝ := (ε i+3*ε (i+1))/4

/-- Outer radius halfway between adjacent phase distances. -/
def shrinkingNewtonOuterRadius (ε : ℕ → ℝ) (i : ℕ) : ℝ := (ε i+ε (i+1))/2

/-- The actual chosen shrinking transition has one quarter of the adjacent gap. -/
theorem shrinkingNewtonRadius_gap (ε : ℕ → ℝ) (i : ℕ) :
    shrinkingNewtonOuterRadius ε i-shrinkingNewtonInnerRadius ε i=(ε i-ε (i+1))/4 := by
  unfold shrinkingNewtonOuterRadius shrinkingNewtonInnerRadius
  ring

/-- Strict decrease gives the positive width required by the genuine Schwartz cutoff. -/
theorem shrinkingNewtonRadius_lt (ε : ℕ → ℝ) (hε : StrictAnti ε) (i : ℕ) :
    shrinkingNewtonInnerRadius ε i < shrinkingNewtonOuterRadius ε i := by
  have h := hε (Nat.lt_succ_self i)
  unfold shrinkingNewtonInnerRadius shrinkingNewtonOuterRadius
  linarith

/-- The complete actual shrinking test is paid by the numerical variable-weight
majorant, after multiplication by its original weight. -/
theorem shrinkingNewtonTest_majorant_bound (p : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε : ℕ → ℝ) (hε : StrictAnti ε),
      (∀ i, 0 < ε i ∧ ε i ≤ 1/4) → ∀ (i : ℕ) (e : Bool),
      ‖schwartzToHermiteScale p (shrinkingNewtonTest (fun j => ε j) i e
        (shrinkingNewtonInnerRadius ε i) (shrinkingNewtonOuterRadius ε i)
        (shrinkingNewtonRadius_lt ε hε i))‖ ≤
      C*shrinkingNewtonMajorant ε (2*p) i*shrinkingNewtonWeight ε i := by
  obtain ⟨C,hC,hb⟩ := shrinkingNewtonTest_native_bound p
  refine ⟨C*4^(2*p),by positivity,fun ε hε hpos i e => ?_⟩
  have hi := hpos i
  have hn := hpos (i+1)
  have hlt := hε (Nat.lt_succ_self i)
  have h := hb ε i e (shrinkingNewtonInnerRadius ε i) (shrinkingNewtonOuterRadius ε i)
    (ε i) (shrinkingNewtonRadius_lt ε hε i)
    (by rw [shrinkingNewtonRadius_gap]; linarith)
    (by unfold shrinkingNewtonOuterRadius; linarith) hi.1 hi.2 (by
      intro l hl
      exact ⟨hε.antitone (by omega), (hpos (l+1)).2.trans (by norm_num)⟩)
  apply h.trans_eq
  rw [shrinkingNewtonRadius_gap]
  unfold shrinkingNewtonMajorant
  rw [div_pow,show 4*p=2*(2*p) by omega]
  field_simp


/-- The genuine complete Newton coordinate, with the two original variable weights. -/
def shrinkingNewtonCoordinate (ε δ : ℕ → ℝ) (T : TemperedDistribution ℝ ℂ)
    (i : ℕ) (e : Bool) (j : ℕ) (f : Bool) : ℂ :=
  halfNewtonCoordinate (fun l => ε l) (fun l => δ l) T i e j f /
    ((shrinkingNewtonWeight ε i*shrinkingNewtonWeight δ j : ℝ) : ℂ)

private theorem shrinkingNewtonWeight_pos (ε : ℕ → ℝ) (hε : ∀ i, 0 < ε i) (i : ℕ) :
    0 < shrinkingNewtonWeight ε i := by
  exact Finset.prod_pos (fun l hl => hε (l+1))

private theorem shrinkingNewtonMajorant_nonneg (ε : ℕ → ℝ) (hε : StrictAnti ε)
    (hpos : ∀ i, 0 < ε i) (m i : ℕ) : 0 ≤ shrinkingNewtonMajorant ε m i := by
  have hg : 0 < ε i-ε (i+1) := sub_pos.mpr (hε (Nat.lt_succ_self i))
  have hw := shrinkingNewtonWeight_pos ε hpos i
  have hi := hpos i
  dsimp [shrinkingNewtonMajorant]
  positivity

/-- Actual paired atomic records bound every full variable-weight Newton reading
by the summable shrinking majorants, retaining both parity arms. -/
theorem shrinkingNewtonCoordinate_native_bound (p : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α β : ℕ+ → ℝ)
      (hia : ∀ l, 0 < α l ∧ α l < 1/2) (hib : ∀ l, 0 < β l ∧ β l < 1/2)
      (ε δ : ℕ → ℝ) (hε : StrictAnti ε) (hδ : StrictAnti δ),
      (∀ i, 0 < ε i ∧ ε i ≤ 1/4) → (∀ i, 0 < δ i ∧ δ i ≤ 1/4) →
      (∀ l : ℕ+, 1/2-α l=ε l) → (∀ l : ℕ+, 1/2-β l=δ l) →
      ∀ T : HermiteScale (-(p:ℤ)),
      AtomicOnCarrier ((criticalPhaseTailCarrier α hia 0 0).translate (-1/2)) (hermiteScaleDistribution p T) →
      AtomicOnCarrier ((criticalPhaseTailCarrier β hib 0 0).translate (-1/2)) (𝓕 (hermiteScaleDistribution p T)) →
      ∀ (i j : ℕ) (e f : Bool),
      ‖shrinkingNewtonCoordinate ε δ (hermiteScaleDistribution p T) i e j f‖ ≤
        C*‖T‖*shrinkingNewtonMajorant ε (2*p) i*shrinkingNewtonMajorant δ (2*p) j := by
  obtain ⟨C,hC,hb⟩ := exists_halfNewtonBilinear_native_bound p
  obtain ⟨D,hD,hd⟩ := shrinkingNewtonTest_majorant_bound p
  refine ⟨C*D*D,by positivity,fun α β hia hib ε δ hε hδ he hd' hα hβ T hT hFT i j e f => ?_⟩
  let u := shrinkingNewtonTest (fun l => ε l) i e (shrinkingNewtonInnerRadius ε i)
    (shrinkingNewtonOuterRadius ε i) (shrinkingNewtonRadius_lt ε hε i)
  let v := shrinkingNewtonTest (fun l => δ l) j f (shrinkingNewtonInnerRadius δ j)
    (shrinkingNewtonOuterRadius δ j) (shrinkingNewtonRadius_lt δ hδ j)
  have houter (η : ℕ → ℝ) (hη : StrictAnti η) (hηp : ∀ i, 0 < η i ∧ η i ≤ 1/4) (k : ℕ) :
      shrinkingNewtonOuterRadius η k ≤ 1/4 := by
    dsimp [shrinkingNewtonOuterRadius]
    linarith [(hηp k).2,(hηp (k+1)).2]
  have htail (η : ℕ → ℝ) (hη : StrictAnti η) (k : ℕ) (l : ℕ+) (hl : k < (l:ℕ)) :
      η l ≤ shrinkingNewtonInnerRadius η k := by
    have hm := hη.antitone (show k+1 ≤ (l:ℕ) by omega)
    have hs := hη (Nat.lt_succ_self k)
    dsimp [shrinkingNewtonInnerRadius]
    linarith
  have heq := halfNewtonBilinear_shrinking_tests α β hia hib (hermiteScaleDistribution p T)
    hT hFT i j e f _ _ _ _ (shrinkingNewtonRadius_lt ε hε i) (shrinkingNewtonRadius_lt δ hδ j)
    (by linarith [houter ε hε he i]) (by linarith [houter δ hδ hd' j])
    (by intro l; rw [hα l,abs_of_pos (he l).1]; exact (he l).2)
    (by intro l; rw [hβ l,abs_of_pos (hd' l).1]; exact (hd' l).2)
    (by intro l hl; rw [hα l,abs_of_pos (he l).1]; exact htail ε hε i l hl)
    (by intro l hl; rw [hβ l,abs_of_pos (hd' l).1]; exact htail δ hδ j l hl)
  have heα : (fun l => 1/2-α l)=(fun l : ℕ+ => ε l) := funext hα
  have heβ : (fun l => 1/2-β l)=(fun l : ℕ+ => δ l) := funext hβ
  rw [heα,heβ] at heq
  have hu : ∀ x, (3/8:ℝ) ≤ |x| → u x=0 := by
    intro x hx; exact shrinkingNewtonTest_zero _ _ _ _ _ _ _ (by linarith [houter ε hε he i])
  have hv : ∀ x, (3/8:ℝ) ≤ |x| → v x=0 := by
    intro x hx; exact shrinkingNewtonTest_zero _ _ _ _ _ _ _ (by linarith [houter δ hδ hd' j])
  have h := hb T u v (3/8) (by norm_num) hu hv
  have hmu := hd ε hε he i e
  have hmv := hd δ hδ hd' j f
  have hwi := shrinkingNewtonWeight_pos ε (fun i => (he i).1) i
  have hwj := shrinkingNewtonWeight_pos δ (fun i => (hd' i).1) j
  have hbi := shrinkingNewtonMajorant_nonneg ε hε (fun i => (he i).1) (2*p) i
  have hbj := shrinkingNewtonMajorant_nonneg δ hδ (fun i => (hd' i).1) (2*p) j
  have hfull : ‖halfNewtonCoordinate (fun l => ε l) (fun l => δ l) (hermiteScaleDistribution p T) i e j f‖ ≤
      (C*D*D*‖T‖*shrinkingNewtonMajorant ε (2*p) i*shrinkingNewtonMajorant δ (2*p) j)*
        (shrinkingNewtonWeight ε i*shrinkingNewtonWeight δ j) := by
    change ‖halfNewtonBilinear _ _ _‖ ≤ _
    rw [← heq]
    apply h.trans
    calc
      _ ≤ C*‖T‖*(D*shrinkingNewtonMajorant ε (2*p) i*shrinkingNewtonWeight ε i)*
          (D*shrinkingNewtonMajorant δ (2*p) j*shrinkingNewtonWeight δ j) := by gcongr
      _ = _ := by ring
  rw [shrinkingNewtonCoordinate,norm_div,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (mul_pos hwi hwj)]
  exact (div_le_iff₀ (mul_pos hwi hwj)).mpr hfull


/-- The positive phases of the actual rapid tail after the finite head has been removed. -/
def shrinkingRapidPhase (P R : ℕ) (j : ℕ+) : ℝ := 1/2-rapidDistance P R j

/-- Every actual rapid tail phase lies strictly between zero and the seam. -/
theorem shrinkingRapidPhase_mem (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) (j : ℕ+) :
    0 < shrinkingRapidPhase P R j ∧ shrinkingRapidPhase P R j < 1/2 := by
  have hpos : 0 < rapidDistance P R j := by unfold rapidDistance; positivity
  have hsmall := rapidDistance_le_small_constant hP hR j
  unfold shrinkingRapidPhase
  constructor <;> norm_num at hsmall ⊢ <;> linarith

/-- The literal full variable-weight Newton array of every actual original-native
rapid paired source is square summable, including the entire two infinite arms. -/
theorem summable_sq_shrinkingNewtonCoordinate_actual (P R p : ℕ)
    (hP : 1 ≤ P) (hR : 1 ≤ R) (hp : p ≤ P)
    (T : HermiteScale (-(p:ℤ)))
    (hT : AtomicOnCarrier ((criticalPhaseTailCarrier (shrinkingRapidPhase P R)
      (shrinkingRapidPhase_mem P R hP hR) 0 0).translate (-1/2)) (hermiteScaleDistribution p T))
    (hFT : AtomicOnCarrier ((criticalPhaseTailCarrier (shrinkingRapidPhase P R)
      (shrinkingRapidPhase_mem P R hP hR) 0 0).translate (-1/2)) (𝓕 (hermiteScaleDistribution p T)))
    (e f : Bool) :
    Summable (fun ij : ℕ×ℕ =>
      ‖shrinkingNewtonCoordinate (rapidDistance P R) (rapidDistance P R)
        (hermiteScaleDistribution p T) ij.1 e ij.2 f‖^2) := by
  obtain ⟨C,hC,hbound⟩ := shrinkingNewtonCoordinate_native_bound p
  have hpos (i : ℕ) : 0 < rapidDistance P R i ∧ rapidDistance P R i ≤ 1/4 := by
    constructor
    · unfold rapidDistance; positivity
    · exact (rapidDistance_le_small_constant hP hR i).trans (by norm_num)
  have he (l : ℕ+) : 1/2-shrinkingRapidPhase P R l=rapidDistance P R l := by
    unfold shrinkingRapidPhase; ring
  have h := hbound _ _ (shrinkingRapidPhase_mem P R hP hR) (shrinkingRapidPhase_mem P R hP hR)
    _ _ (rapidDistance_strictAnti hP hR) (rapidDistance_strictAnti hP hR)
    hpos hpos he he T hT hFT
  have hs := (summable_sq_actualRapidNewtonTensor P R p hP hR hp).mul_left ((C*‖T‖)^2)
  apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) _ hs
  intro ij
  have hh := pow_le_pow_left₀ (norm_nonneg _) (h ij.1 ij.2 e f) 2
  simpa only [mul_pow,mul_assoc] using hh

/-- Source-prescribed parity normalization of the variable-weight Newton readings. -/
def shrinkingNewtonMoment (ε δ : ℕ → ℝ) (T : TemperedDistribution ℝ ℂ)
    (i : ℕ) (e : Bool) (j : ℕ) (f : Bool) : ℂ :=
  ((1/64 : ℂ)^(e.toNat+f.toNat))⁻¹ * shrinkingNewtonCoordinate ε δ T i e j f

/-- The original kappa parity factors preserve full variable-weight membership. -/
theorem summable_sq_shrinkingNewtonMoment_actual (P R p : ℕ)
    (hP : 1 ≤ P) (hR : 1 ≤ R) (hp : p ≤ P)
    (T : HermiteScale (-(p:ℤ)))
    (hT : AtomicOnCarrier ((criticalPhaseTailCarrier (shrinkingRapidPhase P R)
      (shrinkingRapidPhase_mem P R hP hR) 0 0).translate (-1/2)) (hermiteScaleDistribution p T))
    (hFT : AtomicOnCarrier ((criticalPhaseTailCarrier (shrinkingRapidPhase P R)
      (shrinkingRapidPhase_mem P R hP hR) 0 0).translate (-1/2)) (𝓕 (hermiteScaleDistribution p T)))
    (e f : Bool) :
    Summable (fun ij : ℕ×ℕ =>
      ‖shrinkingNewtonMoment (rapidDistance P R) (rapidDistance P R)
        (hermiteScaleDistribution p T) ij.1 e ij.2 f‖^2) := by
  have h := (summable_sq_shrinkingNewtonCoordinate_actual P R p hP hR hp T hT hFT e f).mul_left
    (‖((1/64 : ℂ)^(e.toNat+f.toNat))⁻¹‖^2)
  simpa only [shrinkingNewtonMoment,norm_mul,mul_pow] using h


/-- All four parity arrays form a single square-summable complete Newton matrix;
this includes both axes and imposes no quadrant truncation. -/
theorem summable_sq_shrinkingNewtonMatrix_actual (P R p : ℕ)
    (hP : 1 ≤ P) (hR : 1 ≤ R) (hp : p ≤ P)
    (T : HermiteScale (-(p:ℤ)))
    (hT : AtomicOnCarrier ((criticalPhaseTailCarrier (shrinkingRapidPhase P R)
      (shrinkingRapidPhase_mem P R hP hR) 0 0).translate (-1/2)) (hermiteScaleDistribution p T))
    (hFT : AtomicOnCarrier ((criticalPhaseTailCarrier (shrinkingRapidPhase P R)
      (shrinkingRapidPhase_mem P R hP hR) 0 0).translate (-1/2)) (𝓕 (hermiteScaleDistribution p T))) :
    Summable (fun z : (ℕ×Bool)×(ℕ×Bool) =>
      ‖shrinkingNewtonMoment (rapidDistance P R) (rapidDistance P R)
        (hermiteScaleDistribution p T) z.1.1 z.1.2 z.2.1 z.2.2‖^2) := by
  let E : (ℕ×Bool)×(ℕ×Bool) ≃ (Bool×Bool)×(ℕ×ℕ) :=
    { toFun := fun z => ((z.1.2,z.2.2),(z.1.1,z.2.1))
      invFun := fun z => ((z.2.1,z.1.1),(z.2.2,z.1.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h : Summable (fun z : (Bool×Bool)×(ℕ×ℕ) =>
      ‖shrinkingNewtonMoment (rapidDistance P R) (rapidDistance P R)
        (hermiteScaleDistribution p T) z.2.1 z.1.1 z.2.2 z.1.2‖^2) := by
    apply (summable_prod_of_nonneg (fun _ => sq_nonneg _)).mpr
    exact ⟨fun ef => summable_sq_shrinkingNewtonMoment_actual P R p hP hR hp T hT hFT ef.1 ef.2,
      summable_of_hasFiniteSupport (Set.toFinite _)⟩
  exact E.summable_iff.mpr h

end
end MeyerGeneralProblem.Adaptive
