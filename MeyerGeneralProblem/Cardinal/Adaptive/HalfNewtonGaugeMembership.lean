module

public import MeyerGeneralProblem.Cardinal.Adaptive.HalfNewtonGauge

@[expose] public section

/-! Uniform analytic gauge bounds for the actual shrinking Newton matrix. -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open Set MeasureTheory
open scoped FourierTransform

/-- The actual shrinking test has a single fixed-order derivative bound paid by
its beta majorant and original weight, uniformly in the row and parity. -/
theorem shrinkingNewtonTest_uniformDerivative_majorant (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε : ℕ → ℝ) (hε : StrictAnti ε),
      (∀ i, 0 < ε i ∧ ε i ≤ 1/4) → ∀ (i : ℕ) (e : Bool) (k : ℕ), k ≤ m → ∀ x,
      ‖iteratedDeriv k (shrinkingNewtonTest (fun j => ε j) i e
        (shrinkingNewtonInnerRadius ε i) (shrinkingNewtonOuterRadius ε i)
        (shrinkingNewtonRadius_lt ε hε i)) x‖ ≤
      C*shrinkingNewtonMajorant ε m i*shrinkingNewtonWeight ε i := by
  choose E hE hEb using shrinkingNewtonTest_derivative_bound
  let A : ℝ := 1+∑ k ∈ Finset.range (m+1), E k
  have hA : 0 < A := by
    have h := Finset.sum_nonneg (s := Finset.range (m+1)) (f := E) (fun k _ => (hE k).le)
    dsimp [A]; linarith
  have hEA (k : ℕ) (hk : k ≤ m) : E k ≤ A := by
    have h := Finset.single_le_sum (s := Finset.range (m+1)) (f := E) (a := k)
      (fun j _ => (hE j).le) (Finset.mem_range.mpr (by omega))
    dsimp [A]; linarith
  refine ⟨A*4^m,by positivity,fun ε hε he i e k hk x => ?_⟩
  have hi := he i
  have hn := he (i+1)
  have hlt := hε (Nat.lt_succ_self i)
  have hgap : 0 < ε i-ε (i+1) := sub_pos.mpr hlt
  let K : ℝ := ((i:ℝ)+1)/((ε i-ε (i+1))*(ε i)^2)
  let B : ℝ := (32:ℝ)^i*(shrinkingNewtonWeight ε i)^2
  have hK : 1 ≤ K := by
    apply (le_div_iff₀ (mul_pos hgap (sq_pos_of_pos hi.1))).mpr
    have hd : (ε i)^2 ≤ 1 := pow_le_one₀ hi.1.le (by linarith)
    have hg : ε i-ε (i+1) ≤ 1 := by linarith
    have h := mul_le_mul hg hd (by positivity) (by norm_num : (0:ℝ) ≤ 1)
    nlinarith [Nat.cast_nonneg (α := ℝ) i]
  have h := hEb k ε i e (shrinkingNewtonInnerRadius ε i) (shrinkingNewtonOuterRadius ε i)
    (ε i) (shrinkingNewtonRadius_lt ε hε i)
    (by rw [shrinkingNewtonRadius_gap]; linarith)
    (by unfold shrinkingNewtonOuterRadius; linarith) hi.1 (by linarith)
    (by intro l hl; exact ⟨hε.antitone (by omega),(he (l+1)).2.trans (by norm_num)⟩) x
  have heq : E k*((i:ℝ)+1)^k/
      (shrinkingNewtonOuterRadius ε i-shrinkingNewtonInnerRadius ε i)^k/
      (ε i)^(2*k)*32^i*(shrinkingNewtonWeight ε i)^2 = E k*B*(4*K)^k := by
    rw [shrinkingNewtonRadius_gap]
    dsimp [B,K]
    rw [show 2*k=k*2 by omega]
    simp only [mul_pow,div_pow,pow_mul]
    field_simp
    <;> ring
  rw [heq] at h
  calc
    _ ≤ E k*B*(4*K)^k := h
    _ ≤ A*B*(4*K)^m := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right (hEA k hk) (by dsimp [B]; positivity)
      · exact pow_le_pow_right₀ (by linarith : (1:ℝ) ≤ 4*K) hk
      · positivity
      · dsimp [B]; positivity
    _ = _ := by
      dsimp [B,K,shrinkingNewtonMajorant]
      rw [mul_pow,div_pow,mul_pow,show 2*m=m*2 by omega,pow_mul]
      ring

/-- Multiplication by the full analytic gauge is bounded on compact separated
tests by exactly the original 2p derivative bounds in each variable. -/
theorem exists_halfNewtonGaugeBilinear_compact_derivative_bound (p : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : HermiteScale (-(p:ℤ))) (f g : SchwartzMap ℝ ℂ) (r A B : ℝ),
      r < 1/2 → 0 ≤ A → 0 ≤ B →
      (∀ x, r ≤ |x| → f x=0) → (∀ x, r ≤ |x| → g x=0) →
      (∀ k ≤ 2*p, ∀ x, ‖iteratedDeriv k f x‖ ≤ A) →
      (∀ k ≤ 2*p, ∀ x, ‖iteratedDeriv k g x‖ ≤ B) →
      ‖halfNewtonGaugeBilinear (hermiteScaleDistribution p T) f g‖ ≤ C*‖T‖*A*B := by
  obtain ⟨C,hC,hb⟩ := exists_halfNewtonBilinear_native_bound p
  obtain ⟨D,hD,hd⟩ := exists_hermite_norm_bound_of_compact_derivatives p
  let K : ℝ := ‖(-2*Real.pi*Complex.I : ℂ)‖
  let W : ℕ → ℝ := fun d => ((d:ℝ)+1)^(4*p)*K^d/(d.factorial:ℝ)
  have hW : Summable W := summable_polynomial_factorial (4*p) K (norm_nonneg _)
  have hW0 : ∀ d, 0 ≤ W d := by intro d; dsimp [W,K]; positivity
  let H : ℝ := ∑' d, W d
  have hH : 0 ≤ H := tsum_nonneg hW0
  let L : ℝ := C*D*D*2^(4*p)
  have hL : 0 < L := by dsimp [L]; positivity
  refine ⟨L*(H+1),by positivity,fun T f g r A B hr hA hB hf hg hfa hgb => ?_⟩
  have hs (d : ℕ) (u : SchwartzMap ℝ ℂ) (hu : ∀ x, r ≤ |x| → u x=0) :
      ∀ x, r ≤ |x| → mixedSchwartz d 0 u x=0 := by
    intro x hx; rw [mixedSchwartz_apply,iteratedDeriv_zero,hu x hx,mul_zero]
  have hnorm (u : SchwartzMap ℝ ℂ) (a : ℝ) (ha : 0 ≤ a) (hu : ∀ x, r ≤ |x| → u x=0)
      (hdu : ∀ k ≤ 2*p, ∀ x, ‖iteratedDeriv k u x‖ ≤ a) (d : ℕ) :
      ‖schwartzToHermiteScale p (mixedSchwartz d 0 u)‖ ≤ D*2^(2*p)*((d:ℝ)+1)^(2*p)*a := by
    have h := hd (mixedSchwartz d 0 u) r (2^(2*p)*((d:ℝ)+1)^(2*p)*a)
      hr (by positivity) (hs d u hu)
      (fun k hk x => compact_monomial_derivative_bound u r a hr ha hu (2*p) hdu d k hk x)
    simpa only [mul_assoc] using h
  have hpoint (d : ℕ) : ‖halfNewtonGaugeCoefficient d *
      halfNewtonBilinear (hermiteScaleDistribution p T) (mixedSchwartz d 0 f) (mixedSchwartz d 0 g)‖ ≤
      L*‖T‖*A*B*W d := by
    have h := hb T (mixedSchwartz d 0 f) (mixedSchwartz d 0 g) r hr (hs d f hf) (hs d g hg)
    have h1 := hnorm f A hA hf hfa d
    have h2 := hnorm g B hB hg hgb d
    rw [norm_mul,halfNewtonGaugeCoefficient,norm_div,norm_pow,Complex.norm_natCast]
    calc
      _ ≤ (K^d/(d.factorial:ℝ))*(C*‖T‖*(D*2^(2*p)*((d:ℝ)+1)^(2*p)*A)*
          (D*2^(2*p)*((d:ℝ)+1)^(2*p)*B)) := by
        apply mul_le_mul_of_nonneg_left (h.trans ?_) (by positivity)
        gcongr
      _ = _ := by
        dsimp [L,W]
        rw [show 4*p=2*p+2*p by omega,pow_add,pow_add]
        ring
  have hsum := halfNewtonGaugeBilinear_norm_summable p T f g r hr hf hg
  have hb' := (norm_tsum_le_tsum_norm hsum).trans (hsum.tsum_le_tsum hpoint
    (hW.mul_left (L*‖T‖*A*B)))
  rw [tsum_mul_left] at hb'
  change ‖halfNewtonGaugeBilinear (hermiteScaleDistribution p T) f g‖ ≤ (L*‖T‖*A*B)*H at hb'
  apply hb'.trans
  nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hL.le (norm_nonneg T)) hA) hB]


/-- Equality at every actual signed phase passes through the full analytic gauge
series; all original atomic records and both infinite phase families are retained. -/
theorem halfNewtonGaugeBilinear_eq_of_phase_values (α β : ℕ+ → ℝ)
    (hia : ∀ j, 0 < α j ∧ α j < 1/2) (hib : ∀ j, 0 < β j ∧ β j < 1/2)
    (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier ((criticalPhaseTailCarrier α hia 0 0).translate (-1/2)) T)
    (hFT : AtomicOnCarrier ((criticalPhaseTailCarrier β hib 0 0).translate (-1/2)) (𝓕 T))
    (f f' g g' : SchwartzMap ℝ ℂ)
    (hf : ∀ x : ℝ, 1/2 ≤ |x| → f x=0) (hf' : ∀ x : ℝ, 1/2 ≤ |x| → f' x=0)
    (hg : ∀ x : ℝ, 1/2 ≤ |x| → g x=0) (hg' : ∀ x : ℝ, 1/2 ≤ |x| → g' x=0)
    (he : ∀ j, f (1/2-α j)=f' (1/2-α j) ∧ f (-(1/2-α j))=f' (-(1/2-α j)))
    (he' : ∀ j, g (1/2-β j)=g' (1/2-β j) ∧ g (-(1/2-β j))=g' (-(1/2-β j))) :
    halfNewtonGaugeBilinear T f g=halfNewtonGaugeBilinear T f' g' := by
  apply tsum_congr
  intro d
  congr 1
  have hs (u : SchwartzMap ℝ ℂ) (hu : ∀ x, 1/2 ≤ |x| → u x=0) :
      ∀ x, 1/2 ≤ |x| → mixedSchwartz d 0 u x=0 := by
    intro x hx; rw [mixedSchwartz_apply,iteratedDeriv_zero,hu x hx,mul_zero]
  apply halfNewtonBilinear_eq_of_phase_values α β hia hib T hT hFT
    _ _ _ _ (hs f hf) (hs f' hf') (hs g hg) (hs g' hg')
  · intro j
    simp only [mixedSchwartz_apply,iteratedDeriv_zero,(he j).1,(he j).2,and_self]
  · intro j
    simp only [mixedSchwartz_apply,iteratedDeriv_zero,(he' j).1,(he' j).2,and_self]

/-- The whole analytically gauged source reading survives replacement by actual shrinking tests. -/
theorem halfNewtonGaugeBilinear_shrinking_tests (α β : ℕ+ → ℝ)
    (hia : ∀ j, 0 < α j ∧ α j < 1/2) (hib : ∀ j, 0 < β j ∧ β j < 1/2)
    (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier ((criticalPhaseTailCarrier α hia 0 0).translate (-1/2)) T)
    (hFT : AtomicOnCarrier ((criticalPhaseTailCarrier β hib 0 0).translate (-1/2)) (𝓕 T))
    (i j : ℕ) (e f : Bool) (a b c d : ℝ) (hab : a < b) (hcd : c < d)
    (hb : b < 1/2) (hd : d < 1/2)
    (ha : ∀ l, |1/2-α l| ≤ 1/4) (hc : ∀ l, |1/2-β l| ≤ 1/4)
    (hat : ∀ l : ℕ+, i < (l:ℕ) → |1/2-α l| ≤ a)
    (hct : ∀ l : ℕ+, j < (l:ℕ) → |1/2-β l| ≤ c) :
    halfNewtonGaugeBilinear T
      (shrinkingNewtonTest (fun l => 1/2-α l) i e a b hab)
      (shrinkingNewtonTest (fun l => 1/2-β l) j f c d hcd) =
    halfNewtonGaugeBilinear T (halfNewtonTest (fun l => 1/2-α l) i e)
      (halfNewtonTest (fun l => 1/2-β l) j f) := by
  apply halfNewtonGaugeBilinear_eq_of_phase_values α β hia hib T hT hFT
  · intro x hx; exact shrinkingNewtonTest_zero _ _ _ _ _ _ _ (hb.le.trans hx)
  · intro x hx; rw [halfNewtonTest_apply,zakCentralCutoff_zero x hx,zero_mul]
  · intro x hx; exact shrinkingNewtonTest_zero _ _ _ _ _ _ _ (hd.le.trans hx)
  · intro x hx; rw [halfNewtonTest_apply,zakCentralCutoff_zero x hx,zero_mul]
  · intro l
    exact ⟨shrinkingNewtonTest_eq_fixed_at_phases _ _ _ _ _ hab ha hat l _ (Or.inl rfl),
      shrinkingNewtonTest_eq_fixed_at_phases _ _ _ _ _ hab ha hat l _ (Or.inr rfl)⟩
  · intro l
    exact ⟨shrinkingNewtonTest_eq_fixed_at_phases _ _ _ _ _ hcd hc hct l _ (Or.inl rfl),
      shrinkingNewtonTest_eq_fixed_at_phases _ _ _ _ _ hcd hc hct l _ (Or.inr rfl)⟩


/-- The actual gauged Newton coordinate, divided by the two original variable weights. -/
def shrinkingNewtonGaugeCoordinate (ε δ : ℕ → ℝ) (T : TemperedDistribution ℝ ℂ)
    (i : ℕ) (e : Bool) (j : ℕ) (f : Bool) : ℂ :=
  halfNewtonGaugeBilinear T (halfNewtonTest (fun l => ε l) i e) (halfNewtonTest (fun l => δ l) j f) /
    ((shrinkingNewtonWeight ε i*shrinkingNewtonWeight δ j : ℝ) : ℂ)

/-- Actual paired atomic records bound every full variable-weight Newton reading
by the summable shrinking majorants, retaining both parity arms. -/
theorem shrinkingNewtonGaugeCoordinate_native_bound (p : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α β : ℕ+ → ℝ)
      (hia : ∀ l, 0 < α l ∧ α l < 1/2) (hib : ∀ l, 0 < β l ∧ β l < 1/2)
      (ε δ : ℕ → ℝ) (hε : StrictAnti ε) (hδ : StrictAnti δ),
      (∀ i, 0 < ε i ∧ ε i ≤ 1/4) → (∀ i, 0 < δ i ∧ δ i ≤ 1/4) →
      (∀ l : ℕ+, 1/2-α l=ε l) → (∀ l : ℕ+, 1/2-β l=δ l) →
      ∀ T : HermiteScale (-(p:ℤ)),
      AtomicOnCarrier ((criticalPhaseTailCarrier α hia 0 0).translate (-1/2)) (hermiteScaleDistribution p T) →
      AtomicOnCarrier ((criticalPhaseTailCarrier β hib 0 0).translate (-1/2)) (𝓕 (hermiteScaleDistribution p T)) →
      ∀ (i j : ℕ) (e f : Bool),
      ‖shrinkingNewtonGaugeCoordinate ε δ (hermiteScaleDistribution p T) i e j f‖ ≤
        C*‖T‖*shrinkingNewtonMajorant ε (2*p) i*shrinkingNewtonMajorant δ (2*p) j := by
  obtain ⟨C,hC,hb⟩ := exists_halfNewtonGaugeBilinear_compact_derivative_bound p
  obtain ⟨D,hD,hd⟩ := shrinkingNewtonTest_uniformDerivative_majorant (2*p)
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
  have heq := halfNewtonGaugeBilinear_shrinking_tests α β hia hib (hermiteScaleDistribution p T)
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
  have hwi : 0 < shrinkingNewtonWeight ε i := Finset.prod_pos (fun l hl => (he (l+1)).1)
  have hwj : 0 < shrinkingNewtonWeight δ j := Finset.prod_pos (fun l hl => (hd' (l+1)).1)
  have hbi : 0 ≤ shrinkingNewtonMajorant ε (2*p) i := by
    have hi := (he i).1
    have hg : 0 < ε i-ε (i+1) := sub_pos.mpr (hε (Nat.lt_succ_self i))
    unfold shrinkingNewtonMajorant; positivity
  have hbj : 0 ≤ shrinkingNewtonMajorant δ (2*p) j := by
    have hj := (hd' j).1
    have hg : 0 < δ j-δ (j+1) := sub_pos.mpr (hδ (Nat.lt_succ_self j))
    unfold shrinkingNewtonMajorant; positivity
  have h := hb T u v (3/8)
    (D*shrinkingNewtonMajorant ε (2*p) i*shrinkingNewtonWeight ε i)
    (D*shrinkingNewtonMajorant δ (2*p) j*shrinkingNewtonWeight δ j)
    (by norm_num) (by positivity) (by positivity) hu hv
    (hd ε hε he i e) (hd δ hδ hd' j f)
  have hfull : ‖halfNewtonGaugeBilinear (hermiteScaleDistribution p T)
      (halfNewtonTest (fun l => ε l) i e) (halfNewtonTest (fun l => δ l) j f)‖ ≤
      (C*D*D*‖T‖*shrinkingNewtonMajorant ε (2*p) i*shrinkingNewtonMajorant δ (2*p) j)*
        (shrinkingNewtonWeight ε i*shrinkingNewtonWeight δ j) := by
    rw [← heq]
    convert h using 1 <;> ring
  rw [shrinkingNewtonGaugeCoordinate,norm_div,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (mul_pos hwi hwj)]
  exact (div_le_iff₀ (mul_pos hwi hwj)).mpr hfull



/-- The analytically gauged full variable-weight Newton array of every actual original-native
rapid paired source is square summable, including the entire two infinite arms. -/
theorem summable_sq_shrinkingNewtonGaugeCoordinate_actual (P R p : ℕ)
    (hP : 1 ≤ P) (hR : 1 ≤ R) (hp : p ≤ P)
    (T : HermiteScale (-(p:ℤ)))
    (hT : AtomicOnCarrier ((criticalPhaseTailCarrier (shrinkingRapidPhase P R)
      (shrinkingRapidPhase_mem P R hP hR) 0 0).translate (-1/2)) (hermiteScaleDistribution p T))
    (hFT : AtomicOnCarrier ((criticalPhaseTailCarrier (shrinkingRapidPhase P R)
      (shrinkingRapidPhase_mem P R hP hR) 0 0).translate (-1/2)) (𝓕 (hermiteScaleDistribution p T)))
    (e f : Bool) :
    Summable (fun ij : ℕ×ℕ =>
      ‖shrinkingNewtonGaugeCoordinate (rapidDistance P R) (rapidDistance P R)
        (hermiteScaleDistribution p T) ij.1 e ij.2 f‖^2) := by
  obtain ⟨C,hC,hbound⟩ := shrinkingNewtonGaugeCoordinate_native_bound p
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

/-- Source-prescribed parity normalization of the full analytic gauge of the variable-weight Newton readings. -/
def shrinkingNewtonGaugeMoment (ε δ : ℕ → ℝ) (T : TemperedDistribution ℝ ℂ)
    (i : ℕ) (e : Bool) (j : ℕ) (f : Bool) : ℂ :=
  ((1/64 : ℂ)^(e.toNat+f.toNat))⁻¹ * shrinkingNewtonGaugeCoordinate ε δ T i e j f

/-- The original kappa parity factors preserve full variable-weight membership. -/
theorem summable_sq_shrinkingNewtonGaugeMoment_actual (P R p : ℕ)
    (hP : 1 ≤ P) (hR : 1 ≤ R) (hp : p ≤ P)
    (T : HermiteScale (-(p:ℤ)))
    (hT : AtomicOnCarrier ((criticalPhaseTailCarrier (shrinkingRapidPhase P R)
      (shrinkingRapidPhase_mem P R hP hR) 0 0).translate (-1/2)) (hermiteScaleDistribution p T))
    (hFT : AtomicOnCarrier ((criticalPhaseTailCarrier (shrinkingRapidPhase P R)
      (shrinkingRapidPhase_mem P R hP hR) 0 0).translate (-1/2)) (𝓕 (hermiteScaleDistribution p T)))
    (e f : Bool) :
    Summable (fun ij : ℕ×ℕ =>
      ‖shrinkingNewtonGaugeMoment (rapidDistance P R) (rapidDistance P R)
        (hermiteScaleDistribution p T) ij.1 e ij.2 f‖^2) := by
  have h := (summable_sq_shrinkingNewtonGaugeCoordinate_actual P R p hP hR hp T hT hFT e f).mul_left
    (‖((1/64 : ℂ)^(e.toNat+f.toNat))⁻¹‖^2)
  simpa only [shrinkingNewtonGaugeMoment,norm_mul,mul_pow] using h


/-- All four analytically gauged parity arrays form a single square-summable complete Newton matrix;
this includes both axes and imposes no quadrant truncation. -/
theorem summable_sq_shrinkingNewtonGaugeMatrix_actual (P R p : ℕ)
    (hP : 1 ≤ P) (hR : 1 ≤ R) (hp : p ≤ P)
    (T : HermiteScale (-(p:ℤ)))
    (hT : AtomicOnCarrier ((criticalPhaseTailCarrier (shrinkingRapidPhase P R)
      (shrinkingRapidPhase_mem P R hP hR) 0 0).translate (-1/2)) (hermiteScaleDistribution p T))
    (hFT : AtomicOnCarrier ((criticalPhaseTailCarrier (shrinkingRapidPhase P R)
      (shrinkingRapidPhase_mem P R hP hR) 0 0).translate (-1/2)) (𝓕 (hermiteScaleDistribution p T))) :
    Summable (fun z : (ℕ×Bool)×(ℕ×Bool) =>
      ‖shrinkingNewtonGaugeMoment (rapidDistance P R) (rapidDistance P R)
        (hermiteScaleDistribution p T) z.1.1 z.1.2 z.2.1 z.2.2‖^2) := by
  let E : (ℕ×Bool)×(ℕ×Bool) ≃ (Bool×Bool)×(ℕ×ℕ) :=
    { toFun := fun z => ((z.1.2,z.2.2),(z.1.1,z.2.1))
      invFun := fun z => ((z.2.1,z.1.1),(z.2.2,z.1.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h : Summable (fun z : (Bool×Bool)×(ℕ×ℕ) =>
      ‖shrinkingNewtonGaugeMoment (rapidDistance P R) (rapidDistance P R)
        (hermiteScaleDistribution p T) z.2.1 z.1.1 z.2.2 z.1.2‖^2) := by
    apply (summable_prod_of_nonneg (fun _ => sq_nonneg _)).mpr
    exact ⟨fun ef => summable_sq_shrinkingNewtonGaugeMoment_actual P R p hP hR hp T hT hFT ef.1 ef.2,
      summable_of_hasFiniteSupport (Set.toFinite _)⟩
  exact E.summable_iff.mpr h


/-- The same actual Newton readings with an explicit fixed parity scale. -/
def shrinkingNewtonMomentWithScale (κ : ℝ) (ε δ : ℕ → ℝ) (T : TemperedDistribution ℝ ℂ)
    (i : ℕ) (e : Bool) (j : ℕ) (f : Bool) : ℂ :=
  ((κ : ℂ)^(e.toNat+f.toNat))⁻¹ * shrinkingNewtonCoordinate ε δ T i e j f

/-- Explicit conversion from the earlier one-sixty-fourth parity normalization;
no variable weight or source reading changes in this rescaling. -/
theorem shrinkingNewtonMomentWithScale_eq (κ : ℝ) (hκ : κ ≠ 0)
    (ε δ : ℕ → ℝ) (T : TemperedDistribution ℝ ℂ) (i : ℕ) (e : Bool) (j : ℕ) (f : Bool) :
    shrinkingNewtonMomentWithScale κ ε δ T i e j f =
      ((1/64 : ℂ)/(κ : ℂ))^(e.toNat+f.toNat)*shrinkingNewtonMoment ε δ T i e j f := by
  unfold shrinkingNewtonMomentWithScale shrinkingNewtonMoment
  have hc : (κ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hκ
  rw [div_pow]
  field_simp

/-- The original kappa parity factors preserve full variable-weight membership. -/
theorem summable_sq_shrinkingNewtonMomentWithScale_actual (κ : ℝ) (P R p : ℕ)
    (hP : 1 ≤ P) (hR : 1 ≤ R) (hp : p ≤ P)
    (T : HermiteScale (-(p:ℤ)))
    (hT : AtomicOnCarrier ((criticalPhaseTailCarrier (shrinkingRapidPhase P R)
      (shrinkingRapidPhase_mem P R hP hR) 0 0).translate (-1/2)) (hermiteScaleDistribution p T))
    (hFT : AtomicOnCarrier ((criticalPhaseTailCarrier (shrinkingRapidPhase P R)
      (shrinkingRapidPhase_mem P R hP hR) 0 0).translate (-1/2)) (𝓕 (hermiteScaleDistribution p T)))
    (e f : Bool) :
    Summable (fun ij : ℕ×ℕ =>
      ‖shrinkingNewtonMomentWithScale κ (rapidDistance P R) (rapidDistance P R)
        (hermiteScaleDistribution p T) ij.1 e ij.2 f‖^2) := by
  have h := (summable_sq_shrinkingNewtonCoordinate_actual P R p hP hR hp T hT hFT e f).mul_left
    (‖((κ : ℂ)^(e.toNat+f.toNat))⁻¹‖^2)
  simpa only [shrinkingNewtonMomentWithScale,norm_mul,mul_pow] using h


/-- All four parity arrays form a single square-summable complete Newton matrix;
this includes both axes and imposes no quadrant truncation. -/
theorem summable_sq_shrinkingNewtonMatrixWithScale_actual (κ : ℝ) (P R p : ℕ)
    (hP : 1 ≤ P) (hR : 1 ≤ R) (hp : p ≤ P)
    (T : HermiteScale (-(p:ℤ)))
    (hT : AtomicOnCarrier ((criticalPhaseTailCarrier (shrinkingRapidPhase P R)
      (shrinkingRapidPhase_mem P R hP hR) 0 0).translate (-1/2)) (hermiteScaleDistribution p T))
    (hFT : AtomicOnCarrier ((criticalPhaseTailCarrier (shrinkingRapidPhase P R)
      (shrinkingRapidPhase_mem P R hP hR) 0 0).translate (-1/2)) (𝓕 (hermiteScaleDistribution p T))) :
    Summable (fun z : (ℕ×Bool)×(ℕ×Bool) =>
      ‖shrinkingNewtonMomentWithScale κ (rapidDistance P R) (rapidDistance P R)
        (hermiteScaleDistribution p T) z.1.1 z.1.2 z.2.1 z.2.2‖^2) := by
  let E : (ℕ×Bool)×(ℕ×Bool) ≃ (Bool×Bool)×(ℕ×ℕ) :=
    { toFun := fun z => ((z.1.2,z.2.2),(z.1.1,z.2.1))
      invFun := fun z => ((z.2.1,z.1.1),(z.2.2,z.1.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h : Summable (fun z : (Bool×Bool)×(ℕ×ℕ) =>
      ‖shrinkingNewtonMomentWithScale κ (rapidDistance P R) (rapidDistance P R)
        (hermiteScaleDistribution p T) z.2.1 z.1.1 z.2.2 z.1.2‖^2) := by
    apply (summable_prod_of_nonneg (fun _ => sq_nonneg _)).mpr
    exact ⟨fun ef => summable_sq_shrinkingNewtonMomentWithScale_actual κ P R p hP hR hp T hT hFT ef.1 ef.2,
      summable_of_hasFiniteSupport (Set.toFinite _)⟩
  exact E.summable_iff.mpr h


/-- The same actual gauged Newton readings with an explicit fixed parity scale. -/
def shrinkingNewtonGaugeMomentWithScale (κ : ℝ) (ε δ : ℕ → ℝ) (T : TemperedDistribution ℝ ℂ)
    (i : ℕ) (e : Bool) (j : ℕ) (f : Bool) : ℂ :=
  ((κ : ℂ)^(e.toNat+f.toNat))⁻¹ * shrinkingNewtonGaugeCoordinate ε δ T i e j f

/-- Explicit conversion from the earlier one-sixty-fourth parity normalization;
no variable weight or source reading changes in this rescaling. -/
theorem shrinkingNewtonGaugeMomentWithScale_eq (κ : ℝ) (hκ : κ ≠ 0)
    (ε δ : ℕ → ℝ) (T : TemperedDistribution ℝ ℂ) (i : ℕ) (e : Bool) (j : ℕ) (f : Bool) :
    shrinkingNewtonGaugeMomentWithScale κ ε δ T i e j f =
      ((1/64 : ℂ)/(κ : ℂ))^(e.toNat+f.toNat)*shrinkingNewtonGaugeMoment ε δ T i e j f := by
  unfold shrinkingNewtonGaugeMomentWithScale shrinkingNewtonGaugeMoment
  have hc : (κ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hκ
  rw [div_pow]
  field_simp

/-- The original kappa parity factors preserve full variable-weight membership. -/
theorem summable_sq_shrinkingNewtonGaugeMomentWithScale_actual (κ : ℝ) (P R p : ℕ)
    (hP : 1 ≤ P) (hR : 1 ≤ R) (hp : p ≤ P)
    (T : HermiteScale (-(p:ℤ)))
    (hT : AtomicOnCarrier ((criticalPhaseTailCarrier (shrinkingRapidPhase P R)
      (shrinkingRapidPhase_mem P R hP hR) 0 0).translate (-1/2)) (hermiteScaleDistribution p T))
    (hFT : AtomicOnCarrier ((criticalPhaseTailCarrier (shrinkingRapidPhase P R)
      (shrinkingRapidPhase_mem P R hP hR) 0 0).translate (-1/2)) (𝓕 (hermiteScaleDistribution p T)))
    (e f : Bool) :
    Summable (fun ij : ℕ×ℕ =>
      ‖shrinkingNewtonGaugeMomentWithScale κ (rapidDistance P R) (rapidDistance P R)
        (hermiteScaleDistribution p T) ij.1 e ij.2 f‖^2) := by
  have h := (summable_sq_shrinkingNewtonGaugeCoordinate_actual P R p hP hR hp T hT hFT e f).mul_left
    (‖((κ : ℂ)^(e.toNat+f.toNat))⁻¹‖^2)
  simpa only [shrinkingNewtonGaugeMomentWithScale,norm_mul,mul_pow] using h


/-- All four parity arrays form a single square-summable complete Newton matrix;
this includes both axes and imposes no quadrant truncation. -/
theorem summable_sq_shrinkingNewtonGaugeMatrixWithScale_actual (κ : ℝ) (P R p : ℕ)
    (hP : 1 ≤ P) (hR : 1 ≤ R) (hp : p ≤ P)
    (T : HermiteScale (-(p:ℤ)))
    (hT : AtomicOnCarrier ((criticalPhaseTailCarrier (shrinkingRapidPhase P R)
      (shrinkingRapidPhase_mem P R hP hR) 0 0).translate (-1/2)) (hermiteScaleDistribution p T))
    (hFT : AtomicOnCarrier ((criticalPhaseTailCarrier (shrinkingRapidPhase P R)
      (shrinkingRapidPhase_mem P R hP hR) 0 0).translate (-1/2)) (𝓕 (hermiteScaleDistribution p T))) :
    Summable (fun z : (ℕ×Bool)×(ℕ×Bool) =>
      ‖shrinkingNewtonGaugeMomentWithScale κ (rapidDistance P R) (rapidDistance P R)
        (hermiteScaleDistribution p T) z.1.1 z.1.2 z.2.1 z.2.2‖^2) := by
  let E : (ℕ×Bool)×(ℕ×Bool) ≃ (Bool×Bool)×(ℕ×ℕ) :=
    { toFun := fun z => ((z.1.2,z.2.2),(z.1.1,z.2.1))
      invFun := fun z => ((z.2.1,z.1.1),(z.2.2,z.1.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h : Summable (fun z : (Bool×Bool)×(ℕ×ℕ) =>
      ‖shrinkingNewtonGaugeMomentWithScale κ (rapidDistance P R) (rapidDistance P R)
        (hermiteScaleDistribution p T) z.2.1 z.1.1 z.2.2 z.1.2‖^2) := by
    apply (summable_prod_of_nonneg (fun _ => sq_nonneg _)).mpr
    exact ⟨fun ef => summable_sq_shrinkingNewtonGaugeMomentWithScale_actual κ P R p hP hR hp T hT hFT ef.1 ef.2,
      summable_of_hasFiniteSupport (Set.toFinite _)⟩
  exact E.summable_iff.mpr h


/-- The parity scale fixed in the retained variable-weight rejection source. -/
def shrinkingNewtonSourceKappa : ℝ := 1/1000

/-- The source's small-radius constant is exactly the fourth power of its parity scale. -/
theorem shrinkingNewtonSourceKappa_fourth : shrinkingNewtonSourceKappa^4=1/(10:ℝ)^12 := by
  norm_num [shrinkingNewtonSourceKappa]


/-- The retained variable-weight parity scale is strictly positive. -/
theorem shrinkingNewtonSourceKappa_pos : 0 < shrinkingNewtonSourceKappa := by
  norm_num [shrinkingNewtonSourceKappa]

/-- Complete actual rapid-source matrix membership with precisely the retained source parity scale. -/
theorem summable_sq_sourceNewtonMatrix_actual (P R p : ℕ)
    (hP : 1 ≤ P) (hR : 1 ≤ R) (hp : p ≤ P)
    (T : HermiteScale (-(p:ℤ)))
    (hT : AtomicOnCarrier ((criticalPhaseTailCarrier (shrinkingRapidPhase P R)
      (shrinkingRapidPhase_mem P R hP hR) 0 0).translate (-1/2)) (hermiteScaleDistribution p T))
    (hFT : AtomicOnCarrier ((criticalPhaseTailCarrier (shrinkingRapidPhase P R)
      (shrinkingRapidPhase_mem P R hP hR) 0 0).translate (-1/2)) (𝓕 (hermiteScaleDistribution p T))) :
    Summable (fun z : (ℕ×Bool)×(ℕ×Bool) =>
      ‖shrinkingNewtonMomentWithScale shrinkingNewtonSourceKappa (rapidDistance P R) (rapidDistance P R)
        (hermiteScaleDistribution p T) z.1.1 z.1.2 z.2.1 z.2.2‖^2) :=
  summable_sq_shrinkingNewtonMatrixWithScale_actual shrinkingNewtonSourceKappa P R p hP hR hp T hT hFT

/-- Complete actual rapid-source matrix membership with precisely the retained source parity scale. -/
theorem summable_sq_sourceGaugeNewtonMatrix_actual (P R p : ℕ)
    (hP : 1 ≤ P) (hR : 1 ≤ R) (hp : p ≤ P)
    (T : HermiteScale (-(p:ℤ)))
    (hT : AtomicOnCarrier ((criticalPhaseTailCarrier (shrinkingRapidPhase P R)
      (shrinkingRapidPhase_mem P R hP hR) 0 0).translate (-1/2)) (hermiteScaleDistribution p T))
    (hFT : AtomicOnCarrier ((criticalPhaseTailCarrier (shrinkingRapidPhase P R)
      (shrinkingRapidPhase_mem P R hP hR) 0 0).translate (-1/2)) (𝓕 (hermiteScaleDistribution p T))) :
    Summable (fun z : (ℕ×Bool)×(ℕ×Bool) =>
      ‖shrinkingNewtonGaugeMomentWithScale shrinkingNewtonSourceKappa (rapidDistance P R) (rapidDistance P R)
        (hermiteScaleDistribution p T) z.1.1 z.1.2 z.2.1 z.2.2‖^2) :=
  summable_sq_shrinkingNewtonGaugeMatrixWithScale_actual shrinkingNewtonSourceKappa P R p hP hR hp T hT hFT

end
end MeyerGeneralProblem.Adaptive
