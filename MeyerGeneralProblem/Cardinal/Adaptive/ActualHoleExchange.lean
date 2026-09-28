module

public import MeyerGeneralProblem.Cardinal.Adaptive.FiniteEndpointKernels
public import MeyerGeneralProblem.Cardinal.Adaptive.FiniteHoleExchange
public import MeyerGeneralProblem.Cardinal.Adaptive.HeadNativeBounds

@[expose] public section

/-! # Actual central hole observations
The observations apply actual distributions and their complete Fourier
transforms to isolating Schwartz tests. Their restriction to the complete
antiperiodic head is a bijection, by the checked consecutive minor.
-/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open scoped FourierTransform SchwartzMap

/-- The physical half of a consecutive fundamental block. -/
def headLeftIndex (k : ℕ) (r : Fin (2*k^2)) : Fin (4*k^2) := ⟨r, by omega⟩
/-- The complementary half of the same block. -/
def headRightIndex (k : ℕ) (r : Fin (2*k^2)) : Fin (4*k^2) := ⟨2*k^2+r, by omega⟩

private theorem sum_head_halves {M : Type*} [AddCommMonoid M] (k : ℕ)
    (f : Fin (4*k^2) → M) :
    ∑ i, f i = ∑ r, f (headLeftIndex k r) + ∑ r, f (headRightIndex k r) := by
  have he : 4*k^2 = 2*k^2+2*k^2 := by omega
  rw [Fintype.sum_equiv (finCongr he) f (fun i => f (Fin.cast he.symm i)) (by intro i; rfl)]
  exact Fin.sum_univ_add _

theorem headIndex_left (k : ℕ) (r : Fin (2*k^2)) :
    headIndex k (headLeftIndex k r) = -(k : ℤ)^2+r := rfl

theorem headIndex_right (k : ℕ) (r : Fin (2*k^2)) :
    headIndex k (headRightIndex k r) = (k : ℤ)^2+r := by
  unfold headIndex headRightIndex
  push_cast
  ring

/-- Side-labelled central physical and Fourier hole coordinates. -/
abbrev CentralHoleCoordinates (k : ℕ) := (Fin (2*k^2) ⊕ Fin (2*k^2)) → ℂ

/-- The central hole map on actual whole tempered distributions. -/
def centralHoleObservation (k : ℕ) (hk : 1 ≤ k) :
    TemperedDistribution ℝ ℂ →ₗ[ℂ] CentralHoleCoordinates k where
  toFun T := Sum.elim (fun r => gridCoefficient k hk (-(k : ℤ)^2+r) T)
    (fun r => gridFourierCoefficient k hk (-(k : ℤ)^2+r) T)
  map_add' T U := by ext i; cases i <;> simp
  map_smul' c T := by ext i; cases i <;> simp

/-- Actual observations in the full head's physical coordinates. -/
def centralHeadObservation (k : ℕ) (hk : 1 ≤ k) :
    (Fin (4*k^2) → ℂ) →ₗ[ℂ] CentralHoleCoordinates k :=
  (centralHoleObservation k hk).comp (poissonHeadSynthesis k hk)

@[simp] theorem centralHeadObservation_physical (k : ℕ) (hk : 1 ≤ k)
    (c : Fin (4*k^2) → ℂ) (r : Fin (2*k^2)) :
    centralHeadObservation k hk c (.inl r) = c (headLeftIndex k r) := by
  change gridCoefficient k hk (headIndex k (headLeftIndex k r)) (poissonHeadSynthesis k hk c) = _
  simpa using gridCoefficient_poissonHeadSynthesis k hk c (headLeftIndex k r) 0

theorem centralHeadObservation_fourier_of_physical_zero (k : ℕ) (hk : 1 ≤ k)
    (c : Fin (4*k^2) → ℂ) (hc : ∀ r, c (headLeftIndex k r) = 0)
    (r : Fin (2*k^2)) :
    centralHeadObservation k hk c (.inr r) =
      (halfShiftedFourierMinor k).mulVec (fun j => c (headRightIndex k j)) r := by
  change gridFourierCoefficient k hk (-(k : ℤ)^2+r) (poissonHeadSynthesis k hk c) = _
  rw [gridFourierCoefficient_poissonHeadSynthesis, sum_head_halves]
  simp only [hc, mul_zero, Finset.sum_const_zero, zero_add]
  unfold Matrix.mulVec dotProduct
  apply Finset.sum_congr rfl
  intro j _
  rw [headIndex_right, halfShiftedComb_coefficient_eq_minor]

/-- The true central hole observations are injective on the complete head. -/
theorem centralHeadObservation_injective (k : ℕ) (hk : 1 ≤ k) :
    Function.Injective (centralHeadObservation k hk) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro c hc
  have hz : centralHeadObservation k hk c = 0 := hc
  have hleft (r : Fin (2*k^2)) : c (headLeftIndex k r) = 0 := by
    have h := congrFun hz (.inl r)
    simpa using h
  have hmul : (halfShiftedFourierMinor k).mulVec (fun j => c (headRightIndex k j)) = 0 := by
    funext r
    rw [← centralHeadObservation_fourier_of_physical_zero k hk c hleft]
    exact congrFun hz (.inr r)
  have hright : (fun j => c (headRightIndex k j)) = 0 := by
    apply halfShiftedFourierMinor_mulVec_injective hk
    simpa using hmul
  change c = 0
  funext i
  by_cases hi : (i : ℕ) < 2*k^2
  · let r : Fin (2*k^2) := ⟨i,hi⟩
    exact hleft r
  · let r : Fin (2*k^2) := ⟨(i : ℕ)-2*k^2, by omega⟩
    have he : headRightIndex k r = i := by apply Fin.ext; dsimp [headRightIndex,r]; omega
    simpa only [he, Pi.zero_apply] using congrFun hright r

/-- Bijection with actual side-labelled central hole observations. -/
def centralHeadObservationEquiv (k : ℕ) (hk : 1 ≤ k) :
    (Fin (4*k^2) → ℂ) ≃ₗ[ℂ] CentralHoleCoordinates k :=
  LinearEquiv.ofInjectiveOfFinrankEq (centralHeadObservation k hk)
    (centralHeadObservation_injective k hk) (by
      simp only [Module.finrank_pi, Fintype.card_sum, Fintype.card_fin]
      omega)

/-- The central hole map is bijective on the whole actual head subspace. -/
def actualCentralHoleEquiv (k : ℕ) (hk : 1 ≤ k) :
    poissonHeadSpace k hk ≃ₗ[ℂ] CentralHoleCoordinates k :=
  (poissonHeadEquiv k hk).symm.trans (centralHeadObservationEquiv k hk)

theorem actualCentralHoleEquiv_apply (k : ℕ) (hk : 1 ≤ k) (w : poissonHeadSpace k hk) :
    actualCentralHoleEquiv k hk w = centralHoleObservation k hk w := by
  obtain ⟨c,rfl⟩ := (poissonHeadEquiv k hk).surjective w
  unfold actualCentralHoleEquiv
  simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  rfl

/-- Central holes exchange with any other actual invertible head observation
on every whole ambient subspace containing the head. The prior observation's
invertibility remains explicit until the original triangular theorem is paid. -/
def actualCentralHoleExchange (k : ℕ) (hk : 1 ≤ k)
    (H : Submodule ℂ (TemperedDistribution ℝ ℂ)) (hH : poissonHeadSpace k hk ≤ H)
    (E₀ : TemperedDistribution ℝ ℂ →ₗ[ℂ] CentralHoleCoordinates k)
    (L₀ : poissonHeadSpace k hk ≃ₗ[ℂ] CentralHoleCoordinates k)
    (hL₀ : ∀ w : poissonHeadSpace k hk, E₀ w = L₀ w) :
    ↥(LinearMap.ker E₀ ⊓ H) ≃ₗ[ℂ] ↥(LinearMap.ker (centralHoleObservation k hk) ⊓ H) :=
  holeExchangeEquiv (poissonHeadSpace k hk) H hH E₀ (centralHoleObservation k hk)
    L₀ (actualCentralHoleEquiv k hk) hL₀ (fun w => (actualCentralHoleEquiv_apply k hk w).symm)


/-- The observed indices are exactly the grid points in the central open
window. For the source's odd `k=2R-1`, this is radius `R-1/2`. -/
theorem centralHoleIndex_iff (k : ℕ) (hk : 1 ≤ k) (m : ℤ) :
    (∃ r : Fin (2*k^2), m = -(k : ℤ)^2+r) ↔
      |halfShiftedGridPoint k m| < (k : ℝ)/2 := by
  have hp : (0 : ℝ) < 2*(k : ℝ) := by positivity
  rw [abs_lt]
  simp only [halfShiftedGridPoint, lt_div_iff₀ hp, div_lt_iff₀ hp]
  constructor
  · rintro ⟨r,rfl⟩
    have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
    have hrlt : (r : ℝ) ≤ 2*(k : ℝ)^2-1 := by
      have : (r : ℕ)+1 ≤ 2*k^2 := r.isLt
      have hc : (r : ℝ)+1 ≤ 2*(k : ℝ)^2 := by exact_mod_cast this
      linarith
    push_cast
    constructor <;> nlinarith
  · rintro ⟨hlo,hhi⟩
    have hlo' : -(k : ℤ)^2 < m+1 := by
      have : -(k : ℝ)^2 < (m : ℝ)+1 := by nlinarith
      exact_mod_cast this
    have hhi' : m < (k : ℤ)^2 := by
      have : (m : ℝ) < (k : ℝ)^2 := by nlinarith
      exact_mod_cast this
    have hr0 : 0 ≤ m+(k : ℤ)^2 := by omega
    have hrlt : m+(k : ℤ)^2 < (2*k^2 : ℕ) := by
      push_cast
      nlinarith
    let r : Fin (2*k^2) := ⟨(m+(k : ℤ)^2).toNat, (Int.toNat_lt hr0).mpr hrlt⟩
    refine ⟨r, ?_⟩
    have hr : (r : ℤ) = m+(k : ℤ)^2 := Int.toNat_of_nonneg hr0
    rw [hr]
    ring


/-- Every set of side-labelled central observations has exactly one source
in the COMPLETE double-grid atomic space. No source-coordinate hypothesis remains. -/
theorem existsUnique_atomic_grid_pair_central_holes (k : ℕ) (hk : 1 ≤ k)
    (y : CentralHoleCoordinates k) :
    ∃! T : TemperedDistribution ℝ ℂ,
      (AtomicOnCarrier (halfShiftedGridCarrier k hk) T ∧
        AtomicOnCarrier (halfShiftedGridCarrier k hk) (𝓕 T)) ∧
      centralHoleObservation k hk T = y := by
  let w := (actualCentralHoleEquiv k hk).symm y
  refine ⟨w, ⟨(mem_poissonHeadSpace_iff_atomic_pair k hk w).mp w.property, ?_⟩, ?_⟩
  · rw [← actualCentralHoleEquiv_apply]
    exact (actualCentralHoleEquiv k hk).apply_symm_apply y
  · intro T hT
    let v : poissonHeadSpace k hk := ⟨T,(mem_poissonHeadSpace_iff_atomic_pair k hk T).mpr hT.1⟩
    have he : v = w := by
      apply (actualCentralHoleEquiv k hk).injective
      rw [actualCentralHoleEquiv_apply]
      exact hT.2.trans ((actualCentralHoleEquiv k hk).apply_symm_apply y).symm
    exact congrArg Subtype.val he

/-- The flat central holes annihilate every complete matched finite-cap source. -/
theorem eq_zero_of_atomic_grid_pair_central_holes (k : ℕ) (hk : 1 ≤ k)
    (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier (halfShiftedGridCarrier k hk) T)
    (hF : AtomicOnCarrier (halfShiftedGridCarrier k hk) (𝓕 T))
    (hzero : centralHoleObservation k hk T = 0) : T = 0 := by
  let w : poissonHeadSpace k hk := ⟨T,(mem_poissonHeadSpace_iff_atomic_pair k hk T).mpr ⟨hT,hF⟩⟩
  have he : w = 0 := (actualCentralHoleEquiv k hk).injective (by
    rw [actualCentralHoleEquiv_apply, map_zero]
    exact hzero)
  exact congrArg Subtype.val he


/-- Original matched positive head phases, indexed from zero. -/
def matchedHeadPhase (k : ℕ) (j : Fin k) : ℝ :=
  (2*(j : ℝ)+1)/(4*(k : ℝ))

theorem matchedHeadPhase_interior (k : ℕ) (hk : 1 ≤ k) (j : Fin k) :
    0 < matchedHeadPhase k j ∧ matchedHeadPhase k j < 1/2 := by
  have hp : (0 : ℝ) < 4*(k : ℝ) := by positivity
  have hj : (j : ℝ)+1 ≤ k := by exact_mod_cast j.isLt
  unfold matchedHeadPhase
  constructor
  · positivity
  · rw [div_lt_iff₀ hp]
    nlinarith

theorem matchedHeadPhase_injective (k : ℕ) (hk : 1 ≤ k) :
    Function.Injective (matchedHeadPhase k) := by
  intro i j h
  have hn : 4*(k : ℝ) ≠ 0 := by positivity
  have he := (div_left_inj' hn).mp h
  have : (i : ℝ) = j := by linarith
  exact Fin.ext (by exact_mod_cast this)

/-- The grid index of an actual signed head atom in its integer cell. -/
def matchedOrbitIndex (k : ℕ) (j : Fin k) (u : Bool) (n : ℤ) : ℤ :=
  2*(k : ℤ)*n + (if u then -(j : ℤ)-1 else (j : ℤ))

theorem matchedOrbitIndex_point (k : ℕ) (hk : 1 ≤ k) (j : Fin k) (u : Bool) (n : ℤ) :
    halfShiftedGridPoint k (matchedOrbitIndex k j u n) =
      (n : ℝ)+criticalSignedPhase u (matchedHeadPhase k j) := by
  have hn : (k : ℝ) ≠ 0 := by positivity
  unfold halfShiftedGridPoint matchedOrbitIndex matchedHeadPhase criticalSignedPhase
  cases u <;> norm_num <;> field_simp <;> ring

/-- The original entire Poisson source in equation (1), not its finite samples. -/
def wholePoissonSource (a b : ℝ) : TemperedDistribution ℝ ℂ :=
  combDistributionTranslation a (modulatedIntegerComb b)

theorem wholePoissonSource_apply (a b : ℝ) (f : SchwartzMap ℝ ℂ) :
    wholePoissonSource a b f = ∑' n : ℤ, criticalCharacter n b * f (a+n) := by
  simp only [wholePoissonSource, combDistributionTranslation_apply,
    modulatedIntegerComb_apply, combSchwartzTranslation_apply]
  apply tsum_congr
  intro n
  rw [fourier_coe_apply]
  unfold criticalCharacter
  congr 2
  push_cast
  ring

theorem fourier_wholePoissonSource_apply (a b : ℝ) (f : SchwartzMap ℝ ℂ) :
    𝓕 (wholePoissonSource a b) f =
      ∑' n : ℤ, combModulationCharacter (-a) (b+n) * f (b+n) := by
  simp only [wholePoissonSource, fourier_combDistributionTranslation,
    fourier_modulatedIntegerComb, combDistributionModulation_apply,
    shiftedIntegerComb_apply, combSchwartzModulation_apply]

/-- The complete matched physical record lies on the half-grid. -/
theorem wholePoissonSource_matched_atomic (k : ℕ) (hk : 1 ≤ k)
    (i j : Fin k) (u v : Bool) :
    AtomicOnCarrier (halfShiftedGridCarrier k hk)
      (wholePoissonSource (criticalSignedPhase u (matchedHeadPhase k i))
        (criticalSignedPhase v (matchedHeadPhase k j))) := by
  intro f hf
  rw [wholePoissonSource_apply]
  have hz (n : ℤ) : f (criticalSignedPhase u (matchedHeadPhase k i)+n) = 0 := by
    apply hf
    exact ⟨matchedOrbitIndex k i u n, (matchedOrbitIndex_point k hk i u n).trans (add_comm _ _)⟩
  simp only [hz, mul_zero, tsum_zero]

/-- The complete matched Fourier record lies on the same half-grid. -/
theorem fourier_wholePoissonSource_matched_atomic (k : ℕ) (hk : 1 ≤ k)
    (i j : Fin k) (u v : Bool) :
    AtomicOnCarrier (halfShiftedGridCarrier k hk)
      (𝓕 (wholePoissonSource (criticalSignedPhase u (matchedHeadPhase k i))
        (criticalSignedPhase v (matchedHeadPhase k j)))) := by
  intro f hf
  rw [fourier_wholePoissonSource_apply]
  have hz (n : ℤ) : f (criticalSignedPhase v (matchedHeadPhase k j)+n) = 0 := by
    apply hf
    exact ⟨matchedOrbitIndex k j v n, (matchedOrbitIndex_point k hk j v n).trans (add_comm _ _)⟩
  simp only [hz, mul_zero, tsum_zero]


private theorem matchedOrbitIndex_injective (k : ℕ) (hk : 1 ≤ k)
    (i j : Fin k) (u v : Bool) (n l : ℤ)
    (h : matchedOrbitIndex k i u n = matchedOrbitIndex k j v l) :
    i = j ∧ u = v ∧ n = l := by
  have hi : (i : ℤ) < k := by exact_mod_cast i.isLt
  have hj : (j : ℤ) < k := by exact_mod_cast j.isLt
  have hi0 : (0 : ℤ) ≤ i := Int.natCast_nonneg _
  have hj0 : (0 : ℤ) ≤ j := Int.natCast_nonneg _
  have hk0 : (0 : ℤ) < k := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hk
  have hr (a : Fin k) (b : Bool) :
      -(k : ℤ) ≤ (if b then -(a : ℤ)-1 else (a : ℤ)) ∧
      (if b then -(a : ℤ)-1 else (a : ℤ)) < k := by
    have ha : (a : ℤ) < k := by exact_mod_cast a.isLt
    have ha0 : (0 : ℤ) ≤ a := Int.natCast_nonneg _
    cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> omega
  have hri := hr i u
  have hrj := hr j v
  unfold matchedOrbitIndex at h
  have hnl : n = l := by
    rcases lt_trichotomy n l with hn|he|hl
    · have : n+1 ≤ l := by omega
      nlinarith
    · exact he
    · have : l+1 ≤ n := by omega
      nlinarith
  subst l
  have ho : (if u then -(i : ℤ)-1 else (i : ℤ)) =
      (if v then -(j : ℤ)-1 else (j : ℤ)) := by linarith
  cases u <;> cases v <;> simp only [Bool.false_eq_true, ite_false, ite_true] at ho
  · refine ⟨Fin.ext (by exact_mod_cast ho), rfl, rfl⟩
  · omega
  · omega
  · have he : (i : ℤ) = j := by linarith
    exact ⟨Fin.ext (by exact_mod_cast he), rfl, rfl⟩

/-- Actual isolated physical coefficient of an original whole Poisson source. -/
theorem gridCoefficient_wholePoissonSource (k : ℕ) (hk : 1 ≤ k)
    (i j : Fin k) (u v : Bool) (b : ℝ) (n : ℤ) :
    gridCoefficient k hk (matchedOrbitIndex k j v n)
      (wholePoissonSource (criticalSignedPhase u (matchedHeadPhase k i)) b) =
      if i = j ∧ u = v then criticalCharacter n b else 0 := by
  change wholePoissonSource _ b (gridCoefficientTest k hk _) = _
  rw [wholePoissonSource_apply]
  have ht (l : ℤ) : criticalSignedPhase u (matchedHeadPhase k i)+(l : ℝ) =
      halfShiftedGridPoint k (matchedOrbitIndex k i u l) := by
    rw [matchedOrbitIndex_point k hk]
    ring
  simp_rw [ht, gridCoefficientTest_apply]
  by_cases h : i = j ∧ u = v
  · rcases h with ⟨rfl,rfl⟩
    rw [ite_eq_left (by exact ⟨rfl,rfl⟩), tsum_eq_single n]
    · simp
    · intro l hln
      have he : matchedOrbitIndex k i u l ≠ matchedOrbitIndex k i u n := by
        intro he
        exact hln (matchedOrbitIndex_injective k hk i i u u l n he).2.2
      simp [he]
  · rw [ite_eq_right h]
    have hz (l : ℤ) : matchedOrbitIndex k i u l ≠ matchedOrbitIndex k j v n := by
      intro he
      have hi := matchedOrbitIndex_injective k hk i j u v l n he
      exact h ⟨hi.1,hi.2.1⟩
    simp only [hz, ite_false, mul_zero, tsum_zero]

/-- Synthesis in the original signed whole Poisson characters. -/
def signedPoissonSynthesis (k : ℕ) :
    (Fin k → Fin k → SignedMassBlock) →ₗ[ℂ] TemperedDistribution ℝ ℂ where
  toFun c := ∑ I, ∑ u, ∑ J, ∑ v, c I J u v •
    wholePoissonSource (criticalSignedPhase u (matchedHeadPhase k I))
      (criticalSignedPhase v (matchedHeadPhase k J))
  map_add' c d := by
    ext f
    simp only [_root_.add_apply, sum_apply, smul_apply, smul_eq_mul, Pi.add_apply,
      add_mul, Finset.sum_add_distrib]
  map_smul' a c := by simp [Finset.smul_sum, smul_smul]

/-- Physical observations of actual whole sources are exactly the finite
row samples used in the checked triangular endpoint kernel theorem. -/
theorem gridCoefficient_signedPoissonSynthesis (k : ℕ) (hk : 1 ≤ k)
    (c : Fin k → Fin k → SignedMassBlock) (i : Fin k) (u : Bool) (n : ℤ) :
    gridCoefficient k hk (matchedOrbitIndex k i u n) (signedPoissonSynthesis k c) =
      finiteSignedRow (matchedHeadPhase k) (fun J v => c i J u v) (criticalCharacter n) := by
  change gridCoefficient k hk _ (∑ I, ∑ u, ∑ J, ∑ v, c I J u v •
    wholePoissonSource _ _) = _
  simp only [map_sum, map_smul, smul_eq_mul, gridCoefficient_wholePoissonSource]
  simp [finiteSignedRow, ite_and, mul_comm]


private theorem criticalCharacter_nat (n : ℕ) (x : ℝ) :
    criticalCharacter (n : ℤ) x = (criticalCharacter 1 x)^n := by
  unfold criticalCharacter
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

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

private theorem matched_signed_character_injective (k : ℕ) (hk : 1 ≤ k) :
    Function.Injective (fun a : Fin k × Bool =>
      criticalCharacter 1 (criticalSignedPhase a.2 (matchedHeadPhase k a.1))) := by
  have hb (a : Fin k × Bool) :
      -1/2 < criticalSignedPhase a.2 (matchedHeadPhase k a.1) ∧
        criticalSignedPhase a.2 (matchedHeadPhase k a.1) < 1/2 := by
    have h := matchedHeadPhase_interior k hk a.1
    rcases a with ⟨i,u⟩
    cases u <;> simp only [criticalSignedPhase, Bool.false_eq_true, ite_false, ite_true] <;> constructor <;> linarith
  intro a b h
  have he := criticalCharacter_one_injective (hb a) (hb b) h
  rcases a with ⟨i,u⟩
  rcases b with ⟨j,v⟩
  have hi := matchedHeadPhase_interior k hk i
  have hj := matchedHeadPhase_interior k hk j
  cases u <;> cases v <;> simp only [criticalSignedPhase, Bool.false_eq_true, ite_false, ite_true] at he
  · exact Prod.ext (matchedHeadPhase_injective k hk he) rfl
  · linarith
  · linarith
  · exact Prod.ext (matchedHeadPhase_injective k hk (neg_inj.mp he)) rfl

private theorem finite_power_samples_zero {ι : Type*} [Fintype ι]
    (z a : ι → ℂ) (hz : Function.Injective z)
    (h : ∀ n : Fin (Fintype.card ι), ∑ i, z i^(n : ℕ)*a i = 0) : a = 0 := by
  let e := Fintype.equivFin ι
  let M := (Matrix.vandermonde (fun i => z (e.symm i))).transpose
  have hdet : M.det ≠ 0 := by
    rw [Matrix.det_transpose]
    exact Matrix.det_vandermonde_ne_zero_iff.mpr (hz.comp e.symm.injective)
  have hunit : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).mpr (isUnit_iff_ne_zero.mpr hdet)
  have hm : M.mulVec (fun i => a (e.symm i)) = 0 := by
    funext n
    change (∑ j, z (e.symm j)^(n : ℕ)*a (e.symm j)) = 0
    rw [← Fintype.sum_equiv e (fun i => z i^(n : ℕ)*a i)
      (fun j => z (e.symm j)^(n : ℕ)*a (e.symm j)) (by intro i; simp)]
    exact h n
  have hzv : (fun i => a (e.symm i)) = 0 := by
    apply (Matrix.mulVec_injective_iff_isUnit.mpr hunit)
    simpa using hm
  funext i
  simpa using congrFun hzv (e i)

/-- The original signed whole Poisson sources are independent, proved from
actual isolated samples and a consecutive Vandermonde on distinct characters. -/
theorem signedPoissonSynthesis_injective (k : ℕ) (hk : 1 ≤ k) :
    Function.Injective (signedPoissonSynthesis k) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro c hc
  have hz : signedPoissonSynthesis k c = 0 := hc
  have hrow (i : Fin k) (u : Bool) (n : ℤ) :
      finiteSignedRow (matchedHeadPhase k) (fun J v => c i J u v) (criticalCharacter n) = 0 := by
    rw [← gridCoefficient_signedPoissonSynthesis k hk]
    rw [hz, map_zero]
  have hcoeff (i : Fin k) (u : Bool) : (fun a : Fin k × Bool => c i a.1 u a.2) = 0 := by
    apply finite_power_samples_zero
      (fun a : Fin k × Bool => criticalCharacter 1 (criticalSignedPhase a.2 (matchedHeadPhase k a.1)))
      _ (matched_signed_character_injective k hk)
    intro n
    have h := hrow i u (n : ℕ)
    simpa only [finiteSignedRow, LinearMap.coe_mk, AddHom.coe_mk,
      criticalCharacter_nat, Fintype.sum_prod_type] using h
  change c = 0
  funext i j u v
  exact congrFun (hcoeff i u) (j,v)

/-- All original signed whole Poisson combinations are genuine complete
matched-grid sources, on BOTH sides. -/
theorem signedPoissonSynthesis_mem_head (k : ℕ) (hk : 1 ≤ k)
    (c : Fin k → Fin k → SignedMassBlock) : signedPoissonSynthesis k c ∈ poissonHeadSpace k hk := by
  change (∑ I, ∑ u, ∑ J, ∑ v, c I J u v • wholePoissonSource _ _) ∈ _
  apply Submodule.sum_mem
  intro I _
  apply Submodule.sum_mem
  intro u _
  apply Submodule.sum_mem
  intro J _
  apply Submodule.sum_mem
  intro v _
  apply Submodule.smul_mem
  exact (mem_poissonHeadSpace_iff_atomic_pair k hk _).mpr
    ⟨wholePoissonSource_matched_atomic k hk I J u v,
      fourier_wholePoissonSource_matched_atomic k hk I J u v⟩

/-- Original signed Poisson character coordinates exhaust the COMPLETE head,
using proved independence and the already proved complete finite-cap dimension. -/
def signedPoissonHeadEquiv (k : ℕ) (hk : 1 ≤ k) :
    (Fin k → Fin k → SignedMassBlock) ≃ₗ[ℂ] poissonHeadSpace k hk :=
  LinearEquiv.ofInjectiveOfFinrankEq
    ((signedPoissonSynthesis k).codRestrict (poissonHeadSpace k hk) (signedPoissonSynthesis_mem_head k hk))
    (fun c d h => signedPoissonSynthesis_injective k hk (congrArg Subtype.val h)) (by
      rw [poissonHeadSpace_finrank]
      simp [Module.finrank_pi_fintype, SignedMassBlock]
      ring)


/-- Actual isolated Fourier coefficient of the original whole Poisson source. -/
theorem gridFourierCoefficient_wholePoissonSource (k : ℕ) (hk : 1 ≤ k)
    (i j : Fin k) (u v : Bool) (a : ℝ) (n : ℤ) :
    gridFourierCoefficient k hk (matchedOrbitIndex k j v n)
      (wholePoissonSource a (criticalSignedPhase u (matchedHeadPhase k i))) =
      if i = j ∧ u = v then
        combModulationCharacter (-a) (criticalSignedPhase u (matchedHeadPhase k i)+n) else 0 := by
  change 𝓕 (wholePoissonSource a _) (gridCoefficientTest k hk _) = _
  rw [fourier_wholePoissonSource_apply]
  have ht (l : ℤ) : criticalSignedPhase u (matchedHeadPhase k i)+(l : ℝ) =
      halfShiftedGridPoint k (matchedOrbitIndex k i u l) := by
    rw [matchedOrbitIndex_point k hk]
    ring
  conv_lhs => arg 1; ext l; arg 2; rw [ht, gridCoefficientTest_apply]
  by_cases h : i = j ∧ u = v
  · rcases h with ⟨rfl,rfl⟩
    rw [ite_eq_left (by exact ⟨rfl,rfl⟩), tsum_eq_single n]
    · simp
    · intro l hln
      have he : matchedOrbitIndex k i u l ≠ matchedOrbitIndex k i u n := by
        intro he
        exact hln (matchedOrbitIndex_injective k hk i i u u l n he).2.2
      simp [he]
  · rw [ite_eq_right h]
    have hz (l : ℤ) : matchedOrbitIndex k i u l ≠ matchedOrbitIndex k j v n := by
      intro he
      have hi := matchedOrbitIndex_injective k hk i j u v l n he
      exact h ⟨hi.1,hi.2.1⟩
    simp only [hz, ite_false, mul_zero, tsum_zero]

private theorem modulation_signed_phase_split (a b : ℝ) (u v : Bool) (n : ℤ) (z : ℂ) :
    z * combModulationCharacter (-(criticalSignedPhase u a)) (criticalSignedPhase v b+n) =
      criticalCharacter (-n) (criticalSignedPhase u a) *
        signedGauge (2*Real.pi*a*b) (fun _ _ => z) u v := by
  rw [combModulationCharacter_eq_exp]
  unfold criticalCharacter signedGauge criticalSignedPhase
  rw [← mul_assoc, mul_comm z, mul_assoc, ← Complex.exp_add]
  congr 2
  cases u <;> cases v <;> simp <;> ring

/-- Fourier observations of actual complete signed sources are exactly the
full-gauge column samples in the original triangular kernel theorem. -/
theorem gridFourierCoefficient_signedPoissonSynthesis (k : ℕ) (hk : 1 ≤ k)
    (c : Fin k → Fin k → SignedMassBlock) (j : Fin k) (v : Bool) (n : ℤ) :
    gridFourierCoefficient k hk (matchedOrbitIndex k j v n) (signedPoissonSynthesis k c) =
      finiteSignedRow (matchedHeadPhase k)
        (fun I u => signedGauge (2*Real.pi*matchedHeadPhase k I*matchedHeadPhase k j) (c I j) u v)
        (criticalCharacter (-n)) := by
  change gridFourierCoefficient k hk _ (∑ I, ∑ u, ∑ J, ∑ v, c I J u v •
    wholePoissonSource _ _) = _
  simp only [map_sum, map_smul, smul_eq_mul, gridFourierCoefficient_wholePoissonSource]
  simp only [ite_and, mul_ite, mul_zero]
  unfold finiteSignedRow
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  apply Finset.sum_congr rfl
  intro I _
  apply Finset.sum_congr rfl
  intro u _
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  exact modulation_signed_phase_split _ _ u v n (c I j u v)


/-- Original triangular hole on one side: phase j, sign, and cell -j,…,j. -/
abbrev TriangularHoleIndex (k : ℕ) := Σ j : Fin k, Bool × Fin (2*j.val+1)

/-- Exact original integer cell, retaining the equality endpoints. -/
def triangularHoleCell {k : ℕ} (h : TriangularHoleIndex k) : ℤ := h.2.2.val-h.1.val

/-- Both side-labelled triangular hole records of the original finite head. -/
abbrev TriangularHoleCoordinates (k : ℕ) := (TriangularHoleIndex k ⊕ TriangularHoleIndex k) → ℂ

/-- Both original triangular observations act on the entire distributions. -/
def triangularHoleObservation (k : ℕ) (hk : 1 ≤ k) :
    TemperedDistribution ℝ ℂ →ₗ[ℂ] TriangularHoleCoordinates k where
  toFun T := Sum.elim
    (fun h => gridCoefficient k hk (matchedOrbitIndex k h.1 h.2.1 (triangularHoleCell h)) T)
    (fun h => gridFourierCoefficient k hk (matchedOrbitIndex k h.1 h.2.1 (triangularHoleCell h)) T)
  map_add' T U := by ext h; cases h <;> simp
  map_smul' a T := by ext h; cases h <;> simp

theorem triangularHoleCell_bound {k : ℕ} (h : TriangularHoleIndex k) :
    |triangularHoleCell h| ≤ (h.1 : ℤ) := by
  have hi : (h.2.2.val : ℤ) < 2*(h.1.val : ℤ)+1 := by exact_mod_cast h.2.2.isLt
  have hi0 : (0 : ℤ) ≤ h.2.2.val := Int.natCast_nonneg _
  unfold triangularHoleCell
  rw [abs_le]
  omega

theorem triangularHoleCell_surjective {k : ℕ} (j : Fin k) (u : Bool) (n : ℤ)
    (hn : |n| ≤ (j : ℤ)) :
    ∃ h : TriangularHoleIndex k, h.1 = j ∧ h.2.1 = u ∧ triangularHoleCell h = n := by
  rw [abs_le] at hn
  have hp : 0 ≤ n+(j : ℤ) := by omega
  let r : Fin (2*j.val+1) := ⟨(n+(j : ℤ)).toNat,
    (Int.toNat_lt hp).mpr (by push_cast; omega)⟩
  refine ⟨⟨j,u,r⟩,rfl,rfl,?_⟩
  change ((n+(j : ℤ)).toNat : ℤ)-(j : ℤ) = n
  rw [Int.toNat_of_nonneg hp]
  ring

/-- Actual original triangular holes annihilate the entire complete head.
The proof consumes the physical AND full-gauge Fourier coefficient identities. -/
theorem triangularHoleObservation_head_injective (k : ℕ) (hk : 1 ≤ k) :
    Function.Injective ((triangularHoleObservation k hk).comp (poissonHeadSpace k hk).subtype) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro w hw
  have hz : triangularHoleObservation k hk w = 0 := hw
  obtain ⟨c,hc⟩ := (signedPoissonHeadEquiv k hk).surjective w
  have hv : signedPoissonSynthesis k c = (w : TemperedDistribution ℝ ℂ) :=
    congrArg Subtype.val hc
  have hcz : c = 0 := by
    apply critical_triangular_samples_kernel (matchedHeadPhase k) (matchedHeadPhase k)
      (matchedHeadPhase_injective k hk) (matchedHeadPhase_injective k hk)
      (matchedHeadPhase_interior k hk) (matchedHeadPhase_interior k hk) c
    · intro I u n hn
      obtain ⟨h,hI,hu,hn'⟩ := triangularHoleCell_surjective I u n hn
      have he := congrFun hz (.inl h)
      change gridCoefficient k hk (matchedOrbitIndex k h.1 h.2.1 (triangularHoleCell h)) w = 0 at he
      simp only [hu,hn',hI, ← hv, gridCoefficient_signedPoissonSynthesis] at he
      exact he
    · intro J v n hn
      obtain ⟨h,hJ,hv',hn'⟩ := triangularHoleCell_surjective J v n hn
      have he := congrFun hz (.inr h)
      change gridFourierCoefficient k hk (matchedOrbitIndex k h.1 h.2.1 (triangularHoleCell h)) w = 0 at he
      simp only [hv',hn',hJ, ← hv, gridFourierCoefficient_signedPoissonSynthesis] at he
      exact he
  change w = 0
  rw [← hc,hcz,map_zero]

private theorem sum_triangular_widths (k : ℕ) :
    ∑ j : Fin k, (2*j.val+1) = k^2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, ih]
    ring

theorem triangularHoleIndex_card (k : ℕ) : Fintype.card (TriangularHoleIndex k) = 2*k^2 := by
  simp only [TriangularHoleIndex, Fintype.card_sigma, Fintype.card_prod, Fintype.card_bool,
    Fintype.card_fin]
  rw [← Finset.mul_sum, sum_triangular_widths]

/-- The actual original L₀ is bijective on the complete head; no inverse
hypothesis is supplied. -/
def actualTriangularHoleEquiv (k : ℕ) (hk : 1 ≤ k) :
    poissonHeadSpace k hk ≃ₗ[ℂ] TriangularHoleCoordinates k :=
  LinearEquiv.ofInjectiveOfFinrankEq
    ((triangularHoleObservation k hk).comp (poissonHeadSpace k hk).subtype)
    (triangularHoleObservation_head_injective k hk) (by
      rw [poissonHeadSpace_finrank, Module.finrank_pi, Fintype.card_sum, triangularHoleIndex_card]
      ring)

theorem actualTriangularHoleEquiv_apply (k : ℕ) (hk : 1 ≤ k) (w : poissonHeadSpace k hk) :
    actualTriangularHoleEquiv k hk w = triangularHoleObservation k hk w := rfl


/-- Exact reversible comparison of the ORIGINAL triangular and flat central
holes on every complete ambient subspace containing the actual whole head.
Both observation inverses have been constructed, rather than assumed. -/
def triangularCentralHoleExchange (k : ℕ) (hk : 1 ≤ k)
    (H : Submodule ℂ (TemperedDistribution ℝ ℂ)) (hH : poissonHeadSpace k hk ≤ H) :
    ↥(LinearMap.ker (triangularHoleObservation k hk) ⊓ H) ≃ₗ[ℂ]
      ↥(LinearMap.ker (centralHoleObservation k hk) ⊓ H) where
  toFun T := ⟨holeCorrection (poissonHeadSpace k hk) (centralHoleObservation k hk)
    (actualCentralHoleEquiv k hk) T,
    holeCorrection_mem_kernel _ _ _ (fun w => (actualCentralHoleEquiv_apply k hk w).symm) T,
    holeCorrection_mem_submodule _ _ hH _ _ T.property.2⟩
  invFun T := ⟨holeCorrection (poissonHeadSpace k hk) (triangularHoleObservation k hk)
    (actualTriangularHoleEquiv k hk) T,
    holeCorrection_mem_kernel _ _ _ (fun w => (actualTriangularHoleEquiv_apply k hk w).symm) T,
    holeCorrection_mem_submodule _ _ hH _ _ T.property.2⟩
  left_inv T := by
    apply Subtype.ext
    change holeCorrection _ (triangularHoleObservation k hk) _
      (holeCorrection _ (centralHoleObservation k hk) _ T) = T
    rw [holeCorrection_apply (poissonHeadSpace k hk) (centralHoleObservation k hk), map_sub,
      holeCorrection_head _ _ _ (fun w => (actualTriangularHoleEquiv_apply k hk w).symm), sub_zero]
    exact holeCorrection_fixed _ _ _ T.property.1
  right_inv T := by
    apply Subtype.ext
    change holeCorrection _ (centralHoleObservation k hk) _
      (holeCorrection _ (triangularHoleObservation k hk) _ T) = T
    rw [holeCorrection_apply (poissonHeadSpace k hk) (triangularHoleObservation k hk), map_sub,
      holeCorrection_head _ _ _ (fun w => (actualCentralHoleEquiv_apply k hk w).symm), sub_zero]
    exact holeCorrection_fixed _ _ _ T.property.1
  map_add' T U := by
    apply Subtype.ext
    exact (holeCorrection (poissonHeadSpace k hk) (centralHoleObservation k hk)
      (actualCentralHoleEquiv k hk)).map_add (T : TemperedDistribution ℝ ℂ) (U : TemperedDistribution ℝ ℂ)
  map_smul' a T := by
    apply Subtype.ext
    exact (holeCorrection (poissonHeadSpace k hk) (centralHoleObservation k hk)
      (actualCentralHoleEquiv k hk)).map_smul a (T : TemperedDistribution ℝ ℂ)

/-- Actual negative-order native distributions, as the range of the original
Hermite realization rather than a replacement coefficient norm. -/
def originalNativeDistributionSpace (p : ℕ) : Submodule ℂ (TemperedDistribution ℝ ℂ) :=
  (hermiteScaleDistributionCLM p).toLinearMap.range

/-- The actual distributional native ranges increase with the integer order. -/
theorem originalNativeDistributionSpace_mono {p q : ℕ} (hpq : p ≤ q) :
    originalNativeDistributionSpace p ≤ originalNativeDistributionSpace q := by
  induction q, hpq using Nat.le_induction with
  | base => exact le_rfl
  | succ q _ ih =>
    apply ih.trans
    rintro T ⟨u,rfl⟩
    exact ⟨hermiteScaleInclusion q u, hermiteScaleDistribution_inclusion q u⟩

/-- Every complete Poisson head lies in EVERY original native layer p>=1. -/
theorem poissonHeadSpace_le_native (k : ℕ) (hk : 1 ≤ k) (p : ℕ) (hp : 1 ≤ p) :
    poissonHeadSpace k hk ≤ originalNativeDistributionSpace p :=
  (poissonHeadSpace_le_native_one_range k hk).trans (originalNativeDistributionSpace_mono hp)

/-- Exact native-order exchange on every complete ambient source subspace
containing the head. No original Hermite order is lost in either correction. -/
def triangularCentralNativeHoleExchange (k : ℕ) (hk : 1 ≤ k)
    (H : Submodule ℂ (TemperedDistribution ℝ ℂ)) (hH : poissonHeadSpace k hk ≤ H)
    (p : ℕ) (hp : 1 ≤ p) :
    ↥(LinearMap.ker (triangularHoleObservation k hk) ⊓ (H ⊓ originalNativeDistributionSpace p)) ≃ₗ[ℂ]
      ↥(LinearMap.ker (centralHoleObservation k hk) ⊓ (H ⊓ originalNativeDistributionSpace p)) :=
  triangularCentralHoleExchange k hk (H ⊓ originalNativeDistributionSpace p)
    (le_inf hH (poissonHeadSpace_le_native k hk p hp))

/-- Cardinal rank, including infinite rank, is preserved at each original
native order. Finrank is not used to disguise infinite dimension. -/
theorem triangularCentralNativeHoleExchange_rank (k : ℕ) (hk : 1 ≤ k)
    (H : Submodule ℂ (TemperedDistribution ℝ ℂ)) (hH : poissonHeadSpace k hk ≤ H)
    (p : ℕ) (hp : 1 ≤ p) :
    Module.rank ℂ ↥(LinearMap.ker (triangularHoleObservation k hk) ⊓ (H ⊓ originalNativeDistributionSpace p)) =
      Module.rank ℂ ↥(LinearMap.ker (centralHoleObservation k hk) ⊓ (H ⊓ originalNativeDistributionSpace p)) :=
  (triangularCentralNativeHoleExchange k hk H hH p hp).rank_eq


/-- An actual half-grid coefficient isolated in the COMPLETE ambient carrier.
The larger carrier may contain tail atoms between the head grid points. -/
def ambientGridCoefficient (k : ℕ) (hk : 1 ≤ k) (S : LocallyFiniteCarrier)
    (hS : (halfShiftedGridCarrier k hk).carrier ⊆ S.carrier) (m : ℤ) :
    TemperedDistribution ℝ ℂ →ₗ[ℂ] ℂ where
  toFun T := T (S.isolationSchwartz ⟨halfShiftedGridPoint k m,hS ⟨m,rfl⟩⟩)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Enlarging the isolation carrier does not change an actual head coefficient. -/
theorem ambientGridCoefficient_eq_on_grid (k : ℕ) (hk : 1 ≤ k) (S : LocallyFiniteCarrier)
    (hS : (halfShiftedGridCarrier k hk).carrier ⊆ S.carrier)
    (T : TemperedDistribution ℝ ℂ) (hT : AtomicOnCarrier (halfShiftedGridCarrier k hk) T)
    (m : ℤ) : ambientGridCoefficient k hk S hS m T = gridCoefficient k hk m T := by
  change T (S.isolationSchwartz _) = T (gridCoefficientTest k hk m)
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply hT
  rintro x ⟨n,rfl⟩
  simp only [_root_.sub_apply, gridCoefficientTest_apply]
  by_cases hn : n = m
  · subst n
    rw [ite_eq_left rfl]
    exact sub_eq_zero.mpr (S.isolationSchwartz_self _)
  · rw [ite_eq_right hn]
    rw [S.isolationSchwartz_of_mem_of_ne _ (hS ⟨n,rfl⟩)
      (fun he => hn (halfShiftedGridPoint_injective k hk he)), sub_self]

/-- Actual two-sided observations for any specified head-grid indices, using
separate complete physical and Fourier ambient carriers. -/
def ambientHoleObservation {ι : Type*} (k : ℕ) (hk : 1 ≤ k)
    (S₁ S₂ : LocallyFiniteCarrier)
    (hS₁ : (halfShiftedGridCarrier k hk).carrier ⊆ S₁.carrier)
    (hS₂ : (halfShiftedGridCarrier k hk).carrier ⊆ S₂.carrier) (q : ι → ℤ) :
    TemperedDistribution ℝ ℂ →ₗ[ℂ] ((ι ⊕ ι) → ℂ) where
  toFun T := Sum.elim
    (fun i => ambientGridCoefficient k hk S₁ hS₁ (q i) T)
    (fun i => ambientGridCoefficient k hk S₂ hS₂ (q i) (𝓕 T))
  map_add' T U := by ext i; cases i <;> simp [FourierTransform.fourier_add]
  map_smul' a T := by ext i; cases i <;> simp [FourierTransform.fourier_smul]

/-- The actual original triangular indices, before applying ambient tests. -/
def triangularGridIndices (k : ℕ) (h : TriangularHoleIndex k) : ℤ :=
  matchedOrbitIndex k h.1 h.2.1 (triangularHoleCell h)

/-- The central grid indices, before applying ambient tests. -/
def centralGridIndices (k : ℕ) (r : Fin (2*k^2)) : ℤ := -(k : ℤ)^2+r

theorem ambientTriangularHoleObservation_on_head (k : ℕ) (hk : 1 ≤ k)
    (S₁ S₂ : LocallyFiniteCarrier)
    (hS₁ : (halfShiftedGridCarrier k hk).carrier ⊆ S₁.carrier)
    (hS₂ : (halfShiftedGridCarrier k hk).carrier ⊆ S₂.carrier) (w : poissonHeadSpace k hk) :
    ambientHoleObservation k hk S₁ S₂ hS₁ hS₂ (triangularGridIndices k) w =
      actualTriangularHoleEquiv k hk w := by
  have hw := (mem_poissonHeadSpace_iff_atomic_pair k hk w).mp w.property
  rw [actualTriangularHoleEquiv_apply]
  funext i
  cases i with
  | inl i => exact ambientGridCoefficient_eq_on_grid k hk S₁ hS₁ w hw.1 _
  | inr i => exact ambientGridCoefficient_eq_on_grid k hk S₂ hS₂ (𝓕 (w : TemperedDistribution ℝ ℂ)) hw.2 _

theorem ambientCentralHoleObservation_on_head (k : ℕ) (hk : 1 ≤ k)
    (S₁ S₂ : LocallyFiniteCarrier)
    (hS₁ : (halfShiftedGridCarrier k hk).carrier ⊆ S₁.carrier)
    (hS₂ : (halfShiftedGridCarrier k hk).carrier ⊆ S₂.carrier) (w : poissonHeadSpace k hk) :
    ambientHoleObservation k hk S₁ S₂ hS₁ hS₂ (centralGridIndices k) w =
      actualCentralHoleEquiv k hk w := by
  have hw := (mem_poissonHeadSpace_iff_atomic_pair k hk w).mp w.property
  rw [actualCentralHoleEquiv_apply]
  funext i
  cases i with
  | inl i => exact ambientGridCoefficient_eq_on_grid k hk S₁ hS₁ w hw.1 _
  | inr i => exact ambientGridCoefficient_eq_on_grid k hk S₂ hS₂ (𝓕 (w : TemperedDistribution ℝ ℂ)) hw.2 _

/-- Complete ambient kernels exchange using tests that isolate in the full
carriers. Additional tail atoms cannot contaminate the finite observations. -/
def ambientTriangularCentralHoleExchange (k : ℕ) (hk : 1 ≤ k)
    (S₁ S₂ : LocallyFiniteCarrier)
    (hS₁ : (halfShiftedGridCarrier k hk).carrier ⊆ S₁.carrier)
    (hS₂ : (halfShiftedGridCarrier k hk).carrier ⊆ S₂.carrier)
    (H : Submodule ℂ (TemperedDistribution ℝ ℂ)) (hH : poissonHeadSpace k hk ≤ H) :
    ↥(LinearMap.ker (ambientHoleObservation k hk S₁ S₂ hS₁ hS₂ (triangularGridIndices k)) ⊓ H) ≃ₗ[ℂ]
      ↥(LinearMap.ker (ambientHoleObservation k hk S₁ S₂ hS₁ hS₂ (centralGridIndices k)) ⊓ H) where
  toFun T := ⟨holeCorrection (poissonHeadSpace k hk)
    (ambientHoleObservation k hk S₁ S₂ hS₁ hS₂ (centralGridIndices k))
    (actualCentralHoleEquiv k hk) T,
    holeCorrection_mem_kernel _ _ _ (ambientCentralHoleObservation_on_head k hk S₁ S₂ hS₁ hS₂) T,
    holeCorrection_mem_submodule _ _ hH _ _ T.property.2⟩
  invFun T := ⟨holeCorrection (poissonHeadSpace k hk)
    (ambientHoleObservation k hk S₁ S₂ hS₁ hS₂ (triangularGridIndices k))
    (actualTriangularHoleEquiv k hk) T,
    holeCorrection_mem_kernel _ _ _ (ambientTriangularHoleObservation_on_head k hk S₁ S₂ hS₁ hS₂) T,
    holeCorrection_mem_submodule _ _ hH _ _ T.property.2⟩
  left_inv T := by
    apply Subtype.ext
    change holeCorrection _ _ (actualTriangularHoleEquiv k hk)
      (holeCorrection _ _ (actualCentralHoleEquiv k hk) T) = T
    rw [holeCorrection_apply (poissonHeadSpace k hk) _ (actualCentralHoleEquiv k hk), map_sub,
      holeCorrection_head _ _ _ (ambientTriangularHoleObservation_on_head k hk S₁ S₂ hS₁ hS₂), sub_zero]
    exact holeCorrection_fixed _ _ _ T.property.1
  right_inv T := by
    apply Subtype.ext
    change holeCorrection _ _ (actualCentralHoleEquiv k hk)
      (holeCorrection _ _ (actualTriangularHoleEquiv k hk) T) = T
    rw [holeCorrection_apply (poissonHeadSpace k hk) _ (actualTriangularHoleEquiv k hk), map_sub,
      holeCorrection_head _ _ _ (ambientCentralHoleObservation_on_head k hk S₁ S₂ hS₁ hS₂), sub_zero]
    exact holeCorrection_fixed _ _ _ T.property.1
  map_add' T U := by
    apply Subtype.ext
    exact (holeCorrection (poissonHeadSpace k hk)
      (ambientHoleObservation k hk S₁ S₂ hS₁ hS₂ (centralGridIndices k))
      (actualCentralHoleEquiv k hk)).map_add (T : TemperedDistribution ℝ ℂ) (U : TemperedDistribution ℝ ℂ)
  map_smul' a T := by
    apply Subtype.ext
    exact (holeCorrection (poissonHeadSpace k hk)
      (ambientHoleObservation k hk S₁ S₂ hS₁ hS₂ (centralGridIndices k))
      (actualCentralHoleEquiv k hk)).map_smul a (T : TemperedDistribution ℝ ℂ)


/-- Delete exactly the specified atoms from a complete locally finite carrier. -/
def deleteCarrier (S : LocallyFiniteCarrier) (D : Set ℝ) : LocallyFiniteCarrier :=
  S.restrict (S.carrier \ D) (fun _ h => h.1)

/-- Deletion is equivalent to vanishing of the actual isolated coefficients.
The proof uses compact atomic formulas and full Schwartz-density continuity. -/
theorem atomicOn_deleteCarrier_iff (S : LocallyFiniteCarrier) (D : Set ℝ)
    (T : TemperedDistribution ℝ ℂ) :
    AtomicOnCarrier (deleteCarrier S D) T ↔
      AtomicOnCarrier S T ∧ ∀ x : S.subtype, (x : ℝ) ∈ D → T (S.isolationSchwartz x) = 0 := by
  constructor
  · intro hT
    refine ⟨fun f hf => hT f (fun x hx => hf x hx.1), ?_⟩
    intro x hx
    apply hT
    intro y hy
    exact S.isolationSchwartz_of_mem_of_ne x hy.1 (fun he => hy.2 (he ▸ hx))
  · rintro ⟨hT,hzero⟩
    intro f hf
    have hcompact (g : SchwartzMap ℝ ℂ) (hgc : HasCompactSupport g)
        (hg : SchwartzVanishesOn (deleteCarrier S D) g) : T g = 0 := by
      obtain ⟨E,_,he⟩ := atomicOnCarrier_isLocallyAtomicCoefficientFamily S T hT g hgc
      rw [he]
      apply Finset.sum_eq_zero
      intro x _
      by_cases hx : (x : ℝ) ∈ D
      · change T (S.isolationSchwartz x) * g x = 0
        rw [hzero x hx, zero_mul]
      · rw [hg x ⟨x.property,hx⟩, mul_zero]
    have hlim := (T.continuous.tendsto f).comp (compactSchwartzApproximation_tendsto f)
    have hzlim : Filter.Tendsto (fun N : ℕ => T (compactSchwartzApproximation N f))
        Filter.atTop (nhds (0 : ℂ)) := by
      have hz (N : ℕ) : T (compactSchwartzApproximation N f) = 0 :=
        hcompact _ (compactSchwartzApproximation_hasCompactSupport N f)
          (compactSchwartzApproximation_preserves_vanishing _ N f hf)
      simp only [hz]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique hlim hzlim

/-- Complete two-carrier source space, before or after finite holes. -/
def pairedAtomicSource (S₁ S₂ : LocallyFiniteCarrier) : Submodule ℂ (TemperedDistribution ℝ ℂ) :=
  schwartzAnnihilator (schwartzVanishingSubmodule S₁) ⊓
    (schwartzAnnihilator (schwartzVanishingSubmodule S₂)).comap temperedFourierLinearMap

@[simp] theorem mem_pairedAtomicSource (S₁ S₂ : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ) :
    T ∈ pairedAtomicSource S₁ S₂ ↔ AtomicOnCarrier S₁ T ∧ AtomicOnCarrier S₂ (𝓕 T) := Iff.rfl

/-- The actual hole atom set; no other head cells or tail atoms are removed. -/
def gridHoleSet {ι : Type*} (k : ℕ) (q : ι → ℤ) : Set ℝ :=
  Set.range (fun i => halfShiftedGridPoint k (q i))

/-- The complete deleted-carrier source is exactly the ambient observation
kernel inside the complete paired source space. -/
theorem pairedAtomicSource_delete_eq {ι : Type*} (k : ℕ) (hk : 1 ≤ k)
    (S₁ S₂ : LocallyFiniteCarrier)
    (hS₁ : (halfShiftedGridCarrier k hk).carrier ⊆ S₁.carrier)
    (hS₂ : (halfShiftedGridCarrier k hk).carrier ⊆ S₂.carrier) (q : ι → ℤ) :
    pairedAtomicSource (deleteCarrier S₁ (gridHoleSet k q)) (deleteCarrier S₂ (gridHoleSet k q)) =
      LinearMap.ker (ambientHoleObservation k hk S₁ S₂ hS₁ hS₂ q) ⊓ pairedAtomicSource S₁ S₂ := by
  ext T
  simp only [mem_pairedAtomicSource, atomicOn_deleteCarrier_iff, Submodule.mem_inf, LinearMap.mem_ker]
  constructor
  · rintro ⟨⟨hT,hzeroT⟩,⟨hF,hzeroF⟩⟩
    refine ⟨?_,hT,hF⟩
    funext i
    cases i with
    | inl i => exact hzeroT ⟨halfShiftedGridPoint k (q i),hS₁ ⟨q i,rfl⟩⟩ ⟨i,rfl⟩
    | inr i => exact hzeroF ⟨halfShiftedGridPoint k (q i),hS₂ ⟨q i,rfl⟩⟩ ⟨i,rfl⟩
  · rintro ⟨hz,hT,hF⟩
    refine ⟨⟨hT,?_⟩,⟨hF,?_⟩⟩
    · intro x hx
      obtain ⟨i,hi⟩ := hx
      have he := congrFun hz (.inl i)
      have hx' : x = ⟨halfShiftedGridPoint k (q i),hS₁ ⟨q i,rfl⟩⟩ := Subtype.ext hi.symm
      subst x
      exact he
    · intro x hx
      obtain ⟨i,hi⟩ := hx
      have he := congrFun hz (.inr i)
      have hx' : x = ⟨halfShiftedGridPoint k (q i),hS₂ ⟨q i,rfl⟩⟩ := Subtype.ext hi.symm
      subst x
      exact he

theorem poissonHeadSpace_le_pairedAtomicSource (k : ℕ) (hk : 1 ≤ k)
    (S₁ S₂ : LocallyFiniteCarrier)
    (hS₁ : (halfShiftedGridCarrier k hk).carrier ⊆ S₁.carrier)
    (hS₂ : (halfShiftedGridCarrier k hk).carrier ⊆ S₂.carrier) :
    poissonHeadSpace k hk ≤ pairedAtomicSource S₁ S₂ := by
  intro T hT
  have hw := (mem_poissonHeadSpace_iff_atomic_pair k hk T).mp hT
  exact ⟨fun f hf => hw.1 f (fun x hx => hf x (hS₁ hx)),
    fun f hf => hw.2 f (fun x hx => hf x (hS₂ hx))⟩


/-- Reversible exchange of the COMPLETE two deleted-carrier source spaces.
The ambient carriers may contain arbitrary additional locally finite tails. -/
def deletedCarrierHoleExchange (k : ℕ) (hk : 1 ≤ k)
    (S₁ S₂ : LocallyFiniteCarrier)
    (hS₁ : (halfShiftedGridCarrier k hk).carrier ⊆ S₁.carrier)
    (hS₂ : (halfShiftedGridCarrier k hk).carrier ⊆ S₂.carrier) :
    pairedAtomicSource (deleteCarrier S₁ (gridHoleSet k (triangularGridIndices k)))
      (deleteCarrier S₂ (gridHoleSet k (triangularGridIndices k))) ≃ₗ[ℂ]
    pairedAtomicSource (deleteCarrier S₁ (gridHoleSet k (centralGridIndices k)))
      (deleteCarrier S₂ (gridHoleSet k (centralGridIndices k))) := by
  rw [pairedAtomicSource_delete_eq k hk S₁ S₂ hS₁ hS₂,
    pairedAtomicSource_delete_eq k hk S₁ S₂ hS₁ hS₂]
  exact ambientTriangularCentralHoleExchange k hk S₁ S₂ hS₁ hS₂
    (pairedAtomicSource S₁ S₂) (poissonHeadSpace_le_pairedAtomicSource k hk S₁ S₂ hS₁ hS₂)

/-- Same-original-order exchange for the complete deleted-carrier spaces.
The native inclusion of the entire head is supplied by the actual H_-1 proof. -/
def deletedCarrierNativeHoleExchange (k : ℕ) (hk : 1 ≤ k)
    (S₁ S₂ : LocallyFiniteCarrier)
    (hS₁ : (halfShiftedGridCarrier k hk).carrier ⊆ S₁.carrier)
    (hS₂ : (halfShiftedGridCarrier k hk).carrier ⊆ S₂.carrier) (p : ℕ) (hp : 1 ≤ p) :
    ↥(pairedAtomicSource (deleteCarrier S₁ (gridHoleSet k (triangularGridIndices k)))
      (deleteCarrier S₂ (gridHoleSet k (triangularGridIndices k))) ⊓ originalNativeDistributionSpace p) ≃ₗ[ℂ]
    ↥(pairedAtomicSource (deleteCarrier S₁ (gridHoleSet k (centralGridIndices k)))
      (deleteCarrier S₂ (gridHoleSet k (centralGridIndices k))) ⊓ originalNativeDistributionSpace p) := by
  rw [pairedAtomicSource_delete_eq k hk S₁ S₂ hS₁ hS₂,
    pairedAtomicSource_delete_eq k hk S₁ S₂ hS₁ hS₂, inf_assoc, inf_assoc]
  exact ambientTriangularCentralHoleExchange k hk S₁ S₂ hS₁ hS₂
    (pairedAtomicSource S₁ S₂ ⊓ originalNativeDistributionSpace p)
    (le_inf (poissonHeadSpace_le_pairedAtomicSource k hk S₁ S₂ hS₁ hS₂)
      (poissonHeadSpace_le_native k hk p hp))

/-- Every complete original native-layer cardinal rank is preserved by the
actual triangular-to-central carrier surgery, with arbitrary complete tails. -/
theorem deletedCarrierNativeHoleExchange_rank (k : ℕ) (hk : 1 ≤ k)
    (S₁ S₂ : LocallyFiniteCarrier)
    (hS₁ : (halfShiftedGridCarrier k hk).carrier ⊆ S₁.carrier)
    (hS₂ : (halfShiftedGridCarrier k hk).carrier ⊆ S₂.carrier) (p : ℕ) (hp : 1 ≤ p) :
    Module.rank ℂ ↥(pairedAtomicSource (deleteCarrier S₁ (gridHoleSet k (triangularGridIndices k)))
      (deleteCarrier S₂ (gridHoleSet k (triangularGridIndices k))) ⊓ originalNativeDistributionSpace p) =
    Module.rank ℂ ↥(pairedAtomicSource (deleteCarrier S₁ (gridHoleSet k (centralGridIndices k)))
      (deleteCarrier S₂ (gridHoleSet k (centralGridIndices k))) ⊓ originalNativeDistributionSpace p) :=
  (deletedCarrierNativeHoleExchange k hk S₁ S₂ hS₁ hS₂ p hp).rank_eq

end
end MeyerGeneralProblem.Adaptive
