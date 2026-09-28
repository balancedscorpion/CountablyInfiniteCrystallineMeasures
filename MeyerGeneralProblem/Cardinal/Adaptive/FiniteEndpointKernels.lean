module

public import MeyerGeneralProblem.Cardinal.Adaptive.PoissonHeads

@[expose] public section

/-! # Finite critical endpoint kernels

The finite proof uses a maximal nonzero signed grid block. Newton factors
kill earlier nodes, and maximality kills later nodes. The remaining diagonal
block retains the full gauge and its sine/cosine obstruction.
-/
namespace MeyerGeneralProblem.Adaptive
noncomputable section

/-- The four signed masses of one finite grid cell. False is positive. -/
abbrev SignedMassBlock := Bool → Bool → ℂ

/-- The parity transform on the four actual signed masses. -/
def massParity (c : SignedMassBlock) (e f : Bool) : ℂ :=
  c false false + (if f then -1 else 1) * c false true +
    (if e then -1 else 1) * c true false +
    (if e then -1 else 1) * (if f then -1 else 1) * c true true

@[simp] theorem massParity_zero (e f : Bool) : massParity 0 e f = 0 := by
  simp [massParity]

/-- The four parity moments faithfully determine all four signed masses. -/
theorem massParity_injective : Function.Injective massParity := by
  intro c d h
  have h00 := congrFun (congrFun h false) false
  have h01 := congrFun (congrFun h false) true
  have h10 := congrFun (congrFun h true) false
  have h11 := congrFun (congrFun h true) true
  simp only [massParity, Bool.false_eq_true, ite_false, ite_true] at h00 h01 h10 h11
  funext u v
  cases u <;> cases v
  · linear_combination (h00+h01+h10+h11)/4
  · linear_combination (h00-h01+h10-h11)/4
  · linear_combination (h00+h01-h10-h11)/4
  · linear_combination (h00-h01-h10+h11)/4

/-- Exact finite signed-grid Fourier gauge, with its original negative sign. -/
def signedGauge (θ : ℝ) (c : SignedMassBlock) : SignedMassBlock :=
  fun u v => Complex.exp (-(θ : ℂ)*Complex.I*(if u = v then 1 else -1)) * c u v

@[simp] theorem signedGauge_zero (θ : ℝ) : signedGauge θ 0 = 0 := by
  funext u v
  simp [signedGauge]

theorem signedGauge_injective (θ : ℝ) : Function.Injective (signedGauge θ) := by
  intro c d h
  funext u v
  exact mul_left_cancel₀ (Complex.exp_ne_zero _) (congrFun (congrFun h u) v)

/-- The full gauge couples complementary parities exactly. -/
theorem massParity_signedGauge (θ : ℝ) (c : SignedMassBlock) (e f : Bool) :
    massParity (signedGauge θ c) e f =
      (Real.cos θ : ℂ) * massParity c e f -
        Complex.I * (Real.sin θ : ℂ) * massParity c (!e) (!f) := by
  have hp : Complex.exp ((θ : ℂ)*Complex.I) =
      (Real.cos θ : ℂ) + (Real.sin θ : ℂ)*Complex.I := by
    rw [Complex.exp_mul_I]
    simp
  have hn : Complex.exp (-((θ : ℂ)*Complex.I)) =
      (Real.cos θ : ℂ) - (Real.sin θ : ℂ)*Complex.I := by
    have h := Complex.exp_mul_I (-(θ : ℂ))
    simpa [sub_eq_add_neg] using h
  cases e <;> cases f <;>
    simp [massParity, signedGauge, hp, hn] <;> ring

/-- At a diagonal critical endpoint, the two physical and two Fourier flags
annihilate the entire signed block when the actual sine and cosine are nonzero. -/
theorem signedGauge_diagonal_kernel (θ : ℝ) (c : SignedMassBlock)
    (hs : Real.sin θ ≠ 0) (hc : Real.cos θ ≠ 0)
    (hA : ∀ e, massParity c e false = 0)
    (hB : ∀ f, massParity (signedGauge θ c) false f = 0) : c = 0 := by
  have h11 : massParity c true true = 0 := by
    have h := hB false
    rw [massParity_signedGauge, hA false] at h
    simp only [Bool.not_false, mul_zero, zero_sub, neg_eq_zero] at h
    exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hs))
  have h01 : massParity c false true = 0 := by
    have h := hB true
    rw [massParity_signedGauge] at h
    simp only [Bool.not_false, Bool.not_true, hA true, mul_zero, sub_zero] at h
    exact (mul_eq_zero.mp h).resolve_left (by exact_mod_cast hc)
  apply massParity_injective
  funext e f
  cases e <;> cases f <;> simp [hA, h11, h01]

/-- Finite normalized Newton moments; the node weights are separated from
signed parity so that vanishing at all earlier nodes is visible. -/
def finiteFlagMoment {k : ℕ} (wA wB : Fin k → Fin k → ℂ)
    (κA κB : Fin k → ℂ) (c : Fin k → Fin k → SignedMassBlock)
    (i j : Fin k) (e f : Bool) : ℂ :=
  ∑ I, ∑ J, (wA i I * wB j J * (if e then κA I else 1) *
    (if f then κB J else 1)) * massParity (c I J) e f

/-- A maximal nonzero grid block isolates its exact local parity moments;
this is a finite support argument, without an infinite-array maximality step. -/
theorem finiteFlagMoment_at_max {k : ℕ} (wA wB : Fin k → Fin k → ℂ)
    (κA κB : Fin k → ℂ) (c : Fin k → Fin k → SignedMassBlock)
    (hA : ∀ i I, I < i → wA i I = 0)
    (hB : ∀ j J, J < j → wB j J = 0)
    (i j : Fin k) (hmax : ∀ (I J : Fin k), (i : ℕ)+j < (I : ℕ)+J → c I J = 0)
    (e f : Bool) :
    finiteFlagMoment wA wB κA κB c i j e f =
      (wA i i * wB j j * (if e then κA i else 1) * (if f then κB j else 1)) *
        massParity (c i j) e f := by
  unfold finiteFlagMoment
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · intro J _ hJi
      rcases lt_or_gt_of_ne hJi with hlt|hgt
      · simp [hB j J hlt]
      · simp [hmax i J (by exact Nat.add_lt_add_left hgt _)]
    · simp
  · intro I _ hIi
    apply Finset.sum_eq_zero
    intro J _
    rcases lt_or_gt_of_ne hIi with hlt|hgt
    · simp [hA i I hlt]
    · by_cases hJ : J < j
      · simp [hB j J hJ]
      · have hm : (i : ℕ)+j < (I : ℕ)+J := by
          have : (i : ℕ) < I := hgt
          have : (j : ℕ) ≤ J := le_of_not_gt hJ
          omega
        simp [hmax I J hm]
  · simp


/-- The finite critical two-flag kernel is zero. The full gauge is evaluated
on every actual signed mass block, and the argument uses only finite descent.
The hypotheses are explicit Newton moment equations, not inverse witnesses. -/
theorem finite_critical_flag_kernel {k : ℕ} (wA wB : Fin k → Fin k → ℂ)
    (κA κB : Fin k → ℂ) (θ : Fin k → Fin k → ℝ)
    (c : Fin k → Fin k → SignedMassBlock)
    (hwA : ∀ i I, I < i → wA i I = 0)
    (hwB : ∀ j J, J < j → wB j J = 0)
    (hdA : ∀ i, wA i i ≠ 0) (hdB : ∀ j, wB j j ≠ 0)
    (hκA : ∀ i, κA i ≠ 0) (hκB : ∀ j, κB j ≠ 0)
    (hsin : ∀ i, Real.sin (θ i i) ≠ 0) (hcos : ∀ i, Real.cos (θ i i) ≠ 0)
    (hflagA : ∀ (i j : Fin k) (e f : Bool), (j : ℕ)+f.toNat ≤ (i : ℕ) →
      finiteFlagMoment wA wB κA κB c i j e f = 0)
    (hflagB : ∀ (i j : Fin k) (e f : Bool), (i : ℕ)+e.toNat ≤ (j : ℕ) →
      finiteFlagMoment wA wB κA κB (fun I J => signedGauge (θ I J) (c I J)) i j e f = 0) :
    c = 0 := by
  have hall : ∀ d : ℕ, ∀ i j : Fin k, 2*k-((i : ℕ)+j) = d → c i j = 0 := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro i j hd
      have hmax (I J : Fin k) (hlt : (i : ℕ)+j < (I : ℕ)+J) : c I J = 0 := by
        apply ih (2*k-((I : ℕ)+J)) _ I J rfl
        have hi := i.isLt
        have hj := j.isLt
        have hI := I.isLt
        have hJ := J.isLt
        omega
      have hmaxG (I J : Fin k) (hlt : (i : ℕ)+j < (I : ℕ)+J) :
          signedGauge (θ I J) (c I J) = 0 := by rw [hmax I J hlt, signedGauge_zero]
      have hcoeff (e f : Bool) :
          wA i i * wB j j * (if e then κA i else 1) * (if f then κB j else 1) ≠ 0 := by
        cases e <;> cases f <;> simp [hdA, hdB, hκA, hκB]
      have hPA (e f : Bool) (hf : (j : ℕ)+f.toNat ≤ (i : ℕ)) :
          massParity (c i j) e f = 0 := by
        have h := hflagA i j e f hf
        rw [finiteFlagMoment_at_max wA wB κA κB c hwA hwB i j hmax e f] at h
        exact (mul_eq_zero.mp h).resolve_left (hcoeff e f)
      have hPB (e f : Bool) (he : (i : ℕ)+e.toNat ≤ (j : ℕ)) :
          massParity (signedGauge (θ i j) (c i j)) e f = 0 := by
        have h := hflagB i j e f he
        rw [finiteFlagMoment_at_max wA wB κA κB _ hwA hwB i j hmaxG e f] at h
        exact (mul_eq_zero.mp h).resolve_left (hcoeff e f)
      rcases lt_trichotomy i j with hlt|heq|hgt
      · apply signedGauge_injective (θ i j)
        rw [signedGauge_zero]
        apply massParity_injective
        funext e f
        rw [massParity_zero]
        apply hPB
        cases e <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
      · subst j
        apply signedGauge_diagonal_kernel (θ i i) (c i i) (hsin i) (hcos i)
        · intro e
          exact hPA e false (by simp)
        · intro f
          exact hPB false f (by simp)
      · apply massParity_injective
        funext e f
        rw [massParity_zero]
        apply hPA
        cases f <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
  funext i j
  exact hall _ i j rfl

/-- Every interior positive phase pair supplies the required nonzero diagonal
sine and cosine, without a smallness or separation constant. -/
theorem interior_phase_diagonal_nonzero {a b : ℝ}
    (ha : 0 < a ∧ a < 1/2) (hb : 0 < b ∧ b < 1/2) :
    Real.sin (2*Real.pi*a*b) ≠ 0 ∧ Real.cos (2*Real.pi*a*b) ≠ 0 := by
  have hp := Real.pi_pos
  have hab : 0 < a*b := mul_pos ha.1 hb.1
  have hu : a*b < (1/4 : ℝ) := by nlinarith
  have hθ0 : 0 < 2*Real.pi*a*b := by nlinarith
  have hθ1 : 2*Real.pi*a*b < Real.pi/2 := by nlinarith
  exact ⟨(Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith)).ne',
    (Real.cos_pos_of_mem_Ioo ⟨by linarith, hθ1⟩).ne'⟩


/-- Actual cosine node used by the critical Newton extraction. -/
def criticalNewtonNode (t : ℝ) : ℂ := (1-Real.cos (2*Real.pi*t) : ℝ)

/-- Evaluation of the i-th Newton polynomial on the I-th positive node. -/
def criticalNewtonWeight {k : ℕ} (η : Fin k → ℝ) (i I : Fin k) : ℂ :=
  ∏ l ∈ Finset.Iio i, (criticalNewtonNode (η I)-criticalNewtonNode (η l))

/-- The actual sine at a positive interior phase. -/
def criticalSineNode {k : ℕ} (η : Fin k → ℝ) (i : Fin k) : ℂ :=
  (Real.sin (2*Real.pi*η i) : ℝ)

theorem criticalNewtonWeight_before {k : ℕ} (η : Fin k → ℝ) (i I : Fin k)
    (h : I < i) : criticalNewtonWeight η i I = 0 := by
  unfold criticalNewtonWeight
  exact Finset.prod_eq_zero (Finset.mem_Iio.mpr h) (sub_self _)

theorem criticalNewtonNode_injective_on_interior {a b : ℝ}
    (ha : 0 < a ∧ a < 1/2) (hb : 0 < b ∧ b < 1/2)
    (h : criticalNewtonNode a = criticalNewtonNode b) : a = b := by
  have hc : Real.cos (2*Real.pi*a) = Real.cos (2*Real.pi*b) := by
    have hr := Complex.ofReal_injective h
    linarith
  have hp := Real.pi_pos
  have hea : 2*Real.pi*a ∈ Set.Icc 0 Real.pi := by
    constructor <;> nlinarith [ha.1, ha.2]
  have heb : 2*Real.pi*b ∈ Set.Icc 0 Real.pi := by
    constructor <;> nlinarith [hb.1, hb.2]
  have he := Real.injOn_cos hea heb hc
  nlinarith

theorem criticalNewtonWeight_diagonal_ne_zero {k : ℕ} (η : Fin k → ℝ)
    (hη : Function.Injective η) (hint : ∀ i, 0 < η i ∧ η i < 1/2) (i : Fin k) :
    criticalNewtonWeight η i i ≠ 0 := by
  unfold criticalNewtonWeight
  apply Finset.prod_ne_zero_iff.mpr
  intro l hl
  apply sub_ne_zero.mpr
  intro he
  have hi := hη (criticalNewtonNode_injective_on_interior (hint i) (hint l) he)
  exact (ne_of_lt (Finset.mem_Iio.mp hl)) hi.symm

theorem criticalSineNode_ne_zero {k : ℕ} (η : Fin k → ℝ)
    (hint : ∀ i, 0 < η i ∧ η i < 1/2) (i : Fin k) : criticalSineNode η i ≠ 0 := by
  have hp := Real.pi_pos
  have hi := hint i
  have hs : 0 < Real.sin (2*Real.pi*η i) :=
    Real.sin_pos_of_pos_of_lt_pi (by nlinarith) (by nlinarith)
  unfold criticalSineNode
  exact_mod_cast hs.ne'

/-- The actual finite signed phase-grid Newton flags have zero kernel for
arbitrary distinct interior phase heads. No ordering or smallness is required. -/
theorem actual_finite_newton_flag_kernel {k : ℕ} (α β : Fin k → ℝ)
    (hα : Function.Injective α) (hβ : Function.Injective β)
    (hintα : ∀ i, 0 < α i ∧ α i < 1/2) (hintβ : ∀ j, 0 < β j ∧ β j < 1/2)
    (c : Fin k → Fin k → SignedMassBlock)
    (hA : ∀ (i j : Fin k) (e f : Bool), (j : ℕ)+f.toNat ≤ (i : ℕ) →
      finiteFlagMoment (criticalNewtonWeight α) (criticalNewtonWeight β)
        (criticalSineNode α) (criticalSineNode β) c i j e f = 0)
    (hB : ∀ (i j : Fin k) (e f : Bool), (i : ℕ)+e.toNat ≤ (j : ℕ) →
      finiteFlagMoment (criticalNewtonWeight α) (criticalNewtonWeight β)
        (criticalSineNode α) (criticalSineNode β)
        (fun I J => signedGauge (2*Real.pi*α I*β J) (c I J)) i j e f = 0) : c = 0 := by
  apply finite_critical_flag_kernel (criticalNewtonWeight α) (criticalNewtonWeight β)
    (criticalSineNode α) (criticalSineNode β) (fun i j => 2*Real.pi*α i*β j) c
    (criticalNewtonWeight_before α) (criticalNewtonWeight_before β)
    (criticalNewtonWeight_diagonal_ne_zero α hα hintα)
    (criticalNewtonWeight_diagonal_ne_zero β hβ hintβ)
    (criticalSineNode_ne_zero α hintα) (criticalSineNode_ne_zero β hintβ)
    (fun i => (interior_phase_diagonal_nonzero (hintα i) (hintβ i)).1)
    (fun i => (interior_phase_diagonal_nonzero (hintα i) (hintβ i)).2) hA hB


/-- Integer character in the original Fourier normalization. -/
def criticalCharacter (n : ℤ) (x : ℝ) : ℂ :=
  Complex.exp (2*(Real.pi : ℂ)*Complex.I*(n : ℂ)*(x : ℂ))

/-- Finite trigonometric bandwidth, as a span of the actual integer characters. -/
def criticalTrigBand (d : ℕ) : Submodule ℂ (ℝ → ℂ) :=
  Submodule.span ℂ {f | ∃ n : ℤ, |n| ≤ (d : ℤ) ∧ f = criticalCharacter n}

theorem criticalCharacter_mem_band (d : ℕ) (n : ℤ) (hn : |n| ≤ (d : ℤ)) :
    criticalCharacter n ∈ criticalTrigBand d :=
  Submodule.subset_span ⟨n,hn,rfl⟩

@[simp] theorem criticalCharacter_zero : criticalCharacter 0 = (1 : ℝ → ℂ) := by
  funext x
  simp [criticalCharacter]

theorem criticalCharacter_mul (n m : ℤ) :
    criticalCharacter n * criticalCharacter m = criticalCharacter (n+m) := by
  funext x
  simp only [Pi.mul_apply, criticalCharacter, Int.cast_add]
  rw [← Complex.exp_add]
  congr 1
  ring

theorem criticalTrigBand_mono {d e : ℕ} (h : d ≤ e) : criticalTrigBand d ≤ criticalTrigBand e := by
  apply Submodule.span_le.mpr
  rintro f ⟨n,hn,rfl⟩
  exact criticalCharacter_mem_band e n (hn.trans (by exact_mod_cast h))

theorem criticalTrigBand_one (d : ℕ) : (1 : ℝ → ℂ) ∈ criticalTrigBand d := by
  rw [← criticalCharacter_zero]
  exact criticalCharacter_mem_band d 0 (by simp)

theorem criticalTrigBand_const (d : ℕ) (c : ℂ) : (fun _ : ℝ => c) ∈ criticalTrigBand d := by
  convert (criticalTrigBand d).smul_mem c (criticalTrigBand_one d) using 1
  funext x
  simp

/-- Bandwidths add under pointwise multiplication, proved on the actual
character generators and extended by finite linearity. -/
theorem criticalTrigBand_mul {d e : ℕ} {f g : ℝ → ℂ}
    (hf : f ∈ criticalTrigBand d) (hg : g ∈ criticalTrigBand e) :
    f*g ∈ criticalTrigBand (d+e) := by
  apply Submodule.span_induction₂ (p := fun f g _ _ => f*g ∈ criticalTrigBand (d+e))
    (s := {f | ∃ n : ℤ, |n| ≤ (d : ℤ) ∧ f = criticalCharacter n})
    (t := {g | ∃ n : ℤ, |n| ≤ (e : ℤ) ∧ g = criticalCharacter n})
    _ _ _ _ _ _ _ hf hg
  · rintro f g ⟨n,hn,rfl⟩ ⟨m,hm,rfl⟩
    rw [criticalCharacter_mul]
    apply criticalCharacter_mem_band
    have h := abs_add_le n m
    push_cast
    omega
  · intro g _
    simp
  · intro f _
    simp
  · intro f g h _ _ _ hf hg
    simpa only [add_mul] using (criticalTrigBand (d+e)).add_mem hf hg
  · intro f g h _ _ _ hg hh
    simpa only [mul_add] using (criticalTrigBand (d+e)).add_mem hg hh
  · intro c f g _ _ h
    simpa only [smul_mul_assoc] using (criticalTrigBand (d+e)).smul_mem c h
  · intro c f g _ _ h
    simpa only [mul_smul_comm] using (criticalTrigBand (d+e)).smul_mem c h

private theorem criticalCharacter_pos_neg (x : ℝ) :
    criticalCharacter 1 x = (Real.cos (2*Real.pi*x) : ℂ) +
        (Real.sin (2*Real.pi*x) : ℂ)*Complex.I ∧
    criticalCharacter (-1) x = (Real.cos (2*Real.pi*x) : ℂ) -
        (Real.sin (2*Real.pi*x) : ℂ)*Complex.I := by
  have hp : 2*(Real.pi : ℂ)*Complex.I*(1 : ℤ)*(x : ℂ) =
      ((2*Real.pi*x : ℝ) : ℂ)*Complex.I := by push_cast; ring
  have hn : 2*(Real.pi : ℂ)*Complex.I*((-1 : ℤ) : ℂ)*(x : ℂ) =
      (-((2*Real.pi*x : ℝ) : ℂ))*Complex.I := by push_cast; ring
  constructor
  · unfold criticalCharacter
    rw [hp, Complex.exp_mul_I]
    simp
  · unfold criticalCharacter
    rw [hn, Complex.exp_mul_I]
    simp [sub_eq_add_neg]

theorem criticalNewtonNode_mem_band : criticalNewtonNode ∈ criticalTrigBand 1 := by
  have hpos := criticalCharacter_mem_band 1 1 (by norm_num)
  have hneg := criticalCharacter_mem_band 1 (-1) (by norm_num)
  have h := (criticalTrigBand 1).sub_mem (criticalTrigBand_one 1)
    ((criticalTrigBand 1).smul_mem (1/2 : ℂ) ((criticalTrigBand 1).add_mem hpos hneg))
  convert h using 1
  funext x
  rcases criticalCharacter_pos_neg x with ⟨hp,hn⟩
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.add_apply, Pi.one_apply, smul_eq_mul, hp, hn, criticalNewtonNode]
  push_cast
  ring

theorem criticalSine_mem_band : (fun x => (Real.sin (2*Real.pi*x) : ℂ)) ∈ criticalTrigBand 1 := by
  have hpos := criticalCharacter_mem_band 1 1 (by norm_num)
  have hneg := criticalCharacter_mem_band 1 (-1) (by norm_num)
  have h := (criticalTrigBand 1).smul_mem (-(Complex.I)/2)
    ((criticalTrigBand 1).sub_mem hpos hneg)
  convert h using 1
  funext x
  rcases criticalCharacter_pos_neg x with ⟨hp,hn⟩
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, hp, hn]
  linear_combination (Real.sin (2*Real.pi*x) : ℂ) * Complex.I_mul_I


private theorem criticalTrigBand_prod {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℂ)
    (hf : ∀ a ∈ s, f a ∈ criticalTrigBand 1) :
    (∏ a ∈ s, f a) ∈ criticalTrigBand s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using criticalTrigBand_one 0
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    have h := criticalTrigBand_mul (hf a (Finset.mem_insert_self _ _))
      (ih (fun b hb => hf b (Finset.mem_insert_of_mem hb)))
    simpa only [Nat.add_comm 1] using h

/-- The actual finite sine/Newton test function used in the critical flags. -/
def criticalNewtonTest {k : ℕ} (η : Fin k → ℝ) (i : Fin k) (e : Bool) (x : ℝ) : ℂ :=
  (∏ l ∈ Finset.Iio i, (criticalNewtonNode x-criticalNewtonNode (η l))) *
    (if e then (Real.sin (2*Real.pi*x) : ℂ) else 1)

/-- Exact bandwidth of the actual test. This pays the finite-frequency step
needed to turn original cell holes into the Newton flags. -/
theorem criticalNewtonTest_mem_band {k : ℕ} (η : Fin k → ℝ) (i : Fin k) (e : Bool) :
    criticalNewtonTest η i e ∈ criticalTrigBand ((i : ℕ)+e.toNat) := by
  have hprod := criticalTrigBand_prod (Finset.Iio i)
    (fun l => criticalNewtonNode - fun _ : ℝ => criticalNewtonNode (η l))
    (fun l _ => (criticalTrigBand 1).sub_mem criticalNewtonNode_mem_band
      (criticalTrigBand_const 1 _))
  rw [Fin.card_Iio] at hprod
  cases e
  · simp only [Bool.toNat_false, Nat.add_zero]
    convert hprod using 1
    funext x
    simp [criticalNewtonTest]
  · simp only [Bool.toNat_true]
    have h := criticalTrigBand_mul hprod criticalSine_mem_band
    convert h using 1
    funext x
    simp [criticalNewtonTest]

/-- Signed phases with the positive phase at false. -/
def criticalSignedPhase (u : Bool) (a : ℝ) : ℝ := if u then -a else a

/-- The scalar signed parity at a node. -/
def criticalParitySign (u e : Bool) : ℂ := if e then (if u then -1 else 1) else 1

theorem criticalNewtonTest_at_signed {k : ℕ} (η : Fin k → ℝ)
    (i I : Fin k) (e u : Bool) :
    criticalNewtonTest η i e (criticalSignedPhase u (η I)) =
      criticalNewtonWeight η i I * (if e then criticalSineNode η I else 1) *
        criticalParitySign u e := by
  cases u <;> cases e <;>
    simp [criticalNewtonTest, criticalSignedPhase, criticalNewtonWeight,
      criticalSineNode, criticalParitySign, criticalNewtonNode, mul_neg]

/-- Evaluation of a test against one finite signed phase row. -/
def finiteSignedRow {k : ℕ} (η : Fin k → ℝ) (a : Fin k → Bool → ℂ) :
    (ℝ → ℂ) →ₗ[ℂ] ℂ where
  toFun f := ∑ I, ∑ u, f (criticalSignedPhase u (η I))*a I u
  map_add' f g := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' c f := by simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc, RingHom.id_apply]

/-- Vanishing of every actual integer-frequency sample in a bandwidth kills
every test in that bandwidth, by finite linearity. -/
theorem finiteSignedRow_eq_zero_of_band {k d : ℕ} (η : Fin k → ℝ)
    (a : Fin k → Bool → ℂ)
    (h : ∀ n : ℤ, |n| ≤ (d : ℤ) → finiteSignedRow η a (criticalCharacter n) = 0)
    {f : ℝ → ℂ} (hf : f ∈ criticalTrigBand d) : finiteSignedRow η a f = 0 := by
  have hle : criticalTrigBand d ≤ LinearMap.ker (finiteSignedRow η a) := by
    apply Submodule.span_le.mpr
    rintro g ⟨n,hn,rfl⟩
    exact h n hn
  exact hle hf

/-- Exact finite signed-mass formula for the Newton moments. -/
theorem finiteFlagMoment_eq_rows {k : ℕ} (α β : Fin k → ℝ)
    (c : Fin k → Fin k → SignedMassBlock) (i j : Fin k) (e f : Bool) :
    finiteFlagMoment (criticalNewtonWeight α) (criticalNewtonWeight β)
      (criticalSineNode α) (criticalSineNode β) c i j e f =
      ∑ I, ∑ u, criticalNewtonTest α i e (criticalSignedPhase u (α I)) *
        finiteSignedRow β (fun J v => c I J u v) (criticalNewtonTest β j f) := by
  unfold finiteFlagMoment finiteSignedRow
  simp only [LinearMap.coe_mk, AddHom.coe_mk, criticalNewtonTest_at_signed]
  apply Finset.sum_congr rfl
  intro I _
  simp only [Fintype.sum_bool, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro J _
  cases e <;> cases f <;> simp [criticalParitySign, massParity] <;> ring


/-- The ORIGINAL triangular physical cell holes imply the first complete
Newton flag. The degree/parity equality boundary is included. -/
theorem critical_physical_samples_imply_flag {k : ℕ} (α β : Fin k → ℝ)
    (c : Fin k → Fin k → SignedMassBlock)
    (hholes : ∀ (I : Fin k) (u : Bool) (n : ℤ), |n| ≤ (I : ℤ) →
      finiteSignedRow β (fun J v => c I J u v) (criticalCharacter n) = 0)
    (i j : Fin k) (e f : Bool) (hij : (j : ℕ)+f.toNat ≤ (i : ℕ)) :
    finiteFlagMoment (criticalNewtonWeight α) (criticalNewtonWeight β)
      (criticalSineNode α) (criticalSineNode β) c i j e f = 0 := by
  rw [finiteFlagMoment_eq_rows]
  apply Finset.sum_eq_zero
  intro I _
  apply Finset.sum_eq_zero
  intro u _
  by_cases hI : I < i
  · rw [criticalNewtonTest_at_signed, criticalNewtonWeight_before α i I hI]
    simp
  · have hband : criticalNewtonTest β j f ∈ criticalTrigBand (I : ℕ) :=
      criticalTrigBand_mono (by have : (i : ℕ) ≤ I := le_of_not_gt hI; omega)
        (criticalNewtonTest_mem_band β j f)
    rw [finiteSignedRow_eq_zero_of_band β (fun J v => c I J u v) (hholes I u) hband,
      mul_zero]

private theorem massParity_transpose (c : SignedMassBlock) (e f : Bool) :
    massParity (fun u v => c v u) f e = massParity c e f := by
  cases e <;> cases f <;> simp [massParity] <;> ring

/-- Swapping the two complete grid coordinates preserves the actual Newton
moment, with both parities swapped. -/
theorem finiteFlagMoment_swap {k : ℕ} (wA wB : Fin k → Fin k → ℂ)
    (κA κB : Fin k → ℂ) (c : Fin k → Fin k → SignedMassBlock)
    (i j : Fin k) (e f : Bool) :
    finiteFlagMoment wA wB κA κB c i j e f =
      finiteFlagMoment wB wA κB κA (fun J I u v => c I J v u) j i f e := by
  unfold finiteFlagMoment
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro J _
  apply Finset.sum_congr rfl
  intro I _
  rw [massParity_transpose]
  ring

/-- Every finite signed source satisfying the original two triangular
sample systems vanishes. Both complete Fourier phases are retained in
` signedGauge `; no inverse or Newton-flag hypothesis is supplied. -/
theorem critical_triangular_samples_kernel {k : ℕ} (α β : Fin k → ℝ)
    (hα : Function.Injective α) (hβ : Function.Injective β)
    (hintα : ∀ i, 0 < α i ∧ α i < 1/2) (hintβ : ∀ j, 0 < β j ∧ β j < 1/2)
    (c : Fin k → Fin k → SignedMassBlock)
    (hphysical : ∀ (I : Fin k) (u : Bool) (n : ℤ), |n| ≤ (I : ℤ) →
      finiteSignedRow β (fun J v => c I J u v) (criticalCharacter n) = 0)
    (hfourier : ∀ (J : Fin k) (v : Bool) (n : ℤ), |n| ≤ (J : ℤ) →
      finiteSignedRow α (fun I u => signedGauge (2*Real.pi*α I*β J) (c I J) u v)
        (criticalCharacter (-n)) = 0) : c = 0 := by
  apply actual_finite_newton_flag_kernel α β hα hβ hintα hintβ c
  · exact critical_physical_samples_imply_flag α β c hphysical
  · intro i j e f hij
    rw [finiteFlagMoment_swap]
    apply critical_physical_samples_imply_flag β α _ _ j i f e hij
    intro J v n hn
    have h := hfourier J v (-n) (by simpa using hn)
    simpa only [neg_neg] using h

end
end MeyerGeneralProblem.Adaptive
