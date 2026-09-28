module

public import MeyerGeneralProblem.Sampling.BeurlingInterpolation

@[expose] public section

/-!
# Whole-cluster Haraux removal

The actual averaged-shift operator is iterated at each node in a finite
cluster. Its spectral product annihilates every cluster node before any
coefficient norm is taken. The energy loss depends only on cluster size,
not on internal node gaps or the number of exterior frequencies.
-/

namespace MeyerGeneralProblem

noncomputable section

open MeasureTheory

/-- Iterated actual averaged-shift removals at a finite list of frequencies. -/
def clusterHarauxRemoval (r : ℝ) : List ℝ → (ℝ → ℂ) → ℝ → ℂ
  | [], f => f
  | ω :: nodes, f => harauxFrequencyRemoval r ω (clusterHarauxRemoval r nodes f)

/-- The exact real spectral multiplier of all removals in a finite cluster. -/
def clusterHarauxMultiplier (r : ℝ) (nodes : List ℝ) (s : ℝ) : ℝ :=
  (nodes.map (fun ω => harauxMultiplier r ω s)).prod

/-- The iterated operator acts on actual finite exponential polynomials by
the product of its sinc-defect multipliers. -/
theorem clusterHarauxRemoval_gramFourierPolynomial
    {n : ℕ} (s : Fin n → ℝ) (c : Fin n → ℂ) {r : ℝ} (hr : 0 < r)
    (nodes : List ℝ) (t : ℝ) :
    clusterHarauxRemoval r nodes (gramFourierPolynomial s c) t =
      gramFourierPolynomial s (fun i => (clusterHarauxMultiplier r nodes (s i) : ℂ) * c i) t := by
  induction nodes generalizing t with
  | nil => simp [clusterHarauxRemoval, clusterHarauxMultiplier]
  | cons ω nodes ih =>
    have heq : clusterHarauxRemoval r nodes (gramFourierPolynomial s c) =
        gramFourierPolynomial s (fun i => (clusterHarauxMultiplier r nodes (s i) : ℂ) * c i) := by
      funext t
      exact ih t
    rw [clusterHarauxRemoval, heq, harauxFrequencyRemoval_gramFourierPolynomial s _ hr]
    simp only [clusterHarauxMultiplier, List.map_cons, List.prod_cons, Complex.ofReal_mul,
      mul_assoc]

/-- Every frequency in the removal list is annihilated exactly, without any
estimate involving inverse internal gaps. Repeated removals are permitted. -/
theorem clusterHarauxMultiplier_eq_zero_of_mem
    (r : ℝ) (nodes : List ℝ) (s : ℝ) (hs : s ∈ nodes) :
    clusterHarauxMultiplier r nodes s = 0 := by
  induction nodes with
  | nil => simp at hs
  | cons ω nodes ih =>
    simp only [List.mem_cons] at hs
    simp only [clusterHarauxMultiplier, List.map_cons, List.prod_cons]
    rcases hs with rfl | hs
    · simp only [harauxMultiplier_self, zero_mul]
    · rw [show (nodes.map (fun ω => harauxMultiplier r ω s)).prod = 0 from ih hs, mul_zero]

/-- A common positive exterior separation gives a product lower bound;
the exponent is the number of removed nodes, not the exterior dimension. -/
theorem pow_length_le_clusterHarauxMultiplier
    {r κ : ℝ} (hκ : 0 ≤ κ) (nodes : List ℝ) (s : ℝ)
    (hbound : ∀ ω ∈ nodes, κ ≤ harauxMultiplier r ω s) :
    κ ^ nodes.length ≤ clusterHarauxMultiplier r nodes s := by
  induction nodes with
  | nil => simp [clusterHarauxMultiplier]
  | cons ω nodes ih =>
    have hω := hbound ω (by simp)
    have hnodes := ih (fun x hx => hbound x (by simp [hx]))
    simp only [List.length_cons, clusterHarauxMultiplier, List.map_cons, List.prod_cons] at *
    rw [pow_succ']
    exact mul_le_mul hω hnodes (pow_nonneg hκ _) (hκ.trans hω)

/-- Each actual removal costs at most four in window energy. Iteration
enlarges the window by exactly `length * r`, independently of all gaps. -/
theorem integral_clusterHarauxRemoval_sq_le
    {n : ℕ} (s : Fin n → ℝ) (c : Fin n → ℂ) {r b : ℝ}
    (hr : 0 < r) (hb : 0 ≤ b) (nodes : List ℝ) :
    (∫ t : ℝ in Set.Icc (-b) b,
      ‖clusterHarauxRemoval r nodes (gramFourierPolynomial s c) t‖ ^ 2) ≤
      (4 : ℝ) ^ nodes.length *
        ∫ t : ℝ in Set.Icc (-(b + nodes.length * r)) (b + nodes.length * r),
          ‖gramFourierPolynomial s c t‖ ^ 2 := by
  induction nodes generalizing b with
  | nil => simp [clusterHarauxRemoval]
  | cons ω nodes ih =>
    let d : Fin n → ℂ := fun i => (clusterHarauxMultiplier r nodes (s i) : ℂ) * c i
    have heq : clusterHarauxRemoval r nodes (gramFourierPolynomial s c) =
        gramFourierPolynomial s d := by
      funext t
      exact clusterHarauxRemoval_gramFourierPolynomial s c hr nodes t
    have hone := integral_harauxFrequencyRemoval_sq_le s d hb hr ω
    have hrest := ih (b := b + r) (by linarith)
    rw [heq] at hrest
    have hmul := mul_le_mul_of_nonneg_left hrest (by norm_num : (0 : ℝ) ≤ 4)
    have hwindow : b + r + (nodes.length : ℝ) * r = b + ((ω :: nodes).length : ℝ) * r := by
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
      ring
    rw [hwindow] at hmul
    rw [clusterHarauxRemoval, heq]
    simpa only [List.length_cons, pow_succ', mul_assoc] using hone.trans hmul

/-- Concatenation represents the sum of two actual finite exponential polynomials. -/
theorem gramFourierPolynomial_append {n k : ℕ}
    (s : Fin n → ℝ) (ω : Fin k → ℝ) (c : Fin n → ℂ) (a : Fin k → ℂ) (t : ℝ) :
    gramFourierPolynomial (Fin.append s ω) (Fin.append c a) t =
      gramFourierPolynomial s c t + gramFourierPolynomial ω a t := by
  simp [gramFourierPolynomial, Fin.sum_univ_add]

/-- Removing a whole cluster annihilates its entire exponential polynomial
before taking any norm, while retaining the explicit exterior multipliers. -/
theorem clusterHarauxRemoval_append_eq
    {n k : ℕ} (s : Fin n → ℝ) (ω : Fin k → ℝ)
    (c : Fin n → ℂ) (a : Fin k → ℂ) {r : ℝ} (hr : 0 < r) (t : ℝ) :
    clusterHarauxRemoval r (List.ofFn ω)
      (fun u => gramFourierPolynomial s c u + gramFourierPolynomial ω a u) t =
        gramFourierPolynomial s
          (fun i => (clusterHarauxMultiplier r (List.ofFn ω) (s i) : ℂ) * c i) t := by
  have heq : (fun u => gramFourierPolynomial s c u + gramFourierPolynomial ω a u) =
      gramFourierPolynomial (Fin.append s ω) (Fin.append c a) :=
    (funext (gramFourierPolynomial_append s ω c a)).symm
  rw [heq, clusterHarauxRemoval_gramFourierPolynomial _ _ hr]
  have hz (i : Fin k) : clusterHarauxMultiplier r (List.ofFn ω) (ω i) = 0 :=
    clusterHarauxMultiplier_eq_zero_of_mem r (List.ofFn ω) (ω i)
      (List.mem_ofFn.mpr ⟨i, rfl⟩)
  simp [gramFourierPolynomial, Fin.sum_univ_add, hz]

/-- A separated exterior family with a true window lower bound retains a
uniform coefficient estimate after adding an arbitrary whole cluster.
Only exterior-to-cluster separation occurs; no internal cluster gap is used. -/
theorem exterior_coefficient_bound_after_cluster_removal
    {n k : ℕ} (s : Fin n → ℝ) (ω : Fin k → ℝ)
    {r b A κ : ℝ} (hr : 0 < r) (hb : 0 ≤ b) (hA : 0 ≤ A) (hκ : 0 ≤ κ)
    (hκbound : ∀ i j, κ ≤ harauxMultiplier r (ω j) (s i))
    (hlower : ∀ c : Fin n → ℂ, A * ∑ i, ‖c i‖ ^ 2 ≤
      ∫ t : ℝ in Set.Icc (-b) b, ‖gramFourierPolynomial s c t‖ ^ 2)
    (c : Fin n → ℂ) (a : Fin k → ℂ) :
    A * κ ^ (2 * k) * ∑ i, ‖c i‖ ^ 2 ≤
      (4 : ℝ) ^ k * ∫ t : ℝ in Set.Icc (-(b + k * r)) (b + k * r),
        ‖gramFourierPolynomial s c t + gramFourierPolynomial ω a t‖ ^ 2 := by
  let d : Fin n → ℂ := fun i => (clusterHarauxMultiplier r (List.ofFn ω) (s i) : ℂ) * c i
  have hmult (i : Fin n) : κ ^ k ≤ clusterHarauxMultiplier r (List.ofFn ω) (s i) := by
    have h := pow_length_le_clusterHarauxMultiplier hκ (List.ofFn ω) (s i) (by
      intro x hx
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
      exact hκbound i j)
    simpa only [List.length_ofFn] using h
  have hcoeff : κ ^ (2 * k) * ∑ i, ‖c i‖ ^ 2 ≤ ∑ i, ‖d i‖ ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hm := hmult i
    have hsquare := (sq_le_sq₀ (pow_nonneg hκ _) ((pow_nonneg hκ _).trans hm)).mpr hm
    simp only [d, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    rw [mul_comm 2 k, pow_mul]
    exact mul_le_mul_of_nonneg_right hsquare (sq_nonneg _)
  have hlower' := (mul_le_mul_of_nonneg_left hcoeff hA).trans (hlower d)
  have henergy := integral_clusterHarauxRemoval_sq_le
    (Fin.append s ω) (Fin.append c a) hr hb (List.ofFn ω)
  have heq : gramFourierPolynomial (Fin.append s ω) (Fin.append c a) =
      fun t => gramFourierPolynomial s c t + gramFourierPolynomial ω a t :=
    funext (gramFourierPolynomial_append s ω c a)
  rw [heq] at henergy
  simp only [clusterHarauxRemoval_append_eq s ω c a hr, List.length_ofFn] at henergy
  simpa only [mul_assoc] using hlower'.trans henergy

/-- One positive exterior coefficient constant works for every cluster of
size at most `q`, regardless of its internal gaps or the exterior dimension.
The only supplied lower inequality concerns the original exterior family. -/
theorem exists_uniform_exterior_bound_after_cluster_removal
    (q : ℕ) {r d A : ℝ} (hr : 0 < r) (hd : 0 < d) (hA : 0 < A) :
    ∃ P : ℝ, 0 < P ∧ ∀ b : ℝ, 0 ≤ b → ∀ n k : ℕ, k ≤ q →
      ∀ (s : Fin n → ℝ) (ω : Fin k → ℝ),
      (∀ i j, d ≤ |s i - ω j|) →
      (∀ c : Fin n → ℂ, A * ∑ i, ‖c i‖ ^ 2 ≤
        ∫ t : ℝ in Set.Icc (-b) b, ‖gramFourierPolynomial s c t‖ ^ 2) →
      ∀ (c : Fin n → ℂ) (a : Fin k → ℂ),
        P * ∑ i, ‖c i‖ ^ 2 ≤
          ∫ t : ℝ in Set.Icc (-(b + q * r)) (b + q * r),
            ‖gramFourierPolynomial s c t + gramFourierPolynomial ω a t‖ ^ 2 := by
  obtain ⟨κ, hκ, hκbound⟩ := exists_pos_le_harauxMultiplier hr hd
  let K := min κ 1
  have hK : 0 < K := lt_min hκ zero_lt_one
  have hK1 : K ≤ 1 := min_le_right _ _
  refine ⟨A * K ^ (2 * q) / 4 ^ q, by positivity, ?_⟩
  intro b hb n k hk s ω hsep hlower c a
  have hbase := exterior_coefficient_bound_after_cluster_removal s ω hr hb hA.le hK.le
    (fun i j => (min_le_left _ _).trans (hκbound (ω j) (s i) (hsep i j))) hlower c a
  let f : ℝ → ℝ := fun t => ‖gramFourierPolynomial s c t + gramFourierPolynomial ω a t‖ ^ 2
  have hf : Continuous f := by unfold f gramFourierPolynomial gramPhase; fun_prop
  have hkr : (k:ℝ) * r ≤ (q:ℝ) * r := by gcongr
  have hwindow : (∫ t in Set.Icc (-(b + k * r)) (b + k * r), f t) ≤
      ∫ t in Set.Icc (-(b + q * r)) (b + q * r), f t := by
    apply setIntegral_mono_set (hf.continuousOn.integrableOn_compact isCompact_Icc)
      (Filter.Eventually.of_forall fun t => sq_nonneg _)
    exact Filter.Eventually.of_forall (fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  have hE : 0 ≤ ∫ t in Set.Icc (-(b + q * r)) (b + q * r), f t :=
    integral_nonneg (fun t => sq_nonneg _)
  have hpowers : (4:ℝ)^k ≤ 4^q := pow_le_pow_right₀ (by norm_num) hk
  have hupper := (mul_le_mul_of_nonneg_left hwindow (by positivity : (0:ℝ) ≤ 4^k)).trans
    (mul_le_mul_of_nonneg_right hpowers hE)
  have hKpowers : K^(2*q) ≤ K^(2*k) := pow_le_pow_of_le_one hK.le hK1 (by omega)
  have hQ : 0 ≤ ∑ i, ‖c i‖ ^ 2 := Finset.sum_nonneg (fun i hi => sq_nonneg _)
  have hlower' := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hKpowers hA.le) hQ
  have htotal := hlower'.trans (hbase.trans hupper)
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0:ℝ) < 4^q)]
  simpa only [mul_comm] using htotal

end

end MeyerGeneralProblem
