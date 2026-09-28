module

public import MeyerGeneralProblem.Cardinal.Adaptive.NativeTranslations
public import MeyerGeneralProblem.Sampling.KNSGraphMixedCompletion

@[expose] public section

/-!
# Original oscillator and ordered mixed derivatives

All estimates refer to the actual position and derivative maps on Schwartz
functions and the original normalized Hermite coefficient norm. Pair estimates
cost one Hermite order. No norm equivalence is inserted as an assumption.
-/

namespace MeyerGeneralProblem.Adaptive
noncomputable section
open MeasureTheory
open scoped FourierTransform

/-- Two position multiplications cost one original Hermite order. -/
theorem schwartzToHermiteScale_positionSquared_norm_bound (m : ℕ) (f : SchwartzMap ℝ ℂ) :
    ‖schwartzToHermiteScale m (coordinateMultiplicationCLM (coordinateMultiplicationCLM f))‖ ≤
      (‖Complex.I / (2 * (Real.pi : ℂ))‖^2 * (36 * Real.pi * 3^m)) *
        ‖schwartzToHermiteScale (m+1) f‖ := by
  rw [← schwartzToHermiteScale_fourier_norm m (coordinateMultiplicationCLM
    (coordinateMultiplicationCLM f)), fourier_coordinateMultiplicationCLM,
    fourier_coordinateMultiplicationCLM]
  simp only [map_smul, smul_smul, norm_smul, norm_mul]
  have h := mul_le_mul_of_nonneg_left (schwartzToHermiteScale_secondDerivative_norm_bound m (𝓕 f))
    (sq_nonneg ‖Complex.I / (2 * (Real.pi : ℂ))‖)
  rw [schwartzToHermiteScale_fourier_norm] at h
  simpa only [pow_two, mul_assoc] using h

/-- The exact product rule with multiplication by the real coordinate. -/
theorem derivative_coordinateMultiplication (f : SchwartzMap ℝ ℂ) :
    SchwartzMap.derivCLM ℂ ℂ (coordinateMultiplicationCLM f) =
      f + coordinateMultiplicationCLM (SchwartzMap.derivCLM ℂ ℂ f) := by
  ext x
  have he : (coordinateMultiplicationCLM f : ℝ → ℂ) = fun y : ℝ => (y:ℂ) * f y :=
    funext (coordinateMultiplicationCLM_apply f)
  rw [SchwartzMap.derivCLM_apply, he]
  have h := Complex.ofRealCLM.hasDerivAt.mul (f.hasDerivAt x)
  have hd : deriv (fun y : ℝ => (y:ℂ) * f y) x =
      (1:ℂ) * f x + (x:ℂ) * deriv (f : ℝ → ℂ) x := h.deriv
  simpa only [one_mul, add_apply, coordinateMultiplicationCLM_apply,
    SchwartzMap.derivCLM_apply] using hd

/-- Exact commutator of the original oscillator with the ordered mixed pair. -/
theorem graph_positionDerivative (f : SchwartzMap ℝ ℂ) :
    hermiteGraphOperator (coordinateMultiplicationCLM (SchwartzMap.derivCLM ℂ ℂ f)) =
      coordinateMultiplicationCLM (SchwartzMap.derivCLM ℂ ℂ (hermiteGraphOperator f)) -
        ((2 * (Real.pi : ℂ))⁻¹) •
          SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ f) -
        (2 * (Real.pi : ℂ)) • coordinateMultiplicationCLM (coordinateMultiplicationCLM f) := by
  simp only [hermiteGraphOperator, add_apply, smul_apply, neg_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    map_add, map_smul, map_neg, derivative_coordinateMultiplication]
  ext x
  simp only [add_apply, sub_apply, neg_apply, smul_apply, smul_eq_mul]
  field_simp
  ring

/-- An ordered position-derivative pair costs one original Hermite order,
for every input order. The base case is the existing checked original mixed
L2 estimate; the higher orders follow from the exact oscillator commutator. -/
theorem exists_positionDerivative_norm_bound (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : SchwartzMap ℝ ℂ,
      ‖schwartzToHermiteScale m (coordinateMultiplicationCLM (SchwartzMap.derivCLM ℂ ℂ f))‖ ≤
        C * ‖schwartzToHermiteScale (m+1) f‖ := by
  induction m with
  | zero =>
      refine ⟨3 * (1 + (2 * Real.pi)^4), by positivity, ?_⟩
      intro f
      rw [norm_schwartzToHermiteScale_zero]
      exact KNSGraphMixedCompletion.mixedSchwartz_norm_le f
  | succ m ih =>
      obtain ⟨C, hC, hbound⟩ := ih
      let D : ℝ := 36 * Real.pi * 3^m
      let X : ℝ := ‖Complex.I / (2 * (Real.pi : ℂ))‖^2 * D
      have hD : 0 ≤ D := by dsimp [D]; positivity
      have hX : 0 ≤ X := by dsimp [X]; positivity
      let B := C + ‖(2 * (Real.pi : ℂ))⁻¹‖ * D + ‖2 * (Real.pi : ℂ)‖ * X
      refine ⟨B, by dsimp [B]; positivity, ?_⟩
      intro f
      have hmain := hbound (hermiteGraphOperator f)
      rw [schwartzToHermiteScale_graph] at hmain
      have hmono := schwartzToHermiteScale_norm_mono (m+1) f
      have hDD : ‖schwartzToHermiteScale m (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ f))‖ ≤
          D * ‖schwartzToHermiteScale (m+2) f‖ :=
        (schwartzToHermiteScale_secondDerivative_norm_bound m f).trans
          (mul_le_mul_of_nonneg_left hmono hD)
      have hXX : ‖schwartzToHermiteScale m (coordinateMultiplicationCLM (coordinateMultiplicationCLM f))‖ ≤
          X * ‖schwartzToHermiteScale (m+2) f‖ :=
        (schwartzToHermiteScale_positionSquared_norm_bound m f).trans
          (mul_le_mul_of_nonneg_left hmono hX)
      rw [← schwartzToHermiteScale_graph m, graph_positionDerivative,
        map_sub, map_sub, map_smul, map_smul]
      have htri := (norm_sub_le
        (schwartzToHermiteScale m (coordinateMultiplicationCLM
          (SchwartzMap.derivCLM ℂ ℂ (hermiteGraphOperator f))) -
          ((2 * (Real.pi : ℂ))⁻¹) • schwartzToHermiteScale m
            (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ f)))
        ((2 * (Real.pi : ℂ)) • schwartzToHermiteScale m
          (coordinateMultiplicationCLM (coordinateMultiplicationCLM f)))).trans
          (add_le_add (norm_sub_le _ _) le_rfl)
      simp only [norm_smul] at htri
      have hD' := mul_le_mul_of_nonneg_left hDD (norm_nonneg ((2 * (Real.pi : ℂ))⁻¹))
      have hX' := mul_le_mul_of_nonneg_left hXX (norm_nonneg (2 * (Real.pi : ℂ)))
      dsimp only [B]
      nlinarith


/-- The actual ordered mixed operator `x^j` times the `k`th derivative. -/
def mixedSchwartz (j k : ℕ) (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  (coordinateMultiplicationCLM : SchwartzMap ℝ ℂ → SchwartzMap ℝ ℂ)^[j]
    ((SchwartzMap.derivCLM ℂ ℂ : SchwartzMap ℝ ℂ → SchwartzMap ℝ ℂ)^[k] f)

/-- Exact pointwise action of the ordered operator: an ordinary power of the
coordinate times the ordinary iterated derivative. -/
theorem mixedSchwartz_apply (j k : ℕ) (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    mixedSchwartz j k f x = (x:ℂ)^j * iteratedDeriv k (f : ℝ → ℂ) x := by
  unfold mixedSchwartz
  induction j with
  | zero => simp only [Function.iterate_zero_apply, pow_zero, one_mul,
      schwartzDerivative_iterate_apply]
  | succ j ih =>
      rw [Function.iterate_succ_apply', coordinateMultiplicationCLM_apply, ih, pow_succ]
      ring

/-- Monotonicity through any nonnegative number of original Hermite orders. -/
theorem schwartzToHermiteScale_norm_mono_add (q p : ℕ) (f : SchwartzMap ℝ ℂ) :
    ‖schwartzToHermiteScale q f‖ ≤ ‖schwartzToHermiteScale (q+p) f‖ := by
  induction p with
  | zero => simp
  | succ p ih => exact ih.trans (schwartzToHermiteScale_norm_mono (q+p) f)

private theorem positive_bound_of_nonnegative (q : ℕ)
    (U : SchwartzMap ℝ ℂ → SchwartzMap ℝ ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hU : ∀ f, ‖schwartzToHermiteScale q (U f)‖ ≤ C * ‖schwartzToHermiteScale (q+1) f‖) :
    ∃ A : ℝ, 0 < A ∧ ∀ f, ‖schwartzToHermiteScale q (U f)‖ ≤
      A * ‖schwartzToHermiteScale (q+1) f‖ := by
  refine ⟨C+1, by linarith, ?_⟩
  intro f
  exact (hU f).trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))

private theorem compose_one_order_bound (q p : ℕ)
    (U V : SchwartzMap ℝ ℂ → SchwartzMap ℝ ℂ)
    (hU : ∃ A : ℝ, 0 < A ∧ ∀ f, ‖schwartzToHermiteScale q (U f)‖ ≤
      A * ‖schwartzToHermiteScale (q+1) f‖)
    (hV : ∃ B : ℝ, 0 < B ∧ ∀ f, ‖schwartzToHermiteScale (q+1) (V f)‖ ≤
      B * ‖schwartzToHermiteScale ((q+1)+p) f‖) :
    ∃ C : ℝ, 0 < C ∧ ∀ f, ‖schwartzToHermiteScale q (U (V f))‖ ≤
      C * ‖schwartzToHermiteScale (q+(p+1)) f‖ := by
  obtain ⟨A, hA, hbA⟩ := hU
  obtain ⟨B, hB, hbB⟩ := hV
  refine ⟨A*B, mul_pos hA hB, ?_⟩
  intro f
  have h := (hbA (V f)).trans (mul_le_mul_of_nonneg_left (hbB f) hA.le)
  have he : (q+1)+p = q+(p+1) := by omega
  rw [he] at h
  simpa only [mul_assoc] using h

/-- Every actual ordered monomial of total degree at most `2*p` costs at
most `p` original Hermite orders. The input order `q` is arbitrary. -/
theorem exists_mixedSchwartz_norm_bound (p q j k : ℕ) (hjk : j+k ≤ 2*p) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : SchwartzMap ℝ ℂ,
      ‖schwartzToHermiteScale q (mixedSchwartz j k f)‖ ≤
        C * ‖schwartzToHermiteScale (q+p) f‖ := by
  induction p generalizing q j k with
  | zero =>
      have hj : j = 0 := by omega
      have hk : k = 0 := by omega
      subst j
      subst k
      refine ⟨1, by norm_num, ?_⟩
      intro f
      simp [mixedSchwartz]
  | succ p ih =>
      have hD : ∃ A : ℝ, 0 < A ∧ ∀ f : SchwartzMap ℝ ℂ,
          ‖schwartzToHermiteScale q (SchwartzMap.derivCLM ℂ ℂ f)‖ ≤
            A * ‖schwartzToHermiteScale (q+1) f‖ :=
        positive_bound_of_nonnegative q _ _ (by positivity)
          (schwartzToHermiteScale_derivative_norm_bound q)
      have hX : ∃ A : ℝ, 0 < A ∧ ∀ f : SchwartzMap ℝ ℂ,
          ‖schwartzToHermiteScale q (coordinateMultiplicationCLM f)‖ ≤
            A * ‖schwartzToHermiteScale (q+1) f‖ :=
        positive_bound_of_nonnegative q _ _ (by positivity)
          (schwartzToHermiteScale_position_norm_bound q)
      have hDD : ∃ A : ℝ, 0 < A ∧ ∀ f : SchwartzMap ℝ ℂ,
          ‖schwartzToHermiteScale q (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ f))‖ ≤
            A * ‖schwartzToHermiteScale (q+1) f‖ :=
        positive_bound_of_nonnegative q _ _ (by positivity)
          (schwartzToHermiteScale_secondDerivative_norm_bound q)
      have hXX : ∃ A : ℝ, 0 < A ∧ ∀ f : SchwartzMap ℝ ℂ,
          ‖schwartzToHermiteScale q (coordinateMultiplicationCLM (coordinateMultiplicationCLM f))‖ ≤
            A * ‖schwartzToHermiteScale (q+1) f‖ :=
        positive_bound_of_nonnegative q _ _ (by positivity)
          (schwartzToHermiteScale_positionSquared_norm_bound q)
      cases j with
      | zero =>
          cases k with
          | zero =>
              refine ⟨1, by norm_num, ?_⟩
              intro f
              simpa only [mixedSchwartz, Function.iterate_zero_apply, one_mul] using
                schwartzToHermiteScale_norm_mono_add q (p+1) f
          | succ k =>
              cases k with
              | zero =>
                  have h := compose_one_order_bound q p _ _ hD (ih (q+1) 0 0 (by omega))
                  simpa only [mixedSchwartz, Function.iterate_succ_apply',
                    Function.iterate_zero_apply] using h
              | succ k =>
                  have h := compose_one_order_bound q p _ _ hDD (ih (q+1) 0 k (by omega))
                  simpa only [mixedSchwartz, Function.iterate_succ_apply',
                    Function.iterate_zero_apply] using h
      | succ j =>
          cases j with
          | zero =>
              cases k with
              | zero =>
                  have h := compose_one_order_bound q p _ _ hX (ih (q+1) 0 0 (by omega))
                  simpa only [mixedSchwartz, Function.iterate_succ_apply',
                    Function.iterate_zero_apply] using h
              | succ k =>
                  have h := compose_one_order_bound q p _ _ (exists_positionDerivative_norm_bound q)
                    (ih (q+1) 0 k (by omega))
                  simpa only [mixedSchwartz, Function.iterate_succ_apply',
                    Function.iterate_zero_apply] using h
          | succ j =>
              have h := compose_one_order_bound q p _ _ hXX (ih (q+1) j k (by omega))
              simpa only [mixedSchwartz, Function.iterate_succ_apply',
                Function.iterate_zero_apply] using h

/-- At input order zero, the mixed operator is bounded in the actual L2 norm
by the original order-`p` Hermite norm, for all total degrees through `2*p`. -/
theorem exists_mixedSchwartz_toLp_norm_bound (p j k : ℕ) (hjk : j+k ≤ 2*p) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : SchwartzMap ℝ ℂ,
      ‖(mixedSchwartz j k f).toLp 2 volume‖ ≤ C * ‖schwartzToHermiteScale p f‖ := by
  obtain ⟨C, hC, hbound⟩ := exists_mixedSchwartz_norm_bound p 0 j k hjk
  refine ⟨C, hC, ?_⟩
  intro f
  have h := hbound f
  rw [Nat.zero_add, norm_schwartzToHermiteScale_zero] at h
  exact h

abbrev Xop : Module.End ℂ (SchwartzMap ℝ ℂ) :=
  coordinateMultiplicationCLM.toLinearMap
abbrev Dop : Module.End ℂ (SchwartzMap ℝ ℂ) :=
  (SchwartzMap.derivCLM ℂ ℂ).toLinearMap
abbrev Hop : Module.End ℂ (SchwartzMap ℝ ℂ) :=
  hermiteGraphOperator.toLinearMap
def mixedOp (j k : ℕ) : Module.End ℂ (SchwartzMap ℝ ℂ) := Xop^j * Dop^k

private theorem mixedOp_apply (j k : ℕ) (f : SchwartzMap ℝ ℂ) :
    mixedOp j k f = mixedSchwartz j k f := by
  simp only [mixedOp, Module.End.mul_apply, Module.End.pow_apply, mixedSchwartz]
  rfl

private theorem DX : Dop * Xop = 1 + Xop * Dop := by
  ext f x
  exact congrArg (fun g : SchwartzMap ℝ ℂ => g x) (derivative_coordinateMultiplication f)

private theorem D_powX (j : ℕ) :
    Dop * Xop^(j+1) = Xop^(j+1)*Dop + ((j+1:ℕ):ℂ) • Xop^j := by
  induction j with
  | zero => simpa only [zero_add, pow_one, Nat.cast_one, pow_zero, one_smul, add_comm] using DX
  | succ j ih =>
      calc
        Dop * Xop^(j+1+1) = (Dop * Xop^(j+1))*Xop := by rw [pow_succ, mul_assoc]
        _ = (Xop^(j+1)*Dop + ((j+1:ℕ):ℂ) • Xop^j)*Xop := by rw [ih]
        _ = Xop^(j+1)*(1+Xop*Dop) + ((j+1:ℕ):ℂ) • Xop^(j+1) := by
          rw [add_mul, smul_mul_assoc, mul_assoc, DX, pow_succ]
        _ = Xop^(j+1+1)*Dop + ((j+1+1:ℕ):ℂ) • Xop^(j+1) := by
          rw [mul_add, mul_one, ← mul_assoc, ← pow_succ]
          simp only [Nat.cast_add, Nat.cast_one]
          module

def mixedSpan (n : ℕ) : Submodule ℂ (Module.End ℂ (SchwartzMap ℝ ℂ)) :=
  Submodule.span ℂ {A | ∃ j k : ℕ, j+k ≤ n ∧ A = mixedOp j k}

private theorem mixedOp_mem (n j k : ℕ) (h : j+k ≤ n) : mixedOp j k ∈ mixedSpan n :=
  Submodule.subset_span ⟨j, k, h, rfl⟩

private theorem position_mixedSpan {n : ℕ} {A : Module.End ℂ (SchwartzMap ℝ ℂ)}
    (hA : A ∈ mixedSpan n) : Xop*A ∈ mixedSpan (n+1) := by
  induction hA using Submodule.span_induction with
  | mem A h =>
      obtain ⟨j,k,hjk,rfl⟩ := h
      have he : Xop*mixedOp j k = mixedOp (j+1) k := by
        simp only [mixedOp, pow_succ', mul_assoc]
      rw [he]
      exact mixedOp_mem _ _ _ (by omega)
  | zero => simp
  | add A B hA hB ihA ihB => simpa only [mul_add] using (mixedSpan (n+1)).add_mem ihA ihB
  | smul c A hA ih => simpa only [mul_smul_comm] using (mixedSpan (n+1)).smul_mem c ih

private theorem derivative_mixedSpan {n : ℕ} {A : Module.End ℂ (SchwartzMap ℝ ℂ)}
    (hA : A ∈ mixedSpan n) : Dop*A ∈ mixedSpan (n+1) := by
  induction hA using Submodule.span_induction with
  | mem A h =>
      obtain ⟨j,k,hjk,rfl⟩ := h
      cases j with
      | zero =>
          have he : Dop*mixedOp 0 k = mixedOp 0 (k+1) := by
            simp [mixedOp, pow_succ']
          rw [he]
          exact mixedOp_mem _ _ _ (by omega)
      | succ j =>
          have he : Dop*mixedOp (j+1) k =
              mixedOp (j+1) (k+1) + ((j+1:ℕ):ℂ) • mixedOp j k := by
            simp only [mixedOp, ← mul_assoc Dop, D_powX, add_mul, smul_mul_assoc,
              mul_assoc, ← pow_succ']
          rw [he]
          exact (mixedSpan (n+1)).add_mem (mixedOp_mem _ _ _ (by omega))
            ((mixedSpan (n+1)).smul_mem _ (mixedOp_mem _ _ _ (by omega)))
  | zero => simp
  | add A B hA hB ihA ihB => simpa only [mul_add] using (mixedSpan (n+1)).add_mem ihA ihB
  | smul c A hA ih => simpa only [mul_smul_comm] using (mixedSpan (n+1)).smul_mem c ih

private theorem mixedSpan_mono {n m : ℕ} (h : n ≤ m) : mixedSpan n ≤ mixedSpan m := by
  apply Submodule.span_le.mpr
  rintro A ⟨j,k,hjk,rfl⟩
  exact mixedOp_mem _ _ _ (hjk.trans h)

private theorem graph_mixedSpan {n : ℕ} {A : Module.End ℂ (SchwartzMap ℝ ℂ)}
    (hA : A ∈ mixedSpan n) : Hop*A ∈ mixedSpan (n+2) := by
  have he : Hop*A = -((4*(Real.pi:ℂ))⁻¹) • (Dop*(Dop*A)) +
      (Real.pi:ℂ) • (Xop*(Xop*A)) + (1/2:ℂ) • A := by
    ext f x
    simp [Hop, hermiteGraphOperator, Module.End.mul_apply, Dop, Xop]
    field_simp
  rw [he]
  exact (mixedSpan (n+2)).add_mem
    ((mixedSpan (n+2)).add_mem
      ((mixedSpan (n+2)).smul_mem _ (derivative_mixedSpan (derivative_mixedSpan hA)))
      ((mixedSpan (n+2)).smul_mem _ (position_mixedSpan (position_mixedSpan hA))))
    ((mixedSpan (n+2)).smul_mem _ (mixedSpan_mono (by omega) hA))

private theorem graph_pow_mem (p : ℕ) : Hop^p ∈ mixedSpan (2*p) := by
  induction p with
  | zero => simpa [mixedOp] using mixedOp_mem 0 0 0 (by omega)
  | succ p ih =>
      have h := graph_mixedSpan ih
      rw [← pow_succ'] at h
      have he : 2*(p+1) = 2*p+2 := by omega
      rw [he]
      exact h


/-- The finite triangle of actual weighted derivatives of total degree at most `n`. -/
def mixedIndices (n : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (n+1)).product (Finset.range (n+1))).filter (fun z => z.1+z.2 ≤ n)

@[simp] theorem mem_mixedIndices (n j k : ℕ) : (j,k) ∈ mixedIndices n ↔ j+k ≤ n := by
  simp [mixedIndices]
  omega

/-- Sum of genuine L2 norms of `x^j D^k f`, over `j+k ≤ n`. -/
def mixedL2Sum (n : ℕ) (f : SchwartzMap ℝ ℂ) : ℝ :=
  ∑ z ∈ mixedIndices n, ‖(mixedSchwartz z.1 z.2 f).toLp 2 volume‖

theorem mixedL2Sum_nonneg (n : ℕ) (f : SchwartzMap ℝ ℂ) : 0 ≤ mixedL2Sum n f :=
  Finset.sum_nonneg (fun _ _ => norm_nonneg _)

private theorem mixed_norm_le_sum (n j k : ℕ) (h : j+k ≤ n) (f : SchwartzMap ℝ ℂ) :
    ‖(mixedSchwartz j k f).toLp 2 volume‖ ≤ mixedL2Sum n f := by
  unfold mixedL2Sum
  apply Finset.single_le_sum (a := (j,k))
    (f := fun z : ℕ × ℕ => ‖(mixedSchwartz z.1 z.2 f).toLp 2 volume‖)
  · intro z hz; exact norm_nonneg _
  · exact (mem_mixedIndices n j k).mpr h

private theorem span_norm_bound {n : ℕ} {A : Module.End ℂ (SchwartzMap ℝ ℂ)}
    (hA : A ∈ mixedSpan n) : ∃ C : ℝ, 0 < C ∧ ∀ f : SchwartzMap ℝ ℂ,
      ‖(A f).toLp 2 volume‖ ≤ C * mixedL2Sum n f := by
  induction hA using Submodule.span_induction with
  | mem A h =>
      obtain ⟨j,k,hjk,rfl⟩ := h
      refine ⟨1, by norm_num, ?_⟩
      intro f
      simpa only [one_mul, mixedOp_apply] using mixed_norm_le_sum n j k hjk f
  | zero =>
      refine ⟨1, by norm_num, ?_⟩
      intro f
      change ‖SchwartzMap.toLpCLM ℂ ℂ 2 volume 0‖ ≤ _
      simpa only [map_zero, norm_zero, one_mul] using mixedL2Sum_nonneg n f
  | add A B hA hB ihA ihB =>
      obtain ⟨C,hC,hbC⟩ := ihA
      obtain ⟨D,hD,hbD⟩ := ihB
      refine ⟨C+D, add_pos hC hD, ?_⟩
      intro f
      change ‖SchwartzMap.toLpCLM ℂ ℂ 2 volume (A f+B f)‖ ≤ _
      rw [map_add]
      exact (norm_add_le _ _).trans ((add_le_add (hbC f) (hbD f)).trans_eq (by ring))
  | smul c A hA ih =>
      obtain ⟨C,hC,hbC⟩ := ih
      refine ⟨‖c‖*C+1, by positivity, ?_⟩
      intro f
      change ‖SchwartzMap.toLpCLM ℂ ℂ 2 volume (c • A f)‖ ≤ _
      rw [map_smul, norm_smul]
      have h := mul_le_mul_of_nonneg_left (hbC f) (norm_nonneg c)
      change ‖c‖ * ‖(A f).toLp 2 volume‖ ≤ _
      have hs := mixedL2Sum_nonneg n f
      nlinarith

private theorem norm_graph_pow (p : ℕ) (f : SchwartzMap ℝ ℂ) :
    ‖((Hop^p) f).toLp 2 volume‖ = ‖schwartzToHermiteScale p f‖ := by
  induction p generalizing f with
  | zero => simpa using (norm_schwartzToHermiteScale_zero f).symm
  | succ p ih =>
      rw [pow_succ, Module.End.mul_apply, ih]
      exact congrArg norm (schwartzToHermiteScale_graph p f)

/-- The original order-`p` oscillator norm is controlled by the actual finite
sum of weighted derivative L2 norms of total degree through `2*p`. -/
theorem exists_hermite_norm_le_mixedL2Sum (p : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : SchwartzMap ℝ ℂ,
      ‖schwartzToHermiteScale p f‖ ≤ C * mixedL2Sum (2*p) f := by
  obtain ⟨C,hC,hbC⟩ := span_norm_bound (graph_pow_mem p)
  refine ⟨C,hC,?_⟩
  intro f
  simpa only [norm_graph_pow] using hbC f

/-- The actual finite sum of all weighted derivative L2 norms of total degree
through `2*p` is controlled by the original order-`p` oscillator norm. -/
theorem exists_mixedL2Sum_le_hermite_norm (p : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : SchwartzMap ℝ ℂ,
      mixedL2Sum (2*p) f ≤ C * ‖schwartzToHermiteScale p f‖ := by
  classical
  have hb : ∀ z ∈ mixedIndices (2*p), ∃ C : ℝ, 0 < C ∧ ∀ f : SchwartzMap ℝ ℂ,
      ‖(mixedSchwartz z.1 z.2 f).toLp 2 volume‖ ≤ C * ‖schwartzToHermiteScale p f‖ := by
    intro z hz
    exact exists_mixedSchwartz_toLp_norm_bound p z.1 z.2
      ((mem_mixedIndices (2*p) z.1 z.2).mp hz)
  choose C hC using hb
  let B : ℝ := ∑ z : {z // z ∈ mixedIndices (2*p)}, C z.1 z.2
  have hB : 0 < B := by
    apply Finset.sum_pos'
    · intro z hz; exact (hC z.1 z.2).1.le
    · refine ⟨⟨(0,0), by simp⟩, Finset.mem_univ _, ?_⟩
      exact (hC _ _).1
  refine ⟨B,hB,?_⟩
  intro f
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun (z : {z // z ∈ mixedIndices (2*p)}) _ => (hC z.1 z.2).2 f)
  rw [← Finset.sum_mul] at hsum
  have he := Finset.sum_coe_sort (mixedIndices (2*p))
    (fun z => ‖(mixedSchwartz z.1 z.2 f).toLp 2 volume‖)
  rw [he] at hsum
  exact hsum

end
end MeyerGeneralProblem.Adaptive
