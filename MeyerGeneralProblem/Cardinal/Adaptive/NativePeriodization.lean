module

public import MeyerGeneralProblem.Cardinal.Adaptive.UnitPartition
public import MeyerGeneralProblem.Cardinal.Adaptive.HeadNativeBounds
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import all Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
import all Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

/-! # Original-norm estimates for smooth compact periodization -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open MeasureTheory
open scoped ContDiff

private theorem point_norm_sq_le (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    ‖f x‖^2 ≤ 2*‖f.toLp 2 volume‖^2 + ‖(SchwartzMap.derivCLM ℂ ℂ f).toLp 2 volume‖^2 := by
  have h := sum_norm_sq_le_globalSobolev (fun _ : Fin 1 => x) f
    (SchwartzMap.derivCLM ℂ ℂ f) (fun t => f.hasDerivAt t)
    (SchwartzMap.derivCLM ℂ ℂ f).continuous (f.memLp 2 volume)
    ((SchwartzMap.derivCLM ℂ ℂ f).memLp 2 volume) (d := 1) (by norm_num)
    (by intro i j hij; exact False.elim (hij (Subsingleton.elim _ _)))
  simpa only [Fin.sum_univ_one, inv_one, mul_one, one_mul,
    SchwartzMap.norm_toLp, Lp.norm_toLp] using h

private theorem derivative_mixed_zero (k : ℕ) (f : SchwartzMap ℝ ℂ) :
    SchwartzMap.derivCLM ℂ ℂ (mixedSchwartz 0 k f) = mixedSchwartz 0 (k+1) f := by
  simp only [mixedSchwartz, Function.iterate_zero_apply, Function.iterate_succ_apply']

private theorem derivative_mixed_two (k : ℕ) (f : SchwartzMap ℝ ℂ) :
    SchwartzMap.derivCLM ℂ ℂ (mixedSchwartz 2 k f) =
      (2:ℂ) • mixedSchwartz 1 k f + mixedSchwartz 2 (k+1) f := by
  simp only [mixedSchwartz, Function.iterate_succ_apply', Function.iterate_zero_apply,
    derivative_coordinateMultiplication, map_add]
  module

/-- Original order `p` controls the inverse-square point decay of every
actual derivative whose degree plus three fits within `2*p`. -/
theorem exists_weighted_derivative_point_bound (p k : ℕ) (hk : k+3 ≤ 2*p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : SchwartzMap ℝ ℂ) (x : ℝ),
      (1+|x|)^2 * ‖iteratedDeriv k (f : ℝ → ℂ) x‖ ≤ C*‖schwartzToHermiteScale p f‖ := by
  obtain ⟨A,hA,ha⟩ := exists_mixedL2Sum_le_hermite_norm p
  have hm (j l : ℕ) (hjl : j+l ≤ 2*p) (f : SchwartzMap ℝ ℂ) :
      ‖(mixedSchwartz j l f).toLp 2 volume‖ ≤ A*‖schwartzToHermiteScale p f‖ := by
    exact (Finset.single_le_sum (s := mixedIndices (2*p)) (a := (j,l))
      (f := fun z : ℕ×ℕ => ‖(mixedSchwartz z.1 z.2 f).toLp 2 volume‖)
      (fun _ _ => norm_nonneg _) ((mem_mixedIndices (2*p) j l).mpr hjl)).trans (ha f)
  refine ⟨12*A, by positivity, ?_⟩
  intro f x
  let g := mixedSchwartz 0 k f + mixedSchwartz 2 k f
  let H := ‖schwartzToHermiteScale p f‖
  have hg : ‖g.toLp 2 volume‖ ≤ 2*A*H := by
    change ‖SchwartzMap.toLpCLM ℂ ℂ 2 volume (mixedSchwartz 0 k f + mixedSchwartz 2 k f)‖ ≤ _
    rw [map_add]
    exact (norm_add_le _ _).trans ((add_le_add (hm 0 k (by omega) f)
      (hm 2 k (by omega) f)).trans_eq (by ring))
  have hdg : ‖(SchwartzMap.derivCLM ℂ ℂ g).toLp 2 volume‖ ≤ 4*A*H := by
    change ‖SchwartzMap.toLpCLM ℂ ℂ 2 volume (SchwartzMap.derivCLM ℂ ℂ
      (mixedSchwartz 0 k f+mixedSchwartz 2 k f))‖ ≤ _
    rw [map_add, derivative_mixed_zero, derivative_mixed_two, map_add, map_add, map_smul]
    have h := (norm_add_le
      (SchwartzMap.toLpCLM ℂ ℂ 2 volume (mixedSchwartz 0 (k+1) f))
      ((2:ℂ) • SchwartzMap.toLpCLM ℂ ℂ 2 volume (mixedSchwartz 1 k f) +
        SchwartzMap.toLpCLM ℂ ℂ 2 volume (mixedSchwartz 2 (k+1) f))).trans
          (add_le_add le_rfl (norm_add_le _ _))
    simp only [norm_smul, Complex.norm_ofNat] at h
    have h0 := hm 0 (k+1) (by omega) f
    have h1 := hm 1 k (by omega) f
    have h2 := hm 2 (k+1) (by omega) f
    apply h.trans
    change ‖(mixedSchwartz 0 (k+1) f).toLp 2 volume‖ +
      (2*‖(mixedSchwartz 1 k f).toLp 2 volume‖+‖(mixedSchwartz 2 (k+1) f).toLp 2 volume‖) ≤ _
    dsimp only [H]
    linarith
  have hx : ‖g x‖ ≤ 6*A*H := by
    have h := point_norm_sq_le g x
    have h0 := pow_le_pow_left₀ (norm_nonneg _) hg 2
    have h1 := pow_le_pow_left₀ (norm_nonneg _) hdg 2
    have hn : 0 ≤ 6*A*H := by dsimp [H]; positivity
    nlinarith [sq_nonneg (A*H), norm_nonneg (g x)]
  have he : ‖g x‖ = (1+x^2)*‖iteratedDeriv k (f : ℝ → ℂ) x‖ := by
    have hfun : g x = (1+(x:ℂ)^2)*iteratedDeriv k (f : ℝ → ℂ) x := by
      simp only [g, add_apply, mixedSchwartz_apply, pow_zero, one_mul]
      ring
    rw [hfun, norm_mul]
    have hn : ‖(1:ℂ)+(x:ℂ)^2‖ = 1+x^2 := by
      have he : (1:ℂ)+(x:ℂ)^2 = ((1+x^2:ℝ):ℂ) := by push_cast; rfl
      rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [hn]
  rw [he] at hx
  have hw : (1+|x|)^2 ≤ 2*(1+x^2) := by nlinarith [sq_nonneg (|x|-1), sq_abs x]
  have hh := mul_le_mul_of_nonneg_right hw (norm_nonneg (iteratedDeriv k (f : ℝ → ℂ) x))
  dsimp only [H] at hx
  nlinarith

/-- On the fixed compact partition support, all translated derivatives have
an inverse-square summable bound at the exact original order `q+2`. -/
theorem exists_compact_translate_derivative_bound (q k : ℕ) (hk : k ≤ 2*q) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : SchwartzMap ℝ ℂ) (x : ℝ), |x| ≤ 1 → ∀ n : ℤ,
      ‖iteratedDeriv k (f : ℝ → ℂ) (x+n)‖ ≤
        C*‖schwartzToHermiteScale (q+2) f‖ * integerCombDecay n := by
  obtain ⟨A,hA,hbound⟩ := exists_weighted_derivative_point_bound (q+2) k (by omega)
  refine ⟨4*A, by positivity, ?_⟩
  intro f x hx n
  have hn : |(n:ℝ)| ≤ |x+(n:ℝ)|+1 := by
    have h := abs_sub (x+(n:ℝ)) x
    have he : x+(n:ℝ)-x = n := by ring
    rw [he] at h
    linarith
  have hp : 0 < (1+|(n:ℝ)|)^2 := by positivity
  rw [integerCombDecay, inv_pow, ← div_eq_mul_inv, le_div_iff₀ hp]
  have h := hbound f (x+n)
  have hw : (1+|(n:ℝ)|)^2 ≤ 4*(1+|x+(n:ℝ)|)^2 := by
    nlinarith [abs_nonneg (n:ℝ), abs_nonneg (x+(n:ℝ))]
  have hh := mul_le_mul_of_nonneg_right hw
    (norm_nonneg (iteratedDeriv k (f : ℝ → ℂ) (x+n)))
  nlinarith


/-- The concrete unit-period compact Schwartz partition from `UnitPartition`. -/
def unitPartitionSchwartz : SchwartzMap ℝ ℂ :=
  periodicSchwartzRepresentative (fun _ => 1) contDiff_const

@[simp] theorem unitPartitionSchwartz_apply (x : ℝ) :
    unitPartitionSchwartz x = (unitPartition x : ℂ) := by
  simp [unitPartitionSchwartz]

theorem unitPartitionSchwartz_tsupport :
    tsupport (unitPartitionSchwartz : ℝ → ℂ) ⊆ Set.Icc (-1) 1 := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  apply unitPartition_support
  intro he
  apply hx
  simp [he]

/-- Actual smooth compact partition at every nonzero period. -/
def periodizationCutoff (P : ℝ) (hP : P ≠ 0) : SchwartzMap ℝ ℂ :=
  combSchwartzDilation P⁻¹ (inv_ne_zero hP) unitPartitionSchwartz

@[simp] theorem periodizationCutoff_apply (P : ℝ) (hP : P ≠ 0) (x : ℝ) :
    periodizationCutoff P hP x = (unitPartition (x/P) : ℂ) := by
  simp only [periodizationCutoff, combSchwartzDilation_apply, unitPartitionSchwartz_apply,
    div_eq_mul_inv, mul_comm]

/-- The complete translated partition is exactly one at every point. -/
theorem periodizationCutoff_sum (P : ℝ) (hP : P ≠ 0) (x : ℝ) :
    ∑' n : ℤ, periodizationCutoff P hP (x+n*P) = 1 := by
  have he (n : ℤ) : (x+(n:ℝ)*P)/P = x/P+n := by field_simp
  simp_rw [periodizationCutoff_apply, he]
  rw [← Complex.ofReal_tsum, unitPartition_sum, Complex.ofReal_one]

private theorem mixed_compact_support (g : SchwartzMap ℝ ℂ)
    (hg : tsupport (g : ℝ → ℂ) ⊆ Set.Icc (-1) 1) (j k : ℕ) :
    Function.support (mixedSchwartz j k g : ℝ → ℂ) ⊆ Set.Icc (-1) 1 := by
  have hd (r : ℕ) : tsupport (iteratedDeriv r (g : ℝ → ℂ)) ⊆ tsupport (g : ℝ → ℂ) := by
    induction r with
    | zero => simp only [iteratedDeriv_zero]; exact Set.Subset.rfl
    | succ r ih => rw [iteratedDeriv_succ]; exact tsupport_deriv_subset.trans ih
  intro x hx
  apply hg
  apply hd k
  apply subset_closure
  intro hz
  apply hx
  simp only [mixedSchwartz_apply, hz, mul_zero]

private theorem toLp_le_sum {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (hc : ∀ i ∈ s, 0 ≤ c i) (u : SchwartzMap ℝ ℂ) (v : ι → SchwartzMap ℝ ℂ)
    (h : ∀ x, ‖u x‖ ≤ ∑ i ∈ s, c i * ‖v i x‖) :
    ‖u.toLp 2 volume‖ ≤ ∑ i ∈ s, c i * ‖(v i).toLp 2 volume‖ := by
  have hl (f : SchwartzMap ℝ ℂ) : lpNorm (f : ℝ → ℂ) 2 volume = ‖f.toLp 2 volume‖ := by
    rw [SchwartzMap.norm_toLp, toReal_eLpNorm]
  let w : ι → ℝ → ℝ := fun i x => c i * ‖v i x‖
  have hw (i : ι) : MemLp (w i) 2 volume := ((v i).memLp 2 volume).norm.const_mul _
  have hs : MemLp (∑ i ∈ s, w i) 2 volume := by
    convert memLp_finsetSum s (fun i hi => hw i) using 1
    ext x; simp
  have hm := lpNorm_mono_real hs (f := (u : ℝ → ℂ))
    (by intro x; simpa only [Finset.sum_apply, w] using h x)
  rw [hl] at hm
  apply hm.trans ((lpNorm_sum_le (fun i hi => hw i) (by norm_num)).trans_eq ?_)
  apply Finset.sum_congr rfl
  intro i hi
  change lpNorm (c i • (fun x : ℝ => ‖v i x‖)) 2 volume = _
  rw [lpNorm_const_smul, lpNorm_norm ((v i).memLp 2 volume).aestronglyMeasurable, hl]
  change ‖c i‖ * _ = _
  rw [Real.norm_eq_abs, abs_of_nonneg (hc i hi)]

/-- An actual compact cutoff times one translated test. -/
def periodizationPacket (g : SchwartzMap ℝ ℂ) (n : ℤ) (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.smulLeftCLM ℂ g (combSchwartzTranslation (n:ℝ) f)

@[simp] theorem periodizationPacket_apply (g : SchwartzMap ℝ ℂ) (n : ℤ)
    (f : SchwartzMap ℝ ℂ) (x : ℝ) : periodizationPacket g n f x = g x*f (x+n) := by
  simp [periodizationPacket, SchwartzMap.smulLeftCLM_apply_apply g.hasTemperateGrowth,
    combSchwartzTranslation_apply, smul_eq_mul, add_comm]

private theorem mixed_packet_pointwise (g : SchwartzMap ℝ ℂ) (n : ℤ)
    (f : SchwartzMap ℝ ℂ) (j k : ℕ) (x : ℝ) :
    mixedSchwartz j k (periodizationPacket g n f) x =
      ∑ r ∈ Finset.range (k+1), (k.choose r:ℂ)*mixedSchwartz j r g x*
        iteratedDeriv (k-r) (f : ℝ → ℂ) (x+n) := by
  have he : (periodizationPacket g n f : ℝ → ℂ) =
      (g : ℝ → ℂ)*(fun x => f (x+n)) := by ext x; exact periodizationPacket_apply g n f x
  have ht : ContDiff ℝ (k:ℕ∞) (fun y : ℝ => f (y+(n:ℝ))) := by
    exact (f.smooth k).comp (show ContDiff ℝ (k:ℕ∞) (fun y : ℝ => y+(n:ℝ)) from
      contDiff_id.add contDiff_const)
  rw [mixedSchwartz_apply, he, iteratedDeriv_mul (g.smooth k).contDiffAt ht.contDiffAt, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [iteratedDeriv_comp_add_const, mixedSchwartz_apply]
  ring


/-- Each actual cutoff packet decays inverse-quadratically in its lattice
index in the original order-q norm, with exactly two extra input orders. -/
theorem exists_periodizationPacket_norm_bound (q : ℕ) (g : SchwartzMap ℝ ℂ)
    (hg : tsupport (g : ℝ → ℂ) ⊆ Set.Icc (-1) 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℤ) (f : SchwartzMap ℝ ℂ),
      ‖schwartzToHermiteScale q (periodizationPacket g n f)‖ ≤
        C*integerCombDecay n*‖schwartzToHermiteScale (q+2) f‖ := by
  classical
  have hex : ∀ r : Fin (2*q+1), ∃ C : ℝ, 0 < C ∧
      ∀ (f : SchwartzMap ℝ ℂ) (x : ℝ), |x| ≤ 1 → ∀ n : ℤ,
        ‖iteratedDeriv r.val (f : ℝ → ℂ) (x+n)‖ ≤
          C*‖schwartzToHermiteScale (q+2) f‖*integerCombDecay n :=
    fun r => exists_compact_translate_derivative_bound q r.val (by omega)
  choose C hC using hex
  let A : ℝ := ∑ r, C r
  have hA : 0 ≤ A := Finset.sum_nonneg (fun r _ => (hC r).1.le)
  have hA' (r : Fin (2*q+1)) : C r ≤ A :=
    Finset.single_le_sum (fun t _ => (hC t).1.le) (Finset.mem_univ r)
  let K (j k : ℕ) : ℝ := ∑ r ∈ Finset.range (k+1),
    (k.choose r:ℝ)*A*‖(mixedSchwartz j r g).toLp 2 volume‖
  have hK (j k : ℕ) : 0 ≤ K j k := by dsimp [K]; positivity
  obtain ⟨B,hB,hrev⟩ := exists_hermite_norm_le_mixedL2Sum q
  let E : ℝ := ∑ z ∈ mixedIndices (2*q), K z.1 z.2
  have hE : 0 ≤ E := Finset.sum_nonneg (fun z _ => hK z.1 z.2)
  refine ⟨B*E+1, by positivity, ?_⟩
  intro n f
  let H := ‖schwartzToHermiteScale (q+2) f‖
  have hdec : 0 ≤ integerCombDecay n := by dsimp [integerCombDecay]; positivity
  have hrow (j k : ℕ) (hjk : j+k ≤ 2*q) :
      ‖(mixedSchwartz j k (periodizationPacket g n f)).toLp 2 volume‖ ≤
        K j k * integerCombDecay n * H := by
    have hp (x : ℝ) : ‖mixedSchwartz j k (periodizationPacket g n f) x‖ ≤
        ∑ r ∈ Finset.range (k+1), ((k.choose r:ℝ)*A*integerCombDecay n*H)*‖mixedSchwartz j r g x‖ := by
      rw [mixed_packet_pointwise]
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro r hr
      have hrk : r ≤ k := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hr
      simp only [norm_mul, Complex.norm_natCast]
      by_cases hz : mixedSchwartz j r g x = 0
      · simp [hz]
      · have hx := mixed_compact_support g hg j r hz
        have hx' : |x| ≤ 1 := abs_le.mpr hx
        let t : Fin (2*q+1) := ⟨k-r, by omega⟩
        have hd := (hC t).2 f x hx' n
        have ha := mul_le_mul_of_nonneg_right (hA' t) (norm_nonneg (schwartzToHermiteScale (q+2) f))
        have ha' := mul_le_mul_of_nonneg_right ha hdec
        have hder : ‖iteratedDeriv (k-r) (f : ℝ → ℂ) (x+n)‖ ≤ A*H*integerCombDecay n := hd.trans ha'
        have hm := mul_le_mul_of_nonneg_left hder
          (mul_nonneg (Nat.cast_nonneg (k.choose r)) (norm_nonneg (mixedSchwartz j r g x)))
        convert hm using 1
        ring
    have h := toLp_le_sum (Finset.range (k+1))
      (fun r => (k.choose r:ℝ)*A*integerCombDecay n*H) (fun r hr => by dsimp [H]; positivity)
      (mixedSchwartz j k (periodizationPacket g n f)) (fun r => mixedSchwartz j r g) hp
    convert h using 1
    simp only [K, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro r hr
    ring
  have hsum : mixedL2Sum (2*q) (periodizationPacket g n f) ≤ E*integerCombDecay n*H := by
    dsimp only [mixedL2Sum, E]
    rw [Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro z hz
    exact hrow z.1 z.2 ((mem_mixedIndices (2*q) z.1 z.2).mp hz)
  have h := (hrev (periodizationPacket g n f)).trans (mul_le_mul_of_nonneg_left hsum hB.le)
  have hnon : 0 ≤ integerCombDecay n*H := mul_nonneg hdec (norm_nonneg _)
  dsimp only [H] at h hnon
  nlinarith


def packetCLM (n : ℤ) : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
  (SchwartzMap.smulLeftCLM ℂ unitPartitionSchwartz).comp (combSchwartzTranslation (n:ℝ))

def packetLift (q : ℕ) (n : ℤ) :
    HermiteScale ((q+2):ℤ) →L[ℂ] HermiteScale (q:ℤ) :=
  ((schwartzToHermiteScale q).comp (packetCLM n)).toLinearMap.extendOfNorm
    (schwartzToHermiteScale (q+2)).toLinearMap

private theorem packetLift_bound (q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℤ, ‖packetLift q n‖ ≤ C*integerCombDecay n := by
  obtain ⟨C,hC,hb⟩ := exists_periodizationPacket_norm_bound q unitPartitionSchwartz unitPartitionSchwartz_tsupport
  refine ⟨C,hC,?_⟩
  intro n
  exact LinearMap.opNorm_extendOfNorm_le (schwartzToHermiteScale_denseRange (q+2))
    (by dsimp [integerCombDecay]; positivity) (hb n)

private theorem packetLift_summable (q : ℕ) : Summable (packetLift q) := by
  obtain ⟨C,hC,hb⟩ := packetLift_bound q
  exact Summable.of_norm_bounded (summable_integerCombDecay.mul_left C) hb

private theorem packetLift_on_schwartz (q : ℕ) (n : ℤ) (f : SchwartzMap ℝ ℂ) :
    packetLift q n (schwartzToHermiteScale (q+2) f) =
      schwartzToHermiteScale q (periodizationPacket unitPartitionSchwartz n f) := by
  obtain ⟨C,hC,hb⟩ := exists_periodizationPacket_norm_bound q unitPartitionSchwartz unitPartitionSchwartz_tsupport
  exact LinearMap.extendOfNorm_eq (schwartzToHermiteScale_denseRange (q+2)) ⟨C*integerCombDecay n,hb n⟩ f

/-- The full unit-period compact test operator, formed as an absolutely
convergent series in the original operator norm. -/
def unitPeriodizationPositive (q : ℕ) :
    HermiteScale ((q+2):ℤ) →L[ℂ] HermiteScale (q:ℤ) := ∑' n : ℤ, packetLift q n

/-- Exact complete Schwartz-packet series for the positive operator. -/
theorem unitPeriodizationPositive_schwartz (q : ℕ) (f : SchwartzMap ℝ ℂ) :
    unitPeriodizationPositive q (schwartzToHermiteScale (q+2) f) =
      ∑' n : ℤ, schwartzToHermiteScale q (periodizationPacket unitPartitionSchwartz n f) := by
  have h := (ContinuousLinearMap.apply ℂ (HermiteScale (q:ℤ))
    (schwartzToHermiteScale (q+2) f)).map_tsum (packetLift_summable q)
  change (∑' n : ℤ, packetLift q n) (schwartzToHermiteScale (q+2) f) = _
  exact h.trans (tsum_congr (fun n => packetLift_on_schwartz q n f))

/-- Absolute convergence of the complete original-norm test packet series. -/
theorem summable_unitPeriodization_packets (q : ℕ) (f : SchwartzMap ℝ ℂ) :
    Summable (fun n : ℤ => ‖schwartzToHermiteScale q (periodizationPacket unitPartitionSchwartz n f)‖) := by
  obtain ⟨C,hC,hb⟩ := exists_periodizationPacket_norm_bound q unitPartitionSchwartz unitPartitionSchwartz_tsupport
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _)
    (fun n => hb n f)
  exact (summable_integerCombDecay.mul_left C).mul_right _

def periodizationTransposeLM (q : ℕ) :
    HermiteScale (-(q:ℤ)) →ₗ[ℂ] HermiteScale (-((q+2):ℤ)) where
  toFun T := star ((unitPeriodizationPositive q).adjoint (star T))
  map_add' T S := by simp
  map_smul' c T := by simp

/-- The negative original-scale full unit-periodization operator. -/
def nativeUnitPeriodization (q : ℕ) :
    HermiteScale (-(q:ℤ)) →L[ℂ] HermiteScale (-((q+2):ℤ)) :=
  (periodizationTransposeLM q).mkContinuous ‖unitPeriodizationPositive q‖ fun T => by
    change ‖star ((unitPeriodizationPositive q).adjoint (star T))‖ ≤ _
    simpa only [norm_star, LinearIsometryEquiv.norm_map] using
      (unitPeriodizationPositive q).adjoint.le_opNorm (star T)

private theorem pairing_inner_periodization (q : ℕ) (T : HermiteScale (-(q:ℤ)))
    (u : HermiteScale (q:ℤ)) : hermiteScalePairing (q:ℤ) T u = inner ℂ (star T) u := by
  rw [hermiteScalePairing, lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  simp [RCLike.inner_apply, mul_comm]

/-- Whole-distribution action is the complete sum of actual compact packets;
there is no finite-period truncation or coefficient-only interpretation. -/
theorem nativeUnitPeriodization_apply (q : ℕ) (T : HermiteScale (-(q:ℤ)))
    (f : SchwartzMap ℝ ℂ) :
    hermiteScaleDistribution (q+2) (nativeUnitPeriodization q T) f =
      ∑' n : ℤ, hermiteScaleDistribution q T (periodizationPacket unitPartitionSchwartz n f) := by
  rw [hermiteScaleDistribution_apply, pairing_inner_periodization]
  change inner ℂ (star (star ((unitPeriodizationPositive q).adjoint (star T))))
    (schwartzToHermiteScale (q+2) f) = _
  rw [star_star, ContinuousLinearMap.adjoint_inner_left, unitPeriodizationPositive_schwartz]
  have h := (innerSL ℂ (star T)).map_tsum (summable_unitPeriodization_packets q f).of_norm
  apply h.trans
  apply tsum_congr
  intro n
  rw [hermiteScaleDistribution_apply, pairing_inner_periodization]
  rfl


theorem period_nonzero (P : ℝ) (hP : P ∈ Set.Icc (1/2:ℝ) 2) : P ≠ 0 := by
  linarith [hP.1]

theorem inv_period_range (P : ℝ) (hP : P ∈ Set.Icc (1/2:ℝ) 2) :
    P⁻¹ ∈ Set.Icc (1/2:ℝ) 2 := by
  have hp : 0 < P := by linarith [hP.1]
  constructor
  · rw [inv_eq_one_div]
    apply (le_div_iff₀ hp).mpr
    nlinarith [hP.2]
  · rw [inv_eq_one_div]
    apply (div_le_iff₀ hp).mpr
    nlinarith [hP.1]

/-- Complete period-P compact packet, with all operations on genuine Schwartz tests. -/
def periodizationPacketAt (P : ℝ) (hP : P ∈ Set.Icc (1/2:ℝ) 2)
    (n : ℤ) (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  combSchwartzDilation P⁻¹ (inv_ne_zero (period_nonzero P hP))
    (periodizationPacket unitPartitionSchwartz n (combSchwartzDilation P (period_nonzero P hP) f))

/-- Exact physical formula for the period-P compact packet. -/
theorem periodizationPacketAt_apply (P : ℝ) (hP : P ∈ Set.Icc (1/2:ℝ) 2)
    (n : ℤ) (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    periodizationPacketAt P hP n f x = periodizationCutoff P (period_nonzero P hP) x * f (x+n*P) := by
  simp only [periodizationPacketAt, combSchwartzDilation_apply, periodizationPacket_apply,
    unitPartitionSchwartz_apply, periodizationCutoff_apply]
  have he : P*(P⁻¹*x+(n:ℝ)) = x+n*P := by field_simp [period_nonzero P hP]
  rw [he]
  simp only [div_eq_mul_inv, mul_comm]

/-- The actual full periodization on original negative scales for every
period in the fixed compact interval. -/
def nativePeriodization (q : ℕ) (P : ℝ) (hP : P ∈ Set.Icc (1/2:ℝ) 2) :
    HermiteScale (-(q:ℤ)) →L[ℂ] HermiteScale (-((q+2):ℤ)) :=
  (nativeDilation (q+2) P hP).comp
    ((nativeUnitPeriodization q).comp (nativeDilation q P⁻¹ (inv_period_range P hP)))

/-- A single original operator bound controls all periods in [1/2,2].
No distance from a support boundary enters its definition or bound. -/
theorem exists_nativePeriodization_norm_bound (q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : ℝ) (hP : P ∈ Set.Icc (1/2:ℝ) 2),
      ‖nativePeriodization q P hP‖ ≤ C := by
  obtain ⟨A,hA,hbA⟩ := exists_nativeDilation_norm_bound q
  obtain ⟨B,hB,hbB⟩ := exists_nativeDilation_norm_bound (q+2)
  let C := ‖nativeUnitPeriodization q‖
  refine ⟨B*C*A+1, by dsimp [C]; positivity, ?_⟩
  intro P hP
  have h := ContinuousLinearMap.opNorm_comp_le (nativeDilation (q+2) P hP)
    ((nativeUnitPeriodization q).comp (nativeDilation q P⁻¹ (inv_period_range P hP)))
  have hi := ContinuousLinearMap.opNorm_comp_le (nativeUnitPeriodization q)
    (nativeDilation q P⁻¹ (inv_period_range P hP))
  have hr := (mul_le_mul (hbB P hP) (hi.trans
    (mul_le_mul_of_nonneg_left (hbA P⁻¹ (inv_period_range P hP)) (norm_nonneg _)))
      (norm_nonneg _) hB.le)
  exact h.trans (hr.trans (by dsimp only [C]; nlinarith))

/-- Whole-distribution action of full periodization, with every lattice shift
and the actual compact partition. -/
theorem nativePeriodization_apply (q : ℕ) (P : ℝ) (hP : P ∈ Set.Icc (1/2:ℝ) 2)
    (T : HermiteScale (-(q:ℤ))) (f : SchwartzMap ℝ ℂ) :
    hermiteScaleDistribution (q+2) (nativePeriodization q P hP T) f =
      ∑' n : ℤ, hermiteScaleDistribution q T (periodizationPacketAt P hP n f) := by
  change hermiteScaleDistribution (q+2)
    (nativeDilation (q+2) P hP (nativeUnitPeriodization q
      (nativeDilation q P⁻¹ (inv_period_range P hP) T))) f = _
  rw [nativeDilation_realizes, combDistributionDilation_apply, nativeUnitPeriodization_apply]
  apply tsum_congr
  intro n
  rw [nativeDilation_realizes, combDistributionDilation_apply]
  rfl


/-- Absolute convergence of the whole distributional unit-period packet sum. -/
theorem summable_nativeUnitPeriodization_actions (q : ℕ) (T : HermiteScale (-(q:ℤ)))
    (f : SchwartzMap ℝ ℂ) :
    Summable (fun n : ℤ => ‖hermiteScaleDistribution q T
      (periodizationPacket unitPartitionSchwartz n f)‖) := by
  have h := (innerSL ℂ (star T)).summable (summable_unitPeriodization_packets q f).of_norm
  have he (n : ℤ) : (innerSL ℂ (star T))
      (schwartzToHermiteScale q (periodizationPacket unitPartitionSchwartz n f)) =
        hermiteScaleDistribution q T (periodizationPacket unitPartitionSchwartz n f) := by
    rw [hermiteScaleDistribution_apply, pairing_inner_periodization]
    rfl
  simp_rw [he] at h
  exact h.norm

/-- Absolute convergence of the complete actual period-P packet action. -/
theorem summable_nativePeriodization_actions (q : ℕ) (P : ℝ)
    (hP : P ∈ Set.Icc (1/2:ℝ) 2) (T : HermiteScale (-(q:ℤ)))
    (f : SchwartzMap ℝ ℂ) :
    Summable (fun n : ℤ => ‖hermiteScaleDistribution q T (periodizationPacketAt P hP n f)‖) := by
  have h := summable_nativeUnitPeriodization_actions q
    (nativeDilation q P⁻¹ (inv_period_range P hP) T)
    (combSchwartzDilation P (period_nonzero P hP) f)
  simpa only [nativeDilation_realizes, combDistributionDilation_apply, periodizationPacketAt] using h


/-- The pointwise full packet sum is precisely the compact partition times
the full periodized test function in L01. -/
theorem periodizationPacketAt_tsum (P : ℝ) (hP : P ∈ Set.Icc (1/2:ℝ) 2)
    (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    (∑' n : ℤ, periodizationPacketAt P hP n f x) =
      periodizationCutoff P (period_nonzero P hP) x * (∑' n : ℤ, f (x+n*P)) := by
  simp_rw [periodizationPacketAt_apply]
  exact tsum_mul_left

/-- The full pointwise test-function periodization is absolutely convergent
at every real point for all periods in the compact range. -/
theorem summable_periodized_test_values (P : ℝ) (hP : P ∈ Set.Icc (1/2:ℝ) 2)
    (f : SchwartzMap ℝ ℂ) (x : ℝ) : Summable (fun n : ℤ => ‖f (x+n*P)‖) := by
  have hp : 0 < P := by linarith [hP.1]
  obtain ⟨C,hC,hb⟩ := exists_lattice_absolute_hermite_one_bound P x hp
  simpa only [mul_comm P] using (hb f).1

private theorem exists_packet_derivative_uniform_bound (g : SchwartzMap ℝ ℂ)
    (hg : tsupport (g : ℝ → ℂ) ⊆ Set.Icc (-1) 1) (k : ℕ) (f : SchwartzMap ℝ ℂ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (n : ℤ) (x : ℝ),
      ‖iteratedDeriv k (periodizationPacket g n f : ℝ → ℂ) x‖ ≤ B*integerCombDecay n := by
  obtain ⟨A,hA,hpoint⟩ := exists_weighted_derivative_point_bound (k+2) k (by omega)
  obtain ⟨C,hC,hpacket⟩ := exists_periodizationPacket_norm_bound (k+2) g hg
  refine ⟨A*C*‖schwartzToHermiteScale (k+2+2) f‖, by positivity, ?_⟩
  intro n x
  have h1 := hpoint (periodizationPacket g n f) x
  have h2 := mul_le_mul_of_nonneg_left (hpacket n f) hA.le
  have hw : 1 ≤ (1+|x|)^2 := one_le_pow₀ (by linarith [abs_nonneg x])
  have hm := mul_le_mul_of_nonneg_right hw
    (norm_nonneg (iteratedDeriv k (periodizationPacket g n f : ℝ → ℂ) x))
  nlinarith

/-- The complete unit-period compact packet sum is smooth, proved by uniform
summable bounds on every actual derivative. -/
theorem unitPeriodizedTest_contDiff (f : SchwartzMap ℝ ℂ) :
    ContDiff ℝ ∞ (fun x => ∑' n : ℤ, periodizationPacket unitPartitionSchwartz n f x) := by
  classical
  choose B hB using fun k => exists_packet_derivative_uniform_bound unitPartitionSchwartz
    unitPartitionSchwartz_tsupport k f
  apply contDiff_tsum (v := fun k n => B k * integerCombDecay n)
    (fun n => (periodizationPacket unitPartitionSchwartz n f).smooth ⊤)
  · intro k hk
    exact summable_integerCombDecay.mul_left (B k)
  · intro k n x hk
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    exact (hB k).2 n x

theorem unitPeriodizedTest_compact (f : SchwartzMap ℝ ℂ) :
    HasCompactSupport (fun x => ∑' n : ℤ, periodizationPacket unitPartitionSchwartz n f x) := by
  apply (isCompact_Icc : IsCompact (Set.Icc (-1:ℝ) 1)).of_isClosed_subset isClosed_closure
  apply closure_minimal _ isClosed_Icc
  intro x hx
  by_contra hnot
  have hg : unitPartitionSchwartz x = 0 := by
    by_contra hn
    exact hnot (unitPartitionSchwartz_tsupport (subset_closure hn))
  apply hx
  simp only [periodizationPacket_apply, hg, zero_mul, tsum_zero]

/-- The genuine compact Schwartz test used by unit-periodization. -/
def unitPeriodizedTest (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  (unitPeriodizedTest_compact f).toSchwartzMap (unitPeriodizedTest_contDiff f)

/-- Actual complete physical action of the periodized Schwartz test. -/
theorem unitPeriodizedTest_apply (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    unitPeriodizedTest f x = (unitPartition x : ℂ) * (∑' n : ℤ, f (x+n)) := by
  change (∑' n : ℤ, periodizationPacket unitPartitionSchwartz n f x) = _
  simp_rw [periodizationPacket_apply, unitPartitionSchwartz_apply]
  exact tsum_mul_left

private theorem unitPeriodizedTest_coefficients (f : SchwartzMap ℝ ℂ) (m : ℕ) :
    schwartzHermiteCoefficients (unitPeriodizedTest f) m =
      ∑' n : ℤ, schwartzHermiteCoefficients (periodizationPacket unitPartitionSchwartz n f) m := by
  let F (n : ℤ) (x : ℝ) := normalizedHermiteSchwartz m x * periodizationPacket unitPartitionSchwartz n f x
  have hi (n : ℤ) : Integrable (F n) :=
    ((normalizedHermiteSchwartz m).memLp 2 volume).integrable_mul
      ((periodizationPacket unitPartitionSchwartz n f).memLp 2 volume)
  let G (x : ℝ) := ‖normalizedHermiteSchwartz m x‖*‖unitPartitionSchwartz x‖
  have hG : Integrable G := ((normalizedHermiteSchwartz m).memLp 2 volume).norm.integrable_mul
    (unitPartitionSchwartz.memLp 2 volume).norm
  obtain ⟨A,hA,hpoint⟩ := exists_compact_translate_derivative_bound 0 0 (by omega)
  let B := A*‖schwartzToHermiteScale 2 f‖
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hp (n : ℤ) (x : ℝ) : ‖F n x‖ ≤ (B*integerCombDecay n)*G x := by
    by_cases hz : unitPartitionSchwartz x = 0
    · simp only [F, G, periodizationPacket_apply, hz, zero_mul, mul_zero, norm_zero, le_refl]
    · have hx := unitPartitionSchwartz_tsupport (subset_closure hz)
      have h := hpoint f x (abs_le.mpr hx) n
      simp only [iteratedDeriv_zero] at h
      have hm := mul_le_mul_of_nonneg_left h
        (mul_nonneg (norm_nonneg (normalizedHermiteSchwartz m x)) (norm_nonneg (unitPartitionSchwartz x)))
      simpa only [F, G, B, periodizationPacket_apply, norm_mul, mul_assoc, mul_left_comm, mul_comm] using hm
  have hm : Summable (fun n : ℤ => ∫ x : ℝ, ‖F n x‖) := by
    apply Summable.of_nonneg_of_le (fun n => integral_nonneg (fun x => norm_nonneg _))
      (fun n => (integral_mono (hi n).norm (hG.const_mul _) (hp n)).trans_eq (integral_const_mul _ _))
    exact (summable_integerCombDecay.mul_left B).mul_right (∫ x : ℝ, G x)
  have hsum := integral_tsum_of_summable_integral_norm hi hm
  rw [schwartzHermiteCoefficients_apply_integral]
  calc
    _ = ∫ x : ℝ, ∑' n : ℤ, F n x := by
      apply integral_congr_ae
      filter_upwards [] with x
      change normalizedHermiteSchwartz m x * (∑' n : ℤ, periodizationPacket unitPartitionSchwartz n f x) = _
      exact (tsum_mul_left).symm
    _ = ∑' n : ℤ, ∫ x : ℝ, F n x := hsum.symm
    _ = _ := by simp only [schwartzHermiteCoefficients_apply_integral, F]

/-- The strong original-norm packet sum is precisely the actual smooth compact
Schwartz test. Identification uses its genuine Hermite coefficient integrals. -/
theorem unitPeriodizationPositive_eq_test (q : ℕ) (f : SchwartzMap ℝ ℂ) :
    unitPeriodizationPositive q (schwartzToHermiteScale (q+2) f) =
      schwartzToHermiteScale q (unitPeriodizedTest f) := by
  rw [unitPeriodizationPositive_schwartz]
  apply lp.ext
  funext m
  have h := (lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 m).hasSum
    (summable_unitPeriodization_packets q f).of_norm.hasSum
  change HasSum (fun n : ℤ => (schwartzToHermiteScale q
    (periodizationPacket unitPartitionSchwartz n f)) m)
    ((∑' n : ℤ, schwartzToHermiteScale q (periodizationPacket unitPartitionSchwartz n f)) m) at h
  rw [← h.tsum_eq]
  simp only [schwartzToHermiteScale_apply, normalizeHermiteCoefficients]
  rw [unitPeriodizedTest_coefficients, ← tsum_mul_left]

/-- Unit-periodization tests the source against the genuine compact Schwartz
function χ(x) times the complete sum of translated tests. -/
theorem nativeUnitPeriodization_eq_test (q : ℕ) (T : HermiteScale (-(q:ℤ)))
    (f : SchwartzMap ℝ ℂ) :
    hermiteScaleDistribution (q+2) (nativeUnitPeriodization q T) f =
      hermiteScaleDistribution q T (unitPeriodizedTest f) := by
  rw [hermiteScaleDistribution_apply, hermiteScaleDistribution_apply,
    pairing_inner_periodization, pairing_inner_periodization]
  change inner ℂ (star (star ((unitPeriodizationPositive q).adjoint (star T))))
    (schwartzToHermiteScale (q+2) f) = _
  rw [star_star, ContinuousLinearMap.adjoint_inner_left, unitPeriodizationPositive_eq_test]

/-- The genuine compact Schwartz test for period P. -/
def periodizedTest (P : ℝ) (hP : P ∈ Set.Icc (1/2:ℝ) 2) (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  combSchwartzDilation P⁻¹ (inv_ne_zero (period_nonzero P hP))
    (unitPeriodizedTest (combSchwartzDilation P (period_nonzero P hP) f))

theorem periodizedTest_apply (P : ℝ) (hP : P ∈ Set.Icc (1/2:ℝ) 2)
    (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    periodizedTest P hP f x = periodizationCutoff P (period_nonzero P hP) x * (∑' n : ℤ, f (x+n*P)) := by
  simp only [periodizedTest, combSchwartzDilation_apply, unitPeriodizedTest_apply,
    periodizationCutoff_apply]
  have he (n : ℤ) : P*(P⁻¹*x+(n:ℝ)) = x+n*P := by field_simp [period_nonzero P hP]
  simp_rw [he]
  simp only [div_eq_mul_inv, mul_comm]

/-- Complete native periodization equals testing against the actual compact
Schwartz periodization specified in L01. -/
theorem nativePeriodization_eq_test (q : ℕ) (P : ℝ) (hP : P ∈ Set.Icc (1/2:ℝ) 2)
    (T : HermiteScale (-(q:ℤ))) (f : SchwartzMap ℝ ℂ) :
    hermiteScaleDistribution (q+2) (nativePeriodization q P hP T) f =
      hermiteScaleDistribution q T (periodizedTest P hP f) := by
  change hermiteScaleDistribution (q+2) (nativeDilation (q+2) P hP
    (nativeUnitPeriodization q (nativeDilation q P⁻¹ (inv_period_range P hP) T))) f = _
  rw [nativeDilation_realizes, combDistributionDilation_apply, nativeUnitPeriodization_eq_test,
    nativeDilation_realizes, combDistributionDilation_apply]
  rfl

/-- The translated partition contribution before moving the test by its period. -/
def localPartitionPacket (P : ℝ) (hP : P ∈ Set.Icc (1/2:ℝ) 2)
    (n : ℤ) (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.smulLeftCLM ℂ
    (combSchwartzTranslation (-(n:ℝ)*P) (periodizationCutoff P (period_nonzero P hP))) f

private theorem localPartitionPacket_apply (P : ℝ) (hP : P ∈ Set.Icc (1/2:ℝ) 2)
    (n : ℤ) (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    localPartitionPacket P hP n f x = periodizationCutoff P (period_nonzero P hP) (x-n*P) * f x := by
  simp only [localPartitionPacket, SchwartzMap.smulLeftCLM_apply_apply
    (combSchwartzTranslation (-(n:ℝ)*P) (periodizationCutoff P (period_nonzero P hP))).hasTemperateGrowth,
    combSchwartzTranslation_apply, smul_eq_mul]
  congr 2
  ring

private theorem localPartitionPacket_translate (P : ℝ) (hP : P ∈ Set.Icc (1/2:ℝ) 2)
    (n : ℤ) (f : SchwartzMap ℝ ℂ) :
    combSchwartzTranslation ((n:ℝ)*P) (localPartitionPacket P hP n f) = periodizationPacketAt P hP n f := by
  ext x
  rw [combSchwartzTranslation_apply, localPartitionPacket_apply, periodizationPacketAt_apply]
  congr 2 <;> ring

private theorem localPartitionPacket_support (P : ℝ) (hP : P ∈ Set.Icc (1/2:ℝ) 2)
    (n : ℤ) (f : SchwartzMap ℝ ℂ) :
    tsupport (localPartitionPacket P hP n f : ℝ → ℂ) ⊆ tsupport (f : ℝ → ℂ) := by
  apply closure_minimal _ isClosed_closure
  intro x hx
  apply subset_closure
  intro hz
  apply hx
  simp only [localPartitionPacket_apply, hz, mul_zero]

private theorem localPartitionPacket_finite (P : ℝ) (hP : P ∈ Set.Icc (1/2:ℝ) 2)
    (f : SchwartzMap ℝ ℂ) (hf : HasCompactSupport (f : ℝ → ℂ)) :
    ∃ s : Finset ℤ, ∀ n ∉ s, localPartitionPacket P hP n f = 0 := by
  obtain ⟨R,hR,hbound⟩ := hf.isCompact.isBounded.exists_pos_norm_le
  obtain ⟨N:ℕ,hN⟩ := exists_nat_gt (2*R+4)
  refine ⟨Finset.Icc (-(N:ℤ)) (N:ℤ), ?_⟩
  intro n hn
  ext x
  by_cases hz : localPartitionPacket P hP n f x = 0
  · exact hz
  · have hmul : periodizationCutoff P (period_nonzero P hP) (x-n*P) * f x ≠ 0 := by
      simpa only [localPartitionPacket_apply] using hz
    have hfx := (mul_ne_zero_iff.mp hmul).2
    have hcx := (mul_ne_zero_iff.mp hmul).1
    have hx := hbound x (subset_closure hfx)
    rw [Real.norm_eq_abs] at hx
    have hc : (x-(n:ℝ)*P)/P ∈ Set.Icc (-1:ℝ) 1 := by
      apply unitPartition_support
      intro he
      apply hcx
      rw [periodizationCutoff_apply, he, Complex.ofReal_zero]
    have hp : 0 < P := by linarith [hP.1]
    have hlo := (le_div_iff₀ hp).mp hc.1
    have hhi := (div_le_iff₀ hp).mp hc.2
    have hnp : |(n:ℝ)| *P ≤ R+2 := by
      rw [← abs_of_pos hp, ← abs_mul, abs_le]
      constructor <;> nlinarith [hP.2, (abs_le.mp hx).1, (abs_le.mp hx).2]
    have hnR : |(n:ℝ)| ≤ 2*R+4 := by nlinarith [hP.1, abs_nonneg (n:ℝ)]
    have hloN : -(N:ℤ) ≤ n := by exact_mod_cast (by linarith [(abs_le.mp hnR).1] : -(N:ℝ) ≤ n)
    have hhiN : n ≤ (N:ℤ) := by exact_mod_cast (by linarith [(abs_le.mp hnR).2] : (n:ℝ) ≤ N)
    exact False.elim (hn (Finset.mem_Icc.mpr ⟨hloN,hhiN⟩))

private theorem localPartitionPacket_sum (P : ℝ) (hP : P ∈ Set.Icc (1/2:ℝ) 2)
    (f : SchwartzMap ℝ ℂ) (s : Finset ℤ)
    (hs : ∀ n ∉ s, localPartitionPacket P hP n f = 0) :
    (∑ n ∈ s, localPartitionPacket P hP n f) = f := by
  ext x
  simp only [sum_apply]
  have heq : (∑' n : ℤ, localPartitionPacket P hP n f x) =
      ∑ n ∈ s, localPartitionPacket P hP n f x :=
    tsum_eq_sum (fun n hn => congrArg (fun g : SchwartzMap ℝ ℂ => g x) (hs n hn))
  rw [← heq]
  simp_rw [localPartitionPacket_apply]
  rw [tsum_mul_right]
  have he := (Equiv.neg ℤ).tsum_eq (fun n : ℤ => periodizationCutoff P (period_nonzero P hP) (x+n*P))
  have he' : (∑' n : ℤ, periodizationCutoff P (period_nonzero P hP) (x-n*P)) = 1 := by
    simpa only [Equiv.neg_apply, Int.cast_neg, neg_mul, ← sub_eq_add_neg,
      periodizationCutoff_sum] using he
  rw [he', one_mul]

/-- Local P-periodicity expressed on genuine compact Schwartz tests inside O.
For a P-periodic open set this is the usual equality of all integral translates
on that open set; there is no native representation premise. -/
def DistributionPeriodicOn (P : ℝ) (O : Set ℝ) (T : TemperedDistribution ℝ ℂ) : Prop :=
  ∀ (n : ℤ) (f : SchwartzMap ℝ ℂ), HasCompactSupport (f : ℝ → ℂ) →
    tsupport (f : ℝ → ℂ) ⊆ O → T (combSchwartzTranslation ((n:ℝ)*P) f) = T f

/-- Periodization agrees with the source on every compact Schwartz test in a
region where the source is locally P-periodic. The construction and norm bound
use no distance to the region's boundary. -/
theorem nativePeriodization_agrees_on (q : ℕ) (P : ℝ) (hP : P ∈ Set.Icc (1/2:ℝ) 2)
    (T : HermiteScale (-(q:ℤ))) (O : Set ℝ)
    (hlocal : DistributionPeriodicOn P O (hermiteScaleDistribution q T))
    (f : SchwartzMap ℝ ℂ) (hf : HasCompactSupport (f : ℝ → ℂ))
    (hO : tsupport (f : ℝ → ℂ) ⊆ O) :
    hermiteScaleDistribution (q+2) (nativePeriodization q P hP T) f = hermiteScaleDistribution q T f := by
  obtain ⟨s,hs⟩ := localPartitionPacket_finite P hP f hf
  rw [nativePeriodization_apply]
  have he (n : ℤ) : hermiteScaleDistribution q T (periodizationPacketAt P hP n f) =
      hermiteScaleDistribution q T (localPartitionPacket P hP n f) := by
    rw [← localPartitionPacket_translate]
    apply hlocal n _
    · exact hf.isCompact.of_isClosed_subset isClosed_closure (localPartitionPacket_support P hP n f)
    · exact (localPartitionPacket_support P hP n f).trans hO
  simp_rw [he]
  rw [tsum_eq_sum (fun n hn => by rw [hs n hn, map_zero]), ← map_sum,
    localPartitionPacket_sum P hP f s hs]

private theorem translation_test_compact (a : ℝ) (f : SchwartzMap ℝ ℂ)
    (hf : HasCompactSupport (f : ℝ → ℂ)) :
    HasCompactSupport (combSchwartzTranslation a f : ℝ → ℂ) := by
  exact hf.comp_homeomorph (Homeomorph.addLeft a)

private theorem translation_test_support (P : ℝ) (O : Set ℝ)
    (hO : Function.Periodic (fun x => x ∈ O) P) (n : ℤ) (f : SchwartzMap ℝ ℂ)
    (hf : tsupport (f : ℝ → ℂ) ⊆ O) :
    tsupport (combSchwartzTranslation ((n:ℝ)*P) f : ℝ → ℂ) ⊆ O := by
  have he : (combSchwartzTranslation ((n:ℝ)*P) f : ℝ → ℂ) =
      (f : ℝ → ℂ) ∘ Homeomorph.addLeft ((n:ℝ)*P) := rfl
  rw [he, tsupport_comp_eq_preimage]
  intro x hx
  have h := hf hx
  change (n:ℝ)*P+x ∈ O at h
  have hp := (hO.int_mul n) x
  rw [add_comm] at h
  exact hp ▸ h

private theorem translation_test_add (a b : ℝ) (f : SchwartzMap ℝ ℂ) :
    combSchwartzTranslation a (combSchwartzTranslation b f) = combSchwartzTranslation (a+b) f := by
  ext x
  simp only [combSchwartzTranslation_apply]
  congr 1
  ring

/-- On a periodic region, the one-step local translation equation implies
all integer-step equations used by the agreement theorem. -/
theorem distributionPeriodicOn_of_translation_eq (P : ℝ) (O : Set ℝ)
    (hO : Function.Periodic (fun x => x ∈ O) P) (T : TemperedDistribution ℝ ℂ)
    (hstep : ∀ f : SchwartzMap ℝ ℂ, HasCompactSupport (f : ℝ → ℂ) →
      tsupport (f : ℝ → ℂ) ⊆ O → T (combSchwartzTranslation P f) = T f) :
    DistributionPeriodicOn P O T := by
  intro n f hf hs
  induction n using Int.induction_on with
  | zero =>
      have he : combSchwartzTranslation (((0:ℤ):ℝ)*P) f = f := by
        ext x; simp only [Int.cast_zero, zero_mul, combSchwartzTranslation_apply, zero_add]
      exact congrArg T he
  | succ n ih =>
      have h := hstep (combSchwartzTranslation ((n:ℝ)*P) f)
        (translation_test_compact _ f hf) (translation_test_support P O hO n f hs)
      rw [translation_test_add] at h
      have he : P+(n:ℝ)*P = (((n:ℤ)+1:ℤ):ℝ)*P := by push_cast; ring
      rw [he] at h
      exact h.trans ih
  | pred n ih =>
      have h := hstep (combSchwartzTranslation (((-(n:ℤ)-1:ℤ):ℝ)*P) f)
        (translation_test_compact _ f hf) (translation_test_support P O hO (-(n:ℤ)-1) f hs)
      rw [translation_test_add] at h
      have he : P+(((-(n:ℤ)-1:ℤ):ℝ)*P) = ((-(n:ℤ):ℤ):ℝ)*P := by push_cast; ring
      rw [he] at h
      exact h.symm.trans ih

/-- In particular, the local one-step period equation on a P-periodic open
set is sufficient for exact agreement there. -/
theorem nativePeriodization_agrees_of_translation_eq (q : ℕ) (P : ℝ)
    (hP : P ∈ Set.Icc (1/2:ℝ) 2) (T : HermiteScale (-(q:ℤ)))
    (O : Set ℝ) (_hopen : IsOpen O) (hO : Function.Periodic (fun x => x ∈ O) P)
    (hstep : ∀ f : SchwartzMap ℝ ℂ, HasCompactSupport (f : ℝ → ℂ) →
      tsupport (f : ℝ → ℂ) ⊆ O →
        hermiteScaleDistribution q T (combSchwartzTranslation P f) = hermiteScaleDistribution q T f)
    (f : SchwartzMap ℝ ℂ) (hf : HasCompactSupport (f : ℝ → ℂ))
    (hs : tsupport (f : ℝ → ℂ) ⊆ O) :
    hermiteScaleDistribution (q+2) (nativePeriodization q P hP T) f = hermiteScaleDistribution q T f :=
  nativePeriodization_agrees_on q P hP T O
    (distributionPeriodicOn_of_translation_eq P O hO _ hstep) f hf hs

/-- The output of the constructed full operator is genuinely P-periodic as
a whole tempered distribution. -/
theorem nativePeriodization_periodic (q : ℕ) (P : ℝ) (hP : P ∈ Set.Icc (1/2:ℝ) 2)
    (T : HermiteScale (-(q:ℤ))) :
    combDistributionTranslation P (hermiteScaleDistribution (q+2) (nativePeriodization q P hP T)) =
      hermiteScaleDistribution (q+2) (nativePeriodization q P hP T) := by
  ext f
  rw [combDistributionTranslation_apply, nativePeriodization_eq_test, nativePeriodization_eq_test]
  congr 1
  ext x
  rw [periodizedTest_apply, periodizedTest_apply]
  congr 1
  have h := (Equiv.addRight (1:ℤ)).tsum_eq (fun n : ℤ => f (x+n*P))
  convert h using 1
  apply tsum_congr
  intro n
  rw [combSchwartzTranslation_apply]
  congr 1
  simp only [Equiv.coe_addRight, Int.cast_add, Int.cast_one]
  ring


/-- The actual periodized test has compact support uniformly contained in [-2,2]
throughout the full period interval. -/
theorem periodizedTest_tsupport (P : ℝ) (hP : P ∈ Set.Icc (1/2:ℝ) 2)
    (f : SchwartzMap ℝ ℂ) : tsupport (periodizedTest P hP f : ℝ → ℂ) ⊆ Set.Icc (-2) 2 := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  have hc : periodizationCutoff P (period_nonzero P hP) x ≠ 0 := by
    intro he
    apply hx
    rw [periodizedTest_apply, he, zero_mul]
  have hu : x/P ∈ Set.Icc (-1:ℝ) 1 := by
    apply unitPartition_support
    intro he
    apply hc
    rw [periodizationCutoff_apply, he, Complex.ofReal_zero]
  have hp : 0 < P := by linarith [hP.1]
  have hlo := (le_div_iff₀ hp).mp hu.1
  have hhi := (div_le_iff₀ hp).mp hu.2
  constructor <;> nlinarith [hP.2]

/-- Uniform original positive-norm bound for the genuine compact periodized
Schwartz test, with the same two-order loss as the negative operator. -/
theorem exists_periodizedTest_norm_bound (q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : ℝ) (hP : P ∈ Set.Icc (1/2:ℝ) 2)
      (f : SchwartzMap ℝ ℂ),
      ‖schwartzToHermiteScale q (periodizedTest P hP f)‖ ≤
        C*‖schwartzToHermiteScale (q+2) f‖ := by
  obtain ⟨A,hA,hbA⟩ := exists_uniform_hermite_dilation_bound q
  obtain ⟨B,hB,hbB⟩ := exists_uniform_hermite_dilation_bound (q+2)
  let D := ‖unitPeriodizationPositive q‖
  refine ⟨A*D*B+1, by dsimp [D]; positivity, ?_⟩
  intro P hP f
  have h1 := hbA P⁻¹ (inv_ne_zero (period_nonzero P hP)) (inv_period_range P hP)
    (unitPeriodizedTest (combSchwartzDilation P (period_nonzero P hP) f))
  rw [← unitPeriodizationPositive_eq_test] at h1
  have h2 := (unitPeriodizationPositive q).le_opNorm
    (schwartzToHermiteScale (q+2) (combSchwartzDilation P (period_nonzero P hP) f))
  have h3 := hbB P (period_nonzero P hP) hP f
  have h23 := h2.trans (mul_le_mul_of_nonneg_left h3 (norm_nonneg _))
  have h := h1.trans (mul_le_mul_of_nonneg_left h23 hA.le)
  change ‖schwartzToHermiteScale q (periodizedTest P hP f)‖ ≤ _ at h
  dsimp only [D]
  nlinarith [norm_nonneg (schwartzToHermiteScale (q+2) f)]

end
end MeyerGeneralProblem.Adaptive
