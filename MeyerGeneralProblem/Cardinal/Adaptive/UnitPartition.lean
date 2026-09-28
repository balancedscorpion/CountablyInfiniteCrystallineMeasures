module

public import MeyerGeneralProblem.Cardinal.Adaptive.PeriodicAnnihilators
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import all Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Fourier.PoissonSummation
import all Mathlib.Analysis.Fourier.PoissonSummation

@[expose] public section

/-!
# A fixed smooth compact unit-period partition

Normalize the compact bump by its locally finite integer periodization.
The denominator is everywhere at least one. This gives an actual partition
whose translates sum to one, and allows periodic smooth functions to be
represented by the periodization of one compact Schwartz function.
-/

namespace MeyerGeneralProblem.Adaptive
noncomputable section
open Set Function
open scoped Topology ContDiff

/-- Fixed radii leave no uncovered point modulo the integers. -/
def unitPartitionBump : ContDiffBump (0:ℝ) where
  rIn := 1/2
  rOut := 1
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

private theorem unitPartitionBump_support :
    support unitPartitionBump ⊆ Icc (-1) 1 := by
  intro x hx
  rw [unitPartitionBump.support_eq] at hx
  have h : |x| < 1 := by simpa [Metric.mem_ball,Real.dist_eq,unitPartitionBump] using hx
  exact ⟨(abs_lt.mp h).1.le,(abs_lt.mp h).2.le⟩

/-- The full periodized denominator has a unit summand at every point. -/
theorem unitPartition_denominator_ge_one (x:ℝ) :
    1 ≤ unitPeriodization unitPartitionBump x := by
  let n : ℤ := -⌊x+1/2⌋
  have hpoint : x+(n:ℝ) ∈ Metric.closedBall 0 unitPartitionBump.rIn := by
    rw [Metric.mem_closedBall,Real.dist_eq]
    change |x+(n:ℝ)-0| ≤ 1/2
    rw [abs_le]
    have hlo := Int.floor_le (x+1/2)
    have hhi := Int.lt_floor_add_one (x+1/2)
    dsimp [n]
    push_cast
    constructor <;> linarith
  have hone := unitPartitionBump.one_of_mem_closedBall hpoint
  have hle := (summable_unitPeriodization unitPartitionBump unitPartitionBump_support x).le_tsum n
    (fun _ _ => unitPartitionBump.nonneg)
  simpa only [unitPeriodization,hone] using hle

/-- Actual compactly supported smooth partition function. -/
def unitPartition (x:ℝ) : ℝ :=
  unitPartitionBump x / unitPeriodization unitPartitionBump x

theorem unitPartition_contDiff : ContDiff ℝ ∞ unitPartition :=
  unitPartitionBump.contDiff.div
    (unitPeriodization_contDiff unitPartitionBump unitPartitionBump.contDiff unitPartitionBump_support)
    (fun x => (lt_of_lt_of_le zero_lt_one (unitPartition_denominator_ge_one x)).ne')

theorem unitPartition_nonneg (x:ℝ) : 0 ≤ unitPartition x :=
  div_nonneg unitPartitionBump.nonneg (zero_le_one.trans (unitPartition_denominator_ge_one x))

theorem unitPartition_support : support unitPartition ⊆ Icc (-1) 1 := by
  intro x hx
  apply unitPartitionBump_support
  change unitPartitionBump x ≠ 0
  intro h
  apply hx
  simp [unitPartition,h]

theorem unitPartition_hasCompactSupport : HasCompactSupport unitPartition :=
  isCompact_Icc.of_isClosed_subset isClosed_closure
    (closure_minimal unitPartition_support isClosed_Icc)

/-- The complete integer sum equals one, including all positive and negative shifts. -/
theorem unitPartition_sum (x:ℝ) : ∑' n:ℤ, unitPartition (x+n) = 1 := by
  have hp := unitPeriodization_periodic unitPartitionBump
  have hshift (n:ℤ) : unitPeriodization unitPartitionBump (x+n) =
      unitPeriodization unitPartitionBump x := by
    simpa only [mul_one] using hp.int_mul n x
  simp_rw [unitPartition,hshift]
  rw [tsum_div_const]
  exact div_self (lt_of_lt_of_le zero_lt_one (unitPartition_denominator_ge_one x)).ne'

theorem representative_hasCompactSupport (g : ℝ → ℂ) :
    HasCompactSupport (fun x => g x * (unitPartition x : ℂ)) := by
  have hs : support (fun x => g x * (unitPartition x : ℂ)) ⊆ Icc (-1) 1 := by
    intro x hx
    apply unitPartition_support
    intro h
    apply hx
    simp [h]
  exact isCompact_Icc.of_isClosed_subset isClosed_closure (closure_minimal hs isClosed_Icc)

/-- A genuine Schwartz representative of every smooth periodic function. -/
def periodicSchwartzRepresentative (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) :
    SchwartzMap ℝ ℂ :=
  (representative_hasCompactSupport g).toSchwartzMap
    (hg.mul (Complex.ofRealCLM.contDiff.comp unitPartition_contDiff))

@[simp] theorem periodicSchwartzRepresentative_apply (g : ℝ → ℂ)
    (hg : ContDiff ℝ ∞ g) (x : ℝ) :
    periodicSchwartzRepresentative g hg x = g x * (unitPartition x : ℂ) := rfl

/-- The complete integer periodization recovers the entire periodic function. -/
theorem periodicSchwartzRepresentative_sum (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
    (hp : Periodic g 1) (x : ℝ) :
    ∑' n:ℤ, periodicSchwartzRepresentative g hg (x+n) = g x := by
  have hshift (n:ℤ) : g (x+n) = g x := by simpa only [mul_one] using hp.int_mul n x
  simp_rw [periodicSchwartzRepresentative_apply,hshift]
  rw [tsum_mul_left,← Complex.ofReal_tsum,unitPartition_sum,Complex.ofReal_one,mul_one]

/-- Poisson summation gives the full Fourier expansion from an actual
Schwartz transform; neither integer arm nor any phase coefficient is omitted. -/
theorem periodicSchwartzRepresentative_fourier (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
    (hp : Periodic g 1) (x : ℝ) :
    g x = ∑' n:ℤ, FourierTransform.fourier (periodicSchwartzRepresentative g hg) n *
      fourier n (x : UnitAddCircle) := by
  rw [← periodicSchwartzRepresentative_sum g hg hp x]
  exact SchwartzMap.tsum_eq_tsum_fourier _ x

end
end MeyerGeneralProblem.Adaptive
