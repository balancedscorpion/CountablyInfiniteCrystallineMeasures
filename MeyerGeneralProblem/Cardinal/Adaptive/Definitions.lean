module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import all Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.PNat.Basic
import all Mathlib.Data.PNat.Basic

@[expose] public section

/-!
# Concrete sets in the adaptive reciprocal construction

These are the actual atom and phase formulas of `HIGH_ORDER_GAP_SURGERY.md`
§§2–3 and `ADAPTIVE_EXHAUSTION_CANDIDATE.md` §1. The periodic phase closure
is deliberately distinct from the locally finite atom set. No source-space
or good-scale existence assertion is built into these definitions.
-/

namespace MeyerGeneralProblem.Adaptive

noncomputable section

/-- The two reciprocal directions of one positive-index block. -/
inductive ReciprocalSign where
  | forward
  | reciprocal
  deriving DecidableEq

instance : Fintype ReciprocalSign :=
  ⟨{.forward, .reciprocal}, by intro σ; cases σ <;> simp⟩

/-- Swap the two reciprocal directions. -/
def ReciprocalSign.flip : ReciprocalSign → ReciprocalSign
  | .forward => .reciprocal
  | .reciprocal => .forward

@[simp] theorem ReciprocalSign.flip_flip (σ : ReciprocalSign) : σ.flip.flip = σ := by
  cases σ <;> rfl

/-- Positive block index together with a reciprocal direction. -/
abbrev Label := ℕ+ × ReciprocalSign

/-- Number of matched positive head phases for a central gap parameter. -/
def headLength (R : ℕ) : ℕ := 2 * R - 1

/-- Rapid-tail base, controlled by the desired excluded native order. -/
def rapidBase (P : ℕ) : ℝ := 1 + 1 / (6 * (P : ℝ))

/-- Large parameter controlling the rapid tail after the finite head. -/
def rapidScale (R : ℕ) : ℝ := 2 ^ (64 : ℕ) * (headLength R : ℝ)

/-- Exponential decay constant of the actual tail phases. -/
def rapidDecay (P R : ℕ) : ℝ := 6 * (P : ℝ) * Real.log (rapidScale R)

/-- Distance of the `i`th tail phase from the half-integer seam. -/
def rapidDistance (P R i : ℕ) : ℝ :=
  (1 / 16) * Real.exp (-(rapidDecay P R) * rapidBase P ^ i)

/-- The positive head phases followed by the original rapid tail. -/
def blockPhase (P R : ℕ) (j : ℕ+) : ℝ :=
  if (j : ℕ) ≤ headLength R then
    (2 * (j : ℝ) - 1) / (4 * (headLength R : ℝ))
  else
    1 / 2 - rapidDistance P R ((j : ℕ) - headLength R)

/-- The two signed copies of a positive phase; `true` is the positive copy. -/
def signedPhase (positive : Bool) (β : ℝ) : ℝ := if positive then β else -β

/-- Head orbits use the exchanged flat window; the infinite tail keeps its
original cell threshold. Cell zero is excluded for positive gap parameters. -/
def cellThreshold (R : ℕ) (j : ℕ+) : ℕ :=
  if (j : ℕ) ≤ headLength R then R else (j : ℕ)

/-- The actual high-order block set, with both signed phases and all allowed
integer cells. In particular, no half-integer seam has been added. -/
def blockSet (P R : ℕ) : Set ℝ :=
  {x | ∃ (j : ℕ+) (positive : Bool) (n : ℤ),
    cellThreshold R j ≤ n.natAbs ∧
      x = (n : ℝ) + signedPhase positive (blockPhase P R j)}

/-- Signed isolated phases before taking their periodic closure. -/
def phaseSet (P R : ℕ) : Set ℝ :=
  {β | ∃ (j : ℕ+) (positive : Bool), β = signedPhase positive (blockPhase P R j)}

/-- Full periodic phase set, including the half-integer seam. The geometric
closedness theorem is separate from this explicit set formula. -/
def periodicPhaseSet (P R : ℕ) : Set ℝ :=
  {x | ∃ (n : ℤ) (β : ℝ), (β ∈ phaseSet P R ∨ β = 1 / 2) ∧ x = (n : ℝ) + β}

/-- Actual scale associated with a reciprocal label. -/
def labelScale (s : ℕ+ → ℝ) (b : Label) : ℝ :=
  match b.2 with
  | .forward => s b.1
  | .reciprocal => (s b.1)⁻¹

/-- Spectral sector `t_b A_i`, retaining the concrete block formula. -/
def sectorSet (R : ℕ+ → ℕ) (s : ℕ+ → ℝ) (b : Label) : Set ℝ :=
  (fun x => labelScale s b * x) '' blockSet b.1 (R b.1)

/-- Physical sector paired with that spectral restriction: `A_i / t_b`. -/
def physicalSectorSet (R : ℕ+ → ℕ) (s : ℕ+ → ℝ) (b : Label) : Set ℝ :=
  (fun x => (labelScale s b)⁻¹ * x) '' blockSet b.1 (R b.1)

/-- Full periodic physical set associated with a spectral label. -/
def physicalPeriodicSet (R : ℕ+ → ℕ) (s : ℕ+ → ℝ) (b : Label) : Set ℝ :=
  (fun x => (labelScale s b)⁻¹ * x) '' periodicPhaseSet b.1 (R b.1)

/-- Complete actual carrier formula, before proving local finiteness. -/
def carrierSet (R : ℕ+ → ℕ) (s : ℕ+ → ℝ) : Set ℝ := ⋃ b, sectorSet R s b

@[simp] theorem labelScale_forward (s : ℕ+ → ℝ) (i : ℕ+) :
    labelScale s (i, .forward) = s i := rfl

@[simp] theorem labelScale_reciprocal (s : ℕ+ → ℝ) (i : ℕ+) :
    labelScale s (i, .reciprocal) = (s i)⁻¹ := rfl

/-- The reciprocal orientation is exact even before a good scale is chosen. -/
theorem labelScale_flip (s : ℕ+ → ℝ) (b : Label) :
    labelScale s (b.1, b.2.flip) = (labelScale s b)⁻¹ := by
  rcases b with ⟨i, σ⟩
  cases σ <;> simp [labelScale, ReciprocalSign.flip]

/-- Physical recovery lands in the opposite actual reciprocal sector. -/
theorem physicalSectorSet_eq_flipped (R : ℕ+ → ℕ) (s : ℕ+ → ℝ) (b : Label) :
    physicalSectorSet R s b = sectorSet R s (b.1, b.2.flip) := by
  simp only [physicalSectorSet, sectorSet, labelScale_flip]

/-- The actual block is contained in its periodic set; equality is not asserted. -/
theorem blockSet_subset_periodicPhaseSet (P R : ℕ) :
    blockSet P R ⊆ periodicPhaseSet P R := by
  rintro x ⟨j, positive, n, _, rfl⟩
  exact ⟨n, signedPhase positive (blockPhase P R j), Or.inl ⟨j, positive, rfl⟩, rfl⟩

/-- Every recovered physical sector lies in the complete actual carrier. -/
theorem physicalSectorSet_subset_carrierSet (R : ℕ+ → ℕ) (s : ℕ+ → ℝ) (b : Label) :
    physicalSectorSet R s b ⊆ carrierSet R s := by
  rw [physicalSectorSet_eq_flipped]
  exact Set.subset_iUnion (sectorSet R s) (b.1, b.2.flip)

end

end MeyerGeneralProblem.Adaptive
