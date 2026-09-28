module

public import MeyerGeneralProblem.Atomic.PointMass
public import MeyerGeneralProblem.Carrier.LocallyFinite

@[expose] public section

/-!
# Schwartz tests isolating nodes of an extensional carrier

Local finiteness supplies a positive isolation radius at each physical node.
A smooth compactly supported bump inside that radius gives a complex Schwartz
test equal to one at the selected node and zero at every other carrier node.
-/

namespace MeyerGeneralProblem

noncomputable section

open scoped ContDiff

namespace LocallyFiniteCarrier

variable (S : LocallyFiniteCarrier)

/-- A chosen positive radius whose open ball meets the carrier only at `x`. -/
def isolationRadius (x : S.subtype) : ℝ :=
  Classical.choose (S.exists_isolationRadius x.property)

theorem isolationRadius_pos (x : S.subtype) : 0 < S.isolationRadius x :=
  (Classical.choose_spec (S.exists_isolationRadius x.property)).1

@[simp]
theorem ball_isolationRadius_inter (x : S.subtype) :
    Metric.ball (x : ℝ) (S.isolationRadius x) ∩ S.carrier = {(x : ℝ)} :=
  (Classical.choose_spec (S.exists_isolationRadius x.property)).2

/-- Every other carrier node is at least the chosen isolation radius away. -/
theorem isolationRadius_le_dist (x : S.subtype) {y : ℝ}
    (hy : y ∈ S.carrier) (hyx : y ≠ (x : ℝ)) :
    S.isolationRadius x ≤ dist y x := by
  by_contra hnot
  have hydist : dist y (x : ℝ) < S.isolationRadius x := lt_of_not_ge hnot
  have hyball : y ∈ Metric.ball (x : ℝ) (S.isolationRadius x) := by
    simpa [dist_comm] using hydist
  have hyinter : y ∈ Metric.ball (x : ℝ) (S.isolationRadius x) ∩ S.carrier :=
    ⟨hyball, hy⟩
  have : y = (x : ℝ) := by
    simpa [S.ball_isolationRadius_inter x] using hyinter
  exact hyx this

/-- A smooth bump supported strictly inside the isolation ball at `x`. -/
def isolationBump (x : S.subtype) : ContDiffBump (x : ℝ) where
  rIn := S.isolationRadius x / 4
  rOut := S.isolationRadius x / 2
  rIn_pos := div_pos (S.isolationRadius_pos x) (by norm_num)
  rIn_lt_rOut := by
    have h := S.isolationRadius_pos x
    linarith

/-- A complex Schwartz test isolating the selected physical carrier node. -/
def isolationSchwartz (x : S.subtype) : SchwartzMap ℝ ℂ := by
  let b := S.isolationBump x
  let f : ℝ → ℂ := Complex.ofRealCLM ∘ b
  have hfSupport : HasCompactSupport f :=
    b.hasCompactSupport.comp_left rfl
  have hfSmooth : ContDiff ℝ ∞ f :=
    Complex.ofRealCLM.contDiff.comp b.contDiff
  exact hfSupport.toSchwartzMap hfSmooth

@[simp]
theorem isolationSchwartz_self (x : S.subtype) :
    S.isolationSchwartz x x = 1 := by
  simp only [isolationSchwartz]
  change ((S.isolationBump x (x : ℝ) : ℝ) : ℂ) = 1
  rw [(S.isolationBump x).one_of_mem_closedBall]
  · norm_num
  · simpa using (S.isolationBump x).rIn_pos.le

@[simp]
theorem isolationSchwartz_of_mem_of_ne (x : S.subtype) {y : ℝ}
    (hy : y ∈ S.carrier) (hyx : y ≠ (x : ℝ)) :
    S.isolationSchwartz x y = 0 := by
  simp only [isolationSchwartz]
  change ((S.isolationBump x y : ℝ) : ℂ) = 0
  rw [(S.isolationBump x).zero_of_le_dist]
  · norm_num
  · change S.isolationRadius x / 2 ≤ dist y (x : ℝ)
    exact (div_le_self (S.isolationRadius_pos x).le (by norm_num)).trans
      (S.isolationRadius_le_dist x hy hyx)

@[simp]
theorem isolationSchwartz_apply_subtype (x y : S.subtype) :
    S.isolationSchwartz x y = if y = x then 1 else 0 := by
  by_cases hyx : y = x
  · subst y
    simp
  · simp only [hyx, ↓reduceIte]
    exact S.isolationSchwartz_of_mem_of_ne x y.property (by
      exact fun h ↦ hyx (Subtype.ext h))

end LocallyFiniteCarrier

end

end MeyerGeneralProblem
