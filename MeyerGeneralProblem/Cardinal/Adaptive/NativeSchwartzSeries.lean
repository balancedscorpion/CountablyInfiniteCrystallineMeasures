module

public import MeyerGeneralProblem.Cardinal.Adaptive.HalfNewtonFourier
public import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import all Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum

@[expose] public section

/-! # Strong native identification of pointwise Schwartz series -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open MeasureTheory

/-- A pointwise Schwartz sum with absolutely summable actual L2 norms is its
strong L2 sum. This identifies the given function, not an abstract limit. -/
theorem hasSum_schwartz_toLp_of_pointwise {ι : Type*} [Countable ι]
    (v : ι → SchwartzMap ℝ ℂ) (u : SchwartzMap ℝ ℂ)
    (hn : Summable (fun i => ‖(v i).toLp 2 volume‖))
    (hu : ∀ x, u x=∑' i, v i x) :
    HasSum (fun i => (v i).toLp 2 volume) (u.toLp 2 volume) := by
  have ht := Lp.coeFn_tsum (tsum_enorm_ne_top_iff_summable_norm.mpr hn)
  have ha : ∀ᵐ x ∂(volume : Measure ℝ), ∀ i : ι, (v i).toLp 2 volume x=v i x := by
    rw [ae_all_iff]
    intro i
    exact (v i).coeFn_toLp 2 volume
  have he : u.toLp 2 volume=∑' i, (v i).toLp 2 volume := by
    apply Lp.ext
    filter_upwards [u.coeFn_toLp 2 volume,ht,ha] with x hx htx hax
    rw [hx,htx,hu]
    simp only [hax]
  rw [he]
  exact hn.of_norm.hasSum

/-- Absolute summability in the genuine positive native norm and a pointwise
Schwartz identity determine the strong sum in that same original order. -/
theorem hasSum_native_schwartz_of_pointwise {ι : Type*} [Countable ι] (p : ℕ)
    (v : ι → SchwartzMap ℝ ℂ) (u : SchwartzMap ℝ ℂ)
    (hn : Summable (fun i => ‖schwartzToHermiteScale p (v i)‖))
    (hu : ∀ x, u x=∑' i, v i x) :
    HasSum (fun i => schwartzToHermiteScale p (v i)) (schwartzToHermiteScale p u) := by
  have hLp : Summable (fun i => ‖(v i).toLp 2 volume‖) := by
    apply Summable.of_nonneg_of_le (fun i => norm_nonneg _) _ hn
    intro i
    rw [← norm_schwartzToHermiteScale_zero]
    have hm (q : ℕ) : ‖schwartzToHermiteScale 0 (v i)‖ ≤ ‖schwartzToHermiteScale q (v i)‖ := by
      induction q with
      | zero => exact le_rfl
      | succ q ih => exact ih.trans (schwartzToHermiteScale_norm_mono q (v i))
    exact hm p
  have hc := (TauCeti.twoPiHermiteHilbertBasis ℂ).repr.toContinuousLinearEquiv.toContinuousLinearMap.hasSum
    (hasSum_schwartz_toLp_of_pointwise v u hLp hu)
  have hs := hn.of_norm
  apply hs.hasSum_iff.mpr
  apply lp.ext
  funext n
  have hraw := (lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 n).hasSum hc
  change HasSum (fun i => schwartzHermiteCoefficients (v i) n) (schwartzHermiteCoefficients u n) at hraw
  have hweighted := hraw.mul_left (hermiteScaleWeight (p : ℤ) n : ℂ)
  have hnative := (lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 n).hasSum hs.hasSum
  change HasSum (fun i => schwartzToHermiteScale p (v i) n)
    ((∑' i, schwartzToHermiteScale p (v i)) n) at hnative
  have hw : HasSum (fun i => schwartzToHermiteScale p (v i) n)
      (schwartzToHermiteScale p u n) := by
    simpa only [schwartzToHermiteScale_apply,normalizeHermiteCoefficients] using hweighted
  exact hnative.unique hw

/-- Every actual native source may be paired with the whole identified series;
no distribution-specific pointwise interchange is assumed. -/
theorem hasSum_native_pairing_of_pointwise {ι : Type*} [Countable ι] (p : ℕ)
    (v : ι → SchwartzMap ℝ ℂ) (u : SchwartzMap ℝ ℂ)
    (hn : Summable (fun i => ‖schwartzToHermiteScale p (v i)‖))
    (hu : ∀ x, u x=∑' i, v i x) (T : HermiteScale (-(p : ℤ))) :
    HasSum (fun i => hermiteScaleDistribution p T (v i)) (hermiteScaleDistribution p T u) := by
  have h := (hermiteScalePairingLeftCLM p T).hasSum (hasSum_native_schwartz_of_pointwise p v u hn hu)
  simpa only [hermiteScalePairingLeftCLM_apply,← hermiteScaleDistribution_apply] using h

end
end MeyerGeneralProblem.Adaptive
