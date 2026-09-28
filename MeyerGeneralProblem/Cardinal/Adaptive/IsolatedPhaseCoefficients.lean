module

public import MeyerGeneralProblem.Cardinal.Adaptive.ActualSourceSplitting
public import MeyerGeneralProblem.Cardinal.Adaptive.AnnihilatorFourierSeries
public import Mathlib.Order.Filter.AtTopBot.Interval
import all Mathlib.Order.Filter.AtTopBot.Interval

@[expose] public section

/-! Fixed isolated phase orbit coefficients of actual native spectral restrictions. -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open MeasureTheory Set Filter Classical
open scoped Topology ContDiff FourierTransform

/-- Subtracting an integer preserves the complete periodic phase set. -/
theorem periodicPhaseSet_sub_int (P R : ℕ) (n : ℤ) {x : ℝ}
    (hx : x ∈ periodicPhaseSet P R) : x-(n:ℝ) ∈ periodicPhaseSet P R := by
  rcases hx with ⟨m,β,hβ,rfl⟩
  refine ⟨m-n,β,hβ,?_⟩
  push_cast
  ring

/-- Every actual signed phase stays strictly between the neighboring seams. -/
theorem phaseSet_abs_lt_half {P R : ℕ} (hP : 1 ≤ P) (hR : 1 ≤ R)
    {β : ℝ} (hβ : β ∈ phaseSet P R) : |β| < 1/2 := by
  rcases hβ with ⟨j,positive,rfl⟩
  exact abs_signedPhase_lt_half hP hR j positive

/-- A fixed isolated phase admits one positive isolation radius for every integer translate. -/
theorem exists_phase_orbit_isolation {P R : ℕ} (hP : 1 ≤ P) (hR : 1 ≤ R)
    {β : ℝ} (hβ : β ∈ phaseSet P R) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ n : ℤ, ∀ y ∈ periodicPhaseSet P R,
      y ≠ (n:ℝ)+β → ε ≤ |y-((n:ℝ)+β)| := by
  have hmem : β ∈ periodicPhaseSet P R := ⟨0,β,Or.inl hβ,by simp⟩
  have hseam : ∀ n : ℤ, β ≠ (n:ℝ)+1/2 := by
    intro n hn
    have hb := abs_lt.mp (phaseSet_abs_lt_half hP hR hβ)
    have hlo : (-1:ℝ) < n := by linarith
    have hhi : (n:ℝ) < 0 := by linarith
    have hlo' : (-1:ℤ) < n := by exact_mod_cast hlo
    have hhi' : n < 0 := by exact_mod_cast hhi
    omega
  obtain ⟨U,hU,hUS⟩ := periodicPhaseSet_point_isolated hP hR hmem hseam
  have hβU : β ∈ U := (show β ∈ U ∩ periodicPhaseSet P R by rw [hUS]; exact mem_singleton β).1
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hU β hβU
  refine ⟨ε,hε,fun n y hy hne => ?_⟩
  by_contra hnot
  have hd : |(y-(n:ℝ))-β| < ε := by
    simpa only [sub_sub] using (lt_of_not_ge hnot)
  have hu : y-(n:ℝ) ∈ U := hball (by simpa only [Metric.mem_ball,Real.dist_eq] using hd)
  have hs := periodicPhaseSet_sub_int P R n hy
  have he : y-(n:ℝ) = β := by
    have hh : y-(n:ℝ) ∈ U ∩ periodicPhaseSet P R := ⟨hu,hs⟩
    simpa only [hUS,mem_singleton_iff] using hh
  apply hne
  linarith

/-- Scaling a fixed isolated phase yields a single physical probe width for every cell. -/
theorem exists_scaled_phase_probe_width {P R : ℕ} (hP : 1 ≤ P) (hR : 1 ≤ R)
    {β : ℝ} (hβ : β ∈ phaseSet P R) (t : ℝ) (ht : 0 < t) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℤ,
      ∀ y ∈ (fun x : ℝ => t*x) '' periodicPhaseSet P R,
        y ≠ t*((n:ℝ)+β) → 4*δ ≤ |y-t*((n:ℝ)+β)| := by
  obtain ⟨ε,hε,hbound⟩ := exists_phase_orbit_isolation hP hR hβ
  refine ⟨t*ε/4,by positivity,?_⟩
  rintro n y ⟨x,hx,rfl⟩ hne
  have hn : x ≠ (n:ℝ)+β := fun h => hne (by rw [h])
  have hh := mul_le_mul_of_nonneg_left (hbound n x hx hn) ht.le
  have he : t*x-t*((n:ℝ)+β) = t*(x-((n:ℝ)+β)) := by ring
  rw [he,abs_mul,abs_of_pos ht]
  linarith

/-- The concrete whole sector lies in its corresponding scaled periodic closure. -/
theorem sectorSet_subset_scaled_periodic (R : ℕ+ → ℕ) (s : ℕ+ → ℝ) (b : Label) :
    sectorSet R s b ⊆ (fun x : ℝ => labelScale s b*x) '' periodicPhaseSet b.1 (R b.1) := by
  rintro y ⟨x,⟨j,positive,n,hn,rfl⟩,rfl⟩
  exact ⟨_,⟨n,_,Or.inl ⟨j,positive,rfl⟩,rfl⟩,rfl⟩

/-- A coefficient is an actual fixed-width compact probe of one physical phase orbit. -/
def isolatedOrbitCoefficient (U : TemperedDistribution ℝ ℂ) (t β δ : ℝ)
    (hδ : 0 < δ) (n : ℤ) : ℂ :=
  U (localJetProbe compactSchwartzCutoff δ hδ 0 (t*((n:ℝ)+β)))

/-- Fixed native order gives polynomial coefficient growth on every fixed-width orbit.
The constant may depend on the chosen phase and width, never on the integer cell. -/
theorem exists_isolatedOrbitCoefficient_polynomial_bound (q : ℕ) (t β δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : HermiteScale (-(q:ℤ)), ∀ n : ℤ,
      ‖isolatedOrbitCoefficient (hermiteScaleDistribution q T) t β δ hδ n‖ ≤
        C*‖T‖*(1+|(n:ℝ)|)^(2*q) := by
  obtain ⟨B,hB,hbound⟩ := exists_localJetProbe_native_polynomial_bound q 0 compactSchwartzCutoff δ hδ
  let D : ℝ := 1+|t| *(1+|β|)
  have hD : 0 < D := by dsimp only [D]; positivity
  refine ⟨B*D^(2*q),mul_pos hB (pow_pos hD _),fun T n => ?_⟩
  have hweight : 1+|t*((n:ℝ)+β)| ≤ D*(1+|(n:ℝ)|) := by
    have hh : |(n:ℝ)+β| ≤ |(n:ℝ)|+|β| := by
      simpa only [Real.norm_eq_abs] using norm_add_le (n:ℝ) β
    rw [abs_mul]
    dsimp only [D]
    have hmul := mul_le_mul_of_nonneg_left hh (abs_nonneg t)
    have htriple : 0 ≤ |t| * |β| * |(n:ℝ)| := by positivity
    nlinarith [abs_nonneg t,abs_nonneg β,abs_nonneg (n:ℝ)]
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1+|t*((n:ℝ)+β)|) hweight (2*q)
  rw [isolatedOrbitCoefficient,hermiteScaleDistribution_apply]
  calc
    _ ≤ ‖T‖*‖schwartzToHermiteScale q (localJetProbe compactSchwartzCutoff δ hδ 0 (t*((n:ℝ)+β)))‖ :=
      norm_hermiteScalePairing_le (q:ℤ) T _
    _ ≤ ‖T‖*(B*(1+|t*((n:ℝ)+β)|)^(2*q)) :=
      mul_le_mul_of_nonneg_left (hbound 0 (by omega) _) (norm_nonneg _)
    _ ≤ ‖T‖*(B*(D*(1+|(n:ℝ)|))^(2*q)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp hB.le) (norm_nonneg _)
    _ = _ := by rw [mul_pow]; ring

/-- Equal actual carrier values give equal whole atomic-source test actions. -/
theorem atomic_test_eq_of_eqOn (L : LocallyFiniteCarrier) (U : TemperedDistribution ℝ ℂ)
    (hU : AtomicOnCarrier L U) (f g : SchwartzMap ℝ ℂ)
    (he : ∀ x ∈ L.carrier, f x = g x) : U f = U g := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply hU
  intro x hx
  simpa only [sub_apply,sub_eq_zero] using he x hx

/-- Missing physical cells have exactly zero coefficient, derived from value-only carrier action. -/
theorem isolatedOrbitCoefficient_zero_of_missing (L : LocallyFiniteCarrier)
    (U : TemperedDistribution ℝ ℂ) (hU : AtomicOnCarrier L U)
    (t β δ : ℝ) (hδ : 0 < δ)
    (hisol : ∀ n : ℤ, ∀ y ∈ L.carrier, y ≠ t*((n:ℝ)+β) → 4*δ ≤ |y-t*((n:ℝ)+β)|)
    (n : ℤ) (hn : t*((n:ℝ)+β) ∉ L.carrier) : isolatedOrbitCoefficient U t β δ hδ n = 0 := by
  apply hU
  intro y hy
  apply localJetProbe_cutoff_zero
  have hh := hisol n y hy (fun he => hn (he ▸ hy))
  linarith


/-- Actual coefficients of the selected spectral source on one fixed isolated orbit. -/
def isolatedSourceCoefficient (σ : ℝ) (hσ : 0 < σ) (p : ℕ)
    (R : ℕ+ → ℕ) (s : ℕ+ → ℝ) (b : Label) (β δ : ℝ) (hδ : 0 < δ)
    (T : HermiteScale (-(p:ℤ))) (n : ℤ) : ℂ :=
  isolatedOrbitCoefficient
    (𝓕 (hermiteScaleDistribution (6*p) (nativeSourcePiece σ hσ p R s {b} T)))
    (labelScale s b) β δ hδ n

/-- A fixed actual phase has a constructed physical width and polynomial coefficient bound.
No uniformity as the phase approaches the seam is asserted. -/
theorem exists_isolatedSourceCoefficient_bound (σ : ℝ) (hσ : 0 < σ) (p : ℕ)
    (R : ℕ+ → ℕ) (s : ℕ+ → ℝ)
    (hR : ∀ i, 1 ≤ R i) (hs : ∀ i, s i ∈ Icc (1:ℝ) 2)
    (b : Label) (β : ℝ) (hβ : β ∈ phaseSet b.1 (R b.1)) :
    ∃ δ : ℝ, ∃ hδ : 0 < δ,
      (∀ n : ℤ, ∀ y ∈ sectorSet R s b,
        y ≠ labelScale s b*((n:ℝ)+β) → 4*δ ≤ |y-labelScale s b*((n:ℝ)+β)|) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ T : HermiteScale (-(p:ℤ)), ∀ n : ℤ,
        ‖isolatedSourceCoefficient σ hσ p R s b β δ hδ T n‖ ≤
          C*‖T‖*(1+|(n:ℝ)|)^(12*p) := by
  obtain ⟨δ,hδ,hisol⟩ := exists_scaled_phase_probe_width b.1.pos (hR b.1) hβ
    (labelScale s b) (labelScale_pos s hs b)
  refine ⟨δ,hδ,fun n y hy hne => hisol n y (sectorSet_subset_scaled_periodic R s b hy) hne,?_⟩
  obtain ⟨C,hC,hcoeff⟩ := exists_isolatedOrbitCoefficient_polynomial_bound (6*p)
    (labelScale s b) β δ hδ
  obtain ⟨B,hB,hpiece⟩ := exists_nativeSourcePiece_norm_bound σ hσ p
  refine ⟨C*B,mul_pos hC hB,fun T n => ?_⟩
  have he := hermiteFourier_represents_distributionalFourier (6*p)
    (nativeSourcePiece σ hσ p R s {b} T)
  unfold isolatedSourceCoefficient
  rw [← he]
  have hc := hcoeff (hermiteFourier (-((6*p:ℕ):ℤ)) (nativeSourcePiece σ hσ p R s {b} T)) n
  rw [LinearIsometryEquiv.norm_map] at hc
  have hpow : 2*(6*p) = 12*p := by omega
  rw [hpow] at hc
  apply hc.trans
  calc
    _ ≤ C*(B*‖T‖)*(1+|(n:ℝ)|)^(12*p) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hpiece R s {b} T) hC.le) (by positivity)
    _ = _ := by ring

/-- Every deleted physical cell is assigned zero by the actual selected spectral source. -/
theorem isolatedSourceCoefficient_zero_of_missing (σ : ℝ) (hσ : 0 < σ) (p : ℕ)
    (R : ℕ+ → ℕ) (s : ℕ+ → ℝ)
    (hsep : ∀ b d : Label, b ≠ d → ∀ x ∈ sectorSet R s b,
      ∀ y ∈ sectorSet R s d, σ/(1+|x|+|y|)^6 ≤ |x-y|)
    (L : LocallyFiniteCarrier) (hL : L.carrier ⊆ carrierSet R s)
    (T : HermiteScale (-(p:ℤ)))
    (hT : AtomicOnCarrier L (𝓕 (hermiteScaleDistribution p T)))
    (b : Label) (β δ : ℝ) (hδ : 0 < δ)
    (hisol : ∀ n : ℤ, ∀ y ∈ sectorSet R s b,
      y ≠ labelScale s b*((n:ℝ)+β) → 4*δ ≤ |y-labelScale s b*((n:ℝ)+β)|)
    (n : ℤ) (hn : labelScale s b*((n:ℝ)+β) ∉ sectorSet R s b) :
    isolatedSourceCoefficient σ hσ p R s b β δ hδ T n = 0 := by
  have hat := nativeSourcePiece_spectral_atomic σ hσ p R s hsep L hL T hT {b}
  apply isolatedOrbitCoefficient_zero_of_missing
    (L.restrict (L.carrier ∩ selectedSectorUnion R s {b}) inter_subset_left) _ hat
  · intro m y hy hne
    have hyb : y ∈ sectorSet R s b := by
      simpa [selectedSectorUnion] using hy.2
    exact hisol m y hyb hne
  · intro hy
    apply hn
    simpa [selectedSectorUnion] using hy.2


/-- Rapid coefficient moments dominate a fixed polynomially growing phase orbit. -/
theorem summable_phase_convolution_of_polynomial_bound (D : ℕ) (a c : ℤ → ℂ)
    (ha : Summable (fun l : ℤ => (1+|(l:ℝ)|)^D*‖a l‖))
    (C : ℝ) (hC : 0 ≤ C) (hc : ∀ m : ℤ, ‖c m‖ ≤ C*(1+|(m:ℝ)|)^D)
    (n : ℤ) : Summable (fun l : ℤ => a l*c (n-l)) := by
  apply Summable.of_norm_bounded (ha.mul_left (C*(1+|(n:ℝ)|)^D))
  intro l
  have hw : 1+|((n-l:ℤ):ℝ)| ≤ (1+|(n:ℝ)|)*(1+|(l:ℝ)|) := by
    rw [Int.cast_sub]
    have hh : |(n:ℝ)-(l:ℝ)| ≤ |(n:ℝ)|+|(l:ℝ)| := by
      simpa only [Real.norm_eq_abs] using norm_sub_le (n:ℝ) (l:ℝ)
    nlinarith [mul_nonneg (abs_nonneg (n:ℝ)) (abs_nonneg (l:ℝ))]
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1+|((n-l:ℤ):ℝ)|) hw D
  rw [norm_mul]
  calc
    _ ≤ ‖a l‖*(C*(1+|((n-l:ℤ):ℝ)|)^D) := mul_le_mul_of_nonneg_left (hc (n-l)) (norm_nonneg _)
    _ ≤ ‖a l‖*(C*((1+|(n:ℝ)|)*(1+|(l:ℝ)|))^D) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp hC) (norm_nonneg _)
    _ = _ := by rw [mul_pow]; ring

/-- Symmetric actual translation cutoffs converge to the complete phase convolution. -/
theorem tendsto_phase_convolution_cutoffs (a c : ℤ → ℂ) (n : ℤ)
    (h : Summable (fun l : ℤ => a l*c (n-l))) :
    Tendsto (fun L : ℕ => ∑ l ∈ Finset.Icc (-(L:ℤ)) (L:ℤ), a l*c (n-l))
      atTop (𝓝 (∑' l : ℤ, a l*c (n-l))) :=
  h.hasSum.comp Finset.tendsto_Icc_neg

/-- Actual fixed-phase coefficients and the full annihilator Fourier coefficients have an
absolutely convergent convolution, at the same constructed physical width. -/
theorem exists_isolatedSourceCoefficient_convolution (σ : ℝ) (hσ : 0 < σ) (p : ℕ)
    (R : ℕ+ → ℕ) (s : ℕ+ → ℝ)
    (hR : ∀ i, 1 ≤ R i) (hs : ∀ i, s i ∈ Icc (1:ℝ) 2)
    (b : Label) (β : ℝ) (hβ : β ∈ phaseSet b.1 (R b.1)) :
    ∃ δ : ℝ, ∃ hδ : 0 < δ,
      (∀ n : ℤ, ∀ y ∈ sectorSet R s b,
        y ≠ labelScale s b*((n:ℝ)+β) → 4*δ ≤ |y-labelScale s b*((n:ℝ)+β)|) ∧
      ∀ T : HermiteScale (-(p:ℤ)), ∀ n : ℤ,
        Summable (fun l : ℤ => phaseCoefficient b.1 (R b.1) b.1.pos (hR b.1) l *
          isolatedSourceCoefficient σ hσ p R s b β δ hδ T (n-l)) := by
  obtain ⟨δ,hδ,hisol,C,hC,hbound⟩ := exists_isolatedSourceCoefficient_bound σ hσ p R s hR hs b β hβ
  refine ⟨δ,hδ,hisol,fun T n => ?_⟩
  apply summable_phase_convolution_of_polynomial_bound (12*p) _ _
    (phaseCoefficient_all_moments b.1 (R b.1) b.1.pos (hR b.1) (12*p))
    (C*‖T‖) (mul_nonneg hC.le (norm_nonneg _))
  exact hbound T

end
end MeyerGeneralProblem.Adaptive
