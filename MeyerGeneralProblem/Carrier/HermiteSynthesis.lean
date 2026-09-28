module

public import MeyerGeneralProblem.Atomic.GramSchur
public import MeyerGeneralProblem.Atomic.HermiteDistribution
public import MeyerGeneralProblem.Hermite.MehlerOffDiagonal
public import MeyerGeneralProblem.Carrier.SignedSquareSchur
public import MeyerGeneralProblem.Carrier.TwoSided

@[expose] public section

/-!
# Carrier-indexed Hermite point-mass synthesis

This module installs the concrete atomic family used by the endpoint Gram
model. Each negative-scale Dirac vector is normalized by its exact Hilbert
norm. Given the genuinely analytic Bessel analysis map, its adjoint synthesizes
the carrier family, and the resulting norm-convergent series is identified
with a convergent series of genuine tempered Dirac distributions. The same
construction is transported through the Hermite Fourier transform.

The generic synthesis definitions take the Bessel analysis map as explicit
input. Later in this file it is constructed from strict-subcritical carrier
geometry using the compiled Gaussian localization and row-summation theorem;
the endpoint construction therefore carries no Bessel assumption.
-/

namespace MeyerGeneralProblem

noncomputable section

/-- A Hermite point mass divided by its exact negative-scale norm. This is the
diagonal normalization used in the same-side and cross Gram matrices. -/
def normalizedHermitePointMass
    (m : ℕ) (hm : 1 ≤ m) (x : ℝ) : HermiteScale (-(m : ℤ)) :=
  ((‖hermitePointMass m hm x‖⁻¹ : ℝ) : ℂ) • hermitePointMass m hm x

/-- Exact coefficient-series formula for the genuine negative-scale Dirac
inner product. -/
theorem inner_hermitePointMass_eq_tsum
    (m : ℕ) (hm : 1 ≤ m) (x y : ℝ) :
    inner ℂ (hermitePointMass m hm x) (hermitePointMass m hm y) =
      ∑' n : ℕ, starRingEnd ℂ (hermiteDiracCoefficients m x n) *
        hermiteDiracCoefficients m y n := by
  rw [lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  simp only [RCLike.inner_apply, hermitePointMass_apply]
  ring

/-- The actual normalized same-side Hermite Gram kernel. -/
def normalizedHermiteGramKernel
    (m : ℕ) (hm : 1 ≤ m) (x y : ℝ) : ℂ :=
  inner ℂ (normalizedHermitePointMass m hm x)
    (normalizedHermitePointMass m hm y)

/-- Exact series representation of the normalized same-side Gram kernel.
This is the spectral starting point for the Mehler integral and pending
signed-square localization estimate. -/
theorem normalizedHermiteGramKernel_eq_tsum
    (m : ℕ) (hm : 1 ≤ m) (x y : ℝ) :
    normalizedHermiteGramKernel m hm x y =
      (((‖hermitePointMass m hm x‖⁻¹ *
          ‖hermitePointMass m hm y‖⁻¹ : ℝ) : ℂ) *
        ∑' n : ℕ, starRingEnd ℂ (hermiteDiracCoefficients m x n) *
          hermiteDiracCoefficients m y n) := by
  unfold normalizedHermiteGramKernel normalizedHermitePointMass
  rw [inner_smul_left, inner_smul_right, inner_hermitePointMass_eq_tsum]
  have hx : starRingEnd ℂ
      (((‖hermitePointMass m hm x‖⁻¹ : ℝ) : ℂ)) =
      (((‖hermitePointMass m hm x‖⁻¹ : ℝ) : ℂ)) := by
    change star (((‖hermitePointMass m hm x‖⁻¹ : ℝ) : ℂ)) = _
    apply Complex.ext <;> simp
  rw [hx]
  push_cast
  ring

/-- The normalized same-side kernel is the exact Hermite resolvent kernel
divided by the two point-evaluation norms.  This is the form consumed by the
Laplace/Mehler integral and pending tail-shell localization estimates. -/
theorem normalizedHermiteGramKernel_eq_resolventKernel
    (m : ℕ) (hm : 1 ≤ m) (x y : ℝ) :
    normalizedHermiteGramKernel m hm x y =
      (((‖hermitePointMass m hm x‖⁻¹ *
          ‖hermitePointMass m hm y‖⁻¹ : ℝ) : ℂ) *
        hermiteResolventKernel m x y) := by
  unfold normalizedHermiteGramKernel normalizedHermitePointMass
  rw [inner_smul_left, inner_smul_right,
    inner_hermitePointMass_eq_resolventKernel]
  have hx : starRingEnd ℂ
      (((‖hermitePointMass m hm x‖⁻¹ : ℝ) : ℂ)) =
      (((‖hermitePointMass m hm x‖⁻¹ : ℝ) : ℂ)) := by
    change star (((‖hermitePointMass m hm x‖⁻¹ : ℝ) : ℂ)) = _
    apply Complex.ext <;> simp
  rw [hx]
  push_cast
  ring

/-- The normalization loss in the same-side Gram kernel is exactly canceled
by the sharp diagonal scale retained in the refined Mehler estimate. -/
def hermiteNormalizedGramGaussianConstant (m : ℕ) : ℝ :=
  hermiteRawNormalizationConstant m / hermiteDiagonalFloorConstant m

theorem hermiteNormalizedGramGaussianConstant_pos
    {m : ℕ} (hm : 1 ≤ m) :
    0 < hermiteNormalizedGramGaussianConstant m := by
  unfold hermiteNormalizedGramGaussianConstant
  exact div_pos (hermiteRawNormalizationConstant_pos hm)
    (hermiteDiagonalFloorConstant_pos m)

/-- Genuine signed-square Gaussian localization for the normalized Hermite
Gram kernel. -/
theorem norm_normalizedHermiteGramKernel_le_signedSquare
    (m : ℕ) (hm : 1 ≤ m) (x y : ℝ) :
    ‖normalizedHermiteGramKernel m hm x y‖ ≤
      hermiteNormalizedGramGaussianConstant m *
        Real.exp (-(Real.pi / 2) *
          |signedSquare y - signedSquare x|) := by
  have hnormEq :
      ‖normalizedHermiteGramKernel m hm x y‖ =
        ‖hermitePointMass m hm x‖⁻¹ *
          ‖hermitePointMass m hm y‖⁻¹ *
            ‖hermiteResolventKernel m x y‖ := by
    rw [normalizedHermiteGramKernel_eq_resolventKernel m hm x y,
      norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (inv_nonneg.mpr (norm_nonneg _))
        (inv_nonneg.mpr (norm_nonneg _)))]
  rw [hnormEq]
  have hleft : 0 ≤
      ‖hermitePointMass m hm x‖⁻¹ *
        ‖hermitePointMass m hm y‖⁻¹ *
          ‖hermiteResolventKernel m x y‖ := by positivity
  have hright : 0 ≤
      hermiteNormalizedGramGaussianConstant m *
        Real.exp (-(Real.pi / 2) *
          |signedSquare y - signedSquare x|) := by
    exact mul_nonneg (hermiteNormalizedGramGaussianConstant_pos hm).le
      (Real.exp_pos _).le
  rw [← sq_le_sq₀ hleft hright]
  have hInvX :=
    inv_norm_hermitePointMass_sq_le_diagonalFloor_inv m hm x
  have hInvY :=
    inv_norm_hermitePointMass_sq_le_diagonalFloor_inv m hm y
  have hraw :=
    norm_hermiteResolventKernel_sq_le_diagonalScales m hm x y
  let FX := hermitePointMassDiagonalFloor m x
  let FY := hermitePointMassDiagonalFloor m y
  let FC := hermiteDiagonalFloorConstant m
  let S := (hermiteDiagonalScale x * hermiteDiagonalScale y) ^
    hermiteResolventHalfShape m
  let R := hermiteRawNormalizationConstant m
  let E := Real.exp (-Real.pi * |x * abs x - y * abs y|)
  have hFX : 0 < FX := hermitePointMassDiagonalFloor_pos m x
  have hFY : 0 < FY := hermitePointMassDiagonalFloor_pos m y
  have hFC : 0 < FC := hermiteDiagonalFloorConstant_pos m
  have hS : 0 < S := by
    dsimp [S]
    exact Real.rpow_pos_of_pos
      (mul_pos (hermiteDiagonalScale_pos x)
        (hermiteDiagonalScale_pos y)) _
  have hfloor : FX * FY = FC ^ 2 * S := by
    exact mul_hermitePointMassDiagonalFloor_eq m hm x y
  have hmiddle :
      (‖hermitePointMass m hm x‖⁻¹ *
          ‖hermitePointMass m hm y‖⁻¹ *
            ‖hermiteResolventKernel m x y‖) ^ 2 ≤
        FX⁻¹ * FY⁻¹ * (R ^ 2 * E * S) := by
    calc
      (‖hermitePointMass m hm x‖⁻¹ *
          ‖hermitePointMass m hm y‖⁻¹ *
            ‖hermiteResolventKernel m x y‖) ^ 2 =
        ‖hermitePointMass m hm x‖⁻¹ ^ 2 *
          ‖hermitePointMass m hm y‖⁻¹ ^ 2 *
            ‖hermiteResolventKernel m x y‖ ^ 2 := by ring
      _ ≤ FX⁻¹ * FY⁻¹ * (R ^ 2 * E * S) := by
        dsimp [FX, FY, R, E, S]
        gcongr
  calc
    (‖hermitePointMass m hm x‖⁻¹ *
        ‖hermitePointMass m hm y‖⁻¹ *
          ‖hermiteResolventKernel m x y‖) ^ 2 ≤
      FX⁻¹ * FY⁻¹ * (R ^ 2 * E * S) := hmiddle
    _ = (R / FC) ^ 2 * E := by
      field_simp [hFX.ne', hFY.ne', hFC.ne']
      rw [hfloor]
      ring
    _ = (hermiteNormalizedGramGaussianConstant m *
        Real.exp (-(Real.pi / 2) *
          |signedSquare y - signedSquare x|)) ^ 2 := by
      dsimp [R, FC, E]
      unfold hermiteNormalizedGramGaussianConstant signedSquare
      rw [mul_pow]
      have habs : abs (x * abs x - y * abs y) =
          abs (y * abs y - x * abs x) :=
        abs_sub_comm _ _
      rw [habs, ← Real.exp_nat_mul]
      congr 1
      norm_num
      ring

/-- The actual normalized same-side Gram kernel is a rigorously justified
Laplace integral of the genuine Hermite heat kernel.  The imported Mehler
formula supplies its exact closed Gaussian and signed-square decay. -/
theorem normalizedHermiteGramKernel_eq_laplaceIntegral
    (m : ℕ) (hm : 1 ≤ m) (x y : ℝ) :
    normalizedHermiteGramKernel m hm x y =
      (((‖hermitePointMass m hm x‖⁻¹ *
          ‖hermitePointMass m hm y‖⁻¹ : ℝ) : ℂ) *
        ((((2 * m - 1).factorial : ℝ)⁻¹ : ℝ) : ℂ)) *
          ∫ t : ℝ in Set.Ioi 0,
            (((t ^ ((2 * m : ℕ) - 1) * Real.exp (-t) : ℝ) : ℂ)) *
              hermiteHeatKernel t x y := by
  rw [normalizedHermiteGramKernel_eq_resolventKernel m hm x y,
    hermiteResolventKernel_eq_laplaceIntegral m hm x y]
  ring

/-- A Hermite point mass is nonzero; its zeroth raw Hermite coefficient is a
strictly positive Gaussian. -/
theorem hermitePointMass_ne_zero
    (m : ℕ) (hm : 1 ≤ m) (x : ℝ) :
    hermitePointMass m hm x ≠ 0 := by
  intro h
  have hcoord := congrArg
    (fun u : HermiteScale (-(m : ℤ)) =>
      rawHermiteCoefficients (-(m : ℤ)) u 0) h
  rw [rawHermiteCoefficients_hermitePointMass] at hcoord
  have hzero : rawHermiteCoefficients (-(m : ℤ))
      (0 : HermiteScale (-(m : ℤ))) 0 = 0 := by
    change (hermiteScaleWeight (-(m : ℤ)) 0 : ℂ)⁻¹ * 0 = 0
    exact mul_zero _
  rw [hzero, normalizedHermiteSchwartz_eq_twoPi,
    TauCeti.twoPiHermiteSchwartzMap_apply,
    TauCeti.twoPiHermiteFunction_zero] at hcoord
  have hpos : 0 <
      (Real.sqrt (Real.sqrt (2 * Real.pi)) /
        Real.sqrt (Real.sqrt Real.pi)) * Real.exp (-Real.pi * x ^ 2) := by
    positivity
  have hne : (((Real.sqrt (Real.sqrt (2 * Real.pi)) /
        Real.sqrt (Real.sqrt Real.pi)) * Real.exp (-Real.pi * x ^ 2) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hpos.ne'
  exact hne hcoord

/-- Exact diagonal normalization: every normalized Hermite point mass has
unit norm. -/
@[simp]
theorem norm_normalizedHermitePointMass
    (m : ℕ) (hm : 1 ≤ m) (x : ℝ) :
    ‖normalizedHermitePointMass m hm x‖ = 1 := by
  rw [normalizedHermitePointMass, norm_smul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
    inv_mul_cancel₀]
  exact norm_ne_zero_iff.mpr (hermitePointMass_ne_zero m hm x)

/-- Diagonal normalization of the actual same-side Gram kernel. -/
@[simp]
theorem normalizedHermiteGramKernel_self
    (m : ℕ) (hm : 1 ≤ m) (x : ℝ) :
    normalizedHermiteGramKernel m hm x x = 1 := by
  rw [normalizedHermiteGramKernel, inner_self_eq_norm_sq_to_K,
    norm_normalizedHermitePointMass]
  norm_num

/-- Distributional realization of the normalized atom is the same exact
scalar multiple of the genuine Dirac mass. -/
theorem normalizedHermitePointMass_represents_delta
    (m : ℕ) (hm : 1 ≤ m) (x : ℝ) :
    hermiteScaleDistribution m (normalizedHermitePointMass m hm x) =
      ((‖hermitePointMass m hm x‖⁻¹ : ℝ) : ℂ) • pointMass x := by
  rw [← hermiteScaleDistributionCLM_apply, normalizedHermitePointMass,
    map_smul, hermiteScaleDistributionCLM_apply,
    hermitePointMass_represents_delta]

/-- The exact normalized physical atom at the `j`th node of a two-sided
carrier. -/
def carrierHermitePointMass
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier) (j : ℤ) :
    HermiteScale (-(m : ℤ)) :=
  normalizedHermitePointMass m hm (Λ j)

/-- Carrier Gram entries are evaluations of the actual normalized same-side
Hermite kernel at the carrier nodes. -/
theorem inner_carrierHermitePointMass_eq_kernel
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier) (i j : ℤ) :
    inner ℂ (carrierHermitePointMass m hm Λ i)
        (carrierHermitePointMass m hm Λ j) =
      normalizedHermiteGramKernel m hm (Λ i) (Λ j) :=
  rfl

@[simp]
theorem norm_carrierHermitePointMass
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier) (j : ℤ) :
    ‖carrierHermitePointMass m hm Λ j‖ = 1 := by
  exact norm_normalizedHermitePointMass m hm (Λ j)

/-- The analytic Bessel data for the normalized point masses of a carrier.
The generic synthesis layer accepts this data explicitly; the construction
from strict subcriticality is supplied unconditionally later in this file. -/
abbrev CarrierHermiteBesselAnalysis
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier) :=
  BesselAnalysis (carrierHermitePointMass m hm Λ)

/-- The finite-support sampling estimate used to construct the carrier's
Bessel analysis: every finite linear combination of normalized carrier atoms
is controlled by the corresponding finite coefficient vector, with one
constant independent of its support. -/
def CarrierHermiteFinsuppBesselBound
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier) (C : ℝ) : Prop :=
  ∀ c : ℤ →₀ ℂ,
    ‖Finsupp.linearCombination ℂ
        (carrierHermitePointMass m hm Λ) c‖ ≤
      C * ‖Finsupp.linearCombination ℂ
        (coefficientAtom : ℤ → CoefficientSpace ℤ) c‖

/-- Squared finite Gram-form version of the carrier Bessel estimate.  This is
the form produced by same-side kernel estimates: the atomic norm squared is
bounded by `C²` times the finite coefficient energy. -/
def CarrierHermiteFinsuppGramBound
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier) (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ c : ℤ →₀ ℂ,
    (BesselAnalysis.finsuppGramForm
        (carrierHermitePointMass m hm Λ) c).re ≤
      C ^ 2 * (c.sum fun _ z ↦ ‖z‖ ^ 2)

/-- Absolute Schur row bound for every finite section of the normalized
carrier Gram kernel.  This is the direct output expected from signed-square
Mehler localization and bounded geometry. -/
def CarrierHermiteFinsuppGramRowBound
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier) (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ s : Finset ℤ, ∀ i ∈ s,
    ∑ j ∈ s, ‖inner ℂ
      (carrierHermitePointMass m hm Λ i)
      (carrierHermitePointMass m hm Λ j)‖ ≤ C ^ 2

/-- Absolute summability and a uniform full-row ceiling for the normalized
carrier Gram kernel.  A quantitative signed-square localization theorem can
target this proposition directly. -/
def CarrierHermiteSummableGramRows
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier) (C : ℝ) : Prop :=
  0 ≤ C ∧
    (∀ i : ℤ, Summable (fun j : ℤ ↦ ‖inner ℂ
      (carrierHermitePointMass m hm Λ i)
      (carrierHermitePointMass m hm Λ j)‖)) ∧
    ∀ i : ℤ, ∑' j : ℤ, ‖inner ℂ
      (carrierHermitePointMass m hm Λ i)
      (carrierHermitePointMass m hm Λ j)‖ ≤ C ^ 2

/-- A genuine two-index Gaussian localization estimate for the normalized
carrier Gram entries.  The remaining analytic Mehler work should target this
proposition; unlike a one-variable remainder it is summable by strict
signed-square separation. -/
def CarrierHermiteSignedSquareGaussianBound
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier) (A c : ℝ) : Prop :=
  0 ≤ A ∧ 0 < c ∧ ∀ i j : ℤ,
    ‖inner ℂ
      (carrierHermitePointMass m hm Λ i)
      (carrierHermitePointMass m hm Λ j)‖ ≤
        A * Real.exp
          (-c * |signedSquare (Λ j) - signedSquare (Λ i)|)

/-- The refined Mehler estimate supplies the required Gaussian localization
for every carrier; strict subcriticality is needed only to sum its rows. -/
theorem carrierHermiteSignedSquareGaussianBound
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier) :
    CarrierHermiteSignedSquareGaussianBound m hm Λ
      (hermiteNormalizedGramGaussianConstant m) (Real.pi / 2) := by
  refine ⟨(hermiteNormalizedGramGaussianConstant_pos hm).le,
    div_pos Real.pi_pos (by norm_num), ?_⟩
  intro i j
  rw [inner_carrierHermitePointMass_eq_kernel]
  exact norm_normalizedHermiteGramKernel_le_signedSquare
    m hm (Λ i) (Λ j)

/-- A normalized signed-square Gaussian Gram estimate produces summable
carrier rows with one uniform Schur ceiling. -/
theorem TwoSidedCarrier.StrictSubcritical.exists_carrierHermiteSummableGramRows_of_gaussian
    {m : ℕ} {hm : 1 ≤ m} {Λ : TwoSidedCarrier}
    (hΛ : Λ.StrictSubcritical) {A c : ℝ}
    (h : CarrierHermiteSignedSquareGaussianBound m hm Λ A c) :
    ∃ C : ℝ, CarrierHermiteSummableGramRows m hm Λ C := by
  rcases hΛ.exists_uniform_kernelRowBound_of_signedSquareGaussian
      (fun i j ↦ ‖inner ℂ
        (carrierHermitePointMass m hm Λ i)
        (carrierHermitePointMass m hm Λ j)‖)
      h.1 h.2.1
      (fun i j ↦ ⟨norm_nonneg _, h.2.2 i j⟩) with
    ⟨R, hR, hsummable, hrow⟩
  refine ⟨R + 1, ?_⟩
  refine ⟨by linarith, hsummable, ?_⟩
  intro i
  exact (hrow i).trans (by nlinarith)

/-- Strict subcriticality unconditionally gives summable normalized Hermite
Gram rows: the analytic Gaussian hypothesis has now been discharged. -/
theorem TwoSidedCarrier.StrictSubcritical.exists_carrierHermiteSummableGramRows
    {m : ℕ} {hm : 1 ≤ m} {Λ : TwoSidedCarrier}
    (hΛ : Λ.StrictSubcritical) :
    ∃ C : ℝ, CarrierHermiteSummableGramRows m hm Λ C :=
  hΛ.exists_carrierHermiteSummableGramRows_of_gaussian
    (carrierHermiteSignedSquareGaussianBound m hm Λ)

/-- Finite Gram row control implies the carrier's finite Gram quadratic
estimate by the symmetric Schur bound. -/
theorem CarrierHermiteFinsuppGramRowBound.finsuppGramBound
    {m : ℕ} {hm : 1 ≤ m} {Λ : TwoSidedCarrier} {C : ℝ}
    (h : CarrierHermiteFinsuppGramRowBound m hm Λ C) :
    CarrierHermiteFinsuppGramBound m hm Λ C := by
  refine ⟨h.1, ?_⟩
  intro c
  exact BesselAnalysis.finsuppGramForm_re_le_of_row_bound
    (carrierHermitePointMass m hm Λ) h.2 c

/-- Full summable carrier Gram rows bound every finite Gram section. -/
theorem CarrierHermiteSummableGramRows.finsuppGramRowBound
    {m : ℕ} {hm : 1 ≤ m} {Λ : TwoSidedCarrier} {C : ℝ}
    (h : CarrierHermiteSummableGramRows m hm Λ C) :
    CarrierHermiteFinsuppGramRowBound m hm Λ C := by
  refine ⟨h.1, ?_⟩
  intro s i hi
  exact (h.2.1 i).sum_le_tsum s (fun _ _ ↦ norm_nonneg _)
    |>.trans (h.2.2 i)

namespace CarrierHermiteBesselAnalysis

/-- Build the genuine carrier analysis operator from the uniform
finite-support sampling estimate.  Density of finite coefficient sequences
and bounded extension are discharged by `BesselAnalysis`; no infinite sum is
assumed at this interface. -/
def ofFinsuppBound
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier) (C : ℝ)
    (h : CarrierHermiteFinsuppBesselBound m hm Λ C) :
    CarrierHermiteBesselAnalysis m hm Λ :=
  BesselAnalysis.of_finsupp_synthesis_bound
    (carrierHermitePointMass m hm Λ) C h

/-- Build carrier analysis directly from the finite same-side Gram estimate.
Finite Parseval and the extension to all of `ℓ²` are handled by the generic
Bessel construction. -/
def ofFinsuppGramBound
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier) (C : ℝ)
    (h : CarrierHermiteFinsuppGramBound m hm Λ C) :
    CarrierHermiteBesselAnalysis m hm Λ :=
  BesselAnalysis.of_finsupp_gram_bound
    (carrierHermitePointMass m hm Λ) C h.1 h.2

/-- Build carrier Bessel analysis from uniform finite Gram row sums.  The
finite symmetric Schur theorem supplies the quadratic estimate before the
dense-extension constructor is invoked. -/
def ofFinsuppGramRowBound
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier) (C : ℝ)
    (h : CarrierHermiteFinsuppGramRowBound m hm Λ C) :
    CarrierHermiteBesselAnalysis m hm Λ :=
  ofFinsuppGramBound m hm Λ C h.finsuppGramBound

/-- Build carrier Bessel analysis from summable absolute Gram rows with a
uniform ceiling. -/
def ofSummableGramRows
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier) (C : ℝ)
    (h : CarrierHermiteSummableGramRows m hm Λ C) :
    CarrierHermiteBesselAnalysis m hm Λ :=
  ofFinsuppGramRowBound m hm Λ C h.finsuppGramRowBound

end CarrierHermiteBesselAnalysis

/-- Under the same genuine Gaussian kernel estimate, the carrier Bessel
analysis data is constructed rather than assumed. -/
def TwoSidedCarrier.StrictSubcritical.carrierHermiteBesselAnalysisOfGaussian
    {m : ℕ} {hm : 1 ≤ m} {Λ : TwoSidedCarrier}
    (hΛ : Λ.StrictSubcritical) {A c : ℝ}
    (h : CarrierHermiteSignedSquareGaussianBound m hm Λ A c) :
    CarrierHermiteBesselAnalysis m hm Λ := by
  let hrows := hΛ.exists_carrierHermiteSummableGramRows_of_gaussian h
  exact CarrierHermiteBesselAnalysis.ofSummableGramRows
    m hm Λ hrows.choose hrows.choose_spec

/-- The genuine Bessel analysis of normalized carrier point masses under the
strict-subcritical density condition, with no remaining kernel hypothesis. -/
def TwoSidedCarrier.StrictSubcritical.carrierHermiteBesselAnalysis
    {m : ℕ} {hm : 1 ≤ m} {Λ : TwoSidedCarrier}
    (hΛ : Λ.StrictSubcritical) :
    CarrierHermiteBesselAnalysis m hm Λ :=
  hΛ.carrierHermiteBesselAnalysisOfGaussian
    (carrierHermiteSignedSquareGaussianBound m hm Λ)

/-- Continuous synthesis of normalized point masses on a carrier. -/
def carrierPointMassSynthesis
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier)
    (B : CarrierHermiteBesselAnalysis m hm Λ) :
    CoefficientSpace ℤ →L[ℂ] HermiteScale (-(m : ℤ)) :=
  B.synthesis

/-- Carrier synthesis sends a canonical coefficient atom to the corresponding
exact normalized Hermite point mass. -/
@[simp]
theorem carrierPointMassSynthesis_coefficientAtom
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier)
    (B : CarrierHermiteBesselAnalysis m hm Λ) (j : ℤ) :
    carrierPointMassSynthesis m hm Λ B (coefficientAtom j) =
      carrierHermitePointMass m hm Λ j := by
  exact B.synthesis_coefficientAtom j

/-- The carrier synthesis series converges in the negative Hermite-scale
norm, not just weakly or coordinatewise. -/
theorem hasSum_carrierPointMassSynthesis
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier)
    (B : CarrierHermiteBesselAnalysis m hm Λ) (c : CoefficientSpace ℤ) :
    HasSum (fun j => c j • carrierHermitePointMass m hm Λ j)
      (carrierPointMassSynthesis m hm Λ B c) := by
  exact B.hasSum_synthesis c

/-- Every carrier-synthesized vector lies in the closed physical atomic
subspace generated by the carrier's normalized Dirac vectors. -/
theorem carrierPointMassSynthesis_mem_atomicSupportSubspace
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier)
    (B : CarrierHermiteBesselAnalysis m hm Λ) (c : CoefficientSpace ℤ) :
    carrierPointMassSynthesis m hm Λ B c ∈
      atomicSupportSubspace (carrierHermitePointMass m hm Λ) := by
  exact B.synthesis_mem_atomicSupportSubspace c

/-- Applying the Hermite distribution realization to carrier synthesis gives
the norm-limit of the corresponding genuine normalized Dirac series. -/
theorem hasSum_distribution_carrierPointMassSynthesis
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier)
    (B : CarrierHermiteBesselAnalysis m hm Λ) (c : CoefficientSpace ℤ) :
    HasSum
      (fun j => c j •
        (((‖hermitePointMass m hm (Λ j)‖⁻¹ : ℝ) : ℂ) • pointMass (Λ j)))
      (hermiteScaleDistribution m (carrierPointMassSynthesis m hm Λ B c)) := by
  have h := (hermiteScaleDistributionCLM m).hasSum
    (hasSum_carrierPointMassSynthesis m hm Λ B c)
  simpa only [map_smul, hermiteScaleDistributionCLM_apply,
    carrierHermitePointMass,
    normalizedHermitePointMass_represents_delta] using h

/-- Exact tempered-distribution identity for the synthesized carrier series.
The right-hand side is well-defined because the preceding theorem supplies
its unconditional sum. -/
theorem hermiteScaleDistribution_carrierPointMassSynthesis
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier)
    (B : CarrierHermiteBesselAnalysis m hm Λ) (c : CoefficientSpace ℤ) :
    hermiteScaleDistribution m (carrierPointMassSynthesis m hm Λ B c) =
      ∑' j : ℤ, c j •
        (((‖hermitePointMass m hm (Λ j)‖⁻¹ : ℝ) : ℂ) • pointMass (Λ j)) := by
  exact (hasSum_distribution_carrierPointMassSynthesis m hm Λ B c).tsum_eq.symm

/-- Fourier-side carrier synthesis, obtained by the genuine diagonal Hermite
Fourier transform of the physical synthesis. -/
def carrierFourierPointMassSynthesis
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier)
    (B : CarrierHermiteBesselAnalysis m hm Λ) :
    CoefficientSpace ℤ →L[ℂ] HermiteScale (-(m : ℤ)) :=
  (hermiteFourier (-(m : ℤ))).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (carrierPointMassSynthesis m hm Λ B)

/-- A Fourier-side coefficient atom is the Hermite Fourier transform of the
corresponding normalized physical point mass. -/
@[simp]
theorem carrierFourierPointMassSynthesis_coefficientAtom
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier)
    (B : CarrierHermiteBesselAnalysis m hm Λ) (j : ℤ) :
    carrierFourierPointMassSynthesis m hm Λ B (coefficientAtom j) =
      hermiteFourier (-(m : ℤ)) (carrierHermitePointMass m hm Λ j) := by
  rw [carrierFourierPointMassSynthesis, ContinuousLinearMap.comp_apply,
    carrierPointMassSynthesis_coefficientAtom]
  rfl

/-- Distributional realization of Fourier-side synthesis is exactly the
distributional Fourier transform of physical carrier synthesis. -/
theorem hermiteScaleDistribution_carrierFourierPointMassSynthesis
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier)
    (B : CarrierHermiteBesselAnalysis m hm Λ) (c : CoefficientSpace ℤ) :
    hermiteScaleDistribution m (carrierFourierPointMassSynthesis m hm Λ B c) =
      FourierTransform.fourier
        (hermiteScaleDistribution m (carrierPointMassSynthesis m hm Λ B c)) := by
  exact hermiteFourier_represents_distributionalFourier m
    (carrierPointMassSynthesis m hm Λ B c)

/-- Inverse-Fourier-side carrier synthesis. Its range is the original
endpoint space `Y = 𝓕⁻¹ X`, rather than the forward transform `𝓕 X` used to
write the raw cross matrix in reversed unitary orientation. -/
def carrierInverseFourierPointMassSynthesis
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier)
    (B : CarrierHermiteBesselAnalysis m hm Λ) :
    CoefficientSpace ℤ →L[ℂ] HermiteScale (-(m : ℤ)) :=
  (hermiteFourier (-(m : ℤ))).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (carrierPointMassSynthesis m hm Λ B)

/-- An inverse-Fourier-side coefficient atom is the genuine inverse Hermite
Fourier transform of the corresponding normalized physical point mass. -/
@[simp]
theorem carrierInverseFourierPointMassSynthesis_coefficientAtom
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier)
    (B : CarrierHermiteBesselAnalysis m hm Λ) (j : ℤ) :
    carrierInverseFourierPointMassSynthesis m hm Λ B (coefficientAtom j) =
      (hermiteFourier (-(m : ℤ))).symm
        (carrierHermitePointMass m hm Λ j) := by
  rw [carrierInverseFourierPointMassSynthesis,
    ContinuousLinearMap.comp_apply,
    carrierPointMassSynthesis_coefficientAtom]
  rfl

end

end MeyerGeneralProblem
