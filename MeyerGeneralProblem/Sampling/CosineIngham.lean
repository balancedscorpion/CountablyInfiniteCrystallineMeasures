module

public import MeyerGeneralProblem.Sampling.Ingham
public import MeyerGeneralProblem.Atomic.GramSchur

@[expose] public section

/-!
# Cosine-window finite Ingham inequality

This module proves a separated-frequency Ingham lower bound at the strict
threshold `2ad > 1`. A cosine taper turns the window kernel into an explicit
reciprocal-quadratic kernel. Rounding scaled differences toward zero embeds
each off-diagonal row into integer shells, whose exact telescoping sum is one;
a finite Schur estimate then supplies the positive lower quadratic floor.
-/

namespace MeyerGeneralProblem
open Filter MeasureTheory ComplexConjugate
noncomputable section

/-- Positive reciprocal-quadratic terms on the positive integer shells. -/
def cosineNatMajorant (n : ℕ) : ℝ := (4 * ((n + 1 : ℕ) : ℝ) ^ 2 - 1)⁻¹

/-- Each positive-shell term is the difference of two adjacent odd
reciprocals. -/
theorem cosineNatMajorant_eq_telescope (n : ℕ) :
    cosineNatMajorant n = (1 / 2 : ℝ) *
      ((2 * (n : ℝ) + 1)⁻¹ - (2 * (n : ℝ) + 3)⁻¹) := by
  unfold cosineNatMajorant
  push_cast
  have hleft : 4 * ((n : ℝ) + 1) ^ 2 - 1 ≠ 0 := by
    have hn : (0 : ℝ) ≤ n := by positivity
    nlinarith [sq_nonneg (n : ℝ)]
  have h₁ : 2 * (n : ℝ) + 1 ≠ 0 := by positivity
  have h₃ : 2 * (n : ℝ) + 3 ≠ 0 := by positivity
  field_simp [hleft, h₁, h₃]
  ring

/-- Exact finite telescoping sum of the positive-shell majorant. -/
theorem sum_range_cosineNatMajorant (N : ℕ) :
    ∑ n ∈ Finset.range N, cosineNatMajorant n =
      (1 / 2 : ℝ) * (1 - (2 * (N : ℝ) + 1)⁻¹) := by
  simp_rw [cosineNatMajorant_eq_telescope]
  rw [← Finset.mul_sum]
  rw [show (∑ n ∈ Finset.range N,
      ((2 * (n : ℝ) + 1)⁻¹ - (2 * (n : ℝ) + 3)⁻¹)) =
      (fun n : ℕ => (2 * (n : ℝ) + 1)⁻¹) 0 -
        (fun n : ℕ => (2 * (n : ℝ) + 1)⁻¹) N by
    convert Finset.sum_range_sub' (fun n : ℕ => (2 * (n : ℝ) + 1)⁻¹) N using 1
    · apply Finset.sum_congr rfl
      intro n hn
      congr 2
      push_cast
      ring
    ]
  norm_num

/-- The positive-shell reciprocal-quadratic series sums to one half. -/
theorem hasSum_cosineNatMajorant :
    HasSum cosineNatMajorant (1 / 2 : ℝ) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun n => by
    unfold cosineNatMajorant
    exact inv_nonneg.mpr (by
      have hn : (0 : ℝ) ≤ n := by positivity
      push_cast
      nlinarith [sq_nonneg (n : ℝ)])) (1 / 2 : ℝ)).2
  have hg : Tendsto (fun N : ℕ => 2 * (N : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1
      (tendsto_natCast_atTop_atTop.const_mul_atTop
        (by norm_num : (0 : ℝ) < 2))
  have hinv : Tendsto (fun N : ℕ => (2 * (N : ℝ) + 1)⁻¹)
      atTop (nhds 0) := tendsto_inv_atTop_zero.comp hg
  convert (tendsto_const_nhds.sub hinv).const_mul (1 / 2 : ℝ) using 1
  · funext N
    rw [sum_range_cosineNatMajorant]
  · norm_num

/-- Two-sided integer-shell majorant, with the forbidden zero shell removed. -/
def cosineShellMajorant (k : ℤ) : ℝ :=
  if k = 0 then 0 else (4 * (k : ℝ) ^ 2 - 1)⁻¹

/-- The zero shell contributes nothing. -/
theorem cosineShellMajorant_zero : cosineShellMajorant 0 = 0 := by
  simp [cosineShellMajorant]

/-- Positive integer shells agree with `cosineNatMajorant`. -/
theorem cosineShellMajorant_nat_add_one (n : ℕ) :
    cosineShellMajorant ((n : ℤ) + 1) = cosineNatMajorant n := by
  unfold cosineShellMajorant cosineNatMajorant
  rw [ite_eq_right (by omega)]
  push_cast
  ring_nf

/-- Negative integer shells agree with `cosineNatMajorant`. -/
theorem cosineShellMajorant_neg_nat_add_one (n : ℕ) :
    cosineShellMajorant (-((n : ℤ) + 1)) = cosineNatMajorant n := by
  unfold cosineShellMajorant cosineNatMajorant
  rw [ite_eq_right (by omega)]
  push_cast
  congr 2
  ring

/-- The full two-sided shell majorant sums exactly to one. -/
theorem hasSum_cosineShellMajorant :
    HasSum cosineShellMajorant 1 := by
  have hpos : HasSum
      (fun n : ℕ => cosineShellMajorant ((n : ℤ) + 1)) (1 / 2 : ℝ) := by
    simpa only [cosineShellMajorant_nat_add_one] using hasSum_cosineNatMajorant
  have hneg : HasSum
      (fun n : ℕ => cosineShellMajorant (-((n : ℤ) + 1))) (1 / 2 : ℝ) := by
    simpa only [cosineShellMajorant_neg_nat_add_one] using hasSum_cosineNatMajorant
  convert HasSum.of_add_one_of_neg_add_one hpos hneg using 1
  · rw [cosineShellMajorant_zero]
    norm_num

/-- The two-sided shell majorant is summable. -/
theorem summable_cosineShellMajorant : Summable cosineShellMajorant :=
  hasSum_cosineShellMajorant.summable

/-- Exact value of the two-sided shell sum. -/
theorem tsum_cosineShellMajorant : ∑' k : ℤ, cosineShellMajorant k = 1 :=
  hasSum_cosineShellMajorant.tsum_eq

/-- Integer shell obtained by rounding toward zero. -/
def towardZeroFloor (u : ℝ) : ℤ :=
  if 0 ≤ u then ⌊u⌋ else -⌊-u⌋

/-- Rounding toward zero does not increase absolute value. -/
theorem abs_towardZeroFloor_cast_le_abs (u : ℝ) :
    |((towardZeroFloor u : ℤ) : ℝ)| ≤ |u| := by
  by_cases hu : 0 ≤ u
  · rw [towardZeroFloor, ite_eq_left hu, abs_of_nonneg hu,
      abs_of_nonneg (by exact_mod_cast Int.floor_nonneg.mpr hu)]
    exact Int.floor_le u
  · have hu' : u < 0 := lt_of_not_ge hu
    have hneg : 0 ≤ -u := neg_nonneg.mpr hu'.le
    rw [towardZeroFloor, ite_eq_right hu, abs_of_neg hu', Int.cast_neg,
      abs_neg, abs_of_nonneg (by exact_mod_cast Int.floor_nonneg.mpr hneg)]
    exact Int.floor_le (-u)

/-- A real outside the central unit interval rounds to a nonzero shell. -/
theorem towardZeroFloor_ne_zero {u : ℝ} (hu : 1 ≤ |u|) :
    towardZeroFloor u ≠ 0 := by
  by_cases hsign : 0 ≤ u
  · rw [abs_of_nonneg hsign] at hu
    unfold towardZeroFloor
    rw [ite_eq_left hsign]
    exact ne_of_gt (Int.floor_pos.mpr hu)
  · have hneg : 1 ≤ -u := by
      rw [abs_of_neg (lt_of_not_ge hsign)] at hu
      exact hu
    unfold towardZeroFloor
    rw [ite_eq_right hsign]
    exact neg_ne_zero.mpr (ne_of_gt (Int.floor_pos.mpr hneg))

/-- Two reals outside the central unit interval assigned to the same shell
are less than one apart. -/
theorem abs_sub_lt_one_of_towardZeroFloor_eq
    {u v : ℝ} (hu : 1 ≤ |u|) (hv : 1 ≤ |v|)
    (hfloor : towardZeroFloor u = towardZeroFloor v) :
    |u - v| < 1 := by
  by_cases hu0 : 0 ≤ u
  · have hufloor : 0 < ⌊u⌋ := by
      rw [Int.floor_pos]
      simpa [abs_of_nonneg hu0] using hu
    by_cases hv0 : 0 ≤ v
    · apply Int.abs_sub_lt_one_of_floor_eq_floor
      simpa [towardZeroFloor, hu0, hv0] using hfloor
    · have hvfloor : 0 < ⌊-v⌋ := by
        rw [Int.floor_pos]
        simpa [abs_of_neg (lt_of_not_ge hv0)] using hv
      have : ⌊u⌋ = -⌊-v⌋ := by
        simpa [towardZeroFloor, hu0, hv0] using hfloor
      omega
  · have hufloor : 0 < ⌊-u⌋ := by
      rw [Int.floor_pos]
      simpa [abs_of_neg (lt_of_not_ge hu0)] using hu
    by_cases hv0 : 0 ≤ v
    · have hvfloor : 0 < ⌊v⌋ := by
        rw [Int.floor_pos]
        simpa [abs_of_nonneg hv0] using hv
      have : -⌊-u⌋ = ⌊v⌋ := by
        simpa [towardZeroFloor, hu0, hv0] using hfloor
      omega
    · have hneg : |(-u) - (-v)| < 1 := by
        apply Int.abs_sub_lt_one_of_floor_eq_floor
        have : -⌊-u⌋ = -⌊-v⌋ := by
          simpa [towardZeroFloor, hu0, hv0] using hfloor
        omega
      simpa only [neg_sub_neg, abs_sub_comm] using hneg

/-- A scaled reciprocal-quadratic term is bounded by the integer shell to
which its argument rounds. -/
theorem inv_four_sq_sub_one_le_shellMajorant
    {q u : ℝ} (hq : 1 < q) (hu : q ≤ |u|) :
    (4 * u ^ 2 - 1)⁻¹ ≤
      q⁻¹ ^ 2 * cosineShellMajorant (towardZeroFloor (u / q)) := by
  have hq0 : 0 < q := zero_lt_one.trans hq
  have hv : 1 ≤ |u / q| := by
    rw [abs_div, abs_of_pos hq0, one_le_div hq0]
    exact hu
  let k := towardZeroFloor (u / q)
  have hk0 : k ≠ 0 := towardZeroFloor_ne_zero hv
  have hkabs : |((k : ℤ) : ℝ)| ≤ |u / q| :=
    abs_towardZeroFloor_cast_le_abs (u / q)
  have hk1 : 1 ≤ |((k : ℤ) : ℝ)| := by
    have hkpos : (0 : ℤ) < |k| := abs_pos.mpr hk0
    exact_mod_cast (show (1 : ℤ) ≤ |k| by omega)
  have hku : q * |((k : ℤ) : ℝ)| ≤ |u| := by
    calc
      q * |((k : ℤ) : ℝ)| ≤ q * |u / q| :=
        mul_le_mul_of_nonneg_left hkabs hq0.le
      _ = |u| := by rw [abs_div, abs_of_pos hq0]; field_simp
  have hdenK : 0 < 4 * ((k : ℤ) : ℝ) ^ 2 - 1 := by
    nlinarith [sq_abs ((k : ℤ) : ℝ)]
  have hdenU : 0 < 4 * u ^ 2 - 1 := by
    have hu1 : 1 < |u| := hq.trans_le hu
    nlinarith [sq_abs u]
  have hden : q ^ 2 * (4 * ((k : ℤ) : ℝ) ^ 2 - 1) ≤
      4 * u ^ 2 - 1 := by
    have hsq : (q * |((k : ℤ) : ℝ)|) ^ 2 ≤ |u| ^ 2 := by
      exact sq_le_sq₀ (mul_nonneg hq0.le (abs_nonneg _))
        (abs_nonneg _) |>.2 hku
    have hqSq : 1 ≤ q ^ 2 := by nlinarith
    ring_nf at hsq
    rw [show |((k : ℤ) : ℝ)| ^ 2 = ((k : ℤ) : ℝ) ^ 2 by
      exact sq_abs ((k : ℤ) : ℝ)] at hsq
    rw [sq_abs u] at hsq
    nlinarith
  unfold cosineShellMajorant
  rw [ite_eq_right hk0]
  change (4 * u ^ 2 - 1)⁻¹ ≤ q⁻¹ ^ 2 *
    (4 * ((k : ℤ) : ℝ) ^ 2 - 1)⁻¹
  rw [show q⁻¹ ^ 2 * (4 * ((k : ℤ) : ℝ) ^ 2 - 1)⁻¹ =
      (q ^ 2 * (4 * ((k : ℤ) : ℝ) ^ 2 - 1))⁻¹ by
    field_simp]
  exact inv_le_inv₀ hdenU (mul_pos (sq_pos_of_pos hq0) hdenK) |>.2 hden

/-- The reciprocal-quadratic off-diagonal rows of a finite separated family
are bounded by the telescoping shell sum. -/
theorem sum_inv_four_sq_sub_one_le_of_separated
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (x : ι → ℝ)
    {q : ℝ} (hq : 1 < q)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → q ≤ |x j - x i|)
    (i : ι) (hi : i ∈ s) :
    ∑ j ∈ s.erase i, (4 * (x j - x i) ^ 2 - 1)⁻¹ ≤ q⁻¹ ^ 2 := by
  let tail := {j : ι // j ∈ s.erase i}
  let shell : tail → ℤ := fun j =>
    towardZeroFloor ((x j - x i) / q)
  have hq0 : 0 < q := zero_lt_one.trans hq
  have hgap (j : tail) : q ≤ |x j - x i| := by
    apply hsep i hi j (Finset.mem_of_mem_erase j.property)
    exact Ne.symm (Finset.ne_of_mem_erase j.property)
  have hscaled (j : tail) : 1 ≤ |(x j - x i) / q| := by
    rw [abs_div, abs_of_pos hq0, one_le_div hq0]
    exact hgap j
  have hshell : Function.Injective shell := by
    intro j k hjk
    apply Subtype.ext
    by_contra hne
    have hnear := abs_sub_lt_one_of_towardZeroFloor_eq
      (hscaled j) (hscaled k) hjk
    have hnear' : |(x j - x k) / q| < 1 := by
      convert hnear using 1
      ring_nf
    have hfar : q ≤ |x j - x k| := by
      simpa only [abs_sub_comm] using
        hsep j (Finset.mem_of_mem_erase j.property)
          k (Finset.mem_of_mem_erase k.property) hne
    rw [abs_div, abs_of_pos hq0, div_lt_one hq0] at hnear'
    exact (not_lt_of_ge hfar) hnear'
  have hpoint (j : tail) :
      (4 * (x j - x i) ^ 2 - 1)⁻¹ ≤
        q⁻¹ ^ 2 * cosineShellMajorant (shell j) := by
    exact inv_four_sq_sub_one_le_shellMajorant hq (hgap j)
  have hleft : Summable (fun j : tail =>
      (4 * (x j - x i) ^ 2 - 1)⁻¹) := (hasSum_fintype _).summable
  have hright : Summable (fun k : ℤ =>
      q⁻¹ ^ 2 * cosineShellMajorant k) :=
    summable_cosineShellMajorant.mul_left _
  have htsum :
      ∑' j : tail, (4 * (x j - x i) ^ 2 - 1)⁻¹ ≤
        ∑' k : ℤ, q⁻¹ ^ 2 * cosineShellMajorant k :=
    hleft.tsum_le_tsum_of_inj shell hshell
      (fun k _ => mul_nonneg (sq_nonneg _)
        (by
          unfold cosineShellMajorant
          split_ifs
          · exact le_rfl
          · exact inv_nonneg.mpr (by
              have hkpos : (0 : ℤ) < |k| := abs_pos.mpr ‹k ≠ 0›
              have hkone : (1 : ℤ) ≤ |k| := by omega
              have hkone' : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast hkone
              nlinarith [sq_abs (k : ℝ)])))
      hpoint hright
  rw [Finset.sum_subtype (s.erase i) (fun j => by rfl)]
  calc
    ∑ j : tail, (4 * (x j - x i) ^ 2 - 1)⁻¹ =
        ∑' j : tail, (4 * (x j - x i) ^ 2 - 1)⁻¹ := by
      rw [tsum_fintype]
    _ ≤ ∑' k : ℤ, q⁻¹ ^ 2 * cosineShellMajorant k := htsum
    _ = q⁻¹ ^ 2 := by
      rw [tsum_mul_left, tsum_cosineShellMajorant, mul_one]

/-- Cosine taper on the symmetric frequency window. -/
def cosineInghamWeight (a η : ℝ) : ℝ :=
  Real.cos (Real.pi * η / (2 * a))

theorem cosineInghamWeight_mul_phase
    {a : ℝ} (ha : a ≠ 0) (t η : ℝ) :
    ((cosineInghamWeight a η : ℝ) : ℂ) * gramPhase t η =
      (1 / 2 : ℂ) *
        (gramPhase (t + 1 / (4 * a)) η +
          gramPhase (t - 1 / (4 * a)) η) := by
  unfold cosineInghamWeight gramPhase
  rw [Complex.ofReal_cos]
  change Complex.cos (Real.pi * η / (2 * a) : ℝ) *
      Complex.exp (((2 * Real.pi * t * η : ℝ) : ℂ) * Complex.I) = _
  rw [Complex.cos]
  have hplus :
      Complex.exp (((Real.pi * η / (2 * a) : ℝ) : ℂ) * Complex.I) *
          Complex.exp (((2 * Real.pi * t * η : ℝ) : ℂ) * Complex.I) =
        Complex.exp (((2 * Real.pi * (t + 1 / (4 * a)) * η : ℝ) : ℂ) *
          Complex.I) := by
    rw [← Complex.exp_add]
    apply congrArg Complex.exp
    push_cast
    field_simp [ha]
    ring
  have hminus :
      Complex.exp (-((Real.pi * η / (2 * a) : ℝ) : ℂ) * Complex.I) *
          Complex.exp (((2 * Real.pi * t * η : ℝ) : ℂ) * Complex.I) =
        Complex.exp (((2 * Real.pi * (t - 1 / (4 * a)) * η : ℝ) : ℂ) *
          Complex.I) := by
    rw [← Complex.exp_add]
    apply congrArg Complex.exp
    push_cast
    field_simp [ha]
    ring
  calc
    (Complex.exp (((Real.pi * η / (2 * a) : ℝ) : ℂ) * Complex.I) +
          Complex.exp (-((Real.pi * η / (2 * a) : ℝ) : ℂ) * Complex.I)) / 2 *
        Complex.exp (((2 * Real.pi * t * η : ℝ) : ℂ) * Complex.I) =
      (1 / 2 : ℂ) *
        (Complex.exp (((Real.pi * η / (2 * a) : ℝ) : ℂ) * Complex.I) *
            Complex.exp (((2 * Real.pi * t * η : ℝ) : ℂ) * Complex.I) +
          Complex.exp (-((Real.pi * η / (2 * a) : ℝ) : ℂ) * Complex.I) *
            Complex.exp (((2 * Real.pi * t * η : ℝ) : ℂ) * Complex.I)) := by ring
    _ = _ := by rw [hplus, hminus]

/-- Fourier kernel of the cosine-tapered symmetric window. -/
def cosineWindowKernel (a t : ℝ) : ℂ :=
  ∫ η : ℝ in Set.Icc (-a) a,
    ((cosineInghamWeight a η : ℝ) : ℂ) * gramPhase t η

theorem cosineWindowKernel_eq_average
    {a : ℝ} (ha : 0 < a) (t : ℝ) :
    cosineWindowKernel a t =
      (1 / 2 : ℂ) *
        (inghamWindowKernel a (t + 1 / (4 * a)) +
          inghamWindowKernel a (t - 1 / (4 * a))) := by
  have hplus : IntegrableOn (gramPhase (t + 1 / (4 * a)))
      (Set.Icc (-a) a) :=
    ContinuousOn.integrableOn_compact isCompact_Icc (by
      unfold gramPhase
      fun_prop)
  have hminus : IntegrableOn (gramPhase (t - 1 / (4 * a)))
      (Set.Icc (-a) a) :=
    ContinuousOn.integrableOn_compact isCompact_Icc (by
      unfold gramPhase
      fun_prop)
  rw [cosineWindowKernel]
  calc
    (∫ η : ℝ in Set.Icc (-a) a,
        ((cosineInghamWeight a η : ℝ) : ℂ) * gramPhase t η) =
      ∫ η : ℝ in Set.Icc (-a) a,
        (1 / 2 : ℂ) *
          (gramPhase (t + 1 / (4 * a)) η +
            gramPhase (t - 1 / (4 * a)) η) := by
      apply integral_congr_ae
      filter_upwards with η
      exact cosineInghamWeight_mul_phase ha.ne' t η
    _ = (1 / 2 : ℂ) *
        ((∫ η : ℝ in Set.Icc (-a) a,
            gramPhase (t + 1 / (4 * a)) η) +
          ∫ η : ℝ in Set.Icc (-a) a,
            gramPhase (t - 1 / (4 * a)) η) := by
      rw [integral_const_mul, integral_add hplus hminus]
    _ = _ := by rfl

@[simp]
theorem cosineWindowKernel_zero {a : ℝ} (ha : 0 < a) :
    cosineWindowKernel a 0 = (4 * a / Real.pi : ℝ) := by
  rw [cosineWindowKernel_eq_average ha,
    inghamWindowKernel_eq_sinc ha.le,
    inghamWindowKernel_eq_sinc ha.le]
  have harg : 2 * Real.pi * (1 / (4 * a)) * a = Real.pi / 2 := by
    field_simp [ha.ne']
    ring
  rw [show 0 + 1 / (4 * a) = 1 / (4 * a) by ring,
    show 0 - 1 / (4 * a) = -(1 / (4 * a)) by ring]
  rw [harg]
  rw [show 2 * Real.pi * (-(1 / (4 * a))) * a = -(Real.pi / 2) by
    field_simp [ha.ne']
    ring]
  rw [Real.sinc_neg, Real.sinc_of_ne_zero (by positivity : Real.pi / 2 ≠ 0),
    Real.sin_pi_div_two]
  push_cast
  field_simp [Real.pi_ne_zero]
  ring

/-- Closed rational-cosine form of the tapered kernel away from its removable
poles.  The separated application lies in the stronger region `|2at| > 1`. -/
theorem cosineWindowKernel_eq_closed
    {a t : ℝ} (ha : 0 < a) (hfar : 1 < |2 * a * t|) :
    cosineWindowKernel a t =
      ((4 * a / Real.pi) *
        (Real.cos (Real.pi * (2 * a * t)) /
          (1 - 4 * (2 * a * t) ^ 2)) : ℝ) := by
  let u : ℝ := 2 * a * t
  change 1 < |u| at hfar
  have huPlus : u + 1 / 2 ≠ 0 := by
    intro h
    have : u = -(1 / 2) := by linarith
    rw [this] at hfar
    norm_num at hfar
  have huMinus : u - 1 / 2 ≠ 0 := by
    intro h
    have : u = 1 / 2 := by linarith
    rw [this] at hfar
    norm_num at hfar
  have hargPlus :
      2 * Real.pi * (t + 1 / (4 * a)) * a =
        Real.pi * (u + 1 / 2) := by
    dsimp [u]
    field_simp [ha.ne']
    ring
  have hargMinus :
      2 * Real.pi * (t - 1 / (4 * a)) * a =
        Real.pi * (u - 1 / 2) := by
    dsimp [u]
    field_simp [ha.ne']
    ring
  have hpiPlus : Real.pi * (u + 1 / 2) ≠ 0 :=
    mul_ne_zero Real.pi_ne_zero huPlus
  have hpiMinus : Real.pi * (u - 1 / 2) ≠ 0 :=
    mul_ne_zero Real.pi_ne_zero huMinus
  have hdenPlus : 1 + 2 * u ≠ 0 := by
    intro h
    apply huPlus
    linarith
  have hdenMinus : -1 + 2 * u ≠ 0 := by
    intro h
    apply huMinus
    linarith
  have huSq : 1 < u ^ 2 := by
    nlinarith [sq_abs u]
  have hdenQuad : 1 - 4 * u ^ 2 ≠ 0 := by nlinarith
  have hdenPlus' : 1 + u * 2 ≠ 0 := by simpa [mul_comm] using hdenPlus
  have hdenMinus' : -1 + u * 2 ≠ 0 := by simpa [mul_comm] using hdenMinus
  have hdenQuad' : 1 - u ^ 2 * 4 ≠ 0 := by simpa [mul_comm] using hdenQuad
  have hdenPlusC : (((1 + 2 * u : ℝ) : ℂ)) ≠ 0 := by exact_mod_cast hdenPlus
  have hdenMinusC : (((-1 + 2 * u : ℝ) : ℂ)) ≠ 0 := by exact_mod_cast hdenMinus
  have hdenQuadC : (((1 - 4 * u ^ 2 : ℝ) : ℂ)) ≠ 0 := by exact_mod_cast hdenQuad
  rw [cosineWindowKernel_eq_average ha,
    inghamWindowKernel_eq_sinc ha.le,
    inghamWindowKernel_eq_sinc ha.le,
    hargPlus, hargMinus,
    Real.sinc_of_ne_zero hpiPlus, Real.sinc_of_ne_zero hpiMinus]
  have hsinPlus : Real.sin (Real.pi * (u + 1 / 2)) =
      Real.cos (Real.pi * u) := by
    rw [show Real.pi * (u + 1 / 2) = Real.pi * u + Real.pi / 2 by ring,
      Real.sin_add_pi_div_two]
  have hsinMinus : Real.sin (Real.pi * (u - 1 / 2)) =
      -Real.cos (Real.pi * u) := by
    rw [show Real.pi * (u - 1 / 2) = Real.pi * u - Real.pi / 2 by ring,
      Real.sin_sub_pi_div_two]
  rw [hsinPlus, hsinMinus]
  rw [show 2 * a * t = u by rfl]
  push_cast
  have hcos : Complex.cos ((Real.pi : ℂ) * (u : ℂ)) =
      ((Real.cos (Real.pi * u) : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_mul] using
      (Complex.ofReal_cos (Real.pi * u)).symm
  have hcore :
      Real.cos (Real.pi * u) * (1 + u * 2)⁻¹ * 2 -
          Real.cos (Real.pi * u) * (-1 + u * 2)⁻¹ * 2 =
        Real.cos (Real.pi * u) * (1 - u ^ 2 * 4)⁻¹ * 4 := by
    field_simp [hdenPlus', hdenMinus', hdenQuad']
    ring
  have hinvPlus : (u + 1 / 2)⁻¹ = 2 * (1 + u * 2)⁻¹ := by
    rw [← mul_one (u + 1 / 2)⁻¹,
      inv_mul_eq_iff_eq_mul₀ huPlus]
    field_simp [hdenPlus']
    ring
  have hinvMinus : (u - 1 / 2)⁻¹ = 2 * (-1 + u * 2)⁻¹ := by
    rw [← mul_one (u - 1 / 2)⁻¹,
      inv_mul_eq_iff_eq_mul₀ huMinus]
    field_simp [hdenMinus']
    ring
  have hinvPlusComm : (1 / 2 + u)⁻¹ = 2 * (1 + u * 2)⁻¹ := by
    simpa [add_comm] using hinvPlus
  have hinvMinusComm : (-1 / 2 + u)⁻¹ = 2 * (-1 + u * 2)⁻¹ := by
    rw [show -1 / 2 + u = u - 1 / 2 by ring, hinvMinus]
  have hreal :
      (1 / 2 : ℝ) *
          (2 * a * (Real.cos (Real.pi * u) /
              (Real.pi * (u + 1 / 2))) +
            2 * a * (-Real.cos (Real.pi * u) /
              (Real.pi * (u - 1 / 2)))) =
        4 * a / Real.pi *
          (Real.cos (Real.pi * u) / (1 - 4 * u ^ 2)) := by
    calc
      (1 / 2 : ℝ) *
            (2 * a * (Real.cos (Real.pi * u) /
                (Real.pi * (u + 1 / 2))) +
              2 * a * (-Real.cos (Real.pi * u) /
                (Real.pi * (u - 1 / 2)))) =
          a / Real.pi *
            (Real.cos (Real.pi * u) * (1 + u * 2)⁻¹ * 2 -
              Real.cos (Real.pi * u) * (-1 + u * 2)⁻¹ * 2) := by
            simp only [div_eq_mul_inv, mul_inv]
            rw [show u + 1 * 2⁻¹ = u + 1 / 2 by rfl, hinvPlus,
              show u - 1 * 2⁻¹ = u - 1 / 2 by rfl, hinvMinus]
            ring
      _ = a / Real.pi *
            (Real.cos (Real.pi * u) * (1 - u ^ 2 * 4)⁻¹ * 4) := by
            rw [hcore]
      _ = 4 * a / Real.pi *
            (Real.cos (Real.pi * u) / (1 - 4 * u ^ 2)) := by
            rw [show 1 - 4 * u ^ 2 = 1 - u ^ 2 * 4 by ring]
            ring
  have hcast := congrArg (fun r : ℝ => (r : ℂ)) hreal
  push_cast at hcast
  exact hcast

/-- Absolute tapered-kernel decay beyond the cosine-window transition. -/
theorem norm_cosineWindowKernel_le
    {a t q : ℝ} (ha : 0 < a) (hq : 1 < q)
    (hgap : q ≤ |2 * a * t|) :
    ‖cosineWindowKernel a t‖ ≤
      (4 * a / Real.pi) * (4 * (2 * a * t) ^ 2 - 1)⁻¹ := by
  have hfar : 1 < |2 * a * t| := hq.trans_le hgap
  rw [cosineWindowKernel_eq_closed ha hfar]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_mul]
  have hD : 0 ≤ 4 * a / Real.pi := by positivity
  rw [abs_of_nonneg hD, abs_div]
  have hden : 0 < 4 * (2 * a * t) ^ 2 - 1 := by
    nlinarith [sq_abs (2 * a * t)]
  rw [show |1 - 4 * (2 * a * t) ^ 2| =
      4 * (2 * a * t) ^ 2 - 1 by
    rw [abs_of_nonpos]
    · ring
    · linarith]
  calc
    (4 * a / Real.pi) *
          (|Real.cos (Real.pi * (2 * a * t))| /
            (4 * (2 * a * t) ^ 2 - 1)) ≤
        (4 * a / Real.pi) *
          (1 / (4 * (2 * a * t) ^ 2 - 1)) := by
      apply mul_le_mul_of_nonneg_left _ hD
      exact div_le_div_of_nonneg_right (Real.abs_cos_le_one _) hden.le
    _ = (4 * a / Real.pi) * (4 * (2 * a * t) ^ 2 - 1)⁻¹ := by
      rw [one_div]

/-- The tapered kernel is even beyond the transition region; this is the
symmetry used by the off-diagonal Schur estimate. -/
theorem cosineWindowKernel_neg_of_far
    {a t : ℝ} (ha : 0 < a) (hfar : 1 < |2 * a * t|) :
    cosineWindowKernel a (-t) = cosineWindowKernel a t := by
  rw [cosineWindowKernel_eq_closed ha (by simpa [abs_neg] using hfar),
    cosineWindowKernel_eq_closed ha hfar]
  norm_cast
  rw [show 2 * a * -t = -(2 * a * t) by ring,
    mul_neg, Real.cos_neg]
  ring_nf

/-- Absolute off-diagonal row bound for the tapered kernel on a scaled
separated finite family. -/
theorem sum_norm_cosineWindowKernel_offdiag_le
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (x : ι → ℝ)
    {a q : ℝ} (ha : 0 < a) (hq : 1 < q)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      q ≤ |2 * a * (x j - x i)|)
    (i : ι) (hi : i ∈ s) :
    ∑ j ∈ s.erase i, ‖cosineWindowKernel a (x j - x i)‖ ≤
      (4 * a / Real.pi) * q⁻¹ ^ 2 := by
  have hD : 0 ≤ 4 * a / Real.pi := by positivity
  have hscalar := sum_inv_four_sq_sub_one_le_of_separated
    s (fun j => 2 * a * x j) hq (fun i hi j hj hij => by
      simpa only [show 2 * a * x j - 2 * a * x i =
        2 * a * (x j - x i) by ring] using hsep i hi j hj hij) i hi
  have hscaled (j : ι) :
      2 * a * x j - 2 * a * x i = 2 * a * (x j - x i) := by ring
  calc
    ∑ j ∈ s.erase i, ‖cosineWindowKernel a (x j - x i)‖ ≤
        ∑ j ∈ s.erase i,
          (4 * a / Real.pi) *
            (4 * (2 * a * (x j - x i)) ^ 2 - 1)⁻¹ := by
      apply Finset.sum_le_sum
      intro j hj
      exact norm_cosineWindowKernel_le ha hq
        (hsep i hi j (Finset.mem_of_mem_erase hj)
          (Ne.symm (Finset.ne_of_mem_erase hj)))
    _ = (4 * a / Real.pi) *
        ∑ j ∈ s.erase i,
          (4 * (2 * a * (x j - x i)) ^ 2 - 1)⁻¹ := by
      rw [Finset.mul_sum]
    _ ≤ (4 * a / Real.pi) * q⁻¹ ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ hD
      simpa only [hscaled] using hscalar

/-- Exact finite quadratic-form expansion of the cosine-tapered window
energy. -/
theorem integral_cosineWeight_mul_gramFourierPolynomial_sq_eq_kernel
    {n : ℕ} (x : Fin n → ℝ) (c : Fin n → ℂ) (a : ℝ) :
    (∫ η : ℝ in Set.Icc (-a) a,
        ((cosineInghamWeight a η *
          ‖gramFourierPolynomial x c η‖ ^ 2 : ℝ) : ℂ)) =
      ∑ i, ∑ j, conj (c i) * c j *
        cosineWindowKernel a (x j - x i) := by
  have hphase (t : ℝ) : Continuous (gramPhase t) := by
    unfold gramPhase
    fun_prop
  have hweight : Continuous (cosineInghamWeight a) := by
    unfold cosineInghamWeight
    fun_prop
  have hint (i j : Fin n) : Integrable
      (fun η : ℝ ↦ conj (c i) * c j *
        (((cosineInghamWeight a η : ℝ) : ℂ) *
          gramPhase (x j - x i) η))
      (volume.restrict (Set.Icc (-a) a)) := by
    exact ContinuousOn.integrableOn_compact isCompact_Icc
      ((continuous_const.mul
        ((RCLike.continuous_ofReal.comp hweight).mul
          (hphase (x j - x i)))).continuousOn)
  have hpoint (η : ℝ) :
      ((cosineInghamWeight a η *
          ‖gramFourierPolynomial x c η‖ ^ 2 : ℝ) : ℂ) =
        ∑ i, ∑ j, conj (c i) * c j *
          (((cosineInghamWeight a η : ℝ) : ℂ) *
            gramPhase (x j - x i) η) := by
    have hnorm : (‖gramFourierPolynomial x c η‖ : ℂ) ^ 2 =
        conj (gramFourierPolynomial x c η) *
          gramFourierPolynomial x c η := by
      calc
        (‖gramFourierPolynomial x c η‖ : ℂ) ^ 2 =
            ((‖gramFourierPolynomial x c η‖ ^ 2 : ℝ) : ℂ) := by norm_cast
        _ = (Complex.normSq (gramFourierPolynomial x c η) : ℂ) := by
          rw [Complex.normSq_eq_norm_sq]
        _ = conj (gramFourierPolynomial x c η) *
            gramFourierPolynomial x c η :=
          Complex.normSq_eq_conj_mul_self
    push_cast
    rw [hnorm]
    unfold gramFourierPolynomial
    rw [map_sum, Fintype.sum_mul_sum]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [map_mul, gramPhase_sub]
    ring
  calc
    (∫ η : ℝ in Set.Icc (-a) a,
        ((cosineInghamWeight a η *
          ‖gramFourierPolynomial x c η‖ ^ 2 : ℝ) : ℂ)) =
        ∫ η : ℝ in Set.Icc (-a) a,
          ∑ i, ∑ j, conj (c i) * c j *
            (((cosineInghamWeight a η : ℝ) : ℂ) *
              gramPhase (x j - x i) η) := by
      apply integral_congr_ae
      exact ae_of_all _ hpoint
    _ = ∑ i, ∑ j,
        ∫ η : ℝ in Set.Icc (-a) a,
          conj (c i) * c j *
            (((cosineInghamWeight a η : ℝ) : ℂ) *
              gramPhase (x j - x i) η) := by
      rw [integral_finsetSum Finset.univ (fun i hi =>
        integrable_finsetSum Finset.univ (fun j hj => hint i j))]
      apply Finset.sum_congr rfl
      intro i hi
      rw [integral_finsetSum Finset.univ (fun j hj => hint i j)]
    _ = ∑ i, ∑ j, conj (c i) * c j *
        cosineWindowKernel a (x j - x i) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [cosineWindowKernel, integral_const_mul]

/-- Real form of the exact tapered window-energy identity. -/
theorem integral_cosineWeight_mul_norm_sq_eq_kernel_re
    {n : ℕ} (x : Fin n → ℝ) (c : Fin n → ℂ) (a : ℝ) :
    (∫ η : ℝ in Set.Icc (-a) a,
        cosineInghamWeight a η *
          ‖gramFourierPolynomial x c η‖ ^ 2) =
      (∑ i, ∑ j, conj (c i) * c j *
        cosineWindowKernel a (x j - x i)).re := by
  have henergy : IntegrableOn
      (fun η : ℝ ↦ cosineInghamWeight a η *
        ‖gramFourierPolynomial x c η‖ ^ 2)
      (Set.Icc (-a) a) := by
    exact ContinuousOn.integrableOn_compact isCompact_Icc
      ((by
        unfold cosineInghamWeight
        fun_prop : Continuous (cosineInghamWeight a)).mul
          ((continuous_gramFourierPolynomial x c).norm.pow 2) |>.continuousOn)
  have hcomplex :=
    integral_cosineWeight_mul_gramFourierPolynomial_sq_eq_kernel x c a
  have hre := congrArg Complex.re hcomplex
  have hcomplex_int : Integrable
      (fun η : ℝ ↦ ((cosineInghamWeight a η *
        ‖gramFourierPolynomial x c η‖ ^ 2 : ℝ) : ℂ))
      (volume.restrict (Set.Icc (-a) a)) := by
    exact henergy.ofReal
  calc
    (∫ η : ℝ in Set.Icc (-a) a,
        cosineInghamWeight a η *
          ‖gramFourierPolynomial x c η‖ ^ 2) =
        ∫ η : ℝ in Set.Icc (-a) a,
          (((cosineInghamWeight a η *
            ‖gramFourierPolynomial x c η‖ ^ 2 : ℝ) : ℂ)).re := by
      apply integral_congr_ae
      filter_upwards with η
      rfl
    _ = (∫ η : ℝ in Set.Icc (-a) a,
        ((cosineInghamWeight a η *
          ‖gramFourierPolynomial x c η‖ ^ 2 : ℝ) : ℂ)).re := by
      simpa only [RCLike.re_to_complex] using integral_re hcomplex_int
    _ = (∑ i, ∑ j, conj (c i) * c j *
        cosineWindowKernel a (x j - x i)).re := hre

/-- The cosine taper is nonnegative throughout its defining symmetric
window. -/
theorem cosineInghamWeight_nonneg_on_Icc
    {a η : ℝ} (ha : 0 < a) (hη : η ∈ Set.Icc (-a) a) :
    0 ≤ cosineInghamWeight a η := by
  unfold cosineInghamWeight
  apply Real.cos_nonneg_of_mem_Icc
  constructor
  · rw [le_div_iff₀ (by positivity : 0 < 2 * a)]
    convert mul_le_mul_of_nonneg_left hη.1 Real.pi_pos.le using 1
    ring
  · rw [div_le_iff₀ (by positivity : 0 < 2 * a)]
    convert mul_le_mul_of_nonneg_left hη.2 Real.pi_pos.le using 1
    ring

/-- The tapered energy is bounded above by the untapered interval energy. -/
theorem integral_cosineWeight_mul_norm_sq_le
    {n : ℕ} (x : Fin n → ℝ) (c : Fin n → ℂ)
    (a : ℝ) :
    (∫ η : ℝ in Set.Icc (-a) a,
        cosineInghamWeight a η *
          ‖gramFourierPolynomial x c η‖ ^ 2) ≤
      ∫ η : ℝ in Set.Icc (-a) a,
        ‖gramFourierPolynomial x c η‖ ^ 2 := by
  have hweighted : IntegrableOn
      (fun η : ℝ ↦ cosineInghamWeight a η *
        ‖gramFourierPolynomial x c η‖ ^ 2)
      (Set.Icc (-a) a) := by
    exact ContinuousOn.integrableOn_compact isCompact_Icc
      ((by
        unfold cosineInghamWeight
        fun_prop : Continuous (cosineInghamWeight a)).mul
          ((continuous_gramFourierPolynomial x c).norm.pow 2) |>.continuousOn)
  have hplain : IntegrableOn
      (fun η : ℝ ↦ ‖gramFourierPolynomial x c η‖ ^ 2)
      (Set.Icc (-a) a) := by
    exact ContinuousOn.integrableOn_compact isCompact_Icc
      ((continuous_gramFourierPolynomial x c).norm.pow 2).continuousOn
  apply integral_mono_ae hweighted hplain
  filter_upwards [ae_restrict_mem measurableSet_Icc] with η hη
  calc
    cosineInghamWeight a η * ‖gramFourierPolynomial x c η‖ ^ 2 ≤
        1 * ‖gramFourierPolynomial x c η‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (Real.cos_le_one _)
        (sq_nonneg _)
    _ = ‖gramFourierPolynomial x c η‖ ^ 2 := one_mul _

/-- A finite complex kernel with constant real diagonal and an absolute
off-diagonal Schur row bound has the corresponding lower quadratic bound. -/
theorem finite_kernel_quadratic_re_ge_of_offdiag_row
    {n : ℕ} (K : Fin n → Fin n → ℂ) (c : Fin n → ℂ) (D R : ℝ)
    (hdiag : ∀ i, K i i = (D : ℂ))
    (hsymm : ∀ i j, ‖K i j‖ = ‖K j i‖)
    (hrow : ∀ i, ∑ j ∈ Finset.univ.erase i, ‖K i j‖ ≤ R) :
    (D - R) * ∑ i, ‖c i‖ ^ 2 ≤
      (∑ i, ∑ j, conj (c i) * c j * K i j).re := by
  let g : Fin n → Fin n → ℝ := fun i j =>
    if i = j then 0 else ‖K i j‖
  let E : ℝ := ∑ i, ‖c i‖ ^ 2
  let O : ℂ := ∑ i, ∑ j ∈ Finset.univ.erase i,
    conj (c i) * c j * K i j
  have hrowg (i : Fin n) : ∑ j, g i j ≤ R := by
    calc
      ∑ j, g i j = g i i +
          ∑ j ∈ Finset.univ.erase i, g i j :=
        (Finset.add_sum_erase Finset.univ (fun j => g i j)
          (Finset.mem_univ i)).symm
      _ = ∑ j ∈ Finset.univ.erase i, ‖K i j‖ := by
        rw [show g i i = 0 by simp [g], zero_add]
        apply Finset.sum_congr rfl
        intro j hj
        simp [g, Ne.symm (Finset.ne_of_mem_erase hj)]
      _ ≤ R := hrow i
  have hschur :
      ∑ i, ∑ j, g i j * ‖c i‖ * ‖c j‖ ≤ R * E := by
    dsimp only [E]
    apply finite_symmetric_schur_quadratic_le Finset.univ g
    · intro i hi j hj
      dsimp [g]
      split_ifs
      · exact le_rfl
      · exact norm_nonneg _
    · intro i hi j hj
      dsimp [g]
      by_cases hij : i = j
      · subst j
        simp
      · rw [ite_eq_right hij, ite_eq_right (Ne.symm hij), hsymm]
    · intro i hi
      exact hrowg i
  have hquadg :
      ∑ i, ∑ j, g i j * ‖c i‖ * ‖c j‖ =
        ∑ i, ∑ j ∈ Finset.univ.erase i,
          ‖K i j‖ * ‖c i‖ * ‖c j‖ := by
    apply Finset.sum_congr rfl
    intro i hi
    calc
      ∑ j, g i j * ‖c i‖ * ‖c j‖ =
          g i i * ‖c i‖ * ‖c i‖ +
            ∑ j ∈ Finset.univ.erase i,
              g i j * ‖c i‖ * ‖c j‖ :=
        (Finset.add_sum_erase Finset.univ
          (fun j => g i j * ‖c i‖ * ‖c j‖)
            (Finset.mem_univ i)).symm
      _ = ∑ j ∈ Finset.univ.erase i,
            g i j * ‖c i‖ * ‖c j‖ := by simp [g]
      _ = ∑ j ∈ Finset.univ.erase i,
          ‖K i j‖ * ‖c i‖ * ‖c j‖ := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [show g i j = ‖K i j‖ by
          simp [g, Ne.symm (Finset.ne_of_mem_erase hj)]]
  have hOnorm : ‖O‖ ≤
      ∑ i, ∑ j ∈ Finset.univ.erase i,
        ‖K i j‖ * ‖c i‖ * ‖c j‖ := by
    dsimp only [O]
    calc
      ‖∑ i, ∑ j ∈ Finset.univ.erase i,
          conj (c i) * c j * K i j‖ ≤
          ∑ i, ‖∑ j ∈ Finset.univ.erase i,
            conj (c i) * c j * K i j‖ := norm_sum_le _ _
      _ ≤ ∑ i, ∑ j ∈ Finset.univ.erase i,
          ‖K i j‖ * ‖c i‖ * ‖c j‖ := by
        apply Finset.sum_le_sum
        intro i hi
        calc
          ‖∑ j ∈ Finset.univ.erase i,
              conj (c i) * c j * K i j‖ ≤
              ∑ j ∈ Finset.univ.erase i,
                ‖conj (c i) * c j * K i j‖ := norm_sum_le _ _
          _ = ∑ j ∈ Finset.univ.erase i,
              ‖K i j‖ * ‖c i‖ * ‖c j‖ := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [norm_mul, norm_mul, RCLike.norm_conj]
            ring
  have hOR : ‖O‖ ≤ R * E := by
    exact hOnorm.trans (hquadg ▸ hschur)
  have hsplit :
      (∑ i, ∑ j, conj (c i) * c j * K i j) =
        (D * E : ℝ) + O := by
    calc
      (∑ i, ∑ j, conj (c i) * c j * K i j) =
          ∑ i, (conj (c i) * c i * K i i +
            ∑ j ∈ Finset.univ.erase i,
              conj (c i) * c j * K i j) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.add_sum_erase Finset.univ
          (fun j => conj (c i) * c j * K i j) (Finset.mem_univ i)]
      _ = (∑ i, conj (c i) * c i * K i i) + O := by
        rw [Finset.sum_add_distrib]
      _ = (D * E : ℝ) + O := by
        congr 1
        dsimp only [E]
        push_cast
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [hdiag, ← Complex.normSq_eq_conj_mul_self,
          Complex.normSq_eq_norm_sq]
        push_cast
        ring
  have hOreal : -R * E ≤ O.re := by
    calc
      -R * E = -(R * E) := by ring
      _ ≤ -‖O‖ := neg_le_neg hOR
      _ ≤ O.re := (abs_le.mp (Complex.abs_re_le_norm O)).1
  rw [hsplit]
  simp only [Complex.add_re, Complex.ofReal_re]
  dsimp only [E] at hOreal ⊢
  linarith

/-- Explicit positive floor produced by the cosine-window finite Ingham
argument. -/
def cosineInghamFloorFactor (a d : ℝ) : ℝ :=
  (4 * a / Real.pi) * (1 - (2 * a * d)⁻¹ ^ 2)

/-- The cosine-window floor is positive precisely in the strict separation
regime needed by the endpoint squeeze. -/
theorem cosineInghamFloorFactor_pos
    {a d : ℝ} (ha : 0 < a) (had : 1 < 2 * a * d) :
    0 < cosineInghamFloorFactor a d := by
  unfold cosineInghamFloorFactor
  apply mul_pos (by positivity)
  have hq : 0 < 2 * a * d := zero_lt_one.trans had
  have hinv : (2 * a * d)⁻¹ < 1 := by
    rw [inv_lt_one₀ hq]
    exact had
  have hinv0 : 0 ≤ (2 * a * d)⁻¹ := inv_nonneg.mpr hq.le
  nlinarith [sq_nonneg ((2 * a * d)⁻¹)]

/-- Fully proved finite Ingham inequality at the exact strict threshold
`2ad > 1`, obtained from the cosine taper and telescoping shell bound. -/
theorem finite_cosineIngham
    {a d : ℝ} (ha : 0 < a) (had : 1 < 2 * a * d)
    {n : ℕ} (x : Fin n → ℝ) (hsep : PairwiseFrequencySeparated x d)
    (c : Fin n → ℂ) :
    cosineInghamFloorFactor a d * ∑ i, ‖c i‖ ^ 2 ≤
      ∫ η : ℝ in Set.Icc (-a) a,
        ‖gramFourierPolynomial x c η‖ ^ 2 := by
  let q : ℝ := 2 * a * d
  let D : ℝ := 4 * a / Real.pi
  let R : ℝ := D * q⁻¹ ^ 2
  let K : Fin n → Fin n → ℂ := fun i j =>
    cosineWindowKernel a (x j - x i)
  have hscaled (i j : Fin n) (hij : i ≠ j) :
      q ≤ |2 * a * (x j - x i)| := by
    have ha2 : 0 ≤ 2 * a := by positivity
    calc
      q = (2 * a) * d := by rfl
      _ ≤ (2 * a) * |x j - x i| := by
        apply mul_le_mul_of_nonneg_left _ ha2
        simpa only [abs_sub_comm] using hsep i j hij
      _ = |2 * a * (x j - x i)| := by
        rw [abs_mul, abs_of_nonneg ha2]
  have hq : 1 < q := by exact had
  have hdiag (i : Fin n) : K i i = (D : ℂ) := by
    dsimp only [K, D]
    simpa using cosineWindowKernel_zero ha
  have hsymm (i j : Fin n) : ‖K i j‖ = ‖K j i‖ := by
    by_cases hij : i = j
    · subst j
      rfl
    · have hfar : 1 < |2 * a * (x j - x i)| :=
        hq.trans_le (hscaled i j hij)
      dsimp only [K]
      rw [show x i - x j = -(x j - x i) by ring,
        cosineWindowKernel_neg_of_far ha hfar]
  have hrow (i : Fin n) :
      ∑ j ∈ Finset.univ.erase i, ‖K i j‖ ≤ R := by
    dsimp only [K, R, D]
    exact sum_norm_cosineWindowKernel_offdiag_le Finset.univ x ha hq
      (fun i hi j hj hij => hscaled i j hij) i (Finset.mem_univ i)
  have hlower := finite_kernel_quadratic_re_ge_of_offdiag_row
    K c D R hdiag hsymm hrow
  have hfactor : D - R = cosineInghamFloorFactor a d := by
    dsimp only [D, R, q]
    unfold cosineInghamFloorFactor
    ring
  rw [hfactor] at hlower
  calc
    cosineInghamFloorFactor a d * ∑ i, ‖c i‖ ^ 2 ≤
        (∑ i, ∑ j, conj (c i) * c j *
          cosineWindowKernel a (x j - x i)).re := by
      simpa only [K] using hlower
    _ = ∫ η : ℝ in Set.Icc (-a) a,
        cosineInghamWeight a η *
          ‖gramFourierPolynomial x c η‖ ^ 2 :=
      (integral_cosineWeight_mul_norm_sq_eq_kernel_re x c a).symm
    _ ≤ ∫ η : ℝ in Set.Icc (-a) a,
        ‖gramFourierPolynomial x c η‖ ^ 2 :=
      integral_cosineWeight_mul_norm_sq_le x c a

/-- Separation now supplies the universal Gram lower bound with no unproved
Ingham premise. -/
theorem universalGramKernel_lowerBound_of_separated
    {a d : ℝ} (ha : 0 < a) (had : 1 < 2 * a * d)
    {m n : ℕ} (hm : 1 ≤ m) (x : Fin n → ℝ) (c : Fin n → ℂ)
    (hsep : PairwiseFrequencySeparated x d) :
    2 * gramNormalization m * cosineInghamFloorFactor a d *
        (1 + 4 * a ^ 2)⁻¹ ^ (2 * m) * ∑ i, ‖c i‖ ^ 2 ≤
      (∑ i, ∑ j, conj (c i) * c j *
        universalGramKernel m (x j - x i)).re := by
  apply universalGramKernel_lowerBound_of_windowFloor hm x c a
    (cosineInghamFloorFactor a d)
  exact finite_cosineIngham ha had x hsep c

/-- Explicit universal-Gram lower constant delivered by the cosine-window
argument. -/
def universalGramLowerConstant (m : ℕ) (a d : ℝ) : ℝ :=
  2 * gramNormalization m * cosineInghamFloorFactor a d *
    (1 + 4 * a ^ 2)⁻¹ ^ (2 * m)

theorem universalGramLowerConstant_pos
    {m : ℕ} (hm : 1 ≤ m) {a d : ℝ}
    (ha : 0 < a) (had : 1 < 2 * a * d) :
    0 < universalGramLowerConstant m a d := by
  unfold universalGramLowerConstant
  exact mul_pos
    (mul_pos
      (mul_pos (by positivity) (gramNormalization_pos hm))
      (cosineInghamFloorFactor_pos ha had))
    (pow_pos (by positivity) _)

/-- Reindexed finite-type form of the universal Gram lower bound. -/
theorem universalGramKernel_quadratic_re_ge_of_finite_separated
    {ι : Type*} [Fintype ι] {a d : ℝ} (ha : 0 < a)
    (had : 1 < 2 * a * d) {m : ℕ} (hm : 1 ≤ m)
    (x : ι → ℝ) (hsep : ∀ i j, i ≠ j → d ≤ |x i - x j|)
    (c : ι → ℂ) :
    universalGramLowerConstant m a d * ∑ i, ‖c i‖ ^ 2 ≤
      (∑ i, ∑ j, conj (c i) * c j *
        universalGramKernel m (x j - x i)).re := by
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let x' : Fin (Fintype.card ι) → ℝ := fun i => x (e.symm i)
  let c' : Fin (Fintype.card ι) → ℂ := fun i => c (e.symm i)
  have hsep' : PairwiseFrequencySeparated x' d := by
    intro i j hij
    apply hsep
    exact e.symm.injective.ne hij
  have hfin := universalGramKernel_lowerBound_of_separated
    ha had hm x' c' hsep'
  dsimp only [x', c'] at hfin
  have hQ :
      (∑ i : Fin (Fintype.card ι),
          ∑ j : Fin (Fintype.card ι),
            conj (c (e.symm i)) * c (e.symm j) *
              universalGramKernel m (x (e.symm j) - x (e.symm i))) =
        ∑ i : ι, ∑ j : ι,
          conj (c i) * c j * universalGramKernel m (x j - x i) := by
    calc
      (∑ i : Fin (Fintype.card ι),
          ∑ j : Fin (Fintype.card ι),
            conj (c (e.symm i)) * c (e.symm j) *
              universalGramKernel m (x (e.symm j) - x (e.symm i))) =
          ∑ i : Fin (Fintype.card ι), ∑ j : ι,
            conj (c (e.symm i)) * c j *
              universalGramKernel m (x j - x (e.symm i)) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact e.symm.sum_comp (fun j : ι =>
          conj (c (e.symm i)) * c j *
            universalGramKernel m (x j - x (e.symm i)))
      _ = ∑ i : ι, ∑ j : ι,
          conj (c i) * c j * universalGramKernel m (x j - x i) :=
        e.symm.sum_comp (fun i : ι => ∑ j : ι,
          conj (c i) * c j * universalGramKernel m (x j - x i))
  have hE :
      (∑ i : Fin (Fintype.card ι), ‖c (e.symm i)‖ ^ 2) =
        ∑ i : ι, ‖c i‖ ^ 2 :=
    e.symm.sum_comp (fun i : ι => ‖c i‖ ^ 2)
  unfold universalGramLowerConstant
  rw [hQ, hE] at hfin
  exact hfin

end
end MeyerGeneralProblem
