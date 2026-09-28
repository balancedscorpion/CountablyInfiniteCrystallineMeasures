module

public import MeyerGeneralProblem.Carrier.UniformDensity
public import MeyerGeneralProblem.Carrier.SignedSquareCarrier
public import Mathlib.Order.Filter.AtTopBot.Field
import all Mathlib.Order.Filter.AtTopBot.Field

@[expose] public section

/-!
Exact positive dilation of actual extensional carriers and their numerical
uniform density. Counts include every translated half-open window. No density
value, asymptotic count, or density certificate is assumed.
-/
namespace MeyerGeneralProblem
open Filter
noncomputable section
namespace LocallyFiniteCarrier

/-- The actual positive scalar image remains locally finite. -/
def dilate (S : LocallyFiniteCarrier) (c : ℝ) (hc : 0 < c) : LocallyFiniteCarrier where
  carrier := (fun x => c * x) '' S.carrier
  finite_inter_Icc a b := by
    apply ((S.finite_inter_Icc (a / c) (b / c)).image (fun x => c * x)).subset
    rintro y ⟨⟨x, hx, rfl⟩, hlo, hhi⟩
    refine ⟨x, ⟨hx, ?_, ?_⟩, rfl⟩
    · exact (div_le_iff₀ hc).2 (by simpa [mul_comm] using hlo)
    · exact (le_div_iff₀ hc).2 (by simpa [mul_comm] using hhi)

@[simp] theorem dilate_carrier (S : LocallyFiniteCarrier) (c : ℝ) (hc : 0 < c) :
    (S.dilate c hc).carrier = (fun x => c * x) '' S.carrier := rfl

/-- The window identity includes arbitrary translations and all real lengths.
The positive scale preserves both half-open edge conventions exactly. -/
theorem dilate_window_set (S : LocallyFiniteCarrier) (c : ℝ) (hc : 0 < c) (a L : ℝ) :
    (S.dilate c hc).carrier ∩ Set.Ico a (a + L) =
      (fun x => c * x) '' (S.carrier ∩ Set.Ico (a / c) (a / c + L / c)) := by
  ext y
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hlo, hhi⟩
    refine ⟨x, ⟨hx, ?_, ?_⟩, rfl⟩
    · exact (div_le_iff₀ hc).2 (by simpa [mul_comm] using hlo)
    · rw [← add_div]
      exact (lt_div_iff₀ hc).2 (by simpa [mul_comm] using hhi)
  · rintro ⟨x, ⟨hx, hlo, hhi⟩, rfl⟩
    refine ⟨⟨x, hx, rfl⟩, ?_, ?_⟩
    · simpa [mul_comm] using (div_le_iff₀ hc).1 hlo
    · rw [← add_div] at hhi
      simpa [mul_comm] using (lt_div_iff₀ hc).1 hhi

/-- Actual window counts are preserved by the positive dilation bijection. -/
theorem windowCount_dilate (S : LocallyFiniteCarrier) (c : ℝ) (hc : 0 < c) (a L : ℝ) :
    windowCount (S.dilate c hc) a L = windowCount S (a / c) (L / c) := by
  unfold windowCount
  rw [S.dilate_window_set c hc a L]
  exact Set.ncard_image_of_injective _ (mul_right_injective₀ hc.ne')

/-- The numerical upper profile scales exactly, including its infinite values.
The all-translation supremum is reindexed by a surjective real dilation. -/
theorem upperUniformDensityProfile_dilate
    (S : LocallyFiniteCarrier) (c : ℝ) (hc : 0 < c) {L : ℝ} (hL : 0 < L) :
    upperUniformDensityProfile (S.dilate c hc) L =
      upperUniformDensityProfile S (L / c) / ENNReal.ofReal c := by
  rw [(S.dilate c hc).upperUniformDensityProfile_of_pos hL,
    S.upperUniformDensityProfile_of_pos (div_pos hL hc), ENNReal.iSup_div]
  simp_rw [S.windowCount_dilate c hc]
  have hratio (n : ℕ) : (n : ENNReal) / ENNReal.ofReal L =
      ((n : ENNReal) / ENNReal.ofReal (L / c)) / ENNReal.ofReal c := by
    rw [← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_div_of_pos hL,
      ← ENNReal.ofReal_div_of_pos (div_pos hL hc),
      ← ENNReal.ofReal_div_of_pos hc]
    congr 1
    field_simp
  simp_rw [hratio]
  have hsurj : Function.Surjective (fun a : ℝ => a / c) := by
    intro b
    exact ⟨b * c, mul_div_cancel_right₀ b hc.ne'⟩
  exact hsurj.iSup_comp (fun a : ℝ =>
    ((windowCount S a (L / c) : ENNReal) / ENNReal.ofReal (L / c)) / ENNReal.ofReal c)

/-- Exact numerical density dilation. The positive length reparameterization
maps `atTop` onto itself, so no subsequence or pointwise asymptotic is substituted. -/
theorem upperUniformBeurlingDensity_dilate
    (S : LocallyFiniteCarrier) (c : ℝ) (hc : 0 < c) :
    upperUniformBeurlingDensity (S.dilate c hc) =
      upperUniformBeurlingDensity S / ENNReal.ofReal c := by
  unfold upperUniformBeurlingDensity
  have hprof : upperUniformDensityProfile (S.dilate c hc) =ᶠ[atTop]
      (fun L : ℝ => upperUniformDensityProfile S (L / c) / ENNReal.ofReal c) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
    exact S.upperUniformDensityProfile_dilate c hc hL
  rw [Filter.limsup_congr hprof]
  change Filter.limsup (fun L : ℝ => upperUniformDensityProfile S (L / c) *
    (ENNReal.ofReal c)⁻¹) atTop =
    Filter.limsup (upperUniformDensityProfile S) atTop * (ENNReal.ofReal c)⁻¹
  rw [ENNReal.limsup_mul_const_of_ne_top
    (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hc).ne')]
  have hlim : Filter.limsup (fun L : ℝ => upperUniformDensityProfile S (L / c)) atTop =
      Filter.limsup (upperUniformDensityProfile S) atTop := by
    change Filter.limsup (upperUniformDensityProfile S ∘ (fun L : ℝ => L / c)) atTop = _
    rw [Filter.limsup_comp, Filter.map_div_atTop_eq c hc]
  rw [hlim, mul_comm]

end LocallyFiniteCarrier

/-- The actual signed-square coordinate acquires the square of a positive scale. -/
theorem signedSquare_positive_mul (h : ℝ) (hh : 0 < h) (x : ℝ) :
    signedSquare (h * x) = h ^ 2 * signedSquare x := by
  simp only [signedSquare, abs_mul, abs_of_pos hh]
  ring

namespace LocallyFiniteCarrier

/-- Positive dilation commutes with signed-square images with the exact `h²`
factor, as an equality of actual locally finite carriers. -/
theorem signedSquareImage_dilate
    (S : LocallyFiniteCarrier) (h : ℝ) (hh : 0 < h) :
    (S.dilate h hh).signedSquareImage =
      S.signedSquareImage.dilate (h ^ 2) (sq_pos_of_pos hh) := by
  apply LocallyFiniteCarrier.ext
  simp only [signedSquareImage_carrier, dilate_carrier, ← Set.image_comp]
  congr 1
  funext x
  exact signedSquare_positive_mul h hh x

/-- Exact signed-square density scaling for actual carrier dilations. -/
theorem upperUniformBeurlingDensity_signedSquare_dilate
    (S : LocallyFiniteCarrier) (h : ℝ) (hh : 0 < h) :
    upperUniformBeurlingDensity (S.dilate h hh).signedSquareImage =
      upperUniformBeurlingDensity S.signedSquareImage / ENNReal.ofReal (h ^ 2) := by
  rw [S.signedSquareImage_dilate h hh,
    S.signedSquareImage.upperUniformBeurlingDensity_dilate (h ^ 2) (sq_pos_of_pos hh)]

end LocallyFiniteCarrier

#print axioms LocallyFiniteCarrier.dilate_window_set
#print axioms LocallyFiniteCarrier.windowCount_dilate
#print axioms LocallyFiniteCarrier.upperUniformDensityProfile_dilate
#print axioms LocallyFiniteCarrier.upperUniformBeurlingDensity_dilate
#print axioms LocallyFiniteCarrier.signedSquareImage_dilate
#print axioms LocallyFiniteCarrier.upperUniformBeurlingDensity_signedSquare_dilate
end
end MeyerGeneralProblem
