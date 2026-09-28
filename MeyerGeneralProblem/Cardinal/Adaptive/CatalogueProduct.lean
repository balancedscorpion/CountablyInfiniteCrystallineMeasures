module

public import MeyerGeneralProblem.Cardinal.Adaptive.CatalogueExtraction
public import MeyerGeneralProblem.Cardinal.Adaptive.ReciprocalAnnihilatorProduct
public import MeyerGeneralProblem.Cardinal.Adaptive.CatalogueTailBudget

@[expose] public section

/-! Reindex the literal reciprocal Fourier product by the exact geometric catalogue. -/
namespace MeyerGeneralProblem.Adaptive
noncomputable section
open Classical
open scoped FourierTransform

/-- The two signed coordinates are exactly the two arms of the actual product. -/
def catalogueProductIndex (M : ℕ) : (Fin M × ReciprocalSign) ≃ Fin (M+M) where
  toFun d := match d.2 with
    | .forward => d.1.castAdd M
    | .reciprocal => d.1.natAdd M
  invFun := Fin.addCases (fun i => (i,.forward)) (fun i => (i,.reciprocal))
  left_inv := by rintro ⟨i,sign⟩; cases sign <;> simp only [Fin.addCases_left,Fin.addCases_right]
  right_inv := by
    intro j
    induction j using Fin.addCases <;> simp only [Fin.addCases_left,Fin.addCases_right]

/-- Literal identification of each signed catalogue coefficient with the corresponding product factor. -/
theorem catalogueProduct_coefficient (R : ℕ+ → ℕ) (hR : ∀ i, 1 ≤ R i)
    {M : ℕ} (d : Fin M × ReciprocalSign) (l : ℤ) :
    periodicCoefficient
      (reciprocalProductFunctions M (fun i => i.val+1) (fun i => R (prefixScaleIndex i))
        (fun _ => Nat.succ_pos _) (fun _ => hR _) (catalogueProductIndex M d))
      (reciprocalProductFunctions_smooth M (fun i => i.val+1) (fun i => R (prefixScaleIndex i))
        (fun _ => Nat.succ_pos _) (fun _ => hR _) (catalogueProductIndex M d)) l =
      cataloguePhaseCoefficient R hR d l := by
  rcases d with ⟨i,sign⟩
  cases sign <;> simp only [catalogueProductIndex,Equiv.coe_fn_mk,reciprocalProductFunctions,
    Fin.addCases_left,Fin.addCases_right,cataloguePhaseCoefficient,phaseCoefficient,prefixScaleIndex] <;> rfl

/-- Literal identification of both signed physical frequencies. -/
theorem catalogueProduct_scale (s : ℕ+ → ℝ) {M : ℕ} (d : Fin M × ReciprocalSign) :
    reciprocalProductScales M (fun i => s (prefixScaleIndex i)) (catalogueProductIndex M d) =
      labelScale s (prefixScaleIndex d.1,d.2) := by
  rcases d with ⟨i,sign⟩
  cases sign <;> simp only [catalogueProductIndex,Equiv.coe_fn_mk,reciprocalProductScales,
    Fin.addCases_left,Fin.addCases_right,labelScale]

/-- Reindex an actual Fourier tuple by its generating signed coordinates. -/
def catalogueProductTuple (M : ℕ) : (Fin (M+M) → ℤ) ≃ (Fin M × ReciprocalSign → ℤ) where
  toFun k d := k (catalogueProductIndex M d)
  invFun k j := k ((catalogueProductIndex M).symm j)
  left_inv := by intro k; funext j; simp
  right_inv := by intro k; funext d; simp

/-- The actual whole product frequency is the exact Laurent catalogue shift. -/
theorem catalogueProduct_frequency (s : ℕ+ → ℝ) {M : ℕ} (k : Fin (M+M) → ℤ) :
    (∑ j, reciprocalProductScales M (fun i => s (prefixScaleIndex i)) j*(k j:ℝ)) =
      catalogueShift (catalogueProductTuple M k) s := by
  rw [← (catalogueProductIndex M).sum_comp]
  simp only [catalogueProduct_scale]
  unfold catalogueShift reciprocalLaurentValue
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i hi
  simp [show (Finset.univ : Finset ReciprocalSign) = {.forward,.reciprocal} from rfl,
    labelScale,catalogueProductTuple,catalogueProductIndex,mul_comm]


/-- The actual coefficient product is exactly the geometric catalogue coefficient product. -/
theorem catalogueProduct_coefficients (R : ℕ+ → ℕ) (hR : ∀ i, 1 ≤ R i)
    {M : ℕ} (k : Fin (M+M) → ℤ) :
    (∏ j, periodicCoefficient
      (reciprocalProductFunctions M (fun i => i.val+1) (fun i => R (prefixScaleIndex i))
        (fun _ => Nat.succ_pos _) (fun _ => hR _) j)
      (reciprocalProductFunctions_smooth M (fun i => i.val+1) (fun i => R (prefixScaleIndex i))
        (fun _ => Nat.succ_pos _) (fun _ => hR _) j) (k j)) =
      ∏ d, cataloguePhaseCoefficient R hR d (catalogueProductTuple M k d) := by
  rw [← (catalogueProductIndex M).prod_comp]
  apply Finset.prod_congr rfl
  intro d hd
  exact catalogueProduct_coefficient R hR d _

/-- The total-frequency norm is preserved exactly by the index equivalence. -/
theorem catalogueProduct_l1 {M : ℕ} (k : Fin (M+M) → ℤ) :
    (∑ j, |(k j:ℝ)|) = ∑ d, |(catalogueProductTuple M k d:ℝ)| :=
  ((catalogueProductIndex M).sum_comp (fun j => |(k j:ℝ)|)).symm


/-- Exact full actual reciprocal product series in the signed catalogue coordinates.
The sum retains every integer tuple. -/
theorem catalogueProduct_fourier_hasSum (R : ℕ+ → ℕ) (hR : ∀ i, 1 ≤ R i)
    (s : ℕ+ → ℝ) (hs : ∀ i, s i ∈ Set.Icc 1 2) (M p : ℕ)
    (T : HermiteScale (-(p:ℤ))) :
    HasSum (fun k : Fin M × ReciprocalSign → ℤ =>
      (∏ d, cataloguePhaseCoefficient R hR d (k d)) •
        combDistributionTranslation (catalogueShift k s) (𝓕 (hermiteScaleDistribution p T)))
      (𝓕 (TemperedDistribution.smulLeftCLM ℂ
        (reciprocalAnnihilatorProduct M (fun i => i.val+1) (fun i => R (prefixScaleIndex i))
          (fun _ => Nat.succ_pos _) (fun _ => hR _) (fun i => s (prefixScaleIndex i)))
        (hermiteScaleDistribution p T))) := by
  apply (catalogueProductTuple M).hasSum_iff.mp
  have h := reciprocalAnnihilatorProduct_fourier_hasSum M p (fun i => i.val+1)
    (fun i => R (prefixScaleIndex i)) (fun _ => Nat.succ_pos _) (fun _ => hR _)
    (fun i => s (prefixScaleIndex i)) (fun i => hs _) T
  simpa only [Function.comp_def,catalogueProduct_coefficients,catalogueProduct_frequency] using h


/-- The analytic product cutoff in its original finite-index coordinates. -/
def productL1Cutoff (M L : ℕ) : Finset (Fin (M+M) → ℤ) :=
  (catalogueL1Cutoff M L).map (catalogueProductTuple M).symm.toEmbedding

/-- The analytic cutoff contains exactly all tuples of total frequency at most L. -/
theorem mem_productL1Cutoff {M L : ℕ} (k : Fin (M+M) → ℤ) :
    k ∈ productL1Cutoff M L ↔ ∑ j, |(k j:ℝ)| ≤ L := by
  rw [productL1Cutoff,Finset.mem_map_equiv,mem_catalogueL1Cutoff,Equiv.symm_symm,← catalogueProduct_l1]

/-- Finite cutoff sums reindex exactly, retaining all actual tuple multiplicities. -/
theorem productL1Cutoff_sum {M L : ℕ} (f : (Fin (M+M) → ℤ) → ℂ) :
    (∑ k ∈ productL1Cutoff M L, f k) =
      ∑ k ∈ catalogueL1Cutoff M L, f ((catalogueProductTuple M).symm k) := by
  exact Finset.sum_map _ _ _


/-- The full whole-distribution sum splits into exactly the finite catalogue
and every omitted tuple of total frequency greater than L. -/
theorem catalogueProduct_full_split (R : ℕ+ → ℕ) (hR : ∀ i, 1 ≤ R i)
    (s : ℕ+ → ℝ) (hs : ∀ i, s i ∈ Set.Icc 1 2) (M p L : ℕ)
    (T : HermiteScale (-(p:ℤ))) :
    (∑ k ∈ catalogueL1Cutoff M L, (∏ d, cataloguePhaseCoefficient R hR d (k d)) •
      combDistributionTranslation (catalogueShift k s) (𝓕 (hermiteScaleDistribution p T))) +
    (∑' k : {k : Fin M × ReciprocalSign → ℤ // (L:ℝ) < ∑ d, |(k d:ℝ)|},
      (∏ d, cataloguePhaseCoefficient R hR d (k.val d)) •
        combDistributionTranslation (catalogueShift k.val s) (𝓕 (hermiteScaleDistribution p T))) =
    (𝓕 (TemperedDistribution.smulLeftCLM ℂ
      (reciprocalAnnihilatorProduct M (fun i => i.val+1) (fun i => R (prefixScaleIndex i))
        (fun _ => Nat.succ_pos _) (fun _ => hR _) (fun i => s (prefixScaleIndex i)))
      (hermiteScaleDistribution p T))) := by
  have h := catalogueProduct_fourier_hasSum R hR s hs M p T
  rw [← h.tsum_eq]
  convert! h.summable.sum_add_tsum_compl (s := catalogueL1Cutoff M L) using 1
  apply congrArg _
  exact tsum_congr_subtype
    (fun k : Fin M × ReciprocalSign → ℤ =>
      ((∏ d, cataloguePhaseCoefficient R hR d (k d)) •
        combDistributionTranslation (catalogueShift k s) (𝓕 (hermiteScaleDistribution p T)) :
          TemperedDistribution ℝ ℂ))
    (fun k => by simp only [Set.mem_compl_iff,Finset.mem_coe,mem_catalogueL1Cutoff,not_le])


/-- Exact reindexing of every omitted tuple; the strict total-frequency boundary is preserved. -/
def catalogueProductTailIndex (M L : ℕ) :
    {k : Fin (M+M) → ℤ // (L:ℝ) < ∑ j, |(k j:ℝ)|} ≃
    {k : Fin M × ReciprocalSign → ℤ // (L:ℝ) < ∑ d, |(k d:ℝ)|} where
  toFun k := ⟨catalogueProductTuple M k.val,by rw [← catalogueProduct_l1]; exact k.property⟩
  invFun k := ⟨(catalogueProductTuple M).symm k.val,by
    rw [catalogueProduct_l1,Equiv.apply_symm_apply]; exact k.property⟩
  left_inv := by intro k; apply Subtype.ext; exact (catalogueProductTuple M).symm_apply_apply k.val
  right_inv := by intro k; apply Subtype.ext; exact (catalogueProductTuple M).apply_symm_apply k.val

/-- The complete omitted signed catalogue sum is represented by the actual
original-order native tail operator used by the deterministic stage budget. -/
theorem catalogueProduct_tail_realizes (R : ℕ+ → ℕ) (hR : ∀ i, 1 ≤ R i)
    (s : ℕ+ → ℝ) (hs : ∀ i, s i ∈ Set.Icc 1 2) (M p L : ℕ)
    (T : HermiteScale (-(p:ℤ))) :
    hermiteScaleDistribution p
      (fourierTranslationTail (M+M) p
        (fun j => periodicCoefficient
          (reciprocalProductFunctions M (fun i => i.val+1) (fun i => R (prefixScaleIndex i))
            (fun _ => Nat.succ_pos _) (fun _ => hR _) j)
          (reciprocalProductFunctions_smooth M (fun i => i.val+1) (fun i => R (prefixScaleIndex i))
            (fun _ => Nat.succ_pos _) (fun _ => hR _) j))
        (reciprocalProductScales M (fun i => s (prefixScaleIndex i))) L
        (hermiteFourier (-(p:ℤ)) T)) =
    ∑' k : {k : Fin M × ReciprocalSign → ℤ // (L:ℝ) < ∑ d, |(k d:ℝ)|},
      (∏ d, cataloguePhaseCoefficient R hR d (k.val d)) •
        combDistributionTranslation (catalogueShift k.val s) (𝓕 (hermiteScaleDistribution p T)) := by
  rw [fourierTranslationTail_realizes (M+M) p L _
    (fun j => periodicCoefficient_all_moments _ _ (2*p)) _
    (reciprocalProductScales_bound M _ (fun i => hs _))]
  rw [hermiteFourier_represents_distributionalFourier]
  have he := (catalogueProductTailIndex M L).tsum_eq
    (fun k => ((∏ d, cataloguePhaseCoefficient R hR d (k.val d)) •
      combDistributionTranslation (catalogueShift k.val s) (𝓕 (hermiteScaleDistribution p T)) :
        TemperedDistribution ℝ ℂ))
  simpa only [catalogueProductTailIndex,Equiv.coe_fn_mk,
    catalogueProduct_coefficients,catalogueProduct_frequency] using he

end
end MeyerGeneralProblem.Adaptive
