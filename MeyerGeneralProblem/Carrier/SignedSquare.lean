module

public import MeyerGeneralProblem.Carrier.StrictSubcritical

@[expose] public section

/-!
# Signed-square coordinates

The change of variables `s = x |x|` converts the subcritical density inequality
into uniform tail separation. Elementary lemmas are kept explicit so that the
negative-tail ratio split cannot be hidden in an asymptotic assertion.
-/

namespace MeyerGeneralProblem

/-- The odd, strictly increasing signed-square coordinate. -/
def signedSquare (x : ℝ) : ℝ := x * |x|

@[simp]
theorem signedSquare_zero : signedSquare 0 = 0 := by simp [signedSquare]

@[simp]
theorem signedSquare_neg (x : ℝ) : signedSquare (-x) = -signedSquare x := by
  simp [signedSquare]

@[simp]
theorem abs_signedSquare (x : ℝ) : |signedSquare x| = |x| ^ 2 := by
  unfold signedSquare
  rw [abs_mul, abs_abs]
  ring

theorem signedSquare_of_nonneg {x : ℝ} (hx : 0 ≤ x) : signedSquare x = x ^ 2 := by
  rw [signedSquare, abs_of_nonneg hx]
  ring

theorem signedSquare_of_nonpos {x : ℝ} (hx : x ≤ 0) : signedSquare x = -(x ^ 2) := by
  rw [signedSquare, abs_of_nonpos hx]
  ring

theorem signedSquare_strictMono : StrictMono signedSquare := by
  intro x y hxy
  by_cases hx : 0 ≤ x
  · have hy : 0 ≤ y := le_trans hx hxy.le
    rw [signedSquare_of_nonneg hx, signedSquare_of_nonneg hy]
    nlinarith
  · have hx' : x < 0 := lt_of_not_ge hx
    by_cases hy : y ≤ 0
    · rw [signedSquare_of_nonpos hx'.le, signedSquare_of_nonpos hy]
      nlinarith
    · have hy' : 0 < y := lt_of_not_ge hy
      rw [signedSquare_of_nonpos hx'.le, signedSquare_of_nonneg hy'.le]
      nlinarith

/-- Same-sign signed-square increments factor into the ordinary gap and sum of magnitudes. -/
theorem signedSquare_sub_eq_gap_mul_abs_add {x y : ℝ}
    (hxy : x ≤ y) (hsign : y ≤ 0 ∨ 0 ≤ x) :
    signedSquare y - signedSquare x = (y - x) * (|x| + |y|) := by
  rcases hsign with hy | hx
  · have hx' : x ≤ 0 := le_trans hxy hy
    rw [signedSquare_of_nonpos hx', signedSquare_of_nonpos hy,
      abs_of_nonpos hx', abs_of_nonpos hy]
    ring
  · have hy : 0 ≤ y := le_trans hx hxy
    rw [signedSquare_of_nonneg hx, signedSquare_of_nonneg hy,
      abs_of_nonneg hx, abs_of_nonneg hy]
    ring

/-- On a same-sign pair, the sum coordinate has magnitude equal to the sum
of magnitudes.  The squared form avoids choosing the common sign. -/
theorem add_sq_eq_abs_add_sq_of_mul_nonneg
    {x y : ℝ} (hxy : 0 ≤ x * y) :
    (x + y) ^ 2 = (|x| + |y|) ^ 2 := by
  rcases mul_nonneg_iff.mp hxy with hsign | hsign
  · rw [abs_of_nonneg hsign.1, abs_of_nonneg hsign.2]
  · rw [abs_of_nonpos hsign.1, abs_of_nonpos hsign.2]
    ring

/-- On a same-sign pair, squared signed-square displacement is ordinary
squared displacement times the squared sum of magnitudes. -/
theorem signedSquare_sub_sq_eq_sub_sq_mul_abs_add_sq_of_mul_nonneg
    {x y : ℝ} (hxy : 0 ≤ x * y) :
    (signedSquare y - signedSquare x) ^ 2 =
      (y - x) ^ 2 * (|x| + |y|) ^ 2 := by
  rcases mul_nonneg_iff.mp hxy with hsign | hsign
  · rw [signedSquare_of_nonneg hsign.1,
      signedSquare_of_nonneg hsign.2,
      abs_of_nonneg hsign.1, abs_of_nonneg hsign.2]
    ring
  · rw [signedSquare_of_nonpos hsign.1,
      signedSquare_of_nonpos hsign.2,
      abs_of_nonpos hsign.1, abs_of_nonpos hsign.2]
    ring

/-- On a same-sign pair, absolute signed-square displacement is ordinary
absolute displacement times the sum of magnitudes. -/
theorem abs_signedSquare_sub_eq_abs_sub_mul_abs_add
    {x y : ℝ} (hxy : 0 ≤ x * y) :
    |signedSquare x - signedSquare y| =
      |x - y| * (|x| + |y|) := by
  rcases mul_nonneg_iff.mp hxy with hsign | hsign
  · rcases le_total x y with hle | hle
    · rw [abs_of_nonpos (sub_nonpos.mpr
          (signedSquare_strictMono.monotone hle)),
        abs_of_nonpos (sub_nonpos.mpr hle), neg_sub, neg_sub,
        signedSquare_sub_eq_gap_mul_abs_add hle (Or.inr hsign.1)]
    · rw [abs_of_nonneg (sub_nonneg.mpr
          (signedSquare_strictMono.monotone hle)),
        abs_of_nonneg (sub_nonneg.mpr hle),
        signedSquare_sub_eq_gap_mul_abs_add hle (Or.inr hsign.2)]
      ring
  · rcases le_total x y with hle | hle
    · rw [abs_of_nonpos (sub_nonpos.mpr
          (signedSquare_strictMono.monotone hle)),
        abs_of_nonpos (sub_nonpos.mpr hle), neg_sub, neg_sub,
        signedSquare_sub_eq_gap_mul_abs_add hle (Or.inl hsign.2)]
    · rw [abs_of_nonneg (sub_nonneg.mpr
          (signedSquare_strictMono.monotone hle)),
        abs_of_nonneg (sub_nonneg.mpr hle),
        signedSquare_sub_eq_gap_mul_abs_add hle (Or.inl hsign.1)]
      ring

/-- For arbitrary signs, signed-square displacement is bounded by ordinary
displacement times the sum of magnitudes.  Equality holds on each fixed ray;
opposite signs only improve the estimate. -/
theorem abs_signedSquare_sub_le_abs_sub_mul_abs_add (x y : ℝ) :
    |signedSquare x - signedSquare y| ≤
      |x - y| * (|x| + |y|) := by
  by_cases hxy : 0 ≤ x * y
  · exact (abs_signedSquare_sub_eq_abs_sub_mul_abs_add hxy).le
  · have hneg : x * y < 0 := lt_of_not_ge hxy
    rcases mul_neg_iff.mp hneg with hsign | hsign
    · have hx : 0 < x := hsign.1
      have hy : y < 0 := hsign.2
      rw [signedSquare_of_nonneg hx.le, signedSquare_of_nonpos hy.le,
        abs_of_pos hx, abs_of_neg hy,
        abs_of_pos (by nlinarith [sq_nonneg x, sq_nonneg y] :
          0 < x ^ 2 - -(y ^ 2)),
        abs_of_pos (by linarith : 0 < x - y)]
      nlinarith
    · have hx : x < 0 := hsign.1
      have hy : 0 < y := hsign.2
      rw [signedSquare_of_nonpos hx.le, signedSquare_of_nonneg hy.le,
        abs_of_neg hx, abs_of_pos hy,
        abs_of_neg (by nlinarith [sq_nonneg x, sq_nonneg y] :
          -(x ^ 2) - y ^ 2 < 0),
        abs_of_neg (by linarith : x - y < 0)]
      nlinarith
/-- Two signed-square points that are both far from the origin but remain in
a fixed signed-square band must lie on the same closed ray.  This is the
geometric reduction needed before applying the pair-scale Mehler formula. -/
theorem sameSign_of_signedSquare_large_of_difference_le
    {x y T L : ℝ}
    (hT : L / 2 < T)
    (hx : T ≤ |signedSquare x|)
    (hy : T ≤ |signedSquare y|)
    (hδ : |signedSquare y - signedSquare x| ≤ L) :
    (0 ≤ x ∧ 0 ≤ y) ∨ (x ≤ 0 ∧ y ≤ 0) := by
  rw [abs_signedSquare, sq_abs] at hx hy
  by_cases hx0 : 0 ≤ x
  · by_cases hy0 : 0 ≤ y
    · exact Or.inl ⟨hx0, hy0⟩
    · have hy0' : y ≤ 0 := le_of_not_ge hy0
      rw [signedSquare_of_nonpos hy0', signedSquare_of_nonneg hx0] at hδ
      rw [abs_of_nonpos (by
        nlinarith [sq_nonneg x, sq_nonneg y] : -(y ^ 2) - x ^ 2 ≤ 0)] at hδ
      nlinarith
  · have hx0' : x ≤ 0 := le_of_not_ge hx0
    by_cases hy0 : 0 ≤ y
    · rw [signedSquare_of_nonneg hy0, signedSquare_of_nonpos hx0'] at hδ
      rw [abs_of_nonneg (by
        nlinarith [sq_nonneg x, sq_nonneg y] : 0 ≤ y ^ 2 - -(x ^ 2))] at hδ
      nlinarith
    · exact Or.inr ⟨hx0', le_of_not_ge hy0⟩

/-- On a close negative step, strict subcriticality already gives spacing above one. -/
theorem negative_close_step_separated {x y ε : ℝ}
    (hε : 0 < ε) (hxy : x < y) (hy : y ≤ 0)
    (hsub : 1 / 2 + ε ≤ |x| * (y - x))
    (hclose : y - x ≤ (2 * ε / (1 + 2 * ε)) * |x|) :
    1 + ε ≤ signedSquare y - signedSquare x := by
  have hx : x ≤ 0 := hxy.le.trans hy
  have habsx : |x| = -x := abs_of_nonpos hx
  have habsy : |y| = -y := abs_of_nonpos hy
  rw [signedSquare_sub_eq_gap_mul_abs_add hxy.le (Or.inl hy), habsx, habsy]
  have hden : 0 < 1 + 2 * ε := by positivity
  have hgap : 0 < y - x := sub_pos.mpr hxy
  rw [habsx] at hsub hclose
  have hfactor :
      2 - 2 * ε / (1 + 2 * ε) = (2 + 2 * ε) / (1 + 2 * ε) := by
    field_simp
    ring
  have hcritical : 0 < 1 / 2 + ε := by positivity
  have hprodpos : 0 < (-x) * (y - x) := lt_of_lt_of_le hcritical hsub
  have habsxpos : 0 < -x := by
    rcases mul_pos_iff.mp hprodpos with hpos | hneg
    · exact hpos.1
    · exfalso
      linarith [hneg.2, hgap]
  have hxneg : 0 < -x := habsxpos
  have hmul := mul_le_mul_of_nonneg_left hclose hgap.le
  have hmain :
      (2 - 2 * ε / (1 + 2 * ε)) * ((-x) * (y - x)) ≤
        (y - x) * (-x - y) := by
    nlinarith
  calc
    1 + ε = (2 - 2 * ε / (1 + 2 * ε)) * (1 / 2 + ε) := by
      field_simp
      ring
    _ ≤ (2 - 2 * ε / (1 + 2 * ε)) * ((-x) * (y - x)) := by
      gcongr
      · rw [hfactor]
        positivity
    _ ≤ (y - x) * (-x - y) := hmain

/-- A far negative step is separated because its length is a fixed fraction of
the magnitude of its left endpoint. -/
theorem negative_far_step_separated {x y δ d : ℝ}
    (hxy : x < y) (hy : y ≤ 0) (_hδ : 0 ≤ δ)
    (hfar : δ * |x| ≤ y - x) (hlarge : d ≤ δ * |x| ^ 2) :
    d ≤ signedSquare y - signedSquare x := by
  have hx : x ≤ 0 := hxy.le.trans hy
  have hgap : 0 ≤ y - x := sub_nonneg.mpr hxy.le
  have hgap_le : y - x ≤ |x| := by
    rw [abs_of_nonpos hx]
    linarith
  rw [signedSquare_sub_eq_gap_mul_abs_add hxy.le (Or.inl hy)]
  have habsy : |y| = -y := abs_of_nonpos hy
  have habsx : |x| = -x := abs_of_nonpos hx
  simp only [habsy, habsx] at hfar hlarge ⊢
  have hfactor : -x ≤ -x - y := by linarith
  calc
    d ≤ δ * (-x) ^ 2 := hlarge
    _ = (δ * (-x)) * (-x) := by ring
    _ ≤ (y - x) * (-x) := by
      gcongr
      exact neg_nonneg.mpr hx
    _ ≤ (y - x) * (-x - y) := by
      exact mul_le_mul_of_nonneg_left hfactor hgap

/-- Positive adjacent steps gain the full factor two from the signed-square map. -/
theorem positive_step_separated {x y ε : ℝ}
    (_hε : 0 < ε) (hxy : x < y) (hx : 0 ≤ x)
    (hsub : 1 / 2 + ε ≤ |x| * (y - x)) :
    1 + 2 * ε ≤ signedSquare y - signedSquare x := by
  have hy : 0 ≤ y := hx.trans hxy.le
  rw [signedSquare_sub_eq_gap_mul_abs_add hxy.le (Or.inr hx),
    abs_of_nonneg hx, abs_of_nonneg hy]
  rw [abs_of_nonneg hx] at hsub
  have hgap : 0 ≤ y - x := sub_nonneg.mpr hxy.le
  calc
    1 + 2 * ε = 2 * (1 / 2 + ε) := by ring
    _ ≤ 2 * (x * (y - x)) := by gcongr
    _ ≤ (y - x) * (x + y) := by nlinarith

/-- Nodes of opposite sign and magnitude at least `R` are signed-square separated. -/
theorem opposite_sign_step_separated {x y R d : ℝ}
    (hx : x ≤ -R) (hy : R ≤ y) (hR : 0 ≤ R) (hd : d ≤ R ^ 2) :
    d ≤ signedSquare y - signedSquare x := by
  have hx0 : x ≤ 0 := le_trans hx (neg_nonpos.mpr hR)
  have hy0 : 0 ≤ y := le_trans hR hy
  rw [signedSquare_of_nonneg hy0, signedSquare_of_nonpos hx0]
  have hx_sq : R ^ 2 ≤ x ^ 2 := by nlinarith
  nlinarith [sq_nonneg y]

/-- Strict subcriticality forces uniform separation above the critical value in
signed-square coordinates, after removal of finitely many central indices.

The negative tail is split into close and far adjacent ratios. This is the
quantitative replacement for the invalid shortcut that would merely assert the
ratio tends to one.
-/
theorem strictSubcritical_signedSquare_separated
    {Λ : TwoSidedCarrier} (hΛ : Λ.StrictSubcritical) :
    ∃ d > 1, ∃ F : Finset ℤ, ∀ i j, i ∉ F → j ∉ F → i ≠ j →
      d ≤ |signedSquare (Λ i) - signedSquare (Λ j)| := by
  rcases hΛ with ⟨ε, hε, N, hsub⟩
  let δ : ℝ := 2 * ε / (1 + 2 * ε)
  have hden : 0 < 1 + 2 * ε := by positivity
  have hδ : 0 < δ := div_pos (mul_pos two_pos hε) hden
  have hδle : 0 ≤ δ := hδ.le
  have hδlt : δ < 1 := by
    dsimp [δ]
    rw [div_lt_one hden]
    linarith
  let R : ℝ := (1 + ε) / δ + 1
  have honeε : 0 < 1 + ε := by positivity
  have hR : 0 < R := by
    dsimp [R]
    positivity
  have hRone : 1 < R := by
    dsimp [R]
    have : 0 < (1 + ε) / δ := div_pos honeε hδ
    linarith
  have hδR : 1 + ε < δ * R := by
    calc
      1 + ε = δ * ((1 + ε) / δ) := by field_simp
      _ < δ * R := by
        apply mul_lt_mul_of_pos_left _ hδ
        dsimp [R]
        linarith
  have hlargeR : 1 + ε ≤ δ * R ^ 2 := by
    have hscale : δ * R ≤ δ * R ^ 2 := by
      nlinarith [mul_pos hδ hR, hRone]
    exact hδR.le.trans hscale
  have hRsep : 1 + ε ≤ R ^ 2 := by
    refine hlargeR.trans ?_
    have hRsq : 0 ≤ R ^ 2 := sq_nonneg R
    nlinarith
  rcases Filter.eventually_atBot.mp (Λ.eventually_point_le (-R)) with ⟨A₀, hA₀⟩
  rcases Filter.eventually_atTop.mp (Λ.eventually_point_ge R) with ⟨B₀, hB₀⟩
  let A : ℤ := min A₀ (-((N : ℤ) + 2))
  let B : ℤ := max B₀ ((N : ℤ) + 2)
  have hAB : A ≤ B := by
    dsimp [A, B]
    omega
  have hleftPoint (j : ℤ) (hj : j < A) : Λ j ≤ -R := by
    apply hA₀ j
    dsimp [A] at hj
    omega
  have hrightPoint (j : ℤ) (hj : B < j) : R ≤ Λ j := by
    apply hB₀ j
    dsimp [B] at hj
    omega
  have hleftAbs (j : ℤ) (hj : j < A) : N ≤ Int.natAbs j := by
    rw [← Int.ofNat_le, Int.ofNat_natAbs_of_nonpos (by
      dsimp [A] at hj
      omega)]
    dsimp [A] at hj
    omega
  have hrightAbs (j : ℤ) (hj : B < j) : N ≤ Int.natAbs j := by
    rw [← Int.ofNat_le, Int.natAbs_of_nonneg (by
      dsimp [B] at hj
      omega)]
    dsimp [B] at hj
    omega
  refine ⟨1 + ε, by linarith, Finset.Icc A B, ?_⟩
  intro i j hiF hjF hij
  have hiOutside : i < A ∨ B < i := by
    have hiNot : ¬ (A ≤ i ∧ i ≤ B) := by
      simpa only [Finset.mem_Icc, not_and_or, not_le] using hiF
    omega
  have hjOutside : j < A ∨ B < j := by
    have hjNot : ¬ (A ≤ j ∧ j ≤ B) := by
      simpa only [Finset.mem_Icc, not_and_or, not_le] using hjF
    omega
  have hordered (i j : ℤ) (hi : i < A ∨ B < i) (hj : j < A ∨ B < j)
      (hij' : i < j) :
      1 + ε ≤ signedSquare (Λ j) - signedSquare (Λ i) := by
    rcases hi with hiLeft | hiRight
    · rcases hj with hjLeft | hjRight
      · have hjPrev : j - 1 < A := by omega
        have hprev : Λ (j - 1) < Λ j := Λ.point_lt_point (by omega)
        have hjNonpos : Λ j ≤ 0 :=
          (hleftPoint j hjLeft).trans (neg_nonpos.mpr hR.le)
        have hsubPrev :
            1 / 2 + ε ≤ |Λ (j - 1)| * (Λ j - Λ (j - 1)) := by
          simpa only [sub_add_cancel] using
            hsub (j - 1) (hleftAbs (j - 1) hjPrev)
        have hstep : 1 + ε ≤ signedSquare (Λ j) - signedSquare (Λ (j - 1)) := by
          by_cases hclose :
              Λ j - Λ (j - 1) ≤ δ * |Λ (j - 1)|
          · exact negative_close_step_separated hε hprev hjNonpos hsubPrev hclose
          · apply negative_far_step_separated hprev hjNonpos hδle
              (le_of_not_ge hclose)
            have hmag : R ≤ |Λ (j - 1)| := by
              have hp := hleftPoint (j - 1) hjPrev
              rw [abs_of_nonpos (hp.trans (neg_nonpos.mpr hR.le))]
              linarith
            have hsq : R ^ 2 ≤ |Λ (j - 1)| ^ 2 := by nlinarith
            exact hlargeR.trans (mul_le_mul_of_nonneg_left hsq hδle)
        have hindex : i ≤ j - 1 := by omega
        have hmono : signedSquare (Λ i) ≤ signedSquare (Λ (j - 1)) :=
          signedSquare_strictMono.monotone (Λ.point_le_point hindex)
        linarith
      · exact opposite_sign_step_separated
          (hleftPoint i hiLeft) (hrightPoint j hjRight) hR.le hRsep
    · have hjRight : B < j := by rcases hj with h | h <;> omega
      have hnext : Λ i < Λ (i + 1) := Λ.point_lt_point (by omega)
      have hiNonneg : 0 ≤ Λ i := hR.le.trans (hrightPoint i hiRight)
      have hsubI := hsub i (hrightAbs i hiRight)
      have hstep := positive_step_separated hε hnext hiNonneg hsubI
      have hindex : i + 1 ≤ j := by omega
      have hmono : signedSquare (Λ (i + 1)) ≤ signedSquare (Λ j) :=
        signedSquare_strictMono.monotone (Λ.point_le_point hindex)
      linarith
  rcases lt_or_gt_of_ne hij with hij' | hji'
  · rw [abs_of_nonpos]
    · simpa only [neg_sub] using hordered i j hiOutside hjOutside hij'
    · exact sub_nonpos.mpr (signedSquare_strictMono.monotone
        (Λ.point_le_point hij'.le))
  · rw [abs_of_nonneg]
    · exact hordered j i hjOutside hiOutside hji'
    · exact sub_nonneg.mpr (signedSquare_strictMono.monotone
        (Λ.point_le_point hji'.le))

/-- After deleting the finite central exceptional set, every unit interval in
signed-square coordinates contains at most one carrier index.  This is the
bounded-geometry consequence used by later Schur estimates. -/
theorem strictSubcritical_signedSquare_unitInterval_encard
    {Λ : TwoSidedCarrier} (hΛ : Λ.StrictSubcritical) :
    ∃ F : Finset ℤ, ∀ a : ℝ,
      {j : ℤ | j ∉ F ∧ signedSquare (Λ j) ∈ Set.Icc a (a + 1)}.encard ≤ 1 := by
  rcases strictSubcritical_signedSquare_separated hΛ with ⟨d, hd, F, hsep⟩
  refine ⟨F, fun a ↦ Set.encard_le_one_iff.mpr ?_⟩
  intro i j hi hj
  change i ∉ F ∧ signedSquare (Λ i) ∈ Set.Icc a (a + 1) at hi
  change j ∉ F ∧ signedSquare (Λ j) ∈ Set.Icc a (a + 1) at hj
  by_contra hij
  have hfar := hsep i j hi.1 hj.1 hij
  have hnear : |signedSquare (Λ i) - signedSquare (Λ j)| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [hi.2.1, hi.2.2, hj.2.1, hj.2.2]
  linarith

/-- Strict subcriticality supplies a unit-separated signed-square tail whose
physical points all lie outside `[-1,1]`.  This is the block-ready carrier
geometry used by fine logarithmic decompositions. -/
theorem TwoSidedCarrier.StrictSubcritical.exists_unitSeparated_noncentral_tail
    {Λ : TwoSidedCarrier} (hΛ : Λ.StrictSubcritical) :
    ∃ F : Finset ℤ,
      (∀ i j, i ∉ F → j ∉ F → i ≠ j →
        1 ≤ |signedSquare (Λ i) - signedSquare (Λ j)|) ∧
      (∀ i, i ∉ F → 1 < (Λ i) ^ 2) := by
  rcases strictSubcritical_signedSquare_separated hΛ with
    ⟨d, hd, F₀, hsep⟩
  let F : Finset ℤ :=
    F₀ ∪ (Λ.finite_indices_in_Icc (-1) 1).toFinset
  refine ⟨F, ?_, ?_⟩
  · intro i j hi hj hij
    have hi₀ : i ∉ F₀ := by
      intro hiF₀
      exact hi (Finset.mem_union_left _ hiF₀)
    have hj₀ : j ∉ F₀ := by
      intro hjF₀
      exact hj (Finset.mem_union_left _ hjF₀)
    exact hd.le.trans (hsep i j hi₀ hj₀ hij)
  · intro i hi
    have hiInterval : Λ i ∉ Set.Icc (-1 : ℝ) 1 := by
      intro hiIcc
      apply hi
      apply Finset.mem_union_right F₀
      exact (Λ.finite_indices_in_Icc (-1) 1).mem_toFinset.mpr hiIcc
    have habs : 1 < |Λ i| := by
      apply lt_of_not_ge
      intro hle
      exact hiInterval (abs_le.mp hle)
    nlinarith [sq_abs (Λ i)]

/-- Strict subcriticality supplies a genuinely more-than-unit-separated
signed-square tail whose physical points lie outside `[-1,1]`.  Unlike the
unit-separated wrapper, this retains the strict separation constant needed
for direct inverse-power summability. -/
theorem TwoSidedCarrier.StrictSubcritical.exists_strictSeparated_noncentral_tail
    {Λ : TwoSidedCarrier} (hΛ : Λ.StrictSubcritical) :
    ∃ d > 1, ∃ F : Finset ℤ,
      (∀ i j, i ∉ F → j ∉ F → i ≠ j →
        d ≤ |signedSquare (Λ i) - signedSquare (Λ j)|) ∧
      (∀ i, i ∉ F → 1 < (Λ i) ^ 2) := by
  rcases strictSubcritical_signedSquare_separated hΛ with
    ⟨d, hd, F₀, hsep⟩
  let F : Finset ℤ :=
    F₀ ∪ (Λ.finite_indices_in_Icc (-1) 1).toFinset
  refine ⟨d, hd, F, ?_, ?_⟩
  · intro i j hi hj hij
    apply hsep i j
    · exact fun hiF₀ ↦ hi (Finset.mem_union_left _ hiF₀)
    · exact fun hjF₀ ↦ hj (Finset.mem_union_left _ hjF₀)
    · exact hij
  · intro i hi
    have hiInterval : Λ i ∉ Set.Icc (-1 : ℝ) 1 := by
      intro hiIcc
      apply hi
      apply Finset.mem_union_right F₀
      exact (Λ.finite_indices_in_Icc (-1) 1).mem_toFinset.mpr hiIcc
    have habs : 1 < |Λ i| := by
      apply lt_of_not_ge
      intro hle
      exact hiInterval (abs_le.mp hle)
    nlinarith [sq_abs (Λ i)]

end MeyerGeneralProblem
