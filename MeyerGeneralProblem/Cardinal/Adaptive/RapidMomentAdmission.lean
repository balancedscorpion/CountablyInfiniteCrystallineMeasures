module

public import MeyerGeneralProblem.Cardinal.Adaptive.GaugedReverseZak

@[expose] public section

/-! Finite maximum-index summation for rapid admission, with the moment premise explicit. -/
noncomputable section
open scoped BigOperators
namespace MeyerGeneralProblem.Adaptive
/-- Exact maximum-index shell count, retaining both arms. -/
theorem sum_max_square (g : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, g (max i j)) =
      ∑ m ∈ Finset.range n, (2*(m:ℝ)+1)*g m := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        _ = (∑ i ∈ Finset.range n, ((∑ j ∈ Finset.range n, g (max i j))+g (max i n)))+
            ((∑ j ∈ Finset.range n, g (max n j))+g n) := by
          rw [Finset.sum_range_succ]
          simp_rw [Finset.sum_range_succ,max_self]
        _ = (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, g (max i j))+
            (n:ℝ)*g n+((n:ℝ)*g n+g n) := by
          rw [Finset.sum_add_distrib]
          have h1 : (∑ i ∈ Finset.range n, g (max i n))=(n:ℝ)*g n := by
            calc
              _ = ∑ i ∈ Finset.range n, g n := Finset.sum_congr rfl (fun i hi => by
                rw [max_eq_right (Nat.le_of_lt (Finset.mem_range.mp hi))])
              _ = _ := by simp
          have h2 : (∑ j ∈ Finset.range n, g (max n j))=(n:ℝ)*g n := by
            calc
              _ = ∑ j ∈ Finset.range n, g n := Finset.sum_congr rfl (fun j hj => by
                rw [max_eq_left (Nat.le_of_lt (Finset.mem_range.mp hj))])
              _ = _ := by simp
          rw [h1,h2]
        _ = _ := by rw [ih,Finset.sum_range_succ]; ring

/-- Exact shell count for finite endpoint coefficient indices. -/
theorem sum_fin_max_square (g : ℕ → ℝ) (n : ℕ) :
    (∑ i : Fin n, ∑ j : Fin n, g (max i.val j.val)) =
      ∑ m ∈ Finset.range n, (2*(m:ℝ)+1)*g m := by
  have hi (i : ℕ) : (∑ j : Fin n, g (max i j.val)) =
      ∑ j ∈ Finset.range n, g (max i j) := Fin.sum_univ_eq_sum_range (fun j => g (max i j)) n
  simp_rw [hi]
  rw [Fin.sum_univ_eq_sum_range (fun i => ∑ j ∈ Finset.range n, g (max i j)) n]
  exact sum_max_square g n

/-- The full maximum-index majorant controls each actual coefficient-moment
product, including indices on the two long arms. -/
theorem rapidAdmission_term_majorant {P R : ℕ} (hP : 1 ≤ P) (hR : 1 ≤ R)
    (i j L : ℕ) (K : ℝ) (hK : 0 ≤ K) :
    4^(i+j)*K^(max i j)*shrinkingNewtonWeight (rapidDistance P R) (max i j) /
      (rapidCharacteristicProduct P R (i-L)*rapidCharacteristicProduct P R (j-L)) ≤
    (16*K)^(max i j)*shrinkingNewtonWeight (rapidDistance P R) (max i j) /
      rapidCharacteristicProduct P R (max i j-L)^2 := by
  have hw : 0 < shrinkingNewtonWeight (rapidDistance P R) (max i j) :=
    Finset.prod_pos (fun l _ => (rapidDistance_bounds hP hR (l+1)).1)
  have hp := rapidCharacteristicProduct_pos hP hR (max i j-L)
  have hi := rapidCharacteristicProduct_pos hP hR (i-L)
  have hj := rapidCharacteristicProduct_pos hP hR (j-L)
  have hpow : (4:ℝ)^(i+j) ≤ 16^(max i j) := by
    calc
      _ ≤ (4:ℝ)^(2*max i j) := pow_le_pow_right₀ (by norm_num) (by omega)
      _ = _ := by rw [pow_mul]; norm_num
  calc
    _ ≤ 4^(i+j)*K^(max i j)*shrinkingNewtonWeight (rapidDistance P R) (max i j) /
        rapidCharacteristicProduct P R (max i j-L)^2 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (rapidCharacteristicProduct_max_le hP hR i j L)
    _ ≤ 16^(max i j)*K^(max i j)*shrinkingNewtonWeight (rapidDistance P R) (max i j) /
        rapidCharacteristicProduct P R (max i j-L)^2 := by gcongr
    _ = _ := by rw [mul_pow]

/-- Uniform original-native finite moment summation for a chart with the actual
rapid interpolation coefficient bound. Both quantitative premises remain explicit. -/
theorem exists_chart_finite_moment_bound {P R : ℕ}
    (hP : 1 ≤ P) (hR : 1 ≤ R) (e d : Bool) (L : ℕ) (hL : 4 < rapidBase P^L)
    (K : ℝ) (hK : 0 ≤ K) (X : SchwartzMap ℝ ℂ → ℝ → ℝ → ℂ)
    (hX : ∃ B : ℝ, 0 < B ∧ ∀ k : ℕ, ∀ f : SchwartzMap ℝ ℂ, ∀ i j : Fin (k+1),
      ‖rapidGridCoefficient P R hP hR k e d (X f) i j‖ ≤
        4^(i.val+j.val)*(B*‖schwartzToHermiteScale (2*L+2) f‖)/
          (rapidCharacteristicProduct P R (i.val-L)*rapidCharacteristicProduct P R (j.val-L))) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, ∀ f : SchwartzMap ℝ ℂ, ∀ A : ℝ, 0 ≤ A →
      ∀ M : Fin (k+1) → Fin (k+1) → ℂ,
      (∀ i j, ‖M i j‖ ≤ A*K^(max i.val j.val)*
        shrinkingNewtonWeight (rapidDistance P R) (max i.val j.val)) →
      ‖∑ i, ∑ j, rapidGridCoefficient P R hP hR k e d (X f) i j*M i j‖ ≤
        C*A*‖schwartzToHermiteScale (2*L+2) f‖ := by
  obtain ⟨B,hB,hcoeff⟩ := hX
  let g : ℕ → ℝ := fun m => (16*K)^m*shrinkingNewtonWeight (rapidDistance P R) m /
    rapidCharacteristicProduct P R (m-L)^2
  have hg (m : ℕ) : 0 ≤ g m := by
    have hw : 0 < shrinkingNewtonWeight (rapidDistance P R) m :=
      Finset.prod_pos (fun l _ => (rapidDistance_bounds hP hR (l+1)).1)
    dsimp [g]
    positivity
  have hs : Summable (fun m : ℕ => (2*(m:ℝ)+1)*g m) := by
    simpa only [g,mul_div_assoc,mul_assoc] using
      summable_rapidAdmission_majorant hP hR (16*K) (by positivity) L hL
  let S : ℝ := ∑' m : ℕ, (2*(m:ℝ)+1)*g m
  have hS : 0 ≤ S := tsum_nonneg (fun m => mul_nonneg (by positivity) (hg m))
  refine ⟨B*S+1,by positivity,?_⟩
  intro k f A hA M hM
  let H : ℝ := ‖schwartzToHermiteScale (2*L+2) f‖
  have hH : 0 ≤ H := norm_nonneg _
  have hterm (i j : Fin (k+1)) :
      ‖rapidGridCoefficient P R hP hR k e d (X f) i j*M i j‖ ≤
        (B*A*H)*g (max i.val j.val) := by
    have hc := hcoeff k f i j
    have hpos : 0 ≤ 4^(i.val+j.val)*(B*H)/
        (rapidCharacteristicProduct P R (i.val-L)*rapidCharacteristicProduct P R (j.val-L)) := by
      have hi := rapidCharacteristicProduct_pos hP hR (i.val-L)
      have hj := rapidCharacteristicProduct_pos hP hR (j.val-L)
      positivity
    rw [norm_mul]
    apply (mul_le_mul hc (hM i j) (norm_nonneg _) hpos).trans
    calc
      _ = (B*A*H)*(4^(i.val+j.val)*K^(max i.val j.val)*
          shrinkingNewtonWeight (rapidDistance P R) (max i.val j.val)/
          (rapidCharacteristicProduct P R (i.val-L)*rapidCharacteristicProduct P R (j.val-L))) := by
        dsimp [H]
        ring
      _ ≤ (B*A*H)*g (max i.val j.val) :=
        mul_le_mul_of_nonneg_left (rapidAdmission_term_majorant hP hR i.val j.val L K hK) (by positivity)
  have hsum : (∑ i : Fin (k+1), ∑ j : Fin (k+1), g (max i.val j.val)) ≤ S := by
    rw [sum_fin_max_square]
    exact hs.sum_le_tsum _ (fun m _ => mul_nonneg (by positivity) (hg m))
  calc
    _ ≤ ∑ i : Fin (k+1), ∑ j : Fin (k+1),
        ‖rapidGridCoefficient P R hP hR k e d (X f) i j*M i j‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => norm_sum_le _ _))
    _ ≤ ∑ i : Fin (k+1), ∑ j : Fin (k+1), (B*A*H)*g (max i.val j.val) :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hterm i j))
    _ = (B*A*H)*(∑ i : Fin (k+1), ∑ j : Fin (k+1), g (max i.val j.val)) := by
      simp_rw [Finset.mul_sum]
    _ ≤ (B*A*H)*S := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ (B*S+1)*A*H := by nlinarith

/-- Uniform original-native bound for one actual gauged finite-grid moment
sum. The full-maximum moment estimate is an explicit premise, not a certificate
for an arbitrary source or an assertion that B07 has been discharged. -/
theorem exists_gaugedReverseZak_finite_moment_bound {P R : ℕ}
    (hP : 1 ≤ P) (hR : 1 ≤ R) (e d : Bool) (L : ℕ) (hL : 4 < rapidBase P^L)
    (K : ℝ) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, ∀ f : SchwartzMap ℝ ℂ, ∀ A : ℝ, 0 ≤ A →
      ∀ M : Fin (k+1) → Fin (k+1) → ℂ,
      (∀ i j, ‖M i j‖ ≤ A*K^(max i.val j.val)*
        shrinkingNewtonWeight (rapidDistance P R) (max i.val j.val)) →
      ‖∑ i, ∑ j, rapidGridCoefficient P R hP hR k e d (gaugedReverseZakChart f) i j*M i j‖ ≤
        C*A*‖schwartzToHermiteScale (2*L+2) f‖ := by
  obtain ⟨B,hB,hcoeff⟩ := exists_gaugedReverseZak_rapidGridCoefficient_bound e d L
  exact exists_chart_finite_moment_bound hP hR e d L hL K hK gaugedReverseZakChart
    ⟨B,hB,hcoeff P R hP hR⟩

/-- Four-parity finite moment summation for any quantitatively controlled actual chart. -/
theorem exists_chart_four_parity_moment_bound {P R : ℕ}
    (hP : 1 ≤ P) (hR : 1 ≤ R) (L : ℕ) (hL : 4 < rapidBase P^L)
    (K : ℝ) (hK : 0 ≤ K) (X : SchwartzMap ℝ ℂ → ℝ → ℝ → ℂ)
    (hX : ∀ e d : Bool, ∃ B : ℝ, 0 < B ∧ ∀ k : ℕ, ∀ f : SchwartzMap ℝ ℂ,
      ∀ i j : Fin (k+1), ‖rapidGridCoefficient P R hP hR k e d (X f) i j‖ ≤
        4^(i.val+j.val)*(B*‖schwartzToHermiteScale (2*L+2) f‖)/
          (rapidCharacteristicProduct P R (i.val-L)*rapidCharacteristicProduct P R (j.val-L))) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, ∀ f : SchwartzMap ℝ ℂ, ∀ A : ℝ, 0 ≤ A →
      ∀ M : Bool → Bool → Fin (k+1) → Fin (k+1) → ℂ,
      (∀ e d i j, ‖M e d i j‖ ≤ A*K^(max i.val j.val)*
        shrinkingNewtonWeight (rapidDistance P R) (max i.val j.val)) →
      ‖∑ e : Bool, ∑ d : Bool, ∑ i, ∑ j,
        rapidGridCoefficient P R hP hR k e d (X f) i j*M e d i j‖ ≤
        C*A*‖schwartzToHermiteScale (2*L+2) f‖ := by
  choose C hC hb using fun e d => exists_chart_finite_moment_bound hP hR e d L hL K hK X (hX e d)
  let D : ℝ := ∑ e : Bool, ∑ d : Bool, C e d
  have hD : 0 < D := by
    have h1 : C false false ≤ ∑ d : Bool, C false d :=
      Finset.single_le_sum (fun d _ => (hC false d).le) (Finset.mem_univ false)
    have h2 : (∑ d : Bool, C false d) ≤ D :=
      Finset.single_le_sum (fun e _ => Finset.sum_nonneg (fun d _ => (hC e d).le))
        (Finset.mem_univ false)
    exact (hC false false).trans_le (h1.trans h2)
  refine ⟨D,hD,?_⟩
  intro k f A hA M hM
  calc
    _ ≤ ∑ e : Bool, ∑ d : Bool, ‖∑ i, ∑ j,
        rapidGridCoefficient P R hP hR k e d (X f) i j*M e d i j‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun e _ => norm_sum_le _ _))
    _ ≤ ∑ e : Bool, ∑ d : Bool, C e d*A*‖schwartzToHermiteScale (2*L+2) f‖ :=
      Finset.sum_le_sum (fun e _ => Finset.sum_le_sum (fun d _ => hb e d k f A hA (M e d) (hM e d)))
    _ = _ := by simp only [D,Finset.sum_mul]
/-- The full four-parity finite gauged moment sum is uniformly bounded in the
original native norm, still retaining the actual moment inequality explicitly. -/
theorem exists_gaugedReverseZak_four_parity_moment_bound {P R : ℕ}
    (hP : 1 ≤ P) (hR : 1 ≤ R) (L : ℕ) (hL : 4 < rapidBase P^L)
    (K : ℝ) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, ∀ f : SchwartzMap ℝ ℂ, ∀ A : ℝ, 0 ≤ A →
      ∀ M : Bool → Bool → Fin (k+1) → Fin (k+1) → ℂ,
      (∀ e d i j, ‖M e d i j‖ ≤ A*K^(max i.val j.val)*
        shrinkingNewtonWeight (rapidDistance P R) (max i.val j.val)) →
      ‖∑ e : Bool, ∑ d : Bool, ∑ i, ∑ j,
        rapidGridCoefficient P R hP hR k e d (gaugedReverseZakChart f) i j*M e d i j‖ ≤
        C*A*‖schwartzToHermiteScale (2*L+2) f‖ := by
  apply exists_chart_four_parity_moment_bound hP hR L hL K hK gaugedReverseZakChart
  intro e d
  obtain ⟨B,hB,hcoeff⟩ := exists_gaugedReverseZak_rapidGridCoefficient_bound e d L
  exact ⟨B,hB,hcoeff P R hP hR⟩

end MeyerGeneralProblem.Adaptive
