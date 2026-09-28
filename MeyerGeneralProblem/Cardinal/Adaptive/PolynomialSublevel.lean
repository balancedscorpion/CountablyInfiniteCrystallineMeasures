module

public import MeyerGeneralProblem.Cardinal.Adaptive.QuadraticSublevel
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import all Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.Pi
import all Mathlib.MeasureTheory.Integral.Pi

@[expose] public section

/-!
# Quantitative sublevel bounds for genuine multiquadratic polynomials

A recursive coefficient array represents every polynomial of degree at most two
in each coordinate. The probability law is an actual finite product of the
uniform scale law. The power-threshold induction keeps the dimension constant
explicit, before conversion to the fractional-power form.
-/

namespace MeyerGeneralProblem.Adaptive

noncomputable section
open MeasureTheory Set
open scoped ENNReal

/-- Explicit scalar coefficient arrays, one ternary index for each variable. -/
@[reducible] def QuadraticArray : ℕ → Type
  | 0 => ℝ
  | q+1 => Fin 3 → QuadraticArray q

/-- The corresponding actual finite-dimensional coordinate space. -/
@[reducible] def ScaleCube : ℕ → Type
  | 0 => Unit
  | q+1 => ScaleCube q × ℝ

@[reducible] instance scaleCubeMeasurable : (q : ℕ) → MeasurableSpace (ScaleCube q)
  | 0 => inferInstanceAs (MeasurableSpace Unit)
  | q+1 => @Prod.instMeasurableSpace _ _ (scaleCubeMeasurable q) inferInstance

/-- The literal product of q uniform laws, with the one-point law in dimension zero. -/
def finiteScaleLaw : (q : ℕ) → Measure (ScaleCube q)
  | 0 => Measure.dirac ()
  | q+1 => (finiteScaleLaw q).prod scaleLaw

instance finiteScaleLaw_probability (q : ℕ) : IsProbabilityMeasure (finiteScaleLaw q) := by
  induction q with
  | zero => change IsProbabilityMeasure (Measure.dirac ()); infer_instance
  | succ q ih =>
    change IsProbabilityMeasure ((finiteScaleLaw q).prod scaleLaw)
    infer_instance

/-- Total mass of the concrete finite product, including numerically fixed dimensions. -/
@[simp] theorem finiteScaleLaw_univ (q : ℕ) : finiteScaleLaw q Set.univ = 1 := measure_univ

/-- The recursive product is measurably equivalent to the usual finite coordinate cube. -/
def ScaleCube.equivFin : (q : ℕ) → ScaleCube q ≃ᵐ (Fin q → ℝ)
  | 0 => (MeasurableEquiv.ofUniqueOfUnique (Fin 0 → ℝ) Unit).symm
  | q+1 => ((ScaleCube.equivFin q).prodCongr (MeasurableEquiv.refl ℝ)).trans
      (MeasurableEquiv.prodComm.trans
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (q+1) => ℝ) 0).symm)

/-- Exact identification with Mathlib's genuine finite-dimensional product measure. -/
theorem ScaleCube.equivFin_measurePreserving (q : ℕ) :
    MeasurePreserving (ScaleCube.equivFin q) (finiteScaleLaw q)
      (Measure.pi (fun _ : Fin q => scaleLaw)) := by
  induction q with
  | zero => exact (measurePreserving_pi_empty (fun _ : Fin 0 => scaleLaw)).symm
  | succ q ih =>
    exact ((measurePreserving_piFinSuccAbove (fun _ : Fin (q+1) => scaleLaw) 0).symm.comp
      (Measure.measurePreserving_swap)).comp (ih.prod (MeasurePreserving.id scaleLaw))

/-- Evaluation of the actual polynomial represented by the full coefficient array. -/
def QuadraticArray.eval : {q : ℕ} → QuadraticArray q → ScaleCube q → ℝ
  | 0, p, _ => p
  | _q+1, p, x => quadraticValue (eval (p 2) x.1) (eval (p 1) x.1) (eval (p 0) x.1) x.2

/-- An explicit coefficient has magnitude at least d; this contains no analytic hypothesis. -/
def QuadraticArray.HasLargeCoefficient : {q : ℕ} → QuadraticArray q → ℝ → Prop
  | 0, p, d => d ≤ |p|
  | _q+1, p, d => ∃ k : Fin 3, HasLargeCoefficient (p k) d

theorem QuadraticArray.measurable_eval {q : ℕ} (p : QuadraticArray q) :
    Measurable (QuadraticArray.eval p) := by
  induction q with
  | zero => exact measurable_const
  | succ q ih =>
    change Measurable (fun x : ScaleCube q × ℝ =>
      quadraticValue (QuadraticArray.eval (p 2) x.1) (QuadraticArray.eval (p 1) x.1)
        (QuadraticArray.eval (p 0) x.1) x.2)
    unfold quadraticValue
    exact (((ih (p 2)).comp measurable_fst).mul (measurable_snd.pow_const 2)).add
      (((ih (p 1)).comp measurable_fst).mul measurable_snd) |>.add
        ((ih (p 0)).comp measurable_fst)

/-- The actual coefficient attached to a multi-index with exponents 0, 1 or 2. -/
def QuadraticArray.coeff : {q : ℕ} → QuadraticArray q → (Fin q → Fin 3) → ℝ
  | 0, p, _ => p
  | _q+1, p, k => coeff (p (k 0)) (Fin.tail k)

/-- Build the polynomial from an arbitrary full finite scalar coefficient table. -/
def QuadraticArray.ofCoefficients : {q : ℕ} → ((Fin q → Fin 3) → ℝ) → QuadraticArray q
  | 0, c => c Fin.elim0
  | _q+1, c => fun k => ofCoefficients (fun j => c (Fin.cons k j))

theorem QuadraticArray.coeff_ofCoefficients {q : ℕ} (c : (Fin q → Fin 3) → ℝ)
    (k : Fin q → Fin 3) : (ofCoefficients c).coeff k = c k := by
  induction q with
  | zero =>
    change c Fin.elim0 = c k
    congr 1
    exact Subsingleton.elim _ _
  | succ q ih =>
    change (ofCoefficients (fun j => c (Fin.cons (k 0) j))).coeff (Fin.tail k) = c k
    rw [ih, Fin.cons_self_tail]

/-- Coefficient normalization is exactly a lower bound for an explicit entry of the table. -/
theorem QuadraticArray.hasLargeCoefficient_iff {q : ℕ} (p : QuadraticArray q) (d : ℝ) :
    p.HasLargeCoefficient d ↔ ∃ k : Fin q → Fin 3, d ≤ |p.coeff k| := by
  induction q with
  | zero => simp [HasLargeCoefficient, coeff]
  | succ q ih =>
    constructor
    · rintro ⟨k, hk⟩
      obtain ⟨j, hj⟩ := (ih (p k)).mp hk
      exact ⟨Fin.cons k j, by simpa [coeff] using hj⟩
    · rintro ⟨k, hk⟩
      exact ⟨k 0, (ih (p (k 0))).mpr ⟨Fin.tail k, hk⟩⟩

/-- Literal finite sum of monomials with each coordinate exponent at most two. -/
def multiquadraticValue {q : ℕ} (c : (Fin q → Fin 3) → ℝ) (x : Fin q → ℝ) : ℝ :=
  ∑ k : Fin q → Fin 3, c k * ∏ i, x i ^ (k i : ℕ)

/-- Splitting the first variable of the full finite monomial sum. -/
theorem multiquadraticValue_succ {q : ℕ} (c : (Fin (q+1) → Fin 3) → ℝ)
    (x : Fin (q+1) → ℝ) :
    multiquadraticValue c x = quadraticValue
      (multiquadraticValue (fun k => c (Fin.cons 2 k)) (Fin.tail x))
      (multiquadraticValue (fun k => c (Fin.cons 1 k)) (Fin.tail x))
      (multiquadraticValue (fun k => c (Fin.cons 0 k)) (Fin.tail x)) (x 0) := by
  unfold multiquadraticValue
  rw [← (Fin.consEquiv (fun _ : Fin (q+1) => Fin 3)).sum_comp]
  rw [Fintype.sum_prod_type]
  simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
  simp_rw [show ∀ k : Fin 3, ∀ j : Fin q → Fin 3,
    c (Fin.cons k j) * (x 0 ^ (k : ℕ) * ∏ i, x i.succ ^ (j i : ℕ)) =
      (c (Fin.cons k j) * ∏ i, x i.succ ^ (j i : ℕ)) * x 0 ^ (k : ℕ) by intros; ring,
      ← Finset.sum_mul]
  rw [Fin.sum_univ_three]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, mul_one]
  unfold quadraticValue
  simp only [Fin.tail_def]
  ring

/-- The recursive implementation evaluates exactly the ordinary finite monomial sum. -/
theorem QuadraticArray.eval_eq_multiquadraticValue {q : ℕ} (p : QuadraticArray q)
    (x : Fin q → ℝ) :
    p.eval ((ScaleCube.equivFin q).symm x) = multiquadraticValue p.coeff x := by
  induction q with
  | zero => simp [eval, coeff, multiquadraticValue]
  | succ q ih =>
    rw [multiquadraticValue_succ]
    change quadraticValue
      ((p 2).eval ((ScaleCube.equivFin q).symm (Fin.tail x)))
      ((p 1).eval ((ScaleCube.equivFin q).symm (Fin.tail x)))
      ((p 0).eval ((ScaleCube.equivFin q).symm (Fin.tail x))) (x 0) = _
    simp only [ih, coeff, Fin.cons_zero, Fin.tail_cons]

/-- A fibre coefficient threshold splits the actual product sublevel probability. -/
theorem quadratic_fiber_sublevel_le {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (a b c : α → ℝ)
    (ha : Measurable a) (hb : Measurable b) (hc : Measurable c)
    (D u : ℝ) (hD : 0 < D) (hu : 0 < u)
    (v : α → ℝ) (hv : Measurable v) (hchoice : v = a ∨ v = b ∨ v = c) :
    (μ.prod scaleLaw) {z : α × ℝ | |quadraticValue (a z.1) (b z.1) (c z.1) z.2| < u} ≤
      μ {x | |v x| < D} + ENNReal.ofReal (16 * Real.sqrt (u/D)) := by
  let E : Set (α × ℝ) := {z | |quadraticValue (a z.1) (b z.1) (c z.1) z.2| < u}
  let B : Set α := {x | |v x| < D}
  let C : ℝ≥0∞ := ENNReal.ofReal (16 * Real.sqrt (u/D))
  have hE : MeasurableSet E := by
    dsimp [E, quadraticValue]
    apply measurableSet_lt _ measurable_const
    apply continuous_abs.measurable.comp
    exact (((ha.comp measurable_fst).mul (measurable_snd.pow_const 2)).add
        ((hb.comp measurable_fst).mul measurable_snd)).add (hc.comp measurable_fst)
  have hB : MeasurableSet B := measurableSet_lt (continuous_abs.measurable.comp hv) measurable_const
  have hfib : ∀ x : α, scaleLaw (Prod.mk x ⁻¹' E) ≤ B.indicator (fun _ => 1) x + C := by
    intro x
    by_cases hx : x ∈ B
    · rw [Set.indicator_of_mem hx]
      calc
        _ ≤ scaleLaw Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
        _ ≤ 1+C := le_add_right le_rfl
    · rw [Set.indicator_of_notMem hx, zero_add]
      have hcoeff : D ≤ |a x| ∨ D ≤ |b x| ∨ D ≤ |c x| := by
        have hx' : D ≤ |v x| := le_of_not_gt hx
        rcases hchoice with rfl | rfl | rfl
        · exact Or.inl hx'
        · exact Or.inr (Or.inl hx')
        · exact Or.inr (Or.inr hx')
      change scaleLaw {y : ℝ | |quadraticValue (a x) (b x) (c x) y| < u} ≤ C
      unfold scaleLaw
      rw [Measure.restrict_apply₀, Set.inter_comm]
      · exact quadratic_sublevel_volume_le (a x) (b x) (c x) D u hD hu hcoeff
      · exact (isOpen_lt (by unfold quadraticValue; fun_prop) continuous_const).measurableSet.nullMeasurableSet
  change (μ.prod scaleLaw) E ≤ μ B + C
  rw [Measure.prod_apply hE]
  calc
    _ ≤ ∫⁻ x, B.indicator (fun _ => 1) x + C ∂μ := lintegral_mono hfib
    _ = μ B + C := by
      rw [lintegral_add_left (measurable_const.indicator hB), lintegral_indicator hB]
      simp

/-- Actual finite-product small-ball estimate in a power threshold, including dimension zero. -/
theorem QuadraticArray.power_sublevel_le {q : ℕ} (p : QuadraticArray q)
    (d t : ℝ) (hd : 0 < d) (ht : 0 < t) (hp : p.HasLargeCoefficient d) :
    finiteScaleLaw q {x | |p.eval x| < d*t^(2*q)} ≤
      ENNReal.ofReal (16*(q : ℝ)*t) := by
  induction q with
  | zero =>
    have hempty : {x : ScaleCube 0 | |p.eval x| < d*t^(2*0)} = ∅ := by
      ext x
      simp only [QuadraticArray.eval, mul_zero, pow_zero, mul_one, mem_ofPred_eq,
        mem_empty_iff_false, iff_false]
      exact not_lt_of_ge hp
    rw [hempty]
    simp
  | succ q ih =>
    obtain ⟨k, hk⟩ := hp
    let D := d*t^(2*q)
    let u := d*t^(2*(q+1))
    have hD : 0 < D := by dsimp [D]; positivity
    have hu : 0 < u := by dsimp [u]; positivity
    have hchoice : (p k).eval = (p 2).eval ∨ (p k).eval = (p 1).eval ∨
        (p k).eval = (p 0).eval := by fin_cases k <;> tauto
    have hsplit := quadratic_fiber_sublevel_le (finiteScaleLaw q)
      (p 2).eval (p 1).eval (p 0).eval (p 2).measurable_eval
      (p 1).measurable_eval (p 0).measurable_eval D u hD hu (p k).eval
      (p k).measurable_eval hchoice
    have hquot : u/D = t^2 := by
      dsimp [u, D]
      rw [show 2*(q+1) = 2*q+2 by omega, pow_add]
      field_simp
    have hsqrt : Real.sqrt (u/D) = t := by
      rw [hquot, Real.sqrt_sq ht.le]
    change (finiteScaleLaw q).prod scaleLaw
      {x | |quadraticValue ((p 2).eval x.1) ((p 1).eval x.1) ((p 0).eval x.1) x.2| < u} ≤ _
    calc
      _ ≤ finiteScaleLaw q {x | |(p k).eval x| < D} +
          ENNReal.ofReal (16*Real.sqrt (u/D)) := hsplit
      _ ≤ ENNReal.ofReal (16*(q : ℝ)*t) + ENNReal.ofReal (16*t) := by
        rw [hsqrt]
        exact add_le_add (ih (p k) hk) le_rfl
      _ = ENNReal.ofReal (16*((q+1 : ℕ) : ℝ)*t) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        push_cast
        ring

/-- Dimension-only quantitative multivariate sublevel probability, with the precise exponent. -/
theorem QuadraticArray.sublevel_le {q : ℕ} (hq : 0 < q) (p : QuadraticArray q)
    (d u : ℝ) (hd : 0 < d) (hu : 0 < u) (hp : p.HasLargeCoefficient d) :
    finiteScaleLaw q {x | |p.eval x| < u} ≤
      min 1 (ENNReal.ofReal (16*(q : ℝ)*(u/d)^((1 : ℝ)/(2*(q : ℝ))))) := by
  let t : ℝ := (u/d)^((1 : ℝ)/(2*(q : ℝ)))
  have ht : 0 < t := Real.rpow_pos_of_pos (by positivity) _
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  have htpow : t^(2*q) = u/d := by
    dsimp [t]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : 0 ≤ u/d)]
    have hexp : (1/(2*(q : ℝ))) * ((2*q : ℕ) : ℝ) = 1 := by
      push_cast
      field_simp
    rw [hexp, Real.rpow_one]
  have hthreshold : d*t^(2*q) = u := by rw [htpow]; field_simp
  apply le_min
  · calc
      _ ≤ finiteScaleLaw q Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  · simpa only [hthreshold] using p.power_sublevel_le d t hd ht hp

/-- The same quantitative bound on the usual finite coordinate cube, with its exact product law. -/
theorem QuadraticArray.finite_pi_sublevel_le {q : ℕ} (hq : 0 < q) (p : QuadraticArray q)
    (d u : ℝ) (hd : 0 < d) (hu : 0 < u) (hp : p.HasLargeCoefficient d) :
    (Measure.pi (fun _ : Fin q => scaleLaw))
      {x | |p.eval ((ScaleCube.equivFin q).symm x)| < u} ≤
        min 1 (ENNReal.ofReal (16*(q : ℝ)*(u/d)^((1 : ℝ)/(2*(q : ℝ))))) := by
  have hm : MeasurableSet {x : Fin q → ℝ | |p.eval ((ScaleCube.equivFin q).symm x)| < u} :=
    measurableSet_lt (continuous_abs.measurable.comp
      (p.measurable_eval.comp (ScaleCube.equivFin q).symm.measurable)) measurable_const
  have hmap := Measure.map_apply (μ := finiteScaleLaw q) (ScaleCube.equivFin q).measurable hm
  rw [(ScaleCube.equivFin_measurePreserving q).map_eq] at hmap
  rw [hmap]
  simpa using p.sublevel_le hq d u hd hu hp

/-- Full scalar-coefficient polynomial theorem on the actual finite product cube. -/
theorem multiquadratic_sublevel_le {q : ℕ} (hq : 0 < q)
    (c : (Fin q → Fin 3) → ℝ) (d u : ℝ) (hd : 0 < d) (hu : 0 < u)
    (hc : ∃ k, d ≤ |c k|) :
    (Measure.pi (fun _ : Fin q => scaleLaw)) {x | |multiquadraticValue c x| < u} ≤
      min 1 (ENNReal.ofReal (16*(q : ℝ)*(u/d)^((1 : ℝ)/(2*(q : ℝ))))) := by
  have hp : (QuadraticArray.ofCoefficients c).HasLargeCoefficient d := by
    simpa only [QuadraticArray.hasLargeCoefficient_iff, QuadraticArray.coeff_ofCoefficients] using hc
  have hcoeff : (QuadraticArray.ofCoefficients c).coeff = c :=
    funext (QuadraticArray.coeff_ofCoefficients c)
  simpa only [QuadraticArray.eval_eq_multiquadraticValue, hcoeff] using
    (QuadraticArray.ofCoefficients c).finite_pi_sublevel_le hq d u hd hu hp

/-- Any injectively selected finite family has exactly the finite product scale law. -/
theorem scaleProbability_map_finite_coordinates {q : ℕ} (f : Fin q → ℕ+)
    (hf : Function.Injective f) :
    scaleProbability.map (fun s i => s (f i)) = Measure.pi (fun _ : Fin q => scaleLaw) := by
  have h := ProbabilityTheory.iIndepFun.map_fun_eq_pi_map
    (fun i => (measurable_pi_apply (f i)).aemeasurable)
    (ProbabilityTheory.iIndepFun.precomp hf scaleProbability_iIndepFun)
  simpa only [scaleProbability_map_eval] using h

/-- The full scalar-coefficient estimate for any distinct actual product coordinates. -/
theorem multiquadratic_coordinate_sublevel_le {q : ℕ} (hq : 0 < q)
    (f : Fin q → ℕ+) (hf : Function.Injective f)
    (c : (Fin q → Fin 3) → ℝ) (d u : ℝ) (hd : 0 < d) (hu : 0 < u)
    (hc : ∃ k, d ≤ |c k|) :
    scaleProbability {s | |multiquadraticValue c (fun i => s (f i))| < u} ≤
      min 1 (ENNReal.ofReal (16*(q : ℝ)*(u/d)^((1 : ℝ)/(2*(q : ℝ))))) := by
  have hm : MeasurableSet {x : Fin q → ℝ | |multiquadraticValue c x| < u} := by
    apply measurableSet_lt _ measurable_const
    apply continuous_abs.measurable.comp
    unfold multiquadraticValue
    fun_prop
  have hmap := Measure.map_apply (μ := scaleProbability)
    (show Measurable (fun s : ℕ+ → ℝ => fun i => s (f i)) by fun_prop) hm
  rw [scaleProbability_map_finite_coordinates f hf] at hmap
  change scaleProbability ((fun s : ℕ+ → ℝ => fun i => s (f i)) ⁻¹'
    {x | |multiquadraticValue c x| < u}) ≤ _
  rw [← hmap]
  exact multiquadratic_sublevel_le hq c d u hd hu hc

end
end MeyerGeneralProblem.Adaptive
