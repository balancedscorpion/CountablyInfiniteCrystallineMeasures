module

public import MeyerGeneralProblem.Cardinal.Adaptive.EndpointFiniteDiagonal
public import MeyerGeneralProblem.Cardinal.Adaptive.EndpointFourierEigen

@[expose] public section

/-! Concrete complete finite-source Newton arrays for the actual operator kernel. -/
noncomputable section
open scoped BigOperators FourierTransform
namespace MeyerGeneralProblem.Adaptive

/-- The actual normalized complete rapid finite endpoint source. -/
def endpointFiniteSource (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) (k : ℕ) : TemperedDistribution ℝ ℂ :=
  normalizedEndpointSource (rapidEndpointPhaseData P R k) (rapidEndpointPhaseData P R k)
    (rapidEndpointPhaseData_injective hP hR k) (rapidEndpointPhaseData_injective hP hR k)
    (rapidEndpointPhaseData_interior hP hR k) (rapidEndpointPhaseData_interior hP hR k)

/-- The full constant-normalized physical array, with both indices and parities. -/
def endpointFinitePhysicalArray (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) (k : ℕ)
    (z : (ℕ×Bool)×(ℕ×Bool)) : ℂ :=
  halfNewtonMoment (endpointPaddedDistance P R k) (endpointPaddedDistance P R k)
    (halfWeylDistributionCLM (endpointFiniteSource P R hP hR k)) z.1.1 z.1.2 z.2.1 z.2.2

/-- The full actual Fourier companion array in the same zero-padded coordinates. -/
def endpointFiniteFourierArray (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) (k : ℕ)
    (z : (ℕ×Bool)×(ℕ×Bool)) : ℂ :=
  halfNewtonFourierMoment (endpointPaddedDistance P R k) (endpointPaddedDistance P R k)
    (endpointFiniteSource P R hP hR k) z.1.1 z.1.2 z.2.1 z.2.2

/-- Both deleted carrier records of the concrete complete finite source. -/
theorem endpointFiniteSource_atomic_records (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) (k : ℕ) :
    AtomicOnCarrier (endpointDeletedCarrier (rapidEndpointPhaseData P R k)) (endpointFiniteSource P R hP hR k) ∧
    AtomicOnCarrier (endpointDeletedCarrier (rapidEndpointPhaseData P R k)) (𝓕 (endpointFiniteSource P R hP hR k)) :=
  normalizedEndpointSource_atomic_records _ _ _ _ _ _

/-- The concrete source is nonzero because its actual coefficient corner is one. -/
theorem endpointFiniteSource_ne_zero (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) (k : ℕ) :
    endpointFiniteSource P R hP hR k ≠ 0 := normalizedEndpointSource_ne_zero _ _ _ _ _ _

/-- The Fourier companion equals the physical recentered source for this actual
same-phase finite line, using the proved complete Fourier eigenvalue. -/
theorem endpointFiniteSource_companion (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) (k : ℕ) :
    halfWeylFourierCompanion (endpointFiniteSource P R hP hR k)=
      halfWeylDistributionCLM (endpointFiniteSource P R hP hR k) := by
  unfold halfWeylFourierCompanion
  rw [halfWeyl_fourier_conjugation]
  have hf : 𝓕 (endpointFiniteSource P R hP hR k)= -Complex.I • endpointFiniteSource P R hP hR k :=
    normalizedEndpointSource_fourier _ _ _
  rw [hf,map_smul,smul_smul]
  simp

/-- Exact signed transpose of the complete actual finite Fourier array. -/
theorem endpointFiniteFourierArray_eq (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) (k : ℕ)
    (z : (ℕ×Bool)×(ℕ×Bool)) :
    endpointFiniteFourierArray P R hP hR k z=
      halfNewtonParitySign z.1.2*endpointFinitePhysicalArray P R hP hR k (z.2,z.1) := by
  unfold endpointFiniteFourierArray endpointFinitePhysicalArray
  rw [halfNewtonFourierMoment_eq_transposed,endpointFiniteSource_companion]

/-- The full concrete physical array vanishes outside the true finite index square. -/
theorem endpointFinitePhysicalArray_zero (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) (k : ℕ)
    (z : (ℕ×Bool)×(ℕ×Bool)) (hz : k < z.1.1 ∨ k < z.2.1) :
    endpointFinitePhysicalArray P R hP hR k z=0 :=
  halfNewtonMoment_endpointPadded_zero hP hR k _ _ _ _ _ hz

/-- Complete physical square summability for the actual normalized endpoint source. -/
theorem summable_sq_endpointFinitePhysicalArray (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) (k : ℕ) :
    Summable (fun z => ‖endpointFinitePhysicalArray P R hP hR k z‖^2) :=
  summable_sq_endpointPaddedMoment hP hR k _

/-- Complete Fourier square summability follows from the actual signed transpose,
not from a hypothetical finite section of an infinite carrier. -/
theorem summable_sq_endpointFiniteFourierArray (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) (k : ℕ) :
    Summable (fun z => ‖endpointFiniteFourierArray P R hP hR k z‖^2) := by
  have hh := (Equiv.prodComm (ℕ×Bool) (ℕ×Bool)).summable_iff.mpr
    (summable_sq_endpointFinitePhysicalArray P R hP hR k)
  apply hh.congr
  intro z
  rw [endpointFiniteFourierArray_eq,norm_mul]
  have he : ‖halfNewtonParitySign z.1.2‖=1 := by cases z.1.2 <;> simp [halfNewtonParitySign]
  simp only [he,one_mul,Equiv.prodComm_apply,Function.comp_apply]
  rfl

/-- Concrete complete physical upper flag, with no support premise left over. -/
theorem endpointFinitePhysicalArray_upper (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) (k : ℕ)
    (i j : ℕ) (e f : Bool) (hij : j < i) :
    endpointFinitePhysicalArray P R hP hR k ((i,e),(j,f))=0 := by
  obtain ⟨hT,hFT⟩ := endpointFiniteSource_atomic_records P R hP hR k
  obtain ⟨hp,hq⟩ := halfWeylEndpoint_atomic_records _ _ _ hT hFT
  exact endpointNewtonMoment_upper_flag hP hR k _ hp hq i j e f hij

/-- Concrete complete Fourier lower flag, with no support premise left over. -/
theorem endpointFiniteFourierArray_lower (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) (k : ℕ)
    (i j : ℕ) (e f : Bool) (hij : i < j) :
    endpointFiniteFourierArray P R hP hR k ((i,e),(j,f))=0 := by
  obtain ⟨hT,hFT⟩ := endpointFiniteSource_atomic_records P R hP hR k
  exact endpointNewtonFourierMoment_lower_flag hP hR k _ hT hFT i j e f hij

/-- Exact concrete physical diagonal equations for every level, including and beyond the cap. -/
theorem endpointFinitePhysicalArray_diagonal (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) (k i : ℕ) :
    endpointFinitePhysicalArray P R hP hR k ((i,true),(i,false))=
      Complex.I*(Real.tan (Real.pi*endpointPaddedDistance P R k ⟨i+1,by omega⟩) : ℂ)*
        endpointFinitePhysicalArray P R hP hR k ((i,false),(i,true)) ∧
    endpointFinitePhysicalArray P R hP hR k ((i,true),(i,true))=
      (-Complex.I*(Real.tan (Real.pi*endpointPaddedDistance P R k ⟨i+1,by omega⟩) : ℂ)/(1/4096 : ℂ))*
        endpointFinitePhysicalArray P R hP hR k ((i,false),(i,false)) := by
  obtain ⟨hT,hFT⟩ := endpointFiniteSource_atomic_records P R hP hR k
  obtain ⟨hp,hq⟩ := halfWeylEndpoint_atomic_records _ _ _ hT hFT
  exact endpointNewtonMoment_diagonal_relations hP hR k _ hp hq i

/-- Exact reversed Fourier diagonal equations for the complete concrete array. -/
theorem endpointFiniteFourierArray_diagonal (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) (k i : ℕ) :
    endpointFiniteFourierArray P R hP hR k ((i,false),(i,true))=
      -Complex.I*(Real.tan (Real.pi*endpointPaddedDistance P R k ⟨i+1,by omega⟩) : ℂ)*
        endpointFiniteFourierArray P R hP hR k ((i,true),(i,false)) ∧
    endpointFiniteFourierArray P R hP hR k ((i,true),(i,true))=
      (Complex.I*(Real.tan (Real.pi*endpointPaddedDistance P R k ⟨i+1,by omega⟩) : ℂ)/(1/4096 : ℂ))*
        endpointFiniteFourierArray P R hP hR k ((i,false),(i,false)) := by
  obtain ⟨hT,hFT⟩ := endpointFiniteSource_atomic_records P R hP hR k
  exact endpointNewtonFourierMoment_diagonal_relations hP hR k _ hT hFT i

/-- The concrete full physical moment array is nonzero. This follows from exact
finite interpolation of every Schwartz reading, not a presumed moment corner. -/
theorem endpointFinitePhysicalArray_ne_zero (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) (k : ℕ) :
    endpointFinitePhysicalArray P R hP hR k ≠ 0 := by
  intro hz
  apply endpointFiniteSource_ne_zero P R hP hR k
  apply halfWeylDistribution_injective
  rw [map_zero]
  ext f
  let c := normalizedEndpointMatrix (rapidEndpointPhaseData P R k) (rapidEndpointPhaseData P R k)
    (rapidEndpointPhaseData_injective hP hR k) (rapidEndpointPhaseData_injective hP hR k)
    (rapidEndpointPhaseData_interior hP hR k) (rapidEndpointPhaseData_interior hP hR k)
  change halfWeylDistributionCLM (endpointPoissonSynthesis
    (rapidEndpointPhaseData P R k) (rapidEndpointPhaseData P R k) c) f=0
  rw [halfWeyl_rapidEndpointSource_halfCoordinate_pairing hP hR]
  apply Finset.sum_eq_zero
  intro e _
  apply Finset.sum_eq_zero
  intro d _
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  have hh := congrFun hz ((i.val,e),(j.val,d))
  change halfNewtonMoment (endpointPaddedDistance P R k) (endpointPaddedDistance P R k)
    (halfWeylDistributionCLM (endpointFiniteSource P R hP hR k)) i.val e j.val d=0 at hh
  rw [halfNewtonMoment_endpointPadded_prefix P R k i.val j.val (by omega) (by omega)] at hh
  have hc := (halfNewtonMoment_eq_zero_iff _ _ _ _ _ _ _).mp hh
  rw [rapidEndpointHalfCoordinate_eq_actual hP hR]
  change _*halfNewtonCoordinate _ _ (halfWeylDistributionCLM (endpointFiniteSource P R hP hR k)) _ _ _ _=0
  rw [hc,mul_zero]

/-- The entire actual physical array is a vector of the original unweighted
square-summable coefficient space, retaining every index and parity. -/
def endpointFinitePhysicalVector (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) (k : ℕ) :
    CoefficientSpace ((ℕ×Bool)×(ℕ×Bool)) :=
  ⟨endpointFinitePhysicalArray P R hP hR k,
    (memℓp_gen_iff (by norm_num : 0 < (2:ENNReal).toReal)).mpr (by
      simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
        summable_sq_endpointFinitePhysicalArray P R hP hR k)⟩

/-- The complete actual Fourier array is a square-summable vector on the same full space. -/
def endpointFiniteFourierVector (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) (k : ℕ) :
    CoefficientSpace ((ℕ×Bool)×(ℕ×Bool)) :=
  ⟨endpointFiniteFourierArray P R hP hR k,
    (memℓp_gen_iff (by norm_num : 0 < (2:ENNReal).toReal)).mpr (by
      simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
        summable_sq_endpointFiniteFourierArray P R hP hR k)⟩

/-- The full actual finite-source physical vector is nonzero before any corner normalization. -/
theorem endpointFinitePhysicalVector_ne_zero (P R : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R) (k : ℕ) :
    endpointFinitePhysicalVector P R hP hR k ≠ 0 := by
  intro hz
  apply endpointFinitePhysicalArray_ne_zero P R hP hR k
  funext z
  exact congrArg (fun u : CoefficientSpace ((ℕ×Bool)×(ℕ×Bool)) => u z) hz

end MeyerGeneralProblem.Adaptive
