module

public import MeyerGeneralProblem.Distribution.FourthOrderHoleVector

@[expose] public section

/-!
# Actual square cyclic Fourier eigenvectors with central zeros

The normalized cyclic DFT has square equal to reflection and fourth power
identity. Its actual finite orbit constraints therefore give a nonzero
fourth-root eigenvector vanishing on fewer than a quarter of the coordinates.
The finite-dimensional construction does not yet assert an infinite comb.
-/

namespace MeyerGeneralProblem

noncomputable section

/-- The actual negative-phase cyclic Fourier map with square-size unitary
normalization 1/m, rather than the unnormalized counting-measure transform. -/
def squareCyclicDFT (m : ℕ) [NeZero m] :
    Module.End ℂ (ZMod (m*m) → ℂ) :=
  (m:ℂ)⁻¹ • (ZMod.dft (N := m*m)).toLinearMap

/-- Exact twice-applied normalized Fourier transform is coordinate reflection. -/
theorem squareCyclicDFT_twice (m : ℕ) [NeZero m] (c : ZMod (m*m) → ℂ) :
    squareCyclicDFT m (squareCyclicDFT m c) = fun j => c (-j) := by
  change (m:ℂ)⁻¹ • ZMod.dft ((m:ℂ)⁻¹ • ZMod.dft c) = _
  rw [ZMod.dft_const_smul, ZMod.dft_dft]
  funext j
  simp only [Pi.smul_apply, smul_eq_mul, Nat.cast_mul]
  have hm : (m:ℂ) ≠ 0 := by exact_mod_cast NeZero.ne m
  field_simp [hm]

/-- The genuine normalized square cyclic DFT has fourth power identity. -/
theorem squareCyclicDFT_pow_four (m : ℕ) [NeZero m] :
    squareCyclicDFT m ^ 4 = 1 := by
  apply LinearMap.ext
  intro c
  change squareCyclicDFT m (squareCyclicDFT m
    (squareCyclicDFT m (squareCyclicDFT m c))) = c
  rw [squareCyclicDFT_twice, squareCyclicDFT_twice]
  simp

/-- The actual first q cyclic coordinates, preserving their original order. -/
def initialCyclicCoordinates (m q : ℕ) :
    (ZMod (m*m) → ℂ) →ₗ[ℂ] (Fin q → ℂ) where
  toFun c j := c (j.val : ZMod (m*m))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- A genuine cyclic Fourier eigenvector with all requested initial zeros,
derived from the actual Fourier inversion identity and finite rank-nullity. -/
theorem exists_squareCyclicDFT_eigenvector_zeros (m q : ℕ) [NeZero m]
    (hq : 4*q < m*m) :
    ∃ (a : Fin 4) (c : ZMod (m*m) → ℂ),
      c ≠ 0 ∧ squareCyclicDFT m c = fourthRootValue a • c ∧
        ∀ j : Fin q, c (j.val : ZMod (m*m)) = 0 := by
  obtain ⟨a,c,hc,he,hz⟩ := exists_fourthRoot_eigenvector_constraint_zero
    (squareCyclicDFT m) (squareCyclicDFT_pow_four m) (initialCyclicCoordinates m q)
    (by simpa using hq)
  exact ⟨a,c,hc,he,fun j => congrFun hz j⟩


/-- Normalize a genuine finite Fourier eigenvector at a largest coefficient:
one coefficient is exactly one, every coefficient has norm at most one,
and the actual Fourier equation and initial zeros are preserved. -/
theorem exists_squareCyclicDFT_unit_eigenvector (m q : ℕ) [NeZero m]
    (hq : 4*q < m*m) :
    ∃ (a : Fin 4) (c : ZMod (m*m) → ℂ) (r : ZMod (m*m)),
      c r = 1 ∧ (∀ j, ‖c j‖ ≤ 1) ∧
      squareCyclicDFT m c = fourthRootValue a • c ∧
      ∀ j : Fin q, c (j.val : ZMod (m*m)) = 0 := by
  classical
  obtain ⟨a,c,hc,he,hz⟩ := exists_squareCyclicDFT_eigenvector_zeros m q hq
  obtain ⟨r,_hr,hr⟩ := Finset.exists_max_image Finset.univ
    (fun j : ZMod (m*m) => ‖c j‖) Finset.univ_nonempty
  have hcr : c r ≠ 0 := by
    intro hzero
    apply hc
    funext j
    apply norm_eq_zero.mp
    exact le_antisymm (by simpa [hzero] using hr j (Finset.mem_univ j)) (norm_nonneg _)
  let b : ZMod (m*m) → ℂ := (c r)⁻¹ • c
  refine ⟨a,b,r,?_,?_,?_,?_⟩
  · simp [b,smul_eq_mul,hcr]
  · intro j
    change ‖(c r)⁻¹ * c j‖ ≤ 1
    rw [norm_mul,norm_inv,← div_eq_inv_mul]
    exact (div_le_one (norm_pos_iff.mpr hcr)).mpr (hr j (Finset.mem_univ j))
  · dsimp only [b]
    rw [map_smul,he,smul_comm]
  · intro j
    simp [b,hz j,smul_eq_mul]

/-- Number of initial zeros leaving a strict four-orbit rank surplus. -/
def squareCyclicCentralZeroCount (m : ℕ) : ℕ := (m*m+3)/4-1

/-- The chosen central zero count leaves at least one finite Fourier degree
of freedom, rather than relying on an assumed DFT eigenspace dimension. -/
theorem four_mul_squareCyclicCentralZeroCount_lt {m : ℕ} (hm : 1 ≤ m) :
    4*squareCyclicCentralZeroCount m < m*m := by
  have hpos : 0 < m*m := Nat.mul_pos (by omega) (by omega)
  unfold squareCyclicCentralZeroCount
  omega

/-- For every positive square size, actual normalized Fourier eigenvectors
exist with the full prescribed central-zero count and a genuine unit atom. -/
theorem exists_squareCyclicDFT_centralHole_vector (m : ℕ) [NeZero m] :
    ∃ (a : Fin 4) (c : ZMod (m*m) → ℂ) (r : ZMod (m*m)),
      c r = 1 ∧ (∀ j, ‖c j‖ ≤ 1) ∧
      squareCyclicDFT m c = fourthRootValue a • c ∧
      ∀ j : Fin (squareCyclicCentralZeroCount m), c (j.val : ZMod (m*m)) = 0 :=
  exists_squareCyclicDFT_unit_eigenvector m _
    (four_mul_squareCyclicCentralZeroCount_lt (Nat.pos_of_ne_zero (NeZero.ne m)))


/-- The actual square-DFT eigenrelation forces the exact reflected
coefficient relation, and hence reflects every prescribed zero. -/
theorem squareCyclicDFT_eigen_neg (m : ℕ) [NeZero m]
    {c : ZMod (m*m) → ℂ} {ζ : ℂ} (hc : squareCyclicDFT m c = ζ • c)
    (j : ZMod (m*m)) : c (-j) = ζ^2*c j := by
  calc
    c (-j) = squareCyclicDFT m (squareCyclicDFT m c) j :=
      (congrFun (squareCyclicDFT_twice m c) j).symm
    _ = ζ^2*c j := by
      rw [hc,map_smul,hc]
      simp [Pi.smul_apply,smul_eq_mul,pow_two,mul_assoc]

/-- Initial and reflected zeros cover every integer of absolute value
below the actual finite zero count, including the origin. -/
theorem squareCyclicDFT_integer_zero (m q : ℕ) [NeZero m]
    {c : ZMod (m*m) → ℂ} {ζ : ℂ} (hc : squareCyclicDFT m c = ζ • c)
    (hz : ∀ j : Fin q, c (j.val : ZMod (m*m)) = 0)
    {j : ℤ} (hj : j.natAbs < q) : c (j : ZMod (m*m)) = 0 := by
  cases j with
  | ofNat n => simpa using hz ⟨n,hj⟩
  | negSucc n =>
    have hh : c ((n : ZMod (m*m))+1) = 0 := by simpa using hz ⟨n+1,hj⟩
    have he := squareCyclicDFT_eigen_neg m hc ((n+1:ℕ) : ZMod (m*m))
    simpa [hh] using he

/-- The actual finite zero count yields a linearly growing physical hole. -/
theorem squareCyclicCentralZeroCount_radius (m : ℕ) [NeZero m] :
    (m:ℝ)/4-1 ≤ (squareCyclicCentralZeroCount m:ℝ)/m := by
  have hm : 1 ≤ m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hn : 0 < m*m := Nat.mul_pos (by omega) (by omega)
  have hq : m*m ≤ 4*(squareCyclicCentralZeroCount m+1) := by
    unfold squareCyclicCentralZeroCount
    omega
  have hmR : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hqR : (m:ℝ)*(m:ℝ) ≤ 4*((squareCyclicCentralZeroCount m:ℝ)+1) := by
    exact_mod_cast hq
  apply (le_div_iff₀ (by positivity : (0:ℝ)<m)).mpr
  nlinarith

/-- The periodic lattice coefficients vanish on the genuine open physical
hole, with its radius growing as m/4-1. No support certificate is assumed. -/
theorem squareCyclicDFT_physical_hole (m : ℕ) [NeZero m]
    {c : ZMod (m*m) → ℂ} {ζ : ℂ} (hc : squareCyclicDFT m c = ζ • c)
    (hz : ∀ j : Fin (squareCyclicCentralZeroCount m), c (j.val : ZMod (m*m)) = 0)
    {j : ℤ} (hj : |(j:ℝ)/(m:ℝ)| < (m:ℝ)/4-1) :
    c (j : ZMod (m*m)) = 0 := by
  apply squareCyclicDFT_integer_zero m _ hc hz
  have hm : (0:ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  have h := hj.trans_le (squareCyclicCentralZeroCount_radius m)
  rw [abs_div,abs_of_pos hm] at h
  have hnat : (j.natAbs:ℝ) < (squareCyclicCentralZeroCount m:ℝ) := by
    simpa using (div_lt_div_iff_of_pos_right hm).mp h
  exact_mod_cast hnat

/-- A distinguished finite residue always occurs in the first physical
period, so unit normalization supplies a nonzero coefficient at linear radius. -/
theorem squareCyclic_residue_mem_first_period (m : ℕ) [NeZero m] (r : ZMod (m*m)) :
    (r.val:ℝ)/(m:ℝ) ∈ Set.Ico 0 (m:ℝ) := by
  have hm : (0:ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  refine ⟨by positivity, (div_lt_iff₀ hm).mpr ?_⟩
  exact_mod_cast ZMod.val_lt r

end

end MeyerGeneralProblem
