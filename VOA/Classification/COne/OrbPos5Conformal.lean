import VOA.Classification.COne.OrbPos5Fields

/-! # The actual conformal mode of the constructed fractional field map -/

namespace VOA.Classification.COne.OrbPos5
open VOA VOA.IntegralLattice VOA.LatGen VOA.LatGen.Triplet VOA.HeisenbergN
open OrbPos2 OrbPos3 OrbPos4 LatMod
open scoped TensorProduct

theorem hVec_eq_latState :
    hVec (latP 1) (a0 1) = latStateGen (latP 1)
      (MvPolynomial.X (0, a0 1)) 0 := by
  simp [hVec, latVacuumGen, latStateGen, LinearMap.rTensor_tmul, currentN_apply,
    mulXN, vacuumN]

theorem coefficientField_integral {n : ℕ} (hn : 0 < n) (a j k : ℤ)
    (d : ℕ) (p : Osc) :
    coefficientField n a j 0 d p ((n : ℤ)*k) =
      mode ((latticeModule 1 le_rfl j).YM (latStateGen (latP 1) p 0)) (k-d) := by
  have hn0 : (n : ℤ) ≠ 0 := by omega
  simp only [coefficientField, LinearMap.coe_mk, AddHom.coe_mk, mul_zero, sub_zero,
    Int.mul_emod_right, ite_true, Int.mul_ediv_cancel_left _ hn0]
  rfl

/-- The field map's actual conformal mode is precisely the shifted energy
operator constructed in `OrbPos3`. No Jacobi hypothesis enters. -/
theorem shiftedY_conformal {n : ℕ} (hn : 0 < n) (a j : ℤ) :
    shiftedY n a j (V2m 1 le_rfl).conformalVector n = energyOperator n a j := by
  change shiftedY n a j (latStateGen (latP 1) (ωN (rank (latP 1)) 1) 0) n = _
  rw [shiftedY_latState]
  change ((Finsupp.lsum ℂ (coefficientField n a j 0))
    (deltaCoeffs ((a : ℂ)/(2*n)) (ωN (rank (latP 1)) 1))) n = _
  rw [deltaCoeffs_omega, map_add, map_add, Finsupp.lsum_single,
    Finsupp.lsum_single, Finsupp.lsum_single]
  simp only [Pi.add_apply, map_smul, Pi.smul_apply]
  rw [show (n : ℤ) = (n : ℤ)*1 by ring]
  rw [coefficientField_integral hn, coefficientField_integral hn,
    coefficientField_integral hn]
  norm_num only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, sub_zero,
    sub_self, show (1 : ℤ)-2 = -1 by omega]
  rw [← hVec_eq_latState]
  change mode ((latticeModule 1 le_rfl j).YM (V2m 1 le_rfl).conformalVector) 1 +
      (-((a : ℂ)/(2*n)) * rootCoord) •
        mode ((latticeModule 1 le_rfl j).YM (hVec (latP 1) (a0 1))) 0 +
      ((a : ℂ)/(2*n))^2 • mode ((latticeModule 1 le_rfl j).YM (V2m 1 le_rfl).vacuum) (-1)
      = _
  rw [(latticeModule 1 le_rfl j).vacuum_YM, mode_one]
  simp only [ite_true]
  rw [energyOperator, shiftedL0, charge_eq_root_zeroMode]
  dsimp [rootCoord]
  module

/-- Completed-square energy on every homogeneous oscillator-and-charge state. -/
theorem shiftedY_L0_latState {n : ℕ} (hn : 0 < n) (a j k : ℤ) {r : ℕ}
    {p : Osc} (hp : p ∈ gradingWN (rank (latP 1)) r) :
    shiftedY n a j (V2m 1 le_rfl).conformalVector n (latStateGen (latP 1) p k) =
      (innerEnergy n a j k r : ℂ) • latStateGen (latP 1) p k := by
  rw [shiftedY_conformal hn]
  exact energyOperator_latState n a j k hp

/-- Positive shifts use the negated numerator in the repository convention.
The corresponding torus automorphism is therefore `shiftAut n (-a)`. -/
theorem shiftedY_positiveShift_L0 {n : ℕ} (hn : 0 < n) (a j k : ℤ) {r : ℕ}
    {p : Osc} (hp : p ∈ gradingWN (rank (latP 1)) r) :
    shiftedY n (-a) j (V2m 1 le_rfl).conformalVector n (latStateGen (latP 1) p k) =
      (((k : ℂ) + j/2 + a/(2*n))^2 + r) • latStateGen (latP 1) p k := by
  rw [shiftedY_L0_latState hn (-a) j k hp]
  congr 1
  simp only [innerEnergy]
  push_cast
  ring

/-- All grading axioms, for the actual conformal mode of `shiftedY`. -/
theorem shiftedY_ordinaryGrading {n : ℕ} (hn : 0 < n) (a j : ℤ) :
    DirectSum.IsInternal (energyGrade n a j) ∧
    (∀ α, FiniteDimensional ℂ (energyGrade n a j α)) ∧
    (∀ α x, x ∈ energyGrade n a j α →
      shiftedY n a j (V2m 1 le_rfl).conformalVector n x = α • x) ∧
    (∀ α, energyGrade n a j α ≠ ⊥ → 0 ≤ α.re) := by
  rw [shiftedY_conformal hn]
  exact shiftedLattice_ordinaryGrading hn a j

end VOA.Classification.COne.OrbPos5
