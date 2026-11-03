import VOA.Huang.GenusTwoPointSepVirasoroFlow

/-!
# Vacuum and conformal-state normalization

The conformal vector is sent to omega - c/24 by the actual exponential,
not by a definition. Consequently the module energy law isolated in
`GenusTwoPointSepZeroConjugation` is necessary for the original target.
-/
noncomputable section
namespace VOA.Huang.GenusTwoPoint.Separate
open VOA GenusOne
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

theorem coordGen_vacuum (c : ℕ → ℂ) : coordGen W c W.vacuum = 0 := by
  have h := coordGen_mem_gradeLE W c
    (mem_gradeLE_of_mem_grading W le_rfl W.vacuum_mem_grading_zero)
  rw [gradeLE_eq_bot W (by norm_num : (0 : ℤ) - 1 < 0)] at h
  exact h

theorem coordGen_conformalVector (c : ℕ → ℂ) :
    coordGen W c W.conformalVector = (c 1 * (W.centralCharge / 2)) • W.vacuum := by
  rw [coordGen_apply, finsum_eq_single _ 1]
  · norm_num only [Nat.cast_one, show (1 + 1 : ℤ) = 2 from rfl]
    rw [L_two_conformalVector, smul_smul]
  · intro j hj
    by_cases hj0 : j = 0
    · subst j
      simp only [Nat.cast_zero, zero_add, L1_conformal_zero, smul_zero]
    · have hz : W.L ((j : ℤ) + 1) W.conformalVector = 0 := by
        have h := L_mem_grading W W.conformal_mem ((j : ℤ) + 1)
        rw [W.positivity _ (by omega), Submodule.mem_bot] at h
        exact h
      rw [hz, smul_zero]

@[simp] theorem normalizedStateChange_vacuum :
    normalizedStateChange W W.vacuum = W.vacuum :=
  changeCoord_of_apply_eq_zero W _ (coordGen_vacuum _)

/-- The Schwarzian correction, verified from the logarithmic generator. -/
theorem normalizedStateChange_conformalVector :
    normalizedStateChange W W.conformalVector =
      W.conformalVector - (W.centralCharge / 24) • W.vacuum := by
  let c : ℕ → ℂ := fun j => -iterativeLog (logarithmicCoordinate 1) j
  have hc : c 1 = -(1 / 12 : ℂ) := by
    norm_num [c, iterativeLog_one, logarithmicCoordinate]
  have htwo : (coordGen W c ^ 2) W.conformalVector = 0 := by
    rw [pow_two, Module.End.mul_apply, coordGen_conformalVector,
      map_smul, coordGen_vacuum, smul_zero]
  change expFun (coordGen_isLocNilp W c) W.conformalVector = _
  rw [expFun_eq_expSum _ htwo, expSum]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, inv_one, one_smul,
    pow_zero, Module.End.one_apply, pow_one]
  rw [coordGen_conformalVector, hc]
  module

/-- The normalized conformal vector really has square weight two. -/
theorem normalizedStateChange_conformal_weight :
    Lsq W 0 (normalizedStateChange W W.conformalVector) =
      (2 : ℂ) • normalizedStateChange W W.conformalVector := by
  rw [normalizedStateChange_conformalVector]
  exact SquareModule.shiftedOmega_weight

/-- The vacuum insertion case of the unchanged target is unconditional. -/
theorem normalizedSquareConjugation_vacuum (P : LWModule W) (m : ℤ) (x : P.carrier) :
    normalizedCoordinateChange P (mode (P.isMod.YM W.vacuum) m x) =
      SquareModule.sqMode P.isMod m (normalizedStateChange W W.vacuum)
        (normalizedCoordinateChange P x) := by
  rw [normalizedStateChange_vacuum,
    SquareModule.sqMode_of_mem_grading P.isMod W.vacuum_mem_grading_zero]
  simp only [Int.toNat_zero, SquareModule.sqAct_vacuum, P.isMod.vacuum_YM, mode_one]
  split_ifs <;> simp

/-- The energy residual is an actual special case, not a stronger module assumption. -/
theorem normalizedModuleZeroConjugation_of_square (P : LWModule W)
    (hP : NormalizedSquareConjugation P) : NormalizedModuleZeroConjugation P := by
  intro x
  have h := hP W.conformalVector 1 x
  rw [normalizedStateChange_conformalVector] at h
  exact (h.trans (congrArg (fun f : Module.End ℂ P.carrier =>
    f (normalizedCoordinateChange P x)) (SquareModule.sqMode_shiftedOmega P.isMod 0))).symm

/-- With the state energy law supplied, the module energy law is precisely
equivalent to the original all-mode target. -/
theorem normalizedSquareConjugation_iff_zero (P : LWModule W)
    (hV : NormalizedStateZeroConjugation W) :
    NormalizedSquareConjugation P ↔ NormalizedModuleZeroConjugation P :=
  ⟨normalizedModuleZeroConjugation_of_square P,
    normalizedSquareConjugation_of_zero P hV⟩

end VOA.Huang.GenusTwoPoint.Separate
