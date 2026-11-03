import VOA.Huang.DLNSchur6Local

/-! # Completion of the large-prime root relations

Both residuals of `DLNSchur5Relations` are theorems. Only the separate powers-of-three
and powers-of-two inputs remain in the DLN assembly below.
-/

namespace VOA.Huang.DLNSchur

/-- All lower transitions, including the genuine prime-power chart boundaries. -/
theorem largePrimeGaussLowerRelations : LargePrimeGaussLowerRelations := by
  intro p k hp hp5 hk E _ π hs hc X Y hX hY hgen hn g
  have hz := torusDefect_eq_one_primePower hp hp5 hk π hs hc X Y hX hY hgen hn
  have hm := gaussLift_mul_primePower_of_defect_eq_one hp hk
    (primePower_coprime_two_three hp hp5).1 (primePower_coprime_two_three hp hp5).2
    π hs X Y hX hY hn hz
  have hy : gaussLift X Y (lowerRoot (1 : ZMod (p ^ k))) =
      Y (Multiplicative.ofAdd 1) := by
    simpa using gaussLift_lower_torus_upper X Y (1 : ZMod (p ^ k)) 0 1
  rw [hm, hy]

theorem largePrimeGaussBoundaryRelations : LargePrimeGaussBoundaryRelations := by
  intro p k hp hp5 hk E _ π hs hc X Y hX hY hgen hn g _
  exact largePrimeGaussLowerRelations p k hp hp5 hk E π hs hc X Y hX hY hgen hn g

/-- `LargePrimeGaussBoundaryRelationsHigher`, unconditionally. -/
theorem largePrimeGaussBoundaryRelationsHigher : LargePrimeGaussBoundaryRelationsHigher := by
  intro p k hp hp5 hk
  exact largePrimeGaussBoundaryRelations p k hp hp5 (by omega)

/-- The full large-prime root-relation family, through the proved equivalence. -/
theorem largePrimeRootRelations : LargePrimeRootRelations :=
  largePrimeRootRelations_iff_mod_four_three_and_higher_boundary.mpr
    ⟨largePrimeTorusGeneratorRelationsModFourThree, largePrimeGaussBoundaryRelationsHigher⟩

/-- Prime-power Schur triviality for every prime at least five. -/
theorem schurTrivial_SL_primePower_large {p k : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k) :
    VOA.Huang.DLNBeyl.SchurTrivial
      (Matrix.SpecialLinearGroup (Fin 2) (ZMod (p ^ k))) :=
  schurTrivial_of_gaussLowerRelations hp hk
    (primePower_coprime_two_three hp hp5).1 (primePower_coprime_two_three hp hp5).2
    (largePrimeGaussLowerRelations p k hp hp5 hk)

/-- Only the powers-of-three family remains in the odd-prime-power theorem. -/
theorem oddPrimePowerSchur_iff_threePowerSchur :
    VOA.Huang.DLNBeyl.OddPrimePowerSchur ↔ ThreePowerSchur := by
  rw [oddPrimePowerSchur_iff_rootRelations_and_three]
  exact ⟨And.right, fun h => ⟨largePrimeRootRelations, h⟩⟩

/-- Assembly with precisely the two small-prime obligations handled separately. -/
theorem matrixDLNLifting_of_session6_remaining
    (hthree : ThreePowerSchur) (htwo : TwoPowerInflationFromTwo) :
    VOA.Huang.DLNBridge.MatrixDLNLifting :=
  matrixDLNLifting_of_rootRelations largePrimeRootRelations hthree htwo

end VOA.Huang.DLNSchur
