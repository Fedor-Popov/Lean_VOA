import VOA.Classification.COne.OrbC2hResult
import VOA.Classification.COne.OrbC2hVirSums
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2b OrbC2c OrbC2e OrbC2f OrbC2g LatMod

/-- The complete state decompositions, including every error coefficient. -/
theorem cubicFiniteVirasoroCertificates : CubicFiniteVirasoroCertificates := by
  have h20 := normalizedNine_weight20_state.trans
    ((congrArg evaluate (by decide +kernel : twentyData = virData20)).trans virData20_value)
  have h22 := normalizedNine_weight22_state.trans
    ((congrArg evaluate (by decide +kernel : twentyTwoData = virData22)).trans virData22_value)
  constructor
  · exact remainder_of_full_sum _ _ _ _ _ _ _ _ _ _
      (plus_self_eq_of_lattice_sum _ _ _ h20)
  · exact remainder_of_full_sum _ _ _ _ _ _ _ _ _ _
      (plus_self_eq_of_lattice_sum _ _ _ h22)

theorem cubicSeedRemaindersCorrected : CubicSeedRemaindersCorrected :=
  corrected_of_finiteVirasoroCertificates cubicFiniteVirasoroCertificates

theorem tetrahedralModeDecomposition : TetrahedralModeDecomposition :=
  tetrahedralModeDecomposition_of_corrected cubicSeedRemaindersCorrected

/-- The quotient-level existential statement retains its original constants.
The negated statement fixes normalizedNine before taking the quotient. -/
theorem tetrahedralDongJiangRelations : OrbC2b.TetrahedralDongJiangRelations :=
  OrbC2c.tetrahedralDongJiangRelations_of_modeDecomposition tetrahedralModeDecomposition
end VOA.Classification.COne.OrbC2h
