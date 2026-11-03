import VOA.DeligneAudit.D4FusionRealizationTwoGradedRanks
import VOA.DeligneAudit.D4FusionRealizationCharacterTwo
import VOA.DeligneAudit.DeligneFusionD1TensorGGrSat
import VOA.DeligneAudit.DeligneCharacterD4Positivity
import VOA.DeligneAudit.D4FusionKernelGeneric

/-! The actual n=2 D4 Demazure realization: original relations and all coefficients. -/
namespace VOA.DeligneAudit.D4Two
open PowerSeries VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.D1TensorG.Gr VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.DeligneCharacter
noncomputable section

/-- The original Ravinder relations hold in the constructed graded source. -/
theorem source_ravFam_sat :
    Sat actualTwoF (grRep sourceRep sourceGenerator) (wg sourceRep sourceGenerator)
      (ravFam D4sector 2 0) := by
  change Sat actualTwoF (grRep sourceRep sourceGenerator) (wg sourceRep sourceGenerator)
    (tensorSpec D4sector 2)
  exact tensor_gr_sat D4sector D1SiteG.D4Check.table_skewC twoPoints

/-- A generic multiplicity variable keeps the closed algorithm opaque. -/
theorem hilbInt_integerCoeff (m N : ℕ) :
    D4K.hilbInt m N = D4CharacterTwo.integerCoeff
      (demazureChar cartanD4 thetaD4 wordD4 m) ((m : ℤ)*m) N := by
  unfold D4K.hilbInt D4CharacterTwo.integerCoeff
  rfl

theorem hilbInt_two (N : ℕ) : D4K.hilbInt 2 N = (gradedRank N : ℤ) := by
  have hc : D4CharacterTwo.integerCoeff (demazureChar cartanD4 thetaD4 wordD4 2) 4 N =
      D4CharacterTwo.profile N := D4CharacterTwo.charTwo_coeff N
  rw [hilbInt_integerCoeff 2 N]
  change D4CharacterTwo.integerCoeff (demazureChar cartanD4 thetaD4 wordD4 2) 4 N = _
  rw [hc]
  rcases N with _ | _ | _ | _ | _ | N <;> rfl

theorem series_two_coeff (N : ℕ) :
    coeff N (D4Wp.hilbSeriesZ 2) = (gradedRank N : ℚ) := by
  rw [D4Wp.hilbSeriesZ,coeff_mk,hilbInt_two]
  simp only [Int.cast_natCast]

/-- The named original D4 n=2 realization input, with no mathematical premise. -/
theorem demazureRealization_two :
    DemazureRealizationG D4sector (ravFam D4sector) D4Wp.hilbSeriesZ 2 := by
  refine ⟨cyclicGr sourceRep sourceGenerator,inferInstance,inferInstance,
    cyclicRep sourceRep sourceGenerator,cyclicGenerator sourceRep sourceGenerator,?_,?_⟩
  · exact cyclicRep_sat sourceRep sourceGenerator source_ravFam_sat
  · intro N
    rw [series_two_coeff]
    exact le_of_eq (congrArg (fun k : ℕ => (k : ℚ)) (cyclic_graded_ranks N).symm)

end
#print axioms source_ravFam_sat
#print axioms hilbInt_two
#print axioms demazureRealization_two
end VOA.DeligneAudit.D4Two
