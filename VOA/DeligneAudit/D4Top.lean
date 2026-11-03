/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.D4LieTop
import VOA.DeligneAudit.DeligneSectorD4
import VOA.DeligneAudit.D4CharacterTop
import VOA.DeligneAudit.DeligneCharacterD4MLDE
import VOA.DeligneAudit.DeligneMLDETypes

/-!
# The `D₄` headline on `L_{-2}(𝔰𝔬₈)`

`d4_headline`: the `D₄` Deligne case on `W4 = simpleVOA d4CertData (-2)` (explicit presentation by the
105 cert relations `I₂ⁿˢ`; classical freeness and `ker = I₂ⁿˢ`), with hypotheses exactly the open
inputs:

* U5 `FusionModuleBoundG D4sector F` and U6 `MixedFusionRecursion F (hilbSeries d4DemazureHilb)`;
* `DivisorComparisonG D4sector`;
* `D4DemazurePositivity` (literature, next to U7), `D4SchurEqE4` (the Schur index is `E₄′/(240η¹⁰)`);
* `RamanujanIdentities`;
* `VacuumQuarticRelation W4 κ` (the weight-four vacuum relation on `W4`).

Discharged here: the central charge `c(W4) = -14 = -2(6+1)` and `|0⟩ ≠ 0` in `W4`; chain:
quartic relation ⟹ `TargetLowerBoundQ W4 (mldeCoeff 6)` ⟹ class S (via the MLDE) ⟹
`DemazureBoundFor` (with the finite identity proved) ⟹ carrier character bound ⟹ headline.
-/

namespace VOA.DeligneAudit.D4Lie

open VOA.AffineGeneral VOA.DeligneHigherRankConditionalCapstone VOA.DeligneAudit.DeligneCarrier
  VOA.DeligneAudit.DeligneCharacter VOA.DeligneAudit.DeligneSector.D4
  VOA.DeligneAudit.DeligneSector VOA.DeligneAudit.DeligneMLDE

noncomputable section

/-- `c(L_{-2}(𝔰𝔬₈)) = 28·(-2)/(-2+6) = -14`. -/
theorem W4_centralCharge : W4.centralCharge = -2 * (((6 : ℕ) : ℂ) + 1) := by
  show centralChargeA d4CertData (-2) = _
  rw [centralChargeA, d4CertData_h, Fintype.card_fin]
  norm_num

theorem W4_vacuum_ne_zero : W4.vacuum ≠ 0 :=
  SimpleQuot.maxQuotientVOA_vacuum_ne_zero _ (vacuumA_ne_zero d4CertData (-2))

/-- **The `D₄` character side on `W4`** from Demazure positivity, the Schur/`E₄` identity, the
Ramanujan identities and the vacuum quartic relation. -/
theorem W4_demazureBound (hpos : D4K.D4DemazurePositivity) (hS : D4MLDE.D4SchurEqE4)
    (hR : D4MLDE.RamanujanIdentities) {κ : ℂ} (hrel : VacuumQuarticRelation W4 κ) :
    DemazureBoundFor W4 d4DemazureHilb :=
  d4DemazureBound_of_literature W4 hpos
    (D4MLDE.d4ClassS_of_mlde W4 hS hR
      (d4_targetLowerBoundQ_of_quartic W4 W4_centralCharge W4_vacuum_ne_zero hrel).le)

/-- **The `D₄` Deligne headline on `L_{-2}(𝔰𝔬₈)`**, conditional exactly on the open inputs. -/
theorem d4_headline (F : ℕ → PowerSeries ℚ) (hU5 : FusionModuleBoundG D4sector F)
    (hD : DivisorComparisonG D4sector) (hU6 : MixedFusionRecursion F (hilbSeries d4DemazureHilb))
    (hpos : D4K.D4DemazurePositivity) (hS : D4MLDE.D4SchurEqE4) (hR : D4MLDE.RamanujanIdentities)
    {κ : ℂ} (hrel : VacuumQuarticRelation W4 κ) :
    CaseClassicallyFree .D4 W4 explicitPresentation4 ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass W4 1 ⟨explicitPresentation4.gen i,
          explicitPresentation4.gen_weight_one i⟩).toRingHom = explicitPresentation4.ideal :=
  d4_classicallyFree_of_sector F (D4_sectorFusionBound F hU5 hD) hU6
    (W4_demazureBound hpos hS hR hrel)

end

end VOA.DeligneAudit.D4Lie

section AxiomAudit
#print axioms VOA.DeligneAudit.D4Lie.W4_centralCharge
#print axioms VOA.DeligneAudit.D4Lie.W4_demazureBound
#print axioms VOA.DeligneAudit.D4Lie.d4_headline
end AxiomAudit
