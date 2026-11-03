/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.D4Top
import VOA.DeligneAudit.DeligneDivisorD4
import VOA.DeligneAudit.DeligneMLDERamanujanAdapters
import VOA.DeligneAudit.DeligneVacuumRelationD4
import VOA.DeligneAudit.DeligneCharacterD4Wp12

/-!
# D₄ Deligne classical freeness: current headline

The `d4_headline` with the inputs that are theorems plugged in: the divisor comparison
(`DeligneDivisor.D4.d4_divisorComparison`) and Ramanujan's identities
(`D4MLDE.ramanujanIdentities`). `L_{-2}(so₈)` (as `W4 = simpleVOA d4CertData (-2)`) is classically
free for its explicit presentation by the 105 quadrics of `I₂ⁿˢ`, which is the full `C₂` kernel,
given:

* U5 (`FusionModuleBoundG D4sector F`) and U6: Ravinder's fusion results (literature);
* `D4DemazurePositivity`: nonnegativity of the level-one Demazure data (literature, with U7);
* `D4SchurEqE4`: the elliptic evaluation of the Schur index, proved (`D4Wp.d4SchurEqE4`),
  so `classicallyFree_of_fusion` rests on U5, U6 and positivity only;
* (the vacuum quartic relation on `W4` is proved, `vacuumQuarticRelation4`).
-/

namespace VOA.DeligneAudit.D4Lie

open VOA.AffineGeneral VOA.DeligneHigherRankConditionalCapstone VOA.DeligneAudit.DeligneCarrier
  VOA.DeligneAudit.DeligneCharacter VOA.DeligneAudit.DeligneSector.D4
  VOA.DeligneAudit.DeligneSector VOA.DeligneAudit.DeligneMLDE VOA.DeligneAudit.VacuumRelation

/-- **D₄ Deligne classical freeness, current form.** -/
theorem classicallyFree_of_open (F : ℕ → PowerSeries ℚ) (hU5 : FusionModuleBoundG D4sector F)
    (hU6 : MixedFusionRecursion F (hilbSeries d4DemazureHilb))
    (hpos : D4K.D4DemazurePositivity) (hS : D4MLDE.D4SchurEqE4) :
    CaseClassicallyFree .D4 W4 explicitPresentation4 ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass W4 1 ⟨explicitPresentation4.gen i,
          explicitPresentation4.gen_weight_one i⟩).toRingHom = explicitPresentation4.ideal :=
  d4_headline F hU5 DeligneDivisor.D4.d4_divisorComparison hU6 hpos hS
    D4MLDE.ramanujanIdentities vacuumQuarticRelation4

/-- **D₄ Deligne classical freeness from U5, U6 and Demazure positivity.** The Schur-index
evaluation `D4SchurEqE4` is discharged by the elliptic proof `D4Wp.d4SchurEqE4`. -/
theorem classicallyFree_of_fusion (F : ℕ → PowerSeries ℚ) (hU5 : FusionModuleBoundG D4sector F)
    (hU6 : MixedFusionRecursion F (hilbSeries d4DemazureHilb))
    (hpos : D4K.D4DemazurePositivity) :
    CaseClassicallyFree .D4 W4 explicitPresentation4 ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass W4 1 ⟨explicitPresentation4.gen i,
          explicitPresentation4.gen_weight_one i⟩).toRingHom = explicitPresentation4.ideal :=
  classicallyFree_of_open F hU5 hU6 hpos D4Wp.d4SchurEqE4

end VOA.DeligneAudit.D4Lie

section AxiomAudit
#print axioms VOA.DeligneAudit.D4Lie.classicallyFree_of_open
#print axioms VOA.DeligneAudit.D4Lie.classicallyFree_of_fusion
end AxiomAudit
