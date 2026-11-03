/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E7LieVacuum
import VOA.DeligneAudit.E7LiePresentation
import VOA.DeligneAudit.E7Divisor
import VOA.DeligneAudit.G2Fusion
import VOA.DeligneAudit.DeligneCharacterExceptional
import VOA.DeligneAudit.DeligneCharacterStarBound

/-!
# The E₇ Deligne case: headline

`L_{-4}(𝔢₇) = W7`, with the explicit presentation `explicitPresentation7` (ideal `I₂ⁿˢ = E7data.I`). The proof
goes through the generic `DeligneCarrier.classicallyFree_of_sectorFusion`, with these inputs:

* `hsurj = explicitCurrentJetSurjectivity7`, `hgeom = explicitGeometricCarrierEmbedding7`
  (`E7sector.toDeligneCarrierData = E7data` holds by `rfl`);
* `hD = e7_divisorComparison` on `E7sector`;
* `hchr = demazureBoundFor_of_Q hstar e7_targetLowerBound`. The target bound is unconditional;
  `E7StarIdentity` (or the `E7StarBound`) is a named input;
* U5 for `fusionOf (hilbSeries e7DemazureHilb)`, a named input.

**`E7Lie.e7_classicallyFree`**: `CaseClassicallyFree .E7 W7 explicitPresentation7 ∧ ker = I₂ⁿˢ`, conditional
on U5 and `E7StarIdentity`.
-/

namespace VOA.DeligneAudit.E7Lie

open VOA.DeligneHigherRankConditionalCapstone VOA.DeligneAudit.DeligneSector VOA.DeligneAudit.DeligneCharacter
open VOA.DeligneAudit.DeligneCarrier
open VOA.DeligneAudit.DeligneCarrier.E7 (E7sector)

/-- **The E₇ Deligne case**, conditional on U5 (the fusion module bound) and the star identity. -/
theorem e7_classicallyFree
    (hU5 : FusionModuleBoundG E7sector (fusionOf (hilbSeries e7DemazureHilb)))
    (hstar : E7StarIdentity) :
    CaseClassicallyFree .E7 W7 explicitPresentation7 ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass W7 1 ⟨explicitPresentation7.gen i,
          explicitPresentation7.gen_weight_one i⟩).toRingHom = explicitPresentation7.ideal :=
  classicallyFree_of_sectorFusion explicitPresentation7 E7sector e7DemazureHilb explicitCurrentJetSurjectivity7
    explicitGeometricCarrierEmbedding7 hU5 DeligneDivisor.E7.e7_divisorComparison
    (demazureBoundFor_of_Q hstar e7_targetLowerBound)

/-- **The E₇ Deligne case, star input in `≤` form**: as `e7_classicallyFree`, with the `E7StarBound`
(`D_N ≤ mldeCoeff 18 N`) in place of `E7StarIdentity`. -/
theorem e7_classicallyFree_of_starBound
    (hU5 : FusionModuleBoundG E7sector (fusionOf (hilbSeries e7DemazureHilb)))
    (hB : E7StarBound) :
    CaseClassicallyFree .E7 W7 explicitPresentation7 ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass W7 1 ⟨explicitPresentation7.gen i,
          explicitPresentation7.gen_weight_one i⟩).toRingHom = explicitPresentation7.ideal :=
  classicallyFree_of_sectorFusion explicitPresentation7 E7sector e7DemazureHilb explicitCurrentJetSurjectivity7
    explicitGeometricCarrierEmbedding7 hU5 DeligneDivisor.E7.e7_divisorComparison
    (e7DemazureBoundFor_of_starBound W7 hB e7_targetLowerBound)

end VOA.DeligneAudit.E7Lie

section AxiomAudit
#print axioms VOA.DeligneAudit.E7Lie.e7_classicallyFree
#print axioms VOA.DeligneAudit.E7Lie.e7_classicallyFree_of_starBound
end AxiomAudit
