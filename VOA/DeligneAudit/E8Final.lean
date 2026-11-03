/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneVacuumRelationE8
import VOA.DeligneAudit.E8Presentation
import VOA.DeligneAudit.E8Divisor
import VOA.DeligneAudit.G2Fusion
import VOA.DeligneAudit.DeligneCharacterExceptional
import VOA.DeligneAudit.DeligneCharacterStarBound

/-!
# The E₈ Deligne case: headline

`L_{-6}(𝔢₈) = W8`, with the explicit presentation `explicitPresentation8` (ideal `I₂ⁿˢ = E8data.I`). The proof
goes through the generic `DeligneCarrier.classicallyFree_of_sectorFusion` (mirroring the `E7Final`), with
these inputs:

* `hsurj = explicitCurrentJetSurjectivity8`, `hgeom = explicitGeometricCarrierEmbedding8`
  (`E8sector.toDeligneCarrierData = E8data` holds by `rfl`);
* `hD = e8_divisorComparison` on `E8sector`;
* `hchr = demazureBoundFor_of_Q hstar targetLowerBoundQ8`. The target bound is unconditional;
  `E8StarIdentity` (or the `E8StarBound`) is a named input;
* U5 for `fusionOf (hilbSeries e8DemazureHilb)`, a named input.

**`E8Lie.e8_classicallyFree`**: `CaseClassicallyFree .E8 W8 explicitPresentation8 ∧ ker = I₂ⁿˢ`, conditional
on U5 and `E8StarIdentity`.  Signatures frozen (consumed by the `E8FusionKernel*`).
-/

namespace VOA.DeligneAudit.E8Lie

open VOA.DeligneHigherRankConditionalCapstone VOA.DeligneAudit.DeligneSector VOA.DeligneAudit.DeligneCharacter
open VOA.DeligneAudit.DeligneCarrier
open VOA.DeligneAudit.DeligneCarrier.E8 (E8sector)

/-- **The E₈ Deligne case**, conditional on U5 (the fusion module bound) and the star identity. -/
theorem e8_classicallyFree
    (hU5 : FusionModuleBoundG E8sector (fusionOf (hilbSeries e8DemazureHilb)))
    (hstar : E8StarIdentity) :
    CaseClassicallyFree .E8 W8 explicitPresentation8 ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass W8 1 ⟨explicitPresentation8.gen i,
          explicitPresentation8.gen_weight_one i⟩).toRingHom = explicitPresentation8.ideal :=
  classicallyFree_of_sectorFusion explicitPresentation8 E8sector e8DemazureHilb explicitCurrentJetSurjectivity8
    explicitGeometricCarrierEmbedding8 hU5 DeligneDivisor.E8.e8_divisorComparison
    (demazureBoundFor_of_Q hstar targetLowerBoundQ8)

/-- **The E₈ Deligne case, star input in `≤` form**: as `e8_classicallyFree`, with the `E8StarBound`
(`D_N ≤ mldeCoeff 30 N`) in place of `E8StarIdentity`. -/
theorem e8_classicallyFree_of_starBound
    (hU5 : FusionModuleBoundG E8sector (fusionOf (hilbSeries e8DemazureHilb)))
    (hB : E8StarBound) :
    CaseClassicallyFree .E8 W8 explicitPresentation8 ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass W8 1 ⟨explicitPresentation8.gen i,
          explicitPresentation8.gen_weight_one i⟩).toRingHom = explicitPresentation8.ideal :=
  classicallyFree_of_sectorFusion explicitPresentation8 E8sector e8DemazureHilb explicitCurrentJetSurjectivity8
    explicitGeometricCarrierEmbedding8 hU5 DeligneDivisor.E8.e8_divisorComparison
    (e8DemazureBoundFor_of_starBound W8 hB targetLowerBoundQ8)

end VOA.DeligneAudit.E8Lie

section AxiomAudit
#print axioms VOA.DeligneAudit.E8Lie.e8_classicallyFree
#print axioms VOA.DeligneAudit.E8Lie.e8_classicallyFree_of_starBound
end AxiomAudit
