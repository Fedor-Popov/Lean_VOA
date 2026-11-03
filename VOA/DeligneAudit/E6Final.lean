/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E6Vacuum
import VOA.DeligneAudit.E6Divisor
import VOA.DeligneAudit.G2Fusion
import VOA.DeligneAudit.DeligneCharacterExceptional
import VOA.DeligneAudit.DeligneCharacterStarBound

/-!
# The E₆ Deligne case: headline

`L_{-3}(𝔢₆) = W6` with the explicit presentation (`E6.explicitPresentation`, ideal `I₂ⁿˢ = E6data.I`), through the
generic `DeligneCarrier.classicallyFree_of_sectorFusion`:

* `hsurj = explicitCurrentJetSurjectivity`, `hgeom = geometricCarrierEmbedding` (step E3 of the `E₆` construction);
* `hD = e6_divisorComparison` (on the `E6sector`);
* `hchr = demazureBoundFor_of_Q hstar e6_targetLowerBound` (the target bound is unconditional; `E6StarIdentity`
  is the named input);
* U5 for `fusionOf (hilbSeries e6DemazureHilb)`: named input.

**`E6.e6_classicallyFree`**: `CaseClassicallyFree .E6 W6 explicitPresentation ∧ ker = I₂ⁿˢ`, conditional on
U5 and `E6StarIdentity`.
-/

namespace VOA.DeligneAudit.DeligneCarrier.E6

open VOA.DeligneHigherRankConditionalCapstone VOA.DeligneAudit.DeligneSector VOA.DeligneAudit.DeligneCharacter

/-- **The E₆ Deligne case**, conditional on U5 (fusion module bound) and the star identity. -/
theorem e6_classicallyFree
    (hU5 : FusionModuleBoundG E6sector (fusionOf (hilbSeries e6DemazureHilb)))
    (hstar : E6StarIdentity) :
    CaseClassicallyFree .E6 W6 explicitPresentation ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass W6 1 ⟨explicitPresentation.gen i,
          explicitPresentation.gen_weight_one i⟩).toRingHom = explicitPresentation.ideal :=
  classicallyFree_of_sectorFusion explicitPresentation E6sector e6DemazureHilb explicitCurrentJetSurjectivity
    geometricCarrierEmbedding hU5 DeligneDivisor.E6.e6_divisorComparison
    (demazureBoundFor_of_Q hstar e6_targetLowerBound)

/-- **The E₆ Deligne case, star input in `≤` form**: as `e6_classicallyFree`, with the `E6StarBound`
(`D_N ≤ mldeCoeff 12 N`) in place of `E6StarIdentity`. -/
theorem e6_classicallyFree_of_starBound
    (hU5 : FusionModuleBoundG E6sector (fusionOf (hilbSeries e6DemazureHilb)))
    (hB : E6StarBound) :
    CaseClassicallyFree .E6 W6 explicitPresentation ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass W6 1 ⟨explicitPresentation.gen i,
          explicitPresentation.gen_weight_one i⟩).toRingHom = explicitPresentation.ideal :=
  classicallyFree_of_sectorFusion explicitPresentation E6sector e6DemazureHilb explicitCurrentJetSurjectivity
    geometricCarrierEmbedding hU5 DeligneDivisor.E6.e6_divisorComparison
    (e6DemazureBoundFor_of_starBound W6 hB e6_targetLowerBound)

end VOA.DeligneAudit.DeligneCarrier.E6

section AxiomAudit
#print axioms VOA.DeligneAudit.DeligneCarrier.E6.e6_classicallyFree
#print axioms VOA.DeligneAudit.DeligneCarrier.E6.e6_classicallyFree_of_starBound
end AxiomAudit
