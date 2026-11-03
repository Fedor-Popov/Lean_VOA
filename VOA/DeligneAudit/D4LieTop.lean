/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.D4LiePresentation
import VOA.DeligneAudit.DeligneCarrierD4Chain
import VOA.DeligneAudit.A2Character

/-!
# The `D₄` Deligne case on `L_{-2}(𝔰𝔬₈)`: what remains

With the explicit presentation (`explicitPresentation4`, ideal `I₂ⁿˢ`), the generic carrier chain
for `D4data` and the `D₄` Demazure data, the `D₄` case (classical freeness and `ker = I₂ⁿˢ`)
rests on exactly three inputs:

* `SectorFusionBound D4data F` (the sector inputs, B2–B8 and U5, for `D₄`);
* `MixedFusionRecursion F (hilbSeries d4DemazureHilb)` (U6);
* `DemazureBoundFor W4 d4DemazureHilb` (the character lower bound, Kac–Wakimoto + star identity).
-/

namespace VOA.DeligneAudit.D4Lie

open VOA.AffineGeneral VOA.DeligneHigherRankConditionalCapstone VOA.DeligneAudit.DeligneCarrier
  VOA.DeligneAudit.DeligneCharacter

noncomputable section

/-- **The `D₄` Deligne case on `L_{-2}(𝔰𝔬₈)`, from the sector inputs, U6 and the character lower
bound.** -/
theorem d4_classicallyFree_of_sector (F : ℕ → PowerSeries ℚ) (hF : SectorFusionBound D4.D4data F)
    (hU6 : MixedFusionRecursion F (hilbSeries d4DemazureHilb))
    (hchr : DemazureBoundFor W4 d4DemazureHilb) :
    CaseClassicallyFree .D4 W4 explicitPresentation4 ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass W4 1 ⟨explicitPresentation4.gen i,
          explicitPresentation4.gen_weight_one i⟩).toRingHom = explicitPresentation4.ideal :=
  caseClassicallyFree_of_lowerBound explicitPresentation4 (CarrierEmbedding.Carrier D4.rel)
    explicitCurrentJetSurjectivity4 explicitGeometricCarrierEmbedding4
    (carrierCharacterLowerBound_of_sector D4.D4data d4DemazureHilb F hF hU6 hchr)

end

end VOA.DeligneAudit.D4Lie

section AxiomAudit
#print axioms VOA.DeligneAudit.D4Lie.d4_classicallyFree_of_sector
end AxiomAudit
