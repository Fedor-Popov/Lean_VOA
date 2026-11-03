/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E8FusionKernelTheta
import VOA.DeligneAudit.E8Final

/-!
# The `E₈` case from the fusion total bound

U5 for `E₈` is not a named input here: it is replaced by the inputs at the `A₂`/`D₄` level:

* `FusionTotalBoundG E8sector`;
* the Demazure realizations for Ravinder's family;
* the count `E8FusionCount`.

The kernel lemma is unconditional: `E8K.e8_ravinderKernelRel'` follows from `E8K.e8KernelTable` and `E8K.e8_thetaNil`.

* `e8_classicallyFree_of_totalBound (hF) (hD) (hcount) (hstar : E8StarIdentity)`.
* `e8_classicallyFree_of_totalBound_starBound (hF) (hD) (hcount) (hB : E8StarBound)`.
-/

namespace VOA.DeligneAudit.UnivG

open VOA.DeligneHigherRankConditionalCapstone VOA.DeligneAudit.DeligneCharacter VOA.DeligneAudit.E8Lie
open VOA.DeligneAudit.UnivG.E8K
open VOA.DeligneAudit.DeligneCarrier.E8 (E8sector)

/-- **The `E₈` case** from `FusionTotalBoundG`, the Demazure realizations, the count and the star
identity. -/
theorem e8_classicallyFree_of_totalBound (hF : FusionTotalBoundG E8sector)
    (hD : ∀ n, DemazureRealizationG E8sector (ravFam E8sector)
      (DeligneCarrier.hilbSeries e8DemazureHilb) n)
    (hcount : E8FusionCount) (hstar : E8StarIdentity) :
    CaseClassicallyFree .E8 W8 explicitPresentation8 ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass W8 1 ⟨explicitPresentation8.gen i,
          explicitPresentation8.gen_weight_one i⟩).toRingHom = explicitPresentation8.ideal :=
  e8_classicallyFree (e8_fusionModuleBound_of_totalBound hF hD hcount) hstar

/-- **The `E₈` case, star input in `≤` form.** -/
theorem e8_classicallyFree_of_totalBound_starBound (hF : FusionTotalBoundG E8sector)
    (hD : ∀ n, DemazureRealizationG E8sector (ravFam E8sector)
      (DeligneCarrier.hilbSeries e8DemazureHilb) n)
    (hcount : E8FusionCount) (hB : E8StarBound) :
    CaseClassicallyFree .E8 W8 explicitPresentation8 ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass W8 1 ⟨explicitPresentation8.gen i,
          explicitPresentation8.gen_weight_one i⟩).toRingHom = explicitPresentation8.ideal :=
  e8_classicallyFree_of_starBound (e8_fusionModuleBound_of_totalBound hF hD hcount) hB

end VOA.DeligneAudit.UnivG

section AxiomAudit
#print axioms VOA.DeligneAudit.UnivG.e8_classicallyFree_of_totalBound
#print axioms VOA.DeligneAudit.UnivG.e8_classicallyFree_of_totalBound_starBound
end AxiomAudit
