/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E6FusionKernelTheta
import VOA.DeligneAudit.E6Final

/-!
# The `E₆` case from the fusion total bound

U5 for `E₆` is not a named input here: it is replaced by the inputs at the `A₂`/`D₄` level:

* `FusionTotalBoundG E6sector`;
* the Demazure realizations for Ravinder's family;
* the count `E6FusionCount`.

The kernel lemma is unconditional: `E6K.e6_ravinderKernelRel'` follows from `E6K.e6KernelTable` and `E6K.e6_thetaNil`.

* `e6_classicallyFree_of_totalBound (hF) (hD) (hcount) (hstar : E6StarIdentity)`.
* `e6_classicallyFree_of_totalBound_starBound (hF) (hD) (hcount) (hB : E6StarBound)`.
-/

namespace VOA.DeligneAudit.UnivG

open VOA.DeligneHigherRankConditionalCapstone VOA.DeligneAudit.DeligneCharacter VOA.DeligneAudit.UnivG.E6K
open VOA.DeligneAudit.DeligneCarrier.E6 (E6sector W6 explicitPresentation e6_classicallyFree
  e6_classicallyFree_of_starBound)

/-- **The `E₆` case** from `FusionTotalBoundG`, the Demazure realizations, the count and the star
identity. -/
theorem e6_classicallyFree_of_totalBound (hF : FusionTotalBoundG E6sector)
    (hD : ∀ n, DemazureRealizationG E6sector (ravFam E6sector)
      (DeligneCarrier.hilbSeries e6DemazureHilb) n)
    (hcount : E6FusionCount) (hstar : E6StarIdentity) :
    CaseClassicallyFree .E6 W6 explicitPresentation ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass W6 1 ⟨explicitPresentation.gen i,
          explicitPresentation.gen_weight_one i⟩).toRingHom = explicitPresentation.ideal :=
  e6_classicallyFree (e6_fusionModuleBound_of_totalBound hF hD hcount) hstar

/-- **The `E₆` case, star input in `≤` form.** -/
theorem e6_classicallyFree_of_totalBound_starBound (hF : FusionTotalBoundG E6sector)
    (hD : ∀ n, DemazureRealizationG E6sector (ravFam E6sector)
      (DeligneCarrier.hilbSeries e6DemazureHilb) n)
    (hcount : E6FusionCount) (hB : E6StarBound) :
    CaseClassicallyFree .E6 W6 explicitPresentation ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass W6 1 ⟨explicitPresentation.gen i,
          explicitPresentation.gen_weight_one i⟩).toRingHom = explicitPresentation.ideal :=
  e6_classicallyFree_of_starBound (e6_fusionModuleBound_of_totalBound hF hD hcount) hB

end VOA.DeligneAudit.UnivG

section AxiomAudit
#print axioms VOA.DeligneAudit.UnivG.e6_classicallyFree_of_totalBound
#print axioms VOA.DeligneAudit.UnivG.e6_classicallyFree_of_totalBound_starBound
end AxiomAudit
