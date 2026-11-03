/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E7FusionKernelTheta
import VOA.DeligneAudit.E7Final

/-!
# The `E₇` case from the fusion total bound

U5 for `E₇` is not a named input here: it is replaced by the inputs at the `A₂`/`D₄` level:

* `FusionTotalBoundG E7sector`;
* the Demazure realizations for Ravinder's family;
* the count `E7FusionCount`.

The kernel lemma is unconditional: `e7_ravinderKernelRel'` follows from `e7KernelTable` and `e7_thetaNil`.

* `e7_classicallyFree_of_totalBound (hF) (hD) (hcount) (hstar : E7StarIdentity)`.
* `e7_classicallyFree_of_totalBound_starBound (hF) (hD) (hcount) (hB : E7StarBound)`.
-/

namespace VOA.DeligneAudit.UnivG

open VOA.DeligneHigherRankConditionalCapstone VOA.DeligneAudit.DeligneCharacter VOA.DeligneAudit.E7Lie
open VOA.DeligneAudit.DeligneCarrier.E7 (E7sector)

/-- **The `E₇` case** from `FusionTotalBoundG`, the Demazure realizations, the count and the star
identity. -/
theorem e7_classicallyFree_of_totalBound (hF : FusionTotalBoundG E7sector)
    (hD : ∀ n, DemazureRealizationG E7sector (ravFam E7sector)
      (DeligneCarrier.hilbSeries e7DemazureHilb) n)
    (hcount : E7FusionCount) (hstar : E7StarIdentity) :
    CaseClassicallyFree .E7 W7 explicitPresentation7 ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass W7 1 ⟨explicitPresentation7.gen i,
          explicitPresentation7.gen_weight_one i⟩).toRingHom = explicitPresentation7.ideal :=
  e7_classicallyFree (e7_fusionModuleBound_of_totalBound hF hD hcount) hstar

/-- **The `E₇` case, star input in `≤` form.** -/
theorem e7_classicallyFree_of_totalBound_starBound (hF : FusionTotalBoundG E7sector)
    (hD : ∀ n, DemazureRealizationG E7sector (ravFam E7sector)
      (DeligneCarrier.hilbSeries e7DemazureHilb) n)
    (hcount : E7FusionCount) (hB : E7StarBound) :
    CaseClassicallyFree .E7 W7 explicitPresentation7 ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass W7 1 ⟨explicitPresentation7.gen i,
          explicitPresentation7.gen_weight_one i⟩).toRingHom = explicitPresentation7.ideal :=
  e7_classicallyFree_of_starBound (e7_fusionModuleBound_of_totalBound hF hD hcount) hB

end VOA.DeligneAudit.UnivG

section AxiomAudit
#print axioms VOA.DeligneAudit.UnivG.e7_classicallyFree_of_totalBound
#print axioms VOA.DeligneAudit.UnivG.e7_classicallyFree_of_totalBound_starBound
end AxiomAudit
