/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.A2DivisorFinal
import VOA.DeligneAudit.A2Top

/-!
# A₂ Deligne classical freeness from the literature inputs only

With `pairComparison` proved, the A₂ top theorem rests only on the three published inputs:
U5 (`FusionModuleBound`), U6 (Ravinder's mixed fusion recursion), and the Kac–Wakimoto lower bound.
-/

namespace VOA.DeligneAudit.A2

open VOA.DeligneHigherRankConditionalCapstone

/-- **A₂ Deligne classical freeness** for `L_{-3/2}(sl₃)` with the explicit presentation by `I₂ⁿˢ`
(shown to be the full `C₂` kernel), conditional only on U5, U6 and Kac–Wakimoto. -/
theorem classicallyFree_of_literature (F : ℕ → PowerSeries ℚ)
    (hU5 : SectorWeyl.FusionModuleBound F)
    (hU6 : MixedFusionRecursion F demazureHilbSeries)
    (hkw : KacWakimotoLowerBound) :
    CaseClassicallyFree .A2 W explicitPresentation ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass W 1 ⟨explicitPresentation.gen i,
          explicitPresentation.gen_weight_one i⟩).toRingHom = I2ns :=
  classicallyFree_of_pairAndLiterature F pairComparison hU5 hU6 hkw

end VOA.DeligneAudit.A2

section AxiomAudit
#print axioms VOA.DeligneAudit.A2.classicallyFree_of_literature
end AxiomAudit
