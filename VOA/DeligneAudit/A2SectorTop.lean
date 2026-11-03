/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.A2Headline
import VOA.DeligneAudit.A2SectorB6

/-!
# A₂ headline with B6 discharged

`mFreeness` proves B6 from U5 (including its total-dimension form), so the A₂ case rests on the
divisor comparison of B8 and the literature inputs U5, U6, Kac–Wakimoto.
-/

namespace VOA.DeligneAudit.A2

open VOA.DeligneHigherRankConditionalCapstone

/-- **A₂ Deligne classical freeness from the divisor comparison and the literature inputs.** -/
theorem classicallyFree_of_divisorAndLiterature (F : ℕ → PowerSeries ℚ)
    (hD : DivisorComparison) (hU5 : SectorWeyl.FusionModuleBound F)
    (hU6 : MixedFusionRecursion F demazureHilbSeries)
    (hkw : KacWakimotoLowerBound) :
    CaseClassicallyFree .A2 W explicitPresentation ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass W 1 ⟨explicitPresentation.gen i,
          explicitPresentation.gen_weight_one i⟩).toRingHom = I2ns :=
  classicallyFree_of_openInputs F (mFreeness hU5) hD hU5 hU6 hkw

end VOA.DeligneAudit.A2

section AxiomAudit
#print axioms VOA.DeligneAudit.A2.classicallyFree_of_divisorAndLiterature
end AxiomAudit
