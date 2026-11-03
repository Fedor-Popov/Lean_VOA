/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.A2SectorTop
import VOA.DeligneAudit.A2DivisorPairOps

/-!
# A₂ Deligne classical freeness: top module

The single remaining *proof* obligation is `PairComparison`: the paper's two-point computation B7
at the divisor `z_a = z_b`. B8's divisor comparison follows from it (`divisorComparison_of_pair`).
The other hypotheses are published results: U5 (`FusionModuleBound`, with its total-dimension
field), U6 (Ravinder's mixed fusion recursion), and the Kac–Wakimoto lower bound.
-/

namespace VOA.DeligneAudit.A2

open VOA.DeligneHigherRankConditionalCapstone

/-- **A₂ Deligne classical freeness** for `L_{-3/2}(sl₃)`, with the explicit presentation by
`I₂ⁿˢ`, which is shown to be the full `C₂` kernel. Conditional on the two-point comparison and
the three literature inputs. -/
theorem classicallyFree_of_pairAndLiterature (F : ℕ → PowerSeries ℚ)
    (hP : PairComparison) (hU5 : SectorWeyl.FusionModuleBound F)
    (hU6 : MixedFusionRecursion F demazureHilbSeries)
    (hkw : KacWakimotoLowerBound) :
    CaseClassicallyFree .A2 W explicitPresentation ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass W 1 ⟨explicitPresentation.gen i,
          explicitPresentation.gen_weight_one i⟩).toRingHom = I2ns :=
  classicallyFree_of_divisorAndLiterature F (divisorComparison_of_pair hP) hU5 hU6 hkw

end VOA.DeligneAudit.A2

section AxiomAudit
#print axioms VOA.DeligneAudit.A2.classicallyFree_of_pairAndLiterature
end AxiomAudit
