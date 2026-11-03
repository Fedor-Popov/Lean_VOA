/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneVacuumRelationA2
import VOA.DeligneAudit.DeligneMLDEProduct

/-!
# A₂ Deligne classical freeness, modulo Ravinder's fusion results only

The final form of the A₂ case of Deligne classical freeness. `L_{-3/2}(sl₃)` (`A2.W`, the simple
quotient of the universal affine VOA) is classically free for its explicit `C₂` presentation by
the eight quadrics `I₂ⁿˢ`, and `I₂ⁿˢ` is the full `C₂` kernel. The only hypotheses are two
published results on current-algebra modules:

* U5 (`SectorWeyl.FusionModuleBound F`): Ravinder/Feigin's fusion upper bound, including
  `dim ≤ 8^m`;
* U6 (`MixedFusionRecursion F demazureHilbSeries`): Ravinder's mixed fusion recursion.

Everything else is proved: the singular vector and the explicit presentation, jet surjectivity,
the carrier embedding, B1, B5–B8, the two-point comparison, the resummation, the q-series identity
(⋆), and the character, by the Arakawa–Kawasetsu MLDE (product identity via the heat equation,
vacuum quartic relation via square-bracket current symbols). No Kac–Wakimoto input remains.
-/

namespace VOA.DeligneAudit.A2

open VOA.DeligneHigherRankConditionalCapstone

/-- **A₂ Deligne classical freeness, conditional only on U5 and U6.** -/
theorem classicallyFree_of_fusion (F : ℕ → PowerSeries ℚ)
    (hU5 : SectorWeyl.FusionModuleBound F)
    (hU6 : MixedFusionRecursion F demazureHilbSeries) :
    CaseClassicallyFree .A2 W explicitPresentation ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass W 1 ⟨explicitPresentation.gen i,
          explicitPresentation.gen_weight_one i⟩).toRingHom = I2ns :=
  classicallyFree_of_productMLDE F hU5 hU6 a2ProductMLDE

end VOA.DeligneAudit.A2

section AxiomAudit
#print axioms VOA.DeligneAudit.A2.classicallyFree_of_fusion
end AxiomAudit
