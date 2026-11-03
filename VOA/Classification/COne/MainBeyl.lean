/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.QExpSpan2Headline
import VOA.Huang.NSSMoveC4Assembly
import VOA.Huang.DLNSchur3Relations

/-!
# The forward Gannon–Rayhaun classification, conditional only on Beyl's prime-power facts

The forward headline `gannonRayhaun_hkl_qexp` assumes `DLNCongruenceInput` and
`GaloisSymmetryNontrivialInput`.  Both follow (`NSGaloisCore.dln_inputs_of_beyl`, through
the unconditional Ng–Schauenburg congruence theorem `DLNBridge.nsProjectiveKernelAll_holds`) from
the two remaining Schur-multiplier statements about `SL₂(ℤ/p^k)` (Mennicke; Beyl, Math. Z. 191
(1986), Theorem 3.9 and Corollary 3.10; Dong–Lin–Ng, Theorem 2.1).  The odd case is split further
into the large-prime Gauss-chart relation and the prime `3`
(`DLNSchur.oddPrimePowerSchur_iff_rootRelations_and_three`,
`DLNSchur.largePrimeRootRelations_iff_gaussLowerRelations`).

Every theorem here is `#print axioms`-clean (the theorem `VOA.pbw` adds no axiom) and conditional on
the displayed hypotheses.
-/

namespace VOA.Classification.COne

universe u

/-- **Forward Gannon–Rayhaun, conditional only on Beyl's two prime-power Schur facts.** -/
theorem gannonRayhaun_beyl (hodd : VOA.Huang.DLNBeyl.OddPrimePowerSchur)
    (htwo : VOA.Huang.DLNSchur.TwoPowerInflationFromTwo) : GannonRayhaunStatement.{u} :=
  gannonRayhaun_hkl_qexp (VOA.Huang.NSGaloisCore.dln_inputs_of_beyl hodd htwo).1
    (VOA.Huang.NSGaloisCore.dln_inputs_of_beyl hodd htwo).2

/-- **Forward Gannon–Rayhaun from the finest named residuals**: the large-prime Gauss-chart
relation, the prime `3`, and the `2`-adic inflation for exponents `≥ 2`. -/
theorem gannonRayhaun_beyl_fine
    (hlarge : VOA.Huang.DLNSchur.LargePrimeGaussLowerRelations)
    (hthree : VOA.Huang.DLNSchur.ThreePowerSchur)
    (htwo : VOA.Huang.DLNSchur.TwoPowerInflationFromTwo) : GannonRayhaunStatement.{u} :=
  gannonRayhaun_beyl
    (VOA.Huang.DLNSchur.oddPrimePowerSchur_iff_rootRelations_and_three.mpr
      ⟨VOA.Huang.DLNSchur.largePrimeRootRelations_iff_gaussLowerRelations.mpr hlarge, hthree⟩)
    htwo

end VOA.Classification.COne
