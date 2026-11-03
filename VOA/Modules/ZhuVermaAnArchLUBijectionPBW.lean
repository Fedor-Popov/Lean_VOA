/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchDLM3PBWAxiom
import VOA.Modules.ZhuVermaAnArchLUBijection

/-!
# Zhu's faithful correspondence from the PBW theorem `VOA.pbw`

`ZhuVermaAnArchLUBijection.zhuBijective` is deliberately reusable: it displays
`Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W))` as an explicit parameter, so its
proof-term audit does not reveal how that datum was obtained.

This file instantiates `Pr` with `voaPBWBottomProjection`, which specializes the Lie-induction
field of `VOA.pbw` (a theorem). The resulting declaration
has no explicit projection hypothesis, and `#print axioms` reports only Lean's three standard
axioms, so it is unconditional.
-/

namespace VOA

open VHat VHat.DLM3

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- **Zhu Theorem 5.3.4 (faithful form)**, with `Pr` supplied by the PBW theorem `VOA.pbw`. -/
theorem zhuBijective_of_voaPBW (W : VertexOperatorAlgebra 𝒱) :
    Function.Bijective (forwardMapIrr W) :=
  zhuBijective
    (voaPBWBottomProjection (parabolicRepOfAMod W (regularAMod W)))

end VOA
