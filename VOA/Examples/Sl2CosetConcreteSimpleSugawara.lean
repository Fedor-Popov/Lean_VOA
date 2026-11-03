/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.Sl2CosetConcreteSimple
import VOA.Examples.Sl2CosetConcreteConformal

/-!
# The Sugawara state is the actual quotient conformal vector

The quadratic state commutes with the maximal-ideal projection. Consequently,
the Sugawara expression in the descended currents is the conformal vector of
the existing simple affine VOA.
-/

namespace VOA.Sl2CosetConcrete

open Sl2SemiInfinite AffineVOA

universe u
variable {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- The normalized quadratic current state descends through the VOA projection. -/
theorem maxQuotientAffineAction_sugawara (W : VertexOperatorAlgebra M) {k : ℂ}
    (A : AffineSl2Action W.toPreVertexAlgebra.toSuper k) :
    sugawaraState (maxQuotientAffineAction W A) =
      (QuotVOA.maxGradedIdeal W).mkQ (sugawaraState A) := by
  let q := (QuotVOA.maxGradedIdeal W).mkQ
  change (2 * (k + 2))⁻¹ •
      (∑ a : Fin 3, ∑ b : Fin 3,
        kappaInv a b • (QuotVOA.maxQuotientVOA W).smul
          (q (A.current a)) (-1) (q (A.current b))) =
    q ((2 * (k + 2))⁻¹ •
      ∑ a : Fin 3, ∑ b : Fin 3, kappaInv a b • W.smul (A.current a) (-1) (A.current b))
  simp only [q, SimpleQuot.maxQuotientVOA_mkQ_smul, map_smul, map_sum]

/-- The current Sugawara expression equals the universal VOA conformal vector. -/
theorem universalAction_sugawara (k : ℂ) (hk : k + 2 ≠ 0) :
    sugawaraState (universalAction k hk).toAffineSl2Action =
      (AffineSl2GeneralRigidity.universal k hk).conformalVector :=
  sugawaraState_affineAction k hk

/-- The current Sugawara expression equals the simple VOA conformal vector. -/
theorem simpleAction_sugawara (k : ℂ) (hk : k + 2 ≠ 0) :
    sugawaraState (simpleAction k hk).toAffineSl2Action =
      (AffineSl2GeneralRigidity.simple k hk).conformalVector := by
  change sugawaraState (maxQuotientAffineAction
    (AffineSl2GeneralRigidity.universal k hk) (affineAction k hk)) = _
  rw [maxQuotientAffineAction_sugawara]
  exact congrArg (QuotVOA.maxGradedIdeal (AffineSl2GeneralRigidity.universal k hk)).mkQ
    (sugawaraState_affineAction k hk)

end VOA.Sl2CosetConcrete
