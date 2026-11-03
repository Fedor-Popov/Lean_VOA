/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.Sl2SemiInfiniteCubicProducts
import VOA.Examples.Sl2SemiInfiniteGhostAnomaly

/-!
# The cubic ghost anomaly

The residue of the cubic ghost current on itself is four times the actual
derivative-ghost anomaly state.  The proof evaluates all nine tensor products
of its three exterior monomials, including their regular derivative terms.
It uses no matter or nilpotency hypothesis.
-/

namespace VOA.Sl2SemiInfinite

/-- The exact cubic self-contraction supplies the ghost level `+4`. -/
theorem ghostBRSTState_zero_self :
    mode (sl2GhostSVA.Y ghostBRSTState) 0 ghostBRSTState =
      (4 : ℂ) • ghostAnomalyState := by
  rw [ghostBRSTState_zero_self_tensor, ghostAnomalyState_tensor]
  module

end VOA.Sl2SemiInfinite
