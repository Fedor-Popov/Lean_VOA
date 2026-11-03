/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneSectorD4Table
import VOA.DeligneAudit.DeligneSectorD4CycChecks

/-!
# D₄: weights, local Weyl tables, and coadjoint cyclicity certificates

* `wtT`: the weights of the basis in simple-root coordinates (field `wt` of `cert_D4.json`);
  `d4_wtCheck`: the brackets are weight-homogeneous.
* `d4_raisingCheck`, `d4_cartanCheck`: the positive root vectors `4..15` kill `δ₂₇`, and the
  coroots `H_i` act on it by `θ(H_i) = (0, 1, 0, 0)` (`θ = ω₂`).
* `cycT`, `d4_cycCheck`: every basis vector of `g*` is a combination of coadjoint words of length
  `≤ 10` applied to `δ₂₇` (root vectors: one word each, letters `F_i` only; coroots: four words
  of length `5`, combined with the inverse Cartan matrix).  Depth `10 = 2 ht θ`.
-/

namespace VOA.DeligneAudit.DeligneSector.D4

open VOA.DeligneAudit.DeligneSector.Sparse

set_option linter.style.longLine false


end VOA.DeligneAudit.DeligneSector.D4

section AxiomAudit
#print axioms VOA.DeligneAudit.DeligneSector.D4.d4_cycCheck
#print axioms VOA.DeligneAudit.DeligneSector.D4.d4_cartanCheck
end AxiomAudit
