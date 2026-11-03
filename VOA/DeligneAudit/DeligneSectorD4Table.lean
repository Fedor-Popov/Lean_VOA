/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneSectorSparse
import VOA.DeligneAudit.DeligneSectorD4TableChecks

/-!
# The `so₈` structure constants in the D₄ carrier basis

Basis of `Notes/deligne/audit_2026_10_25/casimir_cert/cert_D4.json` (the basis of
`DeligneCarrierD4`): `0..3` the coroots `H_i = [E_i, F_i]`, `4..15` the positive root vectors
(`E_1..E_4 = 7, 6, 5, 4`, `θ = 15`), `16..27` the negative ones (`F_1..F_4 = 19, 18, 17, 16`,
`-θ = 27`).  The table is the field `structure` of that file, transcribed verbatim.

* `d4_rangeCheck`, `d4_jacCheck`: index range and **the Jacobi identity**, both by `decide +kernel`.
-/

namespace VOA.DeligneAudit.DeligneSector.D4

open VOA.DeligneAudit.DeligneSector.Sparse

set_option linter.style.longLine false


end VOA.DeligneAudit.DeligneSector.D4

section AxiomAudit
#print axioms VOA.DeligneAudit.DeligneSector.D4.d4_jacCheck
end AxiomAudit
