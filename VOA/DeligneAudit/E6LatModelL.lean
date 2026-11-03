/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E6LatTable

/-!
# The lattice model is the cert table (`pairOK`), rows `77..77` (one kernel check per row)
-/

namespace VOA.DeligneAudit.E6Lat

theorem row_ok77 : ∀ b, pairOK 77 b = true := by decide +kernel

end VOA.DeligneAudit.E6Lat
