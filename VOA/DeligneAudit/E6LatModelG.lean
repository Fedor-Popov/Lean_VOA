/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E6LatTable

/-!
# The lattice model is the cert table (`pairOK`), rows `42..48` (one kernel check per row)
-/

namespace VOA.DeligneAudit.E6Lat

theorem row_ok42 : ∀ b, pairOK 42 b = true := by decide +kernel

theorem row_ok43 : ∀ b, pairOK 43 b = true := by decide +kernel

theorem row_ok44 : ∀ b, pairOK 44 b = true := by decide +kernel

theorem row_ok45 : ∀ b, pairOK 45 b = true := by decide +kernel

theorem row_ok46 : ∀ b, pairOK 46 b = true := by decide +kernel

theorem row_ok47 : ∀ b, pairOK 47 b = true := by decide +kernel

theorem row_ok48 : ∀ b, pairOK 48 b = true := by decide +kernel

end VOA.DeligneAudit.E6Lat
