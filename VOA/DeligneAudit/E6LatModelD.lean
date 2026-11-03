/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E6LatTable

/-!
# The lattice model is the cert table (`pairOK`), rows `21..27` (one kernel check per row)
-/

namespace VOA.DeligneAudit.E6Lat

theorem row_ok21 : ∀ b, pairOK 21 b = true := by decide +kernel

theorem row_ok22 : ∀ b, pairOK 22 b = true := by decide +kernel

theorem row_ok23 : ∀ b, pairOK 23 b = true := by decide +kernel

theorem row_ok24 : ∀ b, pairOK 24 b = true := by decide +kernel

theorem row_ok25 : ∀ b, pairOK 25 b = true := by decide +kernel

theorem row_ok26 : ∀ b, pairOK 26 b = true := by decide +kernel

theorem row_ok27 : ∀ b, pairOK 27 b = true := by decide +kernel

end VOA.DeligneAudit.E6Lat
