/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E6LatTable

/-!
# The lattice model is the cert table (`pairOK`), rows `70..76` (one kernel check per row)
-/

namespace VOA.DeligneAudit.E6Lat

theorem row_ok70 : ∀ b, pairOK 70 b = true := by decide +kernel

theorem row_ok71 : ∀ b, pairOK 71 b = true := by decide +kernel

theorem row_ok72 : ∀ b, pairOK 72 b = true := by decide +kernel

theorem row_ok73 : ∀ b, pairOK 73 b = true := by decide +kernel

theorem row_ok74 : ∀ b, pairOK 74 b = true := by decide +kernel

theorem row_ok75 : ∀ b, pairOK 75 b = true := by decide +kernel

theorem row_ok76 : ∀ b, pairOK 76 b = true := by decide +kernel

end VOA.DeligneAudit.E6Lat
