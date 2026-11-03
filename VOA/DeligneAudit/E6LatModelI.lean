/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E6LatTable

/-!
# The lattice model is the cert table (`pairOK`), rows `56..62` (one kernel check per row)
-/

namespace VOA.DeligneAudit.E6Lat

theorem row_ok56 : ∀ b, pairOK 56 b = true := by decide +kernel

theorem row_ok57 : ∀ b, pairOK 57 b = true := by decide +kernel

theorem row_ok58 : ∀ b, pairOK 58 b = true := by decide +kernel

theorem row_ok59 : ∀ b, pairOK 59 b = true := by decide +kernel

theorem row_ok60 : ∀ b, pairOK 60 b = true := by decide +kernel

theorem row_ok61 : ∀ b, pairOK 61 b = true := by decide +kernel

theorem row_ok62 : ∀ b, pairOK 62 b = true := by decide +kernel

end VOA.DeligneAudit.E6Lat
