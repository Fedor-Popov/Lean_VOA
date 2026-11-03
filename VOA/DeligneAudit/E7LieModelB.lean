/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E7LieTable

/-!
# The lattice model is the cert table (`pairOK`), rows `7..13` (one kernel check per row)
-/

namespace VOA.DeligneAudit.E7Lie

theorem row_ok7 : ∀ b, pairOK 7 b = true := by decide +kernel

theorem row_ok8 : ∀ b, pairOK 8 b = true := by decide +kernel

theorem row_ok9 : ∀ b, pairOK 9 b = true := by decide +kernel

theorem row_ok10 : ∀ b, pairOK 10 b = true := by decide +kernel

theorem row_ok11 : ∀ b, pairOK 11 b = true := by decide +kernel

theorem row_ok12 : ∀ b, pairOK 12 b = true := by decide +kernel

theorem row_ok13 : ∀ b, pairOK 13 b = true := by decide +kernel

end VOA.DeligneAudit.E7Lie
