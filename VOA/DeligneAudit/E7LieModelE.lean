/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E7LieTable

/-!
# The lattice model is the cert table (`pairOK`), rows `28..34` (one kernel check per row)
-/

namespace VOA.DeligneAudit.E7Lie

theorem row_ok28 : ∀ b, pairOK 28 b = true := by decide +kernel

theorem row_ok29 : ∀ b, pairOK 29 b = true := by decide +kernel

theorem row_ok30 : ∀ b, pairOK 30 b = true := by decide +kernel

theorem row_ok31 : ∀ b, pairOK 31 b = true := by decide +kernel

theorem row_ok32 : ∀ b, pairOK 32 b = true := by decide +kernel

theorem row_ok33 : ∀ b, pairOK 33 b = true := by decide +kernel

theorem row_ok34 : ∀ b, pairOK 34 b = true := by decide +kernel

end VOA.DeligneAudit.E7Lie
