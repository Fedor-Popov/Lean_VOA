/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E8LieTable

/-!
# The lattice model is the cert table (`pairOK`), rows `24..31` (one kernel check per row)
-/

namespace VOA.DeligneAudit.E8Lie

theorem row_ok24 : ∀ b, pairOK 24 b = true := by decide +kernel

theorem row_ok25 : ∀ b, pairOK 25 b = true := by decide +kernel

theorem row_ok26 : ∀ b, pairOK 26 b = true := by decide +kernel

theorem row_ok27 : ∀ b, pairOK 27 b = true := by decide +kernel

theorem row_ok28 : ∀ b, pairOK 28 b = true := by decide +kernel

theorem row_ok29 : ∀ b, pairOK 29 b = true := by decide +kernel

theorem row_ok30 : ∀ b, pairOK 30 b = true := by decide +kernel

theorem row_ok31 : ∀ b, pairOK 31 b = true := by decide +kernel

end VOA.DeligneAudit.E8Lie
