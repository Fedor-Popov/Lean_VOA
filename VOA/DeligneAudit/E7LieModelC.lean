/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E7LieTable

/-!
# The lattice model is the cert table (`pairOK`), rows `14..20` (one kernel check per row)
-/

namespace VOA.DeligneAudit.E7Lie

theorem row_ok14 : ∀ b, pairOK 14 b = true := by decide +kernel

theorem row_ok15 : ∀ b, pairOK 15 b = true := by decide +kernel

theorem row_ok16 : ∀ b, pairOK 16 b = true := by decide +kernel

theorem row_ok17 : ∀ b, pairOK 17 b = true := by decide +kernel

theorem row_ok18 : ∀ b, pairOK 18 b = true := by decide +kernel

theorem row_ok19 : ∀ b, pairOK 19 b = true := by decide +kernel

theorem row_ok20 : ∀ b, pairOK 20 b = true := by decide +kernel

end VOA.DeligneAudit.E7Lie
