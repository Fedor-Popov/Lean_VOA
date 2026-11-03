/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E8LieTable

/-!
# The lattice model is the cert table (`pairOK`), rows `16..23` (one kernel check per row)
-/

namespace VOA.DeligneAudit.E8Lie

theorem row_ok16 : ∀ b, pairOK 16 b = true := by decide +kernel

theorem row_ok17 : ∀ b, pairOK 17 b = true := by decide +kernel

theorem row_ok18 : ∀ b, pairOK 18 b = true := by decide +kernel

theorem row_ok19 : ∀ b, pairOK 19 b = true := by decide +kernel

theorem row_ok20 : ∀ b, pairOK 20 b = true := by decide +kernel

theorem row_ok21 : ∀ b, pairOK 21 b = true := by decide +kernel

theorem row_ok22 : ∀ b, pairOK 22 b = true := by decide +kernel

theorem row_ok23 : ∀ b, pairOK 23 b = true := by decide +kernel

end VOA.DeligneAudit.E8Lie
