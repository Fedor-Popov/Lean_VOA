/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E7LieTable

/-!
# The lattice model is the cert table (`pairOK`), rows `0..6` (one kernel check per row)
-/

namespace VOA.DeligneAudit.E7Lie

theorem row_ok0 : ∀ b, pairOK 0 b = true := by decide +kernel

theorem row_ok1 : ∀ b, pairOK 1 b = true := by decide +kernel

theorem row_ok2 : ∀ b, pairOK 2 b = true := by decide +kernel

theorem row_ok3 : ∀ b, pairOK 3 b = true := by decide +kernel

theorem row_ok4 : ∀ b, pairOK 4 b = true := by decide +kernel

theorem row_ok5 : ∀ b, pairOK 5 b = true := by decide +kernel

theorem row_ok6 : ∀ b, pairOK 6 b = true := by decide +kernel

end VOA.DeligneAudit.E7Lie
