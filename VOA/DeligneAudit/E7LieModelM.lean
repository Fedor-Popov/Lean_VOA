/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E7LieTable

/-!
# The lattice model is the cert table (`pairOK`), rows `84..90` (one kernel check per row)
-/

namespace VOA.DeligneAudit.E7Lie

theorem row_ok84 : ∀ b, pairOK 84 b = true := by decide +kernel

theorem row_ok85 : ∀ b, pairOK 85 b = true := by decide +kernel

theorem row_ok86 : ∀ b, pairOK 86 b = true := by decide +kernel

theorem row_ok87 : ∀ b, pairOK 87 b = true := by decide +kernel

theorem row_ok88 : ∀ b, pairOK 88 b = true := by decide +kernel

theorem row_ok89 : ∀ b, pairOK 89 b = true := by decide +kernel

theorem row_ok90 : ∀ b, pairOK 90 b = true := by decide +kernel

end VOA.DeligneAudit.E7Lie
