/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E8LieTable

/-!
# The lattice model is the cert table (`pairOK`), rows `80..87` (one kernel check per row)
-/

namespace VOA.DeligneAudit.E8Lie

theorem row_ok80 : ∀ b, pairOK 80 b = true := by decide +kernel

theorem row_ok81 : ∀ b, pairOK 81 b = true := by decide +kernel

theorem row_ok82 : ∀ b, pairOK 82 b = true := by decide +kernel

theorem row_ok83 : ∀ b, pairOK 83 b = true := by decide +kernel

theorem row_ok84 : ∀ b, pairOK 84 b = true := by decide +kernel

theorem row_ok85 : ∀ b, pairOK 85 b = true := by decide +kernel

theorem row_ok86 : ∀ b, pairOK 86 b = true := by decide +kernel

theorem row_ok87 : ∀ b, pairOK 87 b = true := by decide +kernel

end VOA.DeligneAudit.E8Lie
