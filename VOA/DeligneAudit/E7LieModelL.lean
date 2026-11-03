/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E7LieTable

/-!
# The lattice model is the cert table (`pairOK`), rows `77..83` (one kernel check per row)
-/

namespace VOA.DeligneAudit.E7Lie

theorem row_ok77 : ∀ b, pairOK 77 b = true := by decide +kernel

theorem row_ok78 : ∀ b, pairOK 78 b = true := by decide +kernel

theorem row_ok79 : ∀ b, pairOK 79 b = true := by decide +kernel

theorem row_ok80 : ∀ b, pairOK 80 b = true := by decide +kernel

theorem row_ok81 : ∀ b, pairOK 81 b = true := by decide +kernel

theorem row_ok82 : ∀ b, pairOK 82 b = true := by decide +kernel

theorem row_ok83 : ∀ b, pairOK 83 b = true := by decide +kernel

end VOA.DeligneAudit.E7Lie
