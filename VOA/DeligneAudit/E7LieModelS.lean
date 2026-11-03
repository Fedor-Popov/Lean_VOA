/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E7LieTable

/-!
# The lattice model is the cert table (`pairOK`), rows `126..132` (one kernel check per row)
-/

namespace VOA.DeligneAudit.E7Lie

theorem row_ok126 : ∀ b, pairOK 126 b = true := by decide +kernel

theorem row_ok127 : ∀ b, pairOK 127 b = true := by decide +kernel

theorem row_ok128 : ∀ b, pairOK 128 b = true := by decide +kernel

theorem row_ok129 : ∀ b, pairOK 129 b = true := by decide +kernel

theorem row_ok130 : ∀ b, pairOK 130 b = true := by decide +kernel

theorem row_ok131 : ∀ b, pairOK 131 b = true := by decide +kernel

theorem row_ok132 : ∀ b, pairOK 132 b = true := by decide +kernel

end VOA.DeligneAudit.E7Lie
