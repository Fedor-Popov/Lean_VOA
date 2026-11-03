/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E8LieTable

/-!
# The lattice model is the cert table (`pairOK`), rows `128..135` (one kernel check per row)
-/

namespace VOA.DeligneAudit.E8Lie

theorem row_ok128 : ∀ b, pairOK 128 b = true := by decide +kernel

theorem row_ok129 : ∀ b, pairOK 129 b = true := by decide +kernel

theorem row_ok130 : ∀ b, pairOK 130 b = true := by decide +kernel

theorem row_ok131 : ∀ b, pairOK 131 b = true := by decide +kernel

theorem row_ok132 : ∀ b, pairOK 132 b = true := by decide +kernel

theorem row_ok133 : ∀ b, pairOK 133 b = true := by decide +kernel

theorem row_ok134 : ∀ b, pairOK 134 b = true := by decide +kernel

theorem row_ok135 : ∀ b, pairOK 135 b = true := by decide +kernel

end VOA.DeligneAudit.E8Lie
