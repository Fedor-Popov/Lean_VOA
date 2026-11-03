/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E8LieTable

/-!
# The lattice model is the cert table (`pairOK`), rows `216..223` (one kernel check per row)
-/

namespace VOA.DeligneAudit.E8Lie

theorem row_ok216 : ∀ b, pairOK 216 b = true := by decide +kernel

theorem row_ok217 : ∀ b, pairOK 217 b = true := by decide +kernel

theorem row_ok218 : ∀ b, pairOK 218 b = true := by decide +kernel

theorem row_ok219 : ∀ b, pairOK 219 b = true := by decide +kernel

theorem row_ok220 : ∀ b, pairOK 220 b = true := by decide +kernel

theorem row_ok221 : ∀ b, pairOK 221 b = true := by decide +kernel

theorem row_ok222 : ∀ b, pairOK 222 b = true := by decide +kernel

theorem row_ok223 : ∀ b, pairOK 223 b = true := by decide +kernel

end VOA.DeligneAudit.E8Lie
