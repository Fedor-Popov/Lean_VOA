/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E8LieTable

/-!
# The lattice model is the cert table (`pairOK`), rows `232..239` (one kernel check per row)
-/

namespace VOA.DeligneAudit.E8Lie

theorem row_ok232 : ∀ b, pairOK 232 b = true := by decide +kernel

theorem row_ok233 : ∀ b, pairOK 233 b = true := by decide +kernel

theorem row_ok234 : ∀ b, pairOK 234 b = true := by decide +kernel

theorem row_ok235 : ∀ b, pairOK 235 b = true := by decide +kernel

theorem row_ok236 : ∀ b, pairOK 236 b = true := by decide +kernel

theorem row_ok237 : ∀ b, pairOK 237 b = true := by decide +kernel

theorem row_ok238 : ∀ b, pairOK 238 b = true := by decide +kernel

theorem row_ok239 : ∀ b, pairOK 239 b = true := by decide +kernel

end VOA.DeligneAudit.E8Lie
