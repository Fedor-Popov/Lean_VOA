/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E8LieTable

/-!
# The lattice model is the cert table (`pairOK`), rows `208..215` (one kernel check per row)
-/

namespace VOA.DeligneAudit.E8Lie

theorem row_ok208 : ∀ b, pairOK 208 b = true := by decide +kernel

theorem row_ok209 : ∀ b, pairOK 209 b = true := by decide +kernel

theorem row_ok210 : ∀ b, pairOK 210 b = true := by decide +kernel

theorem row_ok211 : ∀ b, pairOK 211 b = true := by decide +kernel

theorem row_ok212 : ∀ b, pairOK 212 b = true := by decide +kernel

theorem row_ok213 : ∀ b, pairOK 213 b = true := by decide +kernel

theorem row_ok214 : ∀ b, pairOK 214 b = true := by decide +kernel

theorem row_ok215 : ∀ b, pairOK 215 b = true := by decide +kernel

end VOA.DeligneAudit.E8Lie
