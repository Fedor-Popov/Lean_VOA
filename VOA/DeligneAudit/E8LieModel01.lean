/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E8LieTable

/-!
# The lattice model is the cert table (`pairOK`), rows `8..15` (one kernel check per row)
-/

namespace VOA.DeligneAudit.E8Lie

theorem row_ok8 : ∀ b, pairOK 8 b = true := by decide +kernel

theorem row_ok9 : ∀ b, pairOK 9 b = true := by decide +kernel

theorem row_ok10 : ∀ b, pairOK 10 b = true := by decide +kernel

theorem row_ok11 : ∀ b, pairOK 11 b = true := by decide +kernel

theorem row_ok12 : ∀ b, pairOK 12 b = true := by decide +kernel

theorem row_ok13 : ∀ b, pairOK 13 b = true := by decide +kernel

theorem row_ok14 : ∀ b, pairOK 14 b = true := by decide +kernel

theorem row_ok15 : ∀ b, pairOK 15 b = true := by decide +kernel

end VOA.DeligneAudit.E8Lie
