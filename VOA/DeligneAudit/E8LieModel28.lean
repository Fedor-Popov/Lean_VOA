/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E8LieTable

/-!
# The lattice model is the cert table (`pairOK`), rows `224..231` (one kernel check per row)
-/

namespace VOA.DeligneAudit.E8Lie

theorem row_ok224 : ∀ b, pairOK 224 b = true := by decide +kernel

theorem row_ok225 : ∀ b, pairOK 225 b = true := by decide +kernel

theorem row_ok226 : ∀ b, pairOK 226 b = true := by decide +kernel

theorem row_ok227 : ∀ b, pairOK 227 b = true := by decide +kernel

theorem row_ok228 : ∀ b, pairOK 228 b = true := by decide +kernel

theorem row_ok229 : ∀ b, pairOK 229 b = true := by decide +kernel

theorem row_ok230 : ∀ b, pairOK 230 b = true := by decide +kernel

theorem row_ok231 : ∀ b, pairOK 231 b = true := by decide +kernel

end VOA.DeligneAudit.E8Lie
