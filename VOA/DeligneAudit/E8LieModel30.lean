/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E8LieTable

/-!
# The lattice model is the cert table (`pairOK`), rows `240..247` (one kernel check per row)
-/

namespace VOA.DeligneAudit.E8Lie

theorem row_ok240 : ∀ b, pairOK 240 b = true := by decide +kernel

theorem row_ok241 : ∀ b, pairOK 241 b = true := by decide +kernel

theorem row_ok242 : ∀ b, pairOK 242 b = true := by decide +kernel

theorem row_ok243 : ∀ b, pairOK 243 b = true := by decide +kernel

theorem row_ok244 : ∀ b, pairOK 244 b = true := by decide +kernel

theorem row_ok245 : ∀ b, pairOK 245 b = true := by decide +kernel

theorem row_ok246 : ∀ b, pairOK 246 b = true := by decide +kernel

theorem row_ok247 : ∀ b, pairOK 247 b = true := by decide +kernel

end VOA.DeligneAudit.E8Lie
