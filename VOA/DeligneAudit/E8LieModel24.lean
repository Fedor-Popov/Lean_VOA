/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E8LieTable

/-!
# The lattice model is the cert table (`pairOK`), rows `192..199` (one kernel check per row)
-/

namespace VOA.DeligneAudit.E8Lie

theorem row_ok192 : ∀ b, pairOK 192 b = true := by decide +kernel

theorem row_ok193 : ∀ b, pairOK 193 b = true := by decide +kernel

theorem row_ok194 : ∀ b, pairOK 194 b = true := by decide +kernel

theorem row_ok195 : ∀ b, pairOK 195 b = true := by decide +kernel

theorem row_ok196 : ∀ b, pairOK 196 b = true := by decide +kernel

theorem row_ok197 : ∀ b, pairOK 197 b = true := by decide +kernel

theorem row_ok198 : ∀ b, pairOK 198 b = true := by decide +kernel

theorem row_ok199 : ∀ b, pairOK 199 b = true := by decide +kernel

end VOA.DeligneAudit.E8Lie
