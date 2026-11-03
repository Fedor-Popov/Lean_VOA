/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E8LieTable

/-!
# The lattice model is the cert table (`pairOK`), rows `144..151` (one kernel check per row)
-/

namespace VOA.DeligneAudit.E8Lie

theorem row_ok144 : ∀ b, pairOK 144 b = true := by decide +kernel

theorem row_ok145 : ∀ b, pairOK 145 b = true := by decide +kernel

theorem row_ok146 : ∀ b, pairOK 146 b = true := by decide +kernel

theorem row_ok147 : ∀ b, pairOK 147 b = true := by decide +kernel

theorem row_ok148 : ∀ b, pairOK 148 b = true := by decide +kernel

theorem row_ok149 : ∀ b, pairOK 149 b = true := by decide +kernel

theorem row_ok150 : ∀ b, pairOK 150 b = true := by decide +kernel

theorem row_ok151 : ∀ b, pairOK 151 b = true := by decide +kernel

end VOA.DeligneAudit.E8Lie
