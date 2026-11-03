/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E8LieTable

/-!
# The lattice model is the cert table (`pairOK`), rows `136..143` (one kernel check per row)
-/

namespace VOA.DeligneAudit.E8Lie

theorem row_ok136 : ∀ b, pairOK 136 b = true := by decide +kernel

theorem row_ok137 : ∀ b, pairOK 137 b = true := by decide +kernel

theorem row_ok138 : ∀ b, pairOK 138 b = true := by decide +kernel

theorem row_ok139 : ∀ b, pairOK 139 b = true := by decide +kernel

theorem row_ok140 : ∀ b, pairOK 140 b = true := by decide +kernel

theorem row_ok141 : ∀ b, pairOK 141 b = true := by decide +kernel

theorem row_ok142 : ∀ b, pairOK 142 b = true := by decide +kernel

theorem row_ok143 : ∀ b, pairOK 143 b = true := by decide +kernel

end VOA.DeligneAudit.E8Lie
