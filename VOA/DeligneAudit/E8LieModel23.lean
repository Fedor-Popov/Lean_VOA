/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E8LieTable

/-!
# The lattice model is the cert table (`pairOK`), rows `184..191` (one kernel check per row)
-/

namespace VOA.DeligneAudit.E8Lie

theorem row_ok184 : ∀ b, pairOK 184 b = true := by decide +kernel

theorem row_ok185 : ∀ b, pairOK 185 b = true := by decide +kernel

theorem row_ok186 : ∀ b, pairOK 186 b = true := by decide +kernel

theorem row_ok187 : ∀ b, pairOK 187 b = true := by decide +kernel

theorem row_ok188 : ∀ b, pairOK 188 b = true := by decide +kernel

theorem row_ok189 : ∀ b, pairOK 189 b = true := by decide +kernel

theorem row_ok190 : ∀ b, pairOK 190 b = true := by decide +kernel

theorem row_ok191 : ∀ b, pairOK 191 b = true := by decide +kernel

end VOA.DeligneAudit.E8Lie
