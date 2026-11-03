/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E8LieTable

/-!
# The lattice model is the cert table (`pairOK`), rows `200..207` (one kernel check per row)
-/

namespace VOA.DeligneAudit.E8Lie

theorem row_ok200 : ∀ b, pairOK 200 b = true := by decide +kernel

theorem row_ok201 : ∀ b, pairOK 201 b = true := by decide +kernel

theorem row_ok202 : ∀ b, pairOK 202 b = true := by decide +kernel

theorem row_ok203 : ∀ b, pairOK 203 b = true := by decide +kernel

theorem row_ok204 : ∀ b, pairOK 204 b = true := by decide +kernel

theorem row_ok205 : ∀ b, pairOK 205 b = true := by decide +kernel

theorem row_ok206 : ∀ b, pairOK 206 b = true := by decide +kernel

theorem row_ok207 : ∀ b, pairOK 207 b = true := by decide +kernel

end VOA.DeligneAudit.E8Lie
