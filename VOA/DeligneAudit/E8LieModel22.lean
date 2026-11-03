/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E8LieTable

/-!
# The lattice model is the cert table (`pairOK`), rows `176..183` (one kernel check per row)
-/

namespace VOA.DeligneAudit.E8Lie

theorem row_ok176 : ∀ b, pairOK 176 b = true := by decide +kernel

theorem row_ok177 : ∀ b, pairOK 177 b = true := by decide +kernel

theorem row_ok178 : ∀ b, pairOK 178 b = true := by decide +kernel

theorem row_ok179 : ∀ b, pairOK 179 b = true := by decide +kernel

theorem row_ok180 : ∀ b, pairOK 180 b = true := by decide +kernel

theorem row_ok181 : ∀ b, pairOK 181 b = true := by decide +kernel

theorem row_ok182 : ∀ b, pairOK 182 b = true := by decide +kernel

theorem row_ok183 : ∀ b, pairOK 183 b = true := by decide +kernel

end VOA.DeligneAudit.E8Lie
