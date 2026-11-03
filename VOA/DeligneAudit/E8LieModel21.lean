/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E8LieTable

/-!
# The lattice model is the cert table (`pairOK`), rows `168..175` (one kernel check per row)
-/

namespace VOA.DeligneAudit.E8Lie

theorem row_ok168 : ∀ b, pairOK 168 b = true := by decide +kernel

theorem row_ok169 : ∀ b, pairOK 169 b = true := by decide +kernel

theorem row_ok170 : ∀ b, pairOK 170 b = true := by decide +kernel

theorem row_ok171 : ∀ b, pairOK 171 b = true := by decide +kernel

theorem row_ok172 : ∀ b, pairOK 172 b = true := by decide +kernel

theorem row_ok173 : ∀ b, pairOK 173 b = true := by decide +kernel

theorem row_ok174 : ∀ b, pairOK 174 b = true := by decide +kernel

theorem row_ok175 : ∀ b, pairOK 175 b = true := by decide +kernel

end VOA.DeligneAudit.E8Lie
