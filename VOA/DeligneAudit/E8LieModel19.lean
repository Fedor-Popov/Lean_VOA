/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E8LieTable

/-!
# The lattice model is the cert table (`pairOK`), rows `152..159` (one kernel check per row)
-/

namespace VOA.DeligneAudit.E8Lie

theorem row_ok152 : ∀ b, pairOK 152 b = true := by decide +kernel

theorem row_ok153 : ∀ b, pairOK 153 b = true := by decide +kernel

theorem row_ok154 : ∀ b, pairOK 154 b = true := by decide +kernel

theorem row_ok155 : ∀ b, pairOK 155 b = true := by decide +kernel

theorem row_ok156 : ∀ b, pairOK 156 b = true := by decide +kernel

theorem row_ok157 : ∀ b, pairOK 157 b = true := by decide +kernel

theorem row_ok158 : ∀ b, pairOK 158 b = true := by decide +kernel

theorem row_ok159 : ∀ b, pairOK 159 b = true := by decide +kernel

end VOA.DeligneAudit.E8Lie
