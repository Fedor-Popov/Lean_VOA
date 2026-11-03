/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E8LieTable

/-!
# The lattice model is the cert table (`pairOK`), rows `112..119` (one kernel check per row)
-/

namespace VOA.DeligneAudit.E8Lie

theorem row_ok112 : ∀ b, pairOK 112 b = true := by decide +kernel

theorem row_ok113 : ∀ b, pairOK 113 b = true := by decide +kernel

theorem row_ok114 : ∀ b, pairOK 114 b = true := by decide +kernel

theorem row_ok115 : ∀ b, pairOK 115 b = true := by decide +kernel

theorem row_ok116 : ∀ b, pairOK 116 b = true := by decide +kernel

theorem row_ok117 : ∀ b, pairOK 117 b = true := by decide +kernel

theorem row_ok118 : ∀ b, pairOK 118 b = true := by decide +kernel

theorem row_ok119 : ∀ b, pairOK 119 b = true := by decide +kernel

end VOA.DeligneAudit.E8Lie
