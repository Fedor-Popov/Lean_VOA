/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E8LieTable

/-!
# The lattice model is the cert table (`pairOK`), rows `72..79` (one kernel check per row)
-/

namespace VOA.DeligneAudit.E8Lie

theorem row_ok72 : ∀ b, pairOK 72 b = true := by decide +kernel

theorem row_ok73 : ∀ b, pairOK 73 b = true := by decide +kernel

theorem row_ok74 : ∀ b, pairOK 74 b = true := by decide +kernel

theorem row_ok75 : ∀ b, pairOK 75 b = true := by decide +kernel

theorem row_ok76 : ∀ b, pairOK 76 b = true := by decide +kernel

theorem row_ok77 : ∀ b, pairOK 77 b = true := by decide +kernel

theorem row_ok78 : ∀ b, pairOK 78 b = true := by decide +kernel

theorem row_ok79 : ∀ b, pairOK 79 b = true := by decide +kernel

end VOA.DeligneAudit.E8Lie
