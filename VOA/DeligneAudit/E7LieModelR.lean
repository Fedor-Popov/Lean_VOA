/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E7LieTable

/-!
# The lattice model is the cert table (`pairOK`), rows `119..125` (one kernel check per row)
-/

namespace VOA.DeligneAudit.E7Lie

theorem row_ok119 : ∀ b, pairOK 119 b = true := by decide +kernel

theorem row_ok120 : ∀ b, pairOK 120 b = true := by decide +kernel

theorem row_ok121 : ∀ b, pairOK 121 b = true := by decide +kernel

theorem row_ok122 : ∀ b, pairOK 122 b = true := by decide +kernel

theorem row_ok123 : ∀ b, pairOK 123 b = true := by decide +kernel

theorem row_ok124 : ∀ b, pairOK 124 b = true := by decide +kernel

theorem row_ok125 : ∀ b, pairOK 125 b = true := by decide +kernel

end VOA.DeligneAudit.E7Lie
