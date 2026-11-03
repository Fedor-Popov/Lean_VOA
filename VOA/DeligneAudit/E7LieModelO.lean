/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E7LieTable

/-!
# The lattice model is the cert table (`pairOK`), rows `98..104` (one kernel check per row)
-/

namespace VOA.DeligneAudit.E7Lie

theorem row_ok98 : ∀ b, pairOK 98 b = true := by decide +kernel

theorem row_ok99 : ∀ b, pairOK 99 b = true := by decide +kernel

theorem row_ok100 : ∀ b, pairOK 100 b = true := by decide +kernel

theorem row_ok101 : ∀ b, pairOK 101 b = true := by decide +kernel

theorem row_ok102 : ∀ b, pairOK 102 b = true := by decide +kernel

theorem row_ok103 : ∀ b, pairOK 103 b = true := by decide +kernel

theorem row_ok104 : ∀ b, pairOK 104 b = true := by decide +kernel

end VOA.DeligneAudit.E7Lie
