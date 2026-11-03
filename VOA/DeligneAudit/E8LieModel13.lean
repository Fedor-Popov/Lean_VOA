/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E8LieTable

/-!
# The lattice model is the cert table (`pairOK`), rows `104..111` (one kernel check per row)
-/

namespace VOA.DeligneAudit.E8Lie

theorem row_ok104 : ∀ b, pairOK 104 b = true := by decide +kernel

theorem row_ok105 : ∀ b, pairOK 105 b = true := by decide +kernel

theorem row_ok106 : ∀ b, pairOK 106 b = true := by decide +kernel

theorem row_ok107 : ∀ b, pairOK 107 b = true := by decide +kernel

theorem row_ok108 : ∀ b, pairOK 108 b = true := by decide +kernel

theorem row_ok109 : ∀ b, pairOK 109 b = true := by decide +kernel

theorem row_ok110 : ∀ b, pairOK 110 b = true := by decide +kernel

theorem row_ok111 : ∀ b, pairOK 111 b = true := by decide +kernel

end VOA.DeligneAudit.E8Lie
