/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E7LieTable

/-!
# The lattice model is the cert table (`pairOK`), rows `91..97` (one kernel check per row)
-/

namespace VOA.DeligneAudit.E7Lie

theorem row_ok91 : ∀ b, pairOK 91 b = true := by decide +kernel

theorem row_ok92 : ∀ b, pairOK 92 b = true := by decide +kernel

theorem row_ok93 : ∀ b, pairOK 93 b = true := by decide +kernel

theorem row_ok94 : ∀ b, pairOK 94 b = true := by decide +kernel

theorem row_ok95 : ∀ b, pairOK 95 b = true := by decide +kernel

theorem row_ok96 : ∀ b, pairOK 96 b = true := by decide +kernel

theorem row_ok97 : ∀ b, pairOK 97 b = true := by decide +kernel

end VOA.DeligneAudit.E7Lie
