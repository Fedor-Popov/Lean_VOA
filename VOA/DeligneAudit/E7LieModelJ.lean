/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E7LieTable

/-!
# The lattice model is the cert table (`pairOK`), rows `63..69` (one kernel check per row)
-/

namespace VOA.DeligneAudit.E7Lie

theorem row_ok63 : ∀ b, pairOK 63 b = true := by decide +kernel

theorem row_ok64 : ∀ b, pairOK 64 b = true := by decide +kernel

theorem row_ok65 : ∀ b, pairOK 65 b = true := by decide +kernel

theorem row_ok66 : ∀ b, pairOK 66 b = true := by decide +kernel

theorem row_ok67 : ∀ b, pairOK 67 b = true := by decide +kernel

theorem row_ok68 : ∀ b, pairOK 68 b = true := by decide +kernel

theorem row_ok69 : ∀ b, pairOK 69 b = true := by decide +kernel

end VOA.DeligneAudit.E7Lie
