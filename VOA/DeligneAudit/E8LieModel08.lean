/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E8LieTable

/-!
# The lattice model is the cert table (`pairOK`), rows `64..71` (one kernel check per row)
-/

namespace VOA.DeligneAudit.E8Lie

theorem row_ok64 : ∀ b, pairOK 64 b = true := by decide +kernel

theorem row_ok65 : ∀ b, pairOK 65 b = true := by decide +kernel

theorem row_ok66 : ∀ b, pairOK 66 b = true := by decide +kernel

theorem row_ok67 : ∀ b, pairOK 67 b = true := by decide +kernel

theorem row_ok68 : ∀ b, pairOK 68 b = true := by decide +kernel

theorem row_ok69 : ∀ b, pairOK 69 b = true := by decide +kernel

theorem row_ok70 : ∀ b, pairOK 70 b = true := by decide +kernel

theorem row_ok71 : ∀ b, pairOK 71 b = true := by decide +kernel

end VOA.DeligneAudit.E8Lie
