/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E8LieTable

/-!
# The lattice model is the cert table (`pairOK`), rows `160..167` (one kernel check per row)
-/

namespace VOA.DeligneAudit.E8Lie

theorem row_ok160 : ∀ b, pairOK 160 b = true := by decide +kernel

theorem row_ok161 : ∀ b, pairOK 161 b = true := by decide +kernel

theorem row_ok162 : ∀ b, pairOK 162 b = true := by decide +kernel

theorem row_ok163 : ∀ b, pairOK 163 b = true := by decide +kernel

theorem row_ok164 : ∀ b, pairOK 164 b = true := by decide +kernel

theorem row_ok165 : ∀ b, pairOK 165 b = true := by decide +kernel

theorem row_ok166 : ∀ b, pairOK 166 b = true := by decide +kernel

theorem row_ok167 : ∀ b, pairOK 167 b = true := by decide +kernel

end VOA.DeligneAudit.E8Lie
