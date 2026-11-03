/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E6LatTable

/-!
# The lattice model is the cert table (`pairOK`), rows `49..55` (one kernel check per row)
-/

namespace VOA.DeligneAudit.E6Lat

theorem row_ok49 : ∀ b, pairOK 49 b = true := by decide +kernel

theorem row_ok50 : ∀ b, pairOK 50 b = true := by decide +kernel

theorem row_ok51 : ∀ b, pairOK 51 b = true := by decide +kernel

theorem row_ok52 : ∀ b, pairOK 52 b = true := by decide +kernel

theorem row_ok53 : ∀ b, pairOK 53 b = true := by decide +kernel

theorem row_ok54 : ∀ b, pairOK 54 b = true := by decide +kernel

theorem row_ok55 : ∀ b, pairOK 55 b = true := by decide +kernel

end VOA.DeligneAudit.E6Lat
