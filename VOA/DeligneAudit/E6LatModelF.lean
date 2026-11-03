/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E6LatTable

/-!
# The lattice model is the cert table (`pairOK`), rows `35..41` (one kernel check per row)
-/

namespace VOA.DeligneAudit.E6Lat

theorem row_ok35 : ∀ b, pairOK 35 b = true := by decide +kernel

theorem row_ok36 : ∀ b, pairOK 36 b = true := by decide +kernel

theorem row_ok37 : ∀ b, pairOK 37 b = true := by decide +kernel

theorem row_ok38 : ∀ b, pairOK 38 b = true := by decide +kernel

theorem row_ok39 : ∀ b, pairOK 39 b = true := by decide +kernel

theorem row_ok40 : ∀ b, pairOK 40 b = true := by decide +kernel

theorem row_ok41 : ∀ b, pairOK 41 b = true := by decide +kernel

end VOA.DeligneAudit.E6Lat
