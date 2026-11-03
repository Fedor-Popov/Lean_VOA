/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E6LatTable

/-!
# Small kernel checks on the `E₆` lattice-model tables
-/

namespace VOA.DeligneAudit.E6Lat

theorem u_mul_self : ∀ a, u a * u a = 1 := by decide +kernel

theorem wtR_norm : ∀ a : Fin 78, formZ (wtR a) (wtR a) = 2 := by decide +kernel

theorem wt_norm : ∀ a : Fin 78, 6 ≤ a.val → formZ (wt a) (wt a) = 2 := by decide +kernel

theorem wt_cartan : ∀ a : Fin 78, a.val < 6 → wt a = 0 := by decide +kernel

end VOA.DeligneAudit.E6Lat
