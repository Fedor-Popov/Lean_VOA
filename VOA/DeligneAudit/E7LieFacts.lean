/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E7LieTable

/-!
# Small kernel checks on the `E₇` tables
-/

namespace VOA.DeligneAudit.E7Lie

theorem u_mul_self : ∀ a, u a * u a = 1 := by decide +kernel

theorem wtR_norm : ∀ a : Fin 133, formZ (wtR a) (wtR a) = 2 := by decide +kernel

theorem wt_norm : ∀ a : Fin 133, 7 ≤ a.val → formZ (wt a) (wt a) = 2 := by decide +kernel

theorem wt_cartan : ∀ a : Fin 133, a.val < 7 → wt a = 0 := by decide +kernel


end VOA.DeligneAudit.E7Lie
