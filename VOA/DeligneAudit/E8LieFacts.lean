/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E8LieTable

/-!
# Small kernel checks on the `E₈` tables
-/

namespace VOA.DeligneAudit.E8Lie

theorem u_mul_self : ∀ a, u a * u a = 1 := by decide +kernel

theorem wtR_norm : ∀ a : Fin 248, formZ (wtR a) (wtR a) = 2 := by decide +kernel

theorem wt_norm : ∀ a : Fin 248, 8 ≤ a.val → formZ (wt a) (wt a) = 2 := by decide +kernel

theorem wt_cartan : ∀ a : Fin 248, a.val < 8 → wt a = 0 := by decide +kernel


end VOA.DeligneAudit.E8Lie
