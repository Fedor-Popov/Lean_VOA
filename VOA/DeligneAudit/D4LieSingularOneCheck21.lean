/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.D4LieSingularData

/-! Typed one-mode certificate: vector 2, input indices [4, 8). -/
namespace VOA.DeligneAudit.D4Lie

theorem oneZ_block_2_1 : ∀ c e : Fin 28,
    4 ≤ c.val → c.val < 8 → oneZ 2 c e = 0 := by
  decide +kernel

end VOA.DeligneAudit.D4Lie
