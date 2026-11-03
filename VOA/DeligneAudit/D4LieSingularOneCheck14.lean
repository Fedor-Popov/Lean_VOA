/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.D4LieSingularData

/-! Typed one-mode certificate: vector 1, input indices [16, 20). -/
namespace VOA.DeligneAudit.D4Lie

theorem oneZ_block_1_4 : ∀ c e : Fin 28,
    16 ≤ c.val → c.val < 20 → oneZ 1 c e = 0 := by
  decide +kernel

end VOA.DeligneAudit.D4Lie
