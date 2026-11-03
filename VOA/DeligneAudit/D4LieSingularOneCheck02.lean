/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.D4LieSingularData

/-! Typed one-mode certificate: vector 0, input indices [8, 12). -/
namespace VOA.DeligneAudit.D4Lie

theorem oneZ_block_0_2 : ∀ c e : Fin 28,
    8 ≤ c.val → c.val < 12 → oneZ 0 c e = 0 := by
  decide +kernel

end VOA.DeligneAudit.D4Lie
