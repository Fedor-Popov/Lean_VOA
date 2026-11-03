/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.D4LieSingularData

/-! Typed two-mode certificate for singular vector 2. -/
namespace VOA.DeligneAudit.D4Lie

theorem twoZ_row_2 : ∀ c : Fin 28, twoZ 2 c = 0 := by
  decide +kernel

end VOA.DeligneAudit.D4Lie
