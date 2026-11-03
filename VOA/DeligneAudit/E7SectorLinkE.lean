/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E7SectorRowLinkChecks

/-!
# `e7T` agrees with `E7Lie.sL`, rows `76..94`
-/

namespace VOA.DeligneAudit.DeligneCarrier.E7

theorem rowLink4 : (List.range' 76 19).all rowLinkOK = true := by
  apply List.all_eq_true.mpr
  intro a ha
  have ha' := List.mem_range'_1.mp ha
  exact rowLink_checked a (by omega)

end VOA.DeligneAudit.DeligneCarrier.E7
