/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E7SectorStabilityDefs
import Lean.Elab.Tactic.Omega

/-! Join exact stability ranges without reevaluating their Boolean predicates. -/
namespace VOA.DeligneAudit.DeligneCarrier.E7

theorem stabPart_join (g : ℕ) (rows : List (List ℕ)) {lo mid hi : ℕ}
    (h1 : lo ≤ mid) (h2 : mid ≤ hi)
    (ha : stabPart g rows lo mid = true) (hb : stabPart g rows mid hi = true) :
    stabPart g rows lo hi = true := by
  unfold stabPart at *
  have e : hi - lo = (mid - lo) + (hi - mid) := by omega
  have e2 : lo + (mid - lo) = mid := by omega
  rw [e, ← List.range'_append_1, List.all_append, Bool.and_eq_true, e2]
  exact ⟨ha, hb⟩

end VOA.DeligneAudit.DeligneCarrier.E7
