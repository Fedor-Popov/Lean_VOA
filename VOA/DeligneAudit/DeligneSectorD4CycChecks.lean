import VOA.DeligneAudit.DeligneSectorD4CycData

namespace VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.DeligneSector.Sparse

theorem d4_wtCheck : wtCheck = true := by decide +kernel

theorem d4_raisingCheck : ∀ e y : Fin 28, 4 ≤ e.val → e.val < 16 → fZ br e y 27 = 0 := by
  decide +kernel

theorem d4_cartanCheck : ∀ h y : Fin 28, h.val < 4 →
    fZ br h y 27 = if y.val = 27 then -(if h.val = 1 then 1 else 0) else 0 := by
  decide +kernel

theorem d4_cycCheck : cycCheck = true := by decide +kernel

end VOA.DeligneAudit.DeligneSector.D4
