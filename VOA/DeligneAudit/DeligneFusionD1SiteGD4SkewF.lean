import VOA.DeligneAudit.DeligneSectorD4Table

/-! # Light finite skew-table rows for the explicit D4 current site -/

namespace VOA.DeligneAudit.D1SiteG.D4Check

open VOA.DeligneAudit.DeligneSector.Sparse
open VOA.DeligneAudit.DeligneSector.D4

theorem skew20 : ∀ b c : Fin 28, fZ br 20 b c = -fZ br b 20 c := by
  decide +kernel

theorem skew21 : ∀ b c : Fin 28, fZ br 21 b c = -fZ br b 21 c := by
  decide +kernel

theorem skew22 : ∀ b c : Fin 28, fZ br 22 b c = -fZ br b 22 c := by
  decide +kernel

theorem skew23 : ∀ b c : Fin 28, fZ br 23 b c = -fZ br b 23 c := by
  decide +kernel

end VOA.DeligneAudit.D1SiteG.D4Check

